// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
// Copyright (c) 2020 Brian Campbell
// Copyright (c) 2020 Dhruv Makwana
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// 1. Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

//! This module implements the core of the symbolic execution engine.

use crossbeam::deque::{Injector, Steal, Stealer, Worker};
use crossbeam::queue::SegQueue;
use std::borrow::Cow;
use std::collections::VecDeque;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::mpsc;
use std::sync::mpsc::{Receiver, Sender};
use std::sync::{Arc, Condvar, Mutex, RwLock};
use std::thread;
use std::time::{Duration, Instant};

use crate::bitvector::{b64::B64, required_index_bits, BV};
use crate::error::{ExecError, IslaError};
use crate::fraction::Fraction;
use crate::ir::*;
use crate::log;
use crate::primop;
use crate::primop_util::{build_ite, i128_from_bits, ite_phi, smt_value, symbolic};
use crate::probe;
use crate::smt::smtlib::Def;
use crate::smt::*;
use crate::source_loc::SourceLoc;
use crate::zencode;

mod execution_limits;
mod frame;
mod path_timing;
mod task;

use crate::register::RegisterBindings;
#[cfg(test)]
use execution_limits::ExecutionLimitPathState;
use execution_limits::{BranchSample, ExecutionLimitDecision, ExecutionLimitHandler, ExecutionLimitReason};
pub use execution_limits::{ExecutionLimits, LimitBehavior};
pub use frame::{backtrace_string, freeze_frame, unfreeze_frame, Backtrace, Frame, LocalFrame, LocalState};
use frame::{pop_call_stack, push_call_stack};
use path_timing::PathTimeout;
pub use task::{StopAction, StopConditions, Task, TaskId, TaskInterrupt, TaskState};

/// Gets a value from a variable `Bindings` map. Note that this function is set up to handle the
/// following case:
///
/// ```Sail
/// var x;
/// x = 3;
/// ```
///
/// When we declare a variable it has the value `UVal::Uninit(ty)` where `ty` is its type. When
/// that variable is first accessed it'll be initialized to a symbolic value in the SMT solver if it
/// is still uninitialized. This means that in the above code, because `x` is immediately assigned
/// the value 3, no interaction with the SMT solver will occur.
fn get_and_initialize<'state, 'ir, B: BV>(
    v: Name,
    vars: &'state mut Bindings<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<&'state Val<B>>, ExecError> {
    Ok(match vars.get_mut(&v) {
        Some(uval) => match uval {
            UVal::Uninit(ty) => {
                let sym = symbolic(ty, shared_state, solver, info)?;
                *uval = UVal::Init(sym);
                if let UVal::Init(value) = uval {
                    Some(value)
                } else {
                    unreachable!()
                }
            }
            UVal::Init(value) => Some(value),
        },
        None => None,
    })
}

fn get_id_and_initialize<'state, 'ir, B: BV>(
    id: Name,
    local_state: &'state mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    accessor: &mut [Accessor],
    info: SourceLoc,
    for_write: bool,
) -> Result<Cow<'state, Val<B>>, ExecError> {
    use Cow::*;

    Ok(match get_and_initialize(id, &mut local_state.vars, shared_state, solver, info)? {
        Some(value) => Borrowed(value),
        None => match local_state.regs.get(id, shared_state, solver, info)? {
            Some(value) => {
                let symbol = zencode::decode(shared_state.symtab.to_str(id));
                // HACK: Don't store the entire TLB in the trace
                if !for_write && symbol != "_TLB" {
                    solver.add_event(Event::ReadReg(id, accessor.to_vec(), value.clone()));
                }
                Borrowed(value)
            }
            None => match get_and_initialize(id, &mut local_state.lets, shared_state, solver, info)? {
                Some(value) => Borrowed(value),
                None => match shared_state.type_info.enum_members.get(&id) {
                    Some((member, enum_size, enum_id)) => {
                        let enum_id = solver.get_enum(*enum_id, *enum_size);
                        Owned(Val::Enum(EnumMember { enum_id, member: *member }))
                    }
                    None => {
                        return Err(ExecError::VariableNotFound(zencode::decode(shared_state.symtab.to_str(id)), info))
                    }
                },
            },
        },
    })
}

fn get_loc_and_initialize<'ir, B: BV>(
    loc: &Loc<Name>,
    local_state: &mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    accessor: &mut Vec<Accessor>,
    info: SourceLoc,
    for_write: bool,
) -> Result<Val<B>, ExecError> {
    Ok(match loc {
        Loc::Id(id) => {
            get_id_and_initialize(*id, local_state, shared_state, solver, accessor, info, for_write)?.into_owned()
        }
        Loc::Field(loc, field) => {
            accessor.push(Accessor::Field(*field));
            if let Val::Struct(members) =
                get_loc_and_initialize(loc, local_state, shared_state, solver, accessor, info, for_write)?
            {
                match members.get(field) {
                    Some(field_value) => field_value.clone(),
                    None => panic!("No field {:?}", shared_state.symtab.to_str(*field)),
                }
            } else {
                panic!("Struct expression did not evaluate to a struct")
            }
        }
        _ => panic!("Cannot get_loc_and_initialize"),
    })
}

enum RegisterVectorIndex {
    ConcreteIndex(usize),
    SymbolicIndex(Sym),
}

fn fix_index_length<B: BV>(i: Sym, from: u32, to: u32, solver: &mut Solver<B>, info: SourceLoc) -> Sym {
    use smtlib::Exp::*;
    if from == to {
        i
    } else if from > to {
        solver.define_const(Extract(to - 1, 0, Box::new(Var(i))), info)
    } else {
        solver.define_const(ZeroExtend(to - from, Box::new(Var(i))), info)
    }
}

fn read_register_from_vector<'ir, B: BV>(
    n: Val<B>,
    regs_vector: Val<B>,
    local_state: &mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    use smtlib::Exp::*;
    use RegisterVectorIndex::*;

    let bad_regs_argument = "read_register_from_vector must be given a vector of register references";
    let regs: Vec<Name> = match &regs_vector {
        Val::Vector(regs) => {
            regs.iter()
                .map(|r| {
                    if let Val::Ref(r) = r {
                        Ok(*r)
                    } else {
                        Err(ExecError::Type(bad_regs_argument.to_string(), info))
                    }
                })
                .collect::<Result<_, _>>()?
        }
        _ => return Err(ExecError::Type(bad_regs_argument.to_string(), info)),
    };
    let rib = required_index_bits(regs.len());

    let invalid_index_argument = "read_register_from_vector invalid index";
    let index = match n {
        Val::Bits(bv) => ConcreteIndex(bv.lower_u64() as usize),
        Val::I64(n) => {
            ConcreteIndex(n.try_into().map_err(|_| ExecError::Type(invalid_index_argument.to_string(), info))?)
        }
        Val::I128(n) => {
            ConcreteIndex(n.try_into().map_err(|_| ExecError::Type(invalid_index_argument.to_string(), info))?)
        }
        Val::Symbolic(v) => {
            if let Some(len) = solver.length(v) {
                let v = fix_index_length(v, len, rib, solver, info);
                SymbolicIndex(v)
            } else {
                return Err(ExecError::Type(
                    "read_register_from_vector could not determine length of index bitvector".to_string(),
                    info,
                ));
            }
        }
        _ => return Err(ExecError::Type("read_register_from_vector index type must be a bitvector".to_string(), info)),
    };

    match index {
        ConcreteIndex(i) => {
            // This unwrap should be same as all register references must point to value registers
            let value = local_state.regs.get(regs[i], shared_state, solver, info)?.unwrap();
            solver.add_event(Event::ReadReg(regs[i], Vec::new(), value.clone()));
            Ok(value.clone())
        }
        SymbolicIndex(i) => {
            // See above case for unwrap safety
            let mut chain = local_state.regs.get(regs[0], shared_state, solver, info)?.unwrap().clone();
            let mut reg_values = vec![chain.clone()];
            for (j, reg) in regs[1..].iter().enumerate() {
                let choice = solver.with_def_attrs(DefAttrs::uninteresting(), |solver| {
                    solver.define_const(Eq(Box::new(Var(i)), Box::new(Bits64(B64::new((j + 1) as u64, rib)))), info)
                });
                let value = local_state.regs.get(*reg, shared_state, solver, info)?.unwrap();
                reg_values.push(value.clone());
                chain = solver.with_def_attrs(DefAttrs::uninteresting(), |solver| {
                    build_ite(choice, value, &chain, solver, info)
                })?
            }
            solver.add_event(Event::Abstract {
                name: READ_REGISTER_FROM_VECTOR,
                primitive: true,
                args: vec![n, regs_vector, Val::Vector(reg_values)],
                return_value: chain.clone(),
            });
            Ok(chain)
        }
    }
}

fn write_register_from_vector<'ir, B: BV>(
    n: Val<B>,
    value: Val<B>,
    regs_vector: Val<B>,
    local_state: &mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<(), ExecError> {
    use smtlib::Exp::*;
    use RegisterVectorIndex::*;

    let bad_regs_argument = "write_register_from_vector must be given a vector of register references";
    let regs: Vec<Name> = match &regs_vector {
        Val::Vector(regs) => {
            regs.iter()
                .map(|r| {
                    if let Val::Ref(r) = r {
                        Ok(*r)
                    } else {
                        Err(ExecError::Type(bad_regs_argument.to_string(), info))
                    }
                })
                .collect::<Result<_, _>>()?
        }
        _ => return Err(ExecError::Type(bad_regs_argument.to_string(), info)),
    };
    let rib = required_index_bits(regs.len());

    let invalid_index_argument = "write_register_from_vector invalid index";
    let index = match n {
        Val::Bits(bv) => ConcreteIndex(bv.lower_u64() as usize),
        Val::I64(n) => {
            ConcreteIndex(n.try_into().map_err(|_| ExecError::Type(invalid_index_argument.to_string(), info))?)
        }
        Val::I128(n) => {
            ConcreteIndex(n.try_into().map_err(|_| ExecError::Type(invalid_index_argument.to_string(), info))?)
        }
        Val::Symbolic(v) => {
            if let Some(len) = solver.length(v) {
                let v = fix_index_length(v, len, rib, solver, info);
                SymbolicIndex(v)
            } else {
                return Err(ExecError::Type(
                    "write_register_from_vector could not determine length of index bitvector".to_string(),
                    info,
                ));
            }
        }
        _ => {
            return Err(ExecError::Type("write_register_from_vector index type must be a bitvector".to_string(), info))
        }
    };

    match index {
        ConcreteIndex(i) => {
            // This unwrap should be same as all register references must point to value registers
            local_state.regs.assign(regs[i], value.clone(), shared_state);
            solver.add_event(Event::WriteReg(regs[i], Vec::new(), value))
        }
        SymbolicIndex(i) => {
            let mut reg_values = Vec::new();
            for (j, reg) in regs.iter().enumerate() {
                solver.set_def_attrs(DefAttrs::uninteresting());
                let choice = solver.with_def_attrs(DefAttrs::uninteresting(), |solver| {
                    solver.define_const(Eq(Box::new(Var(i)), Box::new(Bits64(B64::new(j as u64, rib)))), info)
                });
                let current_value = local_state.regs.get(*reg, shared_state, solver, info)?.unwrap().clone();
                local_state.regs.assign(
                    *reg,
                    solver.with_def_attrs(DefAttrs::uninteresting(), |solver| {
                        build_ite(choice, &value, &current_value, solver, info)
                    })?,
                    shared_state,
                );
                reg_values.push(current_value);
            }
            solver.add_event(Event::Abstract {
                name: WRITE_REGISTER_FROM_VECTOR,
                primitive: true,
                args: vec![n, value, regs_vector, Val::Vector(reg_values)],
                return_value: Val::Unit,
            })
        }
    }

    Ok(())
}

fn eval_exp_with_accessor<'state, 'ir, B: BV>(
    exp: &Exp<Name>,
    local_state: &'state mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    accessor: &mut Vec<Accessor>,
    info: SourceLoc,
) -> Result<Cow<'state, Val<B>>, ExecError> {
    use Cow::*;
    use Exp::*;

    Ok(match exp {
        Id(id) => get_id_and_initialize(*id, local_state, shared_state, solver, accessor, info, false)?,

        I64(n) => Owned(Val::I64(*n)),
        I128(n) => Owned(Val::I128(*n)),
        Unit => Owned(Val::Unit),
        Bool(b) => Owned(Val::Bool(*b)),
        // The parser only returns 64-bit or less bitvectors
        Bits(bv) => Owned(Val::Bits(B::new(bv.lower_u64(), bv.len()))),
        String(s) => Owned(Val::String(s.clone())),

        Undefined(ty) => Owned(symbolic(ty, shared_state, solver, info)?),

        Call(op, unevaluated_args) => {
            let mut args: Vec<Val<B>> = Vec::new();
            for arg in unevaluated_args {
                args.push(eval_exp(arg, local_state, shared_state, solver, info)?.into_owned())
            }
            Owned(match op {
                Op::Lt => primop::op_lt(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Gt => primop::op_gt(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Lteq => primop::op_lteq(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Gteq => primop::op_gteq(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Eq => primop::op_eq(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Neq => primop::op_neq(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Add => primop::op_add(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Sub => primop::op_sub(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Bvnot => primop::not_bits(args[0].clone(), solver, info)?,
                Op::Bvor => primop::or_bits(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Bvxor => primop::xor_bits(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Bvand => primop::and_bits(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Bvadd => primop::add_bits(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Bvsub => primop::sub_bits(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Bvaccess => primop::vector_access(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Concat => primop::append(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Not => primop::not_bool(args[0].clone(), solver, info)?,
                Op::And => primop::and_bool(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Or => primop::or_bool(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Slice(len) => primop::op_slice(args[0].clone(), args[1].clone(), *len, solver, info)?,
                Op::SetSlice => primop::op_set_slice(args[0].clone(), args[1].clone(), args[2].clone(), solver, info)?,
                Op::Unsigned(_) => primop::op_unsigned(args[0].clone(), solver, info)?,
                Op::Signed(_) => primop::op_signed(args[0].clone(), solver, info)?,
                Op::Head => primop::op_head(args[0].clone(), solver, info)?,
                Op::Tail => primop::op_tail(args[0].clone(), solver, info)?,
                Op::IsEmpty => primop::op_is_empty(args[0].clone(), solver, info)?,
                Op::ZeroExtend(len) => primop::op_zero_extend(args[0].clone(), *len, solver, info)?,
            })
        }

        Kind(ctor_a, exp) => {
            let v = eval_exp(exp, local_state, shared_state, solver, info)?;
            Owned(match v.as_ref() {
                Val::Ctor(ctor_b, _) => Val::Bool(*ctor_a != *ctor_b),
                Val::SymbolicCtor(ctor_sym, _) => {
                    use smtlib::Exp::*;
                    let b = solver.define_const(Neq(Box::new(Var(*ctor_sym)), Box::new(ctor_a.to_smt())), info);
                    Val::Symbolic(b)
                }
                _ => return Err(ExecError::Type(format!("Kind check on non-constructor {:?}", &v), info)),
            })
        }

        Unwrap(ctor_a, exp) => {
            let v = eval_exp(exp, local_state, shared_state, solver, info)?;
            match v {
                Borrowed(Val::Ctor(ctor_b, v)) if *ctor_a == *ctor_b => Borrowed(v),

                Owned(Val::Ctor(ctor_b, v)) if *ctor_a == ctor_b => Owned(*v),

                Borrowed(Val::SymbolicCtor(_, possibilities)) => match possibilities.get(ctor_a) {
                    Some(v) => Borrowed(v),
                    None => return Err(ExecError::Type("No possible value for constructor".to_string(), info)),
                },

                Owned(Val::SymbolicCtor(_, mut possibilities)) => match possibilities.remove(ctor_a) {
                    Some(v) => Owned(v),
                    None => return Err(ExecError::Type("No possible value for constructor".to_string(), info)),
                },

                _ => {
                    return Err(ExecError::Type(
                        format!("Tried to unwrap non-constructor, or constructors didn't match {:?}", &v),
                        info,
                    ))
                }
            }
        }

        Field(exp, field) => {
            accessor.push(Accessor::Field(*field));
            match eval_exp_with_accessor(exp, local_state, shared_state, solver, accessor, info)? {
                Borrowed(Val::Struct(struct_value)) => match struct_value.get(field) {
                    Some(field_value) => Borrowed(field_value),
                    None => panic!("No field {:?}", shared_state.symtab.to_str(*field)),
                },

                Owned(Val::Struct(mut struct_value)) => match struct_value.remove(field) {
                    Some(field_value) => Owned(field_value),
                    None => panic!("No field {:?}", shared_state.symtab.to_str(*field)),
                },

                non_struct => {
                    return Err(ExecError::Type(
                        format!(
                            "When accessing field {} struct expression {:?} did not evaluate to a struct, instead {}",
                            shared_state.symtab.to_str(*field),
                            exp,
                            non_struct.as_ref().to_string(shared_state)
                        ),
                        info,
                    ))
                }
            }
        }

        Ref(reg) => Owned(Val::Ref(*reg)),

        Struct(_, exp_fields) => {
            let mut val_fields = HashMap::default();
            for (id, exp) in exp_fields {
                let v = eval_exp(exp, local_state, shared_state, solver, info)?.into_owned();
                val_fields.insert(*id, v);
            }
            Owned(Val::Struct(val_fields))
        }
    })
}

fn eval_exp<'state, 'ir, B: BV>(
    exp: &Exp<Name>,
    local_state: &'state mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Cow<'state, Val<B>>, ExecError> {
    eval_exp_with_accessor(exp, local_state, shared_state, solver, &mut Vec::new(), info)
}

fn assign_with_accessor<'ir, B: BV>(
    loc: &Loc<Name>,
    v: Val<B>,
    local_state: &mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    accessor: &mut Vec<Accessor>,
    info: SourceLoc,
) -> Result<(), ExecError> {
    match loc {
        Loc::Id(id) => {
            if local_state.vars.contains_key(id) {
                local_state.vars.insert(*id, UVal::Init(v));
            } else if local_state.lets.contains_key(id) {
                local_state.lets.insert(*id, UVal::Init(v));
            } else {
                let symbol = zencode::decode(shared_state.symtab.to_str(*id));
                // HACK: Don't store the entire TLB in the trace
                if symbol != "_TLB" {
                    solver.add_event(Event::WriteReg(*id, accessor.to_vec(), v.clone()))
                }
                local_state.regs.assign(*id, v, shared_state);
            }
        }

        Loc::Field(loc, field) => {
            if let Val::Struct(field_values) =
                get_loc_and_initialize(loc, local_state, shared_state, solver, &mut accessor.clone(), info, true)?
            {
                accessor.push(Accessor::Field(*field));
                // As a sanity test, check that the field exists.
                match field_values.get(field) {
                    Some(_) => {
                        let mut field_values = field_values.clone();
                        field_values.insert(*field, v);
                        assign_with_accessor(
                            loc,
                            Val::Struct(field_values),
                            local_state,
                            shared_state,
                            solver,
                            accessor,
                            info,
                        )?;
                    }
                    None => panic!("Invalid field assignment"),
                }
            } else {
                panic!(
                    "Cannot assign struct to non-struct {:?}.{:?} ({:?})",
                    loc,
                    field,
                    get_loc_and_initialize(loc, local_state, shared_state, solver, &mut accessor.clone(), info, true)
                )
            }
        }

        Loc::Addr(loc) => {
            if let Val::Ref(reg) = get_loc_and_initialize(loc, local_state, shared_state, solver, accessor, info, true)?
            {
                assign_with_accessor(&Loc::Id(reg), v, local_state, shared_state, solver, accessor, info)?
            } else {
                panic!("Cannot get address of non-reference {:?}", loc)
            }
        }
    };
    Ok(())
}

fn assign<'ir, B: BV>(
    tid: usize,
    loc: &Loc<Name>,
    v: Val<B>,
    local_state: &mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<(), ExecError> {
    let id = loc.id();
    if local_state.should_probe(shared_state, &id) {
        log_from!(
            tid,
            log::PROBE,
            &format!(
                "Assigning {}[{:?}] <- {:?} at {}",
                loc_string(loc, &shared_state.symtab),
                id,
                v,
                info.location_string(shared_state.symtab.files())
            )
        )
    }

    assign_with_accessor(loc, v, local_state, shared_state, solver, &mut Vec::new(), info)
}

fn smt_exp_to_value<B: BV>(exp: smtlib::Exp<Sym>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    use smtlib::Exp;
    let v = match exp {
        Exp::Var(v) => Val::Symbolic(v),
        Exp::Bits64(b) => Val::Bits(B::new(b.lower_u64(), b.len())),
        Exp::Enum(m) => Val::Enum(m),
        Exp::Bool(b) => Val::Bool(b),
        _ => {
            // TODO: other sources?
            let v = solver.define_const(exp, SourceLoc::command_line());
            Val::Symbolic(v)
        }
    };
    Ok(v)
}

pub fn interrupt_pending<'ir, B: BV>(
    tid: usize,
    task_id: TaskId,
    frame: &mut LocalFrame<'ir, B>,
    task_state: &TaskState<B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<bool, ExecError> {
    for interrupt in &task_state.interrupts {
        let Some(Val::Bits(reg_value)) =
            frame.local_state.regs.get(interrupt.trigger_register, shared_state, solver, info)?
        else {
            return Err(ExecError::BadInterrupt(
                "trigger register does not exist, or does not have a concrete bitvector value",
            ));
        };

        if *reg_value == interrupt.trigger_value {
            for (taken_task_id, taken_interrupt_id) in frame.taken_interrupts.iter().cloned() {
                if task_id == taken_task_id && interrupt.id == taken_interrupt_id {
                    return Ok(false);
                }
            }

            frame.taken_interrupts.push((task_id, interrupt.id));

            log_from!(tid, log::VERBOSE, "Injecting pending interrupt");
            for (loc, reset) in &interrupt.reset {
                let value = reset(&frame.memory, shared_state.typedefs(), solver)?;
                let mut accessor = Vec::new();
                assign_with_accessor(
                    loc,
                    value.clone(),
                    &mut frame.local_state,
                    shared_state,
                    solver,
                    &mut accessor,
                    info,
                )?;
                solver.add_event(Event::AssumeReg(loc.id(), accessor, value));
            }

            return Ok(true);
        }
    }

    // No interrupts were pending
    Ok(false)
}

pub fn reset_registers<'ir, B: BV>(
    _tid: usize,
    frame: &mut LocalFrame<'ir, B>,
    task_state: &TaskState<B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<(), ExecError> {
    for (loc, reset) in &shared_state.reset_registers {
        if !task_state.reset_registers.contains_key(loc) {
            let value = reset(&frame.memory, shared_state.typedefs(), solver)?;
            let mut accessor = Vec::new();
            assign_with_accessor(
                loc,
                value.clone(),
                &mut frame.local_state,
                shared_state,
                solver,
                &mut accessor,
                info,
            )?;
            let reg_id = loc.id();
            frame.local_state.regs.synchronize_register(reg_id);
            // Note that these are just the assumptions from reset_registers; there
            // may also be assumptions from default register values, recorded at the
            // top level.
            solver.add_event(Event::AssumeReg(reg_id, accessor, value));
        }
    }
    for (loc, reset) in &task_state.reset_registers {
        let value = reset(&frame.memory, shared_state.typedefs(), solver)?;
        let mut accessor = Vec::new();
        assign_with_accessor(loc, value.clone(), &mut frame.local_state, shared_state, solver, &mut accessor, info)?;
        solver.add_event(Event::AssumeReg(loc.id(), accessor, value));
    }
    if !shared_state.reset_constraints.is_empty() {
        for constraint in &shared_state.reset_constraints {
            let mut lookup = |s| match shared_state.symtab.get_loc(s) {
                Some(loc) => {
                    let value = get_loc_and_initialize(
                        &loc,
                        &mut frame.local_state,
                        shared_state,
                        solver,
                        &mut Vec::new(),
                        info,
                        false,
                    )
                    .map_err(|e| e.to_string())?;
                    smt_value(&value, info).map_err(|e| e.to_string())
                }
                None => Err(format!("Location {} not found", s)),
            };
            let assertion_exp = constraint.map_var(&mut lookup).map_err(ExecError::Unreachable)?;
            solver.add_event(Event::Assume(constraint.clone()));
            solver.add(Def::Assert(assertion_exp));
        }
        if solver.check_sat(info).is_unsat()? {
            return Err(ExecError::InconsistentRegisterReset);
        }
    }
    // The arguments and result of any function assumptions are
    // evaluated now so that they can refer to register values in the
    // prestate of an instruction.
    for (f, args, result) in &shared_state.function_assumptions {
        let mut lookup = |s| match shared_state.symtab.get_loc(s) {
            Some(loc) => {
                let value = get_loc_and_initialize(
                    &loc,
                    &mut frame.local_state,
                    shared_state,
                    solver,
                    &mut Vec::new(),
                    info,
                    false,
                )
                .map_err(|e| e.to_string())?;
                smt_value(&value, info).map_err(|e| e.to_string())
            }
            None => Err(format!("Location {} not found", s)),
        };
        let smt_args: Result<Vec<Option<smtlib::Exp<Sym>>>, _> = args
            .iter()
            .map(|e| match e {
                None => Ok(None),
                Some(e) => e.map_var(&mut lookup).map(Some).map_err(ExecError::Unreachable),
            })
            .collect();
        let smt_result: smtlib::Exp<Sym> = result.map_var(&mut lookup).map_err(ExecError::Unreachable)?;
        let val_args: Result<Vec<Val<B>>, _> = smt_args?
            .drain(..)
            .map(|e| match e {
                None => Ok(Val::Unit),
                Some(e) => smt_exp_to_value(e, solver),
            })
            .collect();
        let val_args = val_args?;
        let val_result = smt_exp_to_value(smt_result, solver)?;
        let f_name = shared_state.symtab.lookup(f);
        solver.add_event(Event::AssumeFun { name: f_name, args: val_args.clone(), return_value: val_result.clone() });
        let asms = frame.function_assumptions.entry(f_name).or_default();
        asms.push((val_args, val_result));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn run<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B>>(
    tid: usize,
    task_id: TaskId,
    task_fraction: &mut Fraction,
    timeout: PathTimeout,
    stop_conditions: Option<&'task StopConditions>,
    fork_sink: &S,
    frame: &Frame<'ir, B>,
    task_state: &'task TaskState<B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, LocalFrame<'ir, B>)> {
    let mut frame = unfreeze_frame(frame);
    frame.path_timing.start_active();
    let result = run_loop(
        tid,
        task_id,
        task_fraction,
        timeout,
        stop_conditions,
        fork_sink,
        &mut frame,
        task_state,
        shared_state,
        solver,
    );
    frame.path_timing.pause_active();

    match result {
        Ok(run) => Ok((run, frame)),
        Err(err) => {
            frame.backtrace.push((frame.function_name, frame.pc));
            Err((err, frame))
        }
    }
}

// A special primitive can either continue execution, or it can exit
enum SpecialResult {
    Exit,
    Continue,
}

trait ForkSink<'ir, 'task, B: BV> {
    fn submit(&self, task: Task<'ir, 'task, B>);
}

struct SingleForkSink<'a, 'ir, 'task, B: BV> {
    queue: &'a Worker<Task<'ir, 'task, B>>,
}

impl<'a, 'ir, 'task, B: BV> ForkSink<'ir, 'task, B> for SingleForkSink<'a, 'ir, 'task, B> {
    fn submit(&self, task: Task<'ir, 'task, B>) {
        self.queue.push(task);
    }
}

struct MultiForkSink<'scope, 'env, 'ir, 'task, B: BV, R> {
    runtime: Arc<MultiRuntime<'ir, 'task, B, R>>,
    scope: &'scope thread::Scope<'scope, 'env>,
}

impl<'scope, 'env, 'ir, 'task, B: BV + Send + Sync, R: Send + Sync> ForkSink<'ir, 'task, B>
    for MultiForkSink<'scope, 'env, 'ir, 'task, B, R>
where
    'ir: 'scope,
    'task: 'scope,
{
    fn submit(&self, task: Task<'ir, 'task, B>) {
        self.runtime.submit(self.scope, task);
    }
}

struct MultiRuntime<'ir, 'task, B: BV, R> {
    limit: usize,
    timeout: PathTimeout,
    active_threads: AtomicUsize,
    pending_tasks: AtomicUsize,
    next_tid: AtomicUsize,
    refill_owner: AtomicBool,
    queued_tasks: Mutex<VecDeque<Task<'ir, 'task, B>>>,
    finished_mu: Mutex<()>,
    finished_cv: Condvar,
    shared_state: &'ir SharedState<'ir, B>,
    collected: Arc<R>,
    collector: &'ir Collector<'ir, B, R>,
}

impl<'ir, 'task, B: BV + Send + Sync, R: Send + Sync> MultiRuntime<'ir, 'task, B, R> {
    fn submit<'scope, 'env>(self: &Arc<Self>, scope: &'scope thread::Scope<'scope, 'env>, task: Task<'ir, 'task, B>)
    where
        'ir: 'scope,
        'task: 'scope,
    {
        self.pending_tasks.fetch_add(1, Ordering::AcqRel);
        if self.try_reserve_thread() {
            self.spawn_reserved_task(scope, task);
        } else {
            let mut queued = self.queued_tasks.lock().unwrap();
            queued.push_back(task);
        }
    }

    fn try_reserve_thread(&self) -> bool {
        loop {
            let active = self.active_threads.load(Ordering::Acquire);
            if active >= self.limit {
                return false;
            }
            if self.active_threads.compare_exchange(active, active + 1, Ordering::AcqRel, Ordering::Acquire).is_ok() {
                return true;
            }
        }
    }

    fn spawn_reserved_task<'scope, 'env>(
        self: &Arc<Self>,
        scope: &'scope thread::Scope<'scope, 'env>,
        task: Task<'ir, 'task, B>,
    ) where
        'ir: 'scope,
        'task: 'scope,
    {
        let tid = self.next_tid.fetch_add(1, Ordering::Relaxed);
        let runtime = Arc::clone(self);
        scope.spawn(move || runtime.execute_task(scope, tid, task));
    }

    fn execute_task<'scope, 'env>(
        self: Arc<Self>,
        scope: &'scope thread::Scope<'scope, 'env>,
        tid: usize,
        mut task: Task<'ir, 'task, B>,
    ) where
        'ir: 'scope,
        'task: 'scope,
    {
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::from_checkpoint(&ctx, task.checkpoint);
        if let Some((def, event)) = task.fork_cond {
            solver.add_event(event);
            solver.add(def);
        }
        let fork_sink = MultiForkSink { runtime: Arc::clone(&self), scope };
        let result = run(
            tid,
            task.id,
            &mut task.fraction,
            self.timeout,
            task.stop_conditions,
            &fork_sink,
            &task.frame,
            task.state,
            self.shared_state,
            &mut solver,
        );
        (self.collector)(tid, task.id, result, self.shared_state, solver, self.collected.as_ref());
        self.on_task_finished(scope);
    }

    fn on_task_finished<'scope, 'env>(self: &Arc<Self>, scope: &'scope thread::Scope<'scope, 'env>)
    where
        'ir: 'scope,
        'task: 'scope,
    {
        let remaining = self.pending_tasks.fetch_sub(1, Ordering::AcqRel) - 1;
        self.active_threads.fetch_sub(1, Ordering::AcqRel);

        if remaining == 0 {
            let _finished = self.finished_mu.lock().unwrap();
            self.finished_cv.notify_all();
            return;
        }

        self.try_refill_threads(scope);
    }

    fn try_refill_threads<'scope, 'env>(self: &Arc<Self>, scope: &'scope thread::Scope<'scope, 'env>)
    where
        'ir: 'scope,
        'task: 'scope,
    {
        if self.refill_owner.compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire).is_err() {
            return;
        }

        let mut to_spawn = Vec::new();
        {
            let mut queued = self.queued_tasks.lock().unwrap();
            loop {
                let queued_len = queued.len();
                if queued_len == 0 {
                    break;
                }

                let active = self.active_threads.load(Ordering::Acquire);
                if active >= self.limit {
                    break;
                }

                let available = self.limit - active;
                let batch = queued_len.min(available);
                if batch == 0 {
                    break;
                }

                if self
                    .active_threads
                    .compare_exchange(active, active + batch, Ordering::AcqRel, Ordering::Acquire)
                    .is_ok()
                {
                    for _ in 0..batch {
                        to_spawn.push(queued.pop_front().unwrap());
                    }
                    break;
                }
            }
        }

        self.refill_owner.store(false, Ordering::Release);

        for task in to_spawn {
            self.spawn_reserved_task(scope, task);
        }

        if self.pending_tasks.load(Ordering::Acquire) == 0 {
            let _finished = self.finished_mu.lock().unwrap();
            self.finished_cv.notify_all();
        }
    }

    fn wait_until_finished(&self) {
        let mut finished = self.finished_mu.lock().unwrap();
        while self.pending_tasks.load(Ordering::Acquire) != 0 {
            finished = self.finished_cv.wait(finished).unwrap();
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn run_special_primop<'ir, B: BV>(
    loc: &Loc<Name>,
    f: Name,
    args: &[Exp<Name>],
    info: SourceLoc,
    tid: usize,
    task_id: TaskId,
    frame: &mut LocalFrame<'ir, B>,
    task_state: &TaskState<B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<SpecialResult, ExecError> {
    if f == INTERNAL_VECTOR_INIT && args.len() == 1 {
        let arg = eval_exp(&args[0], &mut frame.local_state, shared_state, solver, info)?.into_owned();
        match loc {
            Loc::Id(v) => match (arg, frame.vars().get(v)) {
                (Val::I64(len), Some(UVal::Uninit(Ty::Vector(_) | Ty::FixedVector(_, _)))) => assign(
                    tid,
                    loc,
                    Val::Vector(vec![Val::Poison; len as usize]),
                    &mut frame.local_state,
                    shared_state,
                    solver,
                    info,
                )?,
                _ => return Err(ExecError::Type(format!("internal_vector_init {:?}", &loc), info)),
            },
            _ => return Err(ExecError::Type(format!("internal_vector_init {:?}", &loc), info)),
        };
        frame.pc += 1
    } else if f == INTERNAL_VECTOR_UPDATE && args.len() == 3 {
        let args = args
            .iter()
            .map(|arg| eval_exp(arg, &mut frame.local_state, shared_state, solver, info).map(Cow::into_owned))
            .collect::<Result<Vec<Val<B>>, _>>()?;
        let vector = primop::vector_update(args, solver, frame, info)?;
        assign(tid, loc, vector, &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else if f == RESET_REGISTERS {
        reset_registers(tid, frame, task_state, shared_state, solver, info)?;
        frame.regs_mut().synchronize();
        assign(tid, loc, Val::Unit, &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else if f == INTERRUPT_PENDING {
        let pending = interrupt_pending(tid, task_id, frame, task_state, shared_state, solver, info)?;
        assign(tid, loc, Val::Bool(pending), &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else if f == ITE_PHI {
        let mut true_value = None;
        let mut symbolics = Vec::new();
        for cond in args.chunks_exact(2) {
            let cond_var = match eval_exp(&cond[0], &mut frame.local_state, shared_state, solver, info) {
                Ok(cond_var) => cond_var.into_owned(),
                // A variable not found error indicates that the block associated with this condition variable
                // has not been executed
                Err(ExecError::VariableNotFound(..)) => Val::Bool(false),
                Err(err) => return Err(err),
            };
            match cond_var {
                Val::Bool(true) => {
                    true_value =
                        Some(eval_exp(&cond[1], &mut frame.local_state, shared_state, solver, info)?.into_owned())
                }
                Val::Bool(false) => (),
                Val::Symbolic(sym) => symbolics.push((sym, &cond[1])),
                _ => return Err(ExecError::Type("ite_phi".to_string(), info)),
            }
        }
        if let Some(true_value) = true_value {
            assign(tid, loc, true_value, &mut frame.local_state, shared_state, solver, info)?
        } else {
            let symbolics = symbolics
                .iter()
                .map(|(sym, arg)| {
                    Ok((*sym, eval_exp(arg, &mut frame.local_state, shared_state, solver, info)?.into_owned()))
                })
                .collect::<Result<Vec<(Sym, Val<B>)>, _>>()?;
            let result = ite_phi(&symbolics[0], &symbolics[1..], solver, info)?;
            assign(tid, loc, result, &mut frame.local_state, shared_state, solver, info)?
        }
        frame.pc += 1
    } else if f == REG_DEREF && args.len() == 1 {
        if let Val::Ref(reg) = eval_exp(&args[0], &mut frame.local_state, shared_state, solver, info)?.into_owned() {
            match frame.regs_mut().get(reg, shared_state, solver, info)? {
                Some(value) => {
                    solver.add_event(Event::ReadReg(reg, Vec::new(), value.clone()));
                    assign(tid, loc, value.clone(), &mut frame.local_state, shared_state, solver, info)?
                }
                None => return Err(ExecError::Type(format!("reg_deref {:?}", &reg), info)),
            }
        } else {
            return Err(ExecError::Type(format!("reg_deref (not a register) {:?}", &f), info));
        };
        frame.pc += 1
    } else if (f == ABSTRACT_CALL || f == ABSTRACT_PRIMOP) && !args.is_empty() {
        let mut args = args
            .iter()
            .map(|arg| eval_exp(arg, &mut frame.local_state, shared_state, solver, info).map(Cow::into_owned))
            .collect::<Result<Vec<Val<B>>, _>>()?;
        let abstracted_fn = match args.pop().unwrap() {
            Val::Ref(f) => f,
            _ => panic!("Invalid abstract call (no function name provided)"),
        };
        let return_ty = if f == ABSTRACT_CALL {
            &shared_state.functions[&abstracted_fn].1
        } else {
            &shared_state.externs[&abstracted_fn].1
        };
        let return_value = symbolic(return_ty, shared_state, solver, info)?;
        solver.add_event(Event::Abstract {
            name: abstracted_fn,
            primitive: f == ABSTRACT_PRIMOP,
            args,
            return_value: return_value.clone(),
        });
        assign(tid, loc, return_value, &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else if f == READ_REGISTER_FROM_VECTOR {
        assert!(args.len() == 2);
        let n = eval_exp(&args[0], &mut frame.local_state, shared_state, solver, info)?.into_owned();
        let regs = eval_exp(&args[1], &mut frame.local_state, shared_state, solver, info)?.into_owned();
        let value = read_register_from_vector(n, regs, &mut frame.local_state, shared_state, solver, info)?;
        assign(tid, loc, value, &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else if f == WRITE_REGISTER_FROM_VECTOR {
        assert!(args.len() == 3);
        let n = eval_exp(&args[0], &mut frame.local_state, shared_state, solver, info)?.into_owned();
        let value = eval_exp(&args[1], &mut frame.local_state, shared_state, solver, info)?.into_owned();
        let regs = eval_exp(&args[2], &mut frame.local_state, shared_state, solver, info)?.into_owned();
        write_register_from_vector(n, value, regs, &mut frame.local_state, shared_state, solver, info)?;
        assign(tid, loc, Val::Unit, &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else if f == INSTR_ANNOUNCE {
        assert!(args.len() == 1);
        let opcode = eval_exp(&args[0], &mut frame.local_state, shared_state, solver, info)?.into_owned();
        if let Some((arch_pc, limit)) = task_state.pc_limit {
            if let Some(reg) = frame.local_state.regs.get(arch_pc, shared_state, solver, info)? {
                match reg {
                    Val::Bits(bv) => {
                        let count = frame.pc_counts.entry(*bv).or_insert(0);
                        *count += 1;
                        if *count > limit {
                            return Err(ExecError::PCLimitReached(bv.lower_u64()));
                        }
                    }
                    // We could just do nothing if the program counter register is symbolic?
                    _ => {
                        return Err(ExecError::Type(
                            "Program counter contains non-bitvector or symbolic value".to_string(),
                            info,
                        ))
                    }
                }
            }
        };
        match opcode {
            Val::Bits(bv) if bv.is_zero() && task_state.zero_announce_exit => return Ok(SpecialResult::Exit),
            _ => (),
        };
        solver.add_event(Event::Instr(opcode));
        assign(tid, loc, Val::Unit, &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else if shared_state.type_info.union_ctors.contains(&f) {
        assert!(args.len() == 1);
        let arg = eval_exp(&args[0], &mut frame.local_state, shared_state, solver, info)?.into_owned();
        assign(tid, loc, Val::Ctor(f, Box::new(arg)), &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else {
        let symbol = zencode::decode(shared_state.symtab.to_str(f));
        return Err(ExecError::NoFunction(symbol, info));
    }
    Ok(SpecialResult::Continue)
}

/// 在不再创建子执行路径的前提下，把符号布尔分支 `v` 固定到一个可满足的具体方向。
///
/// 正常的符号执行会在条件的 `true`、`false` 两侧都可满足时 fork，两条路径分别携带
/// `v` 和 `!v` 约束继续执行。执行限制选择 [`LimitBehavior::Concretize`] 后，系统不再
/// fork，而是只保留其中一个方向，以控制路径数量或路径深度。这个函数是该流程的“机制层”：
/// 它只负责验证方向是否可满足并提交最终约束，不负责决定采样策略，也不更新执行限制统计。
///
/// `preferred_value` 表示优先尝试的方向，而不是必须强制采用的结果：
///
/// - 先通过临时 assumption 查询偏好方向是否可满足；
/// - 如果偏好方向不可满足，则查询相反方向；
/// - 如果两个方向都不可满足，说明调用前的 solver 状态或分支不变量已经被破坏，直接触发断言；
/// - 选定方向后，再把对应断言正式加入当前路径的 solver，使执行器中的控制流位置与 SMT
///   路径条件保持一致。
///
/// 返回值是实际提交的分支条件值，可能与 `preferred_value` 不同。调用者据此选择跳转目标或
/// fall-through 路径。
fn concretize_branch_condition<B: BV>(
    v: Sym,
    preferred_value: bool,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<bool, ExecError> {
    use smtlib::Exp::*;

    // 把 Rust 层的方向偏好转换成 SMT 表达式。这里保留 preferred/alternate 两个表达式，
    // 是为了明确区分“策略希望选择哪边”和“当前路径实际上允许选择哪边”。
    let preferred = if preferred_value { Var(v) } else { Not(Box::new(Var(v))) };
    let alternate = if preferred_value { Not(Box::new(Var(v))) } else { Var(v) };

    // check_sat_with 只在当前 solver 状态上附加临时 assumption 做可满足性探测，不会把该方向
    // 留在路径约束中。因此可以先低成本尝试偏好方向，仅在偏好方向不可满足时再查询另一侧。
    let concrete_value = if solver.check_sat_with(&preferred, info).is_sat()? {
        preferred_value
    } else {
        // 一个仍可执行的符号布尔分支至少应有一侧可满足。两侧都不可满足不是普通的路径截断，
        // 而是内部状态不一致，所以按照执行器的不变量要求立即失败，避免掩盖上游逻辑错误。
        assert!(
            solver.check_sat_with(&alternate, info).is_sat()?,
            "symbolic branch has neither a satisfiable preferred side nor a satisfiable alternate side"
        );
        !preferred_value
    };

    // 上面的 SAT 查询只是探测；这里才把最终方向提交到当前执行路径。若省略这一步，Rust
    // 执行器虽然只沿一个 PC 方向继续，solver 却仍允许另一个方向，后续求解结果就会与实际
    // 控制流不一致。
    solver.add(smtlib::Def::Assert(if concrete_value { Var(v) } else { Not(Box::new(Var(v))) }));

    Ok(concrete_value)
}

/// 使用执行限制的可复现采样策略具体化一个普通符号分支。
///
/// 这是"策略层"包装函数，位于执行限制判定和 [`concretize_branch_condition`] 之间。当最大
/// 路径深度、全局 fork 数、单分支 fork 数或单分支 fork 占比等限制触发且配置为
/// [`LimitBehavior::Concretize`] 时，上层调用它，用一次确定性采样代替继续 fork。
///
/// 整体职责分为两步：
///
/// 1. 从 `sample.preferred()` 获取由采样种子、控制流作用域和采样序号确定的偏好方向；
/// 2. 委托 [`concretize_branch_condition`] 验证可满足性并把实际方向加入 solver。
///
/// `preferred` 仍然只是一种偏好：如果该方向在当前路径下不可满足，机制层会选择另一侧。
fn concretize_branch_with_sampling<B: BV>(
    v: Sym,
    solver: &mut Solver<B>,
    info: SourceLoc,
    sample: &BranchSample,
) -> Result<bool, ExecError> {
    concretize_branch_condition(v, sample.preferred(), solver, info)
}

fn concretize_loop_branch_with_sampling<B: BV>(
    v: Sym,
    solver: &mut Solver<B>,
    info: SourceLoc,
    sample: &BranchSample,
) -> Result<Option<bool>, ExecError> {
    use smtlib::Exp::*;

    let exit = Not(Box::new(Var(v)));
    if !solver.check_sat_with(&exit, info).is_sat()? {
        return Ok(None);
    }

    let concrete_value = sample.preferred() && solver.check_sat_with(&Var(v), info).is_sat()?;
    solver.add(smtlib::Def::Assert(if concrete_value { Var(v) } else { exit }));
    Ok(Some(concrete_value))
}

macro_rules! itrace_push_branch_condition {
    ($frame:expr, $condition:expr) => {{
        #[cfg(feature = "tracetool")]
        {
            $frame.itrace_path.push_branch_condition($condition);
        }
        #[cfg(not(feature = "tracetool"))]
        {
            let _ = (&$frame, &$condition);
        }
    }};
}

macro_rules! itrace_fork_frame_with_branch_condition {
    ($frame:expr, $pc:expr, $condition:expr) => {{
        #[cfg(feature = "tracetool")]
        {
            let mut itrace_path = $frame.itrace_path.clone();
            itrace_path.push_branch_condition($condition);
            Frame { pc: $pc, itrace_path: Arc::new(itrace_path), ..freeze_frame($frame) }
        }
        #[cfg(not(feature = "tracetool"))]
        {
            let _ = &$condition;
            Frame { pc: $pc, ..freeze_frame($frame) }
        }
    }};
}

/// 将执行限制触发事件记录到 itrace 追踪日志中，包含限制原因和采取的动作（如 truncate、
/// sample_branch_condition 等）。需要 `tracetool` feature 启用才生效。
fn record_execution_limit<B: BV>(frame: &mut LocalFrame<'_, B>, reason: ExecutionLimitReason, action: &str) {
    #[cfg(feature = "tracetool")]
    {
        let detail = match reason {
            ExecutionLimitReason::MaxForksPerPath { actual, max } => {
                format!("max_forks_per_path exceeded: path_forks={}, max_forks_per_path={}", actual, max)
            }
            ExecutionLimitReason::MaxForksPerBranch { actual, max } => format!(
                "max_forks_per_branch exceeded: path_branch_forks={}, max_forks_per_branch={}",
                actual, max
            ),
            ExecutionLimitReason::MaxForkPctPerBranch {
                branch_actual,
                path_actual,
                max_pct,
                check_delay,
            } => format!(
                "max_fork_pct_per_branch exceeded: path_branch_forks={}, path_forks={}, max_fork_pct_per_branch={}, check_delay={}",
                branch_actual, path_actual, max_pct, check_delay
            ),
            ExecutionLimitReason::MaxBackjumpsPerLoop { target, actual, max } => format!(
                "max_backjumps_per_loop exceeded: target_pc={}, backjumps={}, max_backjumps_per_loop={}",
                target, actual, max
            ),
            ExecutionLimitReason::MaxPathDepth { actual, max } => {
                format!("max_path_depth exceeded: control_flow_steps={}, max_path_depth={}", actual, max)
            }
        };
        frame.itrace_path.record_summary(
            frame.function_name,
            frame.backtrace.clone(),
            frame.pc as u64,
            format!("execution limit: {}, action={}", detail, action),
        );
    }
    #[cfg(not(feature = "tracetool"))]
    let _ = (frame, reason, action);
}

/// 将执行限制原因转换为对应的 `ExecError` 变体，用于在 `Truncate` 决策时返回错误。
fn execution_limit_error(reason: ExecutionLimitReason, function_name: Name, pc: usize) -> ExecError {
    match reason {
        ExecutionLimitReason::MaxPathDepth { .. } => ExecError::DepthLimitReached,
        ExecutionLimitReason::MaxBackjumpsPerLoop { target, .. } => ExecError::LoopLimitReached(function_name, target),
        ExecutionLimitReason::MaxForksPerPath { .. }
        | ExecutionLimitReason::MaxForksPerBranch { .. }
        | ExecutionLimitReason::MaxForkPctPerBranch { .. } => ExecError::BranchLimitReached(function_name, pc),
    }
}

fn loop_limit_target(reason: ExecutionLimitReason) -> Option<usize> {
    match reason {
        ExecutionLimitReason::MaxBackjumpsPerLoop { target, .. } => Some(target),
        _ => None,
    }
}

pub enum Run<B> {
    /// Returned when the model finishes executing
    Finished(Val<B>),
    /// `Exit` is used when the Sail 'exit' function is explicitly
    /// called by the model to exit early.
    Exit,
    /// `Dead` means we are in an inconsistent state, where the
    /// run/trace can safely be discarded by the consumer.
    Dead,
    /// `Suspended` is used when the execution has not yet finished,
    /// but control has been returned back to the consumer.
    Suspended,
}

#[allow(clippy::too_many_arguments)]
fn run_loop<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B>>(
    tid: usize,
    task_id: TaskId,
    task_fraction: &mut Fraction,
    timeout: PathTimeout,
    stop_conditions: Option<&'task StopConditions>,
    fork_sink: &S,
    frame: &mut LocalFrame<'ir, B>,
    task_state: &'task TaskState<B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<Run<B>, ExecError> {
    let mut last_z3_reset = Instant::now();
    let limit_handler = task_state.execution_limits.as_ref().map(ExecutionLimitHandler::new);

    'main_loop: loop {
        // Completion is checked before the soft timeout. Therefore a path that
        // finished its last IR instruction is reported as finished even if its
        // budget was crossed during that instruction. A path timeout only means
        // that execution is stopped at this safe point before the next IR
        // instruction starts; ordinary Rust/IR execution is never preempted.
        if frame.pc >= frame.instrs.len() {
            // Currently this happens when evaluating letbindings.
            return Ok(Run::Finished(Val::Unit));
        }

        if timeout.timed_out_with(|| frame.path_timing.snapshot()) {
            return Err(ExecError::Timeout);
        }

        if last_z3_reset.elapsed() > Duration::from_millis(500) {
            //let mut vars = HashSet::default();
            //frame.collect_symbolic_variables(&mut vars);
            //solver.reset(vars);
            last_z3_reset = Instant::now()
        };

        #[cfg(feature = "tracetool")]
        frame.itrace_path.record(frame.function_name, frame.backtrace.clone(), frame.pc as u64);

        match &frame.instrs[frame.pc] {
            Instr::Decl(v, ty, _) => {
                frame.vars_mut().insert(*v, UVal::Uninit(ty));
                frame.pc += 1;
            }

            Instr::Init(var, _, exp, info) => {
                let value = eval_exp(exp, &mut frame.local_state, shared_state, solver, *info)?.into_owned();
                frame.vars_mut().insert(*var, UVal::Init(value));
                frame.pc += 1;
            }

            Instr::Jump(exp, target, info) => {
                let decision = match limit_handler.as_ref() {
                    Some(handler) => handler.on_conditional_jump(
                        &mut frame.execution_limit_state,
                        frame.function_name,
                        frame.pc,
                        *target,
                        &frame.backtrace,
                        *info,
                    ),
                    None => {
                        frame.execution_limit_state.advance_control_flow();
                        ExecutionLimitDecision::Continue
                    }
                };
                match decision {
                    ExecutionLimitDecision::Continue => {}
                    ExecutionLimitDecision::Truncate(reason) => {
                        record_execution_limit(frame, reason, "truncate");
                        return Err(execution_limit_error(reason, frame.function_name, frame.pc));
                    }
                    ExecutionLimitDecision::ConcretizeBranch { reason, sample } => {
                        let value = eval_exp(exp, &mut frame.local_state, shared_state, solver, *info)?;
                        match *value.as_ref() {
                            Val::Symbolic(v) => {
                                use smtlib::Exp::*;

                                let handler = limit_handler.as_ref().expect("limit decision requires active handler");
                                handler.commit_sample(&mut frame.execution_limit_state, &sample);
                                record_execution_limit(frame, reason, "sample_branch_condition");
                                let concrete_bool = if loop_limit_target(reason).is_some() {
                                    match concretize_loop_branch_with_sampling(v, solver, *info, &sample)? {
                                        Some(value) => value,
                                        None => {
                                            record_execution_limit(
                                                frame,
                                                reason,
                                                "truncate_exit_direction_unsatisfiable",
                                            );
                                            return Err(execution_limit_error(reason, frame.function_name, frame.pc));
                                        }
                                    }
                                } else {
                                    concretize_branch_with_sampling(v, solver, *info, &sample)?
                                };

                                if concrete_bool {
                                    itrace_push_branch_condition!(frame, Var(v));
                                    frame.pc = *target;
                                } else {
                                    itrace_push_branch_condition!(frame, Not(Box::new(Var(v))));
                                    frame.pc += 1;
                                }
                                continue 'main_loop;
                            }
                            Val::Bool(jump) => {
                                if loop_limit_target(reason).is_some() && jump {
                                    record_execution_limit(frame, reason, "truncate_concrete_backjump");
                                    return Err(execution_limit_error(reason, frame.function_name, frame.pc));
                                }
                                if jump {
                                    frame.pc = *target;
                                } else {
                                    frame.pc += 1;
                                }
                                continue 'main_loop;
                            }
                            _ => return Err(ExecError::Type(format!("Jump on non boolean {:?}", &value), *info)),
                        }
                    }
                    ExecutionLimitDecision::Fork { .. } | ExecutionLimitDecision::KeepCurrentModel { .. } => {
                        panic!("conditional jump pre-check returned an invalid execution-limit decision")
                    }
                }

                let value = eval_exp(exp, &mut frame.local_state, shared_state, solver, *info)?;
                match *value.as_ref() {
                    Val::Symbolic(v) => {
                        use smtlib::Def::*;
                        use smtlib::Exp::*;

                        let test_true = Var(v);
                        let test_false = Not(Box::new(Var(v)));

                        let can_be_true = solver.check_sat_with(&test_true, *info).is_sat()?;
                        let can_be_false = solver.check_sat_with(&test_false, *info).is_sat()?;

                        if can_be_true && can_be_false {
                            let decision = match limit_handler.as_ref() {
                                Some(handler) => handler.on_branch_fork(
                                    &mut frame.execution_limit_state,
                                    frame.function_name,
                                    frame.pc,
                                    &frame.backtrace,
                                    *info,
                                ),
                                None => {
                                    ExecutionLimitDecision::Fork { fork_id: frame.execution_limit_state.record_fork() }
                                }
                            };
                            let fork_id = match decision {
                                ExecutionLimitDecision::Fork { fork_id } => fork_id,
                                ExecutionLimitDecision::Truncate(reason) => {
                                    record_execution_limit(frame, reason, "truncate");
                                    return Err(execution_limit_error(reason, frame.function_name, frame.pc));
                                }
                                ExecutionLimitDecision::ConcretizeBranch { reason, sample } => {
                                    let handler =
                                        limit_handler.as_ref().expect("limit decision requires active handler");
                                    handler.commit_sample(&mut frame.execution_limit_state, &sample);
                                    record_execution_limit(frame, reason, "sample_branch_condition");
                                    let concrete_bool = concretize_branch_with_sampling(v, solver, *info, &sample)?;
                                    if concrete_bool {
                                        itrace_push_branch_condition!(frame, test_true);
                                        frame.pc = *target;
                                    } else {
                                        itrace_push_branch_condition!(frame, test_false);
                                        frame.pc += 1;
                                    }
                                    continue 'main_loop;
                                }
                                ExecutionLimitDecision::Continue | ExecutionLimitDecision::KeepCurrentModel { .. } => {
                                    panic!("branch fork admission returned an invalid execution-limit decision")
                                }
                            };

                            if_logging!(log::FORK, {
                                log_from!(tid, log::FORK, info.location_string(shared_state.symtab.files()));
                                probe::taint_info(log::FORK, v, Some(shared_state), solver)
                            });

                            let point = checkpoint(solver);
                            let frozen =
                                itrace_fork_frame_with_branch_condition!(frame, frame.pc + 1, test_false.clone());
                            task_fraction.halve();
                            fork_sink.submit(Task {
                                id: task_id,
                                fraction: task_fraction.clone(),
                                frame: frozen,
                                checkpoint: point,
                                fork_cond: Some((Assert(test_false), Event::Fork(fork_id, v, 1, *info))),
                                state: task_state,
                                stop_conditions,
                            });

                            // Track which asserts are assocated with each fork in the trace, so we
                            // can turn a set of traces into a tree later
                            solver.add_event(Event::Fork(fork_id, v, 0, *info));
                            solver.add(Assert(test_true.clone()));
                            itrace_push_branch_condition!(frame, test_true);
                            frame.pc = *target;
                        } else if can_be_true {
                            solver.add(Assert(test_true));
                            frame.pc = *target;
                        } else if can_be_false {
                            solver.add(Assert(test_false));
                            frame.pc += 1;
                        } else {
                            return Ok(Run::Dead);
                        }
                    }
                    Val::Bool(jump) => {
                        if jump {
                            frame.pc = *target;
                        } else {
                            frame.pc += 1;
                        }
                    }
                    _ => {
                        return Err(ExecError::Type(format!("Jump on non boolean {:?}", &value), *info));
                    }
                }
            }
            // Goto 是无条件跳转，没有分支条件可供具体化，因此限制触发时只能截断。
            Instr::Goto(target) => {
                let decision = match limit_handler.as_ref() {
                    Some(handler) => handler.on_goto(
                        &mut frame.execution_limit_state,
                        frame.function_name,
                        frame.pc,
                        *target,
                        &frame.backtrace,
                    ),
                    None => {
                        frame.execution_limit_state.advance_control_flow();
                        ExecutionLimitDecision::Continue
                    }
                };
                match decision {
                    ExecutionLimitDecision::Continue => {}
                    ExecutionLimitDecision::Truncate(reason) => {
                        record_execution_limit(frame, reason, "truncate_unconditional_control_flow");
                        return Err(execution_limit_error(reason, frame.function_name, frame.pc));
                    }
                    ExecutionLimitDecision::Fork { .. }
                    | ExecutionLimitDecision::ConcretizeBranch { .. }
                    | ExecutionLimitDecision::KeepCurrentModel { .. } => {
                        panic!("goto returned an invalid execution-limit decision")
                    }
                }
                frame.pc = *target;
            }
            Instr::Copy(loc, exp, info) => {
                let value = eval_exp(exp, &mut frame.local_state, shared_state, solver, *info)?.into_owned();
                assign(tid, loc, value, &mut frame.local_state, shared_state, solver, *info)?;
                frame.pc += 1;
            }

            Instr::PrimopUnary(loc, f, arg, info) => {
                let arg = eval_exp(arg, &mut frame.local_state, shared_state, solver, *info)?.into_owned();
                let value = f(arg, solver, *info)?;
                assign(tid, loc, value, &mut frame.local_state, shared_state, solver, *info)?;
                frame.pc += 1;
            }

            Instr::PrimopBinary(loc, f, arg1, arg2, info) => {
                let arg1 = eval_exp(arg1, &mut frame.local_state, shared_state, solver, *info)?.into_owned();
                let arg2 = eval_exp(arg2, &mut frame.local_state, shared_state, solver, *info)?.into_owned();
                let value = f(arg1, arg2, solver, *info)?;
                assign(tid, loc, value, &mut frame.local_state, shared_state, solver, *info)?;
                frame.pc += 1;
            }

            Instr::PrimopVariadic(loc, f, args, info) => {
                let args = args
                    .iter()
                    .map(|arg| eval_exp(arg, &mut frame.local_state, shared_state, solver, *info).map(Cow::into_owned))
                    .collect::<Result<_, _>>()?;
                let value = f(args, solver, frame, *info)?;
                assign(tid, loc, value, &mut frame.local_state, shared_state, solver, *info)?;
                frame.pc += 1;
            }

            Instr::PrimopReset(loc, reset, info) => {
                let value = reset(&frame.memory, shared_state.typedefs(), solver)?;
                assign(tid, loc, value, &mut frame.local_state, shared_state, solver, *info)?;
                frame.pc += 1;
            }

            // Call 的深度限制同 Goto，无条件控制流只能截断。
            Instr::Call(loc, _, f, args, info) => {
                let decision = match limit_handler.as_ref() {
                    Some(handler) => handler.on_call(&mut frame.execution_limit_state),
                    None => {
                        frame.execution_limit_state.advance_control_flow();
                        ExecutionLimitDecision::Continue
                    }
                };
                match decision {
                    ExecutionLimitDecision::Continue => {}
                    ExecutionLimitDecision::Truncate(reason) => {
                        record_execution_limit(frame, reason, "truncate_call_depth_limit");
                        return Err(execution_limit_error(reason, frame.function_name, frame.pc));
                    }
                    ExecutionLimitDecision::Fork { .. }
                    | ExecutionLimitDecision::ConcretizeBranch { .. }
                    | ExecutionLimitDecision::KeepCurrentModel { .. } => {
                        panic!("call returned an invalid execution-limit decision")
                    }
                }

                match shared_state.functions.get(f) {
                    None => {
                        match run_special_primop(
                            loc,
                            *f,
                            args,
                            *info,
                            tid,
                            task_id,
                            frame,
                            task_state,
                            shared_state,
                            solver,
                        )? {
                            SpecialResult::Continue => (),
                            SpecialResult::Exit => return Ok(Run::Exit),
                        }
                    }

                    Some((params, ret_ty, instrs)) => {
                        frame.set_probes(shared_state);

                        let mut args = args
                            .iter()
                            .map(|arg| {
                                eval_exp(arg, &mut frame.local_state, shared_state, solver, *info).map(Cow::into_owned)
                            })
                            .collect::<Result<Vec<Val<B>>, _>>()?;

                        if frame.local_state.should_probe(shared_state, f) {
                            log_from!(tid, log::PROBE, probe::call_info(*f, &args, shared_state, *info));
                            probe::args_info(tid, &args, shared_state, solver)
                        }

                        if shared_state.trace_functions.contains(f) {
                            solver.trace_call(*f)
                        }

                        if let Some(s) = stop_conditions {
                            match s.should_stop(*f, frame.function_name, &frame.backtrace) {
                                Some(StopAction::Kill) => {
                                    let symbol = zencode::decode(shared_state.symtab.to_str(*f));
                                    return Err(ExecError::Stopped(symbol));
                                }
                                Some(StopAction::Abstract) => {
                                    solver.add_event(Event::Abstract {
                                        name: *f,
                                        args,
                                        primitive: false,
                                        return_value: Val::Poison,
                                    });
                                    return Ok(Run::Finished(Val::Poison));
                                }
                                None => (),
                            }
                        }

                        if let Some(assumptions) = frame.function_assumptions.get(f) {
                            for (required_args, result) in assumptions {
                                let mut all_args_match = args.len() == required_args.len();
                                if all_args_match {
                                    for (req, arg) in required_args.iter().zip(args.iter()) {
                                        let equality = primop::eq_anything(req.clone(), arg.clone(), solver, *info)?;
                                        all_args_match = match equality {
                                            Val::Symbolic(var) => match solver.check_sat_with(
                                                &smtlib::Exp::Eq(
                                                    Box::new(smtlib::Exp::Var(var)),
                                                    Box::new(smtlib::Exp::Bool(false)),
                                                ),
                                                *info,
                                            ) {
                                                SmtResult::Unsat => true,
                                                SmtResult::Error(error) => return Err(ExecError::Smt(error)),
                                                SmtResult::Sat | SmtResult::Unknown => false,
                                            },
                                            Val::Bool(matches) => matches,
                                            _ => panic!("TODO"),
                                        };
                                        if !all_args_match {
                                            break;
                                        }
                                    }
                                }
                                if all_args_match {
                                    assign(
                                        tid,
                                        loc,
                                        result.clone(),
                                        &mut frame.local_state,
                                        shared_state,
                                        solver,
                                        *info,
                                    )?;
                                    solver.add_event(Event::UseFunAssumption {
                                        name: *f,
                                        args,
                                        return_value: result.clone(),
                                    });
                                    frame.pc += 1;
                                    continue 'main_loop;
                                }
                            }
                        }

                        let caller_pc = frame.pc;
                        let caller_instrs = frame.instrs;
                        let caller_stack_call = frame.stack_call.clone();
                        push_call_stack(frame);
                        frame.backtrace.push((frame.function_name, caller_pc));
                        frame.function_name = *f;
                        frame.vars_mut().insert(RETURN, UVal::Uninit(ret_ty));

                        // Set up a closure to restore our state when
                        // the function we call returns
                        frame.stack_call = Some(Arc::new(move |ret, frame, shared_state, solver| {
                            pop_call_stack(frame);
                            frame.set_probes(shared_state);
                            // could avoid putting caller_pc into the stack?
                            if let Some((name, _)) = frame.backtrace.pop() {
                                frame.function_name = name;
                            }
                            frame.pc = caller_pc + 1;
                            frame.instrs = caller_instrs;
                            frame.stack_call = caller_stack_call.clone();
                            assign(tid, &loc.clone(), ret, &mut frame.local_state, shared_state, solver, *info)
                        }));

                        for (i, arg) in args.drain(..).enumerate() {
                            frame.vars_mut().insert(params[i].0, UVal::Init(arg));
                        }
                        frame.pc = 0;
                        frame.instrs = instrs;
                    }
                }
            }

            Instr::End => match frame.vars().get(&RETURN) {
                None => panic!("Return variable missing at end of function"),
                Some(value) => {
                    let value = match value {
                        UVal::Uninit(ty) => symbolic(ty, shared_state, solver, SourceLoc::unknown())?,
                        UVal::Init(value) => value.clone(),
                    };

                    if frame.local_state.should_probe(shared_state, &frame.function_name) {
                        let symbol = zencode::decode(shared_state.symtab.to_str(frame.function_name));
                        log_from!(
                            tid,
                            log::PROBE,
                            &format!("Returning {} = {}", symbol, value.to_string(shared_state))
                        );
                        probe::args_info(tid, std::slice::from_ref(&value), shared_state, solver)
                    }

                    if shared_state.trace_functions.contains(&frame.function_name) {
                        solver.trace_return(frame.function_name)
                    }

                    let caller = match &frame.stack_call {
                        None => return Ok(Run::Finished(value)),
                        Some(caller) => Arc::clone(caller),
                    };
                    (*caller)(value, frame, shared_state, solver)?
                }
            },

            // The idea beind the Monomorphize operation is it takes a
            // bitvector identifier, and if that identifer has a
            // symbolic value, then it uses the SMT solver to find all
            // the possible values for that bitvector and case splits
            // (i.e. forks) on them. This allows us to guarantee that
            // certain bitvectors are non-symbolic, at the cost of
            // increasing the number of paths.
            Instr::Monomorphize(id, ty, info) => {
                let val = get_id_and_initialize(
                    *id,
                    &mut frame.local_state,
                    shared_state,
                    solver,
                    &mut Vec::new(),
                    *info,
                    false,
                )?;
                if let Val::Symbolic(v) = *val.as_ref() {
                    use smtlib::bits64;
                    use smtlib::Def::*;
                    use smtlib::Exp::*;

                    let point = checkpoint(solver);

                    match ty {
                        Ty::Bits(len) => {
                            // For the variable v to appear in the model, there must be some assertion that references it
                            let sym = solver.declare_const(smtlib::Ty::BitVec(*len), *info);
                            solver.assert_eq(Var(v), Var(sym));
                        }
                        Ty::AnyBits => {
                            // In this case, get the length from the variable
                            let len = solver.length(v).ok_or_else(|| {
                                ExecError::Type(format!("No SMT length for monomorphizing {:?}", &v), *info)
                            })?;
                            let sym = solver.declare_const(smtlib::Ty::BitVec(len), *info);
                            solver.assert_eq(Var(v), Var(sym));
                        }
                        Ty::Bool => {
                            let sym = solver.declare_const(smtlib::Ty::Bool, *info);
                            solver.assert_eq(Var(v), Var(sym));
                        }
                        Ty::I128 => {
                            let sym = solver.declare_const(smtlib::Ty::BitVec(128), *info);
                            solver.assert_eq(Var(v), Var(sym));
                        }
                        _ => panic!("unknown monomorphize type {:?}", ty),
                    };

                    if solver.check_sat(*info).is_unsat()? {
                        return Ok(Run::Dead);
                    }

                    let (result_exp, result_val) = {
                        let mut model = Model::new(solver);
                        log_from!(tid, log::FORK, format!("Model: {:?}", model));
                        match model.get_var(v) {
                            Ok(ModelVal::Exp(Bits64(bv))) => match ty {
                                Ty::Bits(len) => {
                                    assert!(*len == bv.len());
                                    (bits64(bv.lower_u64(), bv.len()), Val::Bits(B::new(bv.lower_u64(), bv.len())))
                                }
                                Ty::AnyBits => {
                                    (bits64(bv.lower_u64(), bv.len()), Val::Bits(B::new(bv.lower_u64(), bv.len())))
                                }
                                _ => panic!("failed to interpret monomorphized value"),
                            },

                            Ok(ModelVal::Exp(Bits(bv))) => match ty {
                                Ty::I128 => {
                                    assert!(bv.len() == 128);
                                    let i = i128_from_bits(&bv);
                                    (Bits(bv), Val::I128(i))
                                }
                                _ => panic!("failed to interpret monomorphized value"),
                            },

                            Ok(ModelVal::Exp(Bool(b))) => (Bool(b), Val::Bool(b)),

                            // __monomorphize should have a 'n <= 64 constraint in Sail
                            Ok(ModelVal::Exp(other)) => {
                                return Err(ExecError::Type(format!("__monomorphize {:?}", &other), *info))
                            }

                            Ok(ModelVal::Arbitrary(_)) => match ty {
                                Ty::Bits(len) => (bits64(0, *len), Val::Bits(B::new(0, *len))),
                                Ty::Bool => (Bool(false), Val::Bool(false)),
                                Ty::I128 => (Bits(vec![false; 128]), Val::I128(0)),
                                _ => panic!("failed to interpret monomorphized value"),
                            },

                            Err(error) => return Err(error),
                        }
                    };

                    let remainder = Neq(Box::new(Var(v)), Box::new(result_exp.clone()));
                    if solver.check_sat_with(&remainder, *info).is_sat()? {
                        let decision = match limit_handler.as_ref() {
                            Some(handler) => handler.on_monomorphize_fork(&mut frame.execution_limit_state),
                            None => ExecutionLimitDecision::Fork { fork_id: frame.execution_limit_state.record_fork() },
                        };
                        let fork_id = match decision {
                            ExecutionLimitDecision::Fork { fork_id } => Some(fork_id),
                            ExecutionLimitDecision::KeepCurrentModel { reason } => {
                                record_execution_limit(frame, reason, "keep_current_model");
                                None
                            }
                            ExecutionLimitDecision::Truncate(reason) => {
                                record_execution_limit(frame, reason, "truncate_monomorphize");
                                return Err(execution_limit_error(reason, frame.function_name, frame.pc));
                            }
                            ExecutionLimitDecision::Continue | ExecutionLimitDecision::ConcretizeBranch { .. } => {
                                panic!("monomorphize returned an invalid execution-limit decision")
                            }
                        };

                        if let Some(fork_id) = fork_id {
                            log_from!(tid, log::FORK, format!("Fork @ monomorphizing v{} : {:?}", v, ty));

                            // Because we will likely case-split more times in the task we add to the queue,
                            // give it a larger part of the fraction (otherwise the denominator becomes
                            // small very fast).
                            let child_frac = task_fraction.min_split(6);
                            fork_sink.submit(Task {
                                id: task_id,
                                fraction: child_frac,
                                frame: freeze_frame(frame),
                                checkpoint: point,
                                fork_cond: Some((Assert(remainder), Event::Fork(fork_id, v, 1, *info))),
                                state: task_state,
                                stop_conditions,
                            });

                            solver.add_event(Event::Fork(fork_id, v, 0, *info));
                        }
                    }

                    solver.assert_eq(Var(v), result_exp);

                    assign(tid, &Loc::Id(*id), result_val, &mut frame.local_state, shared_state, solver, *info)?;
                }
                frame.pc += 1
            }

            // Arbitrary means return any value. It is used in the
            // Sail->C compilation for exceptional control flow paths
            // to avoid compiler warnings (which would also be UB in
            // C++ compilers). The value should never be used, so we
            // return Val::Poison here.
            Instr::Arbitrary => {
                if frame.local_state.should_probe(shared_state, &frame.function_name) {
                    let symbol = zencode::decode(shared_state.symtab.to_str(frame.function_name));
                    log_from!(
                        tid,
                        log::PROBE,
                        &format!("Returning via arbitrary {}[{:?}] = poison", symbol, frame.function_name)
                    );
                }

                if shared_state.trace_functions.contains(&frame.function_name) {
                    solver.trace_return(frame.function_name)
                }

                let caller = match &frame.stack_call {
                    None => return Ok(Run::Finished(Val::Poison)),
                    Some(caller) => Arc::clone(caller),
                };
                (*caller)(Val::Poison, frame, shared_state, solver)?
            }

            Instr::Exit(cause, info) => {
                return match cause {
                    ExitCause::MatchFailure => Err(ExecError::MatchFailure(*info)),
                    ExitCause::AssertionFailure => Err(ExecError::AssertionFailure(None, *info)),
                    ExitCause::Explicit => Ok(Run::Exit),
                }
            }
        }
    }
}

/// A collector is run on the result of each path found via symbolic execution through the code. It
/// takes the result of the execution, which is either a combination of the return value and local
/// state at the end of the execution or an error, as well as the shared state and the SMT solver
/// state associated with that execution. It build a final result for all the executions by
/// collecting the results into a type R.
pub type Collector<'ir, B, R> = dyn 'ir
    + Sync
    + Fn(
        usize,
        TaskId,
        Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, LocalFrame<'ir, B>)>,
        &SharedState<'ir, B>,
        Solver<B>,
        &R,
    );

pub fn submit_itrace_for_local_frame<'ir, B: BV>(frame: &LocalFrame<'ir, B>, shared_state: &SharedState<'ir, B>) {
    submit_itrace_for_local_frame_with_diagnostics(frame, shared_state, Vec::new());
}

pub fn submit_itrace_for_local_frame_with_diagnostics<'ir, B: BV>(
    frame: &LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    diagnostics: Vec<(crate::timeout::TimeoutDiagnostic, bool)>,
) {
    let smtperf_summary = crate::smt::take_smtperf_report();
    if let Some(summary) = &smtperf_summary {
        eprint!("{}", summary);
    }
    #[cfg(feature = "tracetool")]
    {
        for (diagnostic, _) in &diagnostics {
            let dump = diagnostic.dump();
            if !dump.is_materialized() {
                dump.configure_names(frame.smt_dump_names(shared_state));
            }
        }
        let mut completed =
            crate::tracetool::itrace::ItraceCompletedPath::without_diagnostics(frame.itrace_path.clone());
        for (diagnostic, include_smt_dump) in diagnostics {
            completed.push_diagnostic_with_dump(diagnostic, include_smt_dump);
        }
        completed.set_timing(frame.path_time_snapshot());
        completed.set_smtperf_summary(smtperf_summary);
        shared_state.itrace.submit_completed_path(&completed, &shared_state.symtab);
    }
    #[cfg(not(feature = "tracetool"))]
    let _ = (frame, shared_state, diagnostics, smtperf_summary);
}

pub fn submit_itrace_for_frame<'ir, B: BV>(frame: &Frame<'ir, B>, shared_state: &SharedState<'ir, B>) {
    #[cfg(feature = "tracetool")]
    {
        let completed = crate::tracetool::itrace::ItraceCompletedPath::with_timing(
            (*frame.itrace_path).clone(),
            Vec::new(),
            frame.path_time_snapshot(),
        );
        shared_state.itrace.submit_completed_path(&completed, &shared_state.symtab);
    }
    #[cfg(not(feature = "tracetool"))]
    let _ = (frame, shared_state);
}

/// Start symbolically executing a Task using just the current thread, collecting the results using
/// the given collector.
pub fn start_single<'ir, B: BV, R>(
    task: Task<'ir, '_, B>,
    shared_state: &SharedState<'ir, B>,
    collected: &R,
    collector: &Collector<'ir, B, R>,
) {
    start_single_with_timeout(task, PathTimeout::from_seconds(None), shared_state, collected, collector);
}

fn start_single_with_timeout<'ir, B: BV, R>(
    task: Task<'ir, '_, B>,
    timeout: PathTimeout,
    shared_state: &SharedState<'ir, B>,
    collected: &R,
    collector: &Collector<'ir, B, R>,
) {
    let queue = Worker::new_lifo();
    queue.push(task);
    while let Some(mut task) = queue.pop() {
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::from_checkpoint(&ctx, task.checkpoint);
        if let Some((def, event)) = task.fork_cond {
            solver.add_event(event);
            solver.add(def)
        };
        let fork_sink = SingleForkSink { queue: &queue };
        let result = run(
            0,
            task.id,
            &mut task.fraction,
            timeout,
            task.stop_conditions,
            &fork_sink,
            &task.frame,
            task.state,
            shared_state,
            &mut solver,
        );
        collector(0, task.id, result, shared_state, solver, collected);
    }
}

fn find_task<T>(local: &Worker<T>, global: &Injector<T>, stealers: &RwLock<Vec<Stealer<T>>>) -> Option<T> {
    let stealers = stealers.read().unwrap();
    local.pop().or_else(|| {
        std::iter::repeat_with(|| {
            let stolen: Steal<T> = stealers.iter().map(|s| s.steal()).collect();
            stolen.or_else(|| global.steal_batch_and_pop(local))
        })
        .find(|s| !s.is_retry())
        .and_then(|s| s.success())
    })
}

fn do_work<'ir, 'task, B: BV, R>(
    tid: usize,
    timeout: PathTimeout,
    queue: &Worker<Task<'ir, 'task, B>>,
    mut task: Task<'ir, 'task, B>,
    shared_state: &SharedState<'ir, B>,
    collected: &R,
    collector: &Collector<'ir, B, R>,
) -> Fraction {
    let cfg = Config::new();
    let ctx = Context::new(cfg);
    let mut solver = Solver::from_checkpoint(&ctx, task.checkpoint);
    if let Some((def, event)) = task.fork_cond {
        solver.add_event(event);
        solver.add(def)
    };
    let fork_sink = SingleForkSink { queue };
    let result = run(
        tid,
        task.id,
        &mut task.fraction,
        timeout,
        task.stop_conditions,
        &fork_sink,
        &task.frame,
        task.state,
        shared_state,
        &mut solver,
    );
    collector(tid, task.id, result, shared_state, solver, collected);
    task.fraction
}

enum Response {
    Poke,
    Kill,
}

enum Progress {
    Finished { tid: usize, task_id: TaskId, frac: Fraction },
    Idle { tid: usize },
}

/// Start symbolically executing a Task across `num_threads` new threads, collecting the results
/// using the given collector.
pub fn start_multi<'ir, B: BV, R>(
    num_threads: usize,
    timeout: Option<u64>,
    tasks: Vec<Task<'ir, '_, B>>,
    shared_state: &'ir SharedState<'ir, B>,
    collected: Arc<R>,
    collector: &'ir Collector<'ir, B, R>,
) where
    B: Send + Sync,
    R: Send + Sync,
{
    let timeout = PathTimeout::from_seconds(timeout);
    if num_threads == 0 {
        for task in tasks {
            start_single_with_timeout(task, timeout, shared_state, collected.as_ref(), collector);
        }
        return;
    }

    thread::scope(|scope| {
        let runtime = Arc::new(MultiRuntime {
            limit: num_threads,
            timeout,
            active_threads: AtomicUsize::new(0),
            pending_tasks: AtomicUsize::new(0),
            next_tid: AtomicUsize::new(0),
            refill_owner: AtomicBool::new(false),
            queued_tasks: Mutex::new(VecDeque::new()),
            finished_mu: Mutex::new(()),
            finished_cv: Condvar::new(),
            shared_state,
            collected,
            collector,
        });

        for task in tasks {
            runtime.submit(scope, task);
        }

        runtime.try_refill_threads(scope);
        runtime.wait_until_finished();
    })
}

type Spawner<'ir, 'task, B, R> = dyn Fn(&R) -> Vec<Task<'ir, 'task, B>>;

pub trait Collection: Default {
    fn link_child(&self, task_id: TaskId);
    fn link_parent(&self, task_id: TaskId);
}

/// Start symbolically executing a Task across `num_threads` new
/// threads, collecting a separate result for each task.
///
/// 初始 Task 和 `spawner` 返回的 Task 都必须借用调用方持有的 `TaskState`，
/// 且该状态的生命周期必须覆盖本函数的完整执行过程。
pub fn start_multi_per_task<'ir, 'task, B: BV, R>(
    num_threads: usize,
    timeout: Option<u64>,
    tasks: Vec<Task<'ir, 'task, B>>,
    shared_state: &SharedState<'ir, B>,
    collector: &Collector<'ir, B, R>,
    spawner: &Spawner<'ir, 'task, B, R>,
) -> HashMap<TaskId, R, ahash::RandomState>
where
    R: Send + Sync + Collection,
{
    let timeout = PathTimeout::from_seconds(timeout);
    let (tx, rx): (Sender<Progress>, Receiver<Progress>) = mpsc::channel();
    let global: Arc<Injector<Task<B>>> = Arc::new(Injector::<Task<B>>::new());
    let stealers: Arc<RwLock<Vec<Stealer<Task<B>>>>> = Arc::new(RwLock::new(Vec::new()));

    let mut progress: HashMap<TaskId, Fraction, ahash::RandomState> = HashMap::default();
    let mut finished: HashSet<TaskId, ahash::RandomState> = HashSet::default();
    let mut collected_lock: RwLock<HashMap<TaskId, R, ahash::RandomState>> = RwLock::new(HashMap::default());

    for task in tasks {
        let collected = collected_lock.get_mut().unwrap();
        collected.insert(task.id, R::default());
        global.push(task);
    }

    thread::scope(|scope| {
        let mut poke_txs = Vec::new();

        for tid in 0..num_threads {
            // When a worker is idle, it reports that to the main orchestrating thread, which can
            // then 'poke' it to wake it up via a channel, which will cause the worker to try to
            // steal some work, or the main thread can kill the worker.
            let (poke_tx, poke_rx): (Sender<Response>, Receiver<Response>) = mpsc::channel();
            poke_txs.push(poke_tx.clone());

            let thread_tx = tx.clone();
            let global = global.clone();
            let stealers = stealers.clone();
            let collected_lock = &collected_lock;

            scope.spawn(move || {
                let q = Worker::new_lifo();
                {
                    let mut stealers = stealers.write().unwrap();
                    stealers.push(q.stealer());
                }
                loop {
                    while let Some(task) = find_task(&q, &global, &stealers) {
                        let task_id = task.id;
                        let collected = collected_lock.read().unwrap();
                        let task_results = collected.get(&task_id).unwrap();
                        let frac = do_work(tid, timeout, &q, task, shared_state, task_results, collector);
                        thread_tx.send(Progress::Finished { tid, task_id, frac }).unwrap();
                    }
                    thread_tx.send(Progress::Idle { tid }).unwrap();
                    match poke_rx.recv().unwrap() {
                        Response::Poke => (),
                        Response::Kill => break,
                    }
                }
            });
        }

        let mut is_idle = vec![false; num_threads];
        loop {
            loop {
                match rx.try_recv() {
                    Ok(Progress::Finished { tid, task_id, frac }) => {
                        let current_fraction = progress.entry(task_id).or_insert(Fraction::zero());
                        *current_fraction += frac;
                        is_idle[tid] = false
                    }
                    Ok(Progress::Idle { tid }) => is_idle[tid] = true,
                    Err(_) => break,
                }
            }
            // Try to wake up any idle threads
            for (tid, idle) in is_idle.iter().enumerate() {
                if *idle {
                    poke_txs[tid].send(Response::Poke).unwrap()
                }
            }
            let mut all_tasks_complete = true;
            for (task_id, frac) in progress.iter() {
                if frac.is_one() && !finished.contains(task_id) {
                    let mut collected = collected_lock.write().unwrap();
                    let task_results = collected.get(task_id).unwrap();
                    let mut new_tasks = spawner(task_results);
                    if !new_tasks.is_empty() {
                        all_tasks_complete = false;
                    };
                    for new_task in new_tasks.iter() {
                        task_results.link_child(new_task.id);
                    }
                    for new_task in new_tasks.drain(..) {
                        let results = R::default();
                        results.link_parent(*task_id);
                        collected.insert(new_task.id, results);
                        global.push(new_task);
                    }
                    finished.insert(*task_id);
                }
                if !frac.is_one() {
                    all_tasks_complete = false;
                }
            }
            if all_tasks_complete {
                for poke_tx in poke_txs.iter() {
                    poke_tx.send(Response::Kill).unwrap()
                }
                break;
            }
            thread::sleep(Duration::from_millis(1))
        }
    });

    collected_lock.into_inner().unwrap()
}

/// This `Collector` is used for boolean Sail functions. It returns
/// true via an AtomicBool if all reachable paths through the program
/// are unsatisfiable, which implies that the function always returns
/// true.
pub fn all_unsat_collector<'ir, B: BV>(
    tid: usize,
    _: TaskId,
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, LocalFrame<'ir, B>)>,
    shared_state: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    collected: &AtomicBool,
) {
    match result {
        Ok((Run::Finished(value), frame)) => {
            match value {
                Val::Symbolic(v) => {
                    use smtlib::Def::*;
                    use smtlib::Exp::*;
                    solver.add(Assert(Not(Box::new(Var(v)))));
                    match solver.check_sat(SourceLoc::unknown()) {
                        SmtResult::Unsat => log_from!(tid, log::VERBOSE, "Got unsat"),
                        SmtResult::Error(error) => {
                            let error = ExecError::Smt(error);
                            log_from!(tid, log::VERBOSE, format!("Got {}", error));
                            collected.store(false, Ordering::Release)
                        }
                        SmtResult::Sat | SmtResult::Unknown => {
                            log_from!(tid, log::VERBOSE, "Got sat");
                            collected.store(false, Ordering::Release)
                        }
                    }
                }
                Val::Bool(true) => log_from!(tid, log::VERBOSE, "Got true"),
                Val::Bool(false) => {
                    log_from!(tid, log::VERBOSE, "Got false");
                    collected.store(false, Ordering::Release)
                }
                _ => log_from!(tid, log::VERBOSE, &format!("Got value {:?}", value)),
            }
            submit_itrace_for_local_frame(&frame, shared_state);
        }
        Ok((Run::Dead, frame)) => submit_itrace_for_local_frame(&frame, shared_state),
        Ok((Run::Exit | Run::Suspended, frame)) => {
            log_from!(tid, log::VERBOSE, "Unexpected return".to_string());
            submit_itrace_for_local_frame(&frame, shared_state);
        }
        Err((err, frame)) => {
            if_logging!(log::VERBOSE, {
                log_from!(tid, log::VERBOSE, &format!("Got error, {:?}", err));
                for (f, pc) in frame.backtrace.iter().rev() {
                    log_from!(tid, log::VERBOSE, format!("  {} @ {}", shared_state.symtab.to_str(*f), pc));
                }
            });
            submit_itrace_for_local_frame(&frame, shared_state);
            collected.store(false, Ordering::Release)
        }
    }
}

#[derive(Debug)]
pub enum TraceError {
    /// This is returned when we get an unexpected value at the end of
    /// a trace, for example if we are expecting a boolean result and
    /// we get something else.
    UnexpectedValue(String),
    /// When the trace suspended itself, and we aren't expecting it
    /// to, we cannot return a complete trace.
    UnexpectedSuspension,
    /// An execution error occured when generating the trace
    Exec { err: ExecError, backtrace: String, model: Option<String> },
}

impl IslaError for TraceError {
    fn source_loc(&self) -> SourceLoc {
        match self {
            TraceError::UnexpectedValue(_) => SourceLoc::unknown(),
            TraceError::UnexpectedSuspension => SourceLoc::unknown(),
            TraceError::Exec { err, .. } => err.source_loc(),
        }
    }
}

impl fmt::Display for TraceError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TraceError::UnexpectedValue(s) => write!(f, "Unexpected value {}", s),
            TraceError::UnexpectedSuspension => write!(f, "Unexpected suspension"),
            TraceError::Exec { err, backtrace, model: Some(s) } => {
                write!(f, "{}\nBacktrace: {}\nModel: {}", err, backtrace, s)
            }
            TraceError::Exec { err, backtrace, model: None } => write!(f, "{}\nBacktrace: {}", err, backtrace),
        }
    }
}

impl TraceError {
    pub fn exec(err: ExecError, backtrace: String) -> Self {
        TraceError::Exec { err, backtrace, model: None }
    }

    fn exec_model<B: BV>(err: ExecError, backtrace: String, model: Model<B>) -> Self {
        TraceError::Exec { err, backtrace, model: Some(format!("{:?}", model)) }
    }

    fn unexpected_value<B: BV>(v: Val<B>) -> Self {
        TraceError::UnexpectedValue(format!("{:?}", v))
    }
}

pub type TraceQueue<B> = SegQueue<Result<(TaskId, Vec<Event<B>>), TraceError>>;

pub type TraceResultQueue<B> = SegQueue<Result<(TaskId, bool, Vec<Event<B>>), TraceError>>;

pub type TraceValueQueue<B> = SegQueue<Result<(TaskId, Val<B>, Vec<Event<B>>), TraceError>>;

pub fn trace_collector<'ir, B: BV>(
    tid: usize,
    task_id: TaskId,
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, LocalFrame<'ir, B>)>,
    shared_state: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    collected: &TraceQueue<B>,
) {
    solver.report_performance(shared_state.symtab.get_directory(), shared_state.symtab.files());

    match result {
        Ok((Run::Finished(_) | Run::Exit, frame)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, events.drain(..).cloned().collect())));
            submit_itrace_for_local_frame(&frame, shared_state);
        }
        Ok((Run::Suspended, frame)) => {
            collected.push(Err(TraceError::UnexpectedSuspension));
            submit_itrace_for_local_frame(&frame, shared_state);
        }
        Ok((Run::Dead, frame)) => submit_itrace_for_local_frame(&frame, shared_state),
        Err((err, frame)) => {
            log_from!(tid, log::VERBOSE, format!("Error {:?}", err));
            for (f, pc) in frame.backtrace.iter().rev() {
                log_from!(tid, log::VERBOSE, format!("  {} @ {}", shared_state.symtab.to_str(*f), pc));
            }
            let backtrace = backtrace_string(&frame.backtrace, &shared_state.symtab);
            match solver.check_sat(SourceLoc::unknown()) {
                SmtResult::Sat => {
                    let model = Model::new(&solver);
                    collected.push(Err(TraceError::exec_model(err, backtrace, model)));
                }
                SmtResult::Error(error) => {
                    let error = ExecError::Smt(error);
                    collected.push(Err(TraceError::exec(error, backtrace)))
                }
                SmtResult::Unsat | SmtResult::Unknown => collected.push(Err(TraceError::exec(err, backtrace))),
            }
            submit_itrace_for_local_frame(&frame, shared_state);
        }
    }
}

pub fn trace_value_collector<'ir, B: BV>(
    _: usize,
    task_id: TaskId,
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, LocalFrame<'ir, B>)>,
    shared_state: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    collected: &TraceValueQueue<B>,
) {
    match result {
        Ok((Run::Finished(value), frame)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, value, events.drain(..).cloned().collect())));
            submit_itrace_for_local_frame(&frame, shared_state);
        }
        Ok((Run::Exit | Run::Suspended, frame)) => submit_itrace_for_local_frame(&frame, shared_state),
        Ok((Run::Dead, frame)) => submit_itrace_for_local_frame(&frame, shared_state),
        Err((err, frame)) => {
            let backtrace = backtrace_string(&frame.backtrace, &shared_state.symtab);
            match solver.check_sat(SourceLoc::unknown()) {
                SmtResult::Sat => {
                    let model = Model::new(&solver);
                    collected.push(Err(TraceError::exec_model(err, backtrace, model)));
                }
                SmtResult::Error(error) => {
                    let error = ExecError::Smt(error);
                    collected.push(Err(TraceError::exec(error, backtrace)))
                }
                SmtResult::Unsat | SmtResult::Unknown => collected.push(Err(TraceError::exec(err, backtrace))),
            }
            submit_itrace_for_local_frame(&frame, shared_state);
        }
    }
}

pub fn trace_result_collector<'ir, B: BV>(
    _: usize,
    task_id: TaskId,
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, LocalFrame<'ir, B>)>,
    shared_state: &SharedState<'ir, B>,
    solver: Solver<B>,
    collected: &TraceResultQueue<B>,
) {
    match result {
        Ok((Run::Finished(Val::Bool(result)), frame)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, result, events.drain(..).cloned().collect())));
            submit_itrace_for_local_frame(&frame, shared_state);
        }
        Ok((Run::Exit, frame)) => submit_itrace_for_local_frame(&frame, shared_state),
        Ok((Run::Suspended, frame)) => {
            collected.push(Err(TraceError::UnexpectedSuspension));
            submit_itrace_for_local_frame(&frame, shared_state);
        }
        Ok((Run::Finished(val), frame)) => {
            collected.push(Err(TraceError::unexpected_value(val)));
            submit_itrace_for_local_frame(&frame, shared_state);
        }
        Ok((Run::Dead, frame)) => submit_itrace_for_local_frame(&frame, shared_state),
        Err((err, frame)) => {
            collected.push(Err(TraceError::exec(err, backtrace_string(&frame.backtrace, &shared_state.symtab))));
            submit_itrace_for_local_frame(&frame, shared_state);
        }
    }
}

pub fn footprint_collector<'ir, B: BV>(
    _: usize,
    task_id: TaskId,
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, LocalFrame<'ir, B>)>,
    shared_state: &SharedState<'ir, B>,
    solver: Solver<B>,
    collected: &TraceQueue<B>,
) {
    match result {
        // Footprint function returns true on traces we need to consider as part of the footprint
        Ok((Run::Finished(Val::Bool(true)), frame)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, events.drain(..).cloned().collect())));
            submit_itrace_for_local_frame(&frame, shared_state);
        }
        // If it is dead, returns false or exits, we ignore that trace
        Ok((Run::Finished(Val::Bool(false)) | Run::Exit | Run::Dead, frame)) => {
            submit_itrace_for_local_frame(&frame, shared_state)
        }
        // Any other value is an error!
        Ok((Run::Finished(value), frame)) => {
            collected.push(Err(TraceError::unexpected_value(value)));
            submit_itrace_for_local_frame(&frame, shared_state);
        }

        Ok((Run::Suspended, frame)) => {
            collected.push(Err(TraceError::UnexpectedSuspension));
            submit_itrace_for_local_frame(&frame, shared_state);
        }

        Err((err, frame)) => {
            collected.push(Err(TraceError::exec(err, backtrace_string(&frame.backtrace, &shared_state.symtab))));
            submit_itrace_for_local_frame(&frame, shared_state);
        }
    }
}

pub fn execute_ir_function<'ir, B: BV, R>(
    function_name: &str,
    args: &[Val<B>],
    shared_state: &SharedState<'ir, B>,
    regs: &RegisterBindings<'ir, B>,
    lets: &Bindings<'ir, B>,
    collected: &R,
    collector: &Collector<'ir, B, R>,
) {
    // 获取函数信息
    let function_id = shared_state.symtab.lookup(function_name);
    let (func_args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();

    // 创建初始帧
    let mut initial_frame = LocalFrame::new(function_id, func_args, ret_ty, Some(args), instrs);
    initial_frame.add_regs(regs);
    initial_frame.add_lets(lets);

    // 创建任务
    let task_state = TaskState::new();
    let task_id = TaskId::fresh();
    let task = initial_frame.task(task_id, &task_state);

    // 执行任务
    start_single(task, shared_state, collected, collector);
}

pub fn execute_ir_function_with_checkpoint<'ir, B: BV, R>(
    function_name: &str,
    args: &[Val<B>],
    shared_state: &SharedState<'ir, B>,
    regs: &RegisterBindings<'ir, B>,
    lets: &Bindings<'ir, B>,
    collected: &R,
    collector: &Collector<'ir, B, R>,
    checkpoint: Checkpoint<B>,
    initial_memory: Option<crate::memory::Memory<B>>,
) {
    // 获取函数信息
    let function_id = shared_state.symtab.lookup(function_name);
    let (func_args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();

    // 创建初始帧
    let mut initial_frame = LocalFrame::new(function_id, func_args, ret_ty, Some(args), instrs);
    initial_frame.add_regs(regs);
    initial_frame.add_lets(lets);

    if let Some(memory) = initial_memory {
        initial_frame.set_memory(memory);
    }

    // 创建任务，使用传入的checkpoint
    let task_state = TaskState::new();
    let task_id = TaskId::fresh();
    let task = initial_frame.task_with_checkpoint(task_id, &task_state, checkpoint);

    start_single(task, &shared_state, collected, collector);
}

pub fn execute_ir_function_with_checkpoint_and_limits<'ir, B: BV, R>(
    function_name: &str,
    args: &[Val<B>],
    shared_state: &SharedState<'ir, B>,
    regs: &RegisterBindings<'ir, B>,
    lets: &Bindings<'ir, B>,
    collected: &R,
    collector: &Collector<'ir, B, R>,
    checkpoint: Checkpoint<B>,
    initial_memory: Option<crate::memory::Memory<B>>,
    task_state: TaskState<B>,
) {
    // 获取函数信息
    let function_id = shared_state.symtab.lookup(function_name);
    let (func_args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();

    // 创建初始帧
    let mut initial_frame = LocalFrame::new(function_id, func_args, ret_ty, Some(args), instrs);
    initial_frame.add_regs(regs);
    initial_frame.add_lets(lets);

    if let Some(memory) = initial_memory {
        initial_frame.set_memory(memory);
    }

    // 创建任务，使用传入的checkpoint和task_state
    let task_id = TaskId::fresh();
    let task = initial_frame.task_with_checkpoint(task_id, &task_state, checkpoint);

    start_single(task, &shared_state, collected, collector);
}

pub fn execute_ir_function_with_limits<'ir, B: BV, R>(
    function_name: &str,
    args: &[Val<B>],
    shared_state: &SharedState<'ir, B>,
    regs: &RegisterBindings<'ir, B>,
    lets: &Bindings<'ir, B>,
    collected: &R,
    collector: &Collector<'ir, B, R>,
    task_state: TaskState<B>,
) {
    // 获取函数信息
    let function_id = shared_state.symtab.lookup(function_name);
    let (func_args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();

    // 创建初始帧
    let mut initial_frame = LocalFrame::new(function_id, func_args, ret_ty, Some(args), instrs);
    initial_frame.add_regs(regs);
    initial_frame.add_lets(lets);

    // 创建任务，使用传入的task_state
    let task_id = TaskId::fresh();
    let task = initial_frame.task(task_id, &task_state);

    // 执行任务
    start_single(task, shared_state, collected, collector);
}

pub fn execute_ir_function_with_checkpoint_multi_thread<'ir, B: BV, R>(
    function_name: &str,
    args: &[Val<B>],
    shared_state: &'ir SharedState<'ir, B>,
    regs: &RegisterBindings<'ir, B>,
    lets: &Bindings<'ir, B>,
    collected: &Arc<R>,
    collector: &'ir Collector<'ir, B, R>,
    checkpoint: Checkpoint<B>,
    num_threads: usize,
    timeout: Option<u64>,
    task_state: &TaskState<B>,
) where
    B: Send + Sync,
    R: Send + Sync,
{
    // 获取函数信息
    let function_id = shared_state.symtab.lookup(function_name);
    let (func_args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();

    // 创建初始帧
    let mut initial_frame = LocalFrame::new(function_id, func_args, ret_ty, Some(args), instrs);
    initial_frame.add_regs(regs);
    initial_frame.add_lets(lets);

    // handler 在本次执行会话内只读共享；所有影响路径选择的计数随 Frame 复制。
    let task_id = TaskId::fresh();
    let task = initial_frame.task_with_checkpoint(task_id, &task_state, checkpoint);

    start_multi(num_threads, timeout, vec![task], &shared_state, collected.clone(), collector);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{ISAConfig, Tool};
    use std::path::PathBuf;

    const REAL_RV64D_ZRX_IR: &str = r#"
val zz5i64zDzKz5i = "%i64->%i" : (%i64) ->  %i

val zeq_int = "eq_int" : (%i, %i) ->  %bool

val zsail_zzeros = "zeros" : (%i) ->  %bv

val zsail_ones : (%i) ->  %bv

val zzzeros : (%i) ->  %bv

fn zzzeros(zn) {
  return = zsail_zzeros(zn) `14 93:21-93:34;
  end;
}

let (zzzero_reg: %bv64) {
  zz40 : %bv64 `34 13:25-13:32;
  zz41 : %i `34 13:25-13:32;
  zz41 = zz5i64zDzKz5i(64) `34 13:25-13:32;
  zz42 : %bv `34 13:25-13:32;
  zz42 = zzzeros(zz41) `34 13:25-13:32;
  zz40 = zz42 `34 13:25-13:32;
  zzzero_reg = zz40 `34 13:4-13:12;
}

val zregval_from_reg : (%bv64) ->  %bv64

fn zregval_from_reg(zr) {
  return = zr `34 20:52-20:53;
  end;
}

register zx1 : %bv64

register zx2 : %bv64

register zx3 : %bv64

register zx4 : %bv64

register zx5 : %bv64

register zx6 : %bv64

register zx7 : %bv64

register zx8 : %bv64

register zx9 : %bv64

register zx10 : %bv64

register zx11 : %bv64

register zx12 : %bv64

register zx13 : %bv64

register zx14 : %bv64

register zx15 : %bv64

register zx16 : %bv64

register zx17 : %bv64

register zx18 : %bv64

register zx19 : %bv64

register zx20 : %bv64

register zx21 : %bv64

register zx22 : %bv64

register zx23 : %bv64

register zx24 : %bv64

register zx25 : %bv64

register zx26 : %bv64

register zx27 : %bv64

register zx28 : %bv64

register zx29 : %bv64

register zx30 : %bv64

register zx31 : %bv64

val zrX : (%i64) ->  %bv64

fn zrX(z3zE1756) {
  zz40 : %i64 `35 151:19-151:20;
  zz40 = z3zE1756 `35 151:19-151:20;
  zz41 : %bv64 `35 152:2-187:20;
  zz42 : %bv64 `35 153:4-186:5;
  zz43 : %i64 `35 154:6-154:7;
  zz43 = zz40 `35 154:6-154:7;
  zz44 : %i `2931;
  zz44 = zz5i64zDzKz5i(0) `2932;
  zz45 : %bool `35 153:4-186:5;
  zz46 : %i `2933;
  zz46 = zz5i64zDzKz5i(zz43) `2934;
  zz45 = zeq_int(zz46, zz44) `2935;
  jump @not(zz45) goto 14 `35 153:4-186:5;
  goto 15;
  goto 17;
  zz42 = zzzero_reg `35 154:11-154:19;
  goto 408;
  zz47 : %i64 `35 155:6-155:7;
  zz47 = zz40 `35 155:6-155:7;
  zz48 : %i `2936;
  zz48 = zz5i64zDzKz5i(1) `2937;
  zz49 : %bool `35 153:4-186:5;
  zz410 : %i `2938;
  zz410 = zz5i64zDzKz5i(zz47) `2939;
  zz49 = zeq_int(zz410, zz48) `2940;
  jump @not(zz49) goto 27 `35 153:4-186:5;
  goto 28;
  goto 30;
  zz42 = zx1 `35 155:11-155:13;
  goto 408;
  zz411 : %i64 `35 156:6-156:7;
  zz411 = zz40 `35 156:6-156:7;
  zz412 : %i `2941;
  zz412 = zz5i64zDzKz5i(2) `2942;
  zz413 : %bool `35 153:4-186:5;
  zz414 : %i `2943;
  zz414 = zz5i64zDzKz5i(zz411) `2944;
  zz413 = zeq_int(zz414, zz412) `2945;
  jump @not(zz413) goto 40 `35 153:4-186:5;
  goto 41;
  goto 43;
  zz42 = zx2 `35 156:11-156:13;
  goto 408;
  zz415 : %i64 `35 157:6-157:7;
  zz415 = zz40 `35 157:6-157:7;
  zz416 : %i `2946;
  zz416 = zz5i64zDzKz5i(3) `2947;
  zz417 : %bool `35 153:4-186:5;
  zz418 : %i `2948;
  zz418 = zz5i64zDzKz5i(zz415) `2949;
  zz417 = zeq_int(zz418, zz416) `2950;
  jump @not(zz417) goto 53 `35 153:4-186:5;
  goto 54;
  goto 56;
  zz42 = zx3 `35 157:11-157:13;
  goto 408;
  zz419 : %i64 `35 158:6-158:7;
  zz419 = zz40 `35 158:6-158:7;
  zz420 : %i `2951;
  zz420 = zz5i64zDzKz5i(4) `2952;
  zz421 : %bool `35 153:4-186:5;
  zz422 : %i `2953;
  zz422 = zz5i64zDzKz5i(zz419) `2954;
  zz421 = zeq_int(zz422, zz420) `2955;
  jump @not(zz421) goto 66 `35 153:4-186:5;
  goto 67;
  goto 69;
  zz42 = zx4 `35 158:11-158:13;
  goto 408;
  zz423 : %i64 `35 159:6-159:7;
  zz423 = zz40 `35 159:6-159:7;
  zz424 : %i `2956;
  zz424 = zz5i64zDzKz5i(5) `2957;
  zz425 : %bool `35 153:4-186:5;
  zz426 : %i `2958;
  zz426 = zz5i64zDzKz5i(zz423) `2959;
  zz425 = zeq_int(zz426, zz424) `2960;
  jump @not(zz425) goto 79 `35 153:4-186:5;
  goto 80;
  goto 82;
  zz42 = zx5 `35 159:11-159:13;
  goto 408;
  zz427 : %i64 `35 160:6-160:7;
  zz427 = zz40 `35 160:6-160:7;
  zz428 : %i `2961;
  zz428 = zz5i64zDzKz5i(6) `2962;
  zz429 : %bool `35 153:4-186:5;
  zz430 : %i `2963;
  zz430 = zz5i64zDzKz5i(zz427) `2964;
  zz429 = zeq_int(zz430, zz428) `2965;
  jump @not(zz429) goto 92 `35 153:4-186:5;
  goto 93;
  goto 95;
  zz42 = zx6 `35 160:11-160:13;
  goto 408;
  zz431 : %i64 `35 161:6-161:7;
  zz431 = zz40 `35 161:6-161:7;
  zz432 : %i `2966;
  zz432 = zz5i64zDzKz5i(7) `2967;
  zz433 : %bool `35 153:4-186:5;
  zz434 : %i `2968;
  zz434 = zz5i64zDzKz5i(zz431) `2969;
  zz433 = zeq_int(zz434, zz432) `2970;
  jump @not(zz433) goto 105 `35 153:4-186:5;
  goto 106;
  goto 108;
  zz42 = zx7 `35 161:11-161:13;
  goto 408;
  zz435 : %i64 `35 162:6-162:7;
  zz435 = zz40 `35 162:6-162:7;
  zz436 : %i `2971;
  zz436 = zz5i64zDzKz5i(8) `2972;
  zz437 : %bool `35 153:4-186:5;
  zz438 : %i `2973;
  zz438 = zz5i64zDzKz5i(zz435) `2974;
  zz437 = zeq_int(zz438, zz436) `2975;
  jump @not(zz437) goto 118 `35 153:4-186:5;
  goto 119;
  goto 121;
  zz42 = zx8 `35 162:11-162:13;
  goto 408;
  zz439 : %i64 `35 163:6-163:7;
  zz439 = zz40 `35 163:6-163:7;
  zz440 : %i `2976;
  zz440 = zz5i64zDzKz5i(9) `2977;
  zz441 : %bool `35 153:4-186:5;
  zz442 : %i `2978;
  zz442 = zz5i64zDzKz5i(zz439) `2979;
  zz441 = zeq_int(zz442, zz440) `2980;
  jump @not(zz441) goto 131 `35 153:4-186:5;
  goto 132;
  goto 134;
  zz42 = zx9 `35 163:11-163:13;
  goto 408;
  zz443 : %i64 `35 164:6-164:8;
  zz443 = zz40 `35 164:6-164:8;
  zz444 : %i `2981;
  zz444 = zz5i64zDzKz5i(10) `2982;
  zz445 : %bool `35 153:4-186:5;
  zz446 : %i `2983;
  zz446 = zz5i64zDzKz5i(zz443) `2984;
  zz445 = zeq_int(zz446, zz444) `2985;
  jump @not(zz445) goto 144 `35 153:4-186:5;
  goto 145;
  goto 147;
  zz42 = zx10 `35 164:12-164:15;
  goto 408;
  zz447 : %i64 `35 165:6-165:8;
  zz447 = zz40 `35 165:6-165:8;
  zz448 : %i `2986;
  zz448 = zz5i64zDzKz5i(11) `2987;
  zz449 : %bool `35 153:4-186:5;
  zz450 : %i `2988;
  zz450 = zz5i64zDzKz5i(zz447) `2989;
  zz449 = zeq_int(zz450, zz448) `2990;
  jump @not(zz449) goto 157 `35 153:4-186:5;
  goto 158;
  goto 160;
  zz42 = zx11 `35 165:12-165:15;
  goto 408;
  zz451 : %i64 `35 166:6-166:8;
  zz451 = zz40 `35 166:6-166:8;
  zz452 : %i `2991;
  zz452 = zz5i64zDzKz5i(12) `2992;
  zz453 : %bool `35 153:4-186:5;
  zz454 : %i `2993;
  zz454 = zz5i64zDzKz5i(zz451) `2994;
  zz453 = zeq_int(zz454, zz452) `2995;
  jump @not(zz453) goto 170 `35 153:4-186:5;
  goto 171;
  goto 173;
  zz42 = zx12 `35 166:12-166:15;
  goto 408;
  zz455 : %i64 `35 167:6-167:8;
  zz455 = zz40 `35 167:6-167:8;
  zz456 : %i `2996;
  zz456 = zz5i64zDzKz5i(13) `2997;
  zz457 : %bool `35 153:4-186:5;
  zz458 : %i `2998;
  zz458 = zz5i64zDzKz5i(zz455) `2999;
  zz457 = zeq_int(zz458, zz456) `3000;
  jump @not(zz457) goto 183 `35 153:4-186:5;
  goto 184;
  goto 186;
  zz42 = zx13 `35 167:12-167:15;
  goto 408;
  zz459 : %i64 `35 168:6-168:8;
  zz459 = zz40 `35 168:6-168:8;
  zz460 : %i `3001;
  zz460 = zz5i64zDzKz5i(14) `3002;
  zz461 : %bool `35 153:4-186:5;
  zz462 : %i `3003;
  zz462 = zz5i64zDzKz5i(zz459) `3004;
  zz461 = zeq_int(zz462, zz460) `3005;
  jump @not(zz461) goto 196 `35 153:4-186:5;
  goto 197;
  goto 199;
  zz42 = zx14 `35 168:12-168:15;
  goto 408;
  zz463 : %i64 `35 169:6-169:8;
  zz463 = zz40 `35 169:6-169:8;
  zz464 : %i `3006;
  zz464 = zz5i64zDzKz5i(15) `3007;
  zz465 : %bool `35 153:4-186:5;
  zz466 : %i `3008;
  zz466 = zz5i64zDzKz5i(zz463) `3009;
  zz465 = zeq_int(zz466, zz464) `3010;
  jump @not(zz465) goto 209 `35 153:4-186:5;
  goto 210;
  goto 212;
  zz42 = zx15 `35 169:12-169:15;
  goto 408;
  zz467 : %i64 `35 170:6-170:8;
  zz467 = zz40 `35 170:6-170:8;
  zz468 : %i `3011;
  zz468 = zz5i64zDzKz5i(16) `3012;
  zz469 : %bool `35 153:4-186:5;
  zz470 : %i `3013;
  zz470 = zz5i64zDzKz5i(zz467) `3014;
  zz469 = zeq_int(zz470, zz468) `3015;
  jump @not(zz469) goto 222 `35 153:4-186:5;
  goto 223;
  goto 225;
  zz42 = zx16 `35 170:12-170:15;
  goto 408;
  zz471 : %i64 `35 171:6-171:8;
  zz471 = zz40 `35 171:6-171:8;
  zz472 : %i `3016;
  zz472 = zz5i64zDzKz5i(17) `3017;
  zz473 : %bool `35 153:4-186:5;
  zz474 : %i `3018;
  zz474 = zz5i64zDzKz5i(zz471) `3019;
  zz473 = zeq_int(zz474, zz472) `3020;
  jump @not(zz473) goto 235 `35 153:4-186:5;
  goto 236;
  goto 238;
  zz42 = zx17 `35 171:12-171:15;
  goto 408;
  zz475 : %i64 `35 172:6-172:8;
  zz475 = zz40 `35 172:6-172:8;
  zz476 : %i `3021;
  zz476 = zz5i64zDzKz5i(18) `3022;
  zz477 : %bool `35 153:4-186:5;
  zz478 : %i `3023;
  zz478 = zz5i64zDzKz5i(zz475) `3024;
  zz477 = zeq_int(zz478, zz476) `3025;
  jump @not(zz477) goto 248 `35 153:4-186:5;
  goto 249;
  goto 251;
  zz42 = zx18 `35 172:12-172:15;
  goto 408;
  zz479 : %i64 `35 173:6-173:8;
  zz479 = zz40 `35 173:6-173:8;
  zz480 : %i `3026;
  zz480 = zz5i64zDzKz5i(19) `3027;
  zz481 : %bool `35 153:4-186:5;
  zz482 : %i `3028;
  zz482 = zz5i64zDzKz5i(zz479) `3029;
  zz481 = zeq_int(zz482, zz480) `3030;
  jump @not(zz481) goto 261 `35 153:4-186:5;
  goto 262;
  goto 264;
  zz42 = zx19 `35 173:12-173:15;
  goto 408;
  zz483 : %i64 `35 174:6-174:8;
  zz483 = zz40 `35 174:6-174:8;
  zz484 : %i `3031;
  zz484 = zz5i64zDzKz5i(20) `3032;
  zz485 : %bool `35 153:4-186:5;
  zz486 : %i `3033;
  zz486 = zz5i64zDzKz5i(zz483) `3034;
  zz485 = zeq_int(zz486, zz484) `3035;
  jump @not(zz485) goto 274 `35 153:4-186:5;
  goto 275;
  goto 277;
  zz42 = zx20 `35 174:12-174:15;
  goto 408;
  zz487 : %i64 `35 175:6-175:8;
  zz487 = zz40 `35 175:6-175:8;
  zz488 : %i `3036;
  zz488 = zz5i64zDzKz5i(21) `3037;
  zz489 : %bool `35 153:4-186:5;
  zz490 : %i `3038;
  zz490 = zz5i64zDzKz5i(zz487) `3039;
  zz489 = zeq_int(zz490, zz488) `3040;
  jump @not(zz489) goto 287 `35 153:4-186:5;
  goto 288;
  goto 290;
  zz42 = zx21 `35 175:12-175:15;
  goto 408;
  zz491 : %i64 `35 176:6-176:8;
  zz491 = zz40 `35 176:6-176:8;
  zz492 : %i `3041;
  zz492 = zz5i64zDzKz5i(22) `3042;
  zz493 : %bool `35 153:4-186:5;
  zz494 : %i `3043;
  zz494 = zz5i64zDzKz5i(zz491) `3044;
  zz493 = zeq_int(zz494, zz492) `3045;
  jump @not(zz493) goto 300 `35 153:4-186:5;
  goto 301;
  goto 303;
  zz42 = zx22 `35 176:12-176:15;
  goto 408;
  zz495 : %i64 `35 177:6-177:8;
  zz495 = zz40 `35 177:6-177:8;
  zz496 : %i `3046;
  zz496 = zz5i64zDzKz5i(23) `3047;
  zz497 : %bool `35 153:4-186:5;
  zz498 : %i `3048;
  zz498 = zz5i64zDzKz5i(zz495) `3049;
  zz497 = zeq_int(zz498, zz496) `3050;
  jump @not(zz497) goto 313 `35 153:4-186:5;
  goto 314;
  goto 316;
  zz42 = zx23 `35 177:12-177:15;
  goto 408;
  zz499 : %i64 `35 178:6-178:8;
  zz499 = zz40 `35 178:6-178:8;
  zz4100 : %i `3051;
  zz4100 = zz5i64zDzKz5i(24) `3052;
  zz4101 : %bool `35 153:4-186:5;
  zz4102 : %i `3053;
  zz4102 = zz5i64zDzKz5i(zz499) `3054;
  zz4101 = zeq_int(zz4102, zz4100) `3055;
  jump @not(zz4101) goto 326 `35 153:4-186:5;
  goto 327;
  goto 329;
  zz42 = zx24 `35 178:12-178:15;
  goto 408;
  zz4103 : %i64 `35 179:6-179:8;
  zz4103 = zz40 `35 179:6-179:8;
  zz4104 : %i `3056;
  zz4104 = zz5i64zDzKz5i(25) `3057;
  zz4105 : %bool `35 153:4-186:5;
  zz4106 : %i `3058;
  zz4106 = zz5i64zDzKz5i(zz4103) `3059;
  zz4105 = zeq_int(zz4106, zz4104) `3060;
  jump @not(zz4105) goto 339 `35 153:4-186:5;
  goto 340;
  goto 342;
  zz42 = zx25 `35 179:12-179:15;
  goto 408;
  zz4107 : %i64 `35 180:6-180:8;
  zz4107 = zz40 `35 180:6-180:8;
  zz4108 : %i `3061;
  zz4108 = zz5i64zDzKz5i(26) `3062;
  zz4109 : %bool `35 153:4-186:5;
  zz4110 : %i `3063;
  zz4110 = zz5i64zDzKz5i(zz4107) `3064;
  zz4109 = zeq_int(zz4110, zz4108) `3065;
  jump @not(zz4109) goto 352 `35 153:4-186:5;
  goto 353;
  goto 355;
  zz42 = zx26 `35 180:12-180:15;
  goto 408;
  zz4111 : %i64 `35 181:6-181:8;
  zz4111 = zz40 `35 181:6-181:8;
  zz4112 : %i `3066;
  zz4112 = zz5i64zDzKz5i(27) `3067;
  zz4113 : %bool `35 153:4-186:5;
  zz4114 : %i `3068;
  zz4114 = zz5i64zDzKz5i(zz4111) `3069;
  zz4113 = zeq_int(zz4114, zz4112) `3070;
  jump @not(zz4113) goto 365 `35 153:4-186:5;
  goto 366;
  goto 368;
  zz42 = zx27 `35 181:12-181:15;
  goto 408;
  zz4115 : %i64 `35 182:6-182:8;
  zz4115 = zz40 `35 182:6-182:8;
  zz4116 : %i `3071;
  zz4116 = zz5i64zDzKz5i(28) `3072;
  zz4117 : %bool `35 153:4-186:5;
  zz4118 : %i `3073;
  zz4118 = zz5i64zDzKz5i(zz4115) `3074;
  zz4117 = zeq_int(zz4118, zz4116) `3075;
  jump @not(zz4117) goto 378 `35 153:4-186:5;
  goto 379;
  goto 381;
  zz42 = zx28 `35 182:12-182:15;
  goto 408;
  zz4119 : %i64 `35 183:6-183:8;
  zz4119 = zz40 `35 183:6-183:8;
  zz4120 : %i `3076;
  zz4120 = zz5i64zDzKz5i(29) `3077;
  zz4121 : %bool `35 153:4-186:5;
  zz4122 : %i `3078;
  zz4122 = zz5i64zDzKz5i(zz4119) `3079;
  zz4121 = zeq_int(zz4122, zz4120) `3080;
  jump @not(zz4121) goto 391 `35 153:4-186:5;
  goto 392;
  goto 394;
  zz42 = zx29 `35 183:12-183:15;
  goto 408;
  zz4123 : %i64 `35 184:6-184:8;
  zz4123 = zz40 `35 184:6-184:8;
  zz4124 : %i `3081;
  zz4124 = zz5i64zDzKz5i(30) `3082;
  zz4125 : %bool `35 153:4-186:5;
  zz4126 : %i `3083;
  zz4126 = zz5i64zDzKz5i(zz4123) `3084;
  zz4125 = zeq_int(zz4126, zz4124) `3085;
  jump @not(zz4125) goto 404 `35 153:4-186:5;
  goto 405;
  goto 407;
  zz42 = zx30 `35 184:12-184:15;
  goto 408;
  zz42 = zx31 `35 185:12-185:15;
  zz41 = zz42 `35 153:4-186:5;
  return = zregval_from_reg(zz41) `35 187:2-187:20;
  end;
}
"#;

    fn info() -> SourceLoc {
        SourceLoc::unknown()
    }

    fn test_name(id: u32) -> Name {
        Name::from_u32(id)
    }

    fn shared_state_from_defs<'ir>(defs: Vec<crate::ir::Def<Name, B64>>) -> SharedState<'ir, B64> {
        let symtab = Symtab::new();
        let defs: &'ir [crate::ir::Def<Name, B64>] = Box::leak(defs.into_boxed_slice());
        let type_info = IRTypeInfo::new(defs);
        SharedState::new(
            symtab,
            defs,
            type_info,
            HashSet::new(),
            HashSet::new(),
            HashSet::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
    }

    fn parse_ir_string(ir: &'static str) -> (Symtab<'static>, Vec<crate::ir::Def<Name, B64>>) {
        let mut symtab = Symtab::new();
        let defs = crate::ir_parser::IrParser::new()
            .parse(&mut symtab, crate::ir_lexer::new_ir_lexer(ir))
            .expect("IR parse failed");
        (symtab, defs)
    }

    fn empty_tool() -> Tool {
        Tool { executable: PathBuf::new(), options: Vec::new() }
    }

    fn empty_isa_config() -> ISAConfig<B64> {
        ISAConfig {
            pc: Name::from_u32(u32::MAX),
            register_event_sets: HashMap::new(),
            assembler: empty_tool(),
            objdump: empty_tool(),
            nm: empty_tool(),
            linker: empty_tool(),
            page_table_base: 0,
            page_size: 0,
            s2_page_table_base: 0,
            s2_page_size: 0,
            default_page_table_setup: String::new(),
            thread_base: 0,
            thread_top: 0,
            thread_stride: 0,
            symbolic_addr_base: 0,
            symbolic_addr_top: 0,
            symbolic_addr_stride: 0,
            default_registers: HashMap::new(),
            reset_registers: Vec::new(),
            reset_constraints: Vec::new(),
            const_primops: HashMap::new(),
            function_assumptions: Vec::new(),
            register_renames: HashMap::new(),
            ignored_registers: HashSet::new(),
            relaxed_registers: HashSet::new(),
            probes: HashSet::new(),
            probe_functions: HashSet::new(),
            trace_functions: HashSet::new(),
            translation_function: None,
            in_program_order: HashSet::new(),
            default_sizeof: 0,
            zero_announce_exit: false,
            memory_regions: None,
            page_table_config: None,
            pmp: None,
            clint_enabled: None,
            execution_limits: None,
        }
    }

    #[cfg(feature = "tracetool")]
    fn itrace_fixture_shared_state() -> SharedState<'static, B64> {
        const IR_FIXTURE: &str = include_str!("../tests/fixtures/ir_cache_assumption.ir");
        let (symtab, defs) = parse_ir_string(IR_FIXTURE);
        let defs: &'static [crate::ir::Def<Name, B64>] = Box::leak(defs.into_boxed_slice());
        let type_info = IRTypeInfo::new(defs);
        let shared_state = SharedState::new(
            symtab,
            defs,
            type_info,
            HashSet::new(),
            HashSet::new(),
            HashSet::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
        let ir_path = PathBuf::from(manifest_dir).join("tests/fixtures/ir_cache_assumption.ir");
        shared_state.itrace.configure("itrace test title", ir_path, None, &shared_state.symtab);
        shared_state
    }

    #[cfg(feature = "tracetool")]
    #[test]
    fn itrace_branch_condition_macros_record_current_and_forked_paths() {
        let shared_state = itrace_fixture_shared_state();
        let temp_dir = std::env::temp_dir();
        let output_path = temp_dir.join(format!(
            "itrace_branch_condition_macro_test_{}_{}.txt",
            std::process::id(),
            std::thread::current().name().unwrap_or("unnamed")
        ));
        let _ = std::fs::remove_file(&output_path);
        shared_state.itrace.set_path(Some(output_path.clone()));

        let instrs: Vec<Instr<Name, B64>> = Vec::new();
        let function = shared_state.symtab.lookup("zcache_ok");
        let mut frame = LocalFrame::new(function, &[], &Ty::Unit, None, &instrs);
        frame.itrace_path.record(function, Vec::new(), 0);

        itrace_push_branch_condition!(&mut frame, smtlib::Exp::<Sym>::Bool(true));
        let forked = itrace_fork_frame_with_branch_condition!(&frame, 7, smtlib::Exp::<Sym>::Bool(false));

        assert_eq!(forked.pc, 7);

        submit_itrace_for_local_frame(&frame, &shared_state);
        submit_itrace_for_frame(&forked, &shared_state);
        shared_state.itrace.dump();

        let content = std::fs::read_to_string(&output_path).expect("read macro itrace output");
        assert_eq!(content.matches("<itrace test title> path").count(), 2);
        assert!(content.contains("<itrace test title> path(itrace test title_branch_true):"));
        assert!(content.contains("<itrace test title> path(itrace test title_branch_true_false):"));

        let _ = std::fs::remove_file(&output_path);
    }

    #[cfg(feature = "tracetool")]
    #[test]
    fn itrace_submit_for_local_frame_writes_rendered_path_text() {
        let shared_state = itrace_fixture_shared_state();
        let temp_dir = std::env::temp_dir();
        let output_path = temp_dir.join(format!("itrace_submit_executor_test_{}.txt", std::process::id()));
        let _ = std::fs::remove_file(&output_path);
        shared_state.itrace.set_path(Some(output_path.clone()));

        let instrs: Vec<Instr<Name, B64>> = Vec::new();
        let mut frame = LocalFrame::new(shared_state.symtab.lookup("zcache_ok"), &[], &Ty::Unit, None, &instrs);
        frame.itrace_path.record(shared_state.symtab.lookup("zcache_ok"), Vec::new(), 3);

        submit_itrace_for_local_frame(&frame, &shared_state);
        shared_state.itrace.dump();

        let content = std::fs::read_to_string(&output_path).expect("read itrace submit output");
        assert!(content.contains("itrace test title"));
        assert!(content.contains("return = z1"));

        let _ = std::fs::remove_file(&output_path);
    }

    #[cfg(feature = "tracetool")]
    #[test]
    fn itrace_submit_for_frame_preserves_frozen_path_and_branch_conditions() {
        let shared_state = itrace_fixture_shared_state();
        let temp_dir = std::env::temp_dir();
        let output_path = temp_dir.join(format!(
            "itrace_integration_executor_test_{}_{}.txt",
            std::process::id(),
            std::thread::current().name().unwrap_or("unnamed")
        ));
        let _ = std::fs::remove_file(&output_path);
        shared_state.itrace.set_path(Some(output_path.clone()));

        let instrs: Vec<Instr<Name, B64>> = Vec::new();
        let zcache_ok = shared_state.symtab.lookup("zcache_ok");
        let zpc_lookup = shared_state.symtab.lookup("zpc_lookup");

        let mut first_frame = LocalFrame::new(zcache_ok, &[], &Ty::Unit, None, &instrs);
        first_frame.itrace_path.push_branch_condition(smtlib::Exp::<Sym>::Bool(true));
        first_frame.itrace_path.record(zcache_ok, Vec::new(), 0);
        first_frame.itrace_path.record(zcache_ok, Vec::new(), 3);

        let mut error_like_frame = LocalFrame::new(zpc_lookup, &[], &Ty::Unit, None, &instrs);
        error_like_frame.itrace_path.push_branch_condition(smtlib::Exp::<Sym>::Bool(false));
        error_like_frame.itrace_path.record(zpc_lookup, Vec::new(), 1);
        error_like_frame.itrace_path.record(zpc_lookup, Vec::new(), 5);
        let frozen_error_like_frame = freeze_frame(&error_like_frame);

        submit_itrace_for_local_frame(&first_frame, &shared_state);
        submit_itrace_for_frame(&frozen_error_like_frame, &shared_state);
        shared_state.itrace.dump();

        let content = std::fs::read_to_string(&output_path).expect("read itrace integration output");

        assert_eq!(content.matches("<itrace test title> path").count(), 2);
        assert!(content.contains("<itrace test title> path(itrace test title_branch_true):"));
        assert!(content.contains("<itrace test title> path(itrace test title_branch_false):"));
        assert!(!content.contains("branch_conditions"));
        assert!(!content.contains("Bool"));
        assert!(content.contains("z0 : %i"));
        assert!(content.contains("return = z1"));
        assert!(content.contains("p1 : %i"));
        assert!(content.contains("end"));
        assert!(!content.contains("`1"));
        assert!(!content.contains("`4"));
        assert!(!content.contains("`11"));

        let title_prefix = "<itrace test title> path";
        let first_title = content.find(title_prefix).expect("first path title missing");
        let second_title = content[first_title + 1..]
            .find(title_prefix)
            .map(|offset| first_title + 1 + offset)
            .expect("second path title missing");
        assert!(content[first_title..second_title].contains("z0 : %i"));
        assert!(content[first_title..second_title].contains("return = z1"));
        assert!(content[second_title..].contains("p1 : %i"));
        assert!(content[second_title..].contains("end"));

        let _ = std::fs::remove_file(&output_path);
    }

    #[cfg(feature = "tracetool")]
    #[test]
    fn itrace_integration_run_loop_collector_writes_executed_path() {
        let shared_state = itrace_fixture_shared_state();
        let temp_dir = std::env::temp_dir();
        let output_path = temp_dir.join(format!("itrace_run_loop_collector_test_{}.txt", std::process::id()));
        let _ = std::fs::remove_file(&output_path);
        shared_state.itrace.set_path(Some(output_path.clone()));

        let function = shared_state.symtab.lookup("zcache_ok");
        let (args, ret_ty, instrs) = shared_state.functions.get(&function).expect("fixture function exists");
        let initial_frame = LocalFrame::new(function, args, ret_ty, None, instrs);
        let task_state = TaskState::new();
        let task = initial_frame.task(TaskId::fresh(), &task_state);
        let collected = AtomicBool::new(true);

        start_single_with_timeout(
            task,
            PathTimeout::from_seconds(None),
            &shared_state,
            &collected,
            &all_unsat_collector,
        );
        shared_state.itrace.dump();

        let content = std::fs::read_to_string(&output_path).expect("read run_loop itrace output");
        assert!(content.contains("itrace test title"));
        assert!(content.contains("z0 : %i"));
        assert!(content.contains("z1 : %i"));
        assert!(content.contains("z1 = z0(zu)"));
        assert!(!content.contains('`'));
        assert!(!content.contains("branch_conditions"));

        let _ = std::fs::remove_file(&output_path);
    }

    fn shared_state_and_bindings_from_ir(
        ir: &'static str,
    ) -> (SharedState<'static, B64>, RegisterBindings<'static, B64>, Bindings<'static, B64>) {
        let (symtab, mut defs) = parse_ir_string(ir);
        crate::ir::insert_primops(&mut defs, crate::ir::AssertionMode::Optimistic, &empty_isa_config());
        let defs: &'static [crate::ir::Def<Name, B64>] = Box::leak(defs.into_boxed_slice());
        let type_info = IRTypeInfo::new(defs);
        let shared_state = SharedState::new(
            symtab,
            defs,
            type_info,
            HashSet::new(),
            HashSet::new(),
            HashSet::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        let mut regs = RegisterBindings::new();
        let mut lets = HashMap::default();
        for def in defs {
            match def {
                crate::ir::Def::Register(id, ty, _) => regs.insert(*id, false, UVal::Uninit(ty)),
                crate::ir::Def::Let(bindings, setup) => {
                    let vars: Vec<_> = bindings.iter().map(|(id, ty)| (*id, ty)).collect();
                    let mut frame = LocalFrame::new(TOP_LEVEL_LET, &vars, &Ty::Unit, None, setup);
                    frame.add_regs(&regs).add_lets(&lets);
                    let task_state = TaskState::new();
                    let queue = Worker::new_lifo();
                    let mut task_fraction = Fraction::one();
                    let ctx = Context::new(Config::new());
                    let mut solver = Solver::new(&ctx);
                    run_loop(
                        0,
                        TaskId::fresh(),
                        &mut task_fraction,
                        PathTimeout::unlimited(),
                        None,
                        &SingleForkSink { queue: &queue },
                        &mut frame,
                        &task_state,
                        &shared_state,
                        &mut solver,
                    )
                    .expect("IR let 初始化失败");
                    for (id, _) in bindings.iter() {
                        let value = frame.vars().get(id).expect("let 绑定缺少返回值").clone();
                        lets.insert(*id, value);
                    }
                }
                _ => (),
            }
        }
        (shared_state, regs, lets)
    }

    fn real_zrx_program(
    ) -> (Vec<Instr<Name, B64>>, SharedState<'static, B64>, RegisterBindings<'static, B64>, Bindings<'static, B64>)
    {
        let (mut shared_state, regs, lets) = shared_state_and_bindings_from_ir(REAL_RV64D_ZRX_IR);
        let arg = shared_state.symtab.intern("zz_arg");
        let result = shared_state.symtab.intern("zz_result");
        let zrx = shared_state.symtab.lookup("zrX");
        let instrs = vec![
            Instr::Init(arg, Ty::I64, Exp::Undefined(Ty::I64), info()),
            Instr::Decl(result, Ty::Bits(64), info()),
            Instr::Call(Loc::Id(result), false, zrx, vec![Exp::Id(arg)], info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(result), info()),
            Instr::End,
        ];
        (instrs, shared_state, regs, lets)
    }

    fn make_frame_with_bindings<'ir>(
        instrs: Vec<Instr<Name, B64>>,
        regs: &RegisterBindings<'ir, B64>,
        lets: &Bindings<'ir, B64>,
    ) -> LocalFrame<'ir, B64> {
        let instrs: &'ir [Instr<Name, B64>] = Box::leak(instrs.into_boxed_slice());
        let ret_ty: &'ir Ty<Name> = Box::leak(Box::new(Ty::Unit));
        let mut frame = LocalFrame::new(test_name(25), &[], ret_ty, None, instrs);
        frame.add_regs(regs).add_lets(lets);
        frame
    }

    fn run_all_with_bindings<'ir>(
        instrs: Vec<Instr<Name, B64>>,
        limits: ExecutionLimits,
        shared_state: SharedState<'ir, B64>,
        regs: RegisterBindings<'ir, B64>,
        lets: Bindings<'ir, B64>,
    ) -> Vec<Result<Run<B64>, ExecError>> {
        let frame = make_frame_with_bindings(instrs, &regs, &lets);
        let task_state = TaskState::new().with_execution_limits(limits);
        let queue = Worker::new_lifo();
        queue.push(frame.task(TaskId::from_usize(0), &task_state));
        let mut results = Vec::new();

        while let Some(mut task) = queue.pop() {
            let mut cfg = Config::new();
            cfg.set_param_value("model", "true");
            let ctx = Context::new(cfg);
            let mut solver = Solver::from_checkpoint(&ctx, task.checkpoint);
            if let Some((def, event)) = task.fork_cond {
                solver.add_event(event);
                solver.add(def);
            }
            let mut task_frame = unfreeze_frame(&task.frame);
            results.push(run_loop(
                0,
                task.id,
                &mut task.fraction,
                PathTimeout::unlimited(),
                task.stop_conditions,
                &SingleForkSink { queue: &queue },
                &mut task_frame,
                task.state,
                &shared_state,
                &mut solver,
            ));
        }

        results
    }

    fn empty_shared_state<'ir>() -> SharedState<'ir, B64> {
        shared_state_from_defs(Vec::new())
    }

    fn make_frame<'ir>(instrs: Vec<Instr<Name, B64>>) -> LocalFrame<'ir, B64> {
        let instrs: &'ir [Instr<Name, B64>] = Box::leak(instrs.into_boxed_slice());
        let ret_ty: &'ir Ty<Name> = Box::leak(Box::new(Ty::Unit));
        LocalFrame::new(test_name(25), &[], ret_ty, None, instrs)
    }

    fn run_with_limits(instrs: Vec<Instr<Name, B64>>, limits: ExecutionLimits) -> Result<Run<B64>, ExecError> {
        let shared_state = empty_shared_state();
        let mut frame = make_frame(instrs);
        let task_state = TaskState::new().with_execution_limits(limits);
        let queue = Worker::new_lifo();
        let mut task_fraction = Fraction::one();
        let ctx = Context::new(Config::new());
        let mut solver = Solver::new(&ctx);

        run_loop(
            0,
            TaskId::from_usize(0),
            &mut task_fraction,
            PathTimeout::unlimited(),
            None,
            &SingleForkSink { queue: &queue },
            &mut frame,
            &task_state,
            &shared_state,
            &mut solver,
        )
    }

    fn run_all_with_shared_state<'ir>(
        instrs: Vec<Instr<Name, B64>>,
        limits: ExecutionLimits,
        shared_state: SharedState<'ir, B64>,
    ) -> Vec<Result<Run<B64>, ExecError>> {
        let frame = make_frame(instrs);
        let task_state = TaskState::new().with_execution_limits(limits);
        let queue = Worker::new_lifo();
        queue.push(frame.task(TaskId::from_usize(0), &task_state));
        let mut results = Vec::new();

        while let Some(mut task) = queue.pop() {
            let mut cfg = Config::new();
            cfg.set_param_value("model", "true");
            let ctx = Context::new(cfg);
            let mut solver = Solver::from_checkpoint(&ctx, task.checkpoint);
            if let Some((def, event)) = task.fork_cond {
                solver.add_event(event);
                solver.add(def);
            }
            let mut task_frame = unfreeze_frame(&task.frame);
            results.push(run_loop(
                0,
                task.id,
                &mut task.fraction,
                PathTimeout::unlimited(),
                task.stop_conditions,
                &SingleForkSink { queue: &queue },
                &mut task_frame,
                task.state,
                &shared_state,
                &mut solver,
            ));
        }

        results
    }

    fn repeated_call_fork_program(call_count: usize) -> (Vec<Instr<Name, B64>>, SharedState<'static, B64>) {
        let callee = test_name(26);
        let var = test_name(100);
        let callee_instrs: &'static [Instr<Name, B64>] = Box::leak(
            vec![Instr::Decl(var, Ty::Bool, info()), Instr::Jump(Exp::Id(var), 2, info()), Instr::End]
                .into_boxed_slice(),
        );
        let defs = vec![
            crate::ir::Def::Val(callee, Vec::new(), Ty::Unit),
            crate::ir::Def::Fn(callee, Vec::new(), callee_instrs.to_vec()),
        ];
        let mut instrs = Vec::new();
        for offset in 0..call_count {
            let result = test_name(101 + offset as u32);
            instrs.push(Instr::Decl(result, Ty::Unit, info()));
            instrs.push(Instr::Call(Loc::Id(result), false, callee, Vec::new(), info()));
        }
        instrs.push(Instr::End);
        (instrs, shared_state_from_defs(defs))
    }

    #[test]
    fn path_timeout_is_evaluated_from_path_local_totals() {
        let timeout = PathTimeout::from_seconds(Some(2));
        let expired = crate::timeout::PathTimeSnapshot {
            active_wall: Duration::from_secs(2),
            ..crate::timeout::PathTimeSnapshot::default()
        };
        let active = crate::timeout::PathTimeSnapshot {
            active_wall: Duration::from_secs(1),
            ..crate::timeout::PathTimeSnapshot::default()
        };

        assert!(timeout.timed_out(expired));
        assert!(!timeout.timed_out(active));
    }

    #[test]
    fn branch_limit_truncate_reports_error_after_max_forks() {
        let limits = ExecutionLimits::default().with_max_forks_per_branch(2).with_call_context_depth(0);
        let (instrs, shared_state) = repeated_call_fork_program(5);
        let results = run_all_with_shared_state(instrs, limits, shared_state);

        let branch_limit = results.into_iter().find_map(|result| match result {
            Err(ExecError::BranchLimitReached(function, pc)) => Some((function, pc)),
            _ => None,
        });
        match branch_limit {
            Some((function, pc)) => {
                assert_eq!(function, test_name(26));
                assert_eq!(pc, 1);
            }
            None => panic!("期望分支限制错误"),
        }
    }

    #[test]
    fn branch_limit_concretize_finishes_without_error() {
        let limits = ExecutionLimits::default()
            .with_max_forks_per_branch(2)
            .with_call_context_depth(0)
            .with_limit_behavior(LimitBehavior::Concretize);
        let (instrs, shared_state) = repeated_call_fork_program(5);
        let results = run_all_with_shared_state(instrs, limits, shared_state);

        assert!(results.iter().any(|result| matches!(result, Ok(Run::Finished(Val::Unit)))));
        assert!(results.iter().all(Result::is_ok));
    }

    struct ForkCountCaptureSink<'a> {
        child_fork_counts: &'a std::sync::Mutex<Vec<u32>>,
    }

    impl<'a, 'ir, 'task> ForkSink<'ir, 'task, B64> for ForkCountCaptureSink<'a> {
        fn submit(&self, task: Task<'ir, 'task, B64>) {
            self.child_fork_counts.lock().unwrap().push(task.frame.forks());
        }
    }

    #[test]
    fn branch_fork_count_is_inherited_by_both_successors() {
        let shared_state = empty_shared_state();
        let var = test_name(100);
        let mut frame =
            make_frame(vec![Instr::Decl(var, Ty::Bool, info()), Instr::Jump(Exp::Id(var), 2, info()), Instr::End]);
        let task_state = TaskState::new();
        let child_fork_counts = std::sync::Mutex::new(Vec::new());
        let fork_sink = ForkCountCaptureSink { child_fork_counts: &child_fork_counts };
        let mut task_fraction = Fraction::one();
        let ctx = Context::new(Config::new());
        let mut solver = Solver::new(&ctx);

        let result = run_loop(
            0,
            TaskId::from_usize(0),
            &mut task_fraction,
            PathTimeout::unlimited(),
            None,
            &fork_sink,
            &mut frame,
            &task_state,
            &shared_state,
            &mut solver,
        );

        assert!(matches!(result, Ok(Run::Finished(Val::Unit))));
        assert_eq!(frame.forks(), 1);
        assert_eq!(*child_fork_counts.lock().unwrap(), vec![1]);
    }

    #[test]
    fn repeated_runs_from_one_task_state_do_not_share_branch_budget() {
        let shared_state = empty_shared_state();
        let var = test_name(100);
        let task_state =
            TaskState::new().with_execution_limits(ExecutionLimits::default().with_max_forks_per_branch(1));

        for _ in 0..2 {
            let mut frame =
                make_frame(vec![Instr::Decl(var, Ty::Bool, info()), Instr::Jump(Exp::Id(var), 2, info()), Instr::End]);
            let child_fork_counts = std::sync::Mutex::new(Vec::new());
            let fork_sink = ForkCountCaptureSink { child_fork_counts: &child_fork_counts };
            let mut task_fraction = Fraction::one();
            let ctx = Context::new(Config::new());
            let mut solver = Solver::new(&ctx);

            let result = run_loop(
                0,
                TaskId::from_usize(0),
                &mut task_fraction,
                PathTimeout::unlimited(),
                None,
                &fork_sink,
                &mut frame,
                &task_state,
                &shared_state,
                &mut solver,
            );

            assert!(matches!(result, Ok(Run::Finished(Val::Unit))));
            assert_eq!(frame.forks(), 1);
            assert_eq!(*child_fork_counts.lock().unwrap(), vec![1]);
        }
    }

    #[test]
    fn monomorphize_fork_count_is_inherited_by_both_successors() {
        let shared_state = empty_shared_state();
        let var = test_name(100);
        let mut frame = make_frame(vec![
            Instr::Decl(var, Ty::Bool, info()),
            Instr::Monomorphize(var, Ty::Bool, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
            Instr::End,
        ]);
        let task_state = TaskState::new();
        let child_fork_counts = std::sync::Mutex::new(Vec::new());
        let fork_sink = ForkCountCaptureSink { child_fork_counts: &child_fork_counts };
        let mut task_fraction = Fraction::one();
        let ctx = Context::new(Config::new());
        let mut solver = Solver::new(&ctx);

        let result = run_loop(
            0,
            TaskId::from_usize(0),
            &mut task_fraction,
            PathTimeout::unlimited(),
            None,
            &fork_sink,
            &mut frame,
            &task_state,
            &shared_state,
            &mut solver,
        );

        assert!(matches!(result, Ok(Run::Finished(Val::Unit))));
        assert_eq!(frame.forks(), 1);
        assert_eq!(*child_fork_counts.lock().unwrap(), vec![1]);
    }

    #[test]
    fn monomorphize_path_limit_can_keep_current_model_without_forking() {
        let shared_state = empty_shared_state();
        let var = test_name(100);
        let mut frame = make_frame(vec![
            Instr::Decl(var, Ty::Bool, info()),
            Instr::Monomorphize(var, Ty::Bool, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
            Instr::End,
        ]);
        let task_state = TaskState::new().with_execution_limits(
            ExecutionLimits::default().with_max_forks_per_path(0).with_limit_behavior(LimitBehavior::Concretize),
        );
        let child_fork_counts = std::sync::Mutex::new(Vec::new());
        let fork_sink = ForkCountCaptureSink { child_fork_counts: &child_fork_counts };
        let mut task_fraction = Fraction::one();
        let ctx = Context::new(Config::new());
        let mut solver = Solver::new(&ctx);

        let result = run_loop(
            0,
            TaskId::from_usize(0),
            &mut task_fraction,
            PathTimeout::unlimited(),
            None,
            &fork_sink,
            &mut frame,
            &task_state,
            &shared_state,
            &mut solver,
        );

        assert!(matches!(result, Ok(Run::Finished(Val::Unit))));
        assert_eq!(frame.forks(), 0);
        assert!(child_fork_counts.lock().unwrap().is_empty());
    }

    #[test]
    fn monomorphize_path_limit_truncates_before_child_submission() {
        let shared_state = empty_shared_state();
        let var = test_name(100);
        let mut frame = make_frame(vec![
            Instr::Decl(var, Ty::Bool, info()),
            Instr::Monomorphize(var, Ty::Bool, info()),
            Instr::End,
        ]);
        let task_state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_max_forks_per_path(0));
        let child_fork_counts = std::sync::Mutex::new(Vec::new());
        let fork_sink = ForkCountCaptureSink { child_fork_counts: &child_fork_counts };
        let mut task_fraction = Fraction::one();
        let ctx = Context::new(Config::new());
        let mut solver = Solver::new(&ctx);

        let result = run_loop(
            0,
            TaskId::from_usize(0),
            &mut task_fraction,
            PathTimeout::unlimited(),
            None,
            &fork_sink,
            &mut frame,
            &task_state,
            &shared_state,
            &mut solver,
        );

        assert!(matches!(result, Err(ExecError::BranchLimitReached(function, 1)) if function == test_name(25)));
        assert_eq!(frame.forks(), 0);
        assert!(child_fork_counts.lock().unwrap().is_empty());
    }

    #[test]
    fn monomorphize_does_not_submit_an_unsatisfiable_remainder_child() {
        let var = test_name(100);
        let results = run_all_with_shared_state(
            vec![
                Instr::Decl(var, Ty::Bool, info()),
                Instr::Monomorphize(var, Ty::Bool, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                Instr::End,
            ],
            ExecutionLimits::default(),
            empty_shared_state(),
        );

        assert_eq!(results.len(), 2);
        assert!(results.iter().all(|result| matches!(result, Ok(Run::Finished(Val::Unit)))));
    }

    #[test]
    fn monomorphize_last_model_does_not_consume_path_fork_budget() {
        let var = test_name(100);
        let results = run_all_with_shared_state(
            vec![
                Instr::Decl(var, Ty::Bool, info()),
                Instr::Monomorphize(var, Ty::Bool, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                Instr::End,
            ],
            ExecutionLimits::default().with_max_forks_per_path(1),
            empty_shared_state(),
        );

        assert_eq!(results.len(), 2);
        assert!(results.iter().all(|result| matches!(result, Ok(Run::Finished(Val::Unit)))));
    }

    #[test]
    fn monomorphize_enumerates_all_two_bit_models_with_three_path_forks() {
        let shared_state = empty_shared_state();
        let var = test_name(100);
        let instrs: &'static [Instr<Name, B64>] = Box::leak(
            vec![
                Instr::Decl(var, Ty::Bits(2), info()),
                Instr::Monomorphize(var, Ty::Bits(2), info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(var), info()),
                Instr::End,
            ]
            .into_boxed_slice(),
        );
        let ret_ty: &'static Ty<Name> = Box::leak(Box::new(Ty::Bits(2)));
        let frame = LocalFrame::new(test_name(25), &[], ret_ty, None, instrs);
        let task_state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_max_forks_per_path(3));
        let queue = Worker::new_lifo();
        queue.push(frame.task(TaskId::from_usize(0), &task_state));
        let mut models = Vec::new();

        while let Some(mut task) = queue.pop() {
            let mut cfg = Config::new();
            cfg.set_param_value("model", "true");
            let ctx = Context::new(cfg);
            let mut solver = Solver::from_checkpoint(&ctx, task.checkpoint);
            if let Some((def, event)) = task.fork_cond {
                solver.add_event(event);
                solver.add(def);
            }
            let mut task_frame = unfreeze_frame(&task.frame);
            match run_loop(
                0,
                task.id,
                &mut task.fraction,
                PathTimeout::unlimited(),
                task.stop_conditions,
                &SingleForkSink { queue: &queue },
                &mut task_frame,
                task.state,
                &shared_state,
                &mut solver,
            ) {
                Ok(Run::Finished(Val::Bits(value))) => models.push((value.lower_u64(), task_frame.forks())),
                Ok(_) => panic!("two-bit monomorphize returned an unexpected run result"),
                Err(error) => panic!("two-bit monomorphize failed: {}", error),
            }
        }

        models.sort();
        assert_eq!(models.iter().map(|(value, _)| *value).collect::<Vec<_>>(), vec![0, 1, 2, 3]);
        let mut fork_counts = models.iter().map(|(_, forks)| *forks).collect::<Vec<_>>();
        fork_counts.sort();
        assert_eq!(fork_counts, vec![1, 2, 3, 3]);
    }

    #[cfg(feature = "tracetool")]
    #[test]
    fn execution_limit_concretize_records_itrace_summary() {
        let shared_state = empty_shared_state();
        let var = test_name(100);
        let mut frame =
            make_frame(vec![Instr::Decl(var, Ty::Bool, info()), Instr::Jump(Exp::Id(var), 2, info()), Instr::End]);
        let task_state = TaskState::new().with_execution_limits(
            ExecutionLimits::default().with_max_path_depth(0).with_limit_behavior(LimitBehavior::Concretize),
        );
        let queue = Worker::new_lifo();
        let mut task_fraction = Fraction::one();
        let ctx = Context::new(Config::new());
        let mut solver = Solver::new(&ctx);

        let result = run_loop(
            0,
            TaskId::from_usize(0),
            &mut task_fraction,
            PathTimeout::unlimited(),
            None,
            &SingleForkSink { queue: &queue },
            &mut frame,
            &task_state,
            &shared_state,
            &mut solver,
        );

        assert!(matches!(result, Ok(Run::Finished(Val::Unit))));
        assert!(frame.itrace_path.records().iter().any(|record| {
            record.summary.as_deref().map_or(false, |summary| {
                summary.contains("execution limit: max_path_depth exceeded")
                    && summary.contains("action=sample_branch_condition")
            })
        }));
    }

    #[cfg(feature = "tracetool")]
    #[test]
    fn execution_limit_truncate_records_itrace_summary() {
        let shared_state = empty_shared_state();
        let mut frame = make_frame(vec![Instr::Goto(0)]);
        let task_state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_max_path_depth(0));
        let queue = Worker::new_lifo();
        let mut task_fraction = Fraction::one();
        let ctx = Context::new(Config::new());
        let mut solver = Solver::new(&ctx);

        let result = run_loop(
            0,
            TaskId::from_usize(0),
            &mut task_fraction,
            PathTimeout::unlimited(),
            None,
            &SingleForkSink { queue: &queue },
            &mut frame,
            &task_state,
            &shared_state,
            &mut solver,
        );

        assert!(matches!(result, Err(ExecError::DepthLimitReached)));
        assert!(frame.itrace_path.records().iter().any(|record| {
            record.summary.as_deref().map_or(false, |summary| {
                summary.contains("execution limit: max_path_depth exceeded") && summary.contains("action=truncate")
            })
        }));
    }

    #[test]
    fn depth_limit_reports_error_after_max_steps() {
        let limits = ExecutionLimits::default().with_max_path_depth(2);
        let result = run_with_limits(vec![Instr::Goto(1), Instr::Goto(2), Instr::Goto(3), Instr::End], limits);

        match result {
            Err(ExecError::DepthLimitReached) => (),
            _ => panic!("期望深度限制错误"),
        }
    }

    #[test]
    fn loop_limit_reports_error_after_max_backjumps() {
        let limits = ExecutionLimits::default().with_max_backjumps_per_loop(2);
        let result = run_with_limits(vec![Instr::Goto(0)], limits);

        match result {
            Err(ExecError::LoopLimitReached(function, pc)) => {
                assert_eq!(function, test_name(25));
                assert_eq!(pc, 0);
            }
            _ => panic!("期望循环限制错误"),
        }
    }

    #[test]
    fn loop_sampling_truncates_when_exit_direction_becomes_unsatisfiable() {
        let var = test_name(100);
        let info = info();
        let seed = (0..1024)
            .find(|seed| {
                let task_state = TaskState::<B64>::new().with_execution_limits(
                    ExecutionLimits::default()
                        .with_max_backjumps_per_loop(0)
                        .with_branch_sampling_seed(*seed)
                        .with_limit_behavior(LimitBehavior::Concretize),
                );
                let handler = ExecutionLimitHandler::new(
                    task_state.execution_limits.as_ref().expect("configured limits must be active"),
                );
                let mut path = ExecutionLimitPathState::default();
                matches!(
                    handler.on_conditional_jump(
                        &mut path,
                        test_name(25),
                        1,
                        1,
                        &[],
                        info,
                    ),
                    ExecutionLimitDecision::ConcretizeBranch { sample, .. } if sample.preferred()
                )
            })
            .expect("必须能找到首轮选择回边的 sampling seed");
        let limits = ExecutionLimits::default()
            .with_max_backjumps_per_loop(0)
            .with_branch_sampling_seed(seed)
            .with_limit_behavior(LimitBehavior::Concretize);
        let result = run_with_limits(
            vec![Instr::Decl(var, Ty::Bool, info), Instr::Jump(Exp::Id(var), 1, info), Instr::End],
            limits,
        );

        match result {
            Err(ExecError::LoopLimitReached(function, pc)) => {
                assert_eq!(function, test_name(25));
                assert_eq!(pc, 1);
            }
            _ => panic!("退出方向不可满足时必须截断符号回边"),
        }
    }

    #[test]
    fn path_fork_limit_truncates_serial_if_else_chain() {
        let (instrs, shared_state) = repeated_call_fork_program(5);
        let limits = ExecutionLimits::default().with_max_forks_per_branch(100).with_max_forks_per_path(2);
        let results = run_all_with_shared_state(instrs, limits, shared_state);

        let branch_limit = results.into_iter().find_map(|result| match result {
            Err(ExecError::BranchLimitReached(function, pc)) => Some((function, pc)),
            _ => None,
        });
        match branch_limit {
            Some((function, pc)) => {
                assert_eq!(function, test_name(26));
                assert_eq!(pc, 1);
            }
            None => panic!("期望单路径 fork 限制错误"),
        }
    }

    #[test]
    fn path_fork_limit_concretize_finishes_serial_if_else_chain() {
        let (instrs, shared_state) = repeated_call_fork_program(5);
        let limits = ExecutionLimits::default()
            .with_max_forks_per_branch(100)
            .with_max_forks_per_path(2)
            .with_limit_behavior(LimitBehavior::Concretize);
        let results = run_all_with_shared_state(instrs, limits, shared_state);

        assert!(results.iter().any(|result| matches!(result, Ok(Run::Finished(Val::Unit)))));
        assert!(results.iter().all(Result::is_ok));
    }

    #[test]
    fn real_ir_path_forks_limit_register_read_chain() {
        let (instrs, shared_state, regs, lets) = real_zrx_program();
        let zrx = shared_state.symtab.lookup("zrX");
        let limits = ExecutionLimits::default().with_max_forks_per_branch(100).with_max_forks_per_path(5);
        let results = run_all_with_bindings(instrs, limits, shared_state, regs, lets);

        let branch_limit = results.into_iter().find_map(|result| match result {
            Err(ExecError::BranchLimitReached(function, pc)) => Some((function, pc)),
            _ => None,
        });
        match branch_limit {
            Some((function, pc)) => {
                assert_eq!(function, zrx);
                assert_eq!(pc, 77);
            }
            None => panic!("期望真实 zrX 触发单路径 fork 限制"),
        }
    }

    #[test]
    fn real_ir_per_branch_cannot_detect_serial_chain() {
        let (instrs, shared_state, regs, lets) = real_zrx_program();
        let limits = ExecutionLimits::default().with_max_forks_per_branch(2);
        let results = run_all_with_bindings(instrs, limits, shared_state, regs, lets);

        assert!(results.iter().any(|result| matches!(result, Ok(Run::Finished(Val::Bits(_))))));
        assert!(results.iter().all(Result::is_ok));
    }

    #[test]
    fn real_ir_concretize_continues_register_read() {
        let (instrs, shared_state, regs, lets) = real_zrx_program();
        let limits = ExecutionLimits::default()
            .with_max_forks_per_branch(100)
            .with_max_forks_per_path(5)
            .with_limit_behavior(LimitBehavior::Concretize);
        let results = run_all_with_bindings(instrs, limits, shared_state, regs, lets);

        assert!(results.iter().any(|result| matches!(result, Ok(Run::Finished(Val::Bits(_))))));
        assert!(results.iter().all(Result::is_ok));
    }

    // 测试 A（red->green）：验证 execute_ir_function_with_checkpoint_multi_thread
    // 透传调用方传入的 task_state（含 limits）。改动前该入口硬编码 TaskState::new()（无 limits），
    // 故 max_path_depth 不会触发；改动后透传生效，第二条 goto 触发 DepthLimitReached。
    #[test]
    fn entry_function_respects_passed_task_state_limits() {
        const STEPT_IR: &str = r#"
val zsteptest : (%unit) -> %unit
fn zsteptest(zu) {
  goto 1;
  goto 2;
  end;
}
"#;
        let (shared_state, regs, lets) = shared_state_and_bindings_from_ir(STEPT_IR);
        let limits = ExecutionLimits::default().with_max_path_depth(1).with_limit_behavior(LimitBehavior::Concretize);
        let task_state = TaskState::new().with_execution_limits(limits);
        let collected: Arc<std::sync::Mutex<u32>> = Arc::new(std::sync::Mutex::new(0));

        execute_ir_function_with_checkpoint_multi_thread(
            "zsteptest",
            &[Val::Unit],
            &shared_state,
            &regs,
            &lets,
            &collected,
            &|_tid, _id, result, _ss, _solver, count| {
                if matches!(result, Err((ExecError::DepthLimitReached, _))) {
                    *count.lock().unwrap() += 1;
                }
            },
            Checkpoint::new(),
            4,
            None,
            &task_state,
        );

        let depth_hits = *collected.lock().unwrap();
        assert!(depth_hits >= 1, "期望入口透传 task_state 后触发 DepthLimitReached，实际 {} 次", depth_hits);
    }

    #[test]
    fn entry_function_timeout_returns_through_collector() {
        const STEPT_IR: &str = r#"
val zsteptest : (%unit) -> %unit
fn zsteptest(zu) {
  goto 1;
  goto 2;
  end;
}
"#;
        let (shared_state, regs, lets) = shared_state_and_bindings_from_ir(STEPT_IR);
        let task_state = TaskState::new();
        let collected: Arc<std::sync::Mutex<u32>> = Arc::new(std::sync::Mutex::new(0));

        execute_ir_function_with_checkpoint_multi_thread(
            "zsteptest",
            &[Val::Unit],
            &shared_state,
            &regs,
            &lets,
            &collected,
            &|_tid, _id, result, _ss, _solver, count| {
                if matches!(result, Err((ExecError::Timeout, _))) {
                    *count.lock().unwrap() += 1;
                }
            },
            Checkpoint::new(),
            4,
            Some(0),
            &task_state,
        );

        let timeout_hits = *collected.lock().unwrap();
        assert_eq!(timeout_hits, 1, "timeout 后应通过 collector 返回一次，实际 {} 次", timeout_hits);
    }

    #[test]
    fn start_single_timeout_none_is_unlimited() {
        let shared_state = empty_shared_state();
        let task_state = TaskState::new();
        let timeout_hits = std::sync::Mutex::new(0);
        let finished_hits = std::sync::Mutex::new(0);

        let timeout_frame = make_frame(vec![Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()), Instr::End]);
        start_single_with_timeout(
            timeout_frame.task_with_checkpoint(TaskId::from_usize(0), &task_state, Checkpoint::new()),
            PathTimeout::from_seconds(Some(0)),
            &shared_state,
            &timeout_hits,
            &|_tid, _id, result, _ss, _solver, count| {
                if matches!(result, Err((ExecError::Timeout, _))) {
                    *count.lock().unwrap() += 1;
                }
            },
        );

        let unlimited_frame = make_frame(vec![Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()), Instr::End]);
        start_single_with_timeout(
            unlimited_frame.task_with_checkpoint(TaskId::from_usize(1), &task_state, Checkpoint::new()),
            PathTimeout::from_seconds(None),
            &shared_state,
            &finished_hits,
            &|_tid, _id, result, _ss, _solver, count| {
                if matches!(result, Ok((Run::Finished(Val::Unit), _))) {
                    *count.lock().unwrap() += 1;
                }
            },
        );

        assert_eq!(*timeout_hits.lock().unwrap(), 1);
        assert_eq!(*finished_hits.lock().unwrap(), 1);
    }

    #[test]
    fn completed_path_wins_over_zero_timeout_at_the_completion_boundary() {
        let shared_state = empty_shared_state();
        let task_state = TaskState::new();
        let completed = std::sync::Mutex::new(false);
        let frame = make_frame(Vec::new());

        start_single_with_timeout(
            frame.task_with_checkpoint(TaskId::from_usize(0), &task_state, Checkpoint::new()),
            PathTimeout::from_seconds(Some(0)),
            &shared_state,
            &completed,
            &|_tid, _id, result, _ss, _solver, completed| {
                *completed.lock().unwrap() = matches!(result, Ok((Run::Finished(Val::Unit), _)));
            },
        );

        assert!(*completed.lock().unwrap());
    }

    #[test]
    fn single_fork_sink_submits_the_child_task() {
        let state = TaskState::new();
        let frame = make_frame(Vec::new());
        let task = frame.task_with_checkpoint(TaskId::from_usize(0), &state, Checkpoint::new());
        let queue = Worker::new_lifo();

        SingleForkSink { queue: &queue }.submit(task);
        let child = queue.pop().expect("forked task was not submitted");

        assert_eq!(child.id, TaskId::from_usize(0));
    }

    fn worker_invariant_branch_prefix() -> (Vec<Instr<Name, B64>>, Name, Name) {
        let first_branch = test_name(100);
        let second_branch = test_name(101);
        let marker = test_name(102);
        let mut instrs = vec![
            Instr::Decl(first_branch, Ty::Bool, info()),
            Instr::Decl(second_branch, Ty::Bool, info()),
            Instr::Decl(marker, Ty::Bool, info()),
            Instr::Jump(Exp::Id(first_branch), 6, info()),
            Instr::Copy(Loc::Id(marker), Exp::Bool(false), info()),
            Instr::Goto(0),
            Instr::Copy(Loc::Id(marker), Exp::Bool(true), info()),
        ];

        for _ in 0..128 {
            let next = instrs.len() + 1;
            instrs.push(Instr::Goto(next));
        }

        let join = instrs.len();
        instrs[5] = Instr::Goto(join);
        (instrs, second_branch, marker)
    }

    fn worker_invariant_limit_program() -> Vec<Instr<Name, B64>> {
        let (mut instrs, second_branch, marker) = worker_invariant_branch_prefix();
        let join = instrs.len();
        let finish = join + 2;
        instrs.push(Instr::Jump(Exp::Id(second_branch), finish, info()));
        instrs.push(Instr::Goto(finish));
        instrs.push(Instr::Copy(Loc::Id(RETURN), Exp::Id(marker), info()));
        instrs.push(Instr::End);
        instrs
    }

    fn run_worker_invariant_limit_program(num_threads: usize) -> Vec<(String, u32)> {
        let shared_state = empty_shared_state();
        let instrs: &'static [Instr<Name, B64>] = Box::leak(worker_invariant_limit_program().into_boxed_slice());
        let ret_ty: &'static Ty<Name> = Box::leak(Box::new(Ty::Bool));
        let frame = LocalFrame::new(test_name(25), &[], ret_ty, None, instrs);
        let task_state = TaskState::new().with_execution_limits(
            ExecutionLimits::default().with_max_forks_per_branch(1).with_limit_behavior(LimitBehavior::Truncate),
        );
        let task = frame.task_with_checkpoint(TaskId::from_usize(0), &task_state, Checkpoint::new());
        let collected: Arc<std::sync::Mutex<Vec<(String, u32)>>> = Arc::new(std::sync::Mutex::new(Vec::new()));

        start_multi(
            num_threads,
            None,
            vec![task],
            &shared_state,
            collected.clone(),
            &|_tid, _id, result, _ss, _solver, outcomes| {
                let outcome = match result {
                    Ok((Run::Finished(Val::Bool(value)), frame)) => (format!("finished:{}", value), frame.forks()),
                    Ok((Run::Finished(_), frame)) => ("finished:other".to_string(), frame.forks()),
                    Ok((Run::Exit, frame)) => ("exit".to_string(), frame.forks()),
                    Ok((Run::Dead, frame)) => ("dead".to_string(), frame.forks()),
                    Ok((Run::Suspended, frame)) => ("suspended".to_string(), frame.forks()),
                    Err((error, frame)) => (format!("error:{}", error), frame.forks()),
                };
                outcomes.lock().unwrap().push(outcome);
            },
        );

        let mut outcomes = collected.lock().unwrap().clone();
        outcomes.sort();
        outcomes
    }

    fn worker_invariant_sampling_program() -> Vec<Instr<Name, B64>> {
        let (mut instrs, second_branch, marker) = worker_invariant_branch_prefix();
        let join = instrs.len();
        let true_block = join + 6;
        let end = join + 11;
        instrs.extend([
            Instr::Jump(Exp::Id(second_branch), true_block, info()),
            Instr::Jump(Exp::Id(marker), join + 4, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::I64(0), info()),
            Instr::Goto(end),
            Instr::Copy(Loc::Id(RETURN), Exp::I64(1), info()),
            Instr::Goto(end),
            Instr::Jump(Exp::Id(marker), join + 9, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::I64(2), info()),
            Instr::Goto(end),
            Instr::Copy(Loc::Id(RETURN), Exp::I64(3), info()),
            Instr::Goto(end),
            Instr::End,
        ]);
        instrs
    }

    fn run_worker_invariant_sampling_program(num_threads: usize) -> Vec<(i64, u32)> {
        let shared_state = empty_shared_state();
        let instrs: &'static [Instr<Name, B64>] = Box::leak(worker_invariant_sampling_program().into_boxed_slice());
        let ret_ty: &'static Ty<Name> = Box::leak(Box::new(Ty::I64));
        let frame = LocalFrame::new(test_name(25), &[], ret_ty, None, instrs);
        let task_state = TaskState::new().with_execution_limits(
            ExecutionLimits::default().with_max_forks_per_path(1).with_limit_behavior(LimitBehavior::Concretize),
        );
        let task = frame.task_with_checkpoint(TaskId::from_usize(0), &task_state, Checkpoint::new());
        let collected: Arc<std::sync::Mutex<Vec<(i64, u32)>>> = Arc::new(std::sync::Mutex::new(Vec::new()));

        start_multi(
            num_threads,
            None,
            vec![task],
            &shared_state,
            collected.clone(),
            &|_tid, _id, result, _ss, _solver, outcomes| match result {
                Ok((Run::Finished(Val::I64(value)), frame)) => {
                    outcomes.lock().unwrap().push((value, frame.forks()));
                }
                Ok(_) => panic!("sampling differential program returned an unexpected run result"),
                Err((error, _)) => panic!("sampling differential program failed: {}", error),
            },
        );

        let mut outcomes = collected.lock().unwrap().clone();
        outcomes.sort();
        outcomes
    }

    #[test]
    fn execution_limits_have_identical_single_and_multi_worker_semantics() {
        let expected = vec![
            ("finished:false".to_string(), 2),
            ("finished:false".to_string(), 2),
            ("finished:true".to_string(), 2),
            ("finished:true".to_string(), 2),
        ];

        assert_eq!(run_worker_invariant_limit_program(0), expected);
        for _ in 0..20 {
            assert_eq!(run_worker_invariant_limit_program(1), expected);
            assert_eq!(run_worker_invariant_limit_program(4), expected);
        }
    }

    #[test]
    fn path_local_sampling_is_stable_across_worker_counts() {
        let expected = run_worker_invariant_sampling_program(0);
        assert!(expected == vec![(0, 1), (1, 1)] || expected == vec![(2, 1), (3, 1)]);

        for _ in 0..20 {
            assert_eq!(run_worker_invariant_sampling_program(1), expected);
            assert_eq!(run_worker_invariant_sampling_program(4), expected);
        }
    }
}
pub fn execute_ir_function_with_checkpoint_and_memory<'ir, B: BV, R>(
    function_name: &str,
    args: &[Val<B>],
    shared_state: &SharedState<'ir, B>,
    regs: &RegisterBindings<'ir, B>,
    lets: &Bindings<'ir, B>,
    memory: super::memory::Memory<B>,
    collected: &R,
    collector: &Collector<'ir, B, R>,
    checkpoint: Checkpoint<B>,
) {
    let function_id = shared_state.symtab.lookup(function_name);
    let (func_args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();

    let mut initial_frame = LocalFrame::new(function_id, func_args, ret_ty, Some(args), instrs);
    initial_frame.add_regs(regs);
    initial_frame.add_lets(lets);
    initial_frame.set_memory(memory);

    let task_state = TaskState::new();
    let task_id = TaskId::fresh();
    let task = initial_frame.task_with_checkpoint(task_id, &task_state, checkpoint);

    start_single(task, &shared_state, collected, collector);
}
pub fn execute_ir_function_with_checkpoint_and_memory_multi_thread<'ir, B: BV, R>(
    function_name: &str,
    args: &[Val<B>],
    shared_state: &'ir SharedState<'ir, B>,
    regs: &RegisterBindings<'ir, B>,
    lets: &Bindings<'ir, B>,
    memory: super::memory::Memory<B>,
    collected: &Arc<R>,
    collector: &'ir Collector<'ir, B, R>,
    checkpoint: Checkpoint<B>,
    timeout: Option<u64>,
) where
    B: Send + Sync,
    R: Send + Sync,
{
    let function_id = shared_state.symtab.lookup(function_name);
    let (func_args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();

    let mut initial_frame = LocalFrame::new(function_id, func_args, ret_ty, Some(args), instrs);
    initial_frame.add_regs(regs);
    initial_frame.add_lets(lets);
    initial_frame.set_memory(memory);

    let task_state = TaskState::new();
    let task_id = TaskId::fresh();
    let task = initial_frame.task_with_checkpoint(task_id, &task_state, checkpoint);

    start_multi(110, timeout, vec![task], &shared_state, collected.clone(), collector);
}
