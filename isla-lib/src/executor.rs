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
use crate::primop_util::{build_ite, i128_from_bits, ite_phi, smt_i128, smt_sbits, smt_value, symbolic};
use crate::probe;
use crate::smt::smtlib::{Def, Exp as SmtExp};
use crate::smt::*;
use crate::source_loc::SourceLoc;
use crate::zencode;

mod frame;
mod task;

use crate::register::RegisterBindings;
pub use frame::{backtrace_string, freeze_frame, unfreeze_frame, Backtrace, Frame, LocalFrame, LocalState};
use frame::{pop_call_stack, push_call_stack};
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

#[derive(Copy, Clone, Debug)]
struct Timeout {
    start_time: Instant,
    duration: Option<Duration>,
}

impl Timeout {
    fn unlimited() -> Self {
        Timeout { start_time: Instant::now(), duration: None }
    }

    fn timed_out(&self) -> bool {
        self.duration.is_some() && self.start_time.elapsed() > self.duration.unwrap()
    }
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
    timeout: Timeout,
    stop_conditions: Option<&'task StopConditions>,
    fork_sink: &S,
    frame: &Frame<'ir, B>,
    task_state: &'task TaskState<B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)> {
    let mut frame = unfreeze_frame(frame);
    match run_loop(
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
    ) {
        Ok(run) => Ok((run, frame)),
        Err(err) => {
            frame.backtrace.push((frame.function_name, frame.pc));
            Err((err, frame.backtrace))
        }
    }
}

fn call_isla_implemented_function<'ir, B: BV>(
    f: Name,
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let function_name = shared_state.symtab.to_str(f);
    match zencode::decode(function_name).as_str() {
        "range_subset" => {
            if args.len() != 4 {
                return Err(ExecError::Type(format!("range_subset expected 4 arguments, got {}", args.len()), info));
            }
            if !env_flag_default_true("ISLA_RISCV_BUILTIN_RANGE_SUBSET") {
                return Ok(None);
            }
            range_subset_builtin(args, solver, info)
        }
        "split_misaligned" => {
            if args.len() != 2 {
                return Err(ExecError::Type(
                    format!("split_misaligned expected 2 arguments, got {}", args.len()),
                    info,
                ));
            }
            if !env_flag_default_true("ISLA_RISCV_BUILTIN_SPLIT_MISALIGNED") {
                return Ok(None);
            }
            split_misaligned_builtin(args, shared_state, solver, info)
        }
        "pmpAddrMatchType_encdec_backwards" | "pmpAddrMatchType_encdec_backwards_infallible" => {
            if args.len() != 1 {
                return Err(ExecError::Type(
                    format!("pmpAddrMatchType_encdec_backwards expected 1 argument, got {}", args.len()),
                    info,
                ));
            }
            if !env_flag_default_true("ISLA_RISCV_BUILTIN_PMP_ADDR_MATCH_TYPE") {
                return Ok(None);
            }
            pmp_addr_match_type_backwards_builtin(args, shared_state, solver, info)
        }
        "pmpCheckRWX" => {
            if args.len() != 2 {
                return Err(ExecError::Type(format!("pmpCheckRWX expected 2 arguments, got {}", args.len()), info));
            }
            if !env_flag_default_true("ISLA_RISCV_BUILTIN_PMP_CHECK_RWX") {
                return Ok(None);
            }
            pmp_check_rwx_builtin(args, shared_state, solver, info)
        }
        "pmpLocked" => {
            if args.len() != 1 {
                return Err(ExecError::Type(format!("pmpLocked expected 1 argument, got {}", args.len()), info));
            }
            if !env_flag_default_true("ISLA_RISCV_BUILTIN_PMP_LOCKED") {
                return Ok(None);
            }
            pmp_locked_builtin(args, shared_state, solver, info)
        }
        "pmpMatchAddr" => {
            if args.len() != 5 {
                return Err(ExecError::Type(format!("pmpMatchAddr expected 5 arguments, got {}", args.len()), info));
            }
            if !env_flag("ISLA_RISCV_BUILTIN_PMP_MATCH_ADDR") {
                return Ok(None);
            }
            pmp_match_addr_builtin(args, frame, shared_state, solver, info)
        }
        "pmpRangeMatch" => {
            if args.len() != 4 {
                return Err(ExecError::Type(format!("pmpRangeMatch expected 4 arguments, got {}", args.len()), info));
            }
            if !env_flag_default_true("ISLA_RISCV_BUILTIN_PMP_RANGE_MATCH") {
                return Ok(None);
            }
            pmp_range_match_builtin(args, shared_state, solver, info)
        }
        "pmpCheck" => {
            if args.len() != 4 {
                return Err(ExecError::Type(format!("pmpCheck expected 4 arguments, got {}", args.len()), info));
            }
            if env_flag("ISLA_RISCV_ASSUME_PMP_OFF") {
                return pmp_check_off_builtin(args, shared_state, info);
            }
            if env_flag("ISLA_RISCV_BUILTIN_PMP_CHECK") {
                return pmp_check_builtin(args, frame, shared_state, solver, info);
            }
            Ok(None)
        }
        "pmaCheck" => {
            if args.len() != 4 {
                return Err(ExecError::Type(format!("pmaCheck expected 4 arguments, got {}", args.len()), info));
            }
            if !env_flag("ISLA_RISCV_BUILTIN_PMA_CHECK") {
                return Ok(None);
            }
            pma_check_builtin(args, frame, shared_state, solver, info)
        }
        "phys_access_check" => {
            if args.len() != 5 {
                return Err(ExecError::Type(
                    format!("phys_access_check expected 5 arguments, got {}", args.len()),
                    info,
                ));
            }
            if !env_flag("ISLA_RISCV_BUILTIN_PHYS_ACCESS_CHECK") {
                return Ok(None);
            }
            phys_access_check_builtin(args, frame, shared_state, solver, info)
        }
        "within_clint" => {
            if args.len() != 2 {
                return Err(ExecError::Type(format!("within_clint expected 2 arguments, got {}", args.len()), info));
            }
            if env_flag("ISLA_RISCV_ASSUME_CLINT_OFF") {
                if clint_off_requires_within_mmio_builtin(true, env_flag("ISLA_RISCV_BUILTIN_WITHIN_MMIO")) {
                    return Err(ExecError::Type(
                        "ISLA_RISCV_ASSUME_CLINT_OFF=1 requires ISLA_RISCV_BUILTIN_WITHIN_MMIO=1 to avoid treating CLINT range as RAM".to_string(),
                        info,
                    ));
                }
                return Ok(clint_disabled_predicate_result());
            }
            Ok(None)
        }
        "clint_load" => {
            if args.len() != 3 {
                return Err(ExecError::Type(format!("clint_load expected 3 arguments, got {}", args.len()), info));
            }
            if !env_flag("ISLA_RISCV_BUILTIN_CLINT_LOAD") {
                return Ok(None);
            }
            clint_load_builtin(args, frame, shared_state, solver, info)
        }
        "within_mmio_readable" | "within_mmio_writable" => {
            if args.len() != 2 {
                return Err(ExecError::Type(
                    format!("{} expected 2 arguments, got {}", function_name, args.len()),
                    info,
                ));
            }
            if !env_flag("ISLA_RISCV_BUILTIN_WITHIN_MMIO") {
                return Ok(None);
            }
            within_mmio_builtin(args, frame, shared_state, solver, info)
        }
        "vmem_write_addr" => {
            if args.len() != 7 {
                return Err(ExecError::Type(format!("vmem_write_addr expected 7 arguments, got {}", args.len()), info));
            }

            if !riscv_vmem_builtin_enabled("vmem_write_addr") {
                return Ok(None);
            }

            match riscv_vmem_builtin_mode() {
                RiscvVmemBuiltinMode::Off => Ok(None),
                RiscvVmemBuiltinMode::Legacy => {
                    let opts = match args[6] {
                        Val::Bool(true) => WriteOpts::exclusive(),
                        _ => WriteOpts::default(),
                    };
                    let write_success = frame.memory_mut().write(
                        args[3].clone(),
                        args[0].clone(),
                        args[2].clone(),
                        solver,
                        None,
                        opts,
                    )?;
                    let ok_ctor = lookup_required_vmem_symbol("zOkzIozCUExecutionResultzK", shared_state, info)?;
                    Ok(Some(Val::Ctor(ok_ctor, Box::new(write_success))))
                }
                RiscvVmemBuiltinMode::PlainRam => {
                    if let Some(reason) = validate_plain_vmem_write(args, shared_state, solver, info)? {
                        if reason == PLAIN_VMEM_MISALIGNED && env_flag("ISLA_RISCV_VMEM_ASSUME_MISALIGNED_FAULTS") {
                            log!(log::VERBOSE, "vmem_write_addr builtin returning concrete alignment exception");
                            return Ok(Some(vmem_alignment_exception(
                                args[0].clone(),
                                "zE_SAMO_Addr_Align",
                                "zErrzIozCUExecutionResultzK",
                                shared_state,
                                info,
                            )?));
                        }
                        log!(log::VERBOSE, &format!("vmem_write_addr builtin fallback: {}", reason));
                        return Ok(None);
                    }

                    let write_success = frame.memory_mut().write(
                        args[3].clone(),
                        args[0].clone(),
                        args[2].clone(),
                        solver,
                        None,
                        WriteOpts::default(),
                    )?;
                    if let Val::Symbolic(success) = write_success {
                        solver.add(Def::Assert(SmtExp::Var(success)));
                    }
                    let ok_ctor = lookup_required_vmem_symbol("zOkzIozCUExecutionResultzK", shared_state, info)?;
                    Ok(Some(Val::Ctor(ok_ctor, Box::new(Val::Bool(true)))))
                }
            }
        }
        "vmem_read_addr" => {
            if args.len() != 7 {
                return Err(ExecError::Type(format!("vmem_read_addr expected 7 arguments, got {}", args.len()), info));
            }

            if !riscv_vmem_builtin_enabled("vmem_read_addr") {
                return Ok(None);
            }

            match riscv_vmem_builtin_mode() {
                RiscvVmemBuiltinMode::Off => Ok(None),
                RiscvVmemBuiltinMode::Legacy => {
                    let opts = match args[6] {
                        Val::Bool(true) => ReadOpts::exclusive(),
                        _ => ReadOpts::default(),
                    };
                    let value =
                        frame.memory().read(args[3].clone(), args[0].clone(), args[2].clone(), solver, false, opts)?;
                    let ok_ctor = lookup_required_vmem_symbol("zOkzIbzCUExecutionResultzK", shared_state, info)?;
                    Ok(Some(Val::Ctor(ok_ctor, Box::new(value))))
                }
                RiscvVmemBuiltinMode::PlainRam => {
                    if let Some(reason) = validate_plain_vmem_read(args, shared_state, solver, info)? {
                        if reason == PLAIN_VMEM_MISALIGNED && env_flag("ISLA_RISCV_VMEM_ASSUME_MISALIGNED_FAULTS") {
                            log!(log::VERBOSE, "vmem_read_addr builtin returning concrete alignment exception");
                            return Ok(Some(vmem_alignment_exception(
                                args[0].clone(),
                                "zE_Load_Addr_Align",
                                "zErrzIbzCUExecutionResultzK",
                                shared_state,
                                info,
                            )?));
                        }
                        log!(log::VERBOSE, &format!("vmem_read_addr builtin fallback: {}", reason));
                        return Ok(None);
                    }

                    let value = frame.memory().read(
                        args[3].clone(),
                        args[0].clone(),
                        args[2].clone(),
                        solver,
                        false,
                        ReadOpts::default(),
                    )?;
                    let ok_ctor = lookup_required_vmem_symbol("zOkzIbzCUExecutionResultzK", shared_state, info)?;
                    Ok(Some(Val::Ctor(ok_ctor, Box::new(value))))
                }
            }
        }
        _ => Ok(None),
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum RiscvVmemBuiltinMode {
    Off,
    Legacy,
    PlainRam,
}

fn riscv_vmem_builtin_mode() -> RiscvVmemBuiltinMode {
    match std::env::var("ISLA_RISCV_VMEM_BUILTIN_MODE") {
        Ok(mode) if mode.eq_ignore_ascii_case("off") => RiscvVmemBuiltinMode::Off,
        Ok(mode) if mode.eq_ignore_ascii_case("plain-ram") => RiscvVmemBuiltinMode::PlainRam,
        Ok(mode) if mode.eq_ignore_ascii_case("plain_ram") => RiscvVmemBuiltinMode::PlainRam,
        Ok(mode) if mode.eq_ignore_ascii_case("legacy") => RiscvVmemBuiltinMode::Legacy,
        Ok(mode) => {
            log!(log::VERBOSE, &format!("unknown ISLA_RISCV_VMEM_BUILTIN_MODE={}; using plain-ram", mode));
            RiscvVmemBuiltinMode::PlainRam
        }
        Err(_) => RiscvVmemBuiltinMode::PlainRam,
    }
}

fn riscv_vmem_builtin_enabled(function_name: &str) -> bool {
    let key = match function_name {
        "vmem_write_addr" => "ISLA_RISCV_BUILTIN_VMEM_WRITE_ADDR",
        "vmem_read_addr" => "ISLA_RISCV_BUILTIN_VMEM_READ_ADDR",
        _ => return false,
    };

    match std::env::var(key) {
        Ok(value) => !matches!(value.as_str(), "0" | "false" | "False" | "FALSE" | "off" | "Off" | "OFF"),
        Err(_) => true,
    }
}

fn env_flag(name: &str) -> bool {
    matches!(std::env::var(name), Ok(value) if matches!(value.as_str(), "1" | "true" | "True" | "TRUE" | "on" | "On" | "ON"))
}

fn env_flag_default_true(name: &str) -> bool {
    match std::env::var(name) {
        Ok(value) => !matches!(value.as_str(), "0" | "false" | "False" | "FALSE" | "off" | "Off" | "OFF"),
        Err(_) => true,
    }
}

fn clint_disabled_predicate_result<B: BV>() -> Option<Val<B>> {
    Some(Val::Bool(false))
}

fn clint_off_requires_within_mmio_builtin(assume_clint_off: bool, within_mmio_builtin_enabled: bool) -> bool {
    assume_clint_off && !within_mmio_builtin_enabled
}

fn clint_off_within_mmio_error(reason: &str, info: SourceLoc) -> ExecError {
    ExecError::Type(
        format!(
            "ISLA_RISCV_ASSUME_CLINT_OFF=1 requires within_mmio summary to avoid treating CLINT range as RAM: {}",
            reason
        ),
        info,
    )
}

fn clint_off_within_mmio_fallback<B: BV>(reason: &str, info: SourceLoc) -> Result<Option<Val<B>>, ExecError> {
    log!(log::VERBOSE, &format!("within_mmio builtin fallback: {}", reason));
    if env_flag("ISLA_RISCV_ASSUME_CLINT_OFF") {
        return Err(clint_off_within_mmio_error(reason, info));
    }
    Ok(None)
}

fn clint_disabled_within_mmio_result<B: BV>(
    htif_tohost_base_none: bool,
    clint_range: Val<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if htif_tohost_base_none {
        Ok(Some(clint_range))
    } else {
        Err(clint_off_within_mmio_error("HTIF tohost base is not concrete None", info))
    }
}

fn within_mmio_builtin<'ir, B: BV>(
    args: &[Val<B>],
    frame: &LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if !function_returns_literal_false("zget_config_rvfi", shared_state) {
        return clint_off_within_mmio_fallback("get_config_rvfi is not literal false", info);
    }
    let htif_tohost_base_none = htif_tohost_base_is_none(frame, shared_state);
    if !htif_tohost_base_none {
        return clint_off_within_mmio_fallback("HTIF tohost base is not concrete None", info);
    }

    let Some(width) = concrete_width_bytes(&args[1]) else {
        return clint_off_within_mmio_fallback("symbolic width", info);
    };
    if width == 0 {
        return clint_off_within_mmio_fallback("zero width", info);
    }

    let Some((addr, addr_width)) = bitvector_exp_and_width(&args[0], solver, info)? else {
        return clint_off_within_mmio_fallback("unsupported address", info);
    };
    let Some((clint_base, clint_base_width)) = let_bitvector_exp_and_width("zplat_clint_base", frame, shared_state)
    else {
        return clint_off_within_mmio_fallback("missing CLINT base", info);
    };
    let Some((clint_size, clint_size_width)) = let_bitvector_exp_and_width("zplat_clint_sizze", frame, shared_state)
    else {
        return clint_off_within_mmio_fallback("missing CLINT size", info);
    };
    if addr_width != clint_base_width || addr_width != clint_size_width || addr_width > 64 {
        return clint_off_within_mmio_fallback("unsupported CLINT/address width", info);
    }

    let addr = unsigned_bv_exp_to_i128(addr, addr_width)?;
    let clint_base = unsigned_bv_exp_to_i128(clint_base, clint_base_width)?;
    let clint_size = unsigned_bv_exp_to_i128(clint_size, clint_size_width)?;
    let clint_range = smt_exp_to_value(unbounded_range_contains_exp(addr, clint_base, clint_size, width), solver)?;
    if env_flag("ISLA_RISCV_ASSUME_CLINT_OFF") {
        clint_disabled_within_mmio_result(htif_tohost_base_none, clint_range, info)
    } else {
        Ok(Some(clint_range))
    }
}

fn unbounded_range_contains_exp(
    addr: SmtExp<Sym>,
    base: SmtExp<Sym>,
    size: SmtExp<Sym>,
    width_bytes: u32,
) -> SmtExp<Sym> {
    let width = smt_i128(i128::from(width_bytes));
    let addr_end = SmtExp::Bvadd(Box::new(addr.clone()), Box::new(width));
    let base_end = SmtExp::Bvadd(Box::new(base.clone()), Box::new(size));
    SmtExp::And(
        Box::new(SmtExp::Bvule(Box::new(base), Box::new(addr))),
        Box::new(SmtExp::Bvule(Box::new(addr_end), Box::new(base_end))),
    )
}

fn range_subset_builtin<B: BV>(
    args: &[Val<B>],
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some(width) = range_subset_width(args, solver) else {
        log!(log::VERBOSE, "range_subset builtin fallback: unsupported argument width");
        return Ok(None);
    };
    if width == 0 {
        log!(log::VERBOSE, "range_subset builtin fallback: zero-width bitvector");
        return Ok(None);
    }

    let a_begin = smt_value(&args[0], info)?;
    let a_size = smt_value(&args[1], info)?;
    let b_begin = smt_value(&args[2], info)?;
    let b_size = smt_value(&args[3], info)?;

    Ok(Some(smt_exp_to_value(range_subset_exp(a_begin, a_size, b_begin, b_size), solver)?))
}

fn range_subset_exp(
    a_begin: SmtExp<Sym>,
    a_size: SmtExp<Sym>,
    b_begin: SmtExp<Sym>,
    b_size: SmtExp<Sym>,
) -> SmtExp<Sym> {
    let a_end =
        SmtExp::Bvsub(Box::new(SmtExp::Bvadd(Box::new(a_begin.clone()), Box::new(a_size))), Box::new(b_begin.clone()));
    let b_end =
        SmtExp::Bvsub(Box::new(SmtExp::Bvadd(Box::new(b_begin.clone()), Box::new(b_size))), Box::new(b_begin.clone()));
    let a_begin = SmtExp::Bvsub(Box::new(a_begin), Box::new(b_begin));

    SmtExp::And(
        Box::new(SmtExp::Bvule(Box::new(a_begin.clone()), Box::new(b_end.clone()))),
        Box::new(SmtExp::And(
            Box::new(SmtExp::Bvule(Box::new(a_end.clone()), Box::new(b_end))),
            Box::new(SmtExp::Bvule(Box::new(a_begin), Box::new(a_end))),
        )),
    )
}

fn range_subset_width<B: BV>(args: &[Val<B>], solver: &mut Solver<B>) -> Option<u32> {
    let mut width = None;
    for arg in args {
        let arg_width = bitvector_width(arg, solver)?;
        match width {
            Some(width) if width != arg_width => return None,
            Some(_) => {}
            None => width = Some(arg_width),
        }
    }
    width
}

fn bitvector_width<B: BV>(value: &Val<B>, solver: &mut Solver<B>) -> Option<u32> {
    match value {
        Val::Bits(bits) => Some(bits.len()),
        Val::Symbolic(sym) => solver.length(*sym),
        _ => None,
    }
}

fn split_misaligned_builtin<B: BV>(
    args: &[Val<B>],
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some(width) = concrete_width_bytes(&args[1]) else {
        log!(log::VERBOSE, "split_misaligned builtin fallback: symbolic width");
        return Ok(None);
    };
    if width == 0 {
        log!(log::VERBOSE, "split_misaligned builtin fallback: zero width");
        return Ok(None);
    }

    match is_concretely_aligned(&args[0], width) {
        Some(true) => split_misaligned_single_access(width, shared_state, info).map(Some),
        Some(false) => {
            log!(log::VERBOSE, "split_misaligned builtin fallback: concrete misaligned address");
            Ok(None)
        }
        None if env_flag("ISLA_RISCV_VMEM_ASSUME_ALIGNED") => {
            assert_plain_vmem_alignment(&args[0], width, solver, info)?;
            split_misaligned_single_access(width, shared_state, info).map(Some)
        }
        None => {
            log!(log::VERBOSE, "split_misaligned builtin fallback: symbolic alignment");
            Ok(None)
        }
    }
}

fn split_misaligned_single_access<B: BV>(
    width: u32,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let n_field = lookup_required_vmem_symbol("ztuplez3z5i_z5i0", shared_state, info)?;
    let bytes_field = lookup_required_vmem_symbol("ztuplez3z5i_z5i1", shared_state, info)?;
    let mut fields = HashMap::default();
    fields.insert(n_field, Val::I128(1));
    fields.insert(bytes_field, Val::I128(i128::from(width)));
    Ok(Val::Struct(fields))
}

fn pmp_addr_match_type_backwards_builtin<B: BV>(
    args: &[Val<B>],
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some((bits, width)) = bitvector_exp_and_width(&args[0], solver, info)? else {
        log!(log::VERBOSE, "pmpAddrMatchType builtin fallback: unsupported argument");
        return Ok(None);
    };
    if width != 2 {
        log!(log::VERBOSE, "pmpAddrMatchType builtin fallback: non-2-bit argument");
        return Ok(None);
    }

    let off = enum_symbol_exp("zOFF", shared_state, solver, info)?;
    let tor = enum_symbol_exp("zTOR", shared_state, solver, info)?;
    let na4 = enum_symbol_exp("zNA4", shared_state, solver, info)?;
    let napot = enum_symbol_exp("zNAPOT", shared_state, solver, info)?;

    let result = SmtExp::Ite(
        Box::new(SmtExp::Eq(Box::new(bits.clone()), Box::new(smt_sbits(B::new(0, 2))))),
        Box::new(off),
        Box::new(SmtExp::Ite(
            Box::new(SmtExp::Eq(Box::new(bits.clone()), Box::new(smt_sbits(B::new(1, 2))))),
            Box::new(tor),
            Box::new(SmtExp::Ite(
                Box::new(SmtExp::Eq(Box::new(bits), Box::new(smt_sbits(B::new(2, 2))))),
                Box::new(na4),
                Box::new(napot),
            )),
        )),
    );

    Ok(Some(smt_exp_to_value(result, solver)?))
}

fn pmp_check_rwx_builtin<B: BV>(
    args: &[Val<B>],
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some(result) = pmp_check_rwx_exp(&args[0], &args[1], shared_state, solver, info)? else {
        log!(log::VERBOSE, "pmpCheckRWX builtin fallback: unsupported access");
        return Ok(None);
    };
    Ok(Some(smt_exp_to_value(result, solver)?))
}

fn pmp_locked_builtin<B: BV>(
    args: &[Val<B>],
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some(result) = pmpcfg_bit_is_set(&args[0], 7, shared_state, solver, info)? else {
        log!(log::VERBOSE, "pmpLocked builtin fallback: unsupported pmpcfg entry");
        return Ok(None);
    };
    Ok(Some(smt_exp_to_value(result, solver)?))
}

fn pmp_match_addr_builtin<B: BV>(
    args: &[Val<B>],
    frame: &LocalFrame<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    match concrete_i64_let("zsys_pmp_grain", frame, shared_state) {
        Some(0) => {}
        Some(_) => {
            log!(log::VERBOSE, "pmpMatchAddr builtin fallback: non-zero PMP grain");
            return Ok(None);
        }
        None => {
            log!(log::VERBOSE, "pmpMatchAddr builtin fallback: unknown PMP grain");
            return Ok(None);
        }
    }

    let Some(result) =
        pmp_match_addr_exp(&args[0], &args[1], &args[2], &args[3], &args[4], shared_state, solver, info)?
    else {
        log!(log::VERBOSE, "pmpMatchAddr builtin fallback: unsupported argument");
        return Ok(None);
    };

    Ok(Some(smt_exp_to_value(result, solver)?))
}

fn pmp_match_addr_exp<B: BV>(
    addr_value: &Val<B>,
    width_value: &Val<B>,
    ent: &Val<B>,
    pmpaddr_value: &Val<B>,
    prev_pmpaddr_value: &Val<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Some((addr_bv, addr_width)) = bitvector_exp_and_width(addr_value, solver, info)? else {
        return Ok(None);
    };
    let Some((width_bv, width_width)) = bitvector_exp_and_width(width_value, solver, info)? else {
        return Ok(None);
    };
    let Some((pmpaddr_bv, pmpaddr_width)) = bitvector_exp_and_width(pmpaddr_value, solver, info)? else {
        return Ok(None);
    };
    let Some((prev_pmpaddr_bv, prev_pmpaddr_width)) = bitvector_exp_and_width(prev_pmpaddr_value, solver, info)? else {
        return Ok(None);
    };
    if addr_width != width_width || addr_width != pmpaddr_width || addr_width != prev_pmpaddr_width || addr_width > 128
    {
        return Ok(None);
    }

    let Some(a_bits) = pmpcfg_a_bits(ent, shared_state, solver, info)? else {
        return Ok(None);
    };

    let no_match = pmp_addr_match_enum("zPMP_NoMatch", shared_state, solver, info)?;
    let partial_match = pmp_addr_match_enum("zPMP_PartialMatch", shared_state, solver, info)?;
    let full_match = pmp_addr_match_enum("zPMP_Match", shared_state, solver, info)?;

    let addr = unsigned_bv_exp_to_i128(addr_bv, addr_width)?;
    let width = unsigned_bv_exp_to_i128(width_bv, width_width)?;
    let pmpaddr = unsigned_bv_exp_to_i128(pmpaddr_bv.clone(), pmpaddr_width)?;
    let prev_pmpaddr = unsigned_bv_exp_to_i128(prev_pmpaddr_bv.clone(), prev_pmpaddr_width)?;

    let four = smt_i128(4);
    let tor_begin = SmtExp::Bvmul(Box::new(prev_pmpaddr), Box::new(four.clone()));
    let tor_end = SmtExp::Bvmul(Box::new(pmpaddr.clone()), Box::new(four.clone()));
    let tor_result = SmtExp::Ite(
        Box::new(SmtExp::Bvuge(Box::new(prev_pmpaddr_bv.clone()), Box::new(pmpaddr_bv.clone()))),
        Box::new(no_match.clone()),
        Box::new(pmp_range_match_exp(
            tor_begin,
            tor_end,
            addr.clone(),
            width.clone(),
            &no_match,
            &partial_match,
            &full_match,
        )),
    );

    let na4_begin = SmtExp::Bvmul(Box::new(pmpaddr.clone()), Box::new(four.clone()));
    let na4_end = SmtExp::Bvadd(Box::new(na4_begin.clone()), Box::new(four.clone()));
    let na4_result =
        pmp_range_match_exp(na4_begin, na4_end, addr.clone(), width.clone(), &no_match, &partial_match, &full_match);

    let one_bv = smt_sbits(B::new(1, addr_width));
    let pmpaddr_plus_one = SmtExp::Bvadd(Box::new(pmpaddr_bv.clone()), Box::new(one_bv));
    let mask_bv = SmtExp::Bvxor(Box::new(pmpaddr_bv.clone()), Box::new(pmpaddr_plus_one));
    let begin_words_bv = SmtExp::Bvand(Box::new(pmpaddr_bv), Box::new(SmtExp::Bvnot(Box::new(mask_bv.clone()))));
    let begin_words = unsigned_bv_exp_to_i128(begin_words_bv, addr_width)?;
    let mask = unsigned_bv_exp_to_i128(mask_bv, addr_width)?;
    let end_words =
        SmtExp::Bvadd(Box::new(SmtExp::Bvadd(Box::new(begin_words.clone()), Box::new(mask))), Box::new(smt_i128(1)));
    let napot_begin = SmtExp::Bvmul(Box::new(begin_words), Box::new(four.clone()));
    let napot_end = SmtExp::Bvmul(Box::new(end_words), Box::new(four));
    let napot_result = pmp_range_match_exp(napot_begin, napot_end, addr, width, &no_match, &partial_match, &full_match);

    Ok(Some(SmtExp::Ite(
        Box::new(SmtExp::Eq(Box::new(a_bits.clone()), Box::new(smt_sbits(B::new(0, 2))))),
        Box::new(no_match),
        Box::new(SmtExp::Ite(
            Box::new(SmtExp::Eq(Box::new(a_bits.clone()), Box::new(smt_sbits(B::new(1, 2))))),
            Box::new(tor_result),
            Box::new(SmtExp::Ite(
                Box::new(SmtExp::Eq(Box::new(a_bits), Box::new(smt_sbits(B::new(2, 2))))),
                Box::new(na4_result),
                Box::new(napot_result),
            )),
        )),
    )))
}

fn pmp_range_match_builtin<B: BV>(
    args: &[Val<B>],
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let begin = int_value_exp(&args[0], info)?;
    let end = int_value_exp(&args[1], info)?;
    let addr = int_value_exp(&args[2], info)?;
    let width = int_value_exp(&args[3], info)?;

    let no_match = pmp_addr_match_enum("zPMP_NoMatch", shared_state, solver, info)?;
    let partial_match = pmp_addr_match_enum("zPMP_PartialMatch", shared_state, solver, info)?;
    let full_match = pmp_addr_match_enum("zPMP_Match", shared_state, solver, info)?;

    Ok(Some(smt_exp_to_value(
        pmp_range_match_exp(begin, end, addr, width, &no_match, &partial_match, &full_match),
        solver,
    )?))
}

fn pma_check_builtin<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some(computation) = pma_check_compute(args, frame, shared_state, solver, info)? else {
        return Ok(None);
    };
    let PmaCheckComputation { access_fault_cond, access_fault, alignment_fault_cond, alignment_fault, effects } =
        computation;
    commit_pending_builtin_effects(effects, solver);
    option_exception_from_fault_conds(
        access_fault_cond,
        access_fault,
        alignment_fault_cond,
        alignment_fault,
        shared_state,
        solver,
        info,
    )
    .map(Some)
}

fn pma_check_compute<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<PmaCheckComputation<B>>, ExecError> {
    if !function_returns_literal_false("zget_config_print_pma", shared_state) {
        log!(log::VERBOSE, "pmaCheck builtin fallback: get_config_print_pma is not literal false");
        return Ok(None);
    }

    let Some(width) = concrete_width_bytes(&args[1]) else {
        log!(log::VERBOSE, "pmaCheck builtin fallback: symbolic width");
        return Ok(None);
    };
    if width == 0 {
        log!(log::VERBOSE, "pmaCheck builtin fallback: zero width");
        return Ok(None);
    }

    let Some((addr, addr_width)) = bitvector_exp_and_width(&args[0], solver, info)? else {
        log!(log::VERBOSE, "pmaCheck builtin fallback: unsupported paddr");
        return Ok(None);
    };
    if addr_width == 0 || addr_width > 64 {
        log!(log::VERBOSE, "pmaCheck builtin fallback: unsupported paddr width");
        return Ok(None);
    }
    let addr = if addr_width == 64 { addr } else { SmtExp::ZeroExtend(64 - addr_width, Box::new(addr)) };
    let width_bits = smt_sbits(B::new(u64::from(width), 64));
    let zero64 = smt_sbits(B::new(0, 64));
    let mut assume_aligned = false;
    let misaligned = match is_concretely_aligned(&args[0], width) {
        Some(true) => SmtExp::Bool(false),
        Some(false) => SmtExp::Bool(true),
        None if env_flag("ISLA_RISCV_VMEM_ASSUME_ALIGNED") => {
            assume_aligned = true;
            SmtExp::Bool(false)
        }
        None => SmtExp::Not(Box::new(SmtExp::Eq(
            Box::new(SmtExp::Bvurem(Box::new(addr.clone()), Box::new(width_bits.clone()))),
            Box::new(zero64),
        ))),
    };

    let Some(access_fault) = access_fault_from_access_type_value(&args[2], shared_state, info)? else {
        log!(log::VERBOSE, "pmaCheck builtin fallback: unsupported access fault");
        return Ok(None);
    };
    let Some(alignment_fault) = alignment_fault_from_access_type_value(&args[2], shared_state, info)? else {
        log!(log::VERBOSE, "pmaCheck builtin fallback: unsupported alignment fault");
        return Ok(None);
    };

    let pma_regions_name = lookup_required_symbol("zpma_regions", shared_state, info)?;
    let Some(pma_regions) = read_register_value_cloned(frame, pma_regions_name, shared_state, solver, info)? else {
        log!(log::VERBOSE, "pmaCheck builtin fallback: missing pma_regions register");
        return Ok(None);
    };
    let Val::List(regions) = &pma_regions else {
        log!(log::VERBOSE, "pmaCheck builtin fallback: pma_regions is not a list");
        return Ok(None);
    };

    let mut no_match_so_far = SmtExp::Bool(true);
    let mut access_fault_cond = SmtExp::Bool(false);
    let mut alignment_fault_cond = SmtExp::Bool(false);

    for region in regions.iter().rev() {
        let Some((match_cond, attributes)) =
            pma_region_match_exp(region, &addr, &width_bits, shared_state, solver, info)?
        else {
            log!(log::VERBOSE, "pmaCheck builtin fallback: unsupported PMA region");
            return Ok(None);
        };
        let Some(can_access) = pma_access_permitted_exp(attributes, &args[2], &args[3], shared_state, solver, info)?
        else {
            log!(log::VERBOSE, "pmaCheck builtin fallback: unsupported PMA access expression");
            return Ok(None);
        };
        let Some(misaligned_access_fault_mode) =
            pma_enum_field_eq_exp(attributes, "zmisaligned_fault", "zAccessFault", shared_state, solver, info)?
        else {
            log!(log::VERBOSE, "pmaCheck builtin fallback: unsupported PMA misaligned access-fault mode");
            return Ok(None);
        };
        let Some(misaligned_alignment_fault_mode) =
            pma_enum_field_eq_exp(attributes, "zmisaligned_fault", "zAlignmentFault", shared_state, solver, info)?
        else {
            log!(log::VERBOSE, "pmaCheck builtin fallback: unsupported PMA misaligned alignment-fault mode");
            return Ok(None);
        };

        let selected = SmtExp::And(Box::new(no_match_so_far.clone()), Box::new(match_cond.clone()));
        let misaligned_access_fault = SmtExp::And(
            Box::new(selected.clone()),
            Box::new(SmtExp::And(Box::new(misaligned.clone()), Box::new(misaligned_access_fault_mode.clone()))),
        );
        let misaligned_alignment_fault = SmtExp::And(
            Box::new(selected.clone()),
            Box::new(SmtExp::And(Box::new(misaligned.clone()), Box::new(misaligned_alignment_fault_mode.clone()))),
        );
        let misaligned_exception = SmtExp::And(
            Box::new(misaligned.clone()),
            Box::new(SmtExp::Or(Box::new(misaligned_access_fault_mode), Box::new(misaligned_alignment_fault_mode))),
        );
        let permission_fault = SmtExp::And(
            Box::new(selected),
            Box::new(SmtExp::And(
                Box::new(SmtExp::Not(Box::new(misaligned_exception))),
                Box::new(SmtExp::Not(Box::new(can_access))),
            )),
        );

        access_fault_cond = SmtExp::Or(
            Box::new(access_fault_cond),
            Box::new(SmtExp::Or(Box::new(misaligned_access_fault), Box::new(permission_fault))),
        );
        alignment_fault_cond = SmtExp::Or(Box::new(alignment_fault_cond), Box::new(misaligned_alignment_fault));
        no_match_so_far = SmtExp::And(Box::new(no_match_so_far), Box::new(SmtExp::Not(Box::new(match_cond))));
    }

    if smt_bool_is(&misaligned, false) {
        alignment_fault_cond = SmtExp::Bool(false);
    }
    access_fault_cond = SmtExp::Or(Box::new(access_fault_cond), Box::new(no_match_so_far));
    let mut effects = vec![PendingBuiltinEffect::ReadReg(pma_regions_name, pma_regions)];
    if assume_aligned {
        if let Some(assertion) = plain_vmem_alignment_assert_exp(&args[0], width, info)? {
            effects.push(PendingBuiltinEffect::Assert(assertion));
        }
    }
    Ok(Some(PmaCheckComputation { access_fault_cond, access_fault, alignment_fault_cond, alignment_fault, effects }))
}

fn phys_access_check_builtin<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if !env_flag("ISLA_RISCV_BUILTIN_PMP_CHECK") || !env_flag("ISLA_RISCV_BUILTIN_PMA_CHECK") {
        log!(log::VERBOSE, "phys_access_check builtin fallback: PMP/PMA summaries are not both enabled");
        return Ok(None);
    }

    let pmp_args = vec![args[2].clone(), args[3].clone(), args[0].clone(), args[1].clone()];
    let Some(pmp_result) = pmp_check_compute(&pmp_args, frame, shared_state, solver, info)? else {
        log!(log::VERBOSE, "phys_access_check builtin fallback: pmpCheck child summary did not handle call");
        return Ok(None);
    };

    let pma_args = vec![args[2].clone(), args[3].clone(), args[0].clone(), args[4].clone()];
    let Some(pma_result) = pma_check_compute(&pma_args, frame, shared_state, solver, info)? else {
        log!(log::VERBOSE, "phys_access_check builtin fallback: pmaCheck child summary did not handle call");
        return Ok(None);
    };

    let Some(pma_parts) = pma_result.parts_for_phys_access() else {
        log!(
            log::VERBOSE,
            "phys_access_check builtin fallback: pmaCheck child summary would leave symbolic inner exception"
        );
        return Ok(None);
    };
    let Some(result) = combine_phys_access_options(&pmp_result.parts, &pma_parts, shared_state, solver, info)? else {
        return Ok(None);
    };
    commit_pending_builtin_effects(pmp_result.effects, solver);
    commit_pending_builtin_effects(pma_result.effects, solver);
    Ok(Some(result))
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum ClintLoadHit {
    Msip,
    MtimecmpLow,
    MtimecmpFull,
    MtimecmpHigh,
    MtimeLow,
    MtimeFull,
    MtimeHigh,
}

fn clint_load_builtin<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if !function_returns_literal_false("zget_config_print_clint", shared_state) {
        log!(log::VERBOSE, "clint_load builtin fallback: get_config_print_clint is not literal false");
        return Ok(None);
    }

    let Some(width) = concrete_width_bytes(&args[2]) else {
        log!(log::VERBOSE, "clint_load builtin fallback: symbolic width");
        return Ok(None);
    };
    let Some((paddr, paddr_width)) = concrete_bv_u64(&args[1]) else {
        log!(log::VERBOSE, "clint_load builtin fallback: symbolic paddr");
        return Ok(None);
    };
    let Some((clint_base, clint_base_width)) = let_concrete_bv_u64("zplat_clint_base", frame, shared_state) else {
        log!(log::VERBOSE, "clint_load builtin fallback: missing concrete CLINT base");
        return Ok(None);
    };
    if paddr_width != clint_base_width {
        log!(log::VERBOSE, "clint_load builtin fallback: paddr/CLINT base width mismatch");
        return Ok(None);
    }
    let Some(offset) = paddr.checked_sub(clint_base) else {
        log!(log::VERBOSE, "clint_load builtin fallback: paddr below CLINT base");
        return Ok(None);
    };
    let Some(hit) = clint_load_exact_hit(offset, width) else {
        log!(log::VERBOSE, "clint_load builtin fallback: not a concrete exact CLINT load hit");
        return Ok(None);
    };

    let result = match hit {
        ClintLoadHit::Msip => clint_load_msip_result(width, frame, shared_state, solver, info)?,
        ClintLoadHit::MtimecmpLow => {
            clint_load_register_slice_result("zmtimecmp", 31, 0, 32, frame, shared_state, solver, info)?
        }
        ClintLoadHit::MtimecmpFull => {
            clint_load_register_slice_result("zmtimecmp", 63, 0, 64, frame, shared_state, solver, info)?
        }
        ClintLoadHit::MtimecmpHigh => {
            clint_load_register_slice_result("zmtimecmp", 63, 32, 32, frame, shared_state, solver, info)?
        }
        ClintLoadHit::MtimeLow => {
            clint_load_register_slice_result("zmtime", 31, 0, 32, frame, shared_state, solver, info)?
        }
        ClintLoadHit::MtimeFull => {
            clint_load_register_slice_result("zmtime", 63, 0, 64, frame, shared_state, solver, info)?
        }
        ClintLoadHit::MtimeHigh => {
            clint_load_register_slice_result("zmtime", 63, 32, 32, frame, shared_state, solver, info)?
        }
    };
    Ok(Some(result))
}

fn clint_load_exact_hit(offset: u64, width: u32) -> Option<ClintLoadHit> {
    match (offset, width) {
        (0x0000, 4 | 8) => Some(ClintLoadHit::Msip),
        (0x4000, 4) => Some(ClintLoadHit::MtimecmpLow),
        (0x4000, 8) => Some(ClintLoadHit::MtimecmpFull),
        (0x4004, 4) => Some(ClintLoadHit::MtimecmpHigh),
        (0xbff8, 4) => Some(ClintLoadHit::MtimeLow),
        (0xbff8, 8) => Some(ClintLoadHit::MtimeFull),
        (0xbffc, 4) => Some(ClintLoadHit::MtimeHigh),
        _ => None,
    }
}

fn clint_load_msip_result<'ir, B: BV>(
    width: u32,
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let mip_name = lookup_required_symbol("zmip", shared_state, info)?;
    let Some(mip) = read_register_cloned(frame, mip_name, shared_state, solver, info)? else {
        return Err(ExecError::Type("clint_load builtin expected mip register".to_string(), info));
    };
    let Some(bits) = struct_field_value(&mip, "zbits", shared_state, info)? else {
        return Err(ExecError::Type("clint_load builtin expected mip.bits field".to_string(), info));
    };
    let Some((bits, bits_width)) = bitvector_exp_and_width(bits, solver, info)? else {
        return Err(ExecError::Type("clint_load builtin expected mip.bits bitvector".to_string(), info));
    };
    if bits_width <= 3 {
        return Err(ExecError::Type("clint_load builtin expected mip.bits to contain MSI".to_string(), info));
    }
    let target_width =
        width.checked_mul(8).ok_or_else(|| ExecError::Type("clint_load builtin width overflow".to_string(), info))?;
    let msi = SmtExp::Extract(3, 3, Box::new(bits));
    clint_load_ok_result(zero_extend_exp_to_width(msi, 1, target_width, info)?, shared_state, solver, info)
}

fn clint_load_register_slice_result<'ir, B: BV>(
    register: &str,
    high: u32,
    low: u32,
    target_width: u32,
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let register_name = lookup_required_symbol(register, shared_state, info)?;
    let Some(value) = read_register_cloned(frame, register_name, shared_state, solver, info)? else {
        return Err(ExecError::Type(format!("clint_load builtin expected {} register", register), info));
    };
    let Some((bits, bits_width)) = bitvector_exp_and_width(&value, solver, info)? else {
        return Err(ExecError::Type(format!("clint_load builtin expected {} bitvector", register), info));
    };
    if bits_width != 64 || high >= bits_width || low > high {
        return Err(ExecError::Type(format!("clint_load builtin unsupported {} width", register), info));
    }
    let slice_width = high - low + 1;
    let slice = if high == 63 && low == 0 { bits } else { SmtExp::Extract(high, low, Box::new(bits)) };
    clint_load_ok_result(zero_extend_exp_to_width(slice, slice_width, target_width, info)?, shared_state, solver, info)
}

fn clint_load_ok_result<B: BV>(
    value: SmtExp<Sym>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let ok_ctor = lookup_required_symbol("zOkzIbzCUExceptionTypezK", shared_state, info)?;
    Ok(Val::Ctor(ok_ctor, Box::new(smt_exp_to_value(value, solver)?)))
}

fn zero_extend_exp_to_width(
    exp: SmtExp<Sym>,
    from_width: u32,
    to_width: u32,
    info: SourceLoc,
) -> Result<SmtExp<Sym>, ExecError> {
    if from_width == to_width {
        Ok(exp)
    } else if from_width < to_width {
        Ok(SmtExp::ZeroExtend(to_width - from_width, Box::new(exp)))
    } else {
        Err(ExecError::Type("clint_load builtin cannot narrow result".to_string(), info))
    }
}

fn pma_region_match_exp<'a, B: BV>(
    region: &'a Val<B>,
    addr: &SmtExp<Sym>,
    width_bits: &SmtExp<Sym>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<(SmtExp<Sym>, &'a Val<B>)>, ExecError> {
    let Some(base_value) = pma_struct_field(region, "zbase", shared_state, info)? else {
        return Ok(None);
    };
    let Some((base, base_width)) = bitvector_exp_and_width(base_value, solver, info)? else {
        return Ok(None);
    };
    if base_width != 64 {
        return Ok(None);
    }

    let Some(size_value) = pma_struct_field(region, "zsizze", shared_state, info)? else {
        return Ok(None);
    };
    let Some((size, size_width)) = bitvector_exp_and_width(size_value, solver, info)? else {
        return Ok(None);
    };
    if size_width != 64 {
        return Ok(None);
    }

    let Some(attributes) = pma_struct_field(region, "zattributes", shared_state, info)? else {
        return Ok(None);
    };

    Ok(Some((range_subset_exp(addr.clone(), width_bits.clone(), base, size), attributes)))
}

fn pma_access_permitted_exp<B: BV>(
    attributes: &Val<B>,
    access: &Val<B>,
    res_or_con: &Val<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Val::Ctor(ctor, payload) = access else {
        return Ok(None);
    };

    match shared_state.symtab.to_str(*ctor) {
        "zInstructionFetchzIEmem_payloadz5zK" => pma_bool_field_exp(attributes, "zexecutable", shared_state, info),
        "zLoadzIEmem_payloadz5zK" => {
            if !matches!(res_or_con, Val::Bool(false)) {
                return Ok(None);
            }
            pma_bool_field_exp(attributes, "zreadable", shared_state, info)
        }
        "zStorezIEmem_payloadz5zK" => pma_bool_field_exp(attributes, "zwritable", shared_state, info),
        "zLoadReservedzIEmem_payloadz5zK" => {
            if !matches!(res_or_con, Val::Bool(true)) {
                return Ok(None);
            }
            let Some(readable) = pma_bool_field_exp(attributes, "zreadable", shared_state, info)? else {
                return Ok(None);
            };
            let Some(reservable) = pma_reservability_not_none_exp(attributes, shared_state, solver, info)? else {
                return Ok(None);
            };
            Ok(Some(SmtExp::And(Box::new(readable), Box::new(reservable))))
        }
        "zStoreConditionalzIEmem_payloadz5zK" => {
            if !matches!(res_or_con, Val::Bool(true)) {
                return Ok(None);
            }
            let Some(writable) = pma_bool_field_exp(attributes, "zwritable", shared_state, info)? else {
                return Ok(None);
            };
            let Some(reservable) = pma_reservability_not_none_exp(attributes, shared_state, solver, info)? else {
                return Ok(None);
            };
            Ok(Some(SmtExp::And(Box::new(writable), Box::new(reservable))))
        }
        "zAtomiczIEmem_payloadz5zK" => {
            if !matches!(res_or_con, Val::Bool(true)) {
                return Ok(None);
            }
            let Some(readable) = pma_bool_field_exp(attributes, "zreadable", shared_state, info)? else {
                return Ok(None);
            };
            let Some(writable) = pma_bool_field_exp(attributes, "zwritable", shared_state, info)? else {
                return Ok(None);
            };
            Ok(Some(SmtExp::And(Box::new(readable), Box::new(writable))))
        }
        "zCacheAccesszIEmem_payloadz5zK" => pma_cache_access_permitted_exp(payload, attributes, shared_state, info),
        _ => Ok(None),
    }
}

fn pma_cache_access_permitted_exp<B: BV>(
    cache_op: &Val<B>,
    attributes: &Val<B>,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Val::Ctor(ctor, payload) = cache_op else {
        return Ok(None);
    };

    match shared_state.symtab.to_str(*ctor) {
        "zCB_zzero" => {
            let Some(writable) = pma_bool_field_exp(attributes, "zwritable", shared_state, info)? else {
                return Ok(None);
            };
            let Some(supports_cbo_zero) = pma_bool_field_exp(attributes, "zsupports_cbo_zzero", shared_state, info)?
            else {
                return Ok(None);
            };
            Ok(Some(SmtExp::And(Box::new(writable), Box::new(supports_cbo_zero))))
        }
        "zCB_manage" => {
            let Some(readable) = pma_bool_field_exp(attributes, "zreadable", shared_state, info)? else {
                return Ok(None);
            };
            let Some(writable) = pma_bool_field_exp(attributes, "zwritable", shared_state, info)? else {
                return Ok(None);
            };
            Ok(Some(SmtExp::Or(Box::new(readable), Box::new(writable))))
        }
        "zCB_prefetch" => match payload.as_ref() {
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_R" => {
                pma_bool_field_exp(attributes, "zreadable", shared_state, info)
            }
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_W" => {
                pma_bool_field_exp(attributes, "zwritable", shared_state, info)
            }
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_I" => {
                pma_bool_field_exp(attributes, "zexecutable", shared_state, info)
            }
            _ => Ok(None),
        },
        _ => Ok(None),
    }
}

fn pma_bool_field_exp<B: BV>(
    attributes: &Val<B>,
    field: &str,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Some(value) = pma_struct_field(attributes, field, shared_state, info)? else {
        return Ok(None);
    };
    bool_exp(value)
}

fn pma_reservability_not_none_exp<B: BV>(
    attributes: &Val<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Some(value) = pma_struct_field(attributes, "zreservability", shared_state, info)? else {
        return Ok(None);
    };
    let Some(is_none) = enum_eq_exp(value, "zRsrvNone", shared_state, solver, info)? else {
        return Ok(None);
    };
    Ok(Some(SmtExp::Not(Box::new(is_none))))
}

fn pma_enum_field_eq_exp<B: BV>(
    attributes: &Val<B>,
    field: &str,
    symbol: &str,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Some(value) = pma_struct_field(attributes, field, shared_state, info)? else {
        return Ok(None);
    };
    enum_eq_exp(value, symbol, shared_state, solver, info)
}

fn pma_struct_field<'a, B: BV>(
    value: &'a Val<B>,
    field: &str,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Option<&'a Val<B>>, ExecError> {
    struct_field_value(value, field, shared_state, info)
}

fn struct_field_value<'a, B: BV>(
    value: &'a Val<B>,
    field: &str,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Option<&'a Val<B>>, ExecError> {
    let Val::Struct(fields) = value else {
        return Ok(None);
    };
    let field = lookup_required_symbol(field, shared_state, info)?;
    Ok(fields.get(&field))
}

fn bool_exp<B: BV>(value: &Val<B>) -> Result<Option<SmtExp<Sym>>, ExecError> {
    match value {
        Val::Bool(value) => Ok(Some(SmtExp::Bool(*value))),
        Val::Symbolic(sym) => Ok(Some(SmtExp::Var(*sym))),
        _ => Ok(None),
    }
}

fn enum_eq_exp<B: BV>(
    value: &Val<B>,
    symbol: &str,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    match value {
        Val::Enum(_) | Val::Symbolic(_) => Ok(Some(SmtExp::Eq(
            Box::new(smt_value(value, info)?),
            Box::new(enum_symbol_exp(symbol, shared_state, solver, info)?),
        ))),
        _ => Ok(None),
    }
}

fn pmp_check_builtin<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some(computation) = pmp_check_compute(args, frame, shared_state, solver, info)? else {
        return Ok(None);
    };
    let PmpCheckComputation { parts, effects } = computation;
    commit_pending_builtin_effects(effects, solver);
    option_exception_from_parts(&parts, shared_state, solver, info).map(Some)
}

fn pmp_check_compute<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<PmpCheckComputation<B>>, ExecError> {
    if env_flag("ISLA_RISCV_ASSUME_PMP_OFF") {
        debug_assert!(pmp_off_assumption_ignores_privilege(&args[3]));
        return Ok(Some(pmp_check_off_computation()));
    }

    let Some(sys_pmp_count) = concrete_i64_let("zsys_pmp_count", frame, shared_state) else {
        log!(log::VERBOSE, "pmpCheck builtin fallback: unknown PMP count");
        return Ok(None);
    };
    if sys_pmp_count == 0 {
        return Ok(Some(PmpCheckComputation {
            parts: OptionExceptionParts { is_some: SmtExp::Bool(false), fault: None },
            effects: Vec::new(),
        }));
    }
    let Ok(sys_pmp_count) = usize::try_from(sys_pmp_count) else {
        log!(log::VERBOSE, "pmpCheck builtin fallback: negative PMP count");
        return Ok(None);
    };
    if sys_pmp_count > 64 {
        log!(log::VERBOSE, "pmpCheck builtin fallback: unsupported PMP count");
        return Ok(None);
    }

    match concrete_i64_let("zsys_pmp_grain", frame, shared_state) {
        Some(0) => {}
        Some(_) => {
            log!(log::VERBOSE, "pmpCheck builtin fallback: non-zero PMP grain");
            return Ok(None);
        }
        None => {
            log!(log::VERBOSE, "pmpCheck builtin fallback: unknown PMP grain");
            return Ok(None);
        }
    }

    let Some(priv_is_machine) = concrete_priv_is_machine(&args[3], shared_state) else {
        log!(log::VERBOSE, "pmpCheck builtin fallback: symbolic privilege");
        return Ok(None);
    };
    let Some(fault) = access_fault_from_access_type_value(&args[2], shared_state, info)? else {
        log!(log::VERBOSE, "pmpCheck builtin fallback: unsupported access fault");
        return Ok(None);
    };

    let pmpcfg_name = lookup_required_symbol("zpmpcfg_n", shared_state, info)?;
    let pmpaddr_name = lookup_required_symbol("zpmpaddr_n", shared_state, info)?;
    let Some(pmpcfg_vector) = read_register_value_cloned(frame, pmpcfg_name, shared_state, solver, info)? else {
        log!(log::VERBOSE, "pmpCheck builtin fallback: missing pmpcfg_n register");
        return Ok(None);
    };
    let Some(pmpaddr_vector) = read_register_value_cloned(frame, pmpaddr_name, shared_state, solver, info)? else {
        log!(log::VERBOSE, "pmpCheck builtin fallback: missing pmpaddr_n register");
        return Ok(None);
    };

    let no_match = pmp_addr_match_enum("zPMP_NoMatch", shared_state, solver, info)?;
    let partial_match = pmp_addr_match_enum("zPMP_PartialMatch", shared_state, solver, info)?;
    let full_match = pmp_addr_match_enum("zPMP_Match", shared_state, solver, info)?;

    let mut no_match_so_far = SmtExp::Bool(true);
    let mut fault_cond = SmtExp::Bool(false);

    for i in 0..sys_pmp_count {
        let Some(cfg) = vector_entry(&pmpcfg_vector, i) else {
            log!(log::VERBOSE, "pmpCheck builtin fallback: pmpcfg_n entry missing");
            return Ok(None);
        };
        let Some(pmpaddr) = vector_entry(&pmpaddr_vector, i) else {
            log!(log::VERBOSE, "pmpCheck builtin fallback: pmpaddr_n entry missing");
            return Ok(None);
        };
        let Some(pmpaddr_width) = bitvector_width(&pmpaddr, solver) else {
            log!(log::VERBOSE, "pmpCheck builtin fallback: pmpaddr_n entry is not a bitvector");
            return Ok(None);
        };
        let Some(width_bits) = concrete_i64_as_bv_width(&args[1], pmpaddr_width) else {
            log!(log::VERBOSE, "pmpCheck builtin fallback: unsupported width");
            return Ok(None);
        };
        let prev_pmpaddr = if i == 0 {
            Val::Bits(B::zeros(pmpaddr_width))
        } else {
            let Some(prev) = vector_entry(&pmpaddr_vector, i - 1) else {
                log!(log::VERBOSE, "pmpCheck builtin fallback: previous pmpaddr_n entry missing");
                return Ok(None);
            };
            prev
        };

        let Some(match_result) =
            pmp_match_addr_exp(&args[0], &width_bits, &cfg, &pmpaddr, &prev_pmpaddr, shared_state, solver, info)?
        else {
            log!(log::VERBOSE, "pmpCheck builtin fallback: unsupported pmpMatchAddr subexpression");
            return Ok(None);
        };
        let is_no_match = SmtExp::Eq(Box::new(match_result.clone()), Box::new(no_match.clone()));
        let is_partial_match = SmtExp::Eq(Box::new(match_result.clone()), Box::new(partial_match.clone()));
        let is_full_match = SmtExp::Eq(Box::new(match_result), Box::new(full_match.clone()));

        let rwx = match pmp_check_rwx_exp(&cfg, &args[2], shared_state, solver, info)? {
            Some(rwx) => rwx,
            None => {
                log!(log::VERBOSE, "pmpCheck builtin fallback: unsupported pmpCheckRWX subexpression");
                return Ok(None);
            }
        };
        let Some(locked) = pmpcfg_bit_is_set(&cfg, 7, shared_state, solver, info)? else {
            log!(log::VERBOSE, "pmpCheck builtin fallback: unsupported pmpLocked subexpression");
            return Ok(None);
        };
        let allowed =
            if priv_is_machine { SmtExp::Or(Box::new(rwx), Box::new(SmtExp::Not(Box::new(locked)))) } else { rwx };

        let partial_fault = SmtExp::And(Box::new(no_match_so_far.clone()), Box::new(is_partial_match));
        let match_fault = SmtExp::And(
            Box::new(no_match_so_far.clone()),
            Box::new(SmtExp::And(Box::new(is_full_match), Box::new(SmtExp::Not(Box::new(allowed))))),
        );
        fault_cond =
            SmtExp::Or(Box::new(fault_cond), Box::new(SmtExp::Or(Box::new(partial_fault), Box::new(match_fault))));
        no_match_so_far = SmtExp::And(Box::new(no_match_so_far), Box::new(is_no_match));
    }

    if !priv_is_machine {
        fault_cond = SmtExp::Or(Box::new(fault_cond), Box::new(no_match_so_far));
    }

    Ok(Some(PmpCheckComputation {
        parts: OptionExceptionParts { is_some: fault_cond, fault: Some(fault) },
        effects: vec![
            PendingBuiltinEffect::ReadReg(pmpcfg_name, pmpcfg_vector),
            PendingBuiltinEffect::ReadReg(pmpaddr_name, pmpaddr_vector),
        ],
    }))
}

fn pmp_check_off_builtin<B: BV>(
    args: &[Val<B>],
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    debug_assert!(pmp_off_assumption_ignores_privilege(&args[3]));
    let none_ctor = lookup_required_symbol("zNonezIUExceptionTypezK", shared_state, info)?;
    Ok(Some(Val::Ctor(none_ctor, Box::new(Val::Unit))))
}

fn pmp_check_off_computation<B: BV>() -> PmpCheckComputation<B> {
    PmpCheckComputation {
        parts: OptionExceptionParts { is_some: SmtExp::Bool(false), fault: None },
        effects: Vec::new(),
    }
}

fn pmp_off_assumption_ignores_privilege<B: BV>(_privilege: &Val<B>) -> bool {
    true
}

fn concrete_priv_is_machine<B: BV>(value: &Val<B>, shared_state: &SharedState<B>) -> Option<bool> {
    match value {
        Val::Enum(member) => Some(shared_state.symtab.to_str(member.to_name(shared_state)) == "zMachine"),
        _ => None,
    }
}

fn concrete_i64_as_bv_width<B: BV>(value: &Val<B>, width: u32) -> Option<Val<B>> {
    match value.clone().widen_int() {
        Val::I128(value) => u64::try_from(value).ok().map(|value| Val::Bits(B::new(value, width))),
        _ => None,
    }
}

fn read_register_cloned<'ir, B: BV>(
    frame: &mut LocalFrame<'ir, B>,
    name: Name,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let value = read_register_value_cloned(frame, name, shared_state, solver, info)?;
    if let Some(value) = &value {
        add_read_register_event(solver, name, value);
    }
    Ok(value)
}

fn read_register_value_cloned<'ir, B: BV>(
    frame: &mut LocalFrame<'ir, B>,
    name: Name,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    frame.regs_mut().get(name, shared_state, solver, info).map(|value| value.cloned())
}

fn add_read_register_event<B: BV>(solver: &mut Solver<B>, name: Name, value: &Val<B>) {
    solver.add_event(Event::ReadReg(name, Vec::new(), value.clone()));
}

fn vector_entry<B: BV>(value: &Val<B>, index: usize) -> Option<Val<B>> {
    match value {
        Val::Vector(entries) => entries.get(index).cloned(),
        _ => None,
    }
}

fn function_returns_literal_false<B: BV>(function_name: &str, shared_state: &SharedState<B>) -> bool {
    let Some(function) = shared_state.symtab.get(function_name) else {
        return false;
    };
    let Some((_, _, instrs)) = shared_state.functions.get(&function) else {
        return false;
    };

    let mut saw_false_return = false;
    for instr in *instrs {
        match instr {
            Instr::Copy(Loc::Id(id), Exp::Bool(false), _) if *id == RETURN => saw_false_return = true,
            Instr::End => return saw_false_return,
            _ => return false,
        }
    }
    false
}

fn htif_tohost_base_is_none<B: BV>(frame: &LocalFrame<B>, shared_state: &SharedState<B>) -> bool {
    let Some(htif_base) = shared_state.symtab.get("zhtif_tohost_base") else {
        return false;
    };
    matches!(
        frame.regs().get_last_if_initialized(htif_base),
        Some(Val::Ctor(ctor, _)) if shared_state.symtab.to_str(*ctor) == "zNonezIbzK"
    )
}

fn let_bitvector_exp_and_width<B: BV>(
    name: &str,
    frame: &LocalFrame<B>,
    shared_state: &SharedState<B>,
) -> Option<(SmtExp<Sym>, u32)> {
    let name = shared_state.symtab.get(name)?;
    match frame.lets().get(&name) {
        Some(UVal::Init(Val::Bits(bits))) => Some((smt_sbits(*bits), bits.len())),
        _ => None,
    }
}

fn let_concrete_bv_u64<B: BV>(name: &str, frame: &LocalFrame<B>, shared_state: &SharedState<B>) -> Option<(u64, u32)> {
    let name = shared_state.symtab.get(name)?;
    match frame.lets().get(&name) {
        Some(UVal::Init(value)) => concrete_bv_u64(value),
        _ => None,
    }
}

fn concrete_bv_u64<B: BV>(value: &Val<B>) -> Option<(u64, u32)> {
    match value {
        Val::Bits(bits) if bits.len() <= 64 => Some((bits.lower_u64(), bits.len())),
        _ => None,
    }
}

fn access_fault_from_access_type_value<B: BV>(
    access: &Val<B>,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some(exception_ctor) = access_fault_ctor_name(access, shared_state) else {
        return Ok(None);
    };
    let exception_ctor = lookup_required_symbol(exception_ctor, shared_state, info)?;
    Ok(Some(Val::Ctor(exception_ctor, Box::new(Val::Unit))))
}

fn alignment_fault_from_access_type_value<B: BV>(
    access: &Val<B>,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some(exception_ctor) = alignment_fault_ctor_name(access, shared_state) else {
        return Ok(None);
    };
    let exception_ctor = lookup_required_symbol(exception_ctor, shared_state, info)?;
    Ok(Some(Val::Ctor(exception_ctor, Box::new(Val::Unit))))
}

fn access_fault_ctor_name<B: BV>(access: &Val<B>, shared_state: &SharedState<B>) -> Option<&'static str> {
    let Val::Ctor(ctor, payload) = access else {
        return None;
    };
    match shared_state.symtab.to_str(*ctor) {
        "zInstructionFetchzIEmem_payloadz5zK" => Some("zE_Fetch_Access_Fault"),
        "zLoadzIEmem_payloadz5zK" | "zLoadReservedzIEmem_payloadz5zK" => Some("zE_Load_Access_Fault"),
        "zStorezIEmem_payloadz5zK" | "zStoreConditionalzIEmem_payloadz5zK" | "zAtomiczIEmem_payloadz5zK" => {
            Some("zE_SAMO_Access_Fault")
        }
        "zCacheAccesszIEmem_payloadz5zK" => cache_access_fault_ctor_name(payload, shared_state),
        _ => None,
    }
}

fn alignment_fault_ctor_name<B: BV>(access: &Val<B>, shared_state: &SharedState<B>) -> Option<&'static str> {
    let Val::Ctor(ctor, payload) = access else {
        return None;
    };
    match shared_state.symtab.to_str(*ctor) {
        "zInstructionFetchzIEmem_payloadz5zK" => Some("zE_Fetch_Addr_Align"),
        "zLoadzIEmem_payloadz5zK" | "zLoadReservedzIEmem_payloadz5zK" => Some("zE_Load_Addr_Align"),
        "zStorezIEmem_payloadz5zK" | "zStoreConditionalzIEmem_payloadz5zK" | "zAtomiczIEmem_payloadz5zK" => {
            Some("zE_SAMO_Addr_Align")
        }
        "zCacheAccesszIEmem_payloadz5zK" => cache_alignment_fault_ctor_name(payload, shared_state),
        _ => None,
    }
}

fn cache_access_fault_ctor_name<B: BV>(cache_op: &Val<B>, shared_state: &SharedState<B>) -> Option<&'static str> {
    let Val::Ctor(ctor, payload) = cache_op else {
        return None;
    };
    match shared_state.symtab.to_str(*ctor) {
        "zCB_manage" | "zCB_zzero" => Some("zE_SAMO_Access_Fault"),
        "zCB_prefetch" => match payload.as_ref() {
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_R" => {
                Some("zE_Load_Access_Fault")
            }
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_W" => {
                Some("zE_SAMO_Access_Fault")
            }
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_I" => {
                Some("zE_Fetch_Access_Fault")
            }
            _ => None,
        },
        _ => None,
    }
}

fn cache_alignment_fault_ctor_name<B: BV>(cache_op: &Val<B>, shared_state: &SharedState<B>) -> Option<&'static str> {
    let Val::Ctor(ctor, payload) = cache_op else {
        return None;
    };
    match shared_state.symtab.to_str(*ctor) {
        "zCB_manage" | "zCB_zzero" => Some("zE_SAMO_Addr_Align"),
        "zCB_prefetch" => match payload.as_ref() {
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_R" => {
                Some("zE_Load_Addr_Align")
            }
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_W" => {
                Some("zE_SAMO_Addr_Align")
            }
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_I" => {
                Some("zE_Fetch_Addr_Align")
            }
            _ => None,
        },
        _ => None,
    }
}

enum PendingBuiltinEffect<B: BV> {
    ReadReg(Name, Val<B>),
    Assert(SmtExp<Sym>),
}

fn commit_pending_builtin_effects<B: BV>(effects: Vec<PendingBuiltinEffect<B>>, solver: &mut Solver<B>) {
    for effect in effects {
        match effect {
            PendingBuiltinEffect::ReadReg(name, value) => add_read_register_event(solver, name, &value),
            PendingBuiltinEffect::Assert(assertion) => solver.add(Def::Assert(assertion)),
        }
    }
}

struct PmpCheckComputation<B: BV> {
    parts: OptionExceptionParts<B>,
    effects: Vec<PendingBuiltinEffect<B>>,
}

struct PmaCheckComputation<B: BV> {
    access_fault_cond: SmtExp<Sym>,
    access_fault: Val<B>,
    alignment_fault_cond: SmtExp<Sym>,
    alignment_fault: Val<B>,
    effects: Vec<PendingBuiltinEffect<B>>,
}

impl<B: BV> PmaCheckComputation<B> {
    fn parts_for_phys_access(&self) -> Option<OptionExceptionParts<B>> {
        if smt_bool_is(&self.alignment_fault_cond, false) {
            return Some(OptionExceptionParts {
                is_some: self.access_fault_cond.clone(),
                fault: Some(self.access_fault.clone()),
            });
        }
        if smt_bool_is(&self.access_fault_cond, false) {
            return Some(OptionExceptionParts {
                is_some: self.alignment_fault_cond.clone(),
                fault: Some(self.alignment_fault.clone()),
            });
        }
        if self.access_fault == self.alignment_fault {
            return Some(OptionExceptionParts {
                is_some: SmtExp::Or(
                    Box::new(self.access_fault_cond.clone()),
                    Box::new(self.alignment_fault_cond.clone()),
                ),
                fault: Some(self.access_fault.clone()),
            });
        }
        None
    }
}

struct OptionExceptionParts<B: BV> {
    is_some: SmtExp<Sym>,
    fault: Option<Val<B>>,
}

fn combine_phys_access_options<B: BV>(
    pmp: &OptionExceptionParts<B>,
    pma: &OptionExceptionParts<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if smt_bool_is(&pmp.is_some, false) {
        return option_exception_from_parts(pma, shared_state, solver, info).map(Some);
    }
    if smt_bool_is(&pma.is_some, false) {
        return option_exception_from_parts(pmp, shared_state, solver, info).map(Some);
    }

    let fault_cond = SmtExp::Or(Box::new(pmp.is_some.clone()), Box::new(pma.is_some.clone()));
    let Some(fault) = selected_phys_access_fault(pmp, pma, shared_state, solver, info)? else {
        log!(log::VERBOSE, "phys_access_check builtin fallback: symbolic inner exception would remain");
        return Ok(None);
    };
    option_exception_from_fault_cond(fault_cond, fault, shared_state, solver, info).map(Some)
}

fn option_exception_from_parts<B: BV>(
    parts: &OptionExceptionParts<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if smt_bool_is(&parts.is_some, false) {
        let none_ctor = lookup_required_symbol("zNonezIUExceptionTypezK", shared_state, info)?;
        return Ok(Val::Ctor(none_ctor, Box::new(Val::Unit)));
    }
    let fault = required_option_fault(parts, "phys_access_check builtin expected Some fault", info)?;
    option_exception_from_fault_cond(parts.is_some.clone(), fault.clone(), shared_state, solver, info)
}

fn selected_phys_access_fault<B: BV>(
    pmp: &OptionExceptionParts<B>,
    pma: &OptionExceptionParts<B>,
    shared_state: &SharedState<B>,
    _solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let pmp_fault = required_option_fault(pmp, "phys_access_check builtin expected PMP fault", info)?;
    let pma_fault = required_option_fault(pma, "phys_access_check builtin expected PMA fault", info)?;
    let Some((pmp_ctor, pmp_payload)) = concrete_exception_ctor_payload_or_fallback(pmp_fault, "PMP", info)? else {
        return Ok(None);
    };
    let Some((pma_ctor, pma_payload)) = concrete_exception_ctor_payload_or_fallback(pma_fault, "PMA", info)? else {
        return Ok(None);
    };
    let pmp_name = shared_state.symtab.to_str(pmp_ctor);
    let pma_name = shared_state.symtab.to_str(pma_ctor);
    let Some(chosen) = highest_priority_alignment_or_access_fault_name(pmp_name, pma_name) else {
        return Err(ExecError::Type(
            format!("phys_access_check builtin cannot prioritize {} vs {}", pmp_name, pma_name),
            info,
        ));
    };
    let (both_ctor, both_payload) =
        if chosen == pmp_name { (pmp_ctor, pmp_payload.clone()) } else { (pma_ctor, pma_payload.clone()) };

    if smt_bool_is(&pmp.is_some, true) && smt_bool_is(&pma.is_some, true) {
        return Ok(Some(Val::Ctor(both_ctor, Box::new(both_payload))));
    }
    if smt_bool_is(&pmp.is_some, true) && smt_bool_is(&pma.is_some, false) {
        return Ok(Some(Val::Ctor(pmp_ctor, Box::new(pmp_payload))));
    }
    if smt_bool_is(&pmp.is_some, false) && smt_bool_is(&pma.is_some, true) {
        return Ok(Some(Val::Ctor(pma_ctor, Box::new(pma_payload))));
    }
    if pmp_ctor == pma_ctor && pmp_payload == pma_payload && pmp_ctor == both_ctor && pmp_payload == both_payload {
        return Ok(Some(Val::Ctor(pmp_ctor, Box::new(pmp_payload))));
    }

    if phys_access_fault_selection_requires_fallback(pmp, pma) {
        return Ok(None);
    }

    Ok(None)
}

fn phys_access_fault_selection_requires_fallback<B: BV>(
    pmp: &OptionExceptionParts<B>,
    pma: &OptionExceptionParts<B>,
) -> bool {
    if smt_bool_is(&pmp.is_some, false) || smt_bool_is(&pma.is_some, false) {
        return false;
    }
    if smt_bool_is(&pmp.is_some, true) && smt_bool_is(&pma.is_some, true) {
        return false;
    }
    pmp.fault != pma.fault
}

fn required_option_fault<'a, B: BV>(
    parts: &'a OptionExceptionParts<B>,
    context: &str,
    info: SourceLoc,
) -> Result<&'a Val<B>, ExecError> {
    parts.fault.as_ref().ok_or_else(|| ExecError::Type(context.to_string(), info))
}

fn concrete_exception_ctor_payload_or_fallback<B: BV>(
    value: &Val<B>,
    context: &str,
    info: SourceLoc,
) -> Result<Option<(Name, Val<B>)>, ExecError> {
    match value {
        Val::Ctor(ctor, payload) => Ok(Some((*ctor, payload.as_ref().clone()))),
        Val::SymbolicCtor(_, _) => Ok(None),
        _ => Err(ExecError::Type(format!("phys_access_check builtin expected concrete {} exception", context), info)),
    }
}

fn highest_priority_alignment_or_access_fault_name<'a>(left: &'a str, right: &'a str) -> Option<&'a str> {
    let left_priority = alignment_or_access_fault_priority_name(left)?;
    let right_priority = alignment_or_access_fault_priority_name(right)?;
    if left_priority > right_priority {
        Some(left)
    } else {
        Some(right)
    }
}

fn alignment_or_access_fault_priority_name(name: &str) -> Option<u8> {
    match name {
        "zE_Fetch_Addr_Align" | "zE_Load_Addr_Align" | "zE_SAMO_Addr_Align" => Some(0),
        "zE_Fetch_Access_Fault" | "zE_Load_Access_Fault" | "zE_SAMO_Access_Fault" => Some(1),
        _ => None,
    }
}

fn option_exception_from_fault_cond<B: BV>(
    fault_cond: SmtExp<Sym>,
    fault: Val<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let some_ctor = lookup_required_symbol("zSomezIUExceptionTypezK", shared_state, info)?;
    let none_ctor = lookup_required_symbol("zNonezIUExceptionTypezK", shared_state, info)?;
    if smt_bool_is(&fault_cond, false) {
        return Ok(Val::Ctor(none_ctor, Box::new(Val::Unit)));
    }
    if smt_bool_is(&fault_cond, true) {
        return Ok(Val::Ctor(some_ctor, Box::new(fault)));
    }
    let discrim = solver.define_const(
        SmtExp::Ite(Box::new(fault_cond), Box::new(some_ctor.to_smt()), Box::new(none_ctor.to_smt())),
        info,
    );

    let mut possibilities = HashMap::default();
    possibilities.insert(some_ctor, fault);
    possibilities.insert(none_ctor, Val::Unit);
    Ok(Val::SymbolicCtor(discrim, possibilities))
}

fn option_exception_from_fault_conds<B: BV>(
    access_fault_cond: SmtExp<Sym>,
    access_fault: Val<B>,
    alignment_fault_cond: SmtExp<Sym>,
    alignment_fault: Val<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if smt_bool_is(&alignment_fault_cond, false) {
        return option_exception_from_fault_cond(access_fault_cond, access_fault, shared_state, solver, info);
    }
    if smt_bool_is(&access_fault_cond, false) {
        return option_exception_from_fault_cond(alignment_fault_cond, alignment_fault, shared_state, solver, info);
    }

    let fault_cond = SmtExp::Or(Box::new(access_fault_cond), Box::new(alignment_fault_cond.clone()));
    if access_fault == alignment_fault {
        return option_exception_from_fault_cond(fault_cond, access_fault, shared_state, solver, info);
    }

    let (Val::Ctor(access_ctor, access_payload), Val::Ctor(alignment_ctor, alignment_payload)) =
        (access_fault, alignment_fault)
    else {
        return Err(ExecError::Type("pmaCheck builtin expected concrete exception constructors".to_string(), info));
    };

    let discrim = solver.define_const(
        SmtExp::Ite(Box::new(alignment_fault_cond), Box::new(alignment_ctor.to_smt()), Box::new(access_ctor.to_smt())),
        info,
    );

    let mut possibilities = HashMap::default();
    possibilities.insert(access_ctor, *access_payload);
    possibilities.insert(alignment_ctor, *alignment_payload);
    option_exception_from_fault_cond(fault_cond, Val::SymbolicCtor(discrim, possibilities), shared_state, solver, info)
}

fn smt_bool_is(exp: &SmtExp<Sym>, value: bool) -> bool {
    matches!(exp, SmtExp::Bool(actual) if *actual == value)
}

fn int_value_exp<B: BV>(value: &Val<B>, info: SourceLoc) -> Result<SmtExp<Sym>, ExecError> {
    match value {
        Val::I128(value) => Ok(smt_i128(*value)),
        Val::I64(value) => Ok(smt_i128(i128::from(*value))),
        Val::Symbolic(sym) => Ok(SmtExp::Var(*sym)),
        _ => Err(ExecError::Type(format!("integer expression {:?}", value), info)),
    }
}

fn concrete_i64_let<B: BV>(name: &str, frame: &LocalFrame<B>, shared_state: &SharedState<B>) -> Option<i64> {
    shared_state.symtab.get(name).and_then(|name| match frame.lets().get(&name) {
        Some(UVal::Init(Val::I64(value))) => Some(*value),
        _ => None,
    })
}

fn bitvector_exp_and_width<B: BV>(
    value: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<(SmtExp<Sym>, u32)>, ExecError> {
    let Some(width) = bitvector_width(value, solver) else {
        return Ok(None);
    };
    Ok(Some((smt_value(value, info)?, width)))
}

fn pmpcfg_a_bits<B: BV>(
    ent: &Val<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Val::Struct(fields) = ent else {
        return Ok(None);
    };
    let bits_field = lookup_required_symbol("zbits", shared_state, info)?;
    let Some(bits) = fields.get(&bits_field) else {
        return Ok(None);
    };
    let Some((bits, width)) = bitvector_exp_and_width(bits, solver, info)? else {
        return Ok(None);
    };
    if width != 8 {
        return Ok(None);
    }
    Ok(Some(SmtExp::Extract(4, 3, Box::new(bits))))
}

fn pmpcfg_bit_is_set<B: BV>(
    ent: &Val<B>,
    bit: u32,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Val::Struct(fields) = ent else {
        return Ok(None);
    };
    let bits_field = lookup_required_symbol("zbits", shared_state, info)?;
    let Some(bits) = fields.get(&bits_field) else {
        return Ok(None);
    };
    let Some((bits, width)) = bitvector_exp_and_width(bits, solver, info)? else {
        return Ok(None);
    };
    if width != 8 {
        return Ok(None);
    }
    Ok(Some(SmtExp::Eq(Box::new(SmtExp::Extract(bit, bit, Box::new(bits))), Box::new(smt_sbits(B::new(1, 1))))))
}

fn pmp_check_rwx_exp<B: BV>(
    ent: &Val<B>,
    access: &Val<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Val::Ctor(ctor, payload) = access else {
        return Ok(None);
    };

    match shared_state.symtab.to_str(*ctor) {
        "zLoadzIEmem_payloadz5zK" | "zLoadReservedzIEmem_payloadz5zK" => {
            pmpcfg_bit_is_set(ent, 0, shared_state, solver, info)
        }
        "zStorezIEmem_payloadz5zK" | "zStoreConditionalzIEmem_payloadz5zK" => {
            pmpcfg_bit_is_set(ent, 1, shared_state, solver, info)
        }
        "zAtomiczIEmem_payloadz5zK" => {
            let Some(r) = pmpcfg_bit_is_set(ent, 0, shared_state, solver, info)? else {
                return Ok(None);
            };
            let Some(w) = pmpcfg_bit_is_set(ent, 1, shared_state, solver, info)? else {
                return Ok(None);
            };
            Ok(Some(SmtExp::And(Box::new(r), Box::new(w))))
        }
        "zInstructionFetchzIEmem_payloadz5zK" => pmpcfg_bit_is_set(ent, 2, shared_state, solver, info),
        "zCacheAccesszIEmem_payloadz5zK" => pmp_check_rwx_cache_exp(payload, ent, shared_state, solver, info),
        _ => Ok(None),
    }
}

fn pmp_check_rwx_cache_exp<B: BV>(
    cache_op: &Val<B>,
    ent: &Val<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Val::Ctor(ctor, payload) = cache_op else {
        return Ok(None);
    };

    match shared_state.symtab.to_str(*ctor) {
        "zCB_manage" => {
            let Some(r) = pmpcfg_bit_is_set(ent, 0, shared_state, solver, info)? else {
                return Ok(None);
            };
            let Some(w) = pmpcfg_bit_is_set(ent, 1, shared_state, solver, info)? else {
                return Ok(None);
            };
            Ok(Some(SmtExp::Or(Box::new(r), Box::new(w))))
        }
        "zCB_zzero" => pmpcfg_bit_is_set(ent, 1, shared_state, solver, info),
        "zCB_prefetch" => match payload.as_ref() {
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_I" => {
                pmpcfg_bit_is_set(ent, 2, shared_state, solver, info)
            }
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_R" => {
                pmpcfg_bit_is_set(ent, 0, shared_state, solver, info)
            }
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_W" => {
                pmpcfg_bit_is_set(ent, 1, shared_state, solver, info)
            }
            _ => Ok(None),
        },
        _ => Ok(None),
    }
}

fn pmp_addr_match_enum<B: BV>(
    symbol: &str,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<SmtExp<Sym>, ExecError> {
    enum_symbol_exp(symbol, shared_state, solver, info)
}

fn enum_symbol_exp<B: BV>(
    symbol: &str,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<SmtExp<Sym>, ExecError> {
    let member = lookup_required_symbol(symbol, shared_state, info)?;
    let Some((member_index, enum_size, enum_name)) = shared_state.type_info.enum_members.get(&member) else {
        return Err(ExecError::Type(format!("builtin expected enum member {}", symbol), info));
    };
    let enum_id = solver.get_enum(*enum_name, *enum_size);
    Ok(SmtExp::Enum(EnumMember { enum_id, member: *member_index }))
}

fn unsigned_bv_exp_to_i128(exp: SmtExp<Sym>, width: u32) -> Result<SmtExp<Sym>, ExecError> {
    if width > 128 {
        Err(ExecError::Type(
            format!("pmpMatchAddr cannot zero-extend {}-bit value to int", width),
            SourceLoc::unknown(),
        ))
    } else if width == 128 {
        Ok(exp)
    } else {
        Ok(SmtExp::ZeroExtend(128 - width, Box::new(exp)))
    }
}

fn pmp_range_match_exp(
    begin: SmtExp<Sym>,
    end: SmtExp<Sym>,
    addr: SmtExp<Sym>,
    width: SmtExp<Sym>,
    no_match: &SmtExp<Sym>,
    partial_match: &SmtExp<Sym>,
    full_match: &SmtExp<Sym>,
) -> SmtExp<Sym> {
    let addr_end = SmtExp::Bvadd(Box::new(addr.clone()), Box::new(width));
    let no_match_cond = SmtExp::Or(
        Box::new(SmtExp::Bvsle(Box::new(addr_end.clone()), Box::new(begin.clone()))),
        Box::new(SmtExp::Bvsle(Box::new(end.clone()), Box::new(addr.clone()))),
    );
    let full_match_cond = SmtExp::And(
        Box::new(SmtExp::Bvsle(Box::new(begin), Box::new(addr))),
        Box::new(SmtExp::Bvsle(Box::new(addr_end), Box::new(end))),
    );
    SmtExp::Ite(
        Box::new(no_match_cond),
        Box::new(no_match.clone()),
        Box::new(SmtExp::Ite(Box::new(full_match_cond), Box::new(full_match.clone()), Box::new(partial_match.clone()))),
    )
}

const PLAIN_VMEM_MISALIGNED: &str = "misaligned concrete address";

fn vmem_alignment_exception<B: BV>(
    address: Val<B>,
    exception_ctor_name: &str,
    result_err_ctor_name: &str,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let exception_ctor = lookup_required_vmem_symbol(exception_ctor_name, shared_state, info)?;
    let memory_exception_ctor = lookup_required_vmem_symbol("zMemory_Exception", shared_state, info)?;
    let result_err_ctor = lookup_required_vmem_symbol(result_err_ctor_name, shared_state, info)?;
    let address_len = match &address {
        Val::Bits(address) => address.len(),
        _ => {
            return Err(ExecError::Type(
                format!("vmem alignment exception requires concrete address, got {:?}", address),
                info,
            ))
        }
    };
    let address_field = lookup_required_vmem_symbol(
        &format!("ztuplez3z5bv{}_z5unionz0zzExceptionType0", address_len),
        shared_state,
        info,
    )?;
    let exception_field = lookup_required_vmem_symbol(
        &format!("ztuplez3z5bv{}_z5unionz0zzExceptionType1", address_len),
        shared_state,
        info,
    )?;

    let exception = Val::Ctor(exception_ctor, Box::new(Val::Unit));
    let mut memory_exception_fields = HashMap::default();
    memory_exception_fields.insert(address_field, address);
    memory_exception_fields.insert(exception_field, exception);
    let memory_exception = Val::Ctor(memory_exception_ctor, Box::new(Val::Struct(memory_exception_fields)));

    Ok(Val::Ctor(result_err_ctor, Box::new(memory_exception)))
}

fn lookup_required_vmem_symbol<B: BV>(
    symbol: &str,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Name, ExecError> {
    lookup_required_symbol(symbol, shared_state, info)
}

fn lookup_required_symbol<B: BV>(
    symbol: &str,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Name, ExecError> {
    shared_state
        .symtab
        .get(symbol)
        .ok_or_else(|| ExecError::Type(format!("builtin expected IR symbol {}", symbol), info))
}

fn validate_plain_vmem_write<B: BV>(
    args: &[Val<B>],
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<&'static str>, ExecError> {
    if let Some(reason) = validate_plain_vmem_common(
        &args[0],
        &args[1],
        &args[3],
        &args[4],
        &args[5],
        &args[6],
        "zStorezIEmem_payloadz5zK",
        shared_state,
        solver,
        info,
    )? {
        return Ok(Some(reason));
    }

    let width = match concrete_width_bytes(&args[1]) {
        Some(width) => width,
        None => return Ok(Some("non-concrete write width")),
    };
    let data_bits = crate::primop_util::length_bits(&args[2], solver, info)?;
    if data_bits != width * 8 {
        return Ok(Some("write data length does not match width"));
    }

    Ok(None)
}

fn validate_plain_vmem_read<B: BV>(
    args: &[Val<B>],
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<&'static str>, ExecError> {
    validate_plain_vmem_common(
        &args[0],
        &args[2],
        &args[3],
        &args[4],
        &args[5],
        &args[6],
        "zLoadzIEmem_payloadz5zK",
        shared_state,
        solver,
        info,
    )
}

fn validate_plain_vmem_common<B: BV>(
    address: &Val<B>,
    width: &Val<B>,
    access: &Val<B>,
    aq: &Val<B>,
    rl: &Val<B>,
    res: &Val<B>,
    expected_access_ctor: &str,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<&'static str>, ExecError> {
    if *aq != Val::Bool(false) {
        return Ok(Some("aq is not false"));
    }
    if *rl != Val::Bool(false) {
        return Ok(Some("rl is not false"));
    }
    if *res != Val::Bool(false) {
        return Ok(Some("reservation access is not supported"));
    }
    if !is_data_access_ctor(access, expected_access_ctor, shared_state) {
        return Ok(Some("access is not ordinary Data load/store"));
    }
    if !env_flag("ISLA_RISCV_VMEM_ASSUME_IDENTITY_TRANSLATION") {
        return Ok(Some("identity translation is not explicitly assumed"));
    }
    if !env_flag("ISLA_RISCV_VMEM_ASSUME_PMP_PERMITS") {
        return Ok(Some("PMP permission is not explicitly assumed"));
    }
    if !env_flag("ISLA_RISCV_VMEM_ASSUME_PLAIN_RAM") {
        return Ok(Some("plain RAM region is not explicitly assumed"));
    }

    let width = match concrete_width_bytes(width) {
        Some(width) => width,
        None => return Ok(Some("non-concrete access width")),
    };
    if width == 0 {
        return Err(ExecError::Type("vmem builtin received zero-width access".to_string(), SourceLoc::unknown()));
    }

    match is_concretely_aligned(address, width) {
        Some(true) => Ok(None),
        Some(false) => Ok(Some(PLAIN_VMEM_MISALIGNED)),
        None if env_flag("ISLA_RISCV_VMEM_ASSUME_ALIGNED") => {
            assert_plain_vmem_alignment(address, width, solver, info)?;
            Ok(None)
        }
        None => Ok(Some("alignment is not proven")),
    }
}

fn assert_plain_vmem_alignment<B: BV>(
    address: &Val<B>,
    width: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<(), ExecError> {
    if let Some(assertion) = plain_vmem_alignment_assert_exp(address, width, info)? {
        solver.add(Def::Assert(assertion));
    }
    Ok(())
}

fn plain_vmem_alignment_assert_exp<B: BV>(
    address: &Val<B>,
    width: u32,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    if width == 1 {
        return Ok(None);
    }
    if !width.is_power_of_two() {
        return Err(ExecError::Type(
            format!("vmem builtin cannot assert non-power-of-two alignment width {}", width),
            info,
        ));
    }

    let align_bits = width.trailing_zeros();
    let low_bits = SmtExp::Extract(align_bits - 1, 0, Box::new(smt_value(address, info)?));
    let zero = SmtExp::Bits64(B64::zeros(align_bits));
    Ok(Some(SmtExp::Eq(Box::new(low_bits), Box::new(zero))))
}

fn concrete_width_bytes<B: BV>(width: &Val<B>) -> Option<u32> {
    match width.clone().widen_int() {
        Val::I128(width) => u32::try_from(width).ok(),
        _ => None,
    }
}

fn is_concretely_aligned<B: BV>(address: &Val<B>, width: u32) -> Option<bool> {
    match address {
        Val::Bits(addr) => Some(addr.lower_u64() % u64::from(width) == 0),
        _ => None,
    }
}

fn is_data_access_ctor<B: BV>(access: &Val<B>, expected_ctor: &str, shared_state: &SharedState<B>) -> bool {
    match access {
        Val::Ctor(ctor, payload) if shared_state.symtab.to_str(*ctor) == expected_ctor => match payload.as_ref() {
            Val::Enum(member) => {
                let enum_name = shared_state.symtab.to_str(member.enum_id.to_name());
                enum_name == "zmem_payload" && member.member == 0
            }
            _ => false,
        },
        _ => false,
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
    timeout: Timeout,
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

fn is_zero_test_exp(exp: &Exp<Name>) -> bool {
    match exp {
        Exp::Bits(bits) => bits.lower_u64() == 0,
        Exp::I64(n) => *n == 0,
        Exp::I128(n) => *n == 0,
        _ => false,
    }
}

fn x0_branch_side(exp: &Exp<Name>) -> Option<bool> {
    match exp {
        Exp::Call(Op::Eq, exps) if exps.len() == 2 => {
            if is_zero_test_exp(&exps[0]) || is_zero_test_exp(&exps[1]) {
                Some(true)
            } else {
                None
            }
        }
        Exp::Call(Op::Neq, exps) if exps.len() == 2 => {
            if is_zero_test_exp(&exps[0]) || is_zero_test_exp(&exps[1]) {
                Some(false)
            } else {
                None
            }
        }
        Exp::Call(Op::Not, exps) if exps.len() == 1 => x0_branch_side(&exps[0]).map(|is_true_branch| !is_true_branch),
        _ => None,
    }
}

fn in_x_function_stack<'ir, B: BV>(frame: &LocalFrame<'ir, B>, shared_state: &SharedState<'ir, B>) -> bool {
    let workaround_list = ["X", "rX", "wX"];
    let is_x = |name: Name| zencode::decode(shared_state.symtab.to_str(name)) == "X";
    is_x(frame.function_name) || frame.backtrace.iter().any(|(name, _)| is_x(*name))
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
    timeout: Timeout,
    stop_conditions: Option<&'task StopConditions>,
    fork_sink: &S,
    frame: &mut LocalFrame<'ir, B>,
    task_state: &'task TaskState<B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<Run<B>, ExecError> {
    let mut last_z3_reset = Instant::now();

    'main_loop: loop {
        if frame.pc >= frame.instrs.len() {
            // Currently this happens when evaluating letbindings.
            return Ok(Run::Finished(Val::Unit));
        }

        if timeout.timed_out() {
            return Err(ExecError::Timeout);
        }

        if last_z3_reset.elapsed() > Duration::from_millis(500) {
            //let mut vars = HashSet::default();
            //frame.collect_symbolic_variables(&mut vars);
            //solver.reset(vars);
            last_z3_reset = Instant::now()
        };

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
                            /* if in_x_function_stack(frame, shared_state) {
                                //先检查条件表达式是不是显式的 == 0 / != 0 / not(...) 这类形式
                                if let Some(x0_is_true_branch) = x0_branch_side(exp) {
                                    /*
                                    如果命中：
                                        x == 0 这种，直接丢掉 true 分支，只保留 false
                                        x != 0 这种，直接丢掉 false 分支，只保留 true
                                     */
                                    if x0_is_true_branch {
                                        solver.add(Assert(test_false.clone()));
                                        frame.branch_conditions.push(test_false);
                                        frame.pc += 1;
                                    } else {
                                        solver.add(Assert(test_true.clone()));
                                        frame.branch_conditions.push(test_true);
                                        frame.pc = *target;
                                    }
                                    continue 'main_loop;
                                }
                            } */

                            if_logging!(log::FORK, {
                                log_from!(tid, log::FORK, info.location_string(shared_state.symtab.files()));
                                probe::taint_info(log::FORK, v, Some(shared_state), solver)
                            });

                            let point = checkpoint(solver);

                            // 为 fork 路径创建条件列表
                            let mut fork_conditions = frame.branch_conditions.clone();
                            fork_conditions.push(test_false.clone());

                            let frozen =
                                Frame { pc: frame.pc + 1, branch_conditions: fork_conditions, ..freeze_frame(frame) };
                            frame.forks += 1;
                            task_fraction.halve();
                            fork_sink.submit(Task {
                                id: task_id,
                                fraction: task_fraction.clone(),
                                frame: frozen,
                                checkpoint: point,
                                fork_cond: Some((Assert(test_false), Event::Fork(frame.forks - 1, v, 1, *info))),
                                state: task_state,
                                stop_conditions,
                            });

                            // Track which asserts are assocated with each fork in the trace, so we
                            // can turn a set of traces into a tree later
                            solver.add_event(Event::Fork(frame.forks - 1, v, 0, *info));

                            solver.add(Assert(test_true.clone()));

                            // 当前路径的条件
                            frame.branch_conditions.push(test_true);

                            frame.pc = *target
                        } else if can_be_true {
                            solver.add(Assert(test_true));
                            frame.pc = *target
                        } else if can_be_false {
                            solver.add(Assert(test_false));
                            frame.pc += 1
                        } else {
                            return Ok(Run::Dead);
                        }
                    }
                    Val::Bool(jump) => {
                        if jump {
                            frame.pc = *target
                        } else {
                            frame.pc += 1
                        }
                    }
                    _ => {
                        return Err(ExecError::Type(format!("Jump on non boolean {:?}", &value), *info));
                    }
                }
            }

            Instr::Goto(target) => frame.pc = *target,

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

            Instr::Call(loc, _, f, args, info) => {
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

                        if let Some(result) =
                            call_isla_implemented_function(*f, &args, frame, shared_state, solver, *info)?
                        {
                            assign(tid, loc, result, &mut frame.local_state, shared_state, solver, *info)?;
                            frame.pc += 1;
                            continue 'main_loop;
                        }

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
                                if args.len() == required_args.len()
                                    && required_args.iter().zip(args.iter()).all(|(req, arg)| {
                                        primop::eq_anything(req.clone(), arg.clone(), solver, *info)
                                            .map(|v| match v {
                                                Val::Symbolic(var) => {
                                                    solver.check_sat_with(
                                                        &smtlib::Exp::Eq(
                                                            Box::new(smtlib::Exp::Var(var)),
                                                            Box::new(smtlib::Exp::Bool(false)),
                                                        ),
                                                        *info,
                                                    ) == SmtResult::Unsat
                                                }
                                                Val::Bool(b) => b,
                                                _ => panic!("TODO"),
                                            })
                                            .unwrap()
                                    })
                                {
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

                    log_from!(tid, log::FORK, format!("Fork @ monomorphizing v{} : {:?}", v, ty));

                    frame.forks += 1;

                    // Because we will likely case-split more times in the task we add to the queue,
                    // give it a larger part of the fraction (otherwise the denominator becomes
                    // small very fast).
                    let child_frac = task_fraction.min_split(6);
                    fork_sink.submit(Task {
                        id: task_id,
                        fraction: child_frac,
                        frame: freeze_frame(frame),
                        checkpoint: point,
                        fork_cond: Some((
                            Assert(Neq(Box::new(Var(v)), Box::new(result_exp.clone()))),
                            Event::Fork(frame.forks - 1, v, 1, *info),
                        )),
                        state: task_state,
                        stop_conditions,
                    });

                    solver.add_event(Event::Fork(frame.forks - 1, v, 0, *info));

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
    + Fn(usize, TaskId, Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>, &SharedState<'ir, B>, Solver<B>, &R);

/// Start symbolically executing a Task using just the current thread, collecting the results using
/// the given collector.
pub fn start_single<'ir, B: BV, R>(
    task: Task<'ir, '_, B>,
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
            Timeout::unlimited(),
            task.stop_conditions,
            &fork_sink,
            &task.frame,
            task.state,
            shared_state,
            &mut solver,
        );
        collector(0, task.id, result, shared_state, solver, collected)
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
    timeout: Timeout,
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
pub fn start_multi<'ir, 'task, B: BV, R>(
    num_threads: usize,
    timeout: Option<u64>,
    tasks: Vec<Task<'ir, 'task, B>>,
    shared_state: &'ir SharedState<'ir, B>,
    collected: Arc<R>,
    collector: &'ir Collector<'ir, B, R>,
) where
    B: Send + Sync,
    R: Send + Sync,
{
    if num_threads == 0 {
        for task in tasks {
            start_single(task, shared_state, collected.as_ref(), collector);
        }
        return;
    }

    let timeout = Timeout { start_time: Instant::now(), duration: timeout.map(Duration::from_secs) };

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
    let timeout = Timeout { start_time: Instant::now(), duration: timeout.map(Duration::from_secs) };

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
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>,
    shared_state: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    collected: &AtomicBool,
) {
    match result {
        Ok((Run::Finished(value), _)) => match value {
            Val::Symbolic(v) => {
                use smtlib::Def::*;
                use smtlib::Exp::*;
                solver.add(Assert(Not(Box::new(Var(v)))));
                if solver.check_sat(SourceLoc::unknown()) != SmtResult::Unsat {
                    log_from!(tid, log::VERBOSE, "Got sat");
                    collected.store(false, Ordering::Release)
                } else {
                    log_from!(tid, log::VERBOSE, "Got unsat")
                }
            }
            Val::Bool(true) => log_from!(tid, log::VERBOSE, "Got true"),
            Val::Bool(false) => {
                log_from!(tid, log::VERBOSE, "Got false");
                collected.store(false, Ordering::Release)
            }
            _ => log_from!(tid, log::VERBOSE, &format!("Got value {:?}", value)),
        },
        Ok((Run::Dead, _)) => (),
        Ok((Run::Exit | Run::Suspended, _)) => log_from!(tid, log::VERBOSE, "Unexpected return".to_string()),
        Err((err, backtrace)) => {
            if_logging!(log::VERBOSE, {
                log_from!(tid, log::VERBOSE, &format!("Got error, {:?}", err));
                for (f, pc) in backtrace.iter().rev() {
                    log_from!(tid, log::VERBOSE, format!("  {} @ {}", shared_state.symtab.to_str(*f), pc));
                }
            });
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
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>,
    shared_state: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    collected: &TraceQueue<B>,
) {
    solver.report_performance(shared_state.symtab.get_directory(), shared_state.symtab.files());

    match result {
        Ok((Run::Finished(_) | Run::Exit, _)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, events.drain(..).cloned().collect())))
        }
        Ok((Run::Suspended, _)) => collected.push(Err(TraceError::UnexpectedSuspension)),
        Ok((Run::Dead, _)) => (),
        Err((err, backtrace)) => {
            log_from!(tid, log::VERBOSE, format!("Error {:?}", err));
            for (f, pc) in backtrace.iter().rev() {
                log_from!(tid, log::VERBOSE, format!("  {} @ {}", shared_state.symtab.to_str(*f), pc));
            }
            if solver.check_sat(SourceLoc::unknown()) == SmtResult::Sat {
                let model = Model::new(&solver);
                collected.push(Err(TraceError::exec_model(
                    err,
                    backtrace_string(&backtrace, &shared_state.symtab),
                    model,
                )))
            } else {
                collected.push(Err(TraceError::exec(err, backtrace_string(&backtrace, &shared_state.symtab))))
            }
        }
    }
}

pub fn trace_value_collector<'ir, B: BV>(
    _: usize,
    task_id: TaskId,
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>,
    shared_state: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    collected: &TraceValueQueue<B>,
) {
    match result {
        Ok((Run::Finished(value), _)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, value, events.drain(..).cloned().collect())))
        }
        Ok((Run::Exit | Run::Suspended, _)) => (),
        Ok((Run::Dead, _)) => (),
        Err((err, backtrace)) => {
            if solver.check_sat(SourceLoc::unknown()) == SmtResult::Sat {
                let model = Model::new(&solver);
                collected.push(Err(TraceError::exec_model(
                    err,
                    backtrace_string(&backtrace, &shared_state.symtab),
                    model,
                )))
            } else {
                collected.push(Err(TraceError::exec(err, backtrace_string(&backtrace, &shared_state.symtab))))
            }
        }
    }
}

pub fn trace_result_collector<'ir, B: BV>(
    _: usize,
    task_id: TaskId,
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>,
    shared_state: &SharedState<'ir, B>,
    solver: Solver<B>,
    collected: &TraceResultQueue<B>,
) {
    match result {
        Ok((Run::Finished(Val::Bool(result)), _)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, result, events.drain(..).cloned().collect())))
        }
        Ok((Run::Exit, _)) => (),
        Ok((Run::Suspended, _)) => collected.push(Err(TraceError::UnexpectedSuspension)),
        Ok((Run::Finished(val), _)) => collected.push(Err(TraceError::unexpected_value(val))),
        Ok((Run::Dead, _)) => (),
        Err((err, backtrace)) => {
            collected.push(Err(TraceError::exec(err, backtrace_string(&backtrace, &shared_state.symtab))))
        }
    }
}

pub fn footprint_collector<'ir, B: BV>(
    _: usize,
    task_id: TaskId,
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>,
    shared_state: &SharedState<'ir, B>,
    solver: Solver<B>,
    collected: &TraceQueue<B>,
) {
    match result {
        // Footprint function returns true on traces we need to consider as part of the footprint
        Ok((Run::Finished(Val::Bool(true)), _)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, events.drain(..).cloned().collect())))
        }
        // If it is dead, returns false or exits, we ignore that trace
        Ok((Run::Finished(Val::Bool(false)) | Run::Exit | Run::Dead, _)) => (),
        // Any other value is an error!
        Ok((Run::Finished(value), _)) => collected.push(Err(TraceError::unexpected_value(value))),

        Ok((Run::Suspended, _)) => collected.push(Err(TraceError::UnexpectedSuspension)),

        Err((err, backtrace)) => {
            collected.push(Err(TraceError::exec(err, backtrace_string(&backtrace, &shared_state.symtab))))
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
) {
    // 获取函数信息
    let function_id = shared_state.symtab.lookup(function_name);
    let (func_args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();

    // 创建初始帧
    let mut initial_frame = LocalFrame::new(function_id, func_args, ret_ty, Some(args), instrs);
    initial_frame.add_regs(regs);
    initial_frame.add_lets(lets);

    // 创建任务，使用传入的checkpoint
    let task_state = TaskState::new();
    let task_id = TaskId::fresh();
    let task = initial_frame.task_with_checkpoint(task_id, &task_state, checkpoint);

    start_single(task, &shared_state, collected, collector);
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

    // 创建任务，使用传入的checkpoint
    let task_state = TaskState::new();
    let task_id = TaskId::fresh();
    let task = initial_frame.task_with_checkpoint(task_id, &task_state, checkpoint);

    start_multi(110, None, vec![task], shared_state, collected.clone(), collector);
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

    start_multi(110, None, vec![task], shared_state, collected.clone(), collector);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bv64(value: u64, width: u32) -> SmtExp<Sym> {
        smt_sbits(B64::new(value, width))
    }

    fn i128_bv(value: i128) -> SmtExp<Sym> {
        smt_i128(value)
    }

    fn eval_bool(exp: SmtExp<Sym>) -> bool {
        match exp {
            SmtExp::Bool(value) => value,
            SmtExp::And(lhs, rhs) => eval_bool(*lhs) && eval_bool(*rhs),
            SmtExp::Or(lhs, rhs) => eval_bool(*lhs) || eval_bool(*rhs),
            SmtExp::Not(exp) => !eval_bool(*exp),
            SmtExp::Bvule(lhs, rhs) => {
                let (lhs, lhs_width) = eval_bv(*lhs);
                let (rhs, rhs_width) = eval_bv(*rhs);
                assert_eq!(lhs_width, rhs_width);
                lhs <= rhs
            }
            _ => panic!("unsupported bool expression in test: {:?}", exp),
        }
    }

    fn eval_bv(exp: SmtExp<Sym>) -> (u128, u32) {
        match exp {
            SmtExp::Bits64(bits) => (u128::from(bits.lower_u64()), bits.len()),
            SmtExp::Bits(bits) => {
                let mut value = 0_u128;
                for (index, bit) in bits.iter().enumerate() {
                    if *bit {
                        value |= 1_u128 << index;
                    }
                }
                (value, bits.len() as u32)
            }
            SmtExp::Bvadd(lhs, rhs) => {
                let (lhs, width) = eval_bv(*lhs);
                let (rhs, rhs_width) = eval_bv(*rhs);
                assert_eq!(width, rhs_width);
                ((lhs + rhs) & mask(width), width)
            }
            SmtExp::Bvsub(lhs, rhs) => {
                let (lhs, width) = eval_bv(*lhs);
                let (rhs, rhs_width) = eval_bv(*rhs);
                assert_eq!(width, rhs_width);
                (lhs.wrapping_sub(rhs) & mask(width), width)
            }
            _ => panic!("unsupported bitvector expression in test: {:?}", exp),
        }
    }

    fn mask(width: u32) -> u128 {
        if width == 128 {
            u128::MAX
        } else {
            (1_u128 << width) - 1
        }
    }

    #[test]
    fn range_subset_exp_matches_sail_wraparound_cases() {
        assert!(eval_bool(range_subset_exp(bv64(0xffff_fffc, 32), bv64(4, 32), bv64(0xffff_fff0, 32), bv64(0x20, 32))));
        assert!(!eval_bool(range_subset_exp(
            bv64(0xffff_fffc, 32),
            bv64(0x24, 32),
            bv64(0xffff_fff0, 32),
            bv64(0x20, 32)
        )));
        assert!(!eval_bool(range_subset_exp(bv64(0x10, 32), bv64(4, 32), bv64(0xffff_fff0, 32), bv64(0x20, 32))));
    }

    #[test]
    fn unbounded_range_contains_exp_does_not_wrap() {
        assert!(eval_bool(unbounded_range_contains_exp(i128_bv(0xffff_fffc), i128_bv(0xffff_fff0), i128_bv(0x20), 4)));
        assert!(!eval_bool(unbounded_range_contains_exp(
            i128_bv(i128::from(u64::MAX) - 1),
            i128_bv(i128::from(u64::MAX) - 8),
            i128_bv(8),
            4,
        )));
    }

    #[test]
    fn clint_off_predicates_return_false_only_when_safe() {
        assert!(matches!(clint_disabled_predicate_result::<B64>(), Some(Val::Bool(false))));
        assert!(clint_off_requires_within_mmio_builtin(true, false));
        assert!(!clint_off_requires_within_mmio_builtin(true, true));
        assert!(!clint_off_requires_within_mmio_builtin(false, false));
        assert!(matches!(
            clint_disabled_within_mmio_result(true, Val::<B64>::Bool(true), SourceLoc::unknown()),
            Ok(Some(Val::Bool(true)))
        ));
        assert!(matches!(
            clint_disabled_within_mmio_result(true, Val::<B64>::Bool(false), SourceLoc::unknown()),
            Ok(Some(Val::Bool(false)))
        ));
        assert!(clint_disabled_within_mmio_result(false, Val::<B64>::Bool(true), SourceLoc::unknown()).is_err());
    }

    #[test]
    fn pmp_off_assumption_does_not_require_concrete_privilege() {
        assert!(pmp_off_assumption_ignores_privilege(&Val::<B64>::Symbolic(Sym::from_u32(1))));
        let computation = pmp_check_off_computation::<B64>();
        assert!(matches!(computation.parts.is_some, SmtExp::Bool(false)));
        assert!(computation.parts.fault.is_none());
        assert!(computation.effects.is_empty());
    }

    #[test]
    fn phys_access_priority_prefers_access_and_right_tie() {
        assert_eq!(alignment_or_access_fault_priority_name("zE_Load_Addr_Align"), Some(0));
        assert_eq!(alignment_or_access_fault_priority_name("zE_Load_Access_Fault"), Some(1));
        assert_eq!(
            highest_priority_alignment_or_access_fault_name("zE_Load_Access_Fault", "zE_Load_Addr_Align"),
            Some("zE_Load_Access_Fault"),
        );
        assert_eq!(
            highest_priority_alignment_or_access_fault_name("zE_Load_Access_Fault", "zE_Load_Access_Fault"),
            Some("zE_Load_Access_Fault"),
        );
        assert_eq!(
            highest_priority_alignment_or_access_fault_name("zE_Load_Access_Fault", "zE_SAMO_Access_Fault"),
            Some("zE_SAMO_Access_Fault"),
        );
    }

    #[test]
    fn symbolic_phys_access_exception_requests_fallback() {
        let fault: Val<B64> = Val::SymbolicCtor(Sym::from_u32(1), HashMap::default());
        let result = concrete_exception_ctor_payload_or_fallback(&fault, "test", SourceLoc::unknown()).unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn symbolic_phys_access_fault_choice_requests_fallback() {
        let pmp = OptionExceptionParts {
            is_some: SmtExp::Var(Sym::from_u32(1)),
            fault: Some(Val::Ctor(Name::from_u32(100), Box::new(Val::<B64>::Unit))),
        };
        let pma = OptionExceptionParts {
            is_some: SmtExp::Var(Sym::from_u32(2)),
            fault: Some(Val::Ctor(Name::from_u32(101), Box::new(Val::<B64>::Unit))),
        };
        assert!(phys_access_fault_selection_requires_fallback(&pmp, &pma));
    }

    #[test]
    fn clint_load_exact_hit_table_matches_sail_branches() {
        assert_eq!(clint_load_exact_hit(0x0000, 4), Some(ClintLoadHit::Msip));
        assert_eq!(clint_load_exact_hit(0x0000, 8), Some(ClintLoadHit::Msip));
        assert_eq!(clint_load_exact_hit(0x4000, 4), Some(ClintLoadHit::MtimecmpLow));
        assert_eq!(clint_load_exact_hit(0x4000, 8), Some(ClintLoadHit::MtimecmpFull));
        assert_eq!(clint_load_exact_hit(0x4004, 4), Some(ClintLoadHit::MtimecmpHigh));
        assert_eq!(clint_load_exact_hit(0xbff8, 4), Some(ClintLoadHit::MtimeLow));
        assert_eq!(clint_load_exact_hit(0xbff8, 8), Some(ClintLoadHit::MtimeFull));
        assert_eq!(clint_load_exact_hit(0xbffc, 4), Some(ClintLoadHit::MtimeHigh));
        assert_eq!(clint_load_exact_hit(0x4004, 8), None);
        assert_eq!(clint_load_exact_hit(0x0004, 4), None);
    }
}
