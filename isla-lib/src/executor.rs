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
use crate::timeout::PathTimeoutDiagnostic;
use crate::zencode;

mod execution_limits;
mod frame;
mod path_timing;
mod symbolic_length;
mod task;

use crate::register::RegisterBindings;
#[cfg(test)]
use execution_limits::ExecutionLimitPathState;
use execution_limits::{BranchSample, ExecutionLimitDecision, ExecutionLimitHandler, ExecutionLimitReason};
pub use execution_limits::{ExecutionLimits, LimitBehavior, SampleBias};
pub use frame::{backtrace_string, freeze_frame, unfreeze_frame, Backtrace, Frame, LocalFrame, LocalState};
use frame::{pop_call_stack, push_call_stack};
use path_timing::PathTimeout;
pub use task::{StopAction, StopConditions, Task, TaskId, TaskInterrupt, TaskState, WriteSet};

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
                if !for_write {
                    if let Some(reads) = local_state.register_reads.as_mut() {
                        reads.push((id, accessor.to_vec(), value.clone()));
                    }
                }
                let symbol = zencode::decode(shared_state.symtab.to_str(id));
                // HACK: Don't store the entire TLB in the trace
                if !for_write && !symbol.contains("_TLB") {
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
        Val::Bits(bv) => {
            if bv.len() > 64 && !bv.slice(64, bv.len() - 64).unwrap().is_zero() {
                return Err(ExecError::Type(invalid_index_argument.to_string(), info));
            }
            let idx = bv.lower_u64() as usize;
            if idx >= regs.len() {
                return Err(ExecError::Type(invalid_index_argument.to_string(), info));
            }
            ConcreteIndex(idx)
        }
        Val::I64(n) => {
            let idx: usize = n.try_into().map_err(|_| ExecError::Type(invalid_index_argument.to_string(), info))?;
            if idx >= regs.len() {
                return Err(ExecError::Type(invalid_index_argument.to_string(), info));
            }
            ConcreteIndex(idx)
        }
        Val::I128(n) => {
            let idx: usize = n.try_into().map_err(|_| ExecError::Type(invalid_index_argument.to_string(), info))?;
            if idx >= regs.len() {
                return Err(ExecError::Type(invalid_index_argument.to_string(), info));
            }
            ConcreteIndex(idx)
        }
        Val::Symbolic(v) => {
            if let Some(len) = solver.length(v) {
                if regs.len() == 1 {
                    let zero = Eq(Box::new(Var(v)), Box::new(primop::smt_zeros(i128::from(len))));
                    let nonzero = Neq(Box::new(Var(v)), Box::new(primop::smt_zeros(i128::from(len))));
                    let zero_sat = !solver.check_sat_with(&zero, info).is_unsat()?;
                    let nonzero_sat = !solver.check_sat_with(&nonzero, info).is_unsat()?;
                    if zero_sat && nonzero_sat {
                        return Err(ExecError::SymbolicLength("read_register_from_vector", info));
                    }
                    if !zero_sat {
                        return Err(ExecError::Type(invalid_index_argument.to_string(), info));
                    }
                    ConcreteIndex(0)
                } else {
                    // 必须先按原始位宽检查边界，防止截断高位后访问错误寄存器。
                    if !(len < 128 && (1u128 << len) <= regs.len() as u128) {
                        let limit = smtlib::bits64(regs.len() as u64, len);
                        let in_bounds = Bvult(Box::new(Var(v)), Box::new(limit.clone()));
                        let out_of_bounds = Bvuge(Box::new(Var(v)), Box::new(limit));
                        let in_bounds_sat = !solver.check_sat_with(&in_bounds, info).is_unsat()?;
                        let out_of_bounds_sat = !solver.check_sat_with(&out_of_bounds, info).is_unsat()?;
                        if in_bounds_sat && out_of_bounds_sat {
                            return Err(ExecError::SymbolicLength("read_register_from_vector", info));
                        }
                        if !in_bounds_sat {
                            return Err(ExecError::Type(invalid_index_argument.to_string(), info));
                        }
                    }
                    let v = fix_index_length(v, len, rib, solver, info);
                    SymbolicIndex(v)
                }
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
                chain = match solver
                    .with_def_attrs(DefAttrs::uninteresting(), |solver| build_ite(choice, value, &chain, solver, info))
                {
                    Ok(value) => value,
                    Err(ExecError::NoSymbolicType | ExecError::IncompatibleMerge) => {
                        // 沿用向量访问的索引拆分；唯一候选必须执行具体寄存器读取并记录 ReadReg。
                        let index = fix_index_length(i, rib, 128, solver, info);
                        return match primop::proven_symbolic_i128(index, solver, info)? {
                            Some(index) => read_register_from_vector(
                                Val::I128(index),
                                regs_vector,
                                local_state,
                                shared_state,
                                solver,
                                info,
                            ),
                            None => Err(ExecError::SymbolicLength("read_register_from_vector", info)),
                        };
                    }
                    Err(error) => return Err(error),
                }
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
        Val::Bits(bv) => {
            if bv.len() > 64 && !bv.slice(64, bv.len() - 64).unwrap().is_zero() {
                return Err(ExecError::Type(invalid_index_argument.to_string(), info));
            }
            let idx = bv.lower_u64() as usize;
            if idx >= regs.len() {
                return Err(ExecError::Type(invalid_index_argument.to_string(), info));
            }
            ConcreteIndex(idx)
        }
        Val::I64(n) => {
            let idx: usize = n.try_into().map_err(|_| ExecError::Type(invalid_index_argument.to_string(), info))?;
            if idx >= regs.len() {
                return Err(ExecError::Type(invalid_index_argument.to_string(), info));
            }
            ConcreteIndex(idx)
        }
        Val::I128(n) => {
            let idx: usize = n.try_into().map_err(|_| ExecError::Type(invalid_index_argument.to_string(), info))?;
            if idx >= regs.len() {
                return Err(ExecError::Type(invalid_index_argument.to_string(), info));
            }
            ConcreteIndex(idx)
        }
        Val::Symbolic(v) => {
            if let Some(len) = solver.length(v) {
                if regs.len() == 1 {
                    let zero = Eq(Box::new(Var(v)), Box::new(primop::smt_zeros(i128::from(len))));
                    let nonzero = Neq(Box::new(Var(v)), Box::new(primop::smt_zeros(i128::from(len))));
                    let zero_sat = !solver.check_sat_with(&zero, info).is_unsat()?;
                    let nonzero_sat = !solver.check_sat_with(&nonzero, info).is_unsat()?;
                    if zero_sat && nonzero_sat {
                        return Err(ExecError::SymbolicLength("write_register_from_vector", info));
                    }
                    if !zero_sat {
                        return Err(ExecError::Type(invalid_index_argument.to_string(), info));
                    }
                    ConcreteIndex(0)
                } else {
                    // 必须先按原始位宽检查边界，防止截断高位后访问错误寄存器。
                    if !(len < 128 && (1u128 << len) <= regs.len() as u128) {
                        let limit = smtlib::bits64(regs.len() as u64, len);
                        let in_bounds = Bvult(Box::new(Var(v)), Box::new(limit.clone()));
                        let out_of_bounds = Bvuge(Box::new(Var(v)), Box::new(limit));
                        let in_bounds_sat = !solver.check_sat_with(&in_bounds, info).is_unsat()?;
                        let out_of_bounds_sat = !solver.check_sat_with(&out_of_bounds, info).is_unsat()?;
                        if in_bounds_sat && out_of_bounds_sat {
                            return Err(ExecError::SymbolicLength("write_register_from_vector", info));
                        }
                        if !in_bounds_sat {
                            return Err(ExecError::Type(invalid_index_argument.to_string(), info));
                        }
                    }
                    let v = fix_index_length(v, len, rib, solver, info);
                    SymbolicIndex(v)
                }
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
            if regs.iter().any(|reg| local_state.regs.is_relaxed(*reg) || local_state.regs.has_old_writes(*reg)) {
                // 直接拆分索引，避免读取 relaxed 历史值后将其写成未选中寄存器的最新值。
                let index = fix_index_length(i, rib, 128, solver, info);
                return match primop::proven_symbolic_i128(index, solver, info)? {
                    Some(index) => write_register_from_vector(
                        Val::I128(index),
                        value,
                        regs_vector,
                        local_state,
                        shared_state,
                        solver,
                        info,
                    ),
                    None => Err(ExecError::SymbolicLength("write_register_from_vector", info)),
                };
            }
            let mut reg_values = Vec::new();
            let mut updates: HashMap<Name, Val<B>> = HashMap::new();
            for (j, reg) in regs.iter().enumerate() {
                let choice = solver.with_def_attrs(DefAttrs::uninteresting(), |solver| {
                    solver.define_const(Eq(Box::new(Var(i)), Box::new(Bits64(B64::new(j as u64, rib)))), info)
                });
                let current_value = match updates.get(reg) {
                    Some(value) => value.clone(),
                    None => local_state.regs.get(*reg, shared_state, solver, info)?.unwrap().clone(),
                };
                let updated = match solver.with_def_attrs(DefAttrs::uninteresting(), |solver| {
                    build_ite(choice, &value, &current_value, solver, info)
                }) {
                    Ok(updated) => updated,
                    Err(ExecError::NoSymbolicType | ExecError::IncompatibleMerge) => {
                        // 所有候选准备成功后才写回，防止重试继承部分更新的寄存器。
                        let index = fix_index_length(i, rib, 128, solver, info);
                        return match primop::proven_symbolic_i128(index, solver, info)? {
                            Some(index) => write_register_from_vector(
                                Val::I128(index),
                                value,
                                regs_vector,
                                local_state,
                                shared_state,
                                solver,
                                info,
                            ),
                            None => Err(ExecError::SymbolicLength("write_register_from_vector", info)),
                        };
                    }
                    Err(error) => return Err(error),
                };
                updates.insert(*reg, updated);
                reg_values.push(current_value);
            }
            for (reg, updated) in updates {
                local_state.regs.assign(reg, updated, shared_state);
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

    if let Some(value) = local_state.expression_values.get(&(exp as *const Exp<Name> as usize)) {
        return Ok(Owned(value.clone()));
    }

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
                args.push(eval_exp(arg, local_state, shared_state, solver, info)?.into_owned());
            }
            let result = match op {
                Op::Lt => primop::op_lt(args[0].clone(), args[1].clone(), solver, info),
                Op::Gt => primop::op_gt(args[0].clone(), args[1].clone(), solver, info),
                Op::Lteq => primop::op_lteq(args[0].clone(), args[1].clone(), solver, info),
                Op::Gteq => primop::op_gteq(args[0].clone(), args[1].clone(), solver, info),
                Op::Eq => primop::op_eq(args[0].clone(), args[1].clone(), solver, info),
                Op::Neq => primop::op_neq(args[0].clone(), args[1].clone(), solver, info),
                Op::Add => primop::op_add(args[0].clone(), args[1].clone(), solver, info),
                Op::Sub => primop::op_sub(args[0].clone(), args[1].clone(), solver, info),
                Op::Bvnot => primop::not_bits(args[0].clone(), solver, info),
                Op::Bvor => primop::or_bits(args[0].clone(), args[1].clone(), solver, info),
                Op::Bvxor => primop::xor_bits(args[0].clone(), args[1].clone(), solver, info),
                Op::Bvand => primop::and_bits(args[0].clone(), args[1].clone(), solver, info),
                Op::Bvadd => primop::add_bits(args[0].clone(), args[1].clone(), solver, info),
                Op::Bvsub => primop::sub_bits(args[0].clone(), args[1].clone(), solver, info),
                Op::Bvaccess => primop::vector_access(args[0].clone(), args[1].clone(), solver, info),
                Op::Concat => primop::append(args[0].clone(), args[1].clone(), solver, info),
                Op::Not => primop::not_bool(args[0].clone(), solver, info),
                Op::And => primop::and_bool(args[0].clone(), args[1].clone(), solver, info),
                Op::Or => primop::or_bool(args[0].clone(), args[1].clone(), solver, info),
                Op::Slice(len) => primop::op_slice(args[0].clone(), args[1].clone(), *len, solver, info),
                Op::SetSlice => primop::op_set_slice(args[0].clone(), args[1].clone(), args[2].clone(), solver, info),
                Op::Unsigned(_) => primop::op_unsigned(args[0].clone(), solver, info),
                Op::Signed(_) => primop::op_signed(args[0].clone(), solver, info),
                Op::Head => primop::op_head(args[0].clone(), solver, info),
                Op::Tail => primop::op_tail(args[0].clone(), solver, info),
                Op::IsEmpty => primop::op_is_empty(args[0].clone(), solver, info),
                Op::ZeroExtend(len) => primop::op_zero_extend(args[0].clone(), *len, solver, info),
            };
            if matches!(result, Err(ExecError::SymbolicLength(..) | ExecError::IntegerConversion(..))) {
                local_state.expression_retry_operands = Some(args);
            }
            Owned(result?)
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

                Borrowed(Val::SymbolicCtor(tag, possibilities)) => match possibilities.get(ctor_a) {
                    Some(v) => {
                        let matches_tag = smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(*tag)), Box::new(ctor_a.to_smt()));
                        if solver.check_sat_with(&matches_tag, info).is_unsat()? {
                            return Err(ExecError::Type(format!("Constructors didn't match {:?}", ctor_a), info));
                        }
                        Borrowed(v)
                    }
                    None => return Err(ExecError::Type("No possible value for constructor".to_string(), info)),
                },

                Owned(Val::SymbolicCtor(tag, mut possibilities)) => match possibilities.remove(ctor_a) {
                    Some(v) => {
                        let matches_tag = smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(tag)), Box::new(ctor_a.to_smt()));
                        if solver.check_sat_with(&matches_tag, info).is_unsat()? {
                            return Err(ExecError::Type(format!("Constructors didn't match {:?}", ctor_a), info));
                        }
                        Owned(v)
                    }
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
    let key = exp as *const Exp<Name> as usize;
    if let Some(value) = local_state.expression_values.get(&key) {
        return Ok(Cow::Owned(value.clone()));
    }
    let value = eval_exp_with_accessor(exp, local_state, shared_state, solver, &mut Vec::new(), info)?.into_owned();
    // 任一后续子表达式或操作数都可能要求重试，成功求值的读取副作用只执行一次。
    local_state.expression_values.insert(key, value.clone());
    Ok(Cow::Owned(value))
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
        let triggered = match frame.local_state.regs.get(interrupt.trigger_register, shared_state, solver, info)? {
            Some(Val::Bits(reg_value)) => *reg_value == interrupt.trigger_value,
            Some(Val::Symbolic(sym)) => {
                let equal = smtlib::Exp::Eq(
                    Box::new(smtlib::Exp::Var(*sym)),
                    Box::new(crate::primop_util::smt_sbits(interrupt.trigger_value)),
                );
                let triggered = solver.check_sat_with(&equal, info).is_sat()?;
                if triggered {
                    assert!(
                        !solver.check_sat_with(&smtlib::Exp::Not(Box::new(equal)), info).is_sat()?,
                        "中断查询前必须拆分触发与未触发路径"
                    );
                }
                triggered
            }
            _ => return Err(ExecError::BadInterrupt("trigger register does not exist, or is not a bitvector")),
        };

        if triggered {
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
        let arg = symbolic_length::eval_operands(args, frame, shared_state, solver, info)?.pop().unwrap();
        let arg = match arg {
            Val::Symbolic(sym) => match primop::proven_symbolic_i128(sym, solver, info)? {
                Some(len) => Val::I64(i64::try_from(len).map_err(|_| ExecError::Overflow)?),
                None => return Err(ExecError::SymbolicLength("internal_vector_init", info)),
            },
            value => value,
        };
        match loc {
            Loc::Id(v) => match (arg, frame.vars().get(v)) {
                (Val::I64(len), Some(UVal::Uninit(Ty::Vector(_) | Ty::FixedVector(_, _)))) => assign(
                    tid,
                    loc,
                    Val::Vector(vec![Val::Poison; usize::try_from(len).map_err(|_| ExecError::Overflow)?]),
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
        let args = symbolic_length::eval_operands(args, frame, shared_state, solver, info)?;
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
        let mut operands = symbolic_length::eval_operands(args, frame, shared_state, solver, info)?;
        let regs = operands.pop().unwrap();
        let n = operands.pop().unwrap();
        let value = read_register_from_vector(n, regs, &mut frame.local_state, shared_state, solver, info)?;
        assign(tid, loc, value, &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else if f == WRITE_REGISTER_FROM_VECTOR {
        assert!(args.len() == 3);
        let mut operands = symbolic_length::eval_operands(args, frame, shared_state, solver, info)?;
        let regs = operands.pop().unwrap();
        let value = operands.pop().unwrap();
        let n = operands.pop().unwrap();
        write_register_from_vector(n, value, regs, &mut frame.local_state, shared_state, solver, info)?;
        assign(tid, loc, Val::Unit, &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else if f == INSTR_ANNOUNCE {
        assert!(args.len() == 1);
        let opcode = symbolic_length::eval_operands(args, frame, shared_state, solver, info)?.pop().unwrap();
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
                    Val::Symbolic(sym) => {
                        assert!(solver.check_sat(info).is_sat()?, "指令公告前的 PC 路径必须可满足");
                        let bv = {
                            let mut model = Model::new(solver);
                            model.set_complete_model(true);
                            match model.get_var(*sym)? {
                                ModelVal::Exp(smtlib::Exp::Bits64(b64)) => B::new(b64.lower_u64(), b64.len()),
                                ModelVal::Exp(smtlib::Exp::Bits(bits)) => crate::smt::model_bits_to_bv(&bits)?,
                                _ => panic!("PC 模型值必须是位向量"),
                            }
                        };
                        let uniqueness = smtlib::Exp::Neq(
                            Box::new(smtlib::Exp::Var(*sym)),
                            Box::new(crate::primop_util::smt_sbits(bv)),
                        );
                        if solver.check_sat_with(&uniqueness, info).is_sat()? {
                            panic!("指令公告前必须将符号 PC 拆分为唯一候选");
                        }
                        let count = frame.pc_counts.entry(bv).or_insert(0);
                        *count += 1;
                        if *count > limit {
                            return Err(ExecError::PCLimitReached(bv.lower_u64()));
                        }
                    }
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
            Val::Symbolic(sym) if task_state.zero_announce_exit => {
                let width = solver.length(sym).expect("指令编码必须是位向量");
                let zero =
                    smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(sym)), Box::new(primop::smt_zeros(i128::from(width))));
                if solver.check_sat_with(&zero, info).is_sat()? {
                    assert!(
                        !solver.check_sat_with(&smtlib::Exp::Not(Box::new(zero)), info).is_sat()?,
                        "公告前必须拆分零指令路径"
                    );
                    return Ok(SpecialResult::Exit);
                }
            }
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

use itrace_fork_frame_with_branch_condition;
use itrace_push_branch_condition;

/// 路径撞上 `--timeout` 预算时，输出这条路径的 SMT 用时构成与超时原因判定。
///
/// 关键区分是"确实需要更多时间"还是"少数 SMT 操作打满单次上限把预算吃掉了"：前者放宽
/// `--timeout` 有效，后者只有放宽 `--smt-timeout` 或简化约束才有用。
fn report_path_timeout<'ir, B: BV>(
    tid: usize,
    timeout: PathTimeout,
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
) {
    let diagnostic = PathTimeoutDiagnostic {
        limit: timeout.limit().expect("path timeout fired without a configured budget"),
        timing: frame.path_time_snapshot(),
        smt: crate::smt::path_smt_stats(),
        smt_operation_limit: crate::smt::configured_smt_operation_timeout(),
        control_flow_steps: frame.execution_limit_state.control_flow_steps(),
        position: format!("{}:{}", zencode::decode(shared_state.symtab.to_str(frame.function_name)), frame.pc),
    };
    let lines = diagnostic.report_lines(shared_state.symtab.files());
    for line in &lines {
        log_from!(tid, log::SYM_EXEC, line);
    }
    #[cfg(feature = "tracetool")]
    frame.itrace_path.record_summary(frame.function_name, frame.backtrace.clone(), frame.pc as u64, lines.join("\n"));
    #[cfg(not(feature = "tracetool"))]
    let _ = frame;
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
            ExecutionLimitReason::MaxForksPerRegion { region, actual, max } => format!(
                "max_forks_per_region exceeded: region={}, path_region_forks={}, max_forks_per_region={}",
                region, actual, max
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
        | ExecutionLimitReason::MaxForksPerRegion { .. }
        | ExecutionLimitReason::MaxForkPctPerBranch { .. } => ExecError::BranchLimitReached(function_name, pc),
    }
}

fn loop_limit_target(reason: ExecutionLimitReason) -> Option<usize> {
    match reason {
        ExecutionLimitReason::MaxBackjumpsPerLoop { target, .. } => Some(target),
        _ => None,
    }
}

fn record_loc_write<B: BV>(loc: &Loc<Name>, frame: &mut LocalFrame<B>) {
    if let Some(ws) = frame.write_set.as_mut() {
        let id = loc.id();
        if frame.local_state.vars.contains_key(&id) || frame.local_state.lets.contains_key(&id) {
            ws.modified_vars.insert(id);
        } else {
            ws.register_write_order.push(id);
            if !ws.modified_regs.insert(id) {
                ws.multiple_written_regs.insert(id);
            }
            if matches!(loc, Loc::Field(_, _)) {
                ws.read_regs.insert(id);
            }
        }
    }
}

fn detect_diamond_joins<B: BV>(instrs: &[Instr<Name, B>], pc: usize, target: usize) -> Vec<usize> {
    let mut joins = Vec::new();
    if target > pc + 1 && target <= instrs.len() {
        if target > 0 {
            if let Instr::Goto(join) = instrs[target - 1] {
                if join >= target && join <= pc + 64 && join <= instrs.len() {
                    joins.push(join);
                }
            }
        }
        if target <= pc + 64 {
            joins.push(target);
        }
    }
    joins
}

fn simulate_assign<'ir, B: BV>(
    loc: &Loc<Name>,
    v: Val<B>,
    local_state: &mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<(), ExecError> {
    let mut base_loc = loc;
    while let Loc::Field(inner, _) = base_loc {
        base_loc = inner;
    }
    if matches!(base_loc, Loc::Addr(_)) {
        return Err(ExecError::IncompatibleMerge);
    }
    match loc {
        Loc::Id(id) => {
            if local_state.vars.contains_key(id) {
                local_state.vars.insert(*id, UVal::Init(v));
            } else if local_state.lets.contains_key(id) {
                local_state.lets.insert(*id, UVal::Init(v));
            } else {
                local_state.regs.assign(*id, v, shared_state);
            }
            Ok(())
        }
        Loc::Field(sub_loc, field) => {
            let mut accessor = Vec::new();
            if let Val::Struct(field_values) =
                get_loc_and_initialize(sub_loc, local_state, shared_state, solver, &mut accessor, info, false)?
            {
                let mut field_values = field_values.clone();
                field_values.insert(*field, v);
                simulate_assign(sub_loc, Val::Struct(field_values), local_state, shared_state, solver, info)
            } else {
                Err(ExecError::Type(format!("Assign to field of non-struct {:?}", loc), info))
            }
        }
        Loc::Addr(_) => Err(ExecError::IncompatibleMerge),
    }
}

fn simulate_diamond_arm<'ir, B: BV>(
    start_pc: usize,
    end_pc: usize,
    join_pc: usize,
    mut arm: LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    limit_handler: Option<&ExecutionLimitHandler<'_>>,
) -> Result<Option<LocalFrame<'ir, B>>, ExecError> {
    arm.pc = start_pc;
    arm.write_set = Some(WriteSet::default());
    arm.local_state.register_reads = Some(Vec::new());
    let mut steps = 0;
    while arm.pc != join_pc {
        if steps >= 64 || arm.pc >= arm.instrs.len() || arm.pc < start_pc || arm.pc > end_pc {
            return Ok(None);
        }
        steps += 1;
        let had_register_write = !arm.write_set.as_ref().unwrap().register_write_order.is_empty();
        let read_count = arm.local_state.register_reads.as_ref().unwrap().len();
        match &arm.instrs[arm.pc] {
            Instr::Decl(v, ty, _) => {
                arm.vars_mut().insert(*v, UVal::Uninit(ty));
                if let Some(ws) = arm.write_set.as_mut() {
                    ws.modified_vars.insert(*v);
                }
                arm.pc += 1;
            }
            Instr::Init(var, _, exp, info) => {
                let value = eval_exp(exp, &mut arm.local_state, shared_state, solver, *info)?.into_owned();
                arm.vars_mut().insert(*var, UVal::Init(value));
                if let Some(ws) = arm.write_set.as_mut() {
                    ws.modified_vars.insert(*var);
                }
                arm.pc += 1;
            }
            Instr::Copy(loc, exp, info) => {
                let value = eval_exp(exp, &mut arm.local_state, shared_state, solver, *info)?.into_owned();
                record_loc_write(loc, &mut arm);
                simulate_assign(loc, value, &mut arm.local_state, shared_state, solver, *info)?;
                arm.pc += 1;
            }
            Instr::PrimopUnary(loc, f, arg, info) => {
                if !crate::primop::is_pure_unary(*f) {
                    return Ok(None);
                }
                let arg = eval_exp(arg, &mut arm.local_state, shared_state, solver, *info)?.into_owned();
                let value = f(arg, solver, *info)?;
                record_loc_write(loc, &mut arm);
                simulate_assign(loc, value, &mut arm.local_state, shared_state, solver, *info)?;
                arm.pc += 1;
            }
            Instr::PrimopBinary(loc, f, arg1, arg2, info) => {
                if !crate::primop::is_pure_binary(*f) {
                    return Ok(None);
                }
                let arg1 = eval_exp(arg1, &mut arm.local_state, shared_state, solver, *info)?.into_owned();
                let arg2 = eval_exp(arg2, &mut arm.local_state, shared_state, solver, *info)?.into_owned();
                let value = f(arg1, arg2, solver, *info)?;
                record_loc_write(loc, &mut arm);
                simulate_assign(loc, value, &mut arm.local_state, shared_state, solver, *info)?;
                arm.pc += 1;
            }
            Instr::PrimopVariadic(..) => return Ok(None),
            Instr::Goto(target) => {
                if (*target != join_pc && (*target < start_pc || *target > end_pc)) || *target > arm.instrs.len() {
                    return Ok(None);
                }
                let decision = match limit_handler {
                    Some(handler) => handler.on_goto(
                        &mut arm.execution_limit_state,
                        arm.function_name,
                        arm.pc,
                        *target,
                        &arm.backtrace,
                    ),
                    None => {
                        arm.execution_limit_state.advance_control_flow();
                        ExecutionLimitDecision::Continue
                    }
                };
                if !matches!(decision, ExecutionLimitDecision::Continue) {
                    return Ok(None);
                }
                arm.pc = *target;
            }
            Instr::Jump(exp, target, info) => {
                let value = eval_exp(exp, &mut arm.local_state, shared_state, solver, *info)?;
                let decision = match limit_handler {
                    Some(handler) => handler.on_conditional_jump(
                        &mut arm.execution_limit_state,
                        arm.function_name,
                        arm.pc,
                        *target,
                        &arm.backtrace,
                        *info,
                    ),
                    None => {
                        arm.execution_limit_state.advance_control_flow();
                        ExecutionLimitDecision::Continue
                    }
                };
                if !matches!(decision, ExecutionLimitDecision::Continue) {
                    return Ok(None);
                }
                match *value.as_ref() {
                    Val::Bool(true) => {
                        if (*target != join_pc && (*target < start_pc || *target > end_pc))
                            || *target > arm.instrs.len()
                        {
                            return Ok(None);
                        }
                        arm.pc = *target;
                    }
                    Val::Bool(false) => {
                        if arm.pc + 1 != join_pc && arm.pc + 1 > end_pc {
                            return Ok(None);
                        }
                        arm.pc += 1;
                    }
                    _ => return Ok(None),
                }
            }
            _ => {
                return Ok(None);
            }
        }
        arm.local_state.expression_values.clear();
        if had_register_write && arm.local_state.register_reads.as_ref().unwrap().len() > read_count {
            // 当前事务先提交读取再提交写入，无法保留写后读的原始顺序。
            return Ok(None);
        }
    }
    arm.write_set
        .as_mut()
        .unwrap()
        .read_regs
        .extend(arm.local_state.register_reads.as_ref().unwrap().iter().map(|(reg, _, _)| *reg));
    Ok(Some(arm))
}

fn merge_two_frames<'ir, B: BV>(
    cond_sym: Sym,
    frame: &mut LocalFrame<'ir, B>,
    arm_then: &LocalFrame<'ir, B>,
    arm_else: &LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<bool, ExecError> {
    let ws_then = match arm_then.write_set.as_ref() {
        Some(ws) => ws,
        None => return Ok(false),
    };
    let ws_else = match arm_else.write_set.as_ref() {
        Some(ws) => ws,
        None => return Ok(false),
    };
    if ws_then.memory_modified || ws_else.memory_modified {
        return Ok(false);
    }
    if ws_then.read_regs != ws_else.read_regs
        || ws_then.register_write_order != ws_else.register_write_order
        || !arm_then
            .local_state
            .register_reads
            .as_ref()
            .unwrap()
            .iter()
            .map(|(reg, accessor, _)| (reg, accessor))
            .eq(arm_else.local_state.register_reads.as_ref().unwrap().iter().map(|(reg, accessor, _)| (reg, accessor)))
    {
        return Ok(false);
    }
    if ws_then.modified_regs != ws_else.modified_regs {
        return Err(ExecError::IncompatibleMerge);
    }

    let mut modified_vars = HashSet::new();
    let mut modified_regs = HashSet::new();
    modified_vars.extend(ws_then.modified_vars.iter().copied());
    modified_vars.extend(ws_else.modified_vars.iter().copied());
    modified_regs.extend(ws_then.modified_regs.iter().copied());
    modified_regs.extend(ws_else.modified_regs.iter().copied());
    modified_vars
        .extend(frame.vars().iter().filter_map(|(name, value)| matches!(value, UVal::Uninit(_)).then_some(*name)));
    modified_vars
        .extend(frame.lets().iter().filter_map(|(name, value)| matches!(value, UVal::Uninit(_)).then_some(*name)));
    for reg in ws_then.read_regs.union(&ws_else.read_regs) {
        if frame.regs().is_relaxed(*reg) {
            return Ok(false);
        }
        if frame.regs().get_last_if_initialized(*reg).is_none() {
            modified_regs.insert(*reg);
        }
    }

    for var in &modified_vars {
        // 新变量只存在于单臂时，不能在汇合后丢弃其作用域。
        if arm_then.vars().contains_key(var) != arm_else.vars().contains_key(var) {
            return Ok(false);
        }
        let v_then = arm_then.vars().get(var).and_then(|u| match u {
            UVal::Init(v) => Some(v),
            _ => None,
        });
        let v_else = arm_else.vars().get(var).and_then(|u| match u {
            UVal::Init(v) => Some(v),
            _ => None,
        });
        if v_then.is_some() != v_else.is_some() {
            return Ok(false);
        }

        if matches!(frame.vars().get(var), Some(UVal::Uninit(_))) && v_then.is_none() && v_else.is_none() {
            continue;
        }
        if frame.vars().contains_key(var) || (arm_then.vars().contains_key(var) && arm_else.vars().contains_key(var)) {
            match (v_then, v_else) {
                (Some(vt), Some(ve)) => {
                    let merged = match crate::primop_util::merge_val(cond_sym, vt, ve, solver, info) {
                        Ok(m) => m,
                        Err(_) => return Ok(false),
                    };
                    frame.vars_mut().insert(*var, UVal::Init(merged));
                }
                _ => return Ok(false),
            }
        } else if frame.lets().contains_key(var) {
            let l_then = arm_then.lets().get(var).and_then(|u| match u {
                UVal::Init(v) => Some(v),
                _ => None,
            });
            let l_else = arm_else.lets().get(var).and_then(|u| match u {
                UVal::Init(v) => Some(v),
                _ => None,
            });
            if matches!(frame.lets().get(var), Some(UVal::Uninit(_))) && l_then.is_none() && l_else.is_none() {
                continue;
            }
            match (l_then, l_else) {
                (Some(vt), Some(ve)) => {
                    let merged = match crate::primop_util::merge_val(cond_sym, vt, ve, solver, info) {
                        Ok(m) => m,
                        Err(_) => return Ok(false),
                    };
                    frame.lets_mut().insert(*var, UVal::Init(merged));
                }
                _ => return Ok(false),
            }
        }
    }

    for reg in &modified_regs {
        if frame.regs().is_relaxed(*reg)
            || ws_then.multiple_written_regs.contains(reg)
            || ws_else.multiple_written_regs.contains(reg)
            || arm_then.regs().has_old_writes(*reg)
            || arm_else.regs().has_old_writes(*reg)
            || (ws_then.modified_regs.contains(reg) || ws_else.modified_regs.contains(reg))
                && (ws_then.read_regs.contains(reg) || ws_else.read_regs.contains(reg))
        {
            return Ok(false);
        }
        let r_then = arm_then.regs().get_last_if_initialized(*reg);
        let r_else = arm_else.regs().get_last_if_initialized(*reg);
        match (r_then, r_else) {
            (Some(rt), Some(re)) => {
                let merged = match crate::primop_util::merge_val(cond_sym, rt, re, solver, info) {
                    Ok(m) => m,
                    Err(_) => return Ok(false),
                };
                frame.regs_mut().assign(*reg, merged.clone(), shared_state);
            }
            _ => return Ok(false),
        }
    }

    Ok(true)
}

fn try_merge_diamond<'ir, B: BV>(
    cond_sym: Sym,
    target: usize,
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
    limit_handler: Option<&ExecutionLimitHandler<'_>>,
    limited_pc: Option<Name>,
) -> Result<Option<usize>, ExecError> {
    let pc = frame.pc;
    let candidate_joins = detect_diamond_joins(frame.instrs, pc, target);
    for join_pc in candidate_joins {
        let tx = solver.start_transaction();

        let arm_else =
            match simulate_diamond_arm(pc + 1, target - 1, join_pc, frame.clone(), shared_state, solver, limit_handler)
            {
                Ok(Some(a)) if !solver.transaction_invalid() => a,
                _ => {
                    solver.rollback_transaction(tx);
                    continue;
                }
            };
        // 两臂读取同一个尚未初始化的普通寄存器时，必须复用首次读取的符号。
        let mut then_frame = frame.clone();
        for (reg, _, value) in arm_else.local_state.register_reads.as_ref().unwrap() {
            if frame.regs().get_last_if_initialized(*reg).is_none() && !frame.regs().is_relaxed(*reg) {
                then_frame.regs_mut().assign(*reg, value.clone(), shared_state);
            }
        }
        let arm_then = match simulate_diamond_arm(
            target,
            join_pc.saturating_sub(1),
            join_pc,
            then_frame,
            shared_state,
            solver,
            limit_handler,
        ) {
            Ok(Some(a)) if !solver.transaction_invalid() => a,
            _ => {
                solver.rollback_transaction(tx);
                continue;
            }
        };

        if let Some(pc) = limited_pc {
            if arm_then.write_set.as_ref().unwrap().modified_regs.contains(&pc)
                || arm_else.write_set.as_ref().unwrap().modified_regs.contains(&pc)
            {
                solver.rollback_transaction(tx);
                continue;
            }
        }
        let mut merged_frame = frame.clone();
        // 有深度预算时，不等深度的两臂不能共享最大步数，否则会提前截断短路径。
        if limit_handler.map_or(false, |handler| handler.config.max_path_depth.is_some())
            && arm_then.execution_limit_state.control_flow_steps()
                != arm_else.execution_limit_state.control_flow_steps()
        {
            solver.rollback_transaction(tx);
            continue;
        }
        // 有回跳预算时，两臂必须保留相同的循环计数历史。
        if limit_handler.map_or(false, |handler| handler.config.max_backjumps_per_loop.is_some())
            && arm_then.execution_limit_state.loop_counts != arm_else.execution_limit_state.loop_counts
        {
            solver.rollback_transaction(tx);
            continue;
        }
        match merge_two_frames(cond_sym, &mut merged_frame, &arm_then, &arm_else, shared_state, solver, info) {
            Ok(true) if !solver.transaction_invalid() => {
                merged_frame.execution_limit_state = if arm_then.execution_limit_state.control_flow_steps()
                    >= arm_else.execution_limit_state.control_flow_steps()
                {
                    arm_then.execution_limit_state.clone()
                } else {
                    arm_else.execution_limit_state.clone()
                };
                let ws_then = arm_then.write_set.as_ref().unwrap();
                let ws_else = arm_else.write_set.as_ref().unwrap();
                // 在事务中检查能否表达相等关系，提交后才加入断言。
                let equalities: Result<Vec<_>, ExecError> = ws_then
                    .read_regs
                    .intersection(&ws_else.read_regs)
                    .filter(|reg| !ws_then.modified_regs.contains(reg))
                    .map(|reg| {
                        let rt = arm_then.regs().get_last_if_initialized(*reg).unwrap();
                        let re = arm_else.regs().get_last_if_initialized(*reg).unwrap();
                        let equal = primop::eq_anything(rt.clone(), re.clone(), solver, info)?;
                        crate::primop_util::smt_value(&equal, info)
                    })
                    .collect();
                let equalities = match equalities {
                    Ok(equalities) if !solver.transaction_invalid() => equalities,
                    _ => {
                        solver.rollback_transaction(tx);
                        continue;
                    }
                };
                solver.commit_transaction();
                for equal in equalities {
                    solver.add(smtlib::Def::Assert(equal));
                }
                // 两臂的寄存器及访问器序列已经验证对齐，每个位置保留一次读取。
                for ((reg, accessor, val_then), (_, _, val_else)) in arm_then
                    .local_state
                    .register_reads
                    .as_ref()
                    .unwrap()
                    .iter()
                    .zip(arm_else.local_state.register_reads.as_ref().unwrap())
                {
                    let val = if val_then == val_else {
                        val_then.clone()
                    } else {
                        build_ite(cond_sym, val_then, val_else, solver, info)?
                    };
                    let symbol = zencode::decode(shared_state.symtab.to_str(*reg));
                    if !symbol.contains("_TLB") {
                        solver.add_event(Event::ReadReg(*reg, accessor.clone(), val));
                    }
                }
                solver.order_transaction_register_reads(tx);
                *frame = merged_frame;
                for reg in &ws_then.register_write_order {
                    let value = frame.regs().get_last_if_initialized(*reg).unwrap().clone();
                    let symbol = zencode::decode(shared_state.symtab.to_str(*reg));
                    if symbol != "_TLB" {
                        solver.add_event(Event::WriteReg(*reg, Vec::new(), value));
                    }
                }
                // 保留合并条件的控制依赖；两种取值都可行，不添加选臂断言。
                solver.add_event(Event::Fork(0, cond_sym, 0, info));
                solver.add_event(Event::Merge(0, 2, info));
                return Ok(Some(join_pc));
            }
            _ => {
                solver.rollback_transaction(tx);
            }
        }
    }
    Ok(None)
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
    // 路径级 SMT 调用本身以线程局部方式计时；调度器会在 fork 时把累计值冻结在 Frame，
    // 因此任务恢复时必须先还原公共前缀，避免诊断漏掉 fork 前的求解时间。
    crate::smt::restore_path_smt_stats(frame.path_smt_stats.clone());
    loop {
        frame.local_state.expression_retry_operands = None;
        let error = match run_loop_inner(
            tid,
            task_id,
            task_fraction,
            timeout,
            stop_conditions,
            fork_sink,
            frame,
            task_state,
            shared_state,
            solver,
        ) {
            Ok(result) => return Ok(result),
            Err(error) => error,
        };
        let Some(operands) = frame.local_state.expression_retry_operands.clone() else { return Err(error) };
        if !symbolic_length::retry_symbolic_length(
            error,
            &operands,
            task_id,
            task_fraction,
            stop_conditions,
            fork_sink,
            frame,
            task_state,
            solver,
        )? {
            return Ok(Run::Dead);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn run_loop_inner<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B>>(
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
        if matches!(&frame.pending_retry_operand, Some((pc, Val::Unit)) if *pc != frame.pc) {
            frame.pending_retry_operand = None;
            frame.local_state.expression_values.clear();
            frame.local_state.expression_retry_operands = None;
        }
        if frame.pending_retry_operand.is_none() {
            frame.local_state.expression_values.clear();
        }
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
            report_path_timeout(tid, timeout, frame, shared_state);
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
                // 条件可能要求分叉重试；求值成功后再计入控制流和回跳预算。
                let value = eval_exp(exp, &mut frame.local_state, shared_state, solver, *info)?.into_owned();
                frame.pending_retry_operand = None;
                frame.local_state.expression_values.clear();
                frame.local_state.expression_retry_operands = None;
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
                    ExecutionLimitDecision::ConcretizeBranch { reason, sample } => match value {
                        Val::Symbolic(v) => {
                            use smtlib::Exp::*;

                            let handler = limit_handler.as_ref().expect("limit decision requires active handler");
                            handler.commit_sample(&mut frame.execution_limit_state, &sample);
                            record_execution_limit(frame, reason, "sample_branch_condition");
                            let concrete_bool = if loop_limit_target(reason).is_some() {
                                match concretize_loop_branch_with_sampling(v, solver, *info, &sample)? {
                                    Some(value) => value,
                                    None => {
                                        record_execution_limit(frame, reason, "truncate_exit_direction_unsatisfiable");
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
                    },
                    ExecutionLimitDecision::Fork { .. } | ExecutionLimitDecision::KeepCurrentModel { .. } => {
                        panic!("conditional jump pre-check returned an invalid execution-limit decision")
                    }
                }

                match value {
                    Val::Symbolic(v) => {
                        use smtlib::Def::*;
                        use smtlib::Exp::*;

                        let test_true = Var(v);
                        let test_false = Not(Box::new(Var(v)));

                        let can_be_true = solver.check_sat_with(&test_true, *info).is_sat()?;
                        let can_be_false = solver.check_sat_with(&test_false, *info).is_sat()?;

                        if can_be_true && can_be_false {
                            let path_merging =
                                task_state.execution_limits.as_ref().map(|l| l.path_merging).unwrap_or(false);
                            if path_merging {
                                if let Ok(Some(new_pc)) = try_merge_diamond(
                                    v,
                                    *target,
                                    frame,
                                    shared_state,
                                    solver,
                                    *info,
                                    limit_handler.as_ref(),
                                    task_state.pc_limit.map(|(pc, _)| pc),
                                ) {
                                    frame.pc = new_pc;
                                    continue 'main_loop;
                                }
                            }

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
                            frame.capture_path_smt_stats();
                            let mut frozen =
                                itrace_fork_frame_with_branch_condition!(frame, frame.pc + 1, test_false.clone());
                            // 父子路径的采样签名从这次 fork 起分叉，受限分支的具体化抽样
                            // 才会在不同路径上抽到不同方向。
                            Arc::make_mut(&mut frozen.execution_limit_state).advance_path_signature(false);
                            frame.execution_limit_state.advance_path_signature(true);
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
                let mut args = symbolic_length::eval_operands([arg], frame, shared_state, solver, *info)?;
                assert_eq!(args.len(), 1, "一元算子必须有一个操作数");
                let arg = args.pop().unwrap();
                let value = match f(arg.clone(), solver, *info) {
                    Ok(value) => value,
                    Err(error) => {
                        if symbolic_length::retry_symbolic_length(
                            error,
                            &[arg],
                            task_id,
                            task_fraction,
                            stop_conditions,
                            fork_sink,
                            frame,
                            task_state,
                            solver,
                        )? {
                            continue 'main_loop;
                        }
                        return Ok(Run::Dead);
                    }
                };
                frame.pending_retry_operand = None;
                assign(tid, loc, value, &mut frame.local_state, shared_state, solver, *info)?;
                frame.pc += 1;
            }

            Instr::PrimopBinary(loc, f, arg1, arg2, info) => {
                let mut args = symbolic_length::eval_operands([arg1, arg2], frame, shared_state, solver, *info)?;
                assert_eq!(args.len(), 2, "二元算子必须有两个操作数");
                let arg2 = args.pop().unwrap();
                let arg1 = args.pop().unwrap();
                let value = match f(arg1.clone(), arg2.clone(), solver, *info) {
                    Ok(value) => value,
                    Err(error) => {
                        if symbolic_length::retry_symbolic_length(
                            error,
                            &[arg1, arg2],
                            task_id,
                            task_fraction,
                            stop_conditions,
                            fork_sink,
                            frame,
                            task_state,
                            solver,
                        )? {
                            continue 'main_loop;
                        }
                        return Ok(Run::Dead);
                    }
                };
                frame.pending_retry_operand = None;
                assign(tid, loc, value, &mut frame.local_state, shared_state, solver, *info)?;
                frame.pc += 1;
            }

            Instr::PrimopVariadic(loc, f, args, info) => {
                let args = symbolic_length::eval_operands(args, frame, shared_state, solver, *info)?;
                let value = match f(args.clone(), solver, frame, *info) {
                    Ok(value) => value,
                    Err(error) => {
                        if symbolic_length::retry_symbolic_length(
                            error,
                            &args,
                            task_id,
                            task_fraction,
                            stop_conditions,
                            fork_sink,
                            frame,
                            task_state,
                            solver,
                        )? {
                            continue 'main_loop;
                        }
                        return Ok(Run::Dead);
                    }
                };
                frame.pending_retry_operand = None;
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
                // 长度或条件拆分重试的是同一条 Call，只在首次执行时计入深度。
                let decision = if frame.pending_retry_operand.is_some() {
                    ExecutionLimitDecision::Continue
                } else {
                    match limit_handler.as_ref() {
                        Some(handler) => handler.on_call(&mut frame.execution_limit_state),
                        None => {
                            frame.execution_limit_state.advance_control_flow();
                            ExecutionLimitDecision::Continue
                        }
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
                        let operands = if matches!(
                            *f,
                            INTERNAL_VECTOR_INIT
                                | INTERNAL_VECTOR_UPDATE
                                | READ_REGISTER_FROM_VECTOR
                                | WRITE_REGISTER_FROM_VECTOR
                                | INSTR_ANNOUNCE
                                | INTERRUPT_PENDING
                        ) {
                            Some(symbolic_length::eval_operands(args, frame, shared_state, solver, *info)?)
                        } else {
                            None
                        };
                        if *f == INSTR_ANNOUNCE {
                            if let Some((arch_pc, _)) = task_state.pc_limit {
                                let pc = frame.local_state.regs.get(arch_pc, shared_state, solver, *info)?.cloned();
                                if let Some(Val::Symbolic(sym)) = pc {
                                    if solver.check_sat(*info).is_unsat()? {
                                        return Ok(Run::Dead);
                                    }
                                    if symbolic_length::fork_symbolic_value(
                                        sym,
                                        operands.as_ref().unwrap(),
                                        *info,
                                        task_id,
                                        task_fraction,
                                        stop_conditions,
                                        fork_sink,
                                        frame,
                                        task_state,
                                        solver,
                                    )? {
                                        continue 'main_loop;
                                    }
                                }
                            }
                        }
                        if *f == INTERRUPT_PENDING {
                            for interrupt in &task_state.interrupts {
                                let reg = frame
                                    .local_state
                                    .regs
                                    .get(interrupt.trigger_register, shared_state, solver, *info)?
                                    .cloned();
                                let equal = match reg {
                                    Some(Val::Symbolic(sym)) => smtlib::Exp::Eq(
                                        Box::new(smtlib::Exp::Var(sym)),
                                        Box::new(crate::primop_util::smt_sbits(interrupt.trigger_value)),
                                    ),
                                    Some(Val::Bits(value)) if value == interrupt.trigger_value => break,
                                    Some(Val::Bits(_)) => continue,
                                    _ => {
                                        return Err(ExecError::BadInterrupt(
                                            "trigger register does not exist, or is not a bitvector",
                                        ))
                                    }
                                };
                                if solver.check_sat_with(&equal, *info).is_sat()? {
                                    if solver
                                        .check_sat_with(&smtlib::Exp::Not(Box::new(equal.clone())), *info)
                                        .is_sat()?
                                    {
                                        let cond = solver.define_const(equal, *info);
                                        symbolic_length::fork_retry_operand(
                                            cond,
                                            smtlib::Exp::Var(cond),
                                            smtlib::Exp::Not(Box::new(smtlib::Exp::Var(cond))),
                                            operands.as_ref().unwrap(),
                                            *info,
                                            task_id,
                                            task_fraction,
                                            stop_conditions,
                                            fork_sink,
                                            frame,
                                            task_state,
                                            solver,
                                        )?;
                                        continue 'main_loop;
                                    }
                                    break;
                                }
                            }
                        }
                        if *f == INSTR_ANNOUNCE && task_state.zero_announce_exit {
                            if let Val::Symbolic(sym) = operands.as_ref().unwrap()[0] {
                                let width = solver.length(sym).expect("指令编码必须是位向量");
                                let zero = smtlib::Exp::Eq(
                                    Box::new(smtlib::Exp::Var(sym)),
                                    Box::new(primop::smt_zeros(i128::from(width))),
                                );
                                if solver.check_sat_with(&zero, *info).is_sat()?
                                    && solver
                                        .check_sat_with(&smtlib::Exp::Not(Box::new(zero.clone())), *info)
                                        .is_sat()?
                                {
                                    let cond = solver.define_const(zero, *info);
                                    symbolic_length::fork_retry_operand(
                                        cond,
                                        smtlib::Exp::Var(cond),
                                        smtlib::Exp::Not(Box::new(smtlib::Exp::Var(cond))),
                                        operands.as_ref().unwrap(),
                                        *info,
                                        task_id,
                                        task_fraction,
                                        stop_conditions,
                                        fork_sink,
                                        frame,
                                        task_state,
                                        solver,
                                    )?;
                                }
                            }
                        }
                        // 特殊调用也必须复用预检时的操作数，避免重试时重新读取寄存器。
                        if let Some(operands) = &operands {
                            frame.pending_retry_operand = Some((frame.pc, Val::Vector(operands.clone())));
                        }
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
                        ) {
                            Ok(SpecialResult::Continue) => frame.pending_retry_operand = None,
                            Ok(SpecialResult::Exit) => return Ok(Run::Exit),
                            Err(error) => {
                                let Some(operands) = operands else { return Err(error) };
                                if symbolic_length::retry_symbolic_length(
                                    error,
                                    &operands,
                                    task_id,
                                    task_fraction,
                                    stop_conditions,
                                    fork_sink,
                                    frame,
                                    task_state,
                                    solver,
                                )? {
                                    continue 'main_loop;
                                }
                                return Ok(Run::Dead);
                            }
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
                        Ty::I64 | Ty::I128 => {
                            let width = if matches!(ty, Ty::I64) { 64 } else { 128 };
                            assert_eq!(solver.length(v), Some(width), "整数具体化的位宽必须匹配类型");
                            let sym = solver.declare_const(smtlib::Ty::BitVec(width), *info);
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
                                Ty::I64 => {
                                    assert_eq!(bv.len(), 64);
                                    (Bits64(bv), Val::I64(bv.lower_u64() as i64))
                                }
                                _ => panic!("failed to interpret monomorphized value"),
                            },

                            Ok(ModelVal::Exp(Bits(bv))) => match ty {
                                Ty::Bits(len) => {
                                    assert_eq!(bv.len(), *len as usize);
                                    (Bits(bv.clone()), Val::Bits(crate::smt::model_bits_to_bv(&bv)?))
                                }
                                Ty::AnyBits => (Bits(bv.clone()), Val::Bits(crate::smt::model_bits_to_bv(&bv)?)),
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
                                Ty::I64 => (bits64(0, 64), Val::I64(0)),
                                Ty::I128 => (Bits(vec![false; 128]), Val::I128(0)),
                                _ => panic!("failed to interpret monomorphized value"),
                            },

                            Err(error) => return Err(error),
                        }
                    };

                    let remainder = Neq(Box::new(Var(v)), Box::new(result_exp.clone()));
                    if solver.check_sat_with(&remainder, *info).is_sat()? {
                        let decision = match limit_handler.as_ref() {
                            Some(handler) => handler.on_monomorphize_fork_at(
                                &mut frame.execution_limit_state,
                                frame.function_name,
                                frame.pc,
                                &frame.backtrace,
                                *info,
                            ),
                            None => ExecutionLimitDecision::Fork { fork_id: frame.execution_limit_state.record_fork() },
                        };
                        let fork_id = match decision {
                            ExecutionLimitDecision::Fork { fork_id } => Some(fork_id),
                            ExecutionLimitDecision::KeepCurrentModel { reason } => {
                                frame.execution_limit_state.record_kept_current_model();
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
                            // 与条件分支 fork 一样，让父子路径的采样签名从这里分叉。
                            frame.capture_path_smt_stats();
                            let mut child_frame = freeze_frame(frame);
                            Arc::make_mut(&mut child_frame.execution_limit_state).advance_path_signature(false);
                            frame.execution_limit_state.advance_path_signature(true);
                            fork_sink.submit(Task {
                                id: task_id,
                                fraction: child_frac,
                                frame: child_frame,
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
        if matches!(&frame.pending_retry_operand, Some((_, Val::Unit))) {
            frame.pending_retry_operand = None;
        }
        frame.local_state.expression_values.clear();
        frame.local_state.expression_retry_operands = None;
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
    mut solver: Solver<B>,
    collected: &TraceResultQueue<B>,
) {
    match result {
        Ok((Run::Finished(Val::Bool(result)), frame)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, result, events.drain(..).cloned().collect())));
            submit_itrace_for_local_frame(&frame, shared_state);
        }
        Ok((Run::Finished(Val::Symbolic(sym)), frame)) if solver.is_bool(sym) => {
            let info = SourceLoc::unknown();
            for result in [false, true] {
                let condition =
                    if result { smtlib::Exp::Var(sym) } else { smtlib::Exp::Not(Box::new(smtlib::Exp::Var(sym))) };
                match solver.check_sat_with(&condition, info).is_sat() {
                    Ok(true) => {
                        // 轨迹按逆序存储；只向本结果的副本追加断言，不改变下一分支的 solver。
                        let mut events = vec![Event::Smt(smtlib::Def::Assert(condition), DefAttrs::default(), info)];
                        events.extend(solver.trace().to_vec().into_iter().cloned());
                        collected.push(Ok((task_id, result, events)));
                    }
                    Ok(false) => (),
                    Err(error) => collected
                        .push(Err(TraceError::exec(error, backtrace_string(&frame.backtrace, &shared_state.symtab)))),
                }
            }
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
    mut solver: Solver<B>,
    collected: &TraceQueue<B>,
) {
    match result {
        // Footprint function returns true on traces we need to consider as part of the footprint
        Ok((Run::Finished(Val::Bool(true)), frame)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, events.drain(..).cloned().collect())));
            submit_itrace_for_local_frame(&frame, shared_state);
        }
        Ok((Run::Finished(Val::Symbolic(sym)), frame)) if solver.is_bool(sym) => {
            let info = SourceLoc::unknown();
            match solver.check_sat_with(&smtlib::Exp::Var(sym), info).is_sat() {
                Ok(true) => {
                    solver.assert(smtlib::Exp::Var(sym));
                    let events = solver.trace().to_vec().into_iter().cloned().collect();
                    collected.push(Ok((task_id, events)));
                }
                Ok(false) => (),
                Err(error) => collected
                    .push(Err(TraceError::exec(error, backtrace_string(&frame.backtrace, &shared_state.symtab)))),
            }
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
    initial_memory: Option<crate::memory::Memory<B>>,
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

    if let Some(memory) = initial_memory {
        initial_frame.set_memory(memory);
    }

    // handler 在本次执行会话内只读共享；所有影响路径选择的计数随 Frame 复制。
    let task_id = TaskId::fresh();
    let task = initial_frame.task_with_checkpoint(task_id, &task_state, checkpoint);

    start_multi(num_threads, timeout, vec![task], &shared_state, collected.clone(), collector);
}

#[cfg(test)]
mod tests {
    mod review27_tests;
    mod review28_tests;
    mod review29_tests;
    mod review30_tests;
    mod symbolic_ctor_unwrap_tests;

    mod review26_tests {
        use super::*;

        #[test]
        fn 合并写入必须保留特殊寄存器事件过滤() {
            let mut observed = Vec::new();
            for enabled in [false, true] {
                let mut shared = empty_shared_state();
                let encoded = zencode::encode("_TLB");
                let reg = shared.symtab.intern(&encoded);
                let cond = test_name(620);
                let mut frame = make_frame(vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Jump(Exp::Id(cond), 4, info()),
                    Instr::Copy(Loc::Id(reg), Exp::Bool(false), info()),
                    Instr::Goto(5),
                    Instr::Copy(Loc::Id(reg), Exp::Bool(true), info()),
                    Instr::End,
                ]);
                frame.regs_mut().insert(reg, false, UVal::Init(Val::Bool(false)));
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let out = Mutex::new(Vec::new());
                start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, solver, out| {
                    assert!(matches!(result, Ok((Run::Finished(_), _))));
                    let events = solver.trace().to_vec();
                    let writes =
                        events.iter().filter(|event| matches!(event, Event::WriteReg(r, _, _) if *r == reg)).count();
                    let merges = events.iter().filter(|event| matches!(event, Event::Merge(..))).count();
                    out.lock().unwrap().push((writes, merges));
                });
                observed.push((enabled, out.into_inner().unwrap()));
            }
            eprintln!("特殊寄存器写轨迹：{observed:?}");
            assert!(observed.iter().all(|(_, paths)| paths.iter().all(|(writes, _)| *writes == 0)));
        }

        #[test]
        fn 宽地址合并不能丢弃具体区域读() {
            use crate::bitvector::b129::B129;
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let mut memory = crate::memory::Memory::new();
            memory.add_concrete_region(0x1000..0x1002, HashMap::from([(0x1000, 1), (0x1001, 2)]));
            let left = Val::Bits(B129::new(0x1000, 65));
            let right = Val::Bits(B129::new(0x1001, 65));
            for address in [&left, &right] {
                assert!(memory
                    .read(Val::Unit, address.clone(), Val::I128(1), &mut solver, false, crate::smt::ReadOpts::default())
                    .is_ok());
            }
            let condition = solver.declare_const(smtlib::Ty::Bool, info());
            let merged = crate::primop_util::merge_val(condition, &left, &right, &mut solver, info()).unwrap();
            let result =
                memory.read(Val::Unit, merged, Val::I128(1), &mut solver, false, crate::smt::ReadOpts::default());
            eprintln!("宽地址读取：{result:?}");
            assert!(
                matches!(result, Err(ExecError::SymbolicLength("read_mem_address", _))),
                "应进入地址谓词拆分而不是丢弃合法读：{result:?}"
            );
        }

        #[test]
        fn 合并后位向量计算与具体执行一致() {
            use crate::bitvector::b129::B129;
            let mut failures = Vec::new();
            for width in [1, 2, 8, 32, 64, 65, 127, 128, 129] {
                for (left, right) in [(B129::zeros(width), B129::ones(width)), (B129::new(1, width), B129::ones(width))]
                {
                    for name in ["shiftl", "shiftr", "arith_shiftr"] {
                        for shift in [-1, 0, 1, i128::from(width - 1), i128::from(width), i128::from(width + 1), 256] {
                            for select in [false, true] {
                                let ctx = Context::new(Config::new());
                                let mut solver = Solver::<B129>::new(&ctx);
                                let condition = solver.declare_const(smtlib::Ty::Bool, info());
                                let input = crate::primop_util::merge_val(
                                    condition,
                                    &Val::Bits(left),
                                    &Val::Bits(right),
                                    &mut solver,
                                    info(),
                                )
                                .unwrap();
                                let op = primop::binary_primops()[name];
                                let actual = op(input, Val::I128(shift), &mut solver, info()).unwrap();
                                let expected = op(
                                    Val::Bits(if select { left } else { right }),
                                    Val::I128(shift),
                                    &mut solver,
                                    info(),
                                )
                                .unwrap();
                                solver.assert(smtlib::Exp::Eq(
                                    Box::new(smtlib::Exp::Var(condition)),
                                    Box::new(smtlib::Exp::Bool(select)),
                                ));
                                let mismatch = smtlib::Exp::Neq(
                                    Box::new(crate::primop_util::smt_value(&actual, info()).unwrap()),
                                    Box::new(crate::primop_util::smt_value(&expected, info()).unwrap()),
                                );
                                if solver.check_sat_with(&mismatch, info()).is_sat().unwrap() {
                                    failures.push((name, width, shift, select, left, right, expected));
                                }
                            }
                        }
                    }
                }
            }
            assert!(failures.is_empty(), "合并后的移位计算发生差异：{failures:?}");
        }

        #[test]
        fn 宽地址菱形必须保留合法访存路径() {
            use crate::bitvector::b129::B129;
            let mut observations = Vec::new();
            for enabled in [false, true] {
                let defs: &'static [crate::ir::Def<Name, B129>] = &[];
                let shared = SharedState::new(
                    Symtab::new(),
                    defs,
                    IRTypeInfo::new(defs),
                    HashSet::new(),
                    HashSet::new(),
                    HashSet::new(),
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                );
                let cond = test_name(620);
                let address = test_name(621);
                let operations = primop::binary_primops::<B129>();
                let instrs = vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(address, Ty::Bits(65), info()),
                    Instr::Jump(Exp::Id(cond), 5, info()),
                    Instr::PrimopBinary(
                        Loc::Id(address),
                        operations["zero_extend"],
                        Exp::Bits(B64::new(0x1000, 64)),
                        Exp::I128(65),
                        info(),
                    ),
                    Instr::Goto(6),
                    Instr::PrimopBinary(
                        Loc::Id(address),
                        operations["zero_extend"],
                        Exp::Bits(B64::new(0x1001, 64)),
                        Exp::I128(65),
                        info(),
                    ),
                    Instr::PrimopVariadic(
                        Loc::Id(RETURN),
                        primop::variadic_primops()["read_mem"],
                        vec![Exp::Unit, Exp::I128(65), Exp::Id(address), Exp::I128(1)],
                        info(),
                    ),
                    Instr::End,
                ];
                let mut frame =
                    LocalFrame::new(test_name(25), &[], &Ty::Unit, None, Box::leak(instrs.into_boxed_slice()));
                frame.memory_mut().add_concrete_region(0x1000..0x1002, HashMap::from([(0x1000, 1), (0x1001, 2)]));
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let out = Mutex::new(Vec::new());
                start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, solver, out| {
                    let merged = solver.trace().to_vec().iter().any(|event| matches!(event, Event::Merge(..)));
                    out.lock().unwrap().push((
                        merged,
                        result
                            .map(|(run, _)| matches!(run, Run::Finished(_)))
                            .map_err(|(error, _)| format!("{error:?}")),
                    ));
                });
                observations.push((enabled, out.into_inner().unwrap()));
            }
            eprintln!("宽地址实际执行：{observations:?}");
            assert!(observations.iter().all(|(_, paths)| paths.iter().any(|(_, result)| matches!(result, Ok(true)))));
        }

        #[test]
        fn 合并后单态化不得采用任意默认值() {
            for ty in [Ty::Bits(8), Ty::I64, Ty::I128] {
                let cond = test_name(620);
                let bits = test_name(621);
                let value = test_name(622);
                let mut instrs = vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(bits, Ty::Bits(8), info()),
                    Instr::Decl(value, ty.clone(), info()),
                    Instr::Jump(Exp::Id(cond), 6, info()),
                    Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(1, 8)), info()),
                    Instr::Goto(7),
                    Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(2, 8)), info()),
                ];
                match ty {
                    Ty::Bits(_) => instrs.push(Instr::Copy(Loc::Id(value), Exp::Id(bits), info())),
                    Ty::I64 => instrs.push(Instr::Copy(
                        Loc::Id(value),
                        Exp::Call(Op::Unsigned(8), vec![Exp::Id(bits)]),
                        info(),
                    )),
                    Ty::I128 => instrs.push(Instr::PrimopUnary(
                        Loc::Id(value),
                        primop::unary_primops()["sail_unsigned"],
                        Exp::Id(bits),
                        info(),
                    )),
                    _ => unreachable!(),
                }
                instrs.extend([
                    Instr::Monomorphize(value, ty.clone(), info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(value), info()),
                    Instr::End,
                ]);
                let results = run_all_with_bindings(
                    instrs,
                    ExecutionLimits::default().with_path_merging(true),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                assert_eq!(results.len(), 2, "单态化必须保留两个值：{ty:?}");
                let mut values = results
                    .into_iter()
                    .map(|result| match result.unwrap() {
                        Run::Finished(Val::Bits(bits)) => bits.lower_u64(),
                        Run::Finished(Val::I64(value)) => value as u64,
                        Run::Finished(Val::I128(value)) => value as u64,
                        _ => panic!("单态化未正常完成"),
                    })
                    .collect::<Vec<_>>();
                values.sort();
                assert_eq!(values, [1, 2], "不得物化为候选域之外的默认值：{ty:?}");
            }
        }
    }
    mod review25_tests {
        use super::*;

        #[test]
        fn 地址重试必须先拆分未固定的符号长度() {
            for op in ["read_mem_address", "write_mem_address", "read_memt_address", "write_memt_address"] {
                let ctx = Context::new(Config::new());
                let mut solver = Solver::<B64>::new(&ctx);
                let address = solver.declare_bitvector(64, info());
                solver.assert(smtlib::Exp::Bvult(Box::new(smtlib::Exp::Var(address)), Box::new(smtlib::bits64(8, 64))));
                let condition = solver.declare_const(smtlib::Ty::Bool, info());
                let bytes = solver.define_const(
                    smtlib::Exp::Ite(
                        Box::new(smtlib::Exp::Var(condition)),
                        Box::new(crate::primop_util::smt_i128(4)),
                        Box::new(crate::primop_util::smt_i128(8)),
                    ),
                    info(),
                );
                let index = if matches!(op, "read_memt_address" | "write_memt_address") { 1 } else { 2 };
                let mut operands = vec![Val::Unit; index + 2];
                operands[index] = Val::Symbolic(address);
                operands[index + 1] = Val::Symbolic(bytes);
                let mut frame = make_frame(vec![Instr::End]);
                frame.memory_mut().add_excluded_region(8..16);
                let state = TaskState::new();
                let queue = Worker::new_lifo();
                let mut fraction = Fraction::one();
                assert!(symbolic_length::retry_symbolic_length(
                    ExecError::SymbolicLength(op, info()),
                    &operands,
                    TaskId::fresh(),
                    &mut fraction,
                    None,
                    &SingleForkSink { queue: &queue },
                    &mut frame,
                    &state,
                    &mut solver,
                )
                .unwrap());
                let child = queue.pop().expect("未固定长度必须拆为当前候选与剩余候选");
                assert!(queue.is_empty());
                let Some((Def::Assert(remainder), _)) = child.fork_cond else {
                    panic!("剩余长度必须携带分叉谓词")
                };
                let mut replay = Solver::from_checkpoint(&ctx, child.checkpoint);
                replay.assert(remainder);
                let selected = primop::proven_symbolic_i128(bytes, &mut solver, info()).unwrap().unwrap();
                let remaining = primop::proven_symbolic_i128(bytes, &mut replay, info()).unwrap().unwrap();
                assert!(matches!((selected, remaining), (4, 8) | (8, 4)), "{op} 必须保留两种长度");
                for candidate in 0..8 {
                    let equal =
                        smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(address)), Box::new(smtlib::bits64(candidate, 64)));
                    assert!(solver.check_sat_with(&equal, info()).is_sat().unwrap(), "{op} 不得提前收窄地址");
                    assert!(replay.check_sat_with(&equal, info()).is_sat().unwrap(), "{op} 不得丢弃剩余地址");
                }
            }
        }

        #[test]
        #[should_panic(expected = "内存访问重试必须提供长度或待写入数据")]
        fn 缺少长度和数据时禁止假定单字节访问() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let address = solver.declare_bitvector(64, info());
            let operands = vec![Val::Unit, Val::I128(64), Val::Symbolic(address)];
            let mut frame = make_frame(vec![Instr::End]);
            frame.memory_mut().add_excluded_region(8..16);
            let state = TaskState::new();
            let queue = Worker::new_lifo();
            let mut fraction = Fraction::one();
            symbolic_length::retry_symbolic_length(
                ExecError::SymbolicLength("read_mem_address", info()),
                &operands,
                TaskId::fresh(),
                &mut fraction,
                None,
                &SingleForkSink { queue: &queue },
                &mut frame,
                &state,
                &mut solver,
            )
            .unwrap();
        }

        #[test]
        fn 窄地址排除区域上界不能导致崩溃() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let address = solver.declare_bitvector(8, info());
            let mut memory = crate::memory::Memory::new();
            memory.add_excluded_region(8..256);
            let result = memory.read(
                Val::Unit,
                Val::Symbolic(address),
                Val::I128(4),
                &mut solver,
                false,
                crate::smt::ReadOpts::default(),
            );
            assert!(matches!(result, Err(ExecError::SymbolicLength("read_mem_address", _))));
        }

        #[test]
        fn 窄地址符号代码区上界不能导致崩溃() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let address = solver.declare_bitvector(8, info());
            let mut memory = crate::memory::Memory::new();
            memory.add_symbolic_code_region(0..256);
            let result = memory.read(
                Val::Unit,
                Val::Symbolic(address),
                Val::I128(1),
                &mut solver,
                false,
                crate::smt::ReadOpts::ifetch(),
            );
            assert!(result.is_ok(), "全部地址都属于代码区：{result:?}");
        }

        #[test]
        fn 已证明符号长度的排除区域拆分必须保留合法路径() {
            let mut failures = Vec::new();
            for op in [
                "read_mem",
                "read_mem_ifetch",
                "read_mem_exclusive",
                "platform_read_memt",
                "write_mem",
                "write_mem_exclusive",
                "platform_write_memt",
            ] {
                let ctx = Context::new(Config::new());
                let mut solver = Solver::<B64>::new(&ctx);
                let address = solver.declare_bitvector(64, info());
                solver.assert(smtlib::Exp::Bvult(Box::new(smtlib::Exp::Var(address)), Box::new(smtlib::bits64(8, 64))));
                let bytes = solver.define_const(crate::primop_util::smt_i128(4), info());
                let address_name = test_name(580);
                let bytes_name = test_name(581);
                let args = match op {
                    "platform_read_memt" => vec![Exp::Unit, Exp::Id(address_name), Exp::Id(bytes_name)],
                    "platform_write_memt" => vec![
                        Exp::Unit,
                        Exp::Id(address_name),
                        Exp::Id(bytes_name),
                        Exp::Bits(B64::zeros(32)),
                        Exp::Bits(B64::zeros(1)),
                    ],
                    "write_mem" | "write_mem_exclusive" => vec![
                        Exp::Unit,
                        Exp::I128(64),
                        Exp::Id(address_name),
                        Exp::Id(bytes_name),
                        Exp::Bits(B64::zeros(32)),
                    ],
                    _ => vec![Exp::Unit, Exp::I128(64), Exp::Id(address_name), Exp::Id(bytes_name)],
                };
                let mut frame = make_frame(vec![
                    Instr::PrimopVariadic(Loc::Id(RETURN), primop::variadic_primops()[op], args, info()),
                    Instr::End,
                ]);
                frame.vars_mut().insert(address_name, UVal::Init(Val::Symbolic(address)));
                frame.vars_mut().insert(bytes_name, UVal::Init(Val::Symbolic(bytes)));
                frame.memory_mut().add_excluded_region(8..16);
                if op == "read_mem_ifetch" {
                    frame.memory_mut().add_symbolic_code_region(0..8);
                }
                let state = TaskState::new();
                let out = Mutex::new(Vec::new());
                start_single(
                    frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
                    &empty_shared_state(),
                    &out,
                    &|_, _, result, _, _, out| {
                        out.lock().unwrap().push(
                            result
                                .map(|(run, _)| matches!(run, Run::Finished(_)))
                                .map_err(|(error, _)| format!("{error:?}")),
                        );
                    },
                );
                let results = out.into_inner().unwrap();
                eprintln!("{op}：{results:?}");
                if !results.iter().any(|result| matches!(result, Ok(true))) {
                    failures.push(op);
                }
            }
            assert!(failures.is_empty(), "地址 0..=4 的合法四字节访问被丢弃：{failures:?}");
        }

        #[test]
        fn 菱形合并后的访存长度不能丢失合法路径() {
            let mut observed = Vec::new();
            for enabled in [false, true] {
                let condition = test_name(580);
                let length_bits = test_name(581);
                let length = test_name(582);
                let address = Exp::Call(Op::Concat, vec![Exp::Bits(B64::zeros(61)), Exp::Undefined(Ty::Bits(3))]);
                let mut frame = make_frame(vec![
                    Instr::Decl(condition, Ty::Bool, info()),
                    Instr::Decl(length_bits, Ty::Bits(8), info()),
                    Instr::Decl(length, Ty::I128, info()),
                    Instr::Jump(Exp::Id(condition), 6, info()),
                    Instr::Copy(Loc::Id(length_bits), Exp::Bits(B64::new(4, 8)), info()),
                    Instr::Goto(7),
                    Instr::Copy(Loc::Id(length_bits), Exp::Bits(B64::new(8, 8)), info()),
                    Instr::PrimopUnary(
                        Loc::Id(length),
                        primop::unary_primops()["sail_unsigned"],
                        Exp::Id(length_bits),
                        info(),
                    ),
                    Instr::PrimopVariadic(
                        Loc::Id(RETURN),
                        primop::variadic_primops()["read_mem"],
                        vec![Exp::Unit, Exp::I128(64), address, Exp::Id(length)],
                        info(),
                    ),
                    Instr::End,
                ]);
                frame.memory_mut().add_excluded_region(8..16);
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let out = Mutex::new(Vec::new());
                start_single(
                    frame.task(TaskId::fresh(), &state),
                    &empty_shared_state(),
                    &out,
                    &|_, _, result, _, _, out| {
                        out.lock().unwrap().push(
                            result
                                .map(|(run, _)| matches!(run, Run::Finished(_)))
                                .map_err(|(error, _)| format!("{error:?}")),
                        );
                    },
                );
                let results = out.into_inner().unwrap();
                eprintln!("合并={enabled}：{results:?}");
                observed.push((enabled, results.iter().filter(|result| matches!(result, Ok(true))).count()));
            }
            assert!(observed.iter().all(|(_, count)| *count > 0), "合法访存路径因合并丢失：{observed:?}");
        }
    }
    mod review24_tests {
        use super::*;

        #[test]
        fn 排除区间拆分必须保留完整合法地址域() {
            for op in ["read_mem_address", "write_mem_address", "read_memt_address", "write_memt_address"] {
                for bytes in [Val::I128(4), Val::I64(4), Val::Bits(B64::new(4, 8))] {
                    let ctx = Context::new(Config::new());
                    let mut solver = Solver::<B64>::new(&ctx);
                    let address = solver.declare_const(smtlib::Ty::BitVec(64), info());
                    solver.add(Def::Assert(smtlib::Exp::Bvult(
                        Box::new(smtlib::Exp::Var(address)),
                        Box::new(smtlib::bits64(8, 64)),
                    )));
                    let mut frame = make_frame(vec![Instr::End]);
                    frame.memory_mut().add_excluded_region(8..16);
                    let index = if matches!(op, "read_memt_address" | "write_memt_address") { 1 } else { 2 };
                    let mut operands = vec![Val::Unit; index + 2];
                    operands[index] = Val::Symbolic(address);
                    operands[index + 1] = bytes.clone();
                    let state =
                        TaskState::new().with_execution_limits(ExecutionLimits::default().with_max_forks_per_path(1));
                    let queue = Worker::new_lifo();
                    let mut fraction = Fraction::one();
                    assert!(symbolic_length::retry_symbolic_length(
                        ExecError::SymbolicLength(op, info()),
                        &operands,
                        TaskId::fresh(),
                        &mut fraction,
                        None,
                        &SingleForkSink { queue: &queue },
                        &mut frame,
                        &state,
                        &mut solver,
                    )
                    .unwrap());
                    let child = queue.pop().expect("合法与排除子域必须一次拆开");
                    assert!(queue.is_empty(), "不得逐个枚举地址");
                    let Some((Def::Assert(excluded), _)) = child.fork_cond else {
                        panic!("排除路径必须携带分叉谓词")
                    };
                    let mut replay = Solver::from_checkpoint(&ctx, child.checkpoint);
                    replay.add(Def::Assert(excluded));
                    for candidate in 0..8 {
                        let equal = smtlib::Exp::Eq(
                            Box::new(smtlib::Exp::Var(address)),
                            Box::new(smtlib::bits64(candidate, 64)),
                        );
                        assert_eq!(
                            solver.check_sat_with(&equal, info()).is_sat().unwrap(),
                            candidate <= 4,
                            "{op}，{bytes:?} 必须保留每个合法地址"
                        );
                        assert_eq!(
                            replay.check_sat_with(&equal, info()).is_sat().unwrap(),
                            candidate > 4,
                            "{op}，{bytes:?} 的剩余路径只能包含跨入排除区域的地址"
                        );
                    }
                }
            }
        }

        #[test]
        fn 窄地址重试必须用扩展位宽比较区域上界() {
            for op in ["read_mem_address", "write_mem_address", "read_memt_address", "write_memt_address"] {
                let ctx = Context::new(Config::new());
                let mut solver = Solver::<B64>::new(&ctx);
                let address = solver.declare_const(smtlib::Ty::BitVec(8), info());
                let mut frame = make_frame(vec![Instr::End]);
                frame.memory_mut().add_concrete_region(1..256, HashMap::new());
                let index = if matches!(op, "read_memt_address" | "write_memt_address") { 1 } else { 2 };
                let mut operands = vec![Val::Unit; index + 2];
                operands[index] = Val::Symbolic(address);
                operands[index + 1] = Val::I128(1);
                let state = TaskState::new();
                let queue = Worker::new_lifo();
                let mut fraction = Fraction::one();
                assert!(symbolic_length::retry_symbolic_length(
                    ExecError::SymbolicLength(op, info()),
                    &operands,
                    TaskId::fresh(),
                    &mut fraction,
                    None,
                    &SingleForkSink { queue: &queue },
                    &mut frame,
                    &state,
                    &mut solver,
                )
                .unwrap());
                let child = queue.pop().expect("地址零必须留在区域外路径");
                assert!(queue.is_empty());
                let Some((Def::Assert(outside), _)) = child.fork_cond else {
                    panic!("区域外路径必须携带分叉谓词")
                };
                let mut replay = Solver::from_checkpoint(&ctx, child.checkpoint);
                replay.add(Def::Assert(outside));
                for candidate in 0..256 {
                    let equal =
                        smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(address)), Box::new(smtlib::bits64(candidate, 8)));
                    assert_eq!(solver.check_sat_with(&equal, info()).is_sat().unwrap(), candidate != 0);
                    assert_eq!(replay.check_sat_with(&equal, info()).is_sat().unwrap(), candidate == 0);
                }
            }
        }

        #[test]
        fn 窄地址覆盖整个地址域时不能绕过具体区域() {
            let mut observations = Vec::new();
            for enabled in [false, true] {
                let shared = empty_shared_state();
                let cond = test_name(580);
                let address = test_name(581);
                let mut frame = make_frame(vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(address, Ty::Bits(8), info()),
                    Instr::Jump(Exp::Id(cond), 5, info()),
                    Instr::Copy(Loc::Id(address), Exp::Bits(B64::new(1, 8)), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(address), Exp::Bits(B64::new(2, 8)), info()),
                    Instr::PrimopVariadic(
                        Loc::Id(RETURN),
                        primop::variadic_primops()["read_mem"],
                        vec![Exp::Unit, Exp::I128(8), Exp::Id(address), Exp::I128(1)],
                        info(),
                    ),
                    Instr::End,
                ]);
                frame.memory_mut().add_concrete_region(0..256, HashMap::from([(1, 42), (2, 42)]));
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let out = Mutex::new(Vec::new());
                start_single(
                    frame.task(TaskId::fresh(), &state),
                    &shared,
                    &out,
                    &|_, _, result, _, mut solver, out| {
                        let Ok((Run::Finished(value), _)) = result else { panic!("合法读必须完成") };
                        let wrong = primop::eq_anything(value, Val::Bits(B64::new(0, 8)), &mut solver, info()).unwrap();
                        let possible_zero = solver
                            .check_sat_with(&crate::primop_util::smt_value(&wrong, info()).unwrap(), info())
                            .is_sat()
                            .unwrap();
                        out.lock().unwrap().push(possible_zero);
                    },
                );
                let results = out.into_inner().unwrap();
                eprintln!("窄地址：合并={enabled}，允许错误值={results:?}");
                observations.push((enabled, results));
            }
            eprintln!("窄地址具体内存：{observations:?}");
            assert!(
                observations.iter().all(|(_, wrong)| wrong.iter().all(|value| !value)),
                "内存只能返回 42，但合并后允许返回 0"
            );
        }

        #[test]
        fn 排除区域之前的合法跨界候选必须保留() {
            let mut observations = Vec::new();
            for enabled in [false, true] {
                for op in [
                    "read_mem",
                    "read_mem_exclusive",
                    "read_mem_ifetch",
                    "platform_read_memt",
                    "write_mem",
                    "write_mem_exclusive",
                    "platform_write_memt",
                ] {
                    let shared = empty_shared_state();
                    let address = Exp::Call(Op::Concat, vec![Exp::Bits(B64::zeros(61)), Exp::Undefined(Ty::Bits(3))]);
                    let args = match op {
                        "platform_read_memt" => vec![Exp::Unit, address, Exp::I128(4)],
                        "platform_write_memt" => {
                            vec![Exp::Unit, address, Exp::I128(4), Exp::Bits(B64::zeros(32)), Exp::Bits(B64::zeros(1))]
                        }
                        "write_mem" | "write_mem_exclusive" => {
                            vec![Exp::Unit, Exp::I128(64), address, Exp::I128(4), Exp::Bits(B64::zeros(32))]
                        }
                        _ => vec![Exp::Unit, Exp::I128(64), address, Exp::I128(4)],
                    };
                    let mut frame = make_frame(vec![
                        Instr::PrimopVariadic(Loc::Id(RETURN), primop::variadic_primops()[op], args, info()),
                        Instr::End,
                    ]);
                    frame.memory_mut().add_excluded_region(8..16);
                    if op == "read_mem_ifetch" {
                        frame.memory_mut().add_symbolic_code_region(0..8);
                    }
                    let state =
                        TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                    let out = Mutex::new(Vec::new());
                    start_single(
                        frame.task(TaskId::fresh(), &state),
                        &shared,
                        &out,
                        &|_, _, result, _, solver, out| {
                            let ok = matches!(result, Ok((Run::Finished(_), _)));
                            let description = format!(
                                "{:?}",
                                result.map(|(run, _)| matches!(run, Run::Finished(_))).map_err(|(error, _)| error)
                            );
                            let events = solver.trace().to_vec();
                            let exclusive = events.iter().any(|event| {
                                matches!(event, Event::ReadMem{ opts, .. } if opts.is_exclusive)
                                    || matches!(event, Event::WriteMem{ opts, .. } if opts.is_exclusive())
                            });
                            out.lock().unwrap().push((ok, description, exclusive));
                        },
                    );
                    observations.push((enabled, op, out.into_inner().unwrap()));
                }
            }
            eprintln!("跨界排除区域：{observations:?}");
            assert!(
                observations.iter().all(|(_, _, results)| results.iter().any(|(ok, _, _)| *ok)),
                "地址 0..=4 的合法四字节访问全部丢失"
            );
        }

        #[test]
        fn 合并必须沿用特殊寄存器轨迹过滤() {
            let mut observations = Vec::new();
            for enabled in [false, true] {
                for name in ["_TLB", "core_TLB", "_TLB_cache", "ordinary_reg"] {
                    let mut shared = empty_shared_state();
                    let encoded = zencode::encode(name);
                    let reg = shared.symtab.intern(&encoded);
                    let cond = test_name(580);
                    let value = test_name(581);
                    let mut frame = make_frame(vec![
                        Instr::Decl(cond, Ty::Bool, info()),
                        Instr::Decl(value, Ty::Bool, info()),
                        Instr::Jump(Exp::Id(cond), 5, info()),
                        Instr::Copy(Loc::Id(value), Exp::Id(reg), info()),
                        Instr::Goto(6),
                        Instr::Copy(Loc::Id(value), Exp::Id(reg), info()),
                        Instr::Copy(Loc::Id(RETURN), Exp::Id(value), info()),
                        Instr::End,
                    ]);
                    frame.regs_mut().insert(reg, false, UVal::Init(Val::Bool(true)));
                    let state =
                        TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                    let out = Mutex::new(Vec::new());
                    start_single(
                        frame.task(TaskId::fresh(), &state),
                        &shared,
                        &out,
                        &|_, _, result, _, solver, out| {
                            assert!(matches!(result, Ok((Run::Finished(_), _))));
                            let reads = solver
                                .trace()
                                .to_vec()
                                .iter()
                                .filter(|event| matches!(event, Event::ReadReg(r, _, _) if *r == reg))
                                .count();
                            out.lock().unwrap().push(reads);
                        },
                    );
                    let counts = out.into_inner().unwrap();
                    assert_eq!(counts.len(), if enabled { 1 } else { 2 }, "开启合并时必须确实合流");
                    let expected = usize::from(!name.contains("_TLB"));
                    assert!(
                        counts.iter().all(|count| *count == expected),
                        "{name}，合并={enabled}，读取次数={counts:?}"
                    );
                    observations.push((enabled, name, counts));
                }
            }
            eprintln!("特殊寄存器轨迹：{observations:?}");
        }
    }
    mod review23_tests {
        use super::*;

        #[test]
        fn 四种地址重试必须逐区域拆分所有区域类型() {
            use crate::memory::Region;

            let regions = [
                Region::Concrete(0..1, HashMap::from([(0, 42)])),
                Region::Excluded(0..1),
                Region::Constrained(0..1, Arc::new(|solver| solver.define_bitvector(smtlib::bits64(42, 8), info()))),
                Region::Custom(0..1, Box::new(super::review15_tests::AuditDevice { value: 42 })),
                Region::SymbolicCode(0..1),
                Region::Symbolic(0..1),
            ];
            for op in ["read_mem_address", "write_mem_address", "read_memt_address", "write_memt_address"] {
                for region in &regions {
                    let ctx = Context::new(Config::new());
                    let mut solver = Solver::<B64>::new(&ctx);
                    let address = solver.declare_const(smtlib::Ty::BitVec(64), info());
                    let mut frame = make_frame(vec![Instr::End]);
                    frame.memory_mut().add_region(region.clone());
                    let index = if matches!(op, "read_memt_address" | "write_memt_address") { 1 } else { 2 };
                    let mut operands = vec![Val::Unit; index + 2];
                    operands[index] = Val::Symbolic(address);
                    operands[index + 1] = Val::I128(1);
                    let state =
                        TaskState::new().with_execution_limits(ExecutionLimits::default().with_max_forks_per_path(1));
                    let queue = Worker::new_lifo();
                    let mut fraction = Fraction::one();
                    assert!(symbolic_length::retry_symbolic_length(
                        ExecError::SymbolicLength(op, info()),
                        &operands,
                        TaskId::fresh(),
                        &mut fraction,
                        None,
                        &SingleForkSink { queue: &queue },
                        &mut frame,
                        &state,
                        &mut solver,
                    )
                    .unwrap());
                    let child = queue.pop().unwrap();
                    assert!(queue.is_empty(), "{op}，{region:?} 只应分叉一次");
                    let Some((Def::Assert(outside), _)) = child.fork_cond else {
                        panic!("{op}，{region:?} 必须保留区域外谓词")
                    };
                    let excluded = matches!(region, Region::Excluded(_));
                    assert!(
                        matches!(&outside, smtlib::Exp::Not(predicate) if
                        if excluded {
                            matches!(predicate.as_ref(), smtlib::Exp::Not(allowed) if matches!(allowed.as_ref(), smtlib::Exp::And(..)))
                        } else {
                            matches!(predicate.as_ref(), smtlib::Exp::And(..))
                        }),
                        "区域拆分必须使用完整区域谓词，不得使用地址相等谓词"
                    );
                    let mut replay = Solver::from_checkpoint(&ctx, child.checkpoint);
                    replay.add(Def::Assert(outside));
                    for (candidate, expected) in [(0, false), (1, true), ((1u64 << 32) + 1, true)] {
                        assert_eq!(
                            replay
                                .check_sat_with(
                                    &smtlib::Exp::Eq(
                                        Box::new(smtlib::Exp::Var(address)),
                                        Box::new(smtlib::bits64(candidate, 64)),
                                    ),
                                    info(),
                                )
                                .is_sat()
                                .unwrap(),
                            if excluded { !expected } else { expected },
                            "分叉路径必须保留所选子域的全部符号地址"
                        );
                    }
                }
            }
        }

        #[test]
        fn 单一区域无拆分谓词时必须明确报错而非枚举地址() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let address = solver.declare_const(smtlib::Ty::BitVec(64), info());
            solver.add(Def::Assert(smtlib::Exp::Bvult(
                Box::new(smtlib::Exp::Var(address)),
                Box::new(smtlib::bits64(16, 64)),
            )));
            let mut frame = make_frame(vec![Instr::End]);
            frame.memory_mut().add_concrete_region(0..16, HashMap::from_iter((0..16).map(|address| (address, 42))));
            let state = TaskState::new();
            let queue = Worker::new_lifo();
            let mut fraction = Fraction::one();
            let result = symbolic_length::retry_symbolic_length(
                ExecError::SymbolicLength("read_mem_address", info()),
                &[Val::Unit, Val::I128(64), Val::Symbolic(address), Val::I128(1)],
                TaskId::fresh(),
                &mut fraction,
                None,
                &SingleForkSink { queue: &queue },
                &mut frame,
                &state,
                &mut solver,
            );
            assert!(matches!(result, Err(ExecError::SymbolicLength("read_mem_address", _))));
            assert!(queue.is_empty(), "不支持的符号区域内部访问不得启动单点枚举");
        }

        #[test]
        fn 合并必须保留重复读取次数() {
            let mut observations = Vec::new();
            for enabled in [false, true] {
                let mut shared = empty_shared_state();
                let reg = shared.symtab.intern("zreview23_reg");
                let cond = test_name(580);
                let value = test_name(581);
                let mut frame = make_frame(vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(value, Ty::Bits(8), info()),
                    Instr::Jump(Exp::Id(cond), 6, info()),
                    Instr::Copy(Loc::Id(value), Exp::Id(reg), info()),
                    Instr::Copy(Loc::Id(value), Exp::Id(reg), info()),
                    Instr::Goto(8),
                    Instr::Copy(Loc::Id(value), Exp::Id(reg), info()),
                    Instr::Copy(Loc::Id(value), Exp::Id(reg), info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(value), info()),
                    Instr::End,
                ]);
                frame.regs_mut().insert(reg, false, UVal::Init(Val::Bits(B64::new(42, 8))));
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let out = Mutex::new(Vec::new());
                start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, solver, out| {
                    assert!(matches!(result, Ok((Run::Finished(_), _))));
                    let events = solver.trace().to_vec();
                    let reads =
                        events.iter().filter(|event| matches!(event, Event::ReadReg(r, _, _) if *r == reg)).count();
                    out.lock().unwrap().push(reads);
                });
                let counts = out.into_inner().unwrap();
                assert_eq!(counts.len(), if enabled { 1 } else { 2 }, "开启合并时必须确实合流");
                observations.push((enabled, counts));
            }
            eprintln!("真实重复读取次数：{observations:?}");
            assert!(observations.iter().all(|(_, counts)| counts.iter().all(|count| *count == 2)));
        }

        #[test]
        fn 合并首次读取不能增加轨迹事件() {
            let mut observations = Vec::new();
            for enabled in [false, true] {
                let mut shared = empty_shared_state();
                let reg = shared.symtab.intern("zreview23_fresh");
                let cond = test_name(580);
                let value = test_name(581);
                let mut frame = make_frame(vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(value, Ty::Bits(8), info()),
                    Instr::Jump(Exp::Id(cond), 5, info()),
                    Instr::Copy(Loc::Id(value), Exp::Id(reg), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(value), Exp::Id(reg), info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(value), info()),
                    Instr::End,
                ]);
                frame.regs_mut().insert(reg, false, UVal::Uninit(&Ty::Bits(8)));
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let out = Mutex::new(Vec::new());
                start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, solver, out| {
                    assert!(matches!(result, Ok((Run::Finished(_), _))));
                    let reads = solver
                        .trace()
                        .to_vec()
                        .iter()
                        .filter(|event| matches!(event, Event::ReadReg(r, _, _) if *r == reg))
                        .count();
                    out.lock().unwrap().push(reads);
                });
                let counts = out.into_inner().unwrap();
                assert_eq!(counts.len(), if enabled { 1 } else { 2 }, "开启合并时必须确实合流");
                observations.push((enabled, counts));
            }
            eprintln!("首次读取次数：{observations:?}");
            assert!(observations.iter().all(|(_, counts)| counts.iter().all(|count| *count == 1)));
        }

        #[test]
        fn 排除区域和符号默认区域必须按类别拆分() {
            let mut failures = Vec::new();
            for enabled in [false, true] {
                for reverse in [false, true] {
                    let shared = empty_shared_state();
                    let cond = test_name(580);
                    let address = test_name(581);
                    let outside = Exp::Call(Op::Concat, vec![Exp::Bits(B64::new(1, 32)), Exp::Undefined(Ty::Bits(32))]);
                    let excluded = Exp::Bits(B64::zeros(64));
                    let (left, right) = if reverse { (excluded, outside) } else { (outside, excluded) };
                    let mut frame = make_frame(vec![
                        Instr::Decl(cond, Ty::Bool, info()),
                        Instr::Decl(address, Ty::Bits(64), info()),
                        Instr::Jump(Exp::Id(cond), 5, info()),
                        Instr::Copy(Loc::Id(address), left, info()),
                        Instr::Goto(6),
                        Instr::Copy(Loc::Id(address), right, info()),
                        Instr::PrimopVariadic(
                            Loc::Id(RETURN),
                            primop::variadic_primops()["read_mem"],
                            vec![Exp::Unit, Exp::I128(64), Exp::Id(address), Exp::I128(1)],
                            info(),
                        ),
                        Instr::End,
                    ]);
                    frame.memory_mut().add_excluded_region(0..1);
                    let state = TaskState::new().with_execution_limits(
                        ExecutionLimits::default().with_path_merging(enabled).with_max_forks_per_path(1),
                    );
                    let out = Mutex::new(Vec::new());
                    start_single(
                        frame.task(TaskId::fresh(), &state),
                        &shared,
                        &out,
                        &|_, _, result, _, mut solver, out| {
                            let ok = matches!(result, Ok((Run::Finished(_), _)));
                            let coverage = if ok {
                                let address = solver
                                    .trace()
                                    .to_vec()
                                    .iter()
                                    .find_map(|event| match event {
                                        Event::ReadMem { address, .. } => Some(address.clone()),
                                        _ => None,
                                    })
                                    .unwrap();
                                solver
                                    .check_sat_with(
                                        &smtlib::Exp::Eq(
                                            Box::new(crate::primop_util::smt_value(&address, info()).unwrap()),
                                            Box::new(smtlib::bits64((1u64 << 32) + 1, 64)),
                                        ),
                                        info(),
                                    )
                                    .is_sat()
                                    .unwrap()
                            } else {
                                false
                            };
                            out.lock().unwrap().push((
                                format!(
                                    "{:?}",
                                    result.map(|(run, _)| matches!(run, Run::Finished(_))).map_err(|(error, _)| error)
                                ),
                                coverage,
                            ));
                        },
                    );
                    let results = out.into_inner().unwrap();
                    eprintln!("排除区域：合并={enabled}，反转={reverse}，结果={results:?}");
                    if !results.iter().any(|(_, coverage)| *coverage)
                        || results.iter().any(|(result, _)| result.contains("BranchLimitReached"))
                    {
                        failures.push((enabled, reverse));
                    }
                }
            }
            assert!(failures.is_empty(), "合法符号地址覆盖不能因枚举耗尽预算而丢失：{failures:?}");
        }

        #[test]
        fn 受约束区和符号代码区不能退回地址单点枚举() {
            let mut failures = Vec::new();
            for code in [false, true] {
                for enabled in [false, true] {
                    for reverse in [false, true] {
                        let shared = empty_shared_state();
                        let cond = test_name(580);
                        let address = test_name(581);
                        let symbolic = |upper| {
                            Exp::Call(Op::Concat, vec![Exp::Bits(B64::new(upper, 32)), Exp::Undefined(Ty::Bits(32))])
                        };
                        let inside = if code { symbolic(1) } else { Exp::Bits(B64::zeros(64)) };
                        let outside = symbolic(if code { 2 } else { 1 });
                        let (left, right) = if reverse { (inside, outside) } else { (outside, inside) };
                        let mut frame = make_frame(vec![
                            Instr::Decl(cond, Ty::Bool, info()),
                            Instr::Decl(address, Ty::Bits(64), info()),
                            Instr::Jump(Exp::Id(cond), 5, info()),
                            Instr::Copy(Loc::Id(address), left, info()),
                            Instr::Goto(6),
                            Instr::Copy(Loc::Id(address), right, info()),
                            Instr::PrimopVariadic(
                                Loc::Id(RETURN),
                                primop::variadic_primops()[if code { "read_mem_ifetch" } else { "read_mem_exclusive" }],
                                vec![Exp::Unit, Exp::I128(64), Exp::Id(address), Exp::I128(1)],
                                info(),
                            ),
                            Instr::End,
                        ]);
                        if code {
                            frame.memory_mut().add_symbolic_code_region((1u64 << 32)..(2u64 << 32));
                            frame.memory_mut().add_symbolic_code_region((2u64 << 32)..(3u64 << 32));
                        } else {
                            frame.memory_mut().add_region(crate::memory::Region::Constrained(
                                0..1,
                                Arc::new(|solver| solver.define_bitvector(smtlib::bits64(42, 8), info())),
                            ));
                        }
                        let state = TaskState::new().with_execution_limits(
                            ExecutionLimits::default().with_path_merging(enabled).with_max_forks_per_path(1),
                        );
                        let out = Mutex::new(Vec::new());
                        start_single(
                            frame.task(TaskId::fresh(), &state),
                            &shared,
                            &out,
                            &|_, _, result, _, mut solver, out| {
                                let mut coverage = [false; 2];
                                if matches!(result, Ok((Run::Finished(_), _))) {
                                    let address = solver
                                        .trace()
                                        .to_vec()
                                        .iter()
                                        .find_map(|event| match event {
                                            Event::ReadMem { address, opts, .. } => {
                                                assert_eq!(opts.is_ifetch, code);
                                                assert_eq!(opts.is_exclusive, !code);
                                                Some(address.clone())
                                            }
                                            _ => None,
                                        })
                                        .unwrap();
                                    let targets =
                                        if code { [(1u64 << 32) + 1, (2u64 << 32) + 1] } else { [0, (1u64 << 32) + 1] };
                                    for (position, target) in targets.into_iter().enumerate() {
                                        coverage[position] = solver
                                            .check_sat_with(
                                                &smtlib::Exp::Eq(
                                                    Box::new(crate::primop_util::smt_value(&address, info()).unwrap()),
                                                    Box::new(smtlib::bits64(target, 64)),
                                                ),
                                                info(),
                                            )
                                            .is_sat()
                                            .unwrap();
                                    }
                                }
                                out.lock().unwrap().push((
                                    format!(
                                        "{:?}",
                                        result
                                            .map(|(run, _)| matches!(run, Run::Finished(_)))
                                            .map_err(|(error, _)| error)
                                    ),
                                    coverage,
                                ));
                            },
                        );
                        let results = out.into_inner().unwrap();
                        eprintln!("其他区域：代码={code}，合并={enabled}，反转={reverse}，结果={results:?}");
                        if results.iter().any(|(result, _)| result.contains("BranchLimitReached"))
                            || !(0..2).all(|position| results.iter().any(|(_, coverage)| coverage[position]))
                        {
                            failures.push((code, enabled, reverse));
                        }
                    }
                }
            }
            assert!(failures.is_empty(), "区域外符号地址与其他符号代码区必须完整覆盖：{failures:?}");
        }
    }

    mod review22_tests {
        use super::*;

        #[test]
        fn 指令推进后必须清理表达式缓存() {
            let shared = empty_shared_state();
            let reg = test_name(554);
            let mut frame = make_frame(vec![
                Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
                Instr::Copy(Loc::Id(reg), Exp::Bool(false), info()),
                Instr::Jump(Exp::Id(RETURN), 0, info()),
                Instr::End,
            ]);
            frame.regs_mut().insert(reg, false, UVal::Init(Val::Bool(true)));
            let state = TaskState::new();
            let out = Mutex::new(Vec::new());
            start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, solver, out| {
                let Ok((Run::Finished(Val::Bool(value)), frame)) = result else {
                    panic!("回跳后必须读到寄存器的新值并正常结束")
                };
                assert!(!value);
                assert!(frame.local_state.expression_values.is_empty(), "指令成功后不得保留表达式缓存");
                let reads = solver
                    .trace()
                    .to_vec()
                    .iter()
                    .filter(|event| matches!(event, Event::ReadReg(r, _, _) if *r == reg))
                    .count();
                out.lock().unwrap().push(reads);
            });
            assert_eq!(out.into_inner().unwrap(), vec![2], "回跳执行相同表达式必须重新读取寄存器");
        }

        #[test]
        fn 操作数重试必须缓存已经读取的寄存器() {
            let shared = empty_shared_state();
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let index = solver.declare_const(smtlib::Ty::BitVec(128), info());
            solver.add(Def::Assert(smtlib::Exp::Bvult(
                Box::new(smtlib::Exp::Var(index)),
                Box::new(smtlib::bits64(2, 128)),
            )));
            let reg = test_name(551);
            let mut frame = make_frame(vec![Instr::End]);
            frame.regs_mut().insert(reg, true, UVal::Init(Val::Bool(true)));
            frame
                .lets_mut()
                .insert(test_name(552), UVal::Init(Val::Vector(vec![Val::List(vec![]), Val::List(vec![Val::Unit])])));
            frame.lets_mut().insert(test_name(553), UVal::Init(Val::Symbolic(index)));
            let operands =
                vec![Exp::Id(reg), Exp::Call(Op::Bvaccess, vec![Exp::Id(test_name(552)), Exp::Id(test_name(553))])];
            assert!(matches!(
                symbolic_length::eval_operands(&operands, &mut frame, &shared, &mut solver, info()),
                Err(ExecError::SymbolicLength("vector_access", _))
            ));
            solver
                .add(Def::Assert(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(index)), Box::new(smtlib::bits64(0, 128)))));
            let values = symbolic_length::eval_operands(&operands, &mut frame, &shared, &mut solver, info()).unwrap();
            assert!(matches!(values.as_slice(), [Val::Bool(true), Val::List(values)] if values.is_empty()));
            assert_eq!(
                solver
                    .trace()
                    .to_vec()
                    .iter()
                    .filter(|event| matches!(event, Event::ReadReg(r, _, _) if *r == reg))
                    .count(),
                1,
                "后续操作数重试不能重复读取前序寄存器"
            );
        }

        #[test]
        fn 嵌套重试必须保留前序寄存器读取次数() {
            let mut failures = Vec::new();
            for enabled in [false, true] {
                let mut shared = empty_shared_state();
                let cond = shared.symtab.intern("zcond22");
                let bits = shared.symtab.intern("zbits22");
                let index = shared.symtab.intern("zindex22");
                let lists = shared.symtab.intern("zlists22");
                let reg = shared.symtab.intern("zreg22");
                let mut frame = make_frame(vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(bits, Ty::Bits(8), info()),
                    Instr::Decl(index, Ty::I128, info()),
                    Instr::Jump(Exp::Id(cond), 6, info()),
                    Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(0, 8)), info()),
                    Instr::Goto(7),
                    Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(1, 8)), info()),
                    Instr::PrimopUnary(Loc::Id(index), primop::unary_primops()["sail_unsigned"], Exp::Id(bits), info()),
                    Instr::Copy(
                        Loc::Id(RETURN),
                        Exp::Call(
                            Op::And,
                            vec![
                                Exp::Id(reg),
                                Exp::Call(
                                    Op::IsEmpty,
                                    vec![Exp::Call(Op::Bvaccess, vec![Exp::Id(lists), Exp::Id(index)])],
                                ),
                            ],
                        ),
                        info(),
                    ),
                    Instr::End,
                ]);
                frame.regs_mut().insert(reg, true, UVal::Init(Val::Bool(true)));
                frame
                    .lets_mut()
                    .insert(lists, UVal::Init(Val::Vector(vec![Val::List(vec![]), Val::List(vec![Val::Unit])])));
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let out = Mutex::new(Vec::new());
                start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, solver, out| {
                    assert!(matches!(result, Ok((Run::Finished(_), _))));
                    let count = solver
                        .trace()
                        .to_vec()
                        .iter()
                        .filter(|event| matches!(event, Event::ReadReg(r, _, _) if *r == reg))
                        .count();
                    out.lock().unwrap().push(count);
                });
                let counts = out.into_inner().unwrap();
                eprintln!("合并={enabled}，各路径寄存器读取次数={counts:?}");
                if counts != vec![1, 1] {
                    failures.push((enabled, counts));
                }
            }
            assert!(failures.is_empty(), "单条表达式中的一次寄存器读取不能因重试重复：{failures:?}");
        }

        #[test]
        fn 寄存器索引必须按边界拆分而不是枚举非法值() {
            use crate::bitvector::b129::B129;
            let mut failures = Vec::new();
            for count in [1, 2] {
                for write in [false, true] {
                    for reverse in [false, true] {
                        for enabled in [false, true] {
                            let mut shared = SharedState::<B129>::empty(Symtab::new());
                            let function = shared.symtab.intern("zreview22_idx");
                            let cond = shared.symtab.intern("zcond22");
                            let index = shared.symtab.intern("zindex22");
                            let regs = [shared.symtab.intern("zr0_22"), shared.symtab.intern("zr1_22")];
                            let invalid =
                                Exp::Call(Op::Concat, vec![Exp::Bits(B64::new(1, 64)), Exp::Undefined(Ty::Bits(64))]);
                            let valid =
                                Exp::Call(Op::Concat, vec![Exp::Bits(B64::zeros(64)), Exp::Bits(B64::zeros(64))]);
                            let (left, right) = if reverse { (invalid, valid) } else { (valid, invalid) };
                            let instrs = vec![
                                Instr::Decl(cond, Ty::Bool, info()),
                                Instr::Decl(index, Ty::Bits(128), info()),
                                Instr::Jump(Exp::Id(cond), 5, info()),
                                Instr::Copy(Loc::Id(index), left, info()),
                                Instr::Goto(6),
                                Instr::Copy(Loc::Id(index), right, info()),
                                Instr::Call(
                                    Loc::Id(RETURN),
                                    false,
                                    if write { WRITE_REGISTER_FROM_VECTOR } else { READ_REGISTER_FROM_VECTOR },
                                    if write {
                                        vec![Exp::Id(index), Exp::Bits(B64::new(7, 8)), Exp::Id(test_name(550))]
                                    } else {
                                        vec![Exp::Id(index), Exp::Id(test_name(550))]
                                    },
                                    info(),
                                ),
                                Instr::End,
                            ];
                            let mut frame = LocalFrame::new(function, &[], &Ty::Bits(8), None, &instrs);
                            frame.lets_mut().insert(
                                test_name(550),
                                UVal::Init(Val::Vector(regs[..count].iter().copied().map(Val::Ref).collect())),
                            );
                            for reg in regs {
                                frame.regs_mut().insert(reg, false, UVal::Init(Val::Bits(B129::new(42, 8))));
                            }
                            let state = TaskState::new().with_execution_limits(
                                ExecutionLimits::default().with_path_merging(enabled).with_max_forks_per_path(1),
                            );
                            let out = Mutex::new(Vec::new());
                            start_single(
                                frame.task(TaskId::fresh(), &state),
                                &shared,
                                &out,
                                &|_, _, result, _, _, out| {
                                    out.lock().unwrap().push(
                                        result
                                            .map(|(run, _)| matches!(run, Run::Finished(_)))
                                            .map_err(|(error, _)| error),
                                    );
                                },
                            );
                            let results = out.into_inner().unwrap();
                            eprintln!(
                                "索引边界：数量={count}，写={write}，反转={reverse}，合并={enabled}，结果={results:?}"
                            );
                            if results.iter().any(|r| matches!(r, Err(ExecError::BranchLimitReached(..))))
                                || !results.iter().any(Result::is_ok)
                            {
                                failures.push((count, write, reverse, enabled));
                            }
                        }
                    }
                }
            }
            assert!(failures.is_empty(), "非法索引集合不应耗尽预算或丢弃合法路径：{failures:?}");
        }

        #[test]
        fn 内存区域拆分不能枚举整个符号区域() {
            let mut failures = Vec::new();
            for operation in [
                "read_mem",
                "read_mem_exclusive",
                "write_mem",
                "write_mem_exclusive",
                "platform_read_memt",
                "platform_write_memt",
            ] {
                for reverse in [false, true] {
                    for enabled in [false, true] {
                        let mut shared = empty_shared_state();
                        let cond = shared.symtab.intern("zcond22");
                        let address = shared.symtab.intern("zaddress22");
                        let symbolic =
                            Exp::Call(Op::Concat, vec![Exp::Bits(B64::new(1, 32)), Exp::Undefined(Ty::Bits(32))]);
                        let concrete = Exp::Bits(B64::zeros(64));
                        let (left, right) = if reverse { (symbolic, concrete) } else { (concrete, symbolic) };
                        let instrs = vec![
                            Instr::Decl(cond, Ty::Bool, info()),
                            Instr::Decl(address, Ty::Bits(64), info()),
                            Instr::Jump(Exp::Id(cond), 5, info()),
                            Instr::Copy(Loc::Id(address), left, info()),
                            Instr::Goto(6),
                            Instr::Copy(Loc::Id(address), right, info()),
                            Instr::PrimopVariadic(
                                Loc::Id(RETURN),
                                primop::variadic_primops()[operation],
                                if operation == "platform_read_memt" {
                                    vec![Exp::Unit, Exp::Id(address), Exp::I128(1)]
                                } else if operation == "platform_write_memt" {
                                    vec![
                                        Exp::Unit,
                                        Exp::Id(address),
                                        Exp::I128(1),
                                        Exp::Bits(B64::new(7, 8)),
                                        Exp::Bits(B64::zeros(1)),
                                    ]
                                } else if operation.starts_with("write") {
                                    vec![
                                        Exp::Unit,
                                        Exp::I128(64),
                                        Exp::Id(address),
                                        Exp::I128(1),
                                        Exp::Bits(B64::new(7, 8)),
                                    ]
                                } else {
                                    vec![Exp::Unit, Exp::I128(64), Exp::Id(address), Exp::I128(1)]
                                },
                                info(),
                            ),
                            Instr::End,
                        ];
                        let mut frame = make_frame(instrs);
                        frame.memory_mut().add_concrete_region(0..1, HashMap::from_iter([(0, 42)]));
                        let state = TaskState::new().with_execution_limits(
                            ExecutionLimits::default().with_path_merging(enabled).with_max_forks_per_path(1),
                        );
                        let out = Mutex::new(Vec::new());
                        start_single(
                            frame.task(TaskId::fresh(), &state),
                            &shared,
                            &out,
                            &|_, _, result, _, mut solver, out| {
                                let address = solver.trace().to_vec().iter().find_map(|event| match event {
                                    Event::ReadMem { address, .. } | Event::WriteMem { address, .. } => {
                                        Some(address.clone())
                                    }
                                    _ => None,
                                });
                                let mut coverage = [false, false];
                                if let Some(address) = address {
                                    for (position, target) in [0, (1u64 << 32) + 1].into_iter().enumerate() {
                                        let condition = smtlib::Exp::Eq(
                                            Box::new(crate::primop_util::smt_value(&address, info()).unwrap()),
                                            Box::new(smtlib::bits64(target, 64)),
                                        );
                                        coverage[position] =
                                            solver.check_sat_with(&condition, info()).is_sat().unwrap();
                                    }
                                }
                                out.lock().unwrap().push((
                                    result.map(|(run, _)| matches!(run, Run::Finished(_))).map_err(|(error, _)| error),
                                    coverage,
                                ));
                            },
                        );
                        let results = out.into_inner().unwrap();
                        eprintln!("内存区域：操作={operation}，反转={reverse}，合并={enabled}，结果={results:?}");
                        if !results.iter().all(|(result, _)| result.is_ok())
                            || !(0..2).all(|position| {
                                results.iter().any(|(result, coverage)| result.is_ok() && coverage[position])
                            })
                        {
                            failures.push((operation, reverse, enabled));
                        }
                    }
                }
            }
            assert!(failures.is_empty(), "两个地址类别均应保留为合法路径：{failures:?}");
        }
    }

    mod review21_tests {
        use super::*;
        use crate::bitvector::b129::B129;

        #[test]
        fn 机器整数转换的具体符号边界一致() {
            for width in [1, 63, 64, 65, 127, 128, 129] {
                let ctx = Context::new(Config::new());
                let mut solver = Solver::<B129>::new(&ctx);
                // 显式列出边界预期，避免用被测的截断和扩展算法推导预期结果。
                let unsigned_ones = if width < 64 {
                    Some(((1u64 << width) - 1) as i64)
                } else if width == 64 {
                    Some(-1)
                } else {
                    None
                };
                let mut cases = vec![
                    (B129::new(0, width), Some(0), Some(0)),
                    (B129::new(1, width), Some(1), Some(if width == 1 { -1 } else { 1 })),
                    (B129::ones(width), unsigned_ones, Some(-1)),
                ];
                if width >= 64 {
                    cases.extend([
                        (B129::new(i64::MAX as u64, 64).zero_extend(width), Some(i64::MAX), Some(i64::MAX)),
                        (
                            B129::new(1 << 63, 64).zero_extend(width),
                            Some(i64::MIN),
                            if width == 64 { Some(i64::MIN) } else { None },
                        ),
                        (
                            B129::new(1 << 63, 64).sign_extend(width),
                            if width == 64 { Some(i64::MIN) } else { None },
                            Some(i64::MIN),
                        ),
                        (B129::ones(64).zero_extend(width), Some(-1), if width == 64 { Some(-1) } else { None }),
                    ]);
                }
                if width > 64 {
                    cases.push((B129::BIT_ONE.zero_extend(width) << B129::new(64, width), None, None));
                    // -2^63 - 1：低 64 位为正数，高位为 1，不是合法的符号扩展。
                    cases.push((!B129::new(1 << 63, 64).zero_extend(width), None, None));
                }
                for (bits, unsigned_expected, signed_expected) in cases {
                    for signed in [false, true] {
                        let op = if signed { primop::op_signed::<B129> } else { primop::op_unsigned::<B129> };
                        let expected = if signed { signed_expected } else { unsigned_expected };
                        let concrete = op(Val::Bits(bits), &mut solver, info());
                        let sym = solver
                            .define_bitvector(crate::primop_util::smt_value(&Val::Bits(bits), info()).unwrap(), info());
                        let symbolic = op(Val::Symbolic(sym), &mut solver, info());
                        let Some(expected) = expected else {
                            assert!(matches!(concrete, Err(ExecError::Overflow)), "{bits:?}，有符号={signed}");
                            assert!(matches!(symbolic, Err(ExecError::Overflow)), "{bits:?}，有符号={signed}");
                            continue;
                        };
                        assert_eq!(concrete.unwrap(), Val::I64(expected));
                        let symbolic = symbolic.unwrap();
                        let Val::Symbolic(result) = symbolic else { panic!("必须返回符号机器整数") };
                        assert_eq!(solver.length(result), Some(64));
                        assert!(solver.check_sat(info()).is_sat().unwrap());
                        assert_eq!(
                            Model::new(&solver).get_val(&symbolic).unwrap(),
                            Val::Bits(B129::new(expected as u64, 64)),
                            "{bits:?}，有符号={signed}"
                        );
                    }
                }
            }
        }

        #[test]
        fn 具体寄存器索引完整校验且错误无副作用() {
            for count in [0, 1, 2] {
                for write in [false, true] {
                    let ctx = Context::new(Config::new());
                    let mut solver = Solver::<B129>::new(&ctx);
                    let mut shared = SharedState::<B129>::empty(Symtab::new());
                    let f = shared.symtab.intern("zreview21_indices");
                    let regs = [shared.symtab.intern("zr0"), shared.symtab.intern("zr1")];
                    let instrs = Box::leak(vec![Instr::End].into_boxed_slice());
                    let mut frame = LocalFrame::new(f, &[], &Ty::Unit, None, instrs);
                    let mut indices = vec![Val::I64(-1), Val::I128(-1), Val::I64(i64::MAX), Val::I128(i128::MAX)];
                    for index in [0, 1, 2] {
                        indices.extend([Val::I64(index), Val::I128(i128::from(index))]);
                        for width in [8, 64, 65, 128, 129] {
                            indices.push(Val::Bits(B129::new(index as u64, width)));
                        }
                    }
                    for width in [65, 128, 129] {
                        indices.push(Val::Bits(
                            B129::BIT_ONE.zero_extend(width) << B129::new(u64::from(width - 1), width),
                        ));
                        indices.push(Val::Bits(B129::ones(width)));
                    }
                    indices.push(Val::I128(1i128 << 64));
                    for index in indices {
                        for reg in regs {
                            frame.regs_mut().insert(reg, false, UVal::Init(Val::Bits(B129::new(42, 8))));
                        }
                        let valid = match index {
                            Val::I64(n) => n >= 0 && n < count as i64,
                            Val::I128(n) => n >= 0 && n < count as i128,
                            Val::Bits(bits) => {
                                bits.leading_zeros() == bits.len()
                                    || (bits.len() - bits.leading_zeros() <= 64 && bits.lower_u64() < count as u64)
                            }
                            _ => unreachable!(),
                        } && count > 0;
                        let refs = Val::Vector(regs[..count].iter().copied().map(Val::Ref).collect());
                        let events_before = solver.trace().to_vec().len();
                        let result = if write {
                            write_register_from_vector(
                                index.clone(),
                                Val::Bits(B129::new(7, 8)),
                                refs,
                                &mut frame.local_state,
                                &shared,
                                &mut solver,
                                info(),
                            )
                        } else {
                            read_register_from_vector(
                                index.clone(),
                                refs,
                                &mut frame.local_state,
                                &shared,
                                &mut solver,
                                info(),
                            )
                            .map(|value| assert_eq!(value, Val::Bits(B129::new(42, 8))))
                        };
                        if valid {
                            result.unwrap();
                        } else {
                            assert!(matches!(result, Err(ExecError::Type(..))), "数量={count}，索引={index:?}");
                        }
                        let events = solver.trace().to_vec();
                        assert_eq!(events.len() - events_before, usize::from(valid));
                        for (position, reg) in regs.iter().enumerate() {
                            let selected = match index {
                                Val::I64(n) => n == position as i64,
                                Val::I128(n) => n == position as i128,
                                Val::Bits(bits) => bits.lower_u64() == position as u64,
                                _ => unreachable!(),
                            };
                            assert_eq!(
                                frame.regs().get_last_if_initialized(*reg).unwrap(),
                                &Val::Bits(B129::new(if valid && write && selected { 7 } else { 42 }, 8)),
                            );
                        }
                    }
                }
            }
        }

        #[test]
        fn review21_symbolic_unsigned_overflow() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let mut accepted = Vec::new();
            for width in [128, 129] {
                let value = Val::Bits(B129::ones(width));
                assert!(matches!(primop::op_unsigned(value.clone(), &mut solver, info()), Err(ExecError::Overflow)));
                let sym = solver.define_bitvector(crate::primop_util::smt_value(&value, info()).unwrap(), info());
                let result = primop::op_unsigned(Val::Symbolic(sym), &mut solver, info());
                if let Ok(value) = &result {
                    assert!(solver.check_sat(info()).is_sat().unwrap());
                    let actual = Model::new(&solver).get_val(value).unwrap();
                    eprintln!("无符号溢出值宽度={width}，物化结果={actual:?}");
                    accepted.push(width);
                }
                assert!(matches!(result, Err(ExecError::Overflow)), "宽度={width}，结果={result:?}");
            }
            assert!(accepted.is_empty(), "接受了溢出的符号输入：{accepted:?}");
        }

        #[test]
        fn review21_symbolic_signed_overflow() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let value = Val::Bits(B129::BIT_ONE.zero_extend(129) << B129::new(128, 129));
            assert!(matches!(primop::op_signed(value.clone(), &mut solver, info()), Err(ExecError::Overflow)));
            let sym = solver.define_bitvector(crate::primop_util::smt_value(&value, info()).unwrap(), info());
            let result = primop::op_signed(Val::Symbolic(sym), &mut solver, info());
            if let Ok(value) = &result {
                assert!(solver.check_sat(info()).is_sat().unwrap());
                let actual = Model::new(&solver).get_val(value).unwrap();
                eprintln!("有符号129位最高位为1、其余为0，物化结果={actual:?}");
            }
            assert!(matches!(result, Err(ExecError::Overflow)), "结果={result:?}");
        }

        #[test]
        fn review21_merged_overflow_path() {
            for width in [65, 128, 129] {
                for signed in [false, true] {
                    for merge in [false, true] {
                        let mut shared = SharedState::<B129>::empty(Symtab::new());
                        let f = shared.symtab.intern("zreview21");
                        let cond = shared.symtab.intern("zcond");
                        let bits = shared.symtab.intern("zbits");
                        let left = shared.symtab.intern("zleft");
                        let right = shared.symtab.intern("zright");
                        let op = if signed { Op::Signed(width) } else { Op::Unsigned(width) };
                        let instrs = Box::leak(
                            vec![
                                Instr::Decl(cond, Ty::Bool, info()),
                                Instr::Decl(bits, Ty::Bits(width), info()),
                                Instr::Jump(Exp::Id(cond), 5, info()),
                                Instr::Copy(Loc::Id(bits), Exp::Id(left), info()),
                                Instr::Goto(6),
                                Instr::Copy(Loc::Id(bits), Exp::Id(right), info()),
                                Instr::Copy(Loc::Id(RETURN), Exp::Call(op, vec![Exp::Id(bits)]), info()),
                                Instr::End,
                            ]
                            .into_boxed_slice(),
                        );
                        let mut frame = LocalFrame::new(f, &[], &Ty::I64, None, instrs);
                        frame.lets_mut().insert(left, UVal::Init(Val::Bits(B129::new(1, width))));
                        let overflow = if signed {
                            B129::BIT_ONE.zero_extend(width) << B129::new(63, width)
                        } else {
                            B129::ones(width)
                        };
                        frame.lets_mut().insert(right, UVal::Init(Val::Bits(overflow)));
                        let state =
                            TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(merge));
                        let out = Mutex::new(Vec::new());
                        start_single(
                            frame.task(TaskId::fresh(), &state),
                            &shared,
                            &out,
                            &|_, _, result, _, mut solver, out| {
                                let result = match result {
                                    Ok((Run::Finished(value), _)) => {
                                        match value {
                                            Val::I64(n) => assert_eq!(n, 1),
                                            Val::Symbolic(sym) => assert_eq!(solver.length(sym), Some(64)),
                                            _ => panic!("机器整数类型错误：{value:?}"),
                                        }
                                        assert!(solver.check_sat(info()).is_sat().unwrap());
                                        let materialized = Model::new(&solver).get_val(&value).unwrap();
                                        assert!(
                                            matches!(materialized, Val::I64(1))
                                                || materialized == Val::Bits(B129::new(1, 64))
                                        );
                                        Ok(())
                                    }
                                    Err((error, _)) => Err(error),
                                    Ok(_) => panic!("执行未完成"),
                                };
                                out.lock().unwrap().push(result);
                            },
                        );
                        let results = out.into_inner().unwrap();
                        assert_eq!(results.len(), 2, "宽度={width}，有符号={signed}，合并={merge}，结果={results:?}");
                        assert_eq!(results.iter().filter(|result| result.is_ok()).count(), 1, "{results:?}");
                        assert_eq!(
                            results.iter().filter(|result| matches!(result, Err(ExecError::Overflow))).count(),
                            1,
                            "宽度={width}，有符号={signed}，合并={merge}，结果={results:?}"
                        );
                    }
                }
            }
        }

        #[test]
        fn review21_concrete_register_index_out_of_bounds() {
            let mut bad = Vec::new();
            for write in [false, true] {
                let ctx = Context::new(Config::new());
                let mut solver = Solver::<B64>::new(&ctx);
                let mut shared = empty_shared_state();
                let regs = [shared.symtab.intern("zr0"), shared.symtab.intern("zr1")];
                let mut frame = make_frame(vec![Instr::End]);
                for reg in regs {
                    frame.regs_mut().insert(reg, false, UVal::Init(Val::Bits(B64::new(42, 8))));
                }
                let refs = Val::Vector(regs.into_iter().map(Val::Ref).collect());
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    if write {
                        write_register_from_vector(
                            Val::I64(2),
                            Val::Bits(B64::new(7, 8)),
                            refs,
                            &mut frame.local_state,
                            &shared,
                            &mut solver,
                            info(),
                        )
                    } else {
                        read_register_from_vector(
                            Val::I64(2),
                            refs,
                            &mut frame.local_state,
                            &shared,
                            &mut solver,
                            info(),
                        )
                        .map(|_| ())
                    }
                }));
                if !matches!(result, Ok(Err(ExecError::Type(..)))) {
                    eprintln!("具体索引2越界，写入={write}，发生panic={}", result.is_err());
                    bad.push(write);
                }
            }
            assert!(bad.is_empty(), "越界未返回Type：{bad:?}");
        }

        #[test]
        fn review21_wide_concrete_register_index() {
            let mut bad = Vec::new();
            for write in [false, true] {
                let ctx = Context::new(Config::new());
                let mut solver = Solver::<B129>::new(&ctx);
                let mut shared = SharedState::<B129>::empty(Symtab::new());
                let f = shared.symtab.intern("zreview21");
                let regs = [shared.symtab.intern("zr0"), shared.symtab.intern("zr1")];
                let instrs = Box::leak(vec![Instr::End].into_boxed_slice());
                let mut frame = LocalFrame::new(f, &[], &Ty::Unit, None, instrs);
                for reg in regs {
                    frame.regs_mut().insert(reg, false, UVal::Init(Val::Bits(B129::new(42, 8))));
                }
                let refs = Val::Vector(regs.into_iter().map(Val::Ref).collect());
                let index = Val::Bits(B129::BIT_ONE.zero_extend(65) << B129::new(64, 65));
                let result = if write {
                    write_register_from_vector(
                        index,
                        Val::Bits(B129::new(7, 8)),
                        refs,
                        &mut frame.local_state,
                        &shared,
                        &mut solver,
                        info(),
                    )
                } else {
                    read_register_from_vector(index, refs, &mut frame.local_state, &shared, &mut solver, info())
                        .map(|_| ())
                };
                eprintln!("具体65位索引2^64，写入={write}，结果={result:?}");
                if write {
                    eprintln!("错误写入后的r0={:?}", frame.regs().get_last_if_initialized(regs[0]));
                }
                if !matches!(result, Err(ExecError::Type(..))) {
                    bad.push(write);
                }
            }
            assert!(bad.is_empty(), "宽索引高位被丢弃：{bad:?}");
        }

        #[test]
        fn review21_wide_conversion_equality() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            for width in [65, 128, 129] {
                let value = primop::op_unsigned(Val::Bits(B129::new(1, width)), &mut solver, info()).unwrap();
                let actual = primop::op_eq(value, Val::I64(1), &mut solver, info()).unwrap();
                assert_eq!(actual, Val::Bool(true), "宽度={width}，整数1与机器整数1应相等");
            }
        }

        #[test]
        fn review21_free_multi_register_index() {
            let mut shared = empty_shared_state();
            let f = shared.symtab.intern("zreview21_free");
            let index = shared.symtab.intern("zindex");
            let refs = shared.symtab.intern("zrefs");
            let regs = [shared.symtab.intern("zr0"), shared.symtab.intern("zr1")];
            let instrs = Box::leak(
                vec![
                    Instr::Decl(index, Ty::Bits(128), info()),
                    Instr::Call(
                        Loc::Id(RETURN),
                        false,
                        READ_REGISTER_FROM_VECTOR,
                        vec![Exp::Id(index), Exp::Id(refs)],
                        info(),
                    ),
                    Instr::End,
                ]
                .into_boxed_slice(),
            );
            let mut frame = LocalFrame::new(f, &[], &Ty::Bits(8), None, instrs);
            for reg in regs {
                frame.regs_mut().insert(reg, false, UVal::Init(Val::Bits(B64::new(42, 8))));
            }
            frame.lets_mut().insert(refs, UVal::Init(Val::Vector(regs.into_iter().map(Val::Ref).collect())));
            let state = TaskState::new()
                .with_execution_limits(ExecutionLimits::default().with_path_merging(true).with_max_forks_per_path(32));
            let out = Mutex::new(Vec::new());
            start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, _, out| {
                out.lock()
                    .unwrap()
                    .push(result.map(|(run, _)| matches!(run, Run::Finished(_))).map_err(|(error, _)| error));
            });
            let results = out.into_inner().unwrap();
            eprintln!("自由128位索引两元素寄存器向量：{results:?}");
            assert!(results.iter().any(Result::is_ok), "必须找到合法索引路径");
            assert!(
                !results.iter().any(|result| matches!(result, Err(ExecError::BranchLimitReached(..)))),
                "合法有限索引不应在非法值上耗尽分叉预算"
            );
        }

        #[test]
        fn review21_wide_conversion_consumer() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            for width in [1, 63, 64, 65, 128, 129] {
                for signed in [false, true] {
                    let sym = solver.define_bitvector(primop::smt_zeros(i128::from(width)), info());
                    let value = if signed {
                        primop::op_signed(Val::Symbolic(sym), &mut solver, info())
                    } else {
                        primop::op_unsigned(Val::Symbolic(sym), &mut solver, info())
                    }
                    .unwrap();
                    let Val::Symbolic(result) = value else { panic!("转换必须返回符号机器整数") };
                    assert_eq!(solver.length(result), Some(64));
                    let add = primop::op_add(value.clone(), Val::I64(1), &mut solver, info()).unwrap();
                    let sub = primop::op_sub(value.clone(), Val::I64(1), &mut solver, info()).unwrap();
                    let lt = primop::op_lt(value.clone(), Val::I64(1), &mut solver, info()).unwrap();
                    let eq = primop::op_eq(value, Val::I64(0), &mut solver, info()).unwrap();
                    assert!(solver.check_sat(info()).is_sat().unwrap());
                    let mut model = Model::new(&solver);
                    assert_eq!(model.get_val(&add).unwrap(), Val::Bits(B129::new(1, 64)));
                    assert_eq!(model.get_val(&sub).unwrap(), Val::Bits(B129::ones(64)));
                    assert_eq!(model.get_val(&lt).unwrap(), Val::Bool(true));
                    assert_eq!(model.get_val(&eq).unwrap(), Val::Bool(true));
                }
            }
        }
    }

    mod review20_tests {
        use super::*;
        use crate::bitvector::b129::B129;

        fn execute<B: BV>(
            frame: LocalFrame<'static, B>,
            shared: SharedState<'static, B>,
            merge: bool,
        ) -> Vec<Result<Val<B>, ExecError>> {
            let state = TaskState::new()
                .with_execution_limits(ExecutionLimits::default().with_path_merging(merge).with_max_forks_per_path(32));
            let out = Mutex::new(Vec::new());
            start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, mut solver, out| {
                let result = match result {
                    Ok((Run::Finished(value), _)) => {
                        assert!(solver.check_sat(info()).is_sat().unwrap());
                        Ok(Model::new(&solver).get_val(&value).unwrap())
                    }
                    Err((error, _)) => Err(error),
                    Ok(_) => panic!("执行未完成"),
                };
                out.lock().unwrap().push(result);
            });
            out.into_inner().unwrap()
        }

        fn wide_conversion(merge: bool, signed: bool, width: u32) -> Vec<Result<Val<B129>, ExecError>> {
            let mut shared = SharedState::<B129>::empty(Symtab::new());
            let f = shared.symtab.intern("ztest");
            let branch = shared.symtab.intern("zbranch");
            let bits = shared.symtab.intern("zbits");
            let a = shared.symtab.intern("za");
            let b = shared.symtab.intern("zb");
            let info = SourceLoc::unknown();
            let op = if signed { Op::Signed(width) } else { Op::Unsigned(width) };
            let instrs = Box::leak(
                vec![
                    Instr::Decl(branch, Ty::Bool, info),
                    Instr::Decl(bits, Ty::Bits(width), info),
                    Instr::Jump(Exp::Id(branch), 5, info),
                    Instr::Copy(Loc::Id(bits), Exp::Id(a), info),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(bits), Exp::Id(b), info),
                    Instr::Copy(Loc::Id(RETURN), Exp::Call(op, vec![Exp::Id(bits)]), info),
                    Instr::End,
                ]
                .into_boxed_slice(),
            );
            let mut frame = LocalFrame::new(f, &[], &Ty::I64, None, instrs);
            frame.lets_mut().insert(a, UVal::Init(Val::Bits(B129::new(1, width))));
            frame.lets_mut().insert(b, UVal::Init(Val::Bits(B129::new(2, width))));
            execute(frame, shared, merge)
        }

        fn register_vector(merge: bool, count: usize, write: bool) -> Vec<Result<Val<B64>, ExecError>> {
            let mut shared = SharedState::<B64>::empty(Symtab::new());
            let f = shared.symtab.intern("ztest");
            let branch = shared.symtab.intern("zbranch");
            let index = shared.symtab.intern("zindex");
            let refs = shared.symtab.intern("zrefs");
            let info = SourceLoc::unknown();
            let regs: Vec<_> =
                (0..count).map(|i| shared.symtab.intern(Box::leak(format!("zreg{i}").into_boxed_str()))).collect();
            let instrs = Box::leak(
                vec![
                    Instr::Decl(branch, Ty::Bool, info),
                    Instr::Decl(index, Ty::Bits(8), info),
                    Instr::Jump(Exp::Id(branch), 5, info),
                    Instr::Copy(Loc::Id(index), Exp::Bits(B64::new(0, 8)), info),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(index), Exp::Bits(B64::new(count as u64, 8)), info),
                    Instr::Call(
                        Loc::Id(RETURN),
                        false,
                        if write {
                            crate::ir::WRITE_REGISTER_FROM_VECTOR
                        } else {
                            crate::ir::READ_REGISTER_FROM_VECTOR
                        },
                        if write {
                            vec![Exp::Id(index), Exp::Bits(B64::new(7, 8)), Exp::Id(refs)]
                        } else {
                            vec![Exp::Id(index), Exp::Id(refs)]
                        },
                        info,
                    ),
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(regs[0]), info),
                    Instr::End,
                ]
                .into_boxed_slice(),
            );
            let mut frame = LocalFrame::new(f, &[], &Ty::Bits(8), None, instrs);
            for (i, reg) in regs.iter().enumerate() {
                frame.regs_mut().insert(*reg, false, UVal::Init(Val::Bits(B64::new(42 + i as u64, 8))));
            }
            frame.lets_mut().insert(refs, UVal::Init(Val::Vector(regs.into_iter().map(Val::Ref).collect())));
            execute(frame, shared, merge)
        }

        fn singleton_free(width: u32, write: bool) -> Vec<Result<Val<B64>, ExecError>> {
            let mut shared = SharedState::<B64>::empty(Symtab::new());
            let f = shared.symtab.intern("ztest");
            let index = shared.symtab.intern("zindex");
            let refs = shared.symtab.intern("zrefs");
            let reg = shared.symtab.intern("zreg");
            let info = SourceLoc::unknown();
            let instrs = Box::leak(
                vec![
                    Instr::Decl(index, Ty::Bits(width), info),
                    Instr::Call(
                        Loc::Id(RETURN),
                        false,
                        if write { WRITE_REGISTER_FROM_VECTOR } else { READ_REGISTER_FROM_VECTOR },
                        if write {
                            vec![Exp::Id(index), Exp::Bits(B64::new(7, 8)), Exp::Id(refs)]
                        } else {
                            vec![Exp::Id(index), Exp::Id(refs)]
                        },
                        info,
                    ),
                    Instr::End,
                ]
                .into_boxed_slice(),
            );
            let mut frame = LocalFrame::new(f, &[], &Ty::Bits(8), None, instrs);
            frame.regs_mut().insert(reg, false, UVal::Init(Val::Bits(B64::new(42, 8))));
            frame.lets_mut().insert(refs, UVal::Init(Val::Vector(vec![Val::Ref(reg)])));
            execute(frame, shared, true)
        }

        fn wide_monomorphize(merge: bool, width: u32) -> Vec<Result<Val<B129>, ExecError>> {
            let mut shared = SharedState::<B129>::empty(Symtab::new());
            let f = shared.symtab.intern("ztest");
            let branch = shared.symtab.intern("zbranch");
            let bits = shared.symtab.intern("zbits");
            let a = shared.symtab.intern("za");
            let b = shared.symtab.intern("zb");
            let info = SourceLoc::unknown();
            let instrs = Box::leak(
                vec![
                    Instr::Decl(branch, Ty::Bool, info),
                    Instr::Decl(bits, Ty::AnyBits, info),
                    Instr::Jump(Exp::Id(branch), 5, info),
                    Instr::Copy(Loc::Id(bits), Exp::Id(a), info),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(bits), Exp::Id(b), info),
                    Instr::Monomorphize(bits, Ty::AnyBits, info),
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(bits), info),
                    Instr::End,
                ]
                .into_boxed_slice(),
            );
            let mut frame = LocalFrame::new(f, &[], &Ty::AnyBits, None, instrs);
            frame.lets_mut().insert(a, UVal::Init(Val::Bits(B129::new(1, width))));
            frame.lets_mut().insert(b, UVal::Init(Val::Bits(B129::ones(width))));
            execute(frame, shared, merge)
        }

        #[test]
        fn 宽位转换在合并前后保留数值() {
            for width in [64, 65, 128, 129] {
                for signed in [false, true] {
                    for merge in [false, true] {
                        let results = wide_conversion(merge, signed, width);
                        assert_eq!(results.len(), if merge { 1 } else { 2 });
                        for result in results {
                            let value = match result.unwrap() {
                                Val::I64(value) => i128::from(value),
                                Val::Bits(bits) if bits.len() == 64 => bits.signed(),
                                value => panic!("转换结果类型错误：{value:?}"),
                            };
                            assert!(
                                [1, 2].contains(&value),
                                "宽度={width}，signed={signed}，合并={merge}，结果={value}"
                            );
                        }
                    }
                }
            }
        }

        #[test]
        fn 寄存器向量读写保留非法索引路径() {
            for count in [1, 2, 3, 4] {
                for write in [false, true] {
                    let results = register_vector(true, count, write);
                    assert_eq!(results.len(), 2, "寄存器数={count}，写入={write}：{results:?}");
                    assert_eq!(
                        results.iter().filter(|result| matches!(result, Err(ExecError::Type(..)))).count(),
                        1,
                        "{results:?}"
                    );
                    let value = results.into_iter().find_map(Result::ok).unwrap();
                    assert_eq!(value, Val::Bits(B64::new(if write { 7 } else { 42 }, 8)));
                }
            }
        }

        #[test]
        fn 单元素自由索引保留零路径和非法路径() {
            for width in [1, 8, 64, 128] {
                for write in [false, true] {
                    let results = singleton_free(width, write);
                    assert_eq!(results.len(), 2, "宽度={width}，写入={write}：{results:?}");
                    assert_eq!(results.iter().filter(|result| result.is_ok()).count(), 1);
                    assert_eq!(results.iter().filter(|result| matches!(result, Err(ExecError::Type(..)))).count(), 1);
                }
            }
        }

        #[test]
        fn 宽位_any_bits具化保留最高位和全部候选() {
            for width in [65, 128, 129] {
                for merge in [false, true] {
                    let results = wide_monomorphize(merge, width);
                    assert_eq!(results.len(), 2);
                    let values: Vec<_> = results.into_iter().map(Result::unwrap).collect();
                    assert!(values.contains(&Val::Bits(B129::new(1, width))));
                    assert!(values.contains(&Val::Bits(B129::ones(width))));
                }
            }
        }

        #[test]
        fn 具体宽位转换保持整数类型并检查溢出() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            for width in [64, 65, 128, 129] {
                let expected = Val::I64(1);
                assert_eq!(primop::op_unsigned(Val::Bits(B129::new(1, width)), &mut solver, info()).unwrap(), expected);
                assert_eq!(primop::op_signed(Val::Bits(B129::new(1, width)), &mut solver, info()).unwrap(), expected);
                let expected = Val::I64(-1);
                assert_eq!(primop::op_signed(Val::Bits(B129::ones(width)), &mut solver, info()).unwrap(), expected);
            }
            let high = B129::BIT_ONE.zero_extend(128) << B129::new(127, 128);
            assert!(matches!(primop::op_signed(Val::Bits(high), &mut solver, info()), Err(ExecError::Overflow)));
            for bits in [high, B129::ones(128), B129::ones(129)] {
                assert!(matches!(primop::op_unsigned(Val::Bits(bits), &mut solver, info()), Err(ExecError::Overflow)));
            }
            let invalid_signed = B129::BIT_ONE.zero_extend(129) << B129::new(128, 129);
            assert!(matches!(
                primop::op_signed(Val::Bits(invalid_signed), &mut solver, info()),
                Err(ExecError::Overflow)
            ));
        }

        #[test]
        fn 符号转换使用正确整数位宽和符号扩展() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            for width in [1, 63, 64, 65, 127, 128, 129] {
                for signed in [false, true] {
                    let bits = solver.define_const(primop::smt_ones(i128::from(width)), info());
                    let value = if signed {
                        primop::op_signed(Val::Symbolic(bits), &mut solver, info())
                    } else {
                        primop::op_unsigned(Val::Symbolic(bits), &mut solver, info())
                    };
                    if !signed && width > 64 {
                        assert!(matches!(value, Err(ExecError::Overflow)), "宽度={width}：{value:?}");
                        continue;
                    }
                    let value = value.unwrap();
                    let Val::Symbolic(result) = value else { panic!("符号转换必须返回符号整数") };
                    let result_width = 64;
                    assert_eq!(solver.length(result), Some(result_width));
                    assert!(solver.check_sat(info()).is_sat().unwrap());
                    let materialized = Model::new(&solver).get_val(&value).unwrap();
                    let expected = if signed || width >= result_width {
                        B129::ones(result_width)
                    } else {
                        B129::ones(width).zero_extend(result_width)
                    };
                    assert_eq!(materialized, Val::Bits(expected), "宽度={width}，有符号={signed}");
                }
            }
        }
        #[test]
        fn 多元素符号索引在原始位宽检查完整边界() {
            for (count, width, range) in [
                (2, 1, None),
                (3, 1, None),
                (3, 2, Some((0, 2))),
                (2, 8, Some((0, 1))),
                (2, 8, Some((2, 255))),
                (3, 8, Some((3, 255))),
                (2, 8, None),
                (3, 8, None),
                (2, 128, Some((0, 1))),
                (2, 129, Some((2, 3))),
            ] {
                for write in [false, true] {
                    let ctx = Context::new(Config::new());
                    let mut solver = Solver::<B64>::new(&ctx);
                    let mut shared = empty_shared_state();
                    let mut frame = make_frame(vec![Instr::End]);
                    let regs: Vec<_> = (0..count)
                        .map(|index| shared.symtab.intern(Box::leak(format!("zreview20_reg{index}").into_boxed_str())))
                        .collect();
                    for reg in &regs {
                        frame.regs_mut().insert(*reg, false, UVal::Init(Val::Bits(B64::new(42, 8))));
                    }
                    let index = solver.declare_const(smtlib::Ty::BitVec(width), info());
                    if let Some((lower, upper)) = range {
                        solver.assert(smtlib::Exp::Bvuge(
                            Box::new(smtlib::Exp::Var(index)),
                            Box::new(smtlib::bits64(lower, width)),
                        ));
                        solver.assert(smtlib::Exp::Bvule(
                            Box::new(smtlib::Exp::Var(index)),
                            Box::new(smtlib::bits64(upper, width)),
                        ));
                    }
                    let refs = Val::Vector(regs.iter().copied().map(Val::Ref).collect());
                    let result = if write {
                        write_register_from_vector(
                            Val::Symbolic(index),
                            Val::Bits(B64::new(7, 8)),
                            refs,
                            &mut frame.local_state,
                            &shared,
                            &mut solver,
                            info(),
                        )
                    } else {
                        read_register_from_vector(
                            Val::Symbolic(index),
                            refs,
                            &mut frame.local_state,
                            &shared,
                            &mut solver,
                            info(),
                        )
                        .map(|value| {
                            assert_eq!(value, Val::Bits(B64::new(42, 8)));
                        })
                    };
                    if range.is_some_and(|(lower, _)| lower >= count as u64) {
                        assert!(matches!(result, Err(ExecError::Type(..))), "完全越界必须报错：{result:?}");
                    } else if range.is_none() && width > 1 {
                        assert!(matches!(result, Err(ExecError::SymbolicLength(..))), "混合索引必须分叉：{result:?}");
                    } else {
                        assert!(result.is_ok(), "确定在界内必须成功：{result:?}");
                    }
                    if result.is_err() {
                        for reg in regs {
                            assert_eq!(
                                frame.local_state.regs.get(reg, &shared, &mut solver, info()).unwrap().unwrap(),
                                &Val::Bits(B64::new(42, 8))
                            );
                        }
                        assert!(
                            !solver.trace().to_vec().iter().any(|event| matches!(
                                event,
                                Event::ReadReg(..) | Event::WriteReg(..) | Event::Abstract { .. }
                            )),
                            "边界检查失败前不得访问寄存器"
                        );
                    }
                }
            }
        }
    }

    mod review19_tests {
        use super::*;

        #[test]
        fn review19_singleton_mixed_index_keeps_zero_candidate() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let mut shared = empty_shared_state();
            let reg = shared.symtab.intern("zreview19_singleton");
            let mut frame = make_frame(vec![Instr::End]);
            frame.regs_mut().insert(reg, false, UVal::Init(Val::Bits(B64::new(42, 8))));
            let choice = solver.declare_const(smtlib::Ty::Bool, info());
            let index = solver.define_const(
                smtlib::Exp::Ite(
                    Box::new(smtlib::Exp::Var(choice)),
                    Box::new(smtlib::bits64(0, 8)),
                    Box::new(smtlib::bits64(1, 8)),
                ),
                info(),
            );
            let result = read_register_from_vector(
                Val::Symbolic(index),
                Val::Vector(vec![Val::Ref(reg)]),
                &mut frame.local_state,
                &shared,
                &mut solver,
                info(),
            );
            eprintln!("索引仍可为 0，读取结果：{result:?}");
            assert!(
                matches!(result, Err(ExecError::SymbolicLength("read_register_from_vector", location)) if location == info()),
                "混合索引必须触发自适应分叉，保留索引 0 的合法路径"
            );
        }

        #[test]
        fn review19_singleton_write_mixed_index_keeps_zero_candidate() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let mut shared = empty_shared_state();
            let reg = shared.symtab.intern("zreview19_singleton_write");
            let mut frame = make_frame(vec![Instr::End]);
            frame.regs_mut().insert(reg, false, UVal::Init(Val::Bits(B64::new(42, 8))));
            let choice = solver.declare_const(smtlib::Ty::Bool, info());
            let index = solver.define_const(
                smtlib::Exp::Ite(
                    Box::new(smtlib::Exp::Var(choice)),
                    Box::new(smtlib::bits64(0, 8)),
                    Box::new(smtlib::bits64(1, 8)),
                ),
                info(),
            );
            let result = write_register_from_vector(
                Val::Symbolic(index),
                Val::Bits(B64::new(7, 8)),
                Val::Vector(vec![Val::Ref(reg)]),
                &mut frame.local_state,
                &shared,
                &mut solver,
                info(),
            );
            eprintln!("索引仍可为 0，写入结果：{result:?}");
            assert!(
                matches!(result, Err(ExecError::SymbolicLength("write_register_from_vector", location)) if location == info()),
                "混合索引必须触发自适应分叉，保留索引 0 的合法路径"
            );
            assert_eq!(
                frame.local_state.regs.get(reg, &shared, &mut solver, info()).unwrap().unwrap(),
                &Val::Bits(B64::new(42, 8)),
                "等待索引拆分时不得提前修改寄存器"
            );
        }

        #[test]
        fn review19_proven_i128_completion_keeps_free_variable_symbolic() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let free = solver.declare_const(smtlib::Ty::BitVec(128), info());
            assert_eq!(primop::proven_symbolic_i128(free, &mut solver, info()).unwrap(), None);
            let zero = solver.define_const(
                smtlib::Exp::Bvxor(Box::new(smtlib::Exp::Var(free)), Box::new(smtlib::Exp::Var(free))),
                info(),
            );
            assert_eq!(primop::proven_symbolic_i128(zero, &mut solver, info()).unwrap(), Some(0));
        }

        #[test]
        fn review19_wide_anybits_monomorphize() {
            use crate::bitvector::b129::B129;
            let bits = test_name(1901);
            let instrs = Box::leak(
                vec![
                    Instr::Monomorphize(bits, Ty::AnyBits, info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(bits), info()),
                    Instr::End,
                ]
                .into_boxed_slice(),
            );
            let mut frame: LocalFrame<B129> = LocalFrame::new(test_name(25), &[], &Ty::Unit, None, instrs);
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let sym = solver.declare_bitvector(128, info());
            solver.assert_eq(smtlib::Exp::Var(sym), smtlib::Exp::Bits(vec![true; 128]));
            frame.vars_mut().insert(bits, UVal::Init(Val::Symbolic(sym)));
            let state = TaskState::new();
            let shared = SharedState::<B129>::empty(Symtab::new());
            let queue = Worker::new_lifo();
            let result = run_loop(
                0,
                TaskId::fresh(),
                &mut Fraction::one(),
                PathTimeout::unlimited(),
                None,
                &SingleForkSink { queue: &queue },
                &mut frame,
                &state,
                &shared,
                &mut solver,
            );
            match result.unwrap() {
                Run::Finished(Val::Bits(value)) => {
                    assert_eq!(value, B129::ones(128));
                }
                _ => panic!("宽位 AnyBits 具化结果错误"),
            }
        }

        #[test]
        fn review19_wide_unassigned_monomorphize() {
            use crate::bitvector::b129::B129;
            let bits = test_name(1902);
            let instrs = Box::leak(
                vec![
                    Instr::Decl(bits, Ty::Bits(128), info()),
                    Instr::Monomorphize(bits, Ty::Bits(128), info()),
                    Instr::End,
                ]
                .into_boxed_slice(),
            );
            let mut frame: LocalFrame<B129> = LocalFrame::new(test_name(25), &[], &Ty::Unit, None, instrs);
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let state = TaskState::new().with_execution_limits(
                ExecutionLimits::default().with_max_forks_per_path(0).with_limit_behavior(LimitBehavior::Concretize),
            );
            let shared = SharedState::<B129>::empty(Symtab::new());
            let queue = Worker::new_lifo();
            let result = run_loop(
                0,
                TaskId::fresh(),
                &mut Fraction::one(),
                PathTimeout::unlimited(),
                None,
                &SingleForkSink { queue: &queue },
                &mut frame,
                &state,
                &shared,
                &mut solver,
            );
            assert!(matches!(result, Ok(Run::Finished(_))));
        }

        #[test]
        fn review19_wide_anybits_after_diamond() {
            use crate::bitvector::b129::B129;
            for enabled in [false, true] {
                let branch = test_name(1910);
                let bits = test_name(1911);
                let instrs = Box::leak(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(bits, Ty::AnyBits, info()),
                        Instr::Jump(Exp::Id(branch), 5, info()),
                        Instr::Copy(Loc::Id(bits), Exp::Id(test_name(1912)), info()),
                        Instr::Goto(6),
                        Instr::Copy(Loc::Id(bits), Exp::Id(test_name(1913)), info()),
                        Instr::Monomorphize(bits, Ty::AnyBits, info()),
                        Instr::Copy(Loc::Id(RETURN), Exp::Id(bits), info()),
                        Instr::End,
                    ]
                    .into_boxed_slice(),
                );
                let mut frame: LocalFrame<B129> = LocalFrame::new(test_name(25), &[], &Ty::Unit, None, instrs);
                frame.lets_mut().insert(test_name(1912), UVal::Init(Val::Bits(B129::new(1, 128))));
                frame.lets_mut().insert(test_name(1913), UVal::Init(Val::Bits(B129::new(2, 128))));
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let shared = SharedState::<B129>::empty(Symtab::new());
                let values = Mutex::new(Vec::new());
                eprintln!("AnyBits 菱形复现，合并={enabled}");
                start_single(frame.task(TaskId::fresh(), &state), &shared, &values, &|_, _, result, _, _, values| {
                    values.lock().unwrap().push(match result {
                        Ok((Run::Finished(Val::Bits(value)), _)) => value.lower_u64(),
                        Err((error, _)) => panic!("宽位 AnyBits 具化失败：{error:?}"),
                        _ => panic!("返回类型错误"),
                    });
                });
                let mut values = values.into_inner().unwrap();
                values.sort();
                eprintln!("AnyBits 菱形复现，合并={enabled}，结果={values:?}");
                assert_eq!(values, vec![1, 2]);
            }
        }
    }

    mod review18_tests {
        use super::*;

        #[test]
        fn singleton_register_vector_symbolic_read_and_write() {
            for width in [8, 64, 128] {
                for index in [0, 1] {
                    let ctx = Context::new(Config::new());
                    let mut solver = Solver::<B64>::new(&ctx);
                    let mut shared = empty_shared_state();
                    let reg = shared.symtab.intern("zsingleton");
                    let mut frame = make_frame(vec![Instr::End]);
                    frame.regs_mut().insert(reg, false, UVal::Init(Val::Bits(B64::new(42, 8))));
                    let sym = solver.declare_const(smtlib::Ty::BitVec(width), info());
                    solver.assert_eq(smtlib::Exp::Var(sym), smtlib::bits64(index, width));
                    let refs = Val::Vector(vec![Val::Ref(reg)]);
                    let read = read_register_from_vector(
                        Val::Symbolic(sym),
                        refs.clone(),
                        &mut frame.local_state,
                        &shared,
                        &mut solver,
                        info(),
                    );
                    let write = write_register_from_vector(
                        Val::Symbolic(sym),
                        Val::Bits(B64::new(7, 8)),
                        refs,
                        &mut frame.local_state,
                        &shared,
                        &mut solver,
                        info(),
                    );
                    if index == 0 {
                        assert_eq!(read.unwrap(), Val::Bits(B64::new(42, 8)));
                        write.unwrap();
                    } else {
                        assert!(matches!(read, Err(ExecError::Type(..))));
                        assert!(matches!(write, Err(ExecError::Type(..))));
                    }
                    assert_eq!(
                        frame.local_state.regs.get(reg, &shared, &mut solver, info()).unwrap().unwrap(),
                        &Val::Bits(B64::new(if index == 0 { 7 } else { 42 }, 8)),
                    );
                    let events = solver.trace().to_vec();
                    assert_eq!(
                        events.iter().filter(|event| matches!(event, Event::ReadReg(..))).count(),
                        usize::from(index == 0)
                    );
                    assert_eq!(
                        events.iter().filter(|event| matches!(event, Event::WriteReg(..))).count(),
                        usize::from(index == 0)
                    );
                }
            }
        }

        #[test]
        fn reachable_constructor_payload_errors_split_tags() {
            for enabled in [false, true] {
                let branch = test_name(650);
                let value = test_name(651);
                let source_a = test_name(652);
                let source_b = test_name(653);
                let mut lets = Bindings::default();
                lets.insert(source_a, UVal::Init(Val::Ctor(test_name(654), Box::new(Val::String("载荷".to_owned())))));
                lets.insert(source_b, UVal::Init(Val::Ctor(test_name(655), Box::new(Val::Unit))));
                let outcomes = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(value, Ty::Union(test_name(656)), info()),
                        Instr::Jump(Exp::Id(branch), 5, info()),
                        Instr::Copy(Loc::Id(value), Exp::Id(source_a), info()),
                        Instr::Goto(6),
                        Instr::Copy(Loc::Id(value), Exp::Id(source_b), info()),
                        Instr::PrimopBinary(
                            Loc::Id(RETURN),
                            primop::binary_primops()["eq_anything"],
                            Exp::Id(value),
                            Exp::Id(value),
                            info(),
                        ),
                        Instr::Jump(Exp::Id(RETURN), 10, info()),
                        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                        Instr::End,
                        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    lets,
                );
                assert_eq!(outcomes.len(), 2);
                assert_eq!(outcomes.iter().filter(|r| matches!(r, Ok(Run::Finished(Val::Bool(true))))).count(), 1);
                assert_eq!(outcomes.iter().filter(|r| matches!(r, Err(ExecError::Type(..)))).count(), 1);
            }
        }

        #[test]
        fn symbolic_subrange_checks_both_bounds() {
            for enabled in [false, true] {
                let branch = test_name(600);
                let hi_bits = test_name(601);
                let lo_bits = test_name(602);
                let high = test_name(603);
                let low = test_name(604);
                let outcomes = run_all_with_shared_state(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(hi_bits, Ty::Bits(8), info()),
                        Instr::Decl(lo_bits, Ty::Bits(8), info()),
                        Instr::Decl(high, Ty::I128, info()),
                        Instr::Decl(low, Ty::I128, info()),
                        Instr::PrimopUnary(
                            Loc::Id(RETURN),
                            primop::unary_primops()["assume"],
                            Exp::Call(Op::Or, vec![Exp::Id(branch), Exp::Undefined(Ty::Bool)]),
                            info(),
                        ),
                        Instr::Jump(Exp::Id(branch), 10, info()),
                        Instr::Copy(Loc::Id(hi_bits), Exp::Bits(B64::new(7, 8)), info()),
                        Instr::Copy(Loc::Id(lo_bits), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(12),
                        Instr::Copy(Loc::Id(hi_bits), Exp::Bits(B64::new(8, 8)), info()),
                        Instr::Copy(Loc::Id(lo_bits), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::PrimopUnary(
                            Loc::Id(high),
                            primop::unary_primops()["sail_unsigned"],
                            Exp::Id(hi_bits),
                            info(),
                        ),
                        Instr::PrimopUnary(
                            Loc::Id(low),
                            primop::unary_primops()["sail_unsigned"],
                            Exp::Id(lo_bits),
                            info(),
                        ),
                        Instr::PrimopVariadic(
                            Loc::Id(RETURN),
                            primop::variadic_primops()["vector_subrange"],
                            vec![Exp::Bits(B64::new(255, 8)), Exp::Id(high), Exp::Id(low)],
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                );
                eprintln!(
                    "子范围：合并={enabled}，结果={:?}",
                    outcomes
                        .iter()
                        .map(|r| match r {
                            Ok(Run::Finished(v)) => format!("完成 {v:?}"),
                            Err(e) => format!("错误 {e:?}"),
                            _ => "其它".to_owned(),
                        })
                        .collect::<Vec<_>>()
                );
                assert!(outcomes.iter().any(|r| matches!(r, Err(ExecError::Type(_, _)))), "必须保留 high=8 的错误路径");
            }
        }

        #[test]
        fn unique_symbolic_length_with_unassigned_guard() {
            for enabled in [false, true] {
                let branch = test_name(630);
                let hi_bits = test_name(631);
                let lo_bits = test_name(632);
                let high = test_name(633);
                let low = test_name(634);
                let length = test_name(635);
                let outcomes = run_all_with_shared_state(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(hi_bits, Ty::Bits(8), info()),
                        Instr::Decl(lo_bits, Ty::Bits(8), info()),
                        Instr::Decl(high, Ty::I128, info()),
                        Instr::Decl(low, Ty::I128, info()),
                        Instr::Decl(length, Ty::I128, info()),
                        Instr::Jump(Exp::Id(branch), 10, info()),
                        Instr::Copy(Loc::Id(hi_bits), Exp::Bits(B64::new(7, 8)), info()),
                        Instr::Copy(Loc::Id(lo_bits), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(12),
                        Instr::Copy(Loc::Id(hi_bits), Exp::Bits(B64::new(8, 8)), info()),
                        Instr::Copy(Loc::Id(lo_bits), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::PrimopUnary(
                            Loc::Id(high),
                            primop::unary_primops()["sail_unsigned"],
                            Exp::Id(hi_bits),
                            info(),
                        ),
                        Instr::PrimopUnary(
                            Loc::Id(low),
                            primop::unary_primops()["sail_unsigned"],
                            Exp::Id(lo_bits),
                            info(),
                        ),
                        Instr::PrimopBinary(
                            Loc::Id(length),
                            primop::binary_primops()["sub_int"],
                            Exp::Id(high),
                            Exp::Id(low),
                            info(),
                        ),
                        Instr::PrimopBinary(
                            Loc::Id(length),
                            primop::binary_primops()["add_int"],
                            Exp::Id(length),
                            Exp::I128(1),
                            info(),
                        ),
                        Instr::PrimopUnary(Loc::Id(RETURN), primop::unary_primops()["zeros"], Exp::Id(length), info()),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                );
                eprintln!(
                    "唯一符号长度：合并={enabled}，结果={:?}",
                    outcomes
                        .iter()
                        .map(|r| match r {
                            Ok(Run::Finished(v)) => format!("完成 {v:?}"),
                            Err(e) => format!("错误 {e:?}"),
                            _ => "其它".to_owned(),
                        })
                        .collect::<Vec<_>>()
                );
                assert!(outcomes.iter().all(|r| matches!(r, Ok(Run::Finished(_)))), "唯一可行长度 8 不得报错");
            }
        }

        #[test]
        fn symbolic_subrange_with_constrained_input() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let low = solver.declare_const(smtlib::Ty::BitVec(128), info());
            solver.assert(smtlib::Exp::Or(
                Box::new(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(low)), Box::new(crate::primop_util::smt_i128(0)))),
                Box::new(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(low)), Box::new(crate::primop_util::smt_i128(6)))),
            ));
            let high = solver.define_const(
                smtlib::Exp::Bvadd(Box::new(smtlib::Exp::Var(low)), Box::new(crate::primop_util::smt_i128(3))),
                info(),
            );
            let result = primop::subrange_internal(
                Val::Bits(B64::new(255, 8)),
                Val::Symbolic(high),
                Val::Symbolic(low),
                &mut solver,
                info(),
            );
            eprintln!("相关符号索引结果：{result:?}");
            if let Ok(value) = &result {
                let invalid = smtlib::Exp::And(
                    Box::new(smtlib::Exp::Eq(
                        Box::new(smtlib::Exp::Var(low)),
                        Box::new(crate::primop_util::smt_i128(6)),
                    )),
                    Box::new(smtlib::Exp::Eq(
                        Box::new(crate::primop_util::smt_value(value, info()).unwrap()),
                        Box::new(smtlib::bits64(3, 4)),
                    )),
                );
                eprintln!(
                    "越界候选 low=6、high=9、返回四位 3 的可满足性：{:?}",
                    solver.check_sat_with(&invalid, info())
                );
            }
            assert!(result.is_err(), "不能正常接受 high=9 的候选");
        }

        #[test]
        fn singleton_register_vector_with_merged_zero_index() {
            for enabled in [false, true] {
                let mut shared = empty_shared_state();
                let reg = shared.symtab.intern("zsingleton");
                let branch = test_name(620);
                let bits = test_name(621);
                let zero_bits = test_name(622);
                let index = test_name(623);
                let refs = test_name(624);
                let mut lets = Bindings::default();
                lets.insert(refs, UVal::Init(Val::Vector(vec![Val::Ref(reg)])));
                let mut regs = RegisterBindings::new();
                regs.insert(reg, false, UVal::Init(Val::Bits(B64::new(42, 8))));
                let outcomes = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(bits, Ty::Bits(8), info()),
                        Instr::Decl(zero_bits, Ty::Bits(8), info()),
                        Instr::Decl(index, Ty::I128, info()),
                        Instr::Jump(Exp::Id(branch), 7, info()),
                        Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(8),
                        Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::PrimopBinary(
                            Loc::Id(zero_bits),
                            primop::binary_primops()["and_bits"],
                            Exp::Id(bits),
                            Exp::Bits(B64::new(0, 8)),
                            info(),
                        ),
                        Instr::PrimopUnary(
                            Loc::Id(index),
                            primop::unary_primops()["sail_unsigned"],
                            Exp::Id(zero_bits),
                            info(),
                        ),
                        Instr::Call(
                            Loc::Id(RETURN),
                            false,
                            READ_REGISTER_FROM_VECTOR,
                            vec![Exp::Id(index), Exp::Id(refs)],
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    shared,
                    regs,
                    lets,
                );
                eprintln!("单元素寄存器向量：合并={enabled}，完成路径数={}", outcomes.len());
                assert!(outcomes
                    .iter()
                    .all(|r| matches!(r, Ok(Run::Finished(Val::Bits(value))) if value.lower_u64()==42)));
            }
        }

        #[test]
        fn monomorphize_wide_merged_bits() {
            use crate::bitvector::b129::B129;
            for enabled in [false, true] {
                let branch = test_name(640);
                let bits = test_name(641);
                let instrs = vec![
                    Instr::Decl(branch, Ty::Bool, info()),
                    Instr::Decl(bits, Ty::Bits(128), info()),
                    Instr::Jump(Exp::Id(branch), 5, info()),
                    Instr::Copy(Loc::Id(bits), Exp::Id(test_name(642)), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(bits), Exp::Id(test_name(643)), info()),
                    Instr::Monomorphize(bits, Ty::Bits(128), info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(bits), info()),
                    Instr::End,
                ];
                let instrs = Box::leak(instrs.into_boxed_slice());
                let mut frame: LocalFrame<B129> = LocalFrame::new(test_name(25), &[], &Ty::Unit, None, instrs);
                frame.lets_mut().insert(test_name(642), UVal::Init(Val::Bits(B129::new(1, 128))));
                frame.lets_mut().insert(test_name(643), UVal::Init(Val::Bits(B129::new(2, 128))));
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let shared = SharedState::<B129>::empty(Symtab::new());
                let values = Mutex::new(Vec::new());
                start_single(frame.task(TaskId::fresh(), &state), &shared, &values, &|_, _, result, _, _, values| {
                    values.lock().unwrap().push(match result {
                        Ok((Run::Finished(Val::Bits(v)), _)) => v.lower_u64(),
                        Err((e, _)) => panic!("宽位向量具体化失败：{e:?}"),
                        _ => panic!("宽位向量具体化返回类型错误"),
                    });
                });
                let mut values = values.into_inner().unwrap();
                values.sort();
                eprintln!("宽位向量具体化：合并={enabled}，结果={values:?}");
                assert_eq!(values, vec![1, 2]);
            }
        }

        #[test]
        fn opposite_constructor_tags_skip_inactive_payloads() {
            for enabled in [false, true] {
                let branch = test_name(610);
                let a = test_name(611);
                let b = test_name(612);
                let ctor_a = test_name(613);
                let ctor_b = test_name(614);
                let source_a = test_name(615);
                let source_b = test_name(616);
                let mut lets = Bindings::default();
                lets.insert(source_a, UVal::Init(Val::Ctor(ctor_a, Box::new(Val::String("载荷".to_owned())))));
                lets.insert(source_b, UVal::Init(Val::Ctor(ctor_b, Box::new(Val::Unit))));
                let outcomes = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(a, Ty::Union(test_name(617)), info()),
                        Instr::Decl(b, Ty::Union(test_name(617)), info()),
                        Instr::Jump(Exp::Id(branch), 7, info()),
                        Instr::Copy(Loc::Id(a), Exp::Id(source_a), info()),
                        Instr::Copy(Loc::Id(b), Exp::Id(source_b), info()),
                        Instr::Goto(9),
                        Instr::Copy(Loc::Id(a), Exp::Id(source_b), info()),
                        Instr::Copy(Loc::Id(b), Exp::Id(source_a), info()),
                        Instr::PrimopBinary(
                            Loc::Id(RETURN),
                            primop::binary_primops()["eq_anything"],
                            Exp::Id(a),
                            Exp::Id(b),
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    lets,
                );
                eprintln!(
                    "相反构造子：合并={enabled}，结果={:?}",
                    outcomes
                        .iter()
                        .map(|r| match r {
                            Ok(Run::Finished(v)) => format!("完成 {v:?}"),
                            Err(e) => format!("错误 {e:?}"),
                            _ => "其它".to_owned(),
                        })
                        .collect::<Vec<_>>()
                );
                assert!(
                    outcomes.iter().all(|r| matches!(r, Ok(Run::Finished(_)))),
                    "不同构造子的比较不得求值不可达载荷"
                );
            }
        }
    }
    mod review17_tests {
        use super::*;

        #[test]
        fn review17_subrange_all_representations() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let sym = solver.define_bitvector(smtlib::Exp::Bits64(B64::new(0xab, 8)), info());
            let values = [
                Val::Bits(B64::new(0xab, 8)),
                Val::Symbolic(sym),
                Val::MixedBits(vec![crate::ir::BitsSegment::Symbolic(sym)]),
            ];
            for bits in values {
                for (high, low) in [(8, 0), (7, -1), (-1, 0), (2, 3), (i128::MAX, 0), (1_i128 << 32, 0)] {
                    assert!(
                        matches!(
                            primop::subrange_internal(
                                bits.clone(),
                                Val::I128(high),
                                Val::I128(low),
                                &mut solver,
                                info()
                            ),
                            Err(ExecError::Type(_, _))
                        ),
                        "越界索引必须返回类型错误"
                    );
                }
                let sliced = primop::subrange_internal(bits, Val::I128(7), Val::I128(0), &mut solver, info()).unwrap();
                assert!(solver.check_sat(info()).is_sat().unwrap());
                assert_eq!(Model::new(&solver).get_val(&sliced).unwrap(), Val::Bits(B64::new(0xab, 8)));
            }
        }

        #[test]
        fn review17_symbolic_code_ifetch() {
            for enabled in [false, true] {
                let branch = test_name(490);
                let addr = test_name(491);
                let mut frame = make_frame(vec![
                    Instr::Decl(branch, Ty::Bool, info()),
                    Instr::Decl(addr, Ty::Bits(64), info()),
                    Instr::Jump(Exp::Id(branch), 5, info()),
                    Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0x1000, 64)), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0x1004, 64)), info()),
                    Instr::PrimopVariadic(
                        Loc::Id(RETURN),
                        primop::variadic_primops()["platform_read_mem_ifetch"],
                        vec![Exp::Unit, Exp::I128(64), Exp::Id(addr), Exp::I128(4)],
                        info(),
                    ),
                    Instr::End,
                ]);
                frame.memory_mut().add_region(crate::memory::Region::SymbolicCode(0x1000..0x2000));
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let shared = empty_shared_state();
                let outcomes = Mutex::new(Vec::new());
                start_single(
                    frame.task(TaskId::fresh(), &state),
                    &shared,
                    &outcomes,
                    &|_, _, result, _, _, outcomes| {
                        outcomes.lock().unwrap().push(match result {
                            Ok((Run::Finished(value), _)) => format!("完成 {value:?}"),
                            Err((error, _)) => format!("错误 {error:?}"),
                            _ => panic!("异常结果"),
                        });
                    },
                );
                let outcomes = outcomes.into_inner().unwrap();
                eprintln!("代码区取指：合并={enabled}，结果={outcomes:?}");
                assert!(outcomes.iter().all(|r| r.starts_with("完成")), "合法代码区的取指不得失败");
            }
        }

        #[test]
        fn review17_ifetch_region_dispatch() {
            for enabled in [false, true] {
                for (other, expected) in
                    [(0x3004, vec![true, true]), (0x4000, vec![true, true]), (0x5000, vec![false, true])]
                {
                    let branch = test_name(490);
                    let addr = test_name(491);
                    let mut frame = make_frame(vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(addr, Ty::Bits(64), info()),
                        Instr::Jump(Exp::Id(branch), 5, info()),
                        Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0x1000, 64)), info()),
                        Instr::Goto(6),
                        Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(other, 64)), info()),
                        Instr::PrimopVariadic(
                            Loc::Id(RETURN),
                            primop::variadic_primops()["platform_read_mem_ifetch"],
                            vec![Exp::Unit, Exp::I128(64), Exp::Id(addr), Exp::I128(4)],
                            info(),
                        ),
                        Instr::End,
                    ]);
                    frame.memory_mut().add_region(crate::memory::Region::SymbolicCode(0x1000..0x2000));
                    frame.memory_mut().add_region(crate::memory::Region::SymbolicCode(0x3000..0x4000));
                    frame.memory_mut().add_zero_region(0x4000..0x4004);
                    let state =
                        TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                    let shared = empty_shared_state();
                    let results = Mutex::new(Vec::new());
                    start_single(
                        frame.task(TaskId::fresh(), &state),
                        &shared,
                        &results,
                        &|_, _, result, _, _, results| {
                            results.lock().unwrap().push(match result {
                                Ok((Run::Finished(_), _)) => true,
                                Err((ExecError::BadRead(_), _)) => false,
                                _ => panic!("异常取指结果"),
                            });
                        },
                    );
                    let mut results = results.into_inner().unwrap();
                    results.sort();
                    assert_eq!(results, expected, "跨代码区、具体区和默认区域必须按候选独立分派");
                }
            }
        }

        #[test]
        fn review17_hex_machine_integer_width() {
            for enabled in [false, true] {
                let branch = test_name(490);
                let bits = test_name(491);
                let integer = test_name(492);
                let outcomes = run_all_with_shared_state(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(bits, Ty::Bits(8), info()),
                        Instr::Decl(integer, Ty::I64, info()),
                        Instr::Jump(Exp::Id(branch), 6, info()),
                        Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(255, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(254, 8)), info()),
                        Instr::Copy(Loc::Id(integer), Exp::Call(Op::Signed(8), vec![Exp::Id(bits)]), info()),
                        Instr::PrimopUnary(
                            Loc::Id(RETURN),
                            primop::unary_primops()["hex_str"],
                            Exp::Id(integer),
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                );
                let values: Vec<_> = outcomes
                    .into_iter()
                    .map(|r| match r {
                        Ok(Run::Finished(Val::String(value))) => value,
                        _ => panic!("异常结果"),
                    })
                    .collect();
                eprintln!("机器整数十六进制：合并={enabled}，结果={values:?}");
                assert!(values.iter().all(|v| v.len() == 18), "i64 十六进制格式必须保持 16 位");
            }
        }

        #[test]
        fn review17_float_bitvector_shift_category() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<crate::bitvector::b129::B129>::new(&ctx);
            let unary = primop::unary_primops::<crate::bitvector::b129::B129>();
            let binary = primop::binary_primops::<crate::bitvector::b129::B129>();
            let rounding = unary["round_toward_zero"](Val::Unit, &mut solver, info()).unwrap();
            let ieee = solver.define_bitvector(smtlib::Exp::Bits64(B64::new(0xbf800000, 32)), info());
            let fp = unary["fp32_from_ieee"](Val::Symbolic(ieee), &mut solver, info()).unwrap();
            let amount = binary["fp_to_signed128"](rounding, fp, &mut solver, info()).unwrap();
            let Val::Symbolic(amount_sym) = &amount else { panic!("转换必须返回符号位向量") };
            assert!(solver.is_sail_bitvector(*amount_sym), "浮点转换必须标记 Sail 位向量");
            let mut replayed = Solver::from_checkpoint(&ctx, checkpoint(&mut solver));
            assert!(replayed.is_sail_bitvector(*amount_sym), "检查点重放必须保留位向量类别");
            let replayed_result = binary["arith_shiftr"](
                Val::Bits(crate::bitvector::b129::B129::new(1, 8)),
                amount.clone(),
                &mut replayed,
                info(),
            )
            .unwrap();
            assert!(replayed.check_sat(info()).is_sat().unwrap());
            assert_eq!(
                Model::new(&replayed).get_val(&replayed_result).unwrap(),
                Val::Bits(crate::bitvector::b129::B129::zeros(8))
            );
            let shifted = binary["arith_shiftr"](
                Val::Bits(crate::bitvector::b129::B129::new(1, 8)),
                amount.clone(),
                &mut solver,
                info(),
            )
            .unwrap();
            assert!(solver.check_sat(info()).is_sat().unwrap());
            let mut model = Model::new(&solver);
            let concrete_amount = model.get_val(&amount).unwrap();
            let concrete_result = model.get_val(&shifted).unwrap();
            drop(model);
            let expected = binary["arith_shiftr"](
                Val::Bits(crate::bitvector::b129::B129::new(1, 8)),
                concrete_amount.clone(),
                &mut solver,
                info(),
            )
            .unwrap();
            eprintln!("浮点转换移位量={concrete_amount:?}，符号移位={concrete_result:?}，具体移位={expected:?}");
            assert_eq!(
                solver.check_sat_with(
                    &smtlib::Exp::Neq(
                        Box::new(crate::primop_util::smt_value(&shifted, info()).unwrap()),
                        Box::new(smtlib::Exp::Bits64(B64::zeros(8))),
                    ),
                    info()
                ),
                SmtResult::Unsat,
                "位向量移位量必须按无符号解释"
            );
        }

        #[test]
        fn review17_subrange_bounds() {
            for enabled in [false, true] {
                let branch = test_name(490);
                let bits = test_name(491);
                let outcomes = run_all_with_shared_state(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(bits, Ty::Bits(8), info()),
                        Instr::Jump(Exp::Id(branch), 5, info()),
                        Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::Goto(6),
                        Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(2, 8)), info()),
                        Instr::PrimopVariadic(
                            Loc::Id(RETURN),
                            primop::variadic_primops()["vector_subrange"],
                            vec![Exp::Id(bits), Exp::I128(8), Exp::I128(0)],
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                );
                for outcome in outcomes {
                    match outcome {
                        Err(error) => eprintln!("越界子范围：合并={enabled}，错误={error:?}"),
                        _ => panic!("越界子范围必须返回执行错误"),
                    }
                }
            }
        }

        #[test]
        fn review17_mixed_bits_string_representation() {
            for name in ["string_of_bits", "decimal_string_of_bits"] {
                for enabled in [false, true] {
                    let branch = test_name(490);
                    let bits = test_name(491);
                    let mixed = test_name(492);
                    let ctx = Context::new(Config::new());
                    let mut solver = Solver::<B64>::new(&ctx);
                    let low = solver.define_bitvector(smtlib::Exp::Bits64(B64::new(11, 8)), info());
                    let mut frame = make_frame(vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(bits, Ty::Bits(16), info()),
                        Instr::Jump(Exp::Id(branch), 5, info()),
                        Instr::Copy(Loc::Id(bits), Exp::Id(mixed), info()),
                        Instr::Goto(6),
                        Instr::Copy(
                            Loc::Id(bits),
                            Exp::Call(Op::Bvor, vec![Exp::Id(mixed), Exp::Bits(B64::zeros(16))]),
                            info(),
                        ),
                        Instr::PrimopUnary(Loc::Id(RETURN), primop::unary_primops()[name], Exp::Id(bits), info()),
                        Instr::End,
                    ]);
                    frame.lets_mut().insert(
                        mixed,
                        UVal::Init(Val::MixedBits(vec![
                            crate::ir::BitsSegment::Concrete(B64::new(10, 8)),
                            crate::ir::BitsSegment::Symbolic(low),
                        ])),
                    );
                    let shared = empty_shared_state();
                    let state =
                        TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                    let outcomes = Mutex::new(Vec::new());
                    start_single(
                        frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
                        &shared,
                        &outcomes,
                        &|_, _, result, _, _, outcomes| {
                            outcomes.lock().unwrap().push(match result {
                                Ok((Run::Finished(value), _)) => format!("完成 {value:?}"),
                                Err((error, _)) => format!("错误 {error:?}"),
                                _ => panic!("异常结果"),
                            });
                        },
                    );
                    let outcomes = outcomes.into_inner().unwrap();
                    eprintln!("分段位向量：算子={name}，合并={enabled}，结果={outcomes:?}");
                    let expected = if name == "string_of_bits" { "#x0a0b" } else { "2571" };
                    assert!(!outcomes.is_empty(), "字符串转换必须有可达结果");
                    assert!(
                        outcomes.iter().all(|r| *r == format!("完成 String(\"{expected}\")")),
                        "必须按完整位向量统一格式化"
                    );
                }
            }
        }

        #[test]
        fn review17_boolean_trace_result_collector() {
            for enabled in [false, true] {
                let branch = test_name(490);
                let frame = make_frame(vec![
                    Instr::Decl(branch, Ty::Bool, info()),
                    Instr::Jump(Exp::Id(branch), 4, info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                    Instr::Goto(5),
                    Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
                    Instr::End,
                ]);
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let shared = empty_shared_state();
                let queue = TraceResultQueue::new();
                start_single(frame.task(TaskId::fresh(), &state), &shared, &queue, &trace_result_collector);
                let mut values = Vec::new();
                while let Some(result) = queue.pop() {
                    values.push(match result {
                        Ok((_, value, events)) => {
                            let assertions: Vec<_> = events
                                .iter()
                                .filter_map(|event| match event {
                                    Event::Smt(smtlib::Def::Assert(exp), ..) => Some(exp),
                                    _ => None,
                                })
                                .collect();
                            assert!(!assertions.is_empty(), "每条布尔结果轨迹必须携带对应断言");
                            let ctx = Context::new(Config::new());
                            let mut replayed = Solver::<B64>::new(&ctx);
                            for event in events.iter().rev() {
                                if let Event::Smt(def, ..) = event {
                                    replayed.add(def.clone());
                                }
                            }
                            assert!(replayed.check_sat(info()).is_sat().unwrap(), "结果轨迹必须独立可满足");
                            if enabled {
                                let last = assertions[0];
                                assert_eq!(matches!(last, smtlib::Exp::Not(_)), !value, "返回值必须匹配分支断言");
                                assert_eq!(
                                    replayed.check_sat_with(&smtlib::Exp::Not(Box::new(last.clone())), info()),
                                    SmtResult::Unsat
                                );
                            }
                            format!("完成 {value}")
                        }
                        Err(error) => format!("错误 {error:?}"),
                    });
                }
                values.sort();
                eprintln!("布尔轨迹收集：合并={enabled}，结果={values:?}");
                assert_eq!(values, vec!["完成 false", "完成 true"], "布尔返回结果及其轨迹不得丢失");
            }
        }

        #[test]
        fn review17_initial_register_model_materialization() {
            for enabled in [false, true] {
                let mut shared = empty_shared_state();
                let reg = shared.symtab.intern("zreview17_output");
                let branch = test_name(490);
                let mut frame = make_frame(vec![
                    Instr::Decl(branch, Ty::Bool, info()),
                    Instr::Jump(Exp::Id(branch), 4, info()),
                    Instr::Copy(Loc::Id(reg), Exp::Bits(B64::new(1, 8)), info()),
                    Instr::Goto(5),
                    Instr::Copy(Loc::Id(reg), Exp::Bits(B64::new(2, 8)), info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                    Instr::End,
                ]);
                frame.regs_mut().insert(reg, false, UVal::Init(Val::Bits(B64::zeros(8))));
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let values = Mutex::new(Vec::new());
                start_single(
                    frame.task(TaskId::fresh(), &state),
                    &shared,
                    &values,
                    &|_, _, result, _, solver, values| {
                        assert!(result.is_ok(), "合法寄存器写入必须完成");
                        let events: Vec<_> = solver.trace().to_vec().into_iter().rev().cloned().collect();
                        let initial = crate::trace::RegisterState::from_events(&events);
                        let model = initial.model().unwrap();
                        let value = match initial.values.get(&reg).unwrap() {
                            Val::Bits(bits) => bits.lower_u64(),
                            Val::Symbolic(sym) => match model.get(sym).unwrap() {
                                smtlib::Exp::Bits64(bits) => bits.lower_u64(),
                                _ => panic!("预期 8 位常量"),
                            },
                            _ => panic!("预期寄存器值"),
                        };
                        values.lock().unwrap().push(value);
                    },
                );
                let values = values.into_inner().unwrap();
                eprintln!("初始寄存器轨迹模型：合并={enabled}，结果={values:?}");
                assert!(values.iter().all(|value| [1, 2].contains(value)), "物化不能产生两臂均不可达的值");
            }
        }
    }
    mod review16_tests {
        use super::*;

        #[test]
        fn audit_tagged_and_exclusive_memory_write_addresses() {
            for name in ["platform_write_memt", "platform_write_mem_exclusive"] {
                for enabled in [false, true] {
                    let branch = test_name(470);
                    let addr = test_name(471);
                    let mut frame = make_frame(vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(addr, Ty::Bits(64), info()),
                        Instr::Jump(Exp::Id(branch), 5, info()),
                        Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0x1000, 64)), info()),
                        Instr::Goto(6),
                        Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0x1001, 64)), info()),
                        Instr::PrimopVariadic(
                            Loc::Id(RETURN),
                            primop::variadic_primops()[name],
                            if name == "platform_write_memt" {
                                vec![
                                    Exp::Unit,
                                    Exp::Id(addr),
                                    Exp::I128(1),
                                    Exp::Bits(B64::new(7, 8)),
                                    Exp::Bits(B64::new(0, 1)),
                                ]
                            } else {
                                vec![Exp::Unit, Exp::I128(64), Exp::Id(addr), Exp::I128(1), Exp::Bits(B64::new(7, 8))]
                            },
                            info(),
                        ),
                        Instr::End,
                    ]);
                    frame.memory_mut().add_concrete_region(0x1000..0x1002, HashMap::from([(0x1000, 1), (0x1001, 2)]));
                    let shared = empty_shared_state();
                    let state =
                        TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                    let results = Mutex::new(Vec::new());
                    start_single(
                        frame.task(TaskId::fresh(), &state),
                        &shared,
                        &results,
                        &|_, _, result, _, _, results| {
                            let value = match result {
                                Ok((Run::Finished(value), _)) => format!("完成 {value:?}"),
                                Err((error, _)) => format!("错误 {error:?}"),
                                _ => panic!("异常结果"),
                            };
                            results.lock().unwrap().push(value);
                        },
                    );
                    let results = results.into_inner().unwrap();
                    eprintln!("多候选地址写入：合并={enabled}，结果={results:?}");
                    assert_eq!(results.len(), 2, "两个候选写地址都必须执行");
                    assert!(results.iter().all(|v| v.starts_with("完成")), "合法写入必须完成");
                }
            }
        }

        #[test]
        fn audit_writing_across_excluded_memory() {
            for enabled in [false, true] {
                let branch = test_name(470);
                let addr = test_name(471);
                let mut frame = make_frame(vec![
                    Instr::Decl(branch, Ty::Bool, info()),
                    Instr::Decl(addr, Ty::Bits(64), info()),
                    Instr::Jump(Exp::Id(branch), 5, info()),
                    Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0x1000, 64)), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0xfff, 64)), info()),
                    Instr::PrimopVariadic(
                        Loc::Id(RETURN),
                        primop::variadic_primops()["platform_write_mem"],
                        vec![Exp::Unit, Exp::I128(64), Exp::Id(addr), Exp::I128(3), Exp::Bits(B64::new(7, 24))],
                        info(),
                    ),
                    Instr::End,
                ]);
                frame.memory_mut().add_region(crate::memory::Region::Excluded(0x1001..0x1002));
                let shared = empty_shared_state();
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let results = Mutex::new(Vec::new());
                start_single(frame.task(TaskId::fresh(), &state), &shared, &results, &|_, _, result, _, _, results| {
                    let value = match result {
                        Ok((Run::Finished(value), _)) => format!("完成 {value:?}"),
                        Err((error, _)) => format!("错误 {error:?}"),
                        _ => panic!("异常结果"),
                    };
                    results.lock().unwrap().push(value);
                });
                let results = results.into_inner().unwrap();
                eprintln!("跨越排除内存：合并={enabled}，结果={results:?}");
                assert!(results.iter().all(|v| v.starts_with("错误 BadWrite")), "排除内存必须始终拒绝");
            }
        }

        #[test]
        fn audit_truncate_lsb_all_representations_reject_large_lengths() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let bits = solver.declare_bitvector(8, info());
            let truncate = primop::binary_primops()["sail_truncateLSB"];
            for len in [9, 65, (1_i128 << 32) + 1, i128::MAX] {
                for value in [
                    Val::Bits(B64::new(1, 8)),
                    Val::Symbolic(bits),
                    Val::MixedBits(vec![crate::ir::BitsSegment::Symbolic(bits)]),
                ] {
                    let result = truncate(value, Val::I128(len), &mut solver, info());
                    assert!(matches!(result, Err(ExecError::Type(_, _))), "越界截断必须返回类型错误：{result:?}");
                }
            }
        }

        #[test]
        fn audit_integer_string_converters() {
            let mut all_preserved = true;
            for (name, expected) in [("hex_str", "0x1"), ("dec_str", "1")] {
                for enabled in [false, true] {
                    let branch = test_name(470);
                    let bits = test_name(471);
                    let integer = test_name(472);
                    let text = test_name(473);
                    let unary = primop::unary_primops::<B64>();
                    let results = run_all_with_shared_state(
                        vec![
                            Instr::Decl(branch, Ty::Bool, info()),
                            Instr::Decl(bits, Ty::Bits(8), info()),
                            Instr::Decl(integer, Ty::I128, info()),
                            Instr::Decl(text, Ty::String, info()),
                            Instr::Jump(Exp::Id(branch), 7, info()),
                            Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(1, 8)), info()),
                            Instr::Goto(8),
                            Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(2, 8)), info()),
                            Instr::PrimopUnary(Loc::Id(integer), unary["sail_unsigned"], Exp::Id(bits), info()),
                            Instr::PrimopUnary(Loc::Id(text), unary[name], Exp::Id(integer), info()),
                            Instr::PrimopBinary(
                                Loc::Id(RETURN),
                                primop::binary_primops()["eq_string"],
                                Exp::Id(text),
                                Exp::String(expected.into()),
                                info(),
                            ),
                            Instr::End,
                        ],
                        ExecutionLimits::default().with_path_merging(enabled),
                        empty_shared_state(),
                    );
                    let values: Vec<_> = results
                        .iter()
                        .map(|r| match r {
                            Ok(Run::Finished(v)) => format!("{v:?}"),
                            Err(e) => format!("错误 {e:?}"),
                            _ => panic!("异常结果"),
                        })
                        .collect();
                    eprintln!("字符串消费者={name}，合并={enabled}，结果={values:?}");
                    all_preserved &= results.iter().any(|r| matches!(r, Ok(Run::Finished(Val::Bool(true)))));
                }
            }
            assert!(all_preserved, "合法真分支不得丢失");
        }

        #[test]
        fn audit_merged_memory_write_addresses() {
            for enabled in [false, true] {
                let branch = test_name(470);
                let addr = test_name(471);
                let mut frame = make_frame(vec![
                    Instr::Decl(branch, Ty::Bool, info()),
                    Instr::Decl(addr, Ty::Bits(64), info()),
                    Instr::Jump(Exp::Id(branch), 5, info()),
                    Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0x1000, 64)), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0x1001, 64)), info()),
                    Instr::PrimopVariadic(
                        Loc::Id(RETURN),
                        primop::variadic_primops()["platform_write_mem"],
                        vec![Exp::Unit, Exp::I128(64), Exp::Id(addr), Exp::I128(1), Exp::Bits(B64::new(7, 8))],
                        info(),
                    ),
                    Instr::End,
                ]);
                frame.memory_mut().add_concrete_region(0x1000..0x1002, HashMap::from([(0x1000, 1), (0x1001, 2)]));
                let shared = empty_shared_state();
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let results = Mutex::new(Vec::new());
                start_single(frame.task(TaskId::fresh(), &state), &shared, &results, &|_, _, result, _, _, results| {
                    let value = match result {
                        Ok((Run::Finished(value), _)) => format!("完成 {value:?}"),
                        Err((error, _)) => format!("错误 {error:?}"),
                        _ => panic!("异常结果"),
                    };
                    results.lock().unwrap().push(value);
                });
                let results = results.into_inner().unwrap();
                eprintln!("多候选地址写入：合并={enabled}，结果={results:?}");
                assert!(results.iter().any(|v| v.starts_with("完成")), "合法写入必须完成");
            }
        }

        #[test]
        fn audit_truncate_lsb_error_does_not_panic() {
            for enabled in [false, true] {
                let outcome = std::panic::catch_unwind(|| {
                    let branch = test_name(470);
                    let bits = test_name(471);
                    let results = run_all_with_shared_state(
                        vec![
                            Instr::Decl(branch, Ty::Bool, info()),
                            Instr::Decl(bits, Ty::Bits(8), info()),
                            Instr::Jump(Exp::Id(branch), 5, info()),
                            Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(1, 8)), info()),
                            Instr::Goto(6),
                            Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(2, 8)), info()),
                            Instr::PrimopBinary(
                                Loc::Id(RETURN),
                                primop::binary_primops()["sail_truncateLSB"],
                                Exp::Id(bits),
                                Exp::I128(65),
                                info(),
                            ),
                            Instr::End,
                        ],
                        ExecutionLimits::default().with_path_merging(enabled),
                        empty_shared_state(),
                    );
                    for result in &results {
                        match result {
                            Err(error) => eprintln!("截断：合并={enabled}，错误={error:?}"),
                            _ => panic!("越界必须报错"),
                        }
                    }
                });
                eprintln!("截断：合并={enabled}，panic={}", outcome.is_err());
                assert!(outcome.is_ok(), "原本返回 ExecError 的路径不能导致进程 panic");
            }
        }

        #[test]
        fn audit_relaxed_vector_write_preserves_last_write() {
            for enabled in [false, true] {
                let mut shared = empty_shared_state();
                let r0 = shared.symtab.intern("zaudit16_relaxed0");
                let r1 = shared.symtab.intern("zaudit16_relaxed1");
                let branch = test_name(470);
                let index = test_name(471);
                let refs = test_name(472);
                let temp = test_name(473);
                let mut frame = make_frame(vec![
                    Instr::Decl(branch, Ty::Bool, info()),
                    Instr::Decl(index, Ty::Bits(8), info()),
                    Instr::Decl(temp, Ty::Unit, info()),
                    Instr::Jump(Exp::Id(branch), 6, info()),
                    Instr::Copy(Loc::Id(index), Exp::Bits(B64::new(0, 8)), info()),
                    Instr::Goto(7),
                    Instr::Copy(Loc::Id(index), Exp::Bits(B64::new(1, 8)), info()),
                    Instr::Call(
                        Loc::Id(temp),
                        false,
                        WRITE_REGISTER_FROM_VECTOR,
                        vec![Exp::Id(index), Exp::I128(7), Exp::Id(refs)],
                        info(),
                    ),
                    Instr::PrimopVariadic(
                        Loc::Id(temp),
                        primop::variadic_primops()["platform_synchronize_registers"],
                        vec![],
                        info(),
                    ),
                    Instr::PrimopBinary(
                        Loc::Id(RETURN),
                        primop::binary_primops()["eq_anything"],
                        Exp::Id(r0),
                        Exp::I128(0),
                        info(),
                    ),
                    Instr::End,
                ]);
                frame.lets_mut().insert(refs, UVal::Init(Val::Vector(vec![Val::Ref(r0), Val::Ref(r1)])));
                frame.regs_mut().insert(r0, true, UVal::Init(Val::I128(0)));
                frame.regs_mut().insert(r1, true, UVal::Init(Val::I128(10)));
                frame.regs_mut().assign(r0, Val::I128(1), &shared);
                frame.regs_mut().forget_last_reads();
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let results = Mutex::new(Vec::new());
                start_single(
                    frame.task(TaskId::fresh(), &state),
                    &shared,
                    &results,
                    &|_, _, result, _, mut solver, results| {
                        let value = match result {
                            Ok((Run::Finished(value), _)) => value,
                            Err((error, _)) => panic!("合法寄存器操作不能失败：{error:?}"),
                            _ => panic!("异常结果"),
                        };
                        let possible = solver
                            .check_sat_with(&crate::primop_util::smt_value(&value, info()).unwrap(), info())
                            .is_sat()
                            .unwrap();
                        results.lock().unwrap().push(possible);
                    },
                );
                let results = results.into_inner().unwrap();
                eprintln!("relaxed 寄存器同步后 r0=0 可达性：合并={enabled}，结果={results:?}");
                assert!(results.iter().all(|possible| !possible), "不能让未选中寄存器的旧值变成最后写入值");
            }
        }
        #[test]
        fn audit_crossing_excluded_memory() {
            for enabled in [false, true] {
                let branch = test_name(470);
                let addr = test_name(471);
                let mut frame = make_frame(vec![
                    Instr::Decl(branch, Ty::Bool, info()),
                    Instr::Decl(addr, Ty::Bits(64), info()),
                    Instr::Jump(Exp::Id(branch), 5, info()),
                    Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0x1000, 64)), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0xfff, 64)), info()),
                    Instr::PrimopVariadic(
                        Loc::Id(RETURN),
                        primop::variadic_primops()["platform_read_mem"],
                        vec![Exp::Unit, Exp::I128(64), Exp::Id(addr), Exp::I128(3)],
                        info(),
                    ),
                    Instr::End,
                ]);
                frame.memory_mut().add_region(crate::memory::Region::Excluded(0x1001..0x1002));
                let shared = empty_shared_state();
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let results = Mutex::new(Vec::new());
                start_single(frame.task(TaskId::fresh(), &state), &shared, &results, &|_, _, result, _, _, results| {
                    let value = match result {
                        Ok((Run::Finished(value), _)) => format!("完成 {value:?}"),
                        Err((error, _)) => format!("错误 {error:?}"),
                        _ => panic!("异常结果"),
                    };
                    results.lock().unwrap().push(value);
                });
                let results = results.into_inner().unwrap();
                eprintln!("跨越排除内存：合并={enabled}，结果={results:?}");
                assert!(results.iter().all(|v| v.starts_with("错误 BadRead")), "排除内存必须始终拒绝");
            }
        }

        #[test]
        fn audit_ifetch_default_memory() {
            for enabled in [false, true] {
                let branch = test_name(470);
                let addr = test_name(471);
                let results = run_all_with_shared_state(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(addr, Ty::Bits(64), info()),
                        Instr::Jump(Exp::Id(branch), 5, info()),
                        Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0x1000, 64)), info()),
                        Instr::Goto(6),
                        Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0x1001, 64)), info()),
                        Instr::PrimopVariadic(
                            Loc::Id(RETURN),
                            primop::variadic_primops()["platform_read_mem_ifetch"],
                            vec![Exp::Unit, Exp::I128(64), Exp::Id(addr), Exp::I128(1)],
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                );
                for result in &results {
                    match result {
                        Ok(Run::Finished(value)) => eprintln!("默认内存取指：合并={enabled}，完成={value:?}"),
                        Err(error) => eprintln!("默认内存取指：合并={enabled}，错误={error:?}"),
                        _ => panic!("异常结果"),
                    }
                }
                assert!(results.iter().all(|r| matches!(r, Err(ExecError::BadRead(_)))), "默认内存取指必须始终拒绝");
            }
        }
    }
    mod review15_tests {
        use super::*;

        #[derive(Clone)]
        pub(super) struct AuditDevice {
            pub(super) value: u8,
        }

        impl crate::memory::CustomRegion<B64> for AuditDevice {
            fn read(
                &self,
                read_kind: Val<B64>,
                address: u64,
                bytes: u32,
                solver: &mut Solver<B64>,
                tag: bool,
            ) -> Result<Val<B64>, ExecError> {
                let _ = (read_kind, address, bytes, solver, tag);
                Ok(Val::Bits(B64::from_u8(self.value)))
            }
            fn write(
                &mut self,
                write_kind: Val<B64>,
                address: u64,
                data: Val<B64>,
                solver: &mut Solver<B64>,
                tag: Option<Val<B64>>,
            ) -> Result<Val<B64>, ExecError> {
                let _ = (write_kind, address, solver, tag);
                let Val::Bits(data) = data else { panic!("设备测试只写入具体字节") };
                self.value = data.lower_u8();
                Ok(Val::Bool(true))
            }
            fn initial_value(&self, address: u64, bytes: u32) -> Option<B64> {
                let _ = (address, bytes);
                Some(B64::from_u8(self.value))
            }
            fn region_name(&self) -> &'static str {
                "审查设备"
            }
            fn clone_dyn(&self) -> Box<dyn Send + Sync + crate::memory::CustomRegion<B64>> {
                Box::new(self.clone())
            }
        }

        #[test]
        fn merged_custom_memory_write_preserves_device_state() {
            for enabled in [false, true] {
                let branch = test_name(450);
                let addr = test_name(451);
                let temp = test_name(452);
                let primops = primop::variadic_primops::<B64>();
                let mut frame = make_frame(vec![
                    Instr::Decl(branch, Ty::Bool, info()),
                    Instr::Decl(addr, Ty::Bits(64), info()),
                    Instr::Decl(temp, Ty::Bool, info()),
                    Instr::Jump(Exp::Id(branch), 6, info()),
                    Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0x1000, 64)), info()),
                    Instr::Goto(7),
                    Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0x1001, 64)), info()),
                    Instr::Jump(Exp::Id(branch), 10, info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(0, 8)), info()),
                    Instr::Goto(12),
                    Instr::PrimopVariadic(
                        Loc::Id(temp),
                        primops["platform_write_mem"],
                        vec![Exp::Unit, Exp::I128(64), Exp::Id(addr), Exp::I128(1), Exp::Bits(B64::new(7, 8))],
                        info(),
                    ),
                    Instr::PrimopVariadic(
                        Loc::Id(RETURN),
                        primops["platform_read_mem"],
                        vec![Exp::Unit, Exp::I128(64), Exp::Id(addr), Exp::I128(1)],
                        info(),
                    ),
                    Instr::End,
                ]);
                frame
                    .memory_mut()
                    .add_region(crate::memory::Region::Custom(0x1000..0x1002, Box::new(AuditDevice { value: 0 })));
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let shared = empty_shared_state();
                let collected = Mutex::new(Vec::new());
                start_single(
                    frame.task(TaskId::from_usize(0), &state),
                    &shared,
                    &collected,
                    &|tid, id, result, shared, solver, collected| {
                        let _ = (tid, id, shared, solver);
                        let value = match result {
                            Ok((Run::Finished(Val::Bits(bits)), _)) => bits.lower_u64(),
                            _ => panic!("设备读写必须完成"),
                        };
                        collected.lock().unwrap().push(value);
                    },
                );
                let mut values = collected.into_inner().unwrap();
                values.sort();
                eprintln!("设备写后读：合并={enabled}，结果={values:?}");
                assert_eq!(values, vec![0, 7], "合并不能跳过设备写入");
            }
        }

        #[test]
        fn merged_concrete_memory_addresses_preserve_reads() {
            for enabled in [false, true] {
                let branch = test_name(450);
                let addr = test_name(451);
                let mut frame = make_frame(vec![
                    Instr::Decl(branch, Ty::Bool, info()),
                    Instr::Decl(addr, Ty::Bits(64), info()),
                    Instr::Jump(Exp::Id(branch), 5, info()),
                    Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0x1000, 64)), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(addr), Exp::Bits(B64::new(0x1001, 64)), info()),
                    Instr::PrimopVariadic(
                        Loc::Id(RETURN),
                        primop::variadic_primops()["platform_read_mem"],
                        vec![Exp::Unit, Exp::I128(64), Exp::Id(addr), Exp::I128(1)],
                        info(),
                    ),
                    Instr::End,
                ]);
                frame.memory_mut().add_concrete_region(0x1000..0x1002, HashMap::from([(0x1000, 1), (0x1001, 2)]));
                let shared = empty_shared_state();
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let results = Mutex::new(Vec::new());
                start_single(frame.task(TaskId::fresh(), &state), &shared, &results, &|_, _, result, _, _, results| {
                    let outcome = match result {
                        Ok((Run::Finished(value), _)) => format!("完成 {value:?}"),
                        Err((error, _)) => format!("错误 {error:?}"),
                        _ => panic!("异常结果"),
                    };
                    results.lock().unwrap().push(outcome);
                });
                let results = results.into_inner().unwrap();
                eprintln!("具体内存的有限地址：合并={enabled}，结果={results:?}");
                assert_eq!(results.iter().filter(|r| r.starts_with("完成")).count(), 2);
            }
        }

        #[test]
        fn write_register_vector_strings_after_merge() {
            for enabled in [false, true] {
                let mut shared = empty_shared_state();
                let r0 = shared.symtab.intern("zaudit15_r0");
                let r1 = shared.symtab.intern("zaudit15_r1");
                let branch = test_name(450);
                let data = test_name(451);
                let refs = test_name(452);
                let mut lets = HashMap::default();
                lets.insert(refs, UVal::Init(Val::Vector(vec![Val::Ref(r0), Val::Ref(r1)])));
                let mut regs = RegisterBindings::new();
                regs.insert(r0, false, UVal::Init(Val::String("甲".into())));
                regs.insert(r1, false, UVal::Init(Val::String("乙".into())));
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Jump(Exp::Id(branch), 5, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(6),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::Call(
                            Loc::Id(RETURN),
                            false,
                            WRITE_REGISTER_FROM_VECTOR,
                            vec![Exp::Id(data), Exp::String("丙".into()), Exp::Id(refs)],
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    shared,
                    regs,
                    lets,
                );
                let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err()).collect();
                eprintln!(
                    "寄存器向量写入：合并={enabled}，完成={}，错误={errors:?}",
                    results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count()
                );
                assert!(errors.is_empty(), "合法具体索引写入不能因合并而失败");
            }
        }

        #[test]
        fn decimal_129_unique_merged_value() {
            use crate::bitvector::b129::B129;
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let c = solver.declare_const(smtlib::Ty::Bool, info());
            let f = primop::unary_primops::<B129>()["decimal_string_of_bits"];
            let left = Val::Bits(B129::new(1, 129));
            let right = Val::Bits(B129::new(2, 129));
            assert_eq!(f(left.clone(), &mut solver, info()).unwrap(), Val::String("1".into()));
            let merged = crate::primop_util::merge_val(c, &left, &right, &mut solver, info()).unwrap();
            solver.assert(smtlib::Exp::Var(c));
            let result = f(merged, &mut solver, info());
            eprintln!("129 位唯一候选的十进制转换：{result:?}");
            assert_eq!(result.unwrap(), Val::String("1".into()));
        }

        #[test]
        fn decimal_129_after_merge_preserves_paths() {
            use crate::bitvector::b129::B129;
            let branch = test_name(450);
            let data = test_name(451);
            let left = test_name(452);
            let right = test_name(453);
            for enabled in [false, true] {
                let instrs: Vec<Instr<Name, B129>> = vec![
                    Instr::Decl(branch, Ty::Bool, info()),
                    Instr::Decl(data, Ty::Bits(129), info()),
                    Instr::Jump(Exp::Id(branch), 5, info()),
                    Instr::Copy(Loc::Id(data), Exp::Id(left), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(data), Exp::Id(right), info()),
                    Instr::PrimopUnary(
                        Loc::Id(RETURN),
                        primop::unary_primops()["decimal_string_of_bits"],
                        Exp::Id(data),
                        info(),
                    ),
                    Instr::End,
                ];
                let shared = SharedState::<B129>::empty(Symtab::new());
                let mut frame = LocalFrame::new(test_name(25), &[], &Ty::String, None, &instrs);
                frame.lets_mut().insert(left, UVal::Init(Val::Bits(B129::new(1, 129))));
                frame.lets_mut().insert(right, UVal::Init(Val::Bits(B129::new(2, 129))));
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let results = Mutex::new(Vec::new());
                start_single(frame.task(TaskId::fresh(), &state), &shared, &results, &|_, _, result, _, _, results| {
                    let outcome = match result {
                        Ok((Run::Finished(value), _)) => format!("完成 {value:?}"),
                        Err((error, _)) => format!("错误 {error:?}"),
                        _ => panic!("异常结果"),
                    };
                    results.lock().unwrap().push(outcome);
                });
                let results = results.into_inner().unwrap();
                eprintln!("129 位十进制字符串：合并={enabled}，结果={results:?}");
                assert_eq!(results.iter().filter(|r| r.starts_with("完成")).count(), 2);
            }
        }

        #[test]
        fn wide_zero_padding_slice() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let source = solver.define_bitvector(primop::smt_ones(256), info());
            let start = solver.define_const(crate::primop_util::smt_i128(224), info());
            let symbolic =
                primop::op_slice(Val::Symbolic(source), Val::Symbolic(start), 128, &mut solver, info()).unwrap();
            let expected = smtlib::Exp::ZeroExtend(96, Box::new(primop::smt_ones(32)));
            assert!(solver
                .check_sat_with(
                    &smtlib::Exp::Neq(
                        Box::new(crate::primop_util::smt_value(&symbolic, info()).unwrap()),
                        Box::new(expected)
                    ),
                    info()
                )
                .is_unsat()
                .unwrap());
            let result = primop::op_slice(Val::Symbolic(source), Val::I128(224), 128, &mut solver, info());
            assert!(result.is_ok(), "宽位切片的补零必须使用符号位向量");
        }

        #[test]
        fn wide_slice_symbolic_start_matches_concrete_start() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let source = solver.define_bitvector(primop::smt_ones(256), info());
            let start = solver.define_const(crate::primop_util::smt_i128(256), info());
            assert!(primop::op_slice(Val::Symbolic(source), Val::Symbolic(start), 128, &mut solver, info()).is_ok());
            assert!(primop::op_slice(Val::Symbolic(source), Val::I128(256), 128, &mut solver, info()).is_ok());
        }
    }

    mod review15_boundary_tests {
        use super::*;

        #[test]
        fn symbolic_write_preserves_aliased_register_references() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let shared = empty_shared_state();
            let reg = test_name(460);
            let mut frame = make_frame(vec![]);
            frame.local_state.regs.insert(reg, false, UVal::Init(Val::I128(0)));
            let index = solver.declare_const(smtlib::Ty::BitVec(1), info());
            write_register_from_vector(
                Val::Symbolic(index),
                Val::I128(7),
                Val::Vector(vec![Val::Ref(reg), Val::Ref(reg)]),
                &mut frame.local_state,
                &shared,
                &mut solver,
                info(),
            )
            .unwrap();
            let result = frame.local_state.regs.get(reg, &shared, &mut solver, info()).unwrap().unwrap().clone();
            assert!(
                solver
                    .check_sat_with(
                        &smtlib::Exp::Neq(
                            Box::new(crate::primop_util::smt_value(&result, info()).unwrap()),
                            Box::new(crate::primop_util::smt_i128(7)),
                        ),
                        info(),
                    )
                    .is_unsat()
                    .unwrap(),
                "任一索引都必须更新同一个寄存器"
            );
        }
    }

    mod review14_tests {
        #[test]
        fn memory_read_bitvector_category_survives_checkpoint() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let value = crate::memory::Memory::new()
                .read(Val::Unit, Val::Bits(B64::new(0x1000, 64)), Val::I128(16), &mut solver, true, ReadOpts::default())
                .unwrap();
            let Val::Struct(fields) = value else { panic!("带标签读取必须返回结构体") };
            let replay = Solver::from_checkpoint(&ctx, checkpoint(&mut solver));
            for value in fields.values() {
                let Val::Symbolic(sym) = value else { panic!("读取结果必须为符号位向量") };
                assert!(replay.is_sail_bitvector(*sym), "检查点必须保留数据和标签的位向量类别");
            }
        }

        #[test]
        fn string_drop_retries_merged_length() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let n = solver.declare_const(smtlib::Ty::BitVec(128), info());
            let drop = primop::binary_primops()["string_drop"];
            assert!(matches!(
                drop(Val::String("abc".into()), Val::Symbolic(n), &mut solver, info()),
                Err(ExecError::SymbolicLength("string_drop", _))
            ));
            solver.assert_eq(smtlib::Exp::Var(n), crate::primop_util::smt_i128(1));
            assert_eq!(
                drop(Val::String("abc".into()), Val::Symbolic(n), &mut solver, info()).unwrap(),
                Val::String("bc".into())
            );
        }

        #[test]
        fn platform_read_memt_retries_merged_byte_count() {
            for enabled in [false, true] {
                let branch = test_name(400);
                let data = test_name(401);
                let bytes = test_name(402);
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(bytes, Ty::I128, info()),
                        Instr::Jump(Exp::Id(branch), 6, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(4, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(8, 8)), info()),
                        Instr::PrimopUnary(
                            Loc::Id(bytes),
                            primop::unary_primops()["sail_unsigned"],
                            Exp::Id(data),
                            info(),
                        ),
                        Instr::PrimopVariadic(
                            Loc::Id(RETURN),
                            primop::variadic_primops()["platform_read_memt"],
                            vec![Exp::Unit, Exp::Bits(B64::new(0x1000, 64)), Exp::Id(bytes)],
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                assert_eq!(results.len(), 2);
                assert!(
                    results.iter().all(|result| matches!(result, Ok(Run::Finished(Val::Struct(_))))),
                    "带标签的访存必须保留两个字节数候选"
                );
            }
        }

        #[test]
        fn read_mem_retries_merged_byte_count() {
            for enabled in [false, true] {
                let branch = test_name(400);
                let data = test_name(401);
                let bytes = test_name(402);
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(bytes, Ty::I128, info()),
                        Instr::Jump(Exp::Id(branch), 6, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(4, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(8, 8)), info()),
                        Instr::PrimopUnary(
                            Loc::Id(bytes),
                            primop::unary_primops()["sail_unsigned"],
                            Exp::Id(data),
                            info(),
                        ),
                        Instr::PrimopVariadic(
                            Loc::Id(RETURN),
                            primop::variadic_primops()["read_mem"],
                            vec![Exp::Unit, Exp::I128(64), Exp::Bits(B64::new(0x1000, 64)), Exp::Id(bytes)],
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                for result in &results {
                    match result {
                        Ok(Run::Finished(value)) => eprintln!("访存字节数：合并={enabled}，完成={value:?}"),
                        Err(error) => eprintln!("访存字节数：合并={enabled}，错误={error:?}"),
                        _ => panic!("异常结果"),
                    }
                }
                assert_eq!(results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count(), 2);
            }
        }

        #[test]
        fn string_take_retries_merged_length() {
            for enabled in [false, true] {
                let branch = test_name(400);
                let data = test_name(401);
                let len = test_name(402);
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(len, Ty::I128, info()),
                        Instr::Jump(Exp::Id(branch), 6, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(2, 8)), info()),
                        Instr::PrimopUnary(
                            Loc::Id(len),
                            primop::unary_primops()["sail_unsigned"],
                            Exp::Id(data),
                            info(),
                        ),
                        Instr::PrimopBinary(
                            Loc::Id(RETURN),
                            primop::binary_primops()["string_take"],
                            Exp::String("abc".into()),
                            Exp::Id(len),
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                for result in &results {
                    match result {
                        Ok(Run::Finished(value)) => eprintln!("字符串截取：合并={enabled}，完成={value:?}"),
                        Err(error) => eprintln!("字符串截取：合并={enabled}，错误={error:?}"),
                        _ => panic!("异常结果"),
                    }
                }
                assert_eq!(results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count(), 2);
            }
        }
        #[test]
        fn memory_bitvector_shift_keeps_unsigned_amount() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let memory = crate::memory::Memory::new();
            let shift = memory
                .read(
                    Val::Unit,
                    Val::Bits(B64::new(0x1000, 64)),
                    Val::I128(16),
                    &mut solver,
                    false,
                    ReadOpts::default(),
                )
                .unwrap();
            let Val::Symbolic(sym) = shift else { panic!("内存读取必须产生符号位向量") };
            solver.assert_eq(smtlib::Exp::Var(sym), primop::smt_ones(128));
            let f = primop::binary_primops()["arith_shiftr"];
            let actual = f(Val::Bits(B64::new(1, 8)), Val::Symbolic(sym), &mut solver, info()).unwrap();
            assert!(solver.check_sat(info()).is_sat().unwrap());
            let materialized = Model::new(&solver).get_val(&actual).unwrap();
            eprintln!("内存位向量移位：类别={}，实际={materialized:?}，预期=0", solver.is_sail_bitvector(sym));
            assert_eq!(materialized, Val::Bits(B64::new(0, 8)));
        }

        #[test]
        fn read_register_vector_retries_strings() {
            for enabled in [false, true] {
                let mut shared = empty_shared_state();
                let reg0 = shared.symtab.intern("zaudit_string_reg0");
                let reg1 = shared.symtab.intern("zaudit_string_reg1");
                let branch = test_name(400);
                let data = test_name(401);
                let index = test_name(402);
                let refs = test_name(403);
                let mut lets = HashMap::default();
                lets.insert(refs, UVal::Init(Val::Vector(vec![Val::Ref(reg0), Val::Ref(reg1)])));
                let mut regs = RegisterBindings::new();
                regs.insert(reg0, false, UVal::Init(Val::String("甲".into())));
                regs.insert(reg1, false, UVal::Init(Val::String("乙".into())));
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(index, Ty::I64, info()),
                        Instr::Jump(Exp::Id(branch), 6, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::Copy(Loc::Id(index), Exp::Call(Op::Unsigned(8), vec![Exp::Id(data)]), info()),
                        Instr::Call(
                            Loc::Id(RETURN),
                            false,
                            READ_REGISTER_FROM_VECTOR,
                            vec![Exp::Id(index), Exp::Id(refs)],
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    shared,
                    regs,
                    lets,
                );
                for result in &results {
                    match result {
                        Ok(Run::Finished(value)) => eprintln!("寄存器向量读取：合并={enabled}，完成={value:?}"),
                        Err(error) => eprintln!("寄存器向量读取：合并={enabled}，错误={error:?}"),
                        _ => panic!("异常结果"),
                    }
                }
                assert_eq!(results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count(), 2);
            }
        }
        use super::*;

        #[test]
        fn internal_vector_update_retries_merged_index() {
            for enabled in [false, true] {
                let branch = test_name(400);
                let data = test_name(401);
                let index = test_name(402);
                let vector = test_name(403);
                let mut lets = HashMap::default();
                lets.insert(vector, UVal::Init(Val::Vector(vec![Val::String("甲".into()), Val::String("乙".into())])));
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(index, Ty::I64, info()),
                        Instr::Jump(Exp::Id(branch), 6, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::Copy(Loc::Id(index), Exp::Call(Op::Unsigned(8), vec![Exp::Id(data)]), info()),
                        Instr::Call(
                            Loc::Id(RETURN),
                            false,
                            INTERNAL_VECTOR_UPDATE,
                            vec![Exp::Id(vector), Exp::Id(index), Exp::String("丙".into())],
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    lets,
                );
                for result in &results {
                    match result {
                        Ok(Run::Finished(value)) => eprintln!("内部向量更新：合并={enabled}，完成={value:?}"),
                        Err(error) => eprintln!("内部向量更新：合并={enabled}，错误={error:?}"),
                        _ => panic!("异常结果"),
                    }
                }
                assert_eq!(results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count(), 2);
            }
        }

        #[test]
        fn read_vreg_retries_merged_vrid() {
            for enabled in [false, true] {
                let branch = test_name(400);
                let data = test_name(401);
                let vrid = test_name(402);
                let mut args = vec![Exp::I128(1), Exp::I128(8), Exp::Id(vrid)];
                args.extend((0..8).map(|_| Exp::Bits(B64::zeros(64))));
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(vrid, Ty::I128, info()),
                        Instr::Jump(Exp::Id(branch), 6, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::PrimopUnary(
                            Loc::Id(vrid),
                            primop::unary_primops()["sail_unsigned"],
                            Exp::Id(data),
                            info(),
                        ),
                        Instr::PrimopVariadic(
                            Loc::Id(RETURN),
                            primop::variadic_primops()["isla_read_vreg"],
                            args,
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                for result in &results {
                    match result {
                        Ok(Run::Finished(value)) => eprintln!("向量寄存器编号：合并={enabled}，完成={value:?}"),
                        Err(error) => eprintln!("向量寄存器编号：合并={enabled}，错误={error:?}"),
                        _ => panic!("异常结果"),
                    }
                }
                assert_eq!(results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count(), 2);
            }
        }

        #[test]
        fn string_of_bits_keeps_129_bit_candidates() {
            use crate::bitvector::b129::B129;
            let branch = test_name(400);
            let data = test_name(401);
            let left = test_name(402);
            let right = test_name(403);
            for enabled in [false, true] {
                let instrs: Vec<Instr<Name, B129>> = vec![
                    Instr::Decl(branch, Ty::Bool, info()),
                    Instr::Decl(data, Ty::Bits(129), info()),
                    Instr::Jump(Exp::Id(branch), 5, info()),
                    Instr::Copy(Loc::Id(data), Exp::Id(left), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(data), Exp::Id(right), info()),
                    Instr::PrimopUnary(
                        Loc::Id(RETURN),
                        primop::unary_primops()["string_of_bits"],
                        Exp::Id(data),
                        info(),
                    ),
                    Instr::End,
                ];
                let shared = SharedState::<B129>::empty(Symtab::new());
                let mut frame = LocalFrame::new(test_name(25), &[], &Ty::String, None, &instrs);
                frame.lets_mut().insert(left, UVal::Init(Val::Bits(B129::new(1, 129))));
                frame.lets_mut().insert(right, UVal::Init(Val::Bits(B129::new(2, 129))));
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let results = Mutex::new(Vec::new());
                start_single(frame.task(TaskId::fresh(), &state), &shared, &results, &|_, _, result, _, _, results| {
                    let outcome = match result {
                        Ok((Run::Finished(value), _)) => format!("完成 {value:?}"),
                        Err((error, _)) => format!("错误 {error:?}"),
                        _ => panic!("异常结果"),
                    };
                    results.lock().unwrap().push(outcome);
                });
                let results = results.into_inner().unwrap();
                eprintln!("129位字符串：合并={enabled}，结果={results:?}");
                assert_eq!(results.iter().filter(|r| r.starts_with("完成")).count(), 2);
            }
        }
    }

    mod review13_tests {
        use super::*;

        #[test]
        fn nested_condition_retry_counts_control_flow_once() {
            let branch = test_name(340);
            let data = test_name(341);
            let index = test_name(342);
            let vector = test_name(343);
            let mut lets = HashMap::default();
            lets.insert(vector, UVal::Init(Val::Vector(vec![Val::List(vec![]), Val::List(vec![Val::Unit])])));
            let results = run_all_with_bindings(
                vec![
                    Instr::Decl(branch, Ty::Bool, info()),
                    Instr::Decl(data, Ty::Bits(8), info()),
                    Instr::Decl(index, Ty::I128, info()),
                    Instr::Jump(Exp::Id(branch), 6, info()),
                    Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0, 8)), info()),
                    Instr::Goto(8),
                    Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                    Instr::Goto(8),
                    Instr::PrimopUnary(Loc::Id(index), primop::unary_primops()["sail_unsigned"], Exp::Id(data), info()),
                    Instr::Jump(
                        Exp::Call(Op::IsEmpty, vec![Exp::Call(Op::Bvaccess, vec![Exp::Id(vector), Exp::Id(index)])]),
                        12,
                        info(),
                    ),
                    Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                    Instr::Goto(13),
                    Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
                    Instr::End,
                ],
                ExecutionLimits::default().with_path_merging(true).with_max_path_depth(4),
                empty_shared_state(),
                RegisterBindings::new(),
                lets,
            );
            assert_eq!(results.len(), 2);
            assert!(results.iter().any(|r| matches!(r, Ok(Run::Finished(Val::Bool(true))))));
            assert!(results.iter().any(|r| matches!(r, Ok(Run::Finished(Val::Bool(false))))));
        }

        #[test]
        fn nested_access_retry_continues_into_the_next_primop() {
            for enabled in [false, true] {
                let branch = test_name(330);
                let index = test_name(331);
                let data = test_name(332);
                let vector = test_name(333);
                let string = test_name(334);
                let mut lets = HashMap::default();
                lets.insert(vector, UVal::Init(Val::Vector(vec![Val::String("甲".into()), Val::String("乙".into())])));
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(index, Ty::I128, info()),
                        Instr::Decl(string, Ty::String, info()),
                        Instr::Jump(Exp::Id(branch), 7, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(8),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::PrimopUnary(
                            Loc::Id(index),
                            primop::unary_primops()["sail_unsigned"],
                            Exp::Id(data),
                            info(),
                        ),
                        Instr::Copy(
                            Loc::Id(string),
                            Exp::Call(Op::Bvaccess, vec![Exp::Id(vector), Exp::Id(index)]),
                            info(),
                        ),
                        Instr::PrimopUnary(
                            Loc::Id(RETURN),
                            primop::unary_primops()["string_length"],
                            Exp::Id(string),
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    lets,
                );
                assert_eq!(results.len(), 2);
                assert!(results.iter().all(|r| matches!(r, Ok(Run::Finished(Val::I128(3))))));
            }
        }

        #[test]
        fn machine_integer_models_preserve_negative_i64_and_i128() {
            for ty in [Ty::I64, Ty::I128] {
                let branch = test_name(330);
                let data = test_name(331);
                let integer = test_name(332);
                let conversion = if matches!(ty, Ty::I64) {
                    Instr::Copy(Loc::Id(integer), Exp::Call(Op::Signed(8), vec![Exp::Id(data)]), info())
                } else {
                    Instr::PrimopUnary(Loc::Id(integer), primop::unary_primops()["sail_signed"], Exp::Id(data), info())
                };
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(integer, ty.clone(), info()),
                        Instr::Jump(Exp::Id(branch), 6, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(255, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(128, 8)), info()),
                        conversion,
                        Instr::Monomorphize(integer, ty.clone(), info()),
                        Instr::Copy(Loc::Id(RETURN), Exp::Id(integer), info()),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(true),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                let mut values: Vec<i128> = results
                    .into_iter()
                    .map(|r| match (r.unwrap(), &ty) {
                        (Run::Finished(Val::I64(value)), Ty::I64) => i128::from(value),
                        (Run::Finished(Val::I128(value)), Ty::I128) => value,
                        _ => panic!("整数具体化结果类型错误"),
                    })
                    .collect();
                values.sort();
                assert_eq!(values, [-128, -1]);
            }
        }

        #[test]
        fn all_string_conversions_preserve_each_reachable_candidate() {
            for op in ["string_of_bits", "decimal_string_of_bits", "string_of_int"] {
                let mut outcomes = Vec::new();
                for enabled in [false, true] {
                    let branch = test_name(330);
                    let data = test_name(331);
                    let integer = test_name(332);
                    let results = run_all_with_bindings(
                        vec![
                            Instr::Decl(branch, Ty::Bool, info()),
                            Instr::Decl(data, Ty::Bits(8), info()),
                            Instr::Decl(integer, Ty::I128, info()),
                            Instr::Jump(Exp::Id(branch), 6, info()),
                            Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(255, 8)), info()),
                            Instr::Goto(7),
                            Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(128, 8)), info()),
                            Instr::PrimopUnary(
                                Loc::Id(integer),
                                primop::unary_primops()["sail_signed"],
                                Exp::Id(data),
                                info(),
                            ),
                            Instr::PrimopUnary(
                                Loc::Id(RETURN),
                                primop::unary_primops()[op],
                                Exp::Id(if op == "string_of_int" { integer } else { data }),
                                info(),
                            ),
                            Instr::End,
                        ],
                        ExecutionLimits::default().with_path_merging(enabled),
                        empty_shared_state(),
                        RegisterBindings::new(),
                        HashMap::default(),
                    );
                    let mut values: Vec<String> = results
                        .into_iter()
                        .map(|r| match r.unwrap() {
                            Run::Finished(Val::String(value)) => value,
                            _ => panic!("字符串转换结果类型错误"),
                        })
                        .collect();
                    values.sort();
                    assert_eq!(values.len(), 2);
                    outcomes.push(values);
                }
                assert_eq!(outcomes[0], outcomes[1], "转换算子：{op}");
            }
        }

        #[test]
        fn pack_vreg_symbolic_sew_preserves_legal_paths() {
            for enabled in [false, true] {
                let branch = test_name(330);
                let data = test_name(331);
                let sew = test_name(332);
                let vector = test_name(333);
                let mut lets = HashMap::default();
                lets.insert(vector, UVal::Init(Val::Vector(vec![])));
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(sew, Ty::I128, info()),
                        Instr::Jump(Exp::Id(branch), 6, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(8, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(16, 8)), info()),
                        Instr::PrimopUnary(
                            Loc::Id(sew),
                            primop::unary_primops()["sail_unsigned"],
                            Exp::Id(data),
                            info(),
                        ),
                        Instr::PrimopVariadic(
                            Loc::Id(data),
                            primop::variadic_primops()["isla_pack_vreg"],
                            vec![Exp::Id(sew), Exp::I128(64), Exp::Id(vector)],
                            info(),
                        ),
                        Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    lets,
                );
                assert_eq!(results.len(), 2);
                assert!(results.iter().all(|r| matches!(r, Ok(Run::Finished(Val::Unit)))));
            }
        }

        fn check_concrete_register_observer(observer: &str) {
            for enabled in [false, true] {
                let mut shared = empty_shared_state();
                let reg = shared.symtab.intern("zreview13_observed_register");
                let branch = test_name(320);
                let data = test_name(321);
                let mut instrs = vec![
                    Instr::Decl(branch, Ty::Bool, info()),
                    Instr::Decl(data, Ty::Bits(64), info()),
                    Instr::Jump(Exp::Id(branch), 5, info()),
                    Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0x1000, 64)), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0x2000, 64)), info()),
                    Instr::Copy(Loc::Id(reg), Exp::Id(data), info()),
                ];
                let mut task_state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                if observer == "pc_limit" {
                    task_state = task_state.with_pc_limit(reg, 1);
                    instrs.push(Instr::Call(
                        Loc::Id(RETURN),
                        false,
                        INSTR_ANNOUNCE,
                        vec![Exp::Bits(B64::new(0x13, 32))],
                        info(),
                    ));
                } else {
                    task_state.add_interrupt(TaskInterrupt::new(1, reg, B64::new(0x1000, 64), HashMap::new()));
                    instrs.push(Instr::Call(Loc::Id(RETURN), false, INTERRUPT_PENDING, vec![], info()));
                }
                instrs.push(Instr::End);
                let mut frame = make_frame(instrs);
                frame.regs_mut().insert(reg, false, UVal::Init(Val::Bits(B64::new(0, 64))));
                let results = std::sync::Mutex::new(Vec::new());
                start_single(
                    frame.task(TaskId::fresh(), &task_state),
                    &shared,
                    &results,
                    &|_, _, result, _, _, results| {
                        let outcome = match result {
                            Ok((Run::Finished(v), _)) => format!("完成 {v:?}"),
                            Err((error, _)) => format!("错误 {error:?}"),
                            _ => panic!("异常结果"),
                        };
                        results.lock().unwrap().push(outcome);
                    },
                );
                let results = results.into_inner().unwrap();
                eprintln!("寄存器观察：{observer}，合并={enabled}，结果={results:?}");
                assert_eq!(results.iter().filter(|r| r.starts_with("完成")).count(), 2);
            }
        }

        #[test]
        fn pc_limit_after_indirect_merged_write() {
            check_concrete_register_observer("pc_limit");
        }

        #[test]
        fn interrupt_after_merged_write() {
            check_concrete_register_observer("interrupt");
        }

        #[test]
        fn monomorphize_machine_integer_after_merge_does_not_crash() {
            for enabled in [false, true] {
                let branch = test_name(320);
                let data = test_name(321);
                let integer = test_name(322);
                let result = std::panic::catch_unwind(|| {
                    run_all_with_bindings(
                        vec![
                            Instr::Decl(branch, Ty::Bool, info()),
                            Instr::Decl(data, Ty::Bits(8), info()),
                            Instr::Decl(integer, Ty::I64, info()),
                            Instr::Jump(Exp::Id(branch), 6, info()),
                            Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                            Instr::Goto(7),
                            Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(2, 8)), info()),
                            Instr::Copy(Loc::Id(integer), Exp::Call(Op::Unsigned(8), vec![Exp::Id(data)]), info()),
                            Instr::Monomorphize(integer, Ty::I64, info()),
                            Instr::Copy(Loc::Id(RETURN), Exp::Id(integer), info()),
                            Instr::End,
                        ],
                        ExecutionLimits::default().with_path_merging(enabled),
                        empty_shared_state(),
                        RegisterBindings::new(),
                        HashMap::default(),
                    )
                });
                eprintln!("机器整数具体化：合并={enabled}，panic={}", result.is_err());
                assert!(result.is_ok());
                assert!(result.unwrap().iter().all(Result::is_ok));
            }
        }

        #[test]
        fn negative_integer_high_slice_matches_concrete_paths() {
            for enabled in [false, true] {
                let branch = test_name(320);
                let data = test_name(321);
                let integer = test_name(322);
                let slice = test_name(323);
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(integer, Ty::I128, info()),
                        Instr::Decl(slice, Ty::Bits(64), info()),
                        Instr::Jump(Exp::Id(branch), 7, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0xff, 8)), info()),
                        Instr::Goto(8),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0xfe, 8)), info()),
                        Instr::PrimopUnary(
                            Loc::Id(integer),
                            primop::unary_primops()["sail_signed"],
                            Exp::Id(data),
                            info(),
                        ),
                        Instr::PrimopVariadic(
                            Loc::Id(slice),
                            primop::variadic_primops()["get_slice_int"],
                            vec![Exp::I128(64), Exp::Id(integer), Exp::I128(96)],
                            info(),
                        ),
                        Instr::PrimopBinary(
                            Loc::Id(RETURN),
                            primop::binary_primops()["eq_bits"],
                            Exp::Id(slice),
                            Exp::Bits(B64::ones(64)),
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                for r in &results {
                    match r {
                        Ok(Run::Finished(v)) => eprintln!("负整数高位切片：合并={enabled}，返回={v:?}"),
                        Err(e) => eprintln!("负整数高位切片：合并={enabled}，错误={e:?}"),
                        _ => panic!("异常结果"),
                    }
                }
                assert!(
                    results.iter().all(|r| matches!(r, Ok(Run::Finished(Val::Bool(true))))),
                    "负整数超出最高位的切片必须符号扩展"
                );
            }
        }

        #[test]
        fn read_vreg_symbolic_sew_preserves_legal_paths() {
            for enabled in [false, true] {
                let branch = test_name(320);
                let data = test_name(321);
                let sew = test_name(322);
                let vector = test_name(323);
                let mut args = vec![Exp::I128(1), Exp::Id(sew), Exp::I128(0)];
                args.extend((0..8).map(|_| Exp::Bits(B64::zeros(64))));
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(sew, Ty::I128, info()),
                        Instr::Decl(vector, Ty::Vector(Box::new(Ty::AnyBits)), info()),
                        Instr::Jump(Exp::Id(branch), 7, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(8, 8)), info()),
                        Instr::Goto(8),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(16, 8)), info()),
                        Instr::PrimopUnary(
                            Loc::Id(sew),
                            primop::unary_primops()["sail_unsigned"],
                            Exp::Id(data),
                            info(),
                        ),
                        Instr::PrimopVariadic(
                            Loc::Id(vector),
                            primop::variadic_primops()["isla_read_vreg"],
                            args,
                            info(),
                        ),
                        Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                for r in &results {
                    match r {
                        Ok(Run::Finished(v)) => eprintln!("符号SEW：合并={enabled}，返回={v:?}"),
                        Err(e) => eprintln!("符号SEW：合并={enabled}，错误={e:?}"),
                        _ => panic!("异常结果"),
                    }
                }
                assert_eq!(results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count(), 2);
            }
        }

        #[test]
        fn nested_vector_access_preserves_both_legal_paths() {
            for enabled in [false, true] {
                let branch = test_name(320);
                let data = test_name(321);
                let index = test_name(322);
                let vector = test_name(323);
                let mut lets = HashMap::default();
                lets.insert(vector, UVal::Init(Val::Vector(vec![Val::String("左".into()), Val::String("右".into())])));
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(index, Ty::I128, info()),
                        Instr::Jump(Exp::Id(branch), 6, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::PrimopUnary(
                            Loc::Id(index),
                            primop::unary_primops()["sail_unsigned"],
                            Exp::Id(data),
                            info(),
                        ),
                        Instr::Copy(
                            Loc::Id(RETURN),
                            Exp::Call(Op::Bvaccess, vec![Exp::Id(vector), Exp::Id(index)]),
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    lets,
                );
                for r in &results {
                    match r {
                        Ok(Run::Finished(v)) => eprintln!("嵌套访问：合并={enabled}，返回={v:?}"),
                        Err(e) => eprintln!("嵌套访问：合并={enabled}，错误={e:?}"),
                        _ => panic!("异常结果"),
                    }
                }
                assert_eq!(results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count(), 2);
            }
        }

        #[test]
        fn vector_update_preserves_concrete_elements() {
            for enabled in [false, true] {
                let branch = test_name(320);
                let data = test_name(321);
                let index = test_name(322);
                let vector = test_name(323);
                let mut lets = HashMap::default();
                lets.insert(vector, UVal::Init(Val::Vector(vec![Val::String("甲".into()), Val::String("乙".into())])));
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(index, Ty::I128, info()),
                        Instr::Jump(Exp::Id(branch), 6, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::PrimopUnary(
                            Loc::Id(index),
                            primop::unary_primops()["sail_unsigned"],
                            Exp::Id(data),
                            info(),
                        ),
                        Instr::PrimopVariadic(
                            Loc::Id(RETURN),
                            primop::variadic_primops()["vector_update"],
                            vec![Exp::Id(vector), Exp::Id(index), Exp::String("丙".into())],
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    lets,
                );
                for r in &results {
                    match r {
                        Ok(Run::Finished(v)) => eprintln!("向量更新：合并={enabled}，返回={v:?}"),
                        Err(e) => eprintln!("向量更新：合并={enabled}，错误={e:?}"),
                        _ => panic!("异常结果"),
                    }
                }
                assert_eq!(results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count(), 2);
            }
        }

        #[test]
        fn string_conversion_must_preserve_reachable_true_result() {
            for enabled in [false, true] {
                let branch = test_name(320);
                let data = test_name(321);
                let string = test_name(322);
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(string, Ty::String, info()),
                        Instr::Jump(Exp::Id(branch), 6, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(2, 8)), info()),
                        Instr::PrimopUnary(
                            Loc::Id(string),
                            primop::unary_primops()["string_of_bits"],
                            Exp::Id(data),
                            info(),
                        ),
                        Instr::PrimopBinary(
                            Loc::Id(RETURN),
                            primop::binary_primops()["eq_string"],
                            Exp::Id(string),
                            Exp::String(B64::new(1, 8).to_string()),
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                for r in &results {
                    match r {
                        Ok(Run::Finished(v)) => eprintln!("字符串转换：合并={enabled}，返回={v:?}"),
                        Err(e) => eprintln!("字符串转换：合并={enabled}，错误={e:?}"),
                        _ => panic!("异常结果"),
                    }
                }
                assert!(
                    results.iter().any(|r| matches!(r, Ok(Run::Finished(Val::Bool(true))))),
                    "真实的相等路径不能丢失"
                );
            }
        }
    }

    mod review12_tests {
        use super::*;

        fn slice_program(enabled: bool) {
            let branch = test_name(310);
            let data = test_name(311);
            let slice = crate::primop::variadic_primops::<B64>()["slice"];
            let results = run_all_with_bindings(
                vec![
                    Instr::Decl(branch, Ty::Bool, info()),
                    Instr::Decl(data, Ty::Bits(8), info()),
                    Instr::Jump(Exp::Id(branch), 5, info()),
                    Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0x12, 8)), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0x34, 8)), info()),
                    Instr::PrimopVariadic(
                        Loc::Id(RETURN),
                        slice,
                        vec![Exp::Id(data), Exp::I128(8), Exp::I128(1)],
                        info(),
                    ),
                    Instr::End,
                ],
                ExecutionLimits::default().with_path_merging(enabled),
                empty_shared_state(),
                RegisterBindings::new(),
                HashMap::default(),
            );
            for result in &results {
                match result {
                    Ok(Run::Finished(value)) => eprintln!("合并={enabled}，返回={value:?}"),
                    Err(error) => eprintln!("合并={enabled}，错误={error:?}"),
                    _ => panic!("执行结果异常"),
                }
                assert!(matches!(result, Ok(Run::Finished(Val::Bits(value))) if *value == B64::new(0, 1)));
            }
        }

        #[test]
        fn special_primop_retry_counts_call_once() {
            for op in [INTERNAL_VECTOR_INIT, INSTR_ANNOUNCE] {
                let data = test_name(311);
                let vector = test_name(313);
                let arg = if op == INTERNAL_VECTOR_INIT {
                    Exp::Call(Op::Unsigned(1), vec![Exp::Id(data)])
                } else {
                    Exp::Id(data)
                };
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(data, Ty::Bits(1), info()),
                        Instr::Decl(vector, Ty::Vector(Box::new(Ty::Bool)), info()),
                        Instr::Call(Loc::Id(vector), false, op, vec![arg], info()),
                        Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_max_path_depth(1),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                assert_eq!(results.len(), 2);
                assert!(
                    results.iter().all(|r| matches!(r, Ok(Run::Finished(_) | Run::Exit))),
                    "内部重试不能重复计入 Call 深度"
                );
            }
        }

        #[test]
        fn slice_partial_zero_extension_indices() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let bits = solver.declare_bitvector(8, info());
            solver.assert_eq(smtlib::Exp::Var(bits), smtlib::Exp::Bits64(B64::new(0xd2, 8)));
            let inputs = [
                Val::Symbolic(bits),
                Val::Bits(B64::new(0xd2, 8)),
                Val::MixedBits(vec![
                    crate::ir::BitsSegment::Concrete(B64::new(0xd, 4)),
                    crate::ir::BitsSegment::Concrete(B64::new(2, 4)),
                ]),
            ];
            for input in inputs {
                for index in [Val::I64(6), Val::I128(6), Val::I64(8), Val::I128(i128::MAX)] {
                    let expected = if matches!(index, Val::I64(6) | Val::I128(6)) { 3 } else { 0 };
                    let value = primop::op_slice(input.clone(), index, 4, &mut solver, info()).unwrap();
                    assert_eq!(crate::primop_util::length_bits(&value, &mut solver, info()).unwrap(), 4);
                    let wrong = smtlib::Exp::Neq(
                        Box::new(crate::primop_util::smt_value(&value, info()).unwrap()),
                        Box::new(smtlib::Exp::Bits64(B64::new(expected, 4))),
                    );
                    assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
                }
            }
        }

        #[test]
        fn internal_conversion_retry_keeps_success_and_overflow() {
            let data = test_name(311);
            let results = run_all_with_bindings(
                vec![
                    Instr::Decl(data, Ty::Bits(128), info()),
                    Instr::PrimopUnary(
                        Loc::Id(data),
                        primop::unary_primops()["undefined_bitvector"],
                        Exp::I128(128),
                        info(),
                    ),
                    Instr::PrimopBinary(
                        Loc::Id(RETURN),
                        primop::binary_primops()["align_bits"],
                        Exp::Id(data),
                        Exp::I128(3),
                        info(),
                    ),
                    Instr::End,
                ],
                ExecutionLimits::default().with_path_merging(true),
                empty_shared_state(),
                RegisterBindings::new(),
                HashMap::default(),
            );
            assert_eq!(results.len(), 2);
            assert_eq!(results.iter().filter(|r| matches!(r, Err(ExecError::Overflow))).count(), 1);
            assert_eq!(results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count(), 1);
        }

        #[test]
        fn vector_access_concrete_only_elements_retry() {
            for values in [
                vec![Val::String("左".to_owned()), Val::String("右".to_owned())],
                vec![Val::Ref(test_name(301)), Val::Ref(test_name(302))],
                vec![Val::Vector(vec![Val::Bool(false)]), Val::Vector(vec![Val::Bool(true), Val::Bool(false)])],
            ] {
                let branch = test_name(310);
                let data = test_name(311);
                let index = test_name(312);
                let vector = test_name(313);
                let mut lets = HashMap::default();
                lets.insert(vector, UVal::Init(Val::Vector(values.clone())));
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(index, Ty::I128, info()),
                        Instr::Jump(Exp::Id(branch), 6, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::PrimopUnary(
                            Loc::Id(index),
                            primop::unary_primops()["sail_unsigned"],
                            Exp::Id(data),
                            info(),
                        ),
                        Instr::PrimopBinary(
                            Loc::Id(RETURN),
                            primop::binary_primops()["vector_access"],
                            Exp::Id(vector),
                            Exp::Id(index),
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(true),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    lets,
                );
                assert_eq!(results.len(), 2);
                for expected in values {
                    assert!(
                        results.iter().any(|r| matches!(r, Ok(Run::Finished(value)) if *value == expected)),
                        "必须按索引返回原元素"
                    );
                }
            }
        }

        #[test]
        fn slice_concrete_paths() {
            slice_program(false);
        }

        #[test]
        fn slice_after_merge() {
            slice_program(true);
        }

        #[test]
        fn small_index_vector() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let n = solver.declare_const(smtlib::Ty::BitVec(1), info());
            let value = primop::vector_access(
                Val::Vector((0..4).map(Val::I128).collect()),
                Val::Symbolic(n),
                &mut solver,
                info(),
            )
            .unwrap();
            eprintln!("向量结果={value:?}");
            solver.assert_eq(smtlib::Exp::Var(n), smtlib::Exp::Bits64(B64::BIT_ONE));
            let values = Val::Vector(vec![Val::String("左".to_owned()), Val::String("右".to_owned())]);
            assert_eq!(
                primop::vector_access(values, Val::Symbolic(n), &mut solver, info()).unwrap(),
                Val::String("右".to_owned())
            );
        }

        #[test]
        fn large_pow_exponent() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let b = solver.declare_const(smtlib::Ty::Bool, info());
            let bits = crate::primop_util::merge_val(
                b,
                &Val::Bits(B64::new(0, 8)),
                &Val::Bits(B64::new(1, 8)),
                &mut solver,
                info(),
            )
            .unwrap();
            let unsigned = crate::primop::unary_primops::<B64>()["sail_unsigned"];
            let pow = crate::primop::binary_primops::<B64>()["pow_int"];
            let base = unsigned(bits, &mut solver, info()).unwrap();
            let exp = Val::I128(1_i128 << 32);
            for x in [0, 1] {
                assert!(matches!(pow(Val::I128(x), exp.clone(), &mut solver, info()), Err(ExecError::Overflow)));
            }
            let result = pow(base, exp, &mut solver, info());
            eprintln!("合并后的幂={result:?}");
            assert!(matches!(result, Err(ExecError::Overflow)), "合并应保留逐分支的溢出结果");
        }

        #[test]
        fn zero_instruction_announce() {
            for enabled in [false, true] {
                let branch = test_name(310);
                let data = test_name(311);
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Jump(Exp::Id(branch), 5, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(6),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::Call(Loc::Id(RETURN), false, INSTR_ANNOUNCE, vec![Exp::Id(data)], info()),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                let exits = results.iter().filter(|r| matches!(r, Ok(Run::Exit))).count();
                let finished = results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count();
                eprintln!("合并={enabled}，Exit={exits}，Finished={finished}");
                assert_eq!(exits, 1, "必须保留零指令的停止路径");
                assert_eq!(finished, 1, "必须保留非零指令的继续路径");
            }
        }

        #[test]
        fn internal_vector_init_after_merge() {
            for enabled in [false, true] {
                let branch = test_name(310);
                let data = test_name(311);
                let length = test_name(312);
                let vector = test_name(313);
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(length, Ty::I64, info()),
                        Instr::Decl(vector, Ty::Vector(Box::new(Ty::Bool)), info()),
                        Instr::Jump(Exp::Id(branch), 7, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::Goto(8),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(2, 8)), info()),
                        Instr::Copy(Loc::Id(length), Exp::Call(Op::Unsigned(8), vec![Exp::Id(data)]), info()),
                        Instr::Call(Loc::Id(vector), false, INTERNAL_VECTOR_INIT, vec![Exp::Id(length)], info()),
                        Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                for result in &results {
                    if let Err(error) = result {
                        eprintln!("合并={enabled}，错误={error:?}");
                    }
                }
                let finished = results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count();
                eprintln!("合并={enabled}，正常路径={finished}");
                assert_eq!(finished, 2, "必须保留两条合法的向量长度路径");
                assert_eq!(results.len(), 2);
            }
        }

        #[test]
        fn read_vreg_length_after_merge() {
            for enabled in [false, true] {
                let branch = test_name(310);
                let data = test_name(311);
                let length = test_name(312);
                let vector = test_name(313);
                let unary = primop::unary_primops::<B64>();
                let variadic = primop::variadic_primops::<B64>();
                let mut args = vec![Exp::Id(length), Exp::I128(32), Exp::I128(0)];
                args.extend((0..8).map(|_| Exp::Bits(B64::new(0, 64))));
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(length, Ty::I128, info()),
                        Instr::Decl(vector, Ty::Vector(Box::new(Ty::Bits(32))), info()),
                        Instr::Jump(Exp::Id(branch), 7, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::Goto(8),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(2, 8)), info()),
                        Instr::PrimopUnary(Loc::Id(length), unary["sail_unsigned"], Exp::Id(data), info()),
                        Instr::PrimopVariadic(Loc::Id(vector), variadic["isla_read_vreg"], args, info()),
                        Instr::PrimopUnary(Loc::Id(RETURN), unary["length"], Exp::Id(vector), info()),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                let mut lengths = Vec::new();
                for result in results {
                    match result {
                        Ok(Run::Finished(Val::I128(n))) => lengths.push(n),
                        Err(error) => panic!("执行失败：{error:?}"),
                        _ => panic!("执行结果异常"),
                    }
                }
                lengths.sort_unstable();
                assert_eq!(lengths, vec![1, 2], "必须保留两个真实的候选长度");
                eprintln!("合并={enabled}，读取的向量长度={lengths:?}");
                assert!(lengths.iter().all(|n| [1, 2].contains(n)), "不能把动态长度替换为物理容量");
            }
        }

        #[test]
        fn mask_width_after_merge() {
            for enabled in [false, true] {
                let branch = test_name(310);
                let data = test_name(311);
                let length = test_name(312);
                let mask = test_name(313);
                let unary = primop::unary_primops::<B64>();
                let variadic = primop::variadic_primops::<B64>();
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(length, Ty::I128, info()),
                        Instr::Decl(mask, Ty::AnyBits, info()),
                        Instr::Jump(Exp::Id(branch), 7, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::Goto(8),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(2, 8)), info()),
                        Instr::PrimopUnary(Loc::Id(length), unary["sail_unsigned"], Exp::Id(data), info()),
                        Instr::PrimopVariadic(
                            Loc::Id(mask),
                            variadic["isla_mask_from_low_bits"],
                            vec![
                                Exp::Id(length),
                                Exp::Bits(B64::BIT_ZERO),
                                Exp::Bits(B64::BIT_ZERO),
                                Exp::Bits(B64::new(3, 8)),
                            ],
                            info(),
                        ),
                        Instr::PrimopUnary(Loc::Id(RETURN), unary["length"], Exp::Id(mask), info()),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                let mut lengths = Vec::new();
                for result in results {
                    match result {
                        Ok(Run::Finished(Val::I128(n))) => lengths.push(n),
                        Err(error) => panic!("执行失败：{error:?}"),
                        _ => panic!("执行结果异常"),
                    }
                }
                lengths.sort_unstable();
                assert_eq!(lengths, vec![1, 2], "必须保留两种结果位宽");
                eprintln!("合并={enabled}，掩码长度={lengths:?}");
                assert!(lengths.iter().all(|n| [1, 2].contains(n)), "不能把动态结果位宽替换为源位宽");
            }
        }

        #[test]
        fn nested_vector_access_after_merge() {
            for enabled in [false, true] {
                let mut shared = empty_shared_state();
                let vector = shared.symtab.intern("zreview12_nested_vector");
                let branch = test_name(310);
                let data = test_name(311);
                let index = test_name(312);
                let unary = primop::unary_primops::<B64>();
                let binary = primop::binary_primops::<B64>();
                let mut lets = HashMap::default();
                lets.insert(
                    vector,
                    UVal::Init(Val::Vector(vec![
                        Val::Vector(vec![Val::Bool(false)]),
                        Val::Vector(vec![Val::Bool(true)]),
                    ])),
                );
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(index, Ty::I128, info()),
                        Instr::Jump(Exp::Id(branch), 6, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::PrimopUnary(Loc::Id(index), unary["sail_unsigned"], Exp::Id(data), info()),
                        Instr::PrimopBinary(
                            Loc::Id(RETURN),
                            binary["vector_access"],
                            Exp::Id(vector),
                            Exp::Id(index),
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    shared,
                    RegisterBindings::new(),
                    lets,
                );
                for result in &results {
                    if let Err(error) = result {
                        eprintln!("合并={enabled}，错误={error:?}");
                    }
                }
                let finished = results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count();
                eprintln!("合并={enabled}，嵌套向量正常路径={finished}");
                assert!(finished > 0, "向量元素为向量时也必须保留合法索引路径");
            }
        }

        #[test]
        fn align_overflow_after_merge() {
            for enabled in [false, true] {
                let branch = test_name(310);
                let data = test_name(311);
                let binary = primop::binary_primops::<B64>();
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Jump(Exp::Id(branch), 5, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(6),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::PrimopBinary(
                            Loc::Id(RETURN),
                            binary["align_bits"],
                            Exp::Id(data),
                            Exp::I128(512),
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                for result in &results {
                    match result {
                        Ok(Run::Finished(value)) => assert_eq!(*value, Val::Bits(B64::zeros(8))),
                        Err(error) => panic!("对齐失败：{error:?}"),
                        _ => panic!("执行结果异常"),
                    }
                }
            }
        }

        #[test]
        fn pow_valid_exponent_cost() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let b = solver.declare_const(smtlib::Ty::Bool, info());
            let bits = crate::primop_util::merge_val(
                b,
                &Val::Bits(B64::new(0, 8)),
                &Val::Bits(B64::new(1, 8)),
                &mut solver,
                info(),
            )
            .unwrap();
            let unsigned = crate::primop::unary_primops::<B64>()["sail_unsigned"];
            let pow = crate::primop::binary_primops::<B64>()["pow_int"];
            let base = unsigned(bits, &mut solver, info()).unwrap();
            for exp in [1_i128 << 20, i128::from(u32::MAX)] {
                for x in [0, 1] {
                    assert_eq!(pow(Val::I128(x), Val::I128(exp), &mut solver, info()).unwrap(), Val::I128(x));
                }
                let started = Instant::now();
                let result = pow(base.clone(), Val::I128(exp), &mut solver, info()).unwrap();
                let expression = crate::primop_util::smt_value(&result, info()).unwrap();
                assert!(solver.exp_to_str(&expression).len() < 256, "实际 Z3 表达式必须使用共享常量");
                for (condition, expected) in
                    [(smtlib::Exp::Var(b), 0), (smtlib::Exp::Not(Box::new(smtlib::Exp::Var(b))), 1)]
                {
                    let wrong = smtlib::Exp::And(
                        Box::new(condition),
                        Box::new(smtlib::Exp::Neq(
                            Box::new(expression.clone()),
                            Box::new(crate::primop_util::smt_i128(expected)),
                        )),
                    );
                    assert_eq!(
                        solver.check_sat_with(&wrong, info()),
                        crate::smt::SmtResult::Unsat,
                        "指数 {exp} 的结果必须与具体路径一致"
                    );
                }
                eprintln!("有效指数={exp}，合并幂结果={result:?}，构造与校验耗时={:?}", started.elapsed());
            }
        }

        #[test]
        fn pc_limit_after_merge() {
            for enabled in [false, true] {
                let mut shared = empty_shared_state();
                let pc = shared.symtab.intern("zreview12_pc");
                let branch = test_name(310);
                let mut frame = make_frame(vec![
                    Instr::Decl(branch, Ty::Bool, info()),
                    Instr::Jump(Exp::Id(branch), 4, info()),
                    Instr::Copy(Loc::Id(pc), Exp::Bits(B64::new(0x1000, 64)), info()),
                    Instr::Goto(5),
                    Instr::Copy(Loc::Id(pc), Exp::Bits(B64::new(0x2000, 64)), info()),
                    Instr::Call(Loc::Id(RETURN), false, INSTR_ANNOUNCE, vec![Exp::Bits(B64::new(0x13, 32))], info()),
                    Instr::End,
                ]);
                frame.regs_mut().insert(pc, false, UVal::Init(Val::Bits(B64::new(0, 64))));
                let task_state = TaskState::new()
                    .with_pc_limit(pc, 1)
                    .with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let results = std::sync::Mutex::new(Vec::new());
                start_single(
                    frame.task(TaskId::fresh(), &task_state),
                    &shared,
                    &results,
                    &|_, _, result, _, _, results| {
                        let outcome = match result {
                            Ok((Run::Finished(_), _)) => "完成".to_owned(),
                            Err((error, _)) => format!("{error:?}"),
                            _ => panic!("执行结果异常"),
                        };
                        results.lock().unwrap().push(outcome);
                    },
                );
                let outcomes = results.into_inner().unwrap();
                eprintln!("合并={enabled}，PC 预算结果={outcomes:?}");
                assert!(outcomes.iter().all(|outcome| outcome == "完成"), "第一次访问每个 PC 不得报错");
            }
        }

        #[test]
        fn align_internal_conversion_prunes_overflow() {
            use crate::bitvector::b129::B129;
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let good = Val::Bits(B129::zeros(128));
            let bad = Val::Bits(B129::ones(128));
            let align = primop::binary_primops::<B129>()["align_bits"];
            assert!(align(good.clone(), Val::I128(3), &mut solver, info()).is_ok());
            assert!(matches!(align(bad.clone(), Val::I128(3), &mut solver, info()), Err(ExecError::Overflow)));
            let merged = crate::primop_util::merge_val(cond, &good, &bad, &mut solver, info()).unwrap();
            let result = align(merged, Val::I128(3), &mut solver, info());
            let overflow_path = solver.check_sat_with(&smtlib::Exp::Not(Box::new(smtlib::Exp::Var(cond))), info());
            eprintln!("内部转换合并结果={result:?}，溢出分支可满足性={overflow_path:?}");
            assert_eq!(overflow_path, crate::smt::SmtResult::Sat, "不得直接加入可表示断言并删除溢出路径");
        }

        #[test]
        fn large_pow_exponent_after_merge_fast() {
            for enabled in [false, true] {
                let branch = test_name(310);
                let data = test_name(311);
                let integer = test_name(312);
                let unary = primop::unary_primops::<B64>();
                let binary = primop::binary_primops::<B64>();
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(branch, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(8), info()),
                        Instr::Decl(integer, Ty::I128, info()),
                        Instr::Jump(Exp::Id(branch), 6, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::PrimopUnary(Loc::Id(integer), unary["sail_unsigned"], Exp::Id(data), info()),
                        Instr::PrimopBinary(
                            Loc::Id(integer),
                            binary["sub_int"],
                            Exp::Id(integer),
                            Exp::Id(integer),
                            info(),
                        ),
                        Instr::PrimopBinary(
                            Loc::Id(RETURN),
                            binary["pow_int"],
                            Exp::Id(integer),
                            Exp::I128(1_i128 << 32),
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                for result in &results {
                    match result {
                        Ok(Run::Finished(value)) => eprintln!("合并={enabled}，幂结果={value:?}"),
                        Err(error) => eprintln!("合并={enabled}，幂错误={error:?}"),
                        _ => panic!("执行结果异常"),
                    }
                }
                assert!(
                    results.iter().all(|r| matches!(r, Err(ExecError::Overflow))),
                    "指数表示范围不能取决于底数是否为符号值"
                );
            }
        }
    }

    mod review11_tests {

        #[test]
        fn review11_conversion_range_forks() {
            for (name, width) in [("sail_unsigned", 128), ("sail_unsigned", 129), ("sail_signed", 129)] {
                let data = test_name(303);
                let unary = crate::primop::unary_primops::<B64>();
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(data, Ty::Bits(width), info()),
                        Instr::PrimopUnary(
                            Loc::Id(data),
                            unary["undefined_bitvector"],
                            Exp::I128(width as i128),
                            info(),
                        ),
                        Instr::PrimopUnary(Loc::Id(RETURN), unary[name], Exp::Id(data), info()),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(true),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                assert_eq!(results.len(), 2, "{name} bv{width}");
                assert_eq!(results.iter().filter(|result| matches!(result, Err(ExecError::Overflow))).count(), 1);
                assert_eq!(results.iter().filter(|result| matches!(result, Ok(Run::Finished(_)))).count(), 1);
            }
        }

        #[test]
        fn review11_integer_slice_result_category() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let integer = solver.declare_const(smtlib::Ty::BitVec(128), info());
            let ops = crate::primop::variadic_primops::<B64>();
            let mut frame = make_frame(vec![Instr::End]);
            let result = ops["set_slice_int"](
                vec![Val::I128(1), Val::Symbolic(integer), Val::I128(0), Val::Bits(B64::BIT_ONE)],
                &mut solver,
                &mut frame,
                info(),
            )
            .unwrap();
            let Val::Symbolic(sym) = result else { panic!("预期符号整数") };
            assert!(!solver.is_sail_bitvector(sym));
        }

        #[test]
        fn review11_bit_access_original_index_bounds() {
            for mixed in [false, true] {
                let ctx = Context::new(Config::new());
                let mut solver = Solver::<B64>::new(&ctx);
                let input = if mixed {
                    Val::MixedBits(vec![
                        crate::ir::BitsSegment::Symbolic(solver.declare_bitvector(4, info())),
                        crate::ir::BitsSegment::Concrete(B64::zeros(4)),
                    ])
                } else {
                    Val::Bits(B64::zeros(8))
                };
                for index in [-1, 8, 256, 1i128 << 64] {
                    assert!(matches!(
                        crate::primop::vector_access(input.clone(), Val::I128(index), &mut solver, info()),
                        Err(ExecError::OutOfBounds(_))
                    ));
                }
                let index = solver.define_const(crate::primop_util::smt_i128(256), info());
                assert!(matches!(
                    crate::primop::vector_access(input, Val::Symbolic(index), &mut solver, info()),
                    Err(ExecError::OutOfBounds(_))
                ));
            }
        }

        #[test]
        fn review11_slice_indices_do_not_wrap() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let index = solver.declare_const(smtlib::Ty::BitVec(128), info());
            solver.assert_eq(smtlib::Exp::Var(index), crate::primop_util::smt_i128(256));
            let value = solver.define_bitvector(crate::primop_util::smt_sbits(B64::new(0xff, 8)), info());
            let slice =
                crate::primop::op_slice(Val::Symbolic(value), Val::Symbolic(index), 1, &mut solver, info()).unwrap();
            let updated = crate::primop::set_slice_internal(
                Val::Symbolic(value),
                Val::Symbolic(index),
                Val::Bits(B64::zeros(1)),
                &mut solver,
                info(),
            )
            .unwrap();
            for (result, expected) in [(slice, B64::zeros(1)), (updated, B64::new(0xff, 8))] {
                let wrong = smtlib::Exp::Neq(
                    Box::new(crate::primop_util::smt_value(&result, info()).unwrap()),
                    Box::new(crate::primop_util::smt_sbits(expected)),
                );
                assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
            }
        }

        #[test]
        fn review11_bitvector_categories_and_replay() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let input = Val::Symbolic(solver.declare_bitvector(128, info()));
            let unary = crate::primop::unary_primops::<B129>();
            let binary = crate::primop::binary_primops::<B129>();
            let mut results = vec![unary["not_bits"](input.clone(), &mut solver, info()).unwrap()];
            for name in ["xor_bits", "or_bits", "and_bits", "add_bits", "sub_bits"] {
                results.push(binary[name](input.clone(), input.clone(), &mut solver, info()).unwrap());
            }
            for name in ["add_bits_int", "sub_bits_int", "shiftl", "shiftr", "arith_shiftr"] {
                results.push(binary[name](input.clone(), Val::I128(1), &mut solver, info()).unwrap());
            }
            results.push(crate::primop::op_slice(input.clone(), Val::I64(0), 64, &mut solver, info()).unwrap());
            results.push(crate::primop::append(input.clone(), input.clone(), &mut solver, info()).unwrap());
            for name in ["zero_extend", "sign_extend"] {
                results.push(binary[name](input.clone(), Val::I128(129), &mut solver, info()).unwrap());
            }
            for result in &results {
                let Val::Symbolic(sym) = result else { panic!("预期符号位向量") };
                assert!(solver.is_sail_bitvector(*sym));
            }
            let signed = unary["sail_signed"](input.clone(), &mut solver, info()).unwrap();
            let unsigned = unary["sail_unsigned"](input.clone(), &mut solver, info());
            let Err(ExecError::IntegerConversion(in_range, _)) = unsigned else {
                panic!("无约束的 128 位 unsigned 必须检查范围")
            };
            solver.assert(in_range);
            let unsigned = unary["sail_unsigned"](input, &mut solver, info()).unwrap();
            let integer_input = Val::Symbolic(solver.declare_bitvector(8, info()));
            let clz = unary["count_leading_zeros"](integer_input.clone(), &mut solver, info()).unwrap();
            let ctz = unary["count_trailing_zeros"](integer_input, &mut solver, info()).unwrap();
            for value in [signed, unsigned, clz, ctz] {
                let Val::Symbolic(sym) = value else { panic!("预期符号整数") };
                assert!(!solver.is_sail_bitvector(sym));
            }
            let raw = solver.declare_const(smtlib::Ty::BitVec(128), info());
            let before_mark = checkpoint(&mut solver);
            solver.mark_bitvector(raw);
            assert!(!Solver::from_checkpoint(&ctx, before_mark).is_sail_bitvector(raw));
            let point = checkpoint(&mut solver);
            let replay = Solver::from_checkpoint(&ctx, point);
            assert!(replay.is_sail_bitvector(raw));
            for result in results {
                let Val::Symbolic(sym) = result else { unreachable!() };
                assert!(replay.is_sail_bitvector(sym));
            }
        }

        #[test]
        fn review11_zero_width_operations() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let input = Val::Symbolic(solver.declare_bitvector(8, info()));
            let integer = Val::Symbolic(solver.declare_const(smtlib::Ty::BitVec(128), info()));
            let ops = crate::primop::binary_primops::<B64>();
            for name in ["shift_bits_left", "shift_bits_right", "arith_shiftr", "shiftl", "shiftr"] {
                assert_eq!(ops[name](input.clone(), Val::Bits(B64::zeros(0)), &mut solver, info()).unwrap(), input);
            }
            for name in ["add_bits_int", "sub_bits_int"] {
                assert_eq!(
                    ops[name](Val::Bits(B64::zeros(0)), integer.clone(), &mut solver, info()).unwrap(),
                    Val::Bits(B64::zeros(0))
                );
            }
        }

        #[test]
        fn review11_equality_width_matrix() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let a = solver.declare_bitvector(8, info());
            let b = solver.declare_bitvector(16, info());
            let low = solver.declare_bitvector(4, info());
            let mixed = Val::MixedBits(vec![
                crate::ir::BitsSegment::Symbolic(low),
                crate::ir::BitsSegment::Concrete(B64::zeros(4)),
            ]);
            let ops = crate::primop::binary_primops::<B64>();
            for name in ["eq_bits", "neq_bits", "eq_anything", "%neq"] {
                let op = if name == "%neq" { crate::primop::op_neq::<B64> } else { *ops.get(name).unwrap() };
                for left in [Val::Symbolic(a), Val::Bits(B64::zeros(8)), mixed.clone()] {
                    for right in [Val::Symbolic(b), Val::Bits(B64::zeros(16))] {
                        assert_eq!(
                            op(left.clone(), right.clone(), &mut solver, info()).unwrap(),
                            Val::Bool(name.contains("neq"))
                        );
                        assert_eq!(
                            op(right, left.clone(), &mut solver, info()).unwrap(),
                            Val::Bool(name.contains("neq"))
                        );
                    }
                }
            }
        }

        #[test]
        fn review11_signed_129_boundaries() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let signed = *crate::primop::unary_primops::<B129>().get("sail_signed").unwrap();
            for value in [i128::MIN, -1, 0, i128::MAX] {
                let bits = B129::from_str(&format!("0x{:032x}", value as u128)).unwrap().sign_extend(129);
                assert_eq!(signed(Val::Bits(bits), &mut solver, info()).unwrap(), Val::I128(value));
            }
            for bits in [B129::new(1, 129).shiftl(127), B129::new(1, 129).shiftl(128)] {
                assert!(matches!(signed(Val::Bits(bits), &mut solver, info()), Err(ExecError::Overflow)));
            }
        }

        #[test]
        fn review11_ctz_width_boundaries() {
            for width in [0, 1, 8, 64, 128, 129] {
                assert_eq!(B129::zeros(width).trailing_zeros(), width);
            }
            assert_eq!(B129::new(1, 129).shiftl(128).trailing_zeros(), 128);
        }

        #[test]
        fn review11_run_loop_narrow_overflow() {
            for enabled in [false, true] {
                let cond = test_name(300);
                let data = test_name(301);
                let integer = test_name(302);
                let unsigned = *crate::primop::unary_primops::<B64>().get("sail_unsigned").unwrap();
                let narrow = *crate::primop::unary_primops::<B64>().get("%i->%i64").unwrap();
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(cond, Ty::Bool, info()),
                        Instr::Decl(data, Ty::Bits(64), info()),
                        Instr::Decl(integer, Ty::I128, info()),
                        Instr::Jump(Exp::Id(cond), 6, info()),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1, 64)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(data), Exp::Bits(B64::new(1u64 << 63, 64)), info()),
                        Instr::PrimopUnary(Loc::Id(integer), unsigned, Exp::Id(data), info()),
                        Instr::PrimopUnary(Loc::Id(RETURN), narrow, Exp::Id(integer), info()),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                let overflows = results.iter().filter(|result| matches!(result, Err(ExecError::Overflow))).count();
                let finished = results.iter().filter(|result| matches!(result, Ok(Run::Finished(_)))).count();
                eprintln!("实际执行：合并={enabled}，路径数={}，溢出={overflows}，完成={finished}", results.len());
                assert_eq!(overflows, 1, "合并不能把溢出分支变成成功执行");
            }
        }

        #[test]
        fn review11_unsigned_mixed_128() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let unsigned = *crate::primop::unary_primops::<B129>().get("sail_unsigned").unwrap();
            assert_eq!(unsigned(Val::Bits(B129::new(1, 128)), &mut solver, info()).unwrap(), Val::I128(1));
            let value = crate::primop_util::merge_val(
                cond,
                &Val::Bits(B129::new(1, 128)),
                &Val::Bits(B129::ones(128)),
                &mut solver,
                info(),
            )
            .unwrap();
            let result = unsigned(value, &mut solver, info());
            eprintln!("混合可表示值与溢出值的 unsigned={result:?}");
            let Err(ExecError::IntegerConversion(in_range, _)) = result else {
                panic!("混合范围必须请求执行器分叉")
            };
            assert_eq!(solver.check_sat_with(&smtlib::Exp::Var(cond), info()), crate::smt::SmtResult::Sat);
            assert_eq!(
                solver.check_sat_with(&smtlib::Exp::Not(Box::new(smtlib::Exp::Var(cond))), info()),
                crate::smt::SmtResult::Sat
            );
            solver.assert(in_range);
            assert_eq!(
                solver.check_sat_with(&smtlib::Exp::Not(Box::new(smtlib::Exp::Var(cond))), info()),
                crate::smt::SmtResult::Unsat
            );
        }

        #[test]
        fn review11_ctz_b129_zero() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let ctz = *crate::primop::unary_primops::<B129>().get("count_trailing_zeros").unwrap();
            let expected = ctz(Val::Bits(B129::zeros(8)), &mut solver, info()).unwrap();
            let input = crate::primop_util::merge_val(
                cond,
                &Val::Bits(B129::zeros(8)),
                &Val::Bits(B129::new(1, 8)),
                &mut solver,
                info(),
            )
            .unwrap();
            let result = ctz(input, &mut solver, info()).unwrap();
            solver.assert(smtlib::Exp::Var(cond));
            assert_eq!(solver.check_sat(info()), crate::smt::SmtResult::Sat);
            eprintln!("B129 ctz(0:bv8) 单臂={expected:?}，合并={:?}", Model::new(&solver).get_val(&result).unwrap());
            let wrong = smtlib::Exp::Neq(
                Box::new(crate::primop_util::smt_value(&result, info()).unwrap()),
                Box::new(crate::primop_util::smt_value(&expected, info()).unwrap()),
            );
            assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
        }

        #[test]
        fn review11_empty_shift_amount() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let shift = crate::primop::shift_bits_right::<B64>;
            for n in [1, 2] {
                assert_eq!(
                    shift(Val::Bits(B64::new(n, 8)), Val::Bits(B64::zeros(0)), &mut solver, info()).unwrap(),
                    Val::Bits(B64::new(n, 8))
                );
            }
            let value = crate::primop_util::merge_val(
                cond,
                &Val::Bits(B64::new(1, 8)),
                &Val::Bits(B64::new(2, 8)),
                &mut solver,
                info(),
            )
            .unwrap();
            assert!(shift(value, Val::Bits(B64::zeros(0)), &mut solver, info()).is_ok());
        }

        #[test]
        fn review11_zero_width_add_int() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let add = *crate::primop::binary_primops::<B64>().get("add_bits_int").unwrap();
            let unsigned = *crate::primop::unary_primops::<B64>().get("sail_unsigned").unwrap();
            for n in [0, 1] {
                assert_eq!(
                    add(Val::Bits(B64::zeros(0)), Val::I128(n), &mut solver, info()).unwrap(),
                    Val::Bits(B64::zeros(0))
                );
            }
            let amount = crate::primop_util::merge_val(
                cond,
                &Val::Bits(B64::new(0, 8)),
                &Val::Bits(B64::new(1, 8)),
                &mut solver,
                info(),
            )
            .unwrap();
            let amount = unsigned(amount, &mut solver, info()).unwrap();
            assert!(add(Val::Bits(B64::zeros(0)), amount, &mut solver, info()).is_ok());
        }

        #[test]
        fn review11_narrow_overflow() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let unsigned = *crate::primop::unary_primops::<B64>().get("sail_unsigned").unwrap();
            let narrow = *crate::primop::unary_primops::<B64>().get("%i->%i64").unwrap();
            let too_big = Val::Bits(B64::new(1u64 << 63, 64));
            let concrete = unsigned(too_big.clone(), &mut solver, info()).unwrap();
            assert!(matches!(narrow(concrete, &mut solver, info()), Err(ExecError::Overflow)));
            let value = crate::primop_util::merge_val(cond, &too_big, &Val::Bits(B64::new(1, 64)), &mut solver, info())
                .unwrap();
            let value = unsigned(value, &mut solver, info()).unwrap();
            solver.assert(smtlib::Exp::Var(cond));
            let result = narrow(value, &mut solver, info());
            eprintln!("合并后溢出窄化={result:?}");
            if let Ok(value) = &result {
                assert_eq!(solver.check_sat(info()), crate::smt::SmtResult::Sat);
                eprintln!("溢出窄化物化={:?}", Model::new(&solver).get_val(value).unwrap());
            }
            assert!(result.is_err());
        }

        #[test]
        fn review11_different_width_equality() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let eq = crate::primop::eq_anything::<B64>;
            for n in [1, 2] {
                assert_eq!(
                    eq(Val::Bits(B64::new(n, 8)), Val::Bits(B64::new(1, 16)), &mut solver, info()).unwrap(),
                    Val::Bool(false)
                );
            }
            let value = crate::primop_util::merge_val(
                cond,
                &Val::Bits(B64::new(1, 8)),
                &Val::Bits(B64::new(2, 8)),
                &mut solver,
                info(),
            )
            .unwrap();
            assert!(eq(value, Val::Bits(B64::new(1, 16)), &mut solver, info()).is_ok());
        }
        use super::*;
        use crate::bitvector::b129::B129;

        #[test]
        fn review11_bitvector_category_after_not() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let amount = crate::primop_util::merge_val(
                cond,
                &Val::Bits(B129::new(0, 128)),
                &Val::Bits(B129::new(1, 128)),
                &mut solver,
                info(),
            )
            .unwrap();
            let not = *crate::primop::unary_primops::<B129>().get("not_bits").unwrap();
            let shift = *crate::primop::binary_primops::<B129>().get("arith_shiftr").unwrap();
            for n in [0, 1] {
                let concrete_amount = not(Val::Bits(B129::new(n, 128)), &mut solver, info()).unwrap();
                assert_eq!(
                    shift(Val::Bits(B129::new(0x80, 8)), concrete_amount, &mut solver, info()).unwrap(),
                    Val::Bits(B129::new(0xff, 8))
                );
            }
            let amount = not(amount, &mut solver, info()).unwrap();
            let Val::Symbolic(sym) = amount else { panic!("预期符号量") };
            eprintln!("not_bits 后位向量标记={}", solver.is_sail_bitvector(sym));
            let result = shift(Val::Bits(B129::new(0x80, 8)), amount, &mut solver, info()).unwrap();
            assert_eq!(solver.check_sat(info()), crate::smt::SmtResult::Sat);
            eprintln!("合并后结果={:?}", Model::new(&solver).get_val(&result).unwrap());
            let wrong = smtlib::Exp::Neq(
                Box::new(crate::primop_util::smt_value(&result, info()).unwrap()),
                Box::new(crate::primop_util::smt_sbits(B129::new(0xff, 8))),
            );
            assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
        }

        #[test]
        fn review11_merged_129_unsigned() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let unsigned = *crate::primop::unary_primops::<B129>().get("sail_unsigned").unwrap();
            for n in [1, 2] {
                assert_eq!(unsigned(Val::Bits(B129::new(n, 129)), &mut solver, info()).unwrap(), Val::I128(n as i128));
            }
            let value = crate::primop_util::merge_val(
                cond,
                &Val::Bits(B129::new(1, 129)),
                &Val::Bits(B129::new(2, 129)),
                &mut solver,
                info(),
            )
            .unwrap();
            let result = unsigned(value, &mut solver, info());
            eprintln!("合并后 unsigned={result:?}");
            assert!(result.is_ok());
        }

        #[test]
        fn review11_merged_129_signed() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let signed = *crate::primop::unary_primops::<B129>().get("sail_signed").unwrap();
            for n in [1, 2] {
                assert_eq!(signed(Val::Bits(B129::new(n, 129)), &mut solver, info()).unwrap(), Val::I128(n as i128));
            }
            let value = crate::primop_util::merge_val(
                cond,
                &Val::Bits(B129::new(1, 129)),
                &Val::Bits(B129::new(2, 129)),
                &mut solver,
                info(),
            )
            .unwrap();
            assert!(signed(value, &mut solver, info()).is_ok());
        }

        #[test]
        fn review11_write_read_interleaving() {
            let mut shared = empty_shared_state();
            let written = shared.symtab.intern("zreview11_written");
            let read = shared.symtab.intern("zreview11_read");
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let mut frame = make_frame(vec![
                Instr::Jump(Exp::Bool(true), 4, info()),
                Instr::Copy(Loc::Id(written), Exp::Bits(B64::new(1, 8)), info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(read), info()),
                Instr::Goto(6),
                Instr::Copy(Loc::Id(written), Exp::Bits(B64::new(2, 8)), info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(read), info()),
                Instr::End,
            ]);
            frame.regs_mut().insert(written, false, UVal::Init(Val::Bits(B64::new(0, 8))));
            frame.regs_mut().insert(read, false, UVal::Init(Val::Bits(B64::new(3, 8))));
            let merged = try_merge_diamond(cond, 4, &mut frame, &shared, &mut solver, info(), None, None).unwrap();
            if merged.is_none() {
                assert!(!solver
                    .trace()
                    .to_vec()
                    .iter()
                    .any(|event| matches!(event, Event::ReadReg(..) | Event::WriteReg(..))));
                return;
            }
            assert_eq!(merged, Some(6));
            let events: Vec<_> = solver
                .trace()
                .to_vec()
                .into_iter()
                .rev()
                .filter_map(|event| match event {
                    Event::ReadReg(reg, _, _) => Some(("read", *reg)),
                    Event::WriteReg(reg, _, _) => Some(("write", *reg)),
                    _ => None,
                })
                .collect();
            eprintln!("合并后读写顺序={events:?}");
            assert_eq!(events, vec![("write", written), ("read", read)]);
        }

        #[test]
        fn review11_bit_access_large_index() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            for n in [1, 3] {
                assert!(crate::primop::vector_access(Val::Bits(B64::new(n, 8)), Val::I128(256), &mut solver, info())
                    .is_err());
            }
            let value = crate::primop_util::merge_val(
                cond,
                &Val::Bits(B64::new(1, 8)),
                &Val::Bits(B64::new(3, 8)),
                &mut solver,
                info(),
            )
            .unwrap();
            let result = crate::primop::vector_access(value, Val::I128(256), &mut solver, info());
            eprintln!("越界位访问={result:?}");
            if let Ok(value) = &result {
                assert_eq!(solver.check_sat(info()), crate::smt::SmtResult::Sat);
                eprintln!("越界位访问物化={:?}", Model::new(&solver).get_val(value).unwrap());
            }
            assert!(result.is_err());
        }
    }
    mod review10_tests {
        use super::*;
        #[test]
        fn review10_b129_integer_arithmetic_variants() {
            use crate::bitvector::b129::B129;
            for op in ["add_bits_int", "sub_bits_int"] {
                for number in [i128::MIN, -1, 0, 1, i128::MAX] {
                    for symbolic_bits in [false, true] {
                        for symbolic_integer in [false, true] {
                            let ctx = Context::new(Config::new());
                            let mut solver = Solver::<B129>::new(&ctx);
                            let bits = B129::new(2, 129);
                            let input = if symbolic_bits {
                                Val::Symbolic(solver.define_bitvector(crate::primop_util::smt_sbits(bits), info()))
                            } else {
                                Val::Bits(bits)
                            };
                            let integer = if symbolic_integer {
                                Val::Symbolic(solver.define_const(crate::primop_util::smt_i128(number), info()))
                            } else {
                                Val::I128(number)
                            };
                            let f = *crate::primop::binary_primops::<B129>().get(op).unwrap();
                            let result = f(input, integer, &mut solver, info()).unwrap();
                            let expected = f(Val::Bits(bits), Val::I128(number), &mut solver, info()).unwrap();
                            let wrong = smtlib::Exp::Neq(
                                Box::new(crate::primop_util::smt_value(&result, info()).unwrap()),
                                Box::new(crate::primop_util::smt_value(&expected, info()).unwrap()),
                            );
                            assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat,
                                "129 位加减不一致：{op}，整数={number}，符号数据={symbolic_bits}，符号整数={symbolic_integer}");
                        }
                    }
                }
            }
        }

        #[test]
        fn review10_signed_conversion_preserves_negative_shift() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let bits = solver.declare_bitvector(128, info());
            solver.assert_eq(smtlib::Exp::Var(bits), crate::primop_util::smt_i128(-1));
            let signed = *crate::primop::unary_primops::<B64>().get("sail_signed").unwrap();
            let amount = signed(Val::Symbolic(bits), &mut solver, info()).unwrap();
            let shift = *crate::primop::binary_primops::<B64>().get("arith_shiftr").unwrap();
            let result = shift(Val::Bits(B64::new(1, 8)), amount, &mut solver, info()).unwrap();
            let wrong = smtlib::Exp::Neq(
                Box::new(crate::primop_util::smt_value(&result, info()).unwrap()),
                Box::new(smtlib::bits64(2, 8)),
            );
            assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
            assert!(solver.is_sail_bitvector(bits), "转换不能改变原位向量的语义");
        }

        #[test]
        fn review10_bitvector_category_survives_checkpoint_and_rollback() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let bits = solver.declare_bitvector(128, info());
            solver.assert_eq(smtlib::Exp::Var(bits), crate::primop_util::smt_i128(i128::MIN));
            let tx = solver.start_transaction();
            let temporary = solver.define_bitvector(smtlib::Exp::Var(bits), info());
            solver.rollback_transaction(tx);
            assert!(!solver.is_sail_bitvector(temporary));
            let point = checkpoint(&mut solver);
            let mut replayed = Solver::from_checkpoint(&ctx, point);
            assert!(replayed.is_sail_bitvector(bits));
            let shift = *crate::primop::binary_primops::<B64>().get("arith_shiftr").unwrap();
            let result = shift(Val::Bits(B64::new(0x80, 8)), Val::Symbolic(bits), &mut replayed, info()).unwrap();
            let wrong = smtlib::Exp::Neq(
                Box::new(crate::primop_util::smt_value(&result, info()).unwrap()),
                Box::new(smtlib::bits64(0xff, 8)),
            );
            assert_eq!(replayed.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
        }

        #[test]
        fn review10_vector_index_domain_and_out_of_bounds() {
            let access = *crate::primop::binary_primops::<B64>().get("vector_access").unwrap();
            for len in [2, 3] {
                let ctx = Context::new(Config::new());
                let mut solver = Solver::<B64>::new(&ctx);
                let index = solver.declare_const(smtlib::Ty::BitVec(1), info());
                let vector = Val::Vector((0..len).map(Val::I128).collect());
                let result = access(vector, Val::Symbolic(index), &mut solver, info()).unwrap();
                for n in [0, 1] {
                    let expected = smtlib::Exp::And(
                        Box::new(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(index)), Box::new(smtlib::bits64(n, 1)))),
                        Box::new(smtlib::Exp::Eq(
                            Box::new(crate::primop_util::smt_value(&result, info()).unwrap()),
                            Box::new(crate::primop_util::smt_i128(n as i128)),
                        )),
                    );
                    assert_eq!(solver.check_sat_with(&expected, info()), crate::smt::SmtResult::Sat);
                }
            }
            for n in [-1, 2, 3] {
                let ctx = Context::new(Config::new());
                let mut solver = Solver::<B64>::new(&ctx);
                let index = solver.define_const(crate::primop_util::smt_i128(n), info());
                assert!(matches!(
                    access(Val::Vector(vec![Val::Unit; 2]), Val::Symbolic(index), &mut solver, info()),
                    Err(ExecError::OutOfBounds("vector_access"))
                ));
            }
        }

        #[test]
        fn review10_different_register_read_order_rejects_merge() {
            let mut shared = empty_shared_state();
            let left = shared.symtab.intern("zreview_read_left");
            let right = shared.symtab.intern("zreview_read_right");
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let mut frame = make_frame(vec![
                Instr::Jump(Exp::Bool(true), 4, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(left), info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(right), info()),
                Instr::Goto(6),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(right), info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(left), info()),
                Instr::End,
            ]);
            for reg in [left, right] {
                frame.regs_mut().insert(reg, false, UVal::Init(Val::Bool(true)));
            }
            assert_eq!(try_merge_diamond(cond, 4, &mut frame, &shared, &mut solver, info(), None, None).unwrap(), None);
            assert!(
                !solver.trace().to_vec().iter().any(|event| matches!(event, Event::ReadReg(..))),
                "拒绝合并必须回滚读取事件"
            );
        }

        #[test]
        fn current_review_structured_vector_access() {
            for enabled in [false, true] {
                let mut shared = empty_shared_state();
                let cond = shared.symtab.intern("zreview_cond");
                let byte = shared.symtab.intern("zreview_byte");
                let index = shared.symtab.intern("zreview_index");
                let vector = shared.symtab.intern("zreview_vector");
                let field = shared.symtab.intern("zreview_field");
                let mut lets = HashMap::default();
                lets.insert(
                    vector,
                    UVal::Init(Val::Vector(vec![
                        Val::Struct(HashMap::from_iter([(field, Val::Bool(false))])),
                        Val::Struct(HashMap::from_iter([(field, Val::Bool(true))])),
                    ])),
                );
                let unsigned = *crate::primop::unary_primops::<B64>().get("sail_unsigned").unwrap();
                let access = *crate::primop::binary_primops::<B64>().get("vector_access").unwrap();
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(cond, Ty::Bool, info()),
                        Instr::Decl(byte, Ty::Bits(8), info()),
                        Instr::Decl(index, Ty::I128, info()),
                        Instr::Jump(Exp::Id(cond), 6, info()),
                        Instr::Copy(Loc::Id(byte), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(byte), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::PrimopUnary(Loc::Id(index), unsigned, Exp::Id(byte), info()),
                        Instr::PrimopBinary(Loc::Id(RETURN), access, Exp::Id(vector), Exp::Id(index), info()),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    shared,
                    RegisterBindings::new(),
                    lets,
                );
                let errors: Vec<_> =
                    results.iter().filter_map(|result| result.as_ref().err().map(ToString::to_string)).collect();
                eprintln!("结构向量读取：合并={enabled}，路径数={}，错误={errors:?}", results.len());
                assert!(errors.is_empty(), "合法向量索引必须完成");
            }
        }

        #[test]
        fn current_review_symbolic_ctor_model() {
            let shared = empty_shared_state();
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let mut frame = make_frame(vec![
                Instr::Jump(Exp::Bool(true), 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                Instr::Goto(4),
                Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                Instr::End,
            ]);
            let left = test_name(200);
            let right = test_name(201);
            let mut lets = HashMap::default();
            lets.insert(left, UVal::Init(Val::Ctor(left, Box::new(Val::Unit))));
            lets.insert(right, UVal::Init(Val::Ctor(right, Box::new(Val::Unit))));
            frame.add_lets(&lets);
            frame.instrs = Box::leak(
                vec![
                    Instr::Jump(Exp::Bool(true), 3, info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(left), info()),
                    Instr::Goto(4),
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(right), info()),
                    Instr::End,
                ]
                .into_boxed_slice(),
            );
            assert_eq!(try_merge_diamond(cond, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(), None);
            assert!(matches!(frame.vars()[&RETURN], UVal::Uninit(Ty::Unit)), "拒绝合流必须保留原始返回值");
            // 通用 ITE 仍可构造有限的符号构造子选择，用于验证模型物化。
            let value = crate::primop_util::build_ite(
                cond,
                &Val::Ctor(left, Box::new(Val::Unit)),
                &Val::Ctor(right, Box::new(Val::Unit)),
                &mut solver,
                info(),
            )
            .unwrap();
            assert_eq!(solver.check_sat(info()), crate::smt::SmtResult::Sat);
            let mut model = Model::new(&solver);
            model.set_complete_model(true);
            let resolved = model.get_val(&value);
            eprintln!("构造子物化：{resolved:?}");
            assert!(resolved.is_ok(), "有限构造子选择必须能够物化");
        }

        #[test]
        fn current_review_b129_add_after_merge() {
            use crate::bitvector::b129::B129;
            let shared = SharedState::<B129>::empty(Symtab::new());
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let instrs: &'static [Instr<Name, B129>] = Box::leak(
                vec![
                    Instr::Jump(Exp::Bool(true), 3, info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(1, 64)), info()),
                    Instr::Goto(4),
                    Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(2, 64)), info()),
                    Instr::End,
                ]
                .into_boxed_slice(),
            );
            let mut frame = LocalFrame::new(test_name(25), &[], &Ty::Unit, None, instrs);
            let left = test_name(200);
            let right = test_name(201);
            let mut lets = HashMap::default();
            lets.insert(left, UVal::Init(Val::Bits(B129::new(1, 129))));
            lets.insert(right, UVal::Init(Val::Bits(B129::new(2, 129))));
            frame.add_lets(&lets);
            frame.instrs = Box::leak(
                vec![
                    Instr::Jump(Exp::Bool(true), 3, info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(left), info()),
                    Instr::Goto(4),
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(right), info()),
                    Instr::End,
                ]
                .into_boxed_slice(),
            );
            let add = *crate::primop::binary_primops::<B129>().get("add_bits_int").unwrap();
            for bits in [B129::new(1, 129), B129::new(2, 129)] {
                assert!(add(Val::Bits(bits), Val::I128(1), &mut solver, info()).is_ok());
            }
            assert_eq!(
                try_merge_diamond(cond, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(),
                Some(4)
            );
            let value =
                eval_exp(&Exp::Id(RETURN), &mut frame.local_state, &shared, &mut solver, info()).unwrap().into_owned();
            let result = add(value, Val::I128(1), &mut solver, info());
            assert!(result.is_ok());
        }

        #[test]
        fn current_review_arith_bit_shift_after_merge() {
            for enabled in [false, true] {
                let cond = test_name(200);
                let amount = test_name(201);
                let shift = *crate::primop::binary_primops::<B64>().get("arith_shiftr").unwrap();
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(cond, Ty::Bool, info()),
                        Instr::Decl(amount, Ty::Bits(8), info()),
                        Instr::Jump(Exp::Id(cond), 5, info()),
                        Instr::Copy(Loc::Id(amount), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::Goto(6),
                        Instr::Copy(Loc::Id(amount), Exp::Bits(B64::new(2, 8)), info()),
                        Instr::PrimopBinary(
                            Loc::Id(RETURN),
                            shift,
                            Exp::Bits(B64::new(0x80, 8)),
                            Exp::Id(amount),
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                eprintln!("位向量算术移位：合并={enabled}，路径数={}", results.len());
                assert!(results.iter().all(|result| matches!(result, Ok(Run::Finished(_)))));
            }
        }

        #[test]
        fn current_review_disjoint_reads() {
            let mut shared = empty_shared_state();
            let left = shared.symtab.intern("zreview_left");
            let right = shared.symtab.intern("zreview_right");
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let mut frame = make_frame(vec![
                Instr::Jump(Exp::Bool(true), 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(left), info()),
                Instr::Goto(4),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(right), info()),
                Instr::End,
            ]);
            frame.regs_mut().insert(left, false, UVal::Init(Val::Bits(B64::new(1, 8))));
            frame.regs_mut().insert(right, false, UVal::Init(Val::Bits(B64::new(2, 8))));
            let merged = try_merge_diamond(cond, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap();
            let events = solver.trace().to_vec();
            let reads: Vec<_> = events
                .iter()
                .rev()
                .filter_map(|event| match event {
                    Event::ReadReg(reg, _, _) => Some(*reg),
                    _ => None,
                })
                .collect();
            eprintln!("互斥读取：合并={merged:?}，读取={reads:?}");
            assert!(merged.is_none() || reads.len() == 1, "每条原始路径恰好读一个寄存器");
        }

        #[test]
        fn current_review_register_order() {
            let mut shared = empty_shared_state();
            let left = shared.symtab.intern("zreview_left");
            let right = shared.symtab.intern("zreview_right");
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let mut frame = make_frame(vec![
                Instr::Jump(Exp::Bool(true), 4, info()),
                Instr::Copy(Loc::Id(left), Exp::Bits(B64::new(1, 8)), info()),
                Instr::Copy(Loc::Id(right), Exp::Bits(B64::new(2, 8)), info()),
                Instr::Goto(6),
                Instr::Copy(Loc::Id(right), Exp::Bits(B64::new(3, 8)), info()),
                Instr::Copy(Loc::Id(left), Exp::Bits(B64::new(4, 8)), info()),
                Instr::End,
            ]);
            frame.regs_mut().insert(left, false, UVal::Init(Val::Bits(B64::new(0, 8))));
            frame.regs_mut().insert(right, false, UVal::Init(Val::Bits(B64::new(0, 8))));
            let merged = try_merge_diamond(cond, 4, &mut frame, &shared, &mut solver, info(), None, None).unwrap();
            let events = solver.trace().to_vec();
            let writes: Vec<_> = events
                .iter()
                .rev()
                .filter_map(|event| match event {
                    Event::WriteReg(reg, _, _) => Some(*reg),
                    _ => None,
                })
                .collect();
            eprintln!(
                "写顺序：合并={merged:?}，写入={writes:?}，假分支={:?}，真分支={:?}",
                [left, right],
                [right, left]
            );
            assert!(merged.is_none(), "互不相同的写事件顺序无法用同一条平铺轨迹表达");
        }

        #[test]
        fn current_review_model_value_must_belong_to_merged_paths() {
            let shared = empty_shared_state();
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let mut frame = make_frame(vec![
                Instr::Jump(Exp::Bool(true), 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(1, 8)), info()),
                Instr::Goto(4),
                Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(2, 8)), info()),
                Instr::End,
            ]);
            assert_eq!(
                try_merge_diamond(cond, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(),
                Some(4)
            );
            let value =
                eval_exp(&Exp::Id(RETURN), &mut frame.local_state, &shared, &mut solver, info()).unwrap().into_owned();
            assert_eq!(solver.check_sat(info()), crate::smt::SmtResult::Sat);
            let result = Model::new(&solver).get_val(&value).unwrap();
            eprintln!("合并结果物化：{result:?}，原始值域={{1,2}}");
            assert!(
                matches!(result, Val::Bits(bits) if bits.lower_u64() == 1 || bits.lower_u64() == 2),
                "物化不能产生合并前不存在的值"
            );
        }

        #[test]
        fn current_review_intrinsic_control_dependency() {
            let mut shared = empty_shared_state();
            let reg = shared.symtab.intern("zreview_input");
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let mut frame = make_frame(vec![
                Instr::Jump(Exp::Id(reg), 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                Instr::Goto(4),
                Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                Instr::End,
            ]);
            frame.regs_mut().insert(reg, false, UVal::Uninit(&Ty::Bool));
            let cond_value =
                eval_exp(&Exp::Id(reg), &mut frame.local_state, &shared, &mut solver, info()).unwrap().into_owned();
            let Val::Symbolic(cond) = cond_value else { panic!("条件必须是符号布尔值") };
            assert_eq!(
                try_merge_diamond(cond, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(),
                Some(4)
            );
            solver.add_event(Event::Branch { address: Val::Bits(B64::new(0x1000, 64)) });
            let events: Vec<_> = solver.trace().to_vec().into_iter().rev().cloned().collect();
            let refs = crate::simplify::EventReferences::from_events(&events);
            let mut taints = crate::simplify::Taints::new();
            let mut forks = Vec::new();
            for event in &events {
                match event {
                    Event::Fork(_, sym, _, _) => forks.push(*sym),
                    Event::Branch { address } => {
                        refs.collect_value_taints(address, &events, &mut taints);
                        for sym in &forks {
                            refs.collect_taints(*sym, &events, &mut taints);
                        }
                    }
                    _ => (),
                }
            }
            eprintln!("合并后分支地址控制依赖：{:?}", taints.registers);
            assert!(taints.registers.contains(&(reg, vec![])), "既有 footprint 算法必须仍能看见合并掉的控制依赖");
        }

        #[test]
        fn current_review_pow_exp_complexity() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let bits = crate::primop_util::build_ite(
                cond,
                &Val::Bits(B64::new(0, 8)),
                &Val::Bits(B64::new(1, 8)),
                &mut solver,
                info(),
            )
            .unwrap();
            let unsigned = *crate::primop::unary_primops::<B64>().get("sail_unsigned").unwrap();
            let base = unsigned(bits, &mut solver, info()).unwrap();
            let pow = *crate::primop::binary_primops::<B64>().get("pow_int").unwrap();
            let before = solver.trace().to_vec().len();
            let started = Instant::now();
            let result = pow(base, Val::I128(1000), &mut solver, info()).unwrap();
            let definitions = solver.trace().to_vec().len() - before;
            eprintln!("符号幂：指数=1000，定义数={definitions}，耗时={:?}，结果={result:?}", started.elapsed());
            assert!(definitions < 30, "有限指数应使用平方乘算法");
        }

        #[test]
        fn current_review_vector_access_bounds() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let bits = crate::primop_util::build_ite(
                cond,
                &Val::Bits(B64::new(0, 8)),
                &Val::Bits(B64::new(2, 8)),
                &mut solver,
                info(),
            )
            .unwrap();
            let unsigned = *crate::primop::unary_primops::<B64>().get("sail_unsigned").unwrap();
            let index = unsigned(bits, &mut solver, info()).unwrap();
            let vec = Val::Vector(vec![Val::I128(10), Val::I128(20)]);
            let access = *crate::primop::binary_primops::<B64>().get("vector_access").unwrap();
            assert!(access(vec.clone(), Val::I128(2), &mut solver, info()).is_err());
            let result = access(vec, index, &mut solver, info()).unwrap();
            let bad = smtlib::Exp::And(
                Box::new(smtlib::Exp::Not(Box::new(smtlib::Exp::Var(cond)))),
                Box::new(smtlib::Exp::Eq(
                    Box::new(crate::primop_util::smt_value(&result, info()).unwrap()),
                    Box::new(crate::primop_util::smt_i128(20)),
                )),
            );
            eprintln!("越界读取却正常返回最后元素：{:?}", solver.check_sat_with(&bad, info()));
            assert_eq!(solver.check_sat_with(&bad, info()), crate::smt::SmtResult::Unsat);
        }

        #[test]
        fn current_review_trace_definition_read_order() {
            let mut shared = empty_shared_state();
            let reg = shared.symtab.intern("zreview_input");
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let value = Exp::Call(Op::Not, vec![Exp::Id(reg)]);
            let mut frame = make_frame(vec![
                Instr::Jump(Exp::Bool(true), 3, info()),
                Instr::Copy(Loc::Id(RETURN), value.clone(), info()),
                Instr::Goto(4),
                Instr::Copy(Loc::Id(RETURN), value, info()),
                Instr::End,
            ]);
            frame.regs_mut().insert(reg, false, UVal::Uninit(&Ty::Bool));
            assert_eq!(
                try_merge_diamond(cond, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(),
                Some(4)
            );
            let result =
                eval_exp(&Exp::Id(RETURN), &mut frame.local_state, &shared, &mut solver, info()).unwrap().into_owned();
            let Val::Symbolic(result) = result else { panic!("必须是符号结果") };
            solver.add_event(Event::Fork(1, result, 0, info()));
            let events: Vec<_> = solver.trace().to_vec().into_iter().rev().cloned().collect();
            let mut intrinsic_data: std::collections::HashMap<Sym, std::collections::HashSet<Name>> =
                std::collections::HashMap::new();
            let mut ctrl = std::collections::HashSet::new();
            for event in &events {
                match event {
                    Event::Smt(smtlib::Def::DefineConst(sym, exp), _, _) => {
                        let taints = exp
                            .variables()
                            .iter()
                            .flat_map(|var| intrinsic_data.get(var).into_iter().flatten())
                            .copied()
                            .collect();
                        intrinsic_data.insert(*sym, taints);
                    }
                    Event::ReadReg(reg, _, value) => {
                        for var in value.symbolic_variables() {
                            intrinsic_data.entry(var).or_default().insert(*reg);
                        }
                    }
                    Event::Fork(_, sym, _, _) => ctrl.extend(intrinsic_data.get(sym).into_iter().flatten().copied()),
                    _ => (),
                }
            }
            eprintln!("后续真实 fork 的顺序污点传播：{ctrl:?}，预期包含 {reg:?}");
            assert!(ctrl.contains(&reg));
        }

        #[test]
        fn current_review_unsigned_representable_129() {
            use crate::bitvector::b129::B129;
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let unsigned = *crate::primop::unary_primops::<B129>().get("sail_unsigned").unwrap();
            let bits = B129::new(1, 129);
            assert_eq!(bits.unsigned(), 1);
            let result = unsigned(Val::Bits(bits), &mut solver, info());
            eprintln!("可表示的 129 位无符号转换：{result:?}");
            assert_eq!(result.unwrap(), Val::I128(1));
        }

        #[test]
        fn current_review_footprint_collector_boolean_phi() {
            for enabled in [false, true] {
                let shared = empty_shared_state();
                let cond = test_name(200);
                let task_state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let frame = make_frame(vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Jump(Exp::Id(cond), 4, info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                    Instr::Goto(5),
                    Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
                    Instr::End,
                ]);
                let collected = SegQueue::new();
                start_single(frame.task(TaskId::fresh(), &task_state), &shared, &collected, &footprint_collector);
                let result = collected.pop().unwrap();
                eprintln!("footprint 布尔返回：合并={enabled}，成功={}", result.is_ok());
                assert!(result.is_ok(), "布尔合并结果必须按可满足的真子域收集");
            }
        }

        #[test]
        fn current_review_undefined_bitvector_finite_length() {
            for enabled in [false, true] {
                let cond = test_name(200);
                let byte = test_name(201);
                let length = test_name(202);
                let unsigned = *crate::primop::unary_primops::<B64>().get("sail_unsigned").unwrap();
                let undefined = *crate::primop::unary_primops::<B64>().get("undefined_bitvector").unwrap();
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(cond, Ty::Bool, info()),
                        Instr::Decl(byte, Ty::Bits(8), info()),
                        Instr::Decl(length, Ty::I128, info()),
                        Instr::Jump(Exp::Id(cond), 6, info()),
                        Instr::Copy(Loc::Id(byte), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(byte), Exp::Bits(B64::new(2, 8)), info()),
                        Instr::PrimopUnary(Loc::Id(length), unsigned, Exp::Id(byte), info()),
                        Instr::PrimopUnary(Loc::Id(RETURN), undefined, Exp::Id(length), info()),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                let errors: Vec<_> =
                    results.iter().filter_map(|result| result.as_ref().err().map(ToString::to_string)).collect();
                eprintln!("有限长度 undefined_bitvector：合并={enabled}，路径数={}，错误={errors:?}", results.len());
                assert!(errors.is_empty());
            }
        }

        #[test]
        fn current_review_arith_unsigned_128_count_changes_direction() {
            use crate::bitvector::b129::B129;
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let mut first = [0u8; 16];
            first[0] = 0x80;
            let mut second = first;
            second[15] = 1;
            let lhs = Val::Bits(B129::from_bytes(&first));
            let rhs = Val::Bits(B129::from_bytes(&second));
            let shift = *crate::primop::binary_primops::<B129>().get("arith_shiftr").unwrap();
            let bits = Val::Bits(B129::new(0x80, 8));
            for amount in [lhs.clone(), rhs.clone()] {
                assert_eq!(shift(bits.clone(), amount, &mut solver, info()).unwrap(), Val::Bits(B129::new(0xff, 8)));
            }
            let merged = crate::primop_util::merge_val(cond, &lhs, &rhs, &mut solver, info()).unwrap();
            let result = shift(bits, merged, &mut solver, info()).unwrap();
            let wrong = smtlib::Exp::Neq(
                Box::new(crate::primop_util::smt_value(&result, info()).unwrap()),
                Box::new(smtlib::bits64(0xff, 8)),
            );
            let query = solver.check_sat_with(&wrong, info());
            eprintln!("128 位无符号移位量合并后错误反向移位：{query:?}");
            assert_eq!(query, crate::smt::SmtResult::Unsat);
        }
    }
    mod review8_tests {
        use super::*;

        // 保留未合流行为与合流行为的差分证据。
        #[test]
        fn adversarial_merge_large_shift() {
            let shared = empty_shared_state();
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let mut frame = make_frame(vec![
                Instr::Jump(Exp::Bool(true), 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(1, 8)), info()),
                Instr::Goto(4),
                Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(2, 8)), info()),
                Instr::End,
            ]);
            assert_eq!(
                try_merge_diamond(cond, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(),
                Some(4)
            );
            let value =
                eval_exp(&Exp::Id(RETURN), &mut frame.local_state, &shared, &mut solver, info()).unwrap().into_owned();
            let shift = *crate::primop::binary_primops::<B64>().get("shiftr").unwrap();
            for n in [1, 2] {
                assert_eq!(
                    shift(Val::Bits(B64::new(n, 8)), Val::I128(256), &mut solver, info()).unwrap(),
                    Val::Bits(B64::new(0, 8))
                );
            }
            let shifted = shift(value, Val::I128(256), &mut solver, info()).unwrap();
            let wrong = smtlib::Exp::Neq(
                Box::new(crate::primop_util::smt_value(&shifted, info()).unwrap()),
                Box::new(smtlib::Exp::Bits64(B64::new(0, 8))),
            );
            assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat, "右移 256 位应为零");
            for op in ["shiftr", "shiftl"] {
                let shift = *crate::primop::binary_primops::<B64>().get(op).unwrap();
                for width in [8, 64, 128, 256] {
                    let bits = solver.define_const(smtlib::bits64(1, width), info());
                    for amount in [0, 1, i128::from(width) - 1, i128::from(width), 256, i128::MAX] {
                        let exponent = solver.define_const(crate::primop_util::smt_i128(amount), info());
                        let expected = if amount >= i128::from(width) {
                            crate::primop::smt_zeros(i128::from(width))
                        } else {
                            let amount = smtlib::bits64(amount as u64, width);
                            if op == "shiftr" {
                                smtlib::Exp::Bvlshr(Box::new(smtlib::Exp::Var(bits)), Box::new(amount))
                            } else {
                                smtlib::Exp::Bvshl(Box::new(smtlib::Exp::Var(bits)), Box::new(amount))
                            }
                        };
                        for count in [Val::I128(amount), Val::Symbolic(exponent)] {
                            let result = shift(Val::Symbolic(bits), count.clone(), &mut solver, info()).unwrap();
                            let wrong = smtlib::Exp::Neq(
                                Box::new(crate::primop_util::smt_value(&result, info()).unwrap()),
                                Box::new(expected.clone()),
                            );
                            assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
                            if width <= 64 {
                                let result = shift(Val::Bits(B64::new(1, width)), count, &mut solver, info()).unwrap();
                                let wrong = smtlib::Exp::Neq(
                                    Box::new(crate::primop_util::smt_value(&result, info()).unwrap()),
                                    Box::new(expected.clone()),
                                );
                                assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
                            }
                        }
                    }
                }
            }
        }

        #[test]
        fn adversarial_merge_constructor_equality() {
            for enabled in [false, true] {
                let mut shared = empty_shared_state();
                let cond = shared.symtab.intern("zcond");
                let value = shared.symtab.intern("zvalue");
                let a = shared.symtab.intern("za");
                let b = shared.symtab.intern("zb");
                let mut lets = HashMap::default();
                lets.insert(a, UVal::Init(Val::Ctor(test_name(180), Box::new(Val::Unit))));
                lets.insert(b, UVal::Init(Val::Ctor(test_name(181), Box::new(Val::Unit))));
                let instrs = vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(value, Ty::Union(test_name(182)), info()),
                    Instr::Jump(Exp::Id(cond), 5, info()),
                    Instr::Copy(Loc::Id(value), Exp::Id(a), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(value), Exp::Id(b), info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(value), Exp::Id(a)]), info()),
                    Instr::End,
                ];
                let results = run_all_with_bindings(
                    instrs,
                    ExecutionLimits::default().with_path_merging(enabled),
                    shared,
                    RegisterBindings::new(),
                    lets,
                );
                let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
                eprintln!("构造子相等比较：合流={enabled}，错误={errors:?}");
                assert!(errors.is_empty(), "两条分支都支持相等比较");
            }
        }

        #[test]
        fn adversarial_merge_bits_to_pow() {
            for enabled in [false, true] {
                let cond = test_name(180);
                let value = test_name(181);
                let exponent = test_name(182);
                let unsigned = *crate::primop::unary_primops::<B64>().get("sail_unsigned").unwrap();
                let pow = *crate::primop::binary_primops::<B64>().get("pow_int").unwrap();
                let instrs = vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(value, Ty::Bits(8), info()),
                    Instr::Decl(exponent, Ty::I128, info()),
                    Instr::Jump(Exp::Id(cond), 6, info()),
                    Instr::Copy(Loc::Id(value), Exp::Bits(B64::new(1, 8)), info()),
                    Instr::Goto(7),
                    Instr::Copy(Loc::Id(value), Exp::Bits(B64::new(2, 8)), info()),
                    Instr::PrimopUnary(Loc::Id(exponent), unsigned, Exp::Id(value), info()),
                    Instr::PrimopBinary(Loc::Id(RETURN), pow, Exp::I128(2), Exp::Id(exponent), info()),
                    Instr::End,
                ];
                let results = run_all_with_bindings(
                    instrs,
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
                eprintln!("位向量转整数后乘方：合流={enabled}，错误={errors:?}");
                assert!(errors.is_empty(), "指数为 1/2 的两条分支都应完成");
                let mut values: Vec<_> = results
                    .into_iter()
                    .map(|result| match result.unwrap() {
                        Run::Finished(Val::I128(value)) => value,
                        _ => panic!("乘方必须返回具体整数"),
                    })
                    .collect();
                values.sort_unstable();
                assert_eq!(values, vec![2, 4]);
            }
        }

        #[test]
        fn adversarial_unsigned_128_must_not_prune_input() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let bits = solver.declare_const(smtlib::Ty::BitVec(128), info());
            solver.assert_eq(smtlib::Exp::Var(bits), crate::primop_util::smt_i128(i128::MIN));
            assert_eq!(solver.check_sat(info()), crate::smt::SmtResult::Sat);
            let unsigned = *crate::primop::unary_primops::<B64>().get("sail_unsigned").unwrap();
            let result = unsigned(Val::Symbolic(bits), &mut solver, info());
            eprintln!("128 位无符号转换：调用成功={}，可满足性={:?}", result.is_ok(), solver.check_sat(info()));
            assert!(
                result.is_err() || solver.check_sat(info()) == crate::smt::SmtResult::Sat,
                "转换溢出应报告错误，不能删除输入"
            );
        }

        #[test]
        fn adversarial_merge_machine_index_width() {
            for enabled in [false, true] {
                let cond = test_name(180);
                let value = test_name(181);
                let index = test_name(182);
                let vector = test_name(183);
                let mut lets = HashMap::default();
                lets.insert(vector, UVal::Init(Val::Vector(vec![Val::I128(0), Val::I128(0)])));
                let update = *crate::primop::variadic_primops::<B64>().get("vector_update").unwrap();
                let instrs = vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(value, Ty::Bits(8), info()),
                    Instr::Decl(index, Ty::I64, info()),
                    Instr::Jump(Exp::Id(cond), 6, info()),
                    Instr::Copy(Loc::Id(value), Exp::Bits(B64::new(0, 8)), info()),
                    Instr::Goto(7),
                    Instr::Copy(Loc::Id(value), Exp::Bits(B64::new(1, 8)), info()),
                    Instr::Copy(Loc::Id(index), Exp::Call(Op::Unsigned(8), vec![Exp::Id(value)]), info()),
                    Instr::PrimopVariadic(
                        Loc::Id(RETURN),
                        update,
                        vec![Exp::Id(vector), Exp::Id(index), Exp::I128(7)],
                        info(),
                    ),
                    Instr::End,
                ];
                let results = run_all_with_bindings(
                    instrs,
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    lets,
                );
                assert!(results.iter().all(|r| matches!(r, Ok(Run::Finished(_)))));
            }
        }

        #[test]
        fn adversarial_enum_cache_variable_collision() {
            let ctx = Context::new(Config::new());
            let enum_name = test_name(200);
            {
                let mut first = Solver::<B64>::new(&ctx);
                for _ in 0..8 {
                    first.declare_const(smtlib::Ty::Bool, info());
                }
                first.get_enum(enum_name, 2);
            }
            let mut second = Solver::<B64>::new(&ctx);
            let eid = second.get_enum(enum_name, 2);
            let mut variable = None;
            for _ in 2..=8 {
                variable = Some(second.declare_const(smtlib::Ty::Enum(eid), info()));
            }
            let variable = variable.unwrap();
            let other = smtlib::Exp::Neq(
                Box::new(smtlib::Exp::Var(variable)),
                Box::new(smtlib::Exp::Enum(crate::smt::EnumMember { enum_id: eid, member: 0 })),
            );
            eprintln!("缓存复用后的枚举变量：{:?}，SMT={}", variable, second.exp_to_str(&smtlib::Exp::Var(variable)));
            assert_eq!(
                second.check_sat_with(&other, info()),
                crate::smt::SmtResult::Sat,
                "未约束的枚举变量必须能取非零成员"
            );
        }

        #[test]
        fn adversarial_merge_lazy_reads_trace() {
            let mut shared = empty_shared_state();
            let reg = shared.symtab.intern("zreg");
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let mut frame = make_frame(vec![
                Instr::Jump(Exp::Bool(true), 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
                Instr::Goto(4),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
                Instr::End,
            ]);
            frame.regs_mut().insert(reg, false, UVal::Uninit(&Ty::I64));
            assert_eq!(
                try_merge_diamond(cond, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(),
                Some(4)
            );
            let events = solver.trace().to_vec();
            let reads: Vec<_> = events
                .iter()
                .filter_map(|event| match event {
                    Event::ReadReg(r, _, value) if *r == reg => Some(value.clone()),
                    _ => None,
                })
                .collect();
            eprintln!("两臂均只读一次同一寄存器，合流后读事件：{reads:?}");
            assert_eq!(reads.len(), 1, "懒初始化只能提交一次合并读取");
            let inconsistent = smtlib::Exp::Neq(
                Box::new(crate::primop_util::smt_value(&reads[0], info()).unwrap()),
                Box::new(
                    crate::primop_util::smt_value(frame.regs().get_last_if_initialized(reg).unwrap(), info()).unwrap(),
                ),
            );
            assert_eq!(
                solver.check_sat_with(&inconsistent, info()),
                crate::smt::SmtResult::Unsat,
                "合并读取必须与没有写入的寄存器值一致"
            );
        }

        #[test]
        fn adversarial_merge_disjoint_register_writes_trace() {
            let mut shared = empty_shared_state();
            let a = shared.symtab.intern("za");
            let b = shared.symtab.intern("zb");
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let mut frame = make_frame(vec![
                Instr::Jump(Exp::Bool(true), 3, info()),
                Instr::Copy(Loc::Id(a), Exp::Bits(B64::new(1, 8)), info()),
                Instr::Goto(4),
                Instr::Copy(Loc::Id(b), Exp::Bits(B64::new(1, 8)), info()),
                Instr::End,
            ]);
            frame.regs_mut().insert(a, false, UVal::Init(Val::Bits(B64::new(0, 8))));
            frame.regs_mut().insert(b, false, UVal::Init(Val::Bits(B64::new(0, 8))));
            assert_eq!(
                try_merge_diamond(cond, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(),
                None,
                "不同写集合必须保留分叉"
            );
            let events = solver.trace().to_vec();
            let writes: Vec<_> = events
                .iter()
                .filter_map(|event| match event {
                    Event::WriteReg(reg, _, _) => Some(*reg),
                    _ => None,
                })
                .collect();
            eprintln!("每条分支仅写一个寄存器，合流后写事件：{writes:?}");
            assert!(writes.is_empty(), "拒绝合流必须回滚推测产生的写事件");

            let branch = shared.symtab.intern("zbranch");
            let mut frame = make_frame(vec![
                Instr::Decl(branch, Ty::Bool, info()),
                Instr::Jump(Exp::Id(branch), 4, info()),
                Instr::Copy(Loc::Id(a), Exp::Bits(B64::new(1, 8)), info()),
                Instr::Goto(5),
                Instr::Copy(Loc::Id(b), Exp::Bits(B64::new(1, 8)), info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                Instr::End,
            ]);
            frame.regs_mut().insert(a, false, UVal::Init(Val::Bits(B64::new(0, 8))));
            frame.regs_mut().insert(b, false, UVal::Init(Val::Bits(B64::new(0, 8))));
            let task_state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(true));
            let queue = Worker::new_lifo();
            queue.push(frame.task(TaskId::from_usize(0), &task_state));
            let mut written = Vec::new();
            while let Some(mut task) = queue.pop() {
                let mut solver = Solver::from_checkpoint(&ctx, task.checkpoint);
                if let Some((def, event)) = task.fork_cond {
                    solver.add_event(event);
                    solver.add(def);
                }
                let mut frame = unfreeze_frame(&task.frame);
                let result = run_loop(
                    0,
                    task.id,
                    &mut task.fraction,
                    PathTimeout::unlimited(),
                    task.stop_conditions,
                    &SingleForkSink { queue: &queue },
                    &mut frame,
                    task.state,
                    &shared,
                    &mut solver,
                )
                .unwrap();
                assert!(matches!(result, Run::Finished(_)));
                let events = solver.trace().to_vec();
                let writes: Vec<_> = events
                    .iter()
                    .filter_map(|event| match event {
                        Event::WriteReg(reg, _, _) => Some(*reg),
                        _ => None,
                    })
                    .collect();
                assert_eq!(writes.len(), 1, "每条实际路径只有一个写事件");
                written.push(writes[0]);
            }
            assert_eq!(written.len(), 2);
            assert!(written.contains(&a) && written.contains(&b));
        }

        #[test]
        fn adversarial_merge_data_to_dynamic_slice() {
            for enabled in [false, true] {
                let cond = test_name(180);
                let value = test_name(181);
                let length = test_name(182);
                let unsigned = *crate::primop::unary_primops::<B64>().get("sail_unsigned").unwrap();
                let slice = *crate::primop::variadic_primops::<B64>().get("slice").unwrap();
                let instrs = vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(value, Ty::Bits(8), info()),
                    Instr::Decl(length, Ty::I128, info()),
                    Instr::Jump(Exp::Id(cond), 6, info()),
                    Instr::Copy(Loc::Id(value), Exp::Bits(B64::new(1, 8)), info()),
                    Instr::Goto(7),
                    Instr::Copy(Loc::Id(value), Exp::Bits(B64::new(2, 8)), info()),
                    Instr::PrimopUnary(Loc::Id(length), unsigned, Exp::Id(value), info()),
                    Instr::PrimopVariadic(
                        Loc::Id(RETURN),
                        slice,
                        vec![Exp::Bits(B64::new(7, 8)), Exp::I128(0), Exp::Id(length)],
                        info(),
                    ),
                    Instr::End,
                ];
                let results = run_all_with_bindings(
                    instrs,
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
                eprintln!("位向量转整数后动态切片：合流={enabled}，错误={errors:?}");
                assert!(errors.is_empty(), "长度为 1/2 的两条分支都应完成");
                let mut widths: Vec<_> = results
                    .into_iter()
                    .map(|result| match result.unwrap() {
                        Run::Finished(Val::Bits(bits)) => bits.len(),
                        _ => panic!("动态切片必须返回具体位向量"),
                    })
                    .collect();
                widths.sort_unstable();
                assert_eq!(widths, vec![1, 2]);
            }
        }

        #[test]
        fn adversarial_relaxed_ctor_integer_history() {
            let mut shared = empty_shared_state();
            let reg = shared.symtab.intern("zreg");
            let ctor = shared.symtab.intern("zctor");
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let mut regs = RegisterBindings::new();
            regs.insert(reg, true, UVal::Init(Val::Ctor(ctor, Box::new(Val::I128(1)))));
            regs.assign(reg, Val::Ctor(ctor, Box::new(Val::I128(2))), &shared);
            regs.forget_last_reads();
            let read = regs.get(reg, &shared, &mut solver, info());
            eprintln!("未启用路径合流时读取 relaxed 构造子历史：{read:?}");
            assert!(read.is_ok(), "通用 ITE 应保留整数载荷的历史选择");
            let Val::Ctor(_, payload) = read.unwrap().unwrap() else { panic!("必须保留构造子") };
            let payload = crate::primop_util::smt_value(payload, info()).unwrap();
            for candidate in [1, 2, 3] {
                let query =
                    smtlib::Exp::Eq(Box::new(payload.clone()), Box::new(crate::primop_util::smt_i128(candidate)));
                assert_eq!(solver.check_sat_with(&query, info()).is_sat().unwrap(), candidate != 3);
            }
        }

        #[test]
        fn machine_and_integer_indices_preserve_slice_and_update_values() {
            for index_width in [64, 128] {
                let ctx = Context::new(Config::new());
                let mut solver = Solver::<B64>::new(&ctx);
                for width in [8, 64, 128, 256] {
                    let bits = solver.define_const(crate::primop::smt_zeros(i128::from(width)), info());
                    for offset in [0, width - 8] {
                        let index = solver.define_const(smtlib::bits64(u64::from(offset), index_width), info());
                        let value = crate::primop::op_set_slice(
                            Val::Symbolic(bits),
                            Val::Symbolic(index),
                            Val::Bits(B64::new(0xa5, 8)),
                            &mut solver,
                            info(),
                        )
                        .unwrap();
                        assert_eq!(crate::primop_util::length_bits(&value, &mut solver, info()).unwrap(), width);
                        let result =
                            crate::primop::op_slice(value, Val::Symbolic(index), 8, &mut solver, info()).unwrap();
                        let wrong = smtlib::Exp::Neq(
                            Box::new(crate::primop_util::smt_value(&result, info()).unwrap()),
                            Box::new(smtlib::bits64(0xa5, 8)),
                        );
                        assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
                    }
                }
                let index = solver.declare_const(smtlib::Ty::BitVec(index_width), info());
                let mut frame = make_frame(vec![Instr::End]);
                let result = crate::primop::vector_update(
                    vec![Val::Vector(vec![Val::I128(0), Val::I128(0)]), Val::Symbolic(index), Val::I128(7)],
                    &mut solver,
                    &mut frame,
                    info(),
                )
                .unwrap();
                let Val::Vector(values) = result else { panic!("必须返回向量") };
                for candidate in [0, 1] {
                    let selected = smtlib::Exp::Eq(
                        Box::new(smtlib::Exp::Var(index)),
                        Box::new(smtlib::bits64(candidate as u64, index_width)),
                    );
                    for (element, value) in values.iter().enumerate() {
                        let wrong = smtlib::Exp::And(
                            Box::new(selected.clone()),
                            Box::new(smtlib::Exp::Neq(
                                Box::new(crate::primop_util::smt_value(value, info()).unwrap()),
                                Box::new(crate::primop_util::smt_i128(if element == candidate { 7 } else { 0 })),
                            )),
                        );
                        assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
                    }
                }
                for invalid in [-1, 2] {
                    let bound = if index_width == 64 {
                        crate::primop_util::smt_i64(invalid)
                    } else {
                        crate::primop_util::smt_i128(i128::from(invalid))
                    };
                    let query = smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(index)), Box::new(bound));
                    assert_eq!(solver.check_sat_with(&query, info()), crate::smt::SmtResult::Unsat);
                }
            }
        }

        #[test]
        fn symbolic_constructor_equality_checks_tag_and_payload() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let a = test_name(180);
            let b = test_name(181);
            let merged = crate::primop_util::build_ite(
                cond,
                &Val::Ctor(a, Box::new(Val::Bits(B64::new(1, 8)))),
                &Val::Ctor(b, Box::new(Val::Bits(B64::new(2, 8)))),
                &mut solver,
                info(),
            )
            .unwrap();
            for tag in [a, b, test_name(182)] {
                for payload in [1, 2] {
                    let rhs = Val::Ctor(tag, Box::new(Val::Bits(B64::new(payload, 8))));
                    for (lhs, rhs) in [(merged.clone(), rhs.clone()), (rhs, merged.clone())] {
                        let equal = primop::eq_anything(lhs, rhs, &mut solver, info()).unwrap();
                        for choice in [false, true] {
                            let expected = if choice { tag == a && payload == 1 } else { tag == b && payload == 2 };
                            let wrong = smtlib::Exp::And(
                                Box::new(smtlib::Exp::Eq(
                                    Box::new(smtlib::Exp::Var(cond)),
                                    Box::new(smtlib::Exp::Bool(choice)),
                                )),
                                Box::new(smtlib::Exp::Neq(
                                    Box::new(crate::primop_util::smt_value(&equal, info()).unwrap()),
                                    Box::new(smtlib::Exp::Bool(expected)),
                                )),
                            );
                            assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
                        }
                    }
                }
            }
        }
    }

    use super::*;
    use crate::config::{ISAConfig, Tool};
    use crate::source_loc::SourceRegion;
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

    /// W17（S2 spike）：复刻 rv64d.ir 的 PMA 匹配链最小形状——
    /// `register zpma_regions : %list(%struct)` + `@is_empty/@hd/@tl` 遍历 +
    /// 字段访问 + `zrange_subset`（bv 加减 + 无符号比较）逐字复制自
    /// rv64d.ir:9997（zrange_subset）与 rv64d.ir:7988（`<=u`），用于验证
    /// "含 Symbolic 字段的 Struct 装进 List 写入寄存器（defaults 路径
    /// UVal::Init）后，执行链完整消费并触发求解分叉"。
    const SYMBOLIC_PMA_REGIONS_IR: &str = r#"
val zadd_bits = "add_bits" : (%bv, %bv) ->  %bv

val zsub_vec = "sub_bits" : (%bv, %bv) ->  %bv

val zlteq_int = "lteq" : (%i, %i) ->  %bool

val zunsigned = "sail_unsigned" : (%bv) ->  %i

val zconsz3z5structz0zzSpike_Region = "cons" : (%struct zSpike_Region, %list(%struct zSpike_Region)) ->  %list(%struct zSpike_Region)

struct zSpike_Region {
  zbase: %bv64,
  zsizze: %bv64
}

register zpma_regions : %list(%struct zSpike_Region) {
  zz40 : %list(%struct zSpike_Region);
  zz40 = zconsz3z5structz0zzSpike_Region(struct zSpike_Region {zbase = 0x0000000080000000, zsizze = 0x0000000000001000}, zz40);
  zpma_regions = zz40;
}

val zz8operatorz0zIzJ_uz9 : (%bv, %bv) ->  %bool

fn zz8operatorz0zIzJ_uz9(zx, zy) {
  zz40 : %i;
  zz40 = zunsigned(zx);
  zz41 : %i;
  zz41 = zunsigned(zy);
  return = zlteq_int(zz40, zz41);
  end;
}

val zrange_subset : (%bv, %bv, %bv, %bv) ->  %bool

fn zrange_subset(za_begin, za_sizze, zb_begin, zb_sizze) {
  zz40 : %bv;
  zz41 : %bv;
  zz41 = zadd_bits(za_begin, za_sizze);
  zz40 = zsub_vec(zz41, zb_begin);
  zz42 : %bv;
  zz43 : %bv;
  zz43 = zadd_bits(zb_begin, zb_sizze);
  zz42 = zsub_vec(zz43, zb_begin);
  zz44 : %bv;
  zz44 = zsub_vec(za_begin, zb_begin);
  zz45 : %bool;
  zz45 = zz8operatorz0zIzJ_uz9(zz44, zz42);
  zz46 : %bool;
  jump zz45 goto 16;
  zz46 = false;
  goto 24;
  zz47 : %bool;
  zz47 = zz8operatorz0zIzJ_uz9(zz40, zz42);
  zz48 : %bool;
  jump zz47 goto 22;
  zz48 = false;
  goto 23;
  zz48 = zz8operatorz0zIzJ_uz9(zz44, zz40);
  zz46 = zz48;
  return = zz46;
  end;
}

val zspike_match_range : (%list(%struct zSpike_Region), %bv64, %bv64) ->  %bool

fn zspike_match_range(zpmas, zaddr, zwidth) {
  zz40 : %bool;
  jump @not(@is_empty(zpmas)) goto 4;
  zz40 = false;
  goto 15;
  zz41 : %struct zSpike_Region;
  zz41 = @hd(zpmas);
  zz42 : %list(%struct zSpike_Region);
  zz42 = @tl(zpmas);
  zz43 : %bv64;
  zz43 = zz41.zbase;
  zz44 : %bv64;
  zz44 = zz41.zsizze;
  zz45 : %bool;
  zz45 = zrange_subset(zaddr, zwidth, zz43, zz44);
  zz40 = zz45;
  return = zz40;
  end;
}

val zspike_match : (%bv64, %bv64) ->  %bool

fn zspike_match(zaddr, zwidth) {
  zz40 : %bool;
  zz40 = zspike_match_range(zpma_regions, zaddr, zwidth);
  return = zz40;
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

    /// Sail 把 `<_u` 编译为 `(operator <_u)`（编码名 zz8operatorz0zI_uz9）的带体
    /// 函数，函数体经 zunsigned 转 %i 再做整数比较，128 位无符号值无法用 %i 表示。
    /// 加载期应把这些算子的调用点改写为直接在位向量上比较的 PrimopBinary，
    /// 不再进入原函数体。
    #[test]
    fn operator_comparison_calls_rewrite_to_bits_primops() {
        const IR: &str = r#"
val zz8operatorz0zI_uz9 : (%bv, %bv) -> %bool
fn zz8operatorz0zI_uz9(zx, zy) {
  return = true;
  end;
}

val zcaller : (%bv, %bv) -> %bool
fn zcaller(za, zb) {
  zz1 : %bool `1 1:1-1:9;
  zz1 = zz8operatorz0zI_uz9(za, zb) `1 1:1-1:9;
  return = zz1;
  end;
}
"#;
        let (symtab, mut defs) = parse_ir_string(IR);
        crate::ir::insert_primops(&mut defs, &symtab, crate::ir::AssertionMode::Optimistic, &empty_isa_config());

        let caller = symtab.lookup("zcaller");
        let mut rewritten = 0;
        for def in defs.iter() {
            if let crate::ir::Def::Fn(f, _, body) = def {
                if *f == caller {
                    for instr in body {
                        assert!(!matches!(instr, crate::ir::Instr::Call(..)), "算子调用点不应保留为 Call");
                        if let crate::ir::Instr::PrimopBinary(..) = instr {
                            rewritten += 1;
                        }
                    }
                }
            }
        }
        assert_eq!(rewritten, 1, "期望 `<_u` 调用点被改写为一个 PrimopBinary");
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
            symbolic_registers: Vec::new(),
            value_hints: Vec::new(),
            encoding_slices: Vec::new(),
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
            pma_regions: None,
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
        crate::ir::insert_primops(&mut defs, &symtab, crate::ir::AssertionMode::Optimistic, &empty_isa_config());
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
    fn monomorphize_branch_local_limit_keeps_one_model_inside_selected_region() {
        let var = test_name(100);
        let selected = SourceLoc::new(1, 20, 0, 20, 8);
        let results = run_all_with_shared_state(
            vec![
                Instr::Decl(var, Ty::Bool, selected),
                Instr::Monomorphize(var, Ty::Bool, selected),
                Instr::Copy(Loc::Id(RETURN), Exp::Unit, selected),
                Instr::End,
            ],
            ExecutionLimits::default()
                .with_max_forks_per_branch(0)
                .with_limit_region(SourceRegion::from_source_loc(selected))
                .with_limit_behavior(LimitBehavior::Concretize),
            empty_shared_state(),
        );

        assert_eq!(results.len(), 1);
        assert!(matches!(results[0], Ok(Run::Finished(Val::Unit))));
    }

    #[test]
    fn monomorphize_branch_local_limit_does_not_apply_outside_selected_region() {
        let var = test_name(100);
        let selected = SourceLoc::new(1, 20, 0, 20, 8);
        let outside = SourceLoc::new(2, 20, 0, 20, 8);
        let results = run_all_with_shared_state(
            vec![
                Instr::Decl(var, Ty::Bool, outside),
                Instr::Monomorphize(var, Ty::Bool, outside),
                Instr::Copy(Loc::Id(RETURN), Exp::Unit, outside),
                Instr::End,
            ],
            ExecutionLimits::default()
                .with_max_forks_per_branch(0)
                .with_limit_region(SourceRegion::from_source_loc(selected))
                .with_limit_behavior(LimitBehavior::Concretize),
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

    /// W17（S2 spike）：含 Symbolic 字段（zsizze）的 Struct 装进 List 写入
    /// 寄存器 zpma_regions（defaults 路径，与 initialize_register 相同的
    /// UVal::Init 注入），执行 zspike_match 验证三点：
    /// 1. plausible 放行（形状检查不拒嵌套 Symbolic）；
    /// 2. 执行链完整消费（@is_empty/@hd/@tl + 字段访问 + bv 加减 + 无符号比较，
    ///    无 panic / 静默丢弃），符号 size 进入 SMT；
    /// 3. zrange_subset 的符号比较触发分叉，两条路径各自 Sat 且模型 size 与
    ///    界内/界外一致（访问 [0x80001000, +8)，region base=0x80000000，
    ///    界内 ⟺ size >= 0x1008）。
    #[test]
    fn symbolic_pma_region_size_forks_matching_range() {
        let (shared_state, mut regs, lets) = shared_state_and_bindings_from_ir(SYMBOLIC_PMA_REGIONS_IR);
        let symtab = &shared_state.symtab;
        let zpma = symtab.get(&zencode::encode("pma_regions")).expect("夹具缺 zpma_regions 寄存器");
        let zbase = symtab.get("zbase").expect("夹具缺字段 zbase");
        let zsizze = symtab.get("zsizze").expect("夹具缺字段 zsizze");

        // 构造与 apply_pma_regions_to_config 同形状的值，仅 zsizze 换成符号常量。
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::new(&ctx);
        let size_sym = solver.declare_const(smtlib::Ty::BitVec(64), info());
        let mut fields: ahash::HashMap<Name, Val<B64>> = ahash::HashMap::default();
        fields.insert(zbase, Val::Bits(B64::new(0x8000_0000, 64)));
        fields.insert(zsizze, Val::Symbolic(size_sym));
        let list = Val::List(vec![Val::Struct(fields)]);

        // spike 点 1：plausible 放行
        let register_ty = shared_state.registers.get(&zpma).expect("zpma_regions 必须在寄存器类型表中");
        list.plausible(register_ty, &shared_state).expect("plausible 应放行含符号字段的 List(Struct)");

        // spike 点 2：defaults 路径——与 initialize_register 命中 default_registers 时
        // 相同的 UVal::Init 注入（不发 reset 事件、不走 AssumeReg）。
        regs.insert(zpma, false, UVal::Init(list));

        // 主 solver 声明符号 size 后取 checkpoint，各路径从 checkpoint 派生 solver。
        let cp = checkpoint(&mut solver);

        let func = symtab.lookup("zspike_match");
        let (func_args, ret_ty, func_instrs) = shared_state.functions.get(&func).expect("夹具缺 zspike_match");
        let mut frame = LocalFrame::new(
            func,
            func_args,
            ret_ty,
            Some(&[Val::Bits(B64::new(0x8000_1000, 64)), Val::Bits(B64::new(8, 64))]),
            func_instrs,
        );
        frame.add_regs(&regs).add_lets(&lets);
        let task_state = TaskState::new();
        let queue = Worker::new_lifo();
        queue.push(frame.task_with_checkpoint(TaskId::from_usize(0), &task_state, cp));

        let mut finished: Vec<(bool, u64)> = Vec::new();
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
            let result = run_loop(
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
            )
            .expect("spike 执行不应报错");
            let Run::Finished(ret) = result else {
                panic!("spike 路径应正常结束（Finished），实际非 Finished 结果")
            };
            let Val::Bool(matched) = ret else { panic!("zspike_match 返回值必须是 bool，实际 {:?}", ret) };

            // spike 点 3：路径可满足且模型给出 size 具体值，界内/界外与 matched 一致。
            assert_eq!(solver.check_sat(info()), SmtResult::Sat, "分叉后每条路径都应 Sat");
            let mut model = Model::new(&solver);
            let size = match model.get_var(size_sym).expect("模型必须给出 size 值") {
                ModelVal::Exp(crate::smt::smtlib::Exp::Bits64(bv)) => bv.lower_u64(),
                other => panic!("size 模型值必须是 64 位位向量，实际 {:?}", other),
            };
            if matched {
                assert!(size >= 0x1008, "界内路径模型 size={:#x} 应 >= 0x1008", size);
            } else {
                assert!(size < 0x1008, "界外路径模型 size={:#x} 应 < 0x1008", size);
            }
            finished.push((matched, size));
        }

        // zrange_subset 内有两次符号 jump（offset ≤u size、offset+width ≤u size），
        // 偏移 0x1000 固定可过第一关，故分叉成三条路径：第一关假（size<0x1000）、
        // 第一关真第二关假（0x1000≤size<0x1008）、两关全真（size≥0x1008）。
        assert_eq!(finished.len(), 3, "符号 size 应让 zrange_subset 的两次符号比较各分叉一次");
        assert!(finished.iter().any(|(matched, _)| *matched), "必须有界内（匹配）路径");
        assert_eq!(finished.iter().filter(|(matched, _)| !*matched).count(), 2, "必须有两条界外（不匹配）路径");
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
            None,
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
            None,
            4,
            Some(0),
            &task_state,
        );

        let timeout_hits = *collected.lock().unwrap();
        assert_eq!(timeout_hits, 1, "timeout 后应通过 collector 返回一次，实际 {} 次", timeout_hits);
    }

    #[test]
    fn multi_thread_entry_injects_initial_memory() {
        const MEM_IR: &str = r#"
val zmemtest : (%unit) -> %unit
fn zmemtest(zu) {
  goto 1;
  goto 2;
  end;
}
"#;
        let (shared_state, regs, lets) = shared_state_and_bindings_from_ir(MEM_IR);
        let task_state = TaskState::new();
        let mut mem = crate::memory::Memory::<B64>::new();
        mem.add_symbolic_region(0x1000..0x2000);
        let collected: Arc<std::sync::Mutex<u32>> = Arc::new(std::sync::Mutex::new(0));

        execute_ir_function_with_checkpoint_multi_thread(
            "zmemtest",
            &[Val::Unit],
            &shared_state,
            &regs,
            &lets,
            &collected,
            &|_tid, _id, result, _ss, _solver, count| {
                if let Ok((Run::Finished(_), frame)) = result {
                    let regions = frame.memory().regions();
                    if !regions.is_empty() && regions.iter().any(|r| r.region_range() == &(0x1000..0x2000)) {
                        *count.lock().unwrap() += 1;
                    }
                }
            },
            Checkpoint::new(),
            Some(mem),
            4,
            None,
            &task_state,
        );

        let injected_hits = *collected.lock().unwrap();
        assert!(
            injected_hits >= 1,
            "期望 multi_thread 入口注入 initial_memory，Finished 帧 memory 应含 0x1000..0x2000 symbol region，实际命中 {} 次",
            injected_hits
        );
    }

    #[test]
    fn multi_thread_entry_none_keeps_default_memory() {
        const MEM_IR: &str = r#"
val zmemtest : (%unit) -> %unit
fn zmemtest(zu) {
  goto 1;
  goto 2;
  end;
}
"#;
        let (shared_state, regs, lets) = shared_state_and_bindings_from_ir(MEM_IR);
        let task_state = TaskState::new();
        let collected: Arc<std::sync::Mutex<u32>> = Arc::new(std::sync::Mutex::new(0));

        execute_ir_function_with_checkpoint_multi_thread(
            "zmemtest",
            &[Val::Unit],
            &shared_state,
            &regs,
            &lets,
            &collected,
            &|_tid, _id, result, _ss, _solver, count| {
                if let Ok((Run::Finished(_), frame)) = result {
                    if frame.memory().regions().is_empty() {
                        *count.lock().unwrap() += 1;
                    }
                }
            },
            Checkpoint::new(),
            None,
            4,
            None,
            &task_state,
        );

        let default_hits = *collected.lock().unwrap();
        assert!(default_hits >= 1, "期望传 None 时保持默认空 Memory（region 为空），实际命中 {} 次", default_hits);
    }

    #[test]
    fn multi_thread_read_mem_symbolic_region_event() {
        // read_mem primop 读 concrete 地址 0x1000（落入注入 Memory 的 0x1000..0x2000
        // symbol region），断言 solver trace 产生 region 为 "symbolic" 的 ReadMem 事件，
        // 锁定 注入 → primop → Memory::read → read_symbolic → Event 链路。
        const MEM_IR: &str = r#"
val zreadmem = "read_mem" : (%unit, %i64, %bv, %i) -> %bv
val zmemread : (%unit) -> %unit
fn zmemread(zu) {
  zv : %bv;
  zv = zreadmem(zu, 0, 0x0000000000001000, 1);
  end;
}
"#;
        let (shared_state, regs, lets) = shared_state_and_bindings_from_ir(MEM_IR);
        let task_state = TaskState::new();
        let mut mem = crate::memory::Memory::<B64>::new();
        mem.add_symbolic_region(0x1000..0x2000);
        let collected: Arc<std::sync::Mutex<u32>> = Arc::new(std::sync::Mutex::new(0));

        execute_ir_function_with_checkpoint_multi_thread(
            "zmemread",
            &[Val::Unit],
            &shared_state,
            &regs,
            &lets,
            &collected,
            &|_tid, _id, result, _ss, solver, count| {
                if let Ok((Run::Finished(_), _frame)) = result {
                    let hit = solver.trace().to_vec().into_iter().any(|event| {
                        matches!(event, Event::ReadMem { region, bytes, .. } if *region == "symbolic" && *bytes == 1)
                    });
                    if hit {
                        *count.lock().unwrap() += 1;
                    }
                }
            },
            Checkpoint::new(),
            Some(mem),
            4,
            None,
            &task_state,
        );

        let hits = *collected.lock().unwrap();
        assert!(
            hits >= 1,
            "期望 read_mem 落入注入的 symbol region 并产生 region 为 symbolic 的 ReadMem 事件，实际命中 {} 次",
            hits
        );
    }

    #[test]
    fn multi_thread_read_mem_event_survives_fork() {
        // fork 后再 read_mem：两条 Finished 路径中 false 分支做了读，
        // 断言该路径 collector 收到的 solver.trace() 仍含 ReadMem 事件
        // （锁定 checkpoint/fork 不丢访存事件，对应 solve-state 物化链路）。
        // 初始 checkpoint 非空（先声明若干符号变量再 checkpoint），对齐
        // solve-state 的 setup（symbolic_args）→ checkpoint → multi_thread 形态。
        const MEM_IR: &str = r#"
val zreadmem = "read_mem" : (%unit, %i64, %bv, %i) -> %bv
val zmemreadfork : (%unit) -> %unit
fn zmemreadfork(zu) {
  zb : %bool;
  zv : %bv;
  jump zb goto 4;
  zv = zreadmem(zu, 0, 0x0000000000001000, 1);
  end;
}
"#;
        let (shared_state, regs, lets) = shared_state_and_bindings_from_ir(MEM_IR);
        let task_state = TaskState::new();
        let mut mem = crate::memory::Memory::<B64>::new();
        mem.add_symbolic_region(0x1000..0x2000);
        let collected: Arc<std::sync::Mutex<(u32, u32)>> = Arc::new(std::sync::Mutex::new((0, 0)));

        let cfg = crate::smt::Config::new();
        let ctx = crate::smt::Context::new(cfg);
        let mut setup_solver = crate::smt::Solver::<B64>::new(&ctx);
        for _ in 0..3 {
            let sym = setup_solver.fresh();
            setup_solver.add(crate::smt::smtlib::Def::DeclareConst(sym, crate::smt::smtlib::Ty::BitVec(8)));
        }
        let cp = checkpoint(&mut setup_solver);

        execute_ir_function_with_checkpoint_multi_thread(
            "zmemreadfork",
            &[Val::Unit],
            &shared_state,
            &regs,
            &lets,
            &collected,
            &|_tid, _id, result, _ss, solver, count| {
                if let Ok((Run::Finished(_), _frame)) = result {
                    let hit = solver
                        .trace()
                        .to_vec()
                        .into_iter()
                        .any(|event| matches!(event, Event::ReadMem { region, bytes, .. } if *region == "symbolic" && *bytes == 1));
                    let mut count = count.lock().unwrap();
                    count.0 += 1;
                    if hit {
                        count.1 += 1;
                    }
                }
            },
            cp,
            Some(mem),
            4,
            None,
            &task_state,
        );

        let (finished, event_hits) = *collected.lock().unwrap();
        assert!(finished >= 2, "期望符号分支 fork 出至少 2 条 Finished 路径，实际 {}", finished);
        assert!(
            event_hits >= 1,
            "期望做读的分支在 collector 收到的 solver trace 中保留 ReadMem 事件，实际命中 {} 次",
            event_hits
        );
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
        // 返回值编码 (marker, 受限分支抽到的方向)：{0,1} 是抽到 false 的两条路径，{2,3} 是抽到
        // true 的两条路径。两条兄弟路径的签名在第一个分支点就分叉，因此必然一条落在 {0,1}、
        // 另一条落在 {2,3}；同时这个结果不随 worker 数变化。
        let expected = run_worker_invariant_sampling_program(0);
        assert!(expected == vec![(0, 1), (3, 1)] || expected == vec![(1, 1), (2, 1)], "{:?}", expected);

        for _ in 0..20 {
            assert_eq!(run_worker_invariant_sampling_program(1), expected);
            assert_eq!(run_worker_invariant_sampling_program(4), expected);
        }
    }

    mod review9_tests {
        use super::*;

        #[test]
        fn signed_symbolic_shift_boundaries() {
            for op in ["shiftr", "shiftl", "arith_shiftr"] {
                for amount in [i128::MIN, -256, -8, -1, 0, 1, 7, 8, 256, i128::MAX] {
                    for value in [1, 0x80] {
                        for symbolic_bits in [false, true] {
                            let ctx = Context::new(Config::new());
                            let mut solver = Solver::<B64>::new(&ctx);
                            let bits = B64::new(value, 8);
                            let input = if symbolic_bits {
                                Val::Symbolic(solver.define_const(crate::primop_util::smt_sbits(bits), info()))
                            } else {
                                Val::Bits(bits)
                            };
                            let shift = solver.declare_const(smtlib::Ty::BitVec(128), info());
                            solver.assert_eq(smtlib::Exp::Var(shift), crate::primop_util::smt_i128(amount));
                            let f = *crate::primop::binary_primops::<B64>().get(op).unwrap();
                            let actual = f(input, Val::Symbolic(shift), &mut solver, info()).unwrap();
                            let expected = f(Val::Bits(bits), Val::I128(amount), &mut solver, info()).unwrap();
                            let wrong = smtlib::Exp::Neq(
                                Box::new(crate::primop_util::smt_value(&actual, info()).unwrap()),
                                Box::new(crate::primop_util::smt_value(&expected, info()).unwrap()),
                            );
                            assert_eq!(
                                solver.check_sat_with(&wrong, info()),
                                crate::smt::SmtResult::Unsat,
                                "符号移位不一致：{op}，移位量={amount}，数据={value}，符号数据={symbolic_bits}"
                            );
                        }
                    }
                }
            }
        }

        #[test]
        fn constructor_tags_and_payloads() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let a = test_name(180);
            let b = test_name(181);
            let left_cond = solver.declare_const(smtlib::Ty::Bool, info());
            let right_cond = solver.declare_const(smtlib::Ty::Bool, info());
            let ctor = |tag, payload| Val::Ctor(tag, Box::new(Val::I128(payload)));
            let left = crate::primop_util::build_ite(left_cond, &ctor(a, 1), &ctor(b, 2), &mut solver, info()).unwrap();
            for (a_payload, b_payload) in [(1, 2), (3, 2), (3, 4)] {
                let right = crate::primop_util::build_ite(
                    right_cond,
                    &ctor(a, a_payload),
                    &ctor(b, b_payload),
                    &mut solver,
                    info(),
                )
                .unwrap();
                for unequal in [false, true] {
                    let f = if unequal { crate::primop::op_neq::<B64> } else { crate::primop::op_eq::<B64> };
                    let actual = f(left.clone(), right.clone(), &mut solver, info()).unwrap();
                    let mut expected = smtlib::Exp::Or(
                        Box::new(smtlib::Exp::And(
                            Box::new(smtlib::Exp::Var(left_cond)),
                            Box::new(smtlib::Exp::And(
                                Box::new(smtlib::Exp::Var(right_cond)),
                                Box::new(smtlib::Exp::Bool(a_payload == 1)),
                            )),
                        )),
                        Box::new(smtlib::Exp::And(
                            Box::new(smtlib::Exp::Not(Box::new(smtlib::Exp::Var(left_cond)))),
                            Box::new(smtlib::Exp::And(
                                Box::new(smtlib::Exp::Not(Box::new(smtlib::Exp::Var(right_cond)))),
                                Box::new(smtlib::Exp::Bool(b_payload == 2)),
                            )),
                        )),
                    );
                    if unequal {
                        expected = smtlib::Exp::Not(Box::new(expected));
                    }
                    let wrong = smtlib::Exp::Neq(
                        Box::new(crate::primop_util::smt_value(&actual, info()).unwrap()),
                        Box::new(expected),
                    );
                    assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
                }
            }
            let disjoint = crate::primop_util::build_ite(
                right_cond,
                &ctor(test_name(182), 1),
                &ctor(test_name(183), 2),
                &mut solver,
                info(),
            )
            .unwrap();
            assert_eq!(crate::primop::eq_anything(left, disjoint, &mut solver, info()).unwrap(), Val::Bool(false));
        }

        #[test]
        fn unsigned_concrete_and_symbolic_range() {
            use crate::bitvector::b129::B129;
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let unsigned = *crate::primop::unary_primops::<B129>().get("sail_unsigned").unwrap();
            for bits in [B129::ones(128), B129::ones(129), B129::new(1, 129) << B129::new(127, 129)] {
                assert!(matches!(unsigned(Val::Bits(bits), &mut solver, info()), Err(ExecError::Overflow)));
            }
            assert_eq!(unsigned(Val::Bits(B129::ones(127)), &mut solver, info()).unwrap(), Val::I128(i128::MAX));
            let bits = solver.declare_const(smtlib::Ty::BitVec(128), info());
            // 混合范围交回执行器分叉，转换层不得自行删除溢出模型。
            assert!(matches!(
                unsigned(Val::Symbolic(bits), &mut solver, info()),
                Err(ExecError::IntegerConversion(_, _))
            ));
            assert_eq!(
                solver.check_sat_with(
                    &smtlib::Exp::Bvslt(Box::new(smtlib::Exp::Var(bits)), Box::new(crate::primop_util::smt_i128(0))),
                    info()
                ),
                crate::smt::SmtResult::Sat
            );
            let overflow = solver.declare_bitvector(128, info());
            solver.assert(smtlib::Exp::Bvslt(
                Box::new(smtlib::Exp::Var(overflow)),
                Box::new(crate::primop_util::smt_i128(0)),
            ));
            assert!(matches!(unsigned(Val::Symbolic(overflow), &mut solver, info()), Err(ExecError::Overflow)));
            solver.assert(smtlib::Exp::Bvsge(
                Box::new(smtlib::Exp::Var(bits)),
                Box::new(crate::primop_util::smt_i128(0)),
            ));
            assert_eq!(unsigned(Val::Symbolic(bits), &mut solver, info()).unwrap(), Val::Symbolic(bits));
        }

        #[test]
        fn pow_symbolic_base_values_and_exponent_retry() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let base = solver.declare_const(smtlib::Ty::BitVec(128), info());
            let pow = *crate::primop::binary_primops::<B64>().get("pow_int").unwrap();
            assert!(matches!(pow(Val::Symbolic(base), Val::I128(-1), &mut solver, info()), Err(ExecError::Overflow)));
            assert_eq!(pow(Val::Symbolic(base), Val::I128(0), &mut solver, info()).unwrap(), Val::I128(1));
            assert_eq!(pow(Val::Symbolic(base), Val::I128(1), &mut solver, info()).unwrap(), Val::Symbolic(base));
            let cube = pow(Val::Symbolic(base), Val::I128(3), &mut solver, info()).unwrap();
            solver.assert_eq(smtlib::Exp::Var(base), crate::primop_util::smt_i128(-3));
            let wrong = smtlib::Exp::Neq(
                Box::new(crate::primop_util::smt_value(&cube, info()).unwrap()),
                Box::new(crate::primop_util::smt_i128(-27)),
            );
            assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
            let cond = test_name(180);
            let exponent = test_name(181);
            let results = run_all_with_bindings(
                vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(exponent, Ty::I128, info()),
                    Instr::Jump(Exp::Id(cond), 5, info()),
                    Instr::Copy(Loc::Id(exponent), Exp::I128(2), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(exponent), Exp::I128(3), info()),
                    Instr::PrimopBinary(Loc::Id(RETURN), pow, Exp::I128(3), Exp::Id(exponent), info()),
                    Instr::End,
                ],
                ExecutionLimits::default().with_path_merging(true),
                empty_shared_state(),
                RegisterBindings::new(),
                HashMap::default(),
            );
            assert_eq!(results.len(), 2);
            assert!(results.iter().all(Result::is_ok));
        }

        #[test]
        fn vector_access_index_widths() {
            use crate::bitvector::b129::B129;
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            for data_width in [8, 64, 128, 129] {
                let bits = B129::new(1, data_width);
                let data = solver.define_const(crate::primop_util::smt_sbits(bits), info());
                for index_width in [8, 64, 128, 129, 256] {
                    let index = solver.declare_const(smtlib::Ty::BitVec(index_width), info());
                    for input in [Val::Bits(bits), Val::Symbolic(data)] {
                        let actual =
                            crate::primop::vector_access(input, Val::Symbolic(index), &mut solver, info()).unwrap();
                        let expected = smtlib::Exp::Ite(
                            Box::new(smtlib::Exp::Eq(
                                Box::new(smtlib::Exp::Var(index)),
                                Box::new(crate::primop::smt_zeros(i128::from(index_width))),
                            )),
                            Box::new(smtlib::Exp::Bits64(B64::new(1, 1))),
                            Box::new(smtlib::Exp::Bits64(B64::new(0, 1))),
                        );
                        // 索引只取合法位置，独立验证宽度调整与取位结果。
                        let in_range = smtlib::Exp::Bvult(
                            Box::new(smtlib::Exp::Var(index)),
                            Box::new(smtlib::bits64(u64::from(data_width), index_width)),
                        );
                        let wrong = smtlib::Exp::And(
                            Box::new(in_range),
                            Box::new(smtlib::Exp::Neq(
                                Box::new(crate::primop_util::smt_value(&actual, info()).unwrap()),
                                Box::new(expected),
                            )),
                        );
                        assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
                    }
                    for n in [0, 1] {
                        let actual =
                            crate::primop::vector_access(Val::Symbolic(data), Val::I128(n), &mut solver, info())
                                .unwrap();
                        let wrong = smtlib::Exp::Neq(
                            Box::new(crate::primop_util::smt_value(&actual, info()).unwrap()),
                            Box::new(smtlib::Exp::Bits64(B64::new(if n == 0 { 1 } else { 0 }, 1))),
                        );
                        assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
                    }
                }
            }
        }

        #[test]
        fn wide_bitvector_shift_amounts() {
            use crate::bitvector::b129::B129;
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            for (data_width, shift_width, amount) in
                [(8, 16, 256), (129, 8, 1), (128, 129, 128), (8, 128, 256), (8, 8, 1)]
            {
                let bits = B129::new(0x81, data_width);
                let shift = B129::new(amount, shift_width);
                let data_sym = solver.define_const(crate::primop_util::smt_sbits(bits), info());
                let shift_sym = solver.define_const(crate::primop_util::smt_sbits(shift), info());
                for op in [
                    crate::primop::shift_bits_left::<B129> as crate::primop::Binary<B129>,
                    crate::primop::shift_bits_right::<B129>,
                ] {
                    let expected = op(Val::Bits(bits), Val::Bits(shift), &mut solver, info()).unwrap();
                    for data in [Val::Bits(bits), Val::Symbolic(data_sym)] {
                        for shift in [Val::Bits(shift), Val::Symbolic(shift_sym)] {
                            let actual = op(data.clone(), shift, &mut solver, info()).unwrap();
                            let wrong = smtlib::Exp::Neq(
                                Box::new(crate::primop_util::smt_value(&actual, info()).unwrap()),
                                Box::new(crate::primop_util::smt_value(&expected, info()).unwrap()),
                            );
                            assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
                        }
                    }
                }
            }
        }

        #[test]
        fn vector_update_nested_elements_preserves_selected_index() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let mut frame = make_frame(vec![Instr::End]);
            let field = test_name(180);
            let old_struct = Val::Struct(HashMap::from_iter([(field, Val::Bool(false))]));
            let new_struct = Val::Struct(HashMap::from_iter([(field, Val::Bool(true))]));
            let old_ctor = Val::Ctor(test_name(181), Box::new(old_struct.clone()));
            let new_ctor = Val::Ctor(test_name(182), Box::new(new_struct.clone()));
            for (old, new) in [
                (old_struct, new_struct),
                (old_ctor.clone(), new_ctor.clone()),
                (
                    Val::Struct(HashMap::from_iter([(field, old_ctor)])),
                    Val::Struct(HashMap::from_iter([(field, new_ctor)])),
                ),
            ] {
                for width in [64, 128] {
                    let index = solver.declare_const(smtlib::Ty::BitVec(width), info());
                    let actual = crate::primop::vector_update(
                        vec![Val::Vector(vec![old.clone(), old.clone()]), Val::Symbolic(index), new.clone()],
                        &mut solver,
                        &mut frame,
                        info(),
                    )
                    .unwrap();
                    let Val::Vector(items) = actual else { panic!("向量更新必须返回向量") };
                    for (i, item) in items.into_iter().enumerate() {
                        let selected = smtlib::Exp::Eq(
                            Box::new(smtlib::Exp::Var(index)),
                            Box::new(smtlib::bits64(i as u64, width)),
                        );
                        let equals_new =
                            crate::primop::eq_anything(item.clone(), new.clone(), &mut solver, info()).unwrap();
                        let equals_old = crate::primop::eq_anything(item, old.clone(), &mut solver, info()).unwrap();
                        let wrong = smtlib::Exp::Or(
                            Box::new(smtlib::Exp::Neq(
                                Box::new(crate::primop_util::smt_value(&equals_new, info()).unwrap()),
                                Box::new(selected.clone()),
                            )),
                            Box::new(smtlib::Exp::Neq(
                                Box::new(crate::primop_util::smt_value(&equals_old, info()).unwrap()),
                                Box::new(smtlib::Exp::Not(Box::new(selected))),
                            )),
                        );
                        assert_eq!(solver.check_sat_with(&wrong, info()), crate::smt::SmtResult::Unsat);
                    }
                }
            }
        }

        #[test]
        fn adversarial_review_shift_equivalence() {
            let mut failures = Vec::new();
            for (op, amount, left, right) in
                [("shiftr", -1, 1, 2), ("shiftl", -1, 4, 8), ("arith_shiftr", 256, 0x80, 0x81)]
            {
                let ctx = Context::new(Config::new());
                let mut solver = Solver::<B64>::new(&ctx);
                let cond = solver.declare_const(smtlib::Ty::Bool, info());
                let x = test_name(180);
                let shared = empty_shared_state();
                let mut frame = make_frame(vec![
                    Instr::Jump(Exp::Bool(true), 3, info()),
                    Instr::Copy(Loc::Id(x), Exp::Bits(B64::new(left, 8)), info()),
                    Instr::Goto(4),
                    Instr::Copy(Loc::Id(x), Exp::Bits(B64::new(right, 8)), info()),
                    Instr::End,
                ]);
                frame.vars_mut().insert(x, UVal::Uninit(&Ty::Bits(8)));
                assert_eq!(
                    try_merge_diamond(cond, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(),
                    Some(4)
                );
                let f = *crate::primop::binary_primops::<B64>().get(op).unwrap();
                let input =
                    eval_exp(&Exp::Id(x), &mut frame.local_state, &shared, &mut solver, info()).unwrap().into_owned();
                let actual = f(input, Val::I128(amount), &mut solver, info()).unwrap();
                let expected_then = f(Val::Bits(B64::new(right, 8)), Val::I128(amount), &mut solver, info()).unwrap();
                let expected_else = f(Val::Bits(B64::new(left, 8)), Val::I128(amount), &mut solver, info()).unwrap();
                let expected =
                    crate::primop_util::build_ite(cond, &expected_then, &expected_else, &mut solver, info()).unwrap();
                let wrong = smtlib::Exp::Neq(
                    Box::new(crate::primop_util::smt_value(&actual, info()).unwrap()),
                    Box::new(crate::primop_util::smt_value(&expected, info()).unwrap()),
                );
                let result = solver.check_sat_with(&wrong, info());
                eprintln!("移位反例：{op}，移位量={amount}，错误结果可满足={result:?}");
                if result != crate::smt::SmtResult::Unsat {
                    failures.push((op, amount));
                }
            }
            assert!(failures.is_empty(), "移位语义不一致：{failures:?}");
        }

        #[test]
        fn adversarial_review_bits_shift_equivalence() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let left = Val::Bits(B64::new(1, 8));
            let right = Val::Bits(B64::new(2, 8));
            let merged = crate::primop_util::merge_val(cond, &left, &right, &mut solver, info()).unwrap();
            let mut failures = Vec::new();
            for (op, f) in [
                ("shift_bits_left", crate::primop::shift_bits_left::<B64> as crate::primop::Binary<B64>),
                ("shift_bits_right", crate::primop::shift_bits_right::<B64>),
            ] {
                let shift = Val::Bits(B64::new(256, 16));
                assert_eq!(f(left.clone(), shift.clone(), &mut solver, info()).unwrap(), Val::Bits(B64::new(0, 8)));
                assert_eq!(f(right.clone(), shift.clone(), &mut solver, info()).unwrap(), Val::Bits(B64::new(0, 8)));
                let actual = f(merged.clone(), shift, &mut solver, info()).unwrap();
                let wrong = smtlib::Exp::Neq(
                    Box::new(crate::primop_util::smt_value(&actual, info()).unwrap()),
                    Box::new(crate::primop_util::smt_value(&Val::Bits(B64::new(0, 8)), info()).unwrap()),
                );
                let result = solver.check_sat_with(&wrong, info());
                eprintln!("宽移位量反例：{op}，错误结果可满足={result:?}");
                if result != crate::smt::SmtResult::Unsat {
                    failures.push(op);
                }
            }
            assert!(failures.is_empty(), "位向量移位语义不一致：{failures:?}");
        }

        #[test]
        fn adversarial_review_vector_update_struct() {
            for enabled in [false, true] {
                let cond = test_name(180);
                let bits = test_name(181);
                let index = test_name(182);
                let vector = test_name(183);
                let update = test_name(184);
                let field = test_name(185);
                let a = Val::Struct(HashMap::from_iter([(field, Val::Bool(false))]));
                let b = Val::Struct(HashMap::from_iter([(field, Val::Bool(true))]));
                let mut lets = HashMap::default();
                lets.insert(vector, UVal::Init(Val::Vector(vec![a.clone(), a])));
                lets.insert(update, UVal::Init(b));
                let unsigned = *crate::primop::unary_primops::<B64>().get("sail_unsigned").unwrap();
                let update_op = *crate::primop::variadic_primops::<B64>().get("vector_update").unwrap();
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(cond, Ty::Bool, info()),
                        Instr::Decl(bits, Ty::Bits(8), info()),
                        Instr::Decl(index, Ty::I128, info()),
                        Instr::Jump(Exp::Id(cond), 6, info()),
                        Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(0, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::PrimopUnary(Loc::Id(index), unsigned, Exp::Id(bits), info()),
                        Instr::PrimopVariadic(
                            Loc::Id(RETURN),
                            update_op,
                            vec![Exp::Id(vector), Exp::Id(index), Exp::Id(update)],
                            info(),
                        ),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    lets,
                );
                let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
                eprintln!("结构向量更新：合并={enabled}，路径数={}，错误={errors:?}", results.len());
                assert!(errors.is_empty());
            }
        }

        #[test]
        fn adversarial_review_constructor_self_equality() {
            for enabled in [false, true] {
                let mut shared = empty_shared_state();
                let cond = shared.symtab.intern("zcond");
                let x = shared.symtab.intern("zx");
                let a = shared.symtab.intern("za");
                let b = shared.symtab.intern("zb");
                let tag_a = shared.symtab.intern("zA");
                let tag_b = shared.symtab.intern("zB");
                let mut lets = HashMap::default();
                lets.insert(a, UVal::Init(Val::Ctor(tag_a, Box::new(Val::Unit))));
                lets.insert(b, UVal::Init(Val::Ctor(tag_b, Box::new(Val::Unit))));
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(cond, Ty::Bool, info()),
                        Instr::Decl(x, Ty::Union(test_name(181)), info()),
                        Instr::Jump(Exp::Id(cond), 5, info()),
                        Instr::Copy(Loc::Id(x), Exp::Id(a), info()),
                        Instr::Goto(6),
                        Instr::Copy(Loc::Id(x), Exp::Id(b), info()),
                        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(x), Exp::Id(x)]), info()),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    shared,
                    RegisterBindings::new(),
                    lets,
                );
                let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
                eprintln!("构造子自比较：合并={enabled}，路径数={}，错误={errors:?}", results.len());
                assert!(errors.is_empty());
            }
        }

        #[test]
        fn adversarial_review_pow_symbolic_base() {
            for enabled in [false, true] {
                let cond = test_name(180);
                let x = test_name(181);
                let n = test_name(182);
                let unsigned = *crate::primop::unary_primops::<B64>().get("sail_unsigned").unwrap();
                let pow = *crate::primop::binary_primops::<B64>().get("pow_int").unwrap();
                let results = run_all_with_bindings(
                    vec![
                        Instr::Decl(cond, Ty::Bool, info()),
                        Instr::Decl(x, Ty::Bits(8), info()),
                        Instr::Decl(n, Ty::I128, info()),
                        Instr::Jump(Exp::Id(cond), 6, info()),
                        Instr::Copy(Loc::Id(x), Exp::Bits(B64::new(2, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(x), Exp::Bits(B64::new(3, 8)), info()),
                        Instr::PrimopUnary(Loc::Id(n), unsigned, Exp::Id(x), info()),
                        Instr::PrimopBinary(Loc::Id(RETURN), pow, Exp::Id(n), Exp::I128(2), info()),
                        Instr::End,
                    ],
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
                eprintln!("整数幂符号底数：合并={enabled}，路径数={}，错误={errors:?}", results.len());
                assert!(errors.is_empty());
            }
        }

        #[test]
        fn adversarial_review_unsigned_128_sign() {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let bits = solver.declare_const(smtlib::Ty::BitVec(128), info());
            solver.assert_eq(smtlib::Exp::Var(bits), crate::primop_util::smt_i128(-1));
            let unsigned = *crate::primop::unary_primops::<B64>().get("sail_unsigned").unwrap();
            assert!(matches!(unsigned(Val::Symbolic(bits), &mut solver, info()), Err(ExecError::Overflow)));
        }

        #[test]
        fn review_wide_vector_access_crash() {
            use crate::bitvector::b129::B129;
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let data = Val::Bits(B129::new(1, 129));
            for n in [0, 1] {
                let value = crate::primop::vector_access(data.clone(), Val::I128(n), &mut solver, info()).unwrap();
                assert_eq!(value, Val::Bits(B129::new(if n == 0 { 1 } else { 0 }, 1)));
            }
            let merged = crate::primop_util::merge_val(
                cond,
                &Val::Bits(B129::new(0, 8)),
                &Val::Bits(B129::new(1, 8)),
                &mut solver,
                info(),
            )
            .unwrap();
            let unsigned = *crate::primop::unary_primops::<B129>().get("sail_unsigned").unwrap();
            let index = unsigned(merged, &mut solver, info()).unwrap();
            let actual = crate::primop::vector_access(data, index, &mut solver, info()).unwrap();
            assert!(matches!(actual, Val::Symbolic(_)));
        }
    }

    #[test]
    fn review7_unsigned_128_preserves_nonnegative() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let bits = solver.declare_const(smtlib::Ty::BitVec(128), info());
        let unsigned = *crate::primop::unary_primops::<B64>().get("sail_unsigned").unwrap();
        solver.assert(smtlib::Exp::Bvsge(Box::new(smtlib::Exp::Var(bits)), Box::new(crate::primop_util::smt_i128(0))));
        let value = unsigned(Val::Symbolic(bits), &mut solver, info()).unwrap();
        assert_eq!(value, Val::Symbolic(bits));
        for input in [0, i128::MAX, i128::MIN, -1] {
            let query =
                smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(bits)), Box::new(crate::primop_util::smt_i128(input)));
            assert_eq!(
                solver.check_sat_with(&query, info()),
                if input >= 0 { crate::smt::SmtResult::Sat } else { crate::smt::SmtResult::Unsat }
            );
        }
    }

    #[test]
    fn review7_slice_machine_index_width() {
        for enabled in [false, true] {
            let cond = test_name(180);
            let index = test_name(181);
            let bits = test_name(182);
            let instrs = vec![
                Instr::Decl(cond, Ty::Bool, info()),
                Instr::Decl(index, Ty::I64, info()),
                Instr::Decl(bits, Ty::Bits(128), info()),
                Instr::Init(
                    bits,
                    Ty::Bits(128),
                    Exp::Call(Op::Concat, vec![Exp::Bits(B64::new(1, 64)), Exp::Bits(B64::new(2, 64))]),
                    info(),
                ),
                Instr::Jump(Exp::Id(cond), 7, info()),
                Instr::Copy(Loc::Id(index), Exp::I64(0), info()),
                Instr::Goto(8),
                Instr::Copy(Loc::Id(index), Exp::I64(8), info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Slice(8), vec![Exp::Id(bits), Exp::Id(index)]), info()),
                Instr::End,
            ];
            let results = run_all_with_bindings(
                instrs,
                ExecutionLimits::default().with_path_merging(enabled),
                empty_shared_state(),
                RegisterBindings::new(),
                HashMap::default(),
            );
            let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
            eprintln!("机器整数切片索引：合并={enabled}，完成={}，错误={errors:?}", results.len());
            assert!(errors.is_empty());
        }
    }

    #[test]
    fn review7_retry_preserves_finite_operand() {
        for stored in [true, false] {
            let zeros = *crate::primop::unary_primops::<B64>().get("zeros").unwrap();
            let mut shared = empty_shared_state();
            let lengths = shared.symtab.intern("zlengths");
            let length = shared.symtab.intern("zlength");
            let mut lets = HashMap::default();
            lets.insert(lengths, UVal::Init(Val::Vector(vec![Val::I128(8), Val::I128(16)])));
            let operand = Exp::Call(Op::Bvaccess, vec![Exp::Id(lengths), Exp::Undefined(Ty::I128)]);
            let mut instrs = Vec::new();
            if stored {
                instrs.push(Instr::Init(length, Ty::I128, operand.clone(), info()));
            }
            instrs.push(Instr::PrimopUnary(
                Loc::Id(RETURN),
                zeros,
                if stored { Exp::Id(length) } else { operand },
                info(),
            ));
            instrs.push(Instr::End);
            let results = run_all_with_bindings(
                instrs,
                ExecutionLimits::default().with_max_forks_per_path(3),
                shared,
                RegisterBindings::new(),
                lets,
            );
            let finished = results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count();
            let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
            eprintln!("128 位有限长度 8/16：先存变量={stored}，完成={finished}，错误={errors:?}");
            assert_eq!(finished, 2, "有限的两个长度应各执行一次");
        }
    }

    #[test]
    fn symbolic_length_retry_preserves_binary_and_variadic_operands() {
        for consumer in ["vector_init", "get_slice_int", "sail_truncate"] {
            let mut shared = empty_shared_state();
            let lengths = shared.symtab.intern("zlengths");
            let mut lets = HashMap::default();
            lets.insert(lengths, UVal::Init(Val::Vector(vec![Val::I128(8), Val::I128(16)])));
            let operand = Exp::Call(Op::Bvaccess, vec![Exp::Id(lengths), Exp::Undefined(Ty::I128)]);
            let consume = match consumer {
                "vector_init" => Instr::PrimopBinary(
                    Loc::Id(RETURN),
                    *crate::primop::binary_primops::<B64>().get(consumer).unwrap(),
                    operand,
                    Exp::I128(0),
                    info(),
                ),
                "get_slice_int" => Instr::PrimopVariadic(
                    Loc::Id(RETURN),
                    *crate::primop::variadic_primops::<B64>().get(consumer).unwrap(),
                    vec![operand, Exp::I128(0), Exp::I128(0)],
                    info(),
                ),
                "sail_truncate" => Instr::PrimopBinary(
                    Loc::Id(RETURN),
                    *crate::primop::binary_primops::<B64>().get(consumer).unwrap(),
                    Exp::Bits(B64::new(0xffff, 16)),
                    operand,
                    info(),
                ),
                _ => unreachable!(),
            };
            let results = run_all_with_bindings(
                vec![consume, Instr::End],
                ExecutionLimits::default().with_max_forks_per_path(3),
                shared,
                RegisterBindings::new(),
                lets,
            );
            let mut widths: Vec<_> = results
                .into_iter()
                .map(|result| match result.unwrap() {
                    Run::Finished(Val::Vector(values)) => values.len() as u32,
                    Run::Finished(Val::Bits(bits)) => bits.len(),
                    Run::Finished(value) => panic!("长度消费者 {consumer} 返回了错误类型：{value:?}"),
                    Run::Dead | Run::Exit | Run::Suspended => panic!("长度消费者 {consumer} 未正常完成"),
                })
                .collect();
            widths.sort_unstable();
            assert_eq!(widths, vec![8, 16], "{consumer} 必须复用拆分前的操作数");
        }
    }

    #[test]
    fn review7_vector_update_i64_index() {
        for enabled in [false, true] {
            let mut shared = empty_shared_state();
            let cond = shared.symtab.intern("zcond");
            let index = shared.symtab.intern("zindex");
            let vec = shared.symtab.intern("zvec");
            let init = *crate::primop::binary_primops::<B64>().get("vector_init").unwrap();
            let update = *crate::primop::variadic_primops::<B64>().get("vector_update").unwrap();
            let instrs = vec![
                Instr::Decl(cond, Ty::Bool, info()),
                Instr::Decl(index, Ty::I64, info()),
                Instr::Decl(vec, Ty::Vector(Box::new(Ty::I128)), info()),
                Instr::PrimopBinary(Loc::Id(vec), init, Exp::I128(2), Exp::I128(0), info()),
                Instr::Jump(Exp::Id(cond), 7, info()),
                Instr::Copy(Loc::Id(index), Exp::I64(0), info()),
                Instr::Goto(8),
                Instr::Copy(Loc::Id(index), Exp::I64(1), info()),
                Instr::PrimopVariadic(Loc::Id(vec), update, vec![Exp::Id(vec), Exp::Id(index), Exp::I128(7)], info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                Instr::End,
            ];
            let results = run_all_with_bindings(
                instrs,
                ExecutionLimits::default().with_path_merging(enabled),
                shared,
                RegisterBindings::new(),
                HashMap::default(),
            );
            eprintln!("vector_update：合并={enabled}，完成={}", results.len());
            assert!(results.iter().all(|r| matches!(r, Ok(Run::Finished(_)))));
        }
    }

    #[test]
    fn review7_dynamic_length_slice() {
        for consumer in ["slice"] {
            for enabled in [false, true] {
                let cond = test_name(160);
                let length = test_name(161);
                let wide = test_name(162);
                let buffer = test_name(163);
                let consume = match consumer {
                    "zeros" | "ones" => Instr::PrimopUnary(
                        Loc::Id(buffer),
                        *crate::primop::unary_primops::<B64>().get(consumer).unwrap(),
                        Exp::Id(wide),
                        info(),
                    ),
                    "sail_truncate" => Instr::PrimopBinary(
                        Loc::Id(buffer),
                        *crate::primop::binary_primops::<B64>().get(consumer).unwrap(),
                        Exp::Bits(B64::new(1, 64)),
                        Exp::Id(wide),
                        info(),
                    ),
                    "undefined_vector" | "vector_init" => Instr::PrimopBinary(
                        Loc::Id(buffer),
                        *crate::primop::binary_primops::<B64>().get(consumer).unwrap(),
                        Exp::Id(wide),
                        Exp::Bool(false),
                        info(),
                    ),
                    "slice" => Instr::PrimopVariadic(
                        Loc::Id(buffer),
                        *crate::primop::variadic_primops::<B64>().get(consumer).unwrap(),
                        vec![Exp::Bits(B64::new(1, 64)), Exp::I128(0), Exp::Id(wide)],
                        info(),
                    ),
                    "vector_subrange" | "vector_subrange_low" => Instr::PrimopVariadic(
                        Loc::Id(buffer),
                        *crate::primop::variadic_primops::<B64>().get("vector_subrange").unwrap(),
                        if consumer == "vector_subrange_low" {
                            vec![Exp::Bits(B64::new(0, 64)), Exp::I128(23), Exp::Id(wide)]
                        } else {
                            vec![Exp::Bits(B64::new(0, 64)), Exp::Id(wide), Exp::I128(1)]
                        },
                        info(),
                    ),
                    _ => unreachable!(),
                };
                let widen = *crate::primop::unary_primops::<B64>().get("%i64->%i").unwrap();
                let instrs = vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(length, Ty::I64, info()),
                    Instr::Decl(wide, Ty::I128, info()),
                    Instr::Decl(buffer, Ty::AnyBits, info()),
                    Instr::Jump(Exp::Id(cond), 7, info()),
                    Instr::Copy(Loc::Id(length), Exp::I64(8), info()),
                    Instr::Goto(8),
                    Instr::Copy(Loc::Id(length), Exp::I64(16), info()),
                    Instr::PrimopUnary(Loc::Id(wide), widen, Exp::Id(length), info()),
                    consume,
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(buffer), info()),
                    Instr::End,
                ];
                let results = run_all_with_bindings(
                    instrs,
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                let finished = results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count();
                let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
                eprintln!(
                    "第七轮未覆盖的长度消费者：算子={consumer}，合并={enabled}，完成={finished}，错误={errors:?}"
                );
                assert!(errors.is_empty(), "合法动态长度路径不应在合并后失败");
                let mut widths: Vec<_> = results
                    .iter()
                    .filter_map(|result| match result {
                        Ok(Run::Finished(Val::Bits(bits))) => Some(bits.len()),
                        Ok(Run::Finished(Val::Vector(values))) => Some(values.len() as u32),
                        _ => None,
                    })
                    .collect();
                widths.sort_unstable();
                assert_eq!(widths, vec![8, 16], "必须完成两个不同长度候选");
            }
        }
    }

    #[test]
    fn review7_pow_int_after_i64_merge() {
        for consumer in ["pow_int"] {
            for enabled in [false, true] {
                let cond = test_name(160);
                let length = test_name(161);
                let wide = test_name(162);
                let buffer = test_name(163);
                let consume = match consumer {
                    "zeros" | "ones" => Instr::PrimopUnary(
                        Loc::Id(buffer),
                        *crate::primop::unary_primops::<B64>().get(consumer).unwrap(),
                        Exp::Id(wide),
                        info(),
                    ),
                    "pow_int" => Instr::PrimopBinary(
                        Loc::Id(buffer),
                        *crate::primop::binary_primops::<B64>().get(consumer).unwrap(),
                        Exp::I128(2),
                        Exp::Id(wide),
                        info(),
                    ),
                    "undefined_vector" | "vector_init" => Instr::PrimopBinary(
                        Loc::Id(buffer),
                        *crate::primop::binary_primops::<B64>().get(consumer).unwrap(),
                        Exp::Id(wide),
                        Exp::Bool(false),
                        info(),
                    ),
                    "slice" => Instr::PrimopVariadic(
                        Loc::Id(buffer),
                        *crate::primop::variadic_primops::<B64>().get(consumer).unwrap(),
                        vec![Exp::Bits(B64::new(1, 64)), Exp::I128(0), Exp::Id(wide)],
                        info(),
                    ),
                    "vector_subrange" | "vector_subrange_low" => Instr::PrimopVariadic(
                        Loc::Id(buffer),
                        *crate::primop::variadic_primops::<B64>().get("vector_subrange").unwrap(),
                        if consumer == "vector_subrange_low" {
                            vec![Exp::Bits(B64::new(0, 64)), Exp::I128(23), Exp::Id(wide)]
                        } else {
                            vec![Exp::Bits(B64::new(0, 64)), Exp::Id(wide), Exp::I128(1)]
                        },
                        info(),
                    ),
                    _ => unreachable!(),
                };
                let widen = *crate::primop::unary_primops::<B64>().get("%i64->%i").unwrap();
                let instrs = vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(length, Ty::I64, info()),
                    Instr::Decl(wide, Ty::I128, info()),
                    Instr::Decl(buffer, Ty::AnyBits, info()),
                    Instr::Jump(Exp::Id(cond), 7, info()),
                    Instr::Copy(Loc::Id(length), Exp::I64(8), info()),
                    Instr::Goto(8),
                    Instr::Copy(Loc::Id(length), Exp::I64(16), info()),
                    Instr::PrimopUnary(Loc::Id(wide), widen, Exp::Id(length), info()),
                    consume,
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(buffer), info()),
                    Instr::End,
                ];
                let results = run_all_with_bindings(
                    instrs,
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                let finished = results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count();
                let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
                eprintln!(
                    "第七轮未覆盖的长度消费者：算子={consumer}，合并={enabled}，完成={finished}，错误={errors:?}"
                );
                assert!(errors.is_empty(), "两个具体整数幂应在合并后仍能执行");
                let mut values: Vec<_> = results
                    .iter()
                    .filter_map(|r| match r {
                        Ok(Run::Finished(Val::I128(v))) => Some(*v),
                        _ => None,
                    })
                    .collect();
                values.sort_unstable();
                assert_eq!(values, vec![256, 65536]);
            }
        }
    }

    #[test]
    fn review7_dynamic_length_missing_consumers() {
        for consumer in ["sail_truncate", "slice"] {
            for enabled in [false, true] {
                let cond = test_name(160);
                let length = test_name(161);
                let wide = test_name(162);
                let buffer = test_name(163);
                let consume = match consumer {
                    "zeros" | "ones" => Instr::PrimopUnary(
                        Loc::Id(buffer),
                        *crate::primop::unary_primops::<B64>().get(consumer).unwrap(),
                        Exp::Id(wide),
                        info(),
                    ),
                    "sail_truncate" => Instr::PrimopBinary(
                        Loc::Id(buffer),
                        *crate::primop::binary_primops::<B64>().get(consumer).unwrap(),
                        Exp::Bits(B64::new(1, 64)),
                        Exp::Id(wide),
                        info(),
                    ),
                    "undefined_vector" | "vector_init" => Instr::PrimopBinary(
                        Loc::Id(buffer),
                        *crate::primop::binary_primops::<B64>().get(consumer).unwrap(),
                        Exp::Id(wide),
                        Exp::Bool(false),
                        info(),
                    ),
                    "slice" => Instr::PrimopVariadic(
                        Loc::Id(buffer),
                        *crate::primop::variadic_primops::<B64>().get(consumer).unwrap(),
                        vec![Exp::Bits(B64::new(1, 64)), Exp::I128(0), Exp::Id(wide)],
                        info(),
                    ),
                    "vector_subrange" | "vector_subrange_low" => Instr::PrimopVariadic(
                        Loc::Id(buffer),
                        *crate::primop::variadic_primops::<B64>().get("vector_subrange").unwrap(),
                        if consumer == "vector_subrange_low" {
                            vec![Exp::Bits(B64::new(0, 64)), Exp::I128(23), Exp::Id(wide)]
                        } else {
                            vec![Exp::Bits(B64::new(0, 64)), Exp::Id(wide), Exp::I128(1)]
                        },
                        info(),
                    ),
                    _ => unreachable!(),
                };
                let widen = *crate::primop::unary_primops::<B64>().get("%i64->%i").unwrap();
                let instrs = vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(length, Ty::I64, info()),
                    Instr::Decl(wide, Ty::I128, info()),
                    Instr::Decl(buffer, Ty::AnyBits, info()),
                    Instr::Jump(Exp::Id(cond), 7, info()),
                    Instr::Copy(Loc::Id(length), Exp::I64(8), info()),
                    Instr::Goto(8),
                    Instr::Copy(Loc::Id(length), Exp::I64(16), info()),
                    Instr::PrimopUnary(Loc::Id(wide), widen, Exp::Id(length), info()),
                    consume,
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(buffer), info()),
                    Instr::End,
                ];
                let results = run_all_with_bindings(
                    instrs,
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                let finished = results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count();
                let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
                eprintln!(
                    "第七轮未覆盖的长度消费者：算子={consumer}，合并={enabled}，完成={finished}，错误={errors:?}"
                );
                assert!(errors.is_empty(), "合法动态长度路径不应在合并后失败");
                let mut widths: Vec<_> = results
                    .iter()
                    .filter_map(|result| match result {
                        Ok(Run::Finished(Val::Bits(bits))) => Some(bits.len()),
                        Ok(Run::Finished(Val::Vector(values))) => Some(values.len() as u32),
                        _ => None,
                    })
                    .collect();
                widths.sort_unstable();
                assert_eq!(widths, vec![8, 16], "必须完成两个不同长度候选");
            }
        }
    }

    #[test]
    fn review6_i64_dynamic_length() {
        for consumer in [
            "zeros",
            "ones",
            "replicate_bits",
            "vector_subrange",
            "vector_subrange_low",
            "zero_extend",
            "sign_extend",
            "sail_truncateLSB",
            "undefined_vector",
            "vector_init",
            "get_slice_int",
        ] {
            for enabled in [false, true] {
                let cond = test_name(160);
                let length = test_name(161);
                let wide = test_name(162);
                let buffer = test_name(163);
                let consume = match consumer {
                    "zeros" | "ones" => Instr::PrimopUnary(
                        Loc::Id(buffer),
                        *crate::primop::unary_primops::<B64>().get(consumer).unwrap(),
                        Exp::Id(wide),
                        info(),
                    ),
                    "replicate_bits" | "zero_extend" | "sign_extend" | "sail_truncateLSB" => Instr::PrimopBinary(
                        Loc::Id(buffer),
                        *crate::primop::binary_primops::<B64>().get(consumer).unwrap(),
                        Exp::Bits(B64::new(1, if consumer == "sail_truncateLSB" { 64 } else { 1 })),
                        Exp::Id(wide),
                        info(),
                    ),
                    "undefined_vector" | "vector_init" => Instr::PrimopBinary(
                        Loc::Id(buffer),
                        *crate::primop::binary_primops::<B64>().get(consumer).unwrap(),
                        Exp::Id(wide),
                        Exp::Bool(false),
                        info(),
                    ),
                    "get_slice_int" => Instr::PrimopVariadic(
                        Loc::Id(buffer),
                        *crate::primop::variadic_primops::<B64>().get(consumer).unwrap(),
                        vec![Exp::Id(wide), Exp::I128(0), Exp::I128(0)],
                        info(),
                    ),
                    "vector_subrange" | "vector_subrange_low" => Instr::PrimopVariadic(
                        Loc::Id(buffer),
                        *crate::primop::variadic_primops::<B64>().get("vector_subrange").unwrap(),
                        if consumer == "vector_subrange_low" {
                            vec![Exp::Bits(B64::new(0, 64)), Exp::I128(23), Exp::Id(wide)]
                        } else {
                            vec![Exp::Bits(B64::new(0, 64)), Exp::Id(wide), Exp::I128(1)]
                        },
                        info(),
                    ),
                    _ => unreachable!(),
                };
                let widen = *crate::primop::unary_primops::<B64>().get("%i64->%i").unwrap();
                let instrs = vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(length, Ty::I64, info()),
                    Instr::Decl(wide, Ty::I128, info()),
                    Instr::Decl(buffer, Ty::AnyBits, info()),
                    Instr::Jump(Exp::Id(cond), 7, info()),
                    Instr::Copy(Loc::Id(length), Exp::I64(8), info()),
                    Instr::Goto(8),
                    Instr::Copy(Loc::Id(length), Exp::I64(16), info()),
                    Instr::PrimopUnary(Loc::Id(wide), widen, Exp::Id(length), info()),
                    consume,
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(buffer), info()),
                    Instr::End,
                ];
                let results = run_all_with_bindings(
                    instrs,
                    ExecutionLimits::default().with_path_merging(enabled),
                    empty_shared_state(),
                    RegisterBindings::new(),
                    HashMap::default(),
                );
                let finished = results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count();
                let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
                eprintln!("第六轮 I64 动态长度：算子={consumer}，合并={enabled}，完成={finished}，错误={errors:?}");
                assert!(errors.is_empty(), "合法动态长度路径不应在合并后失败");
                let mut widths: Vec<_> = results
                    .iter()
                    .filter_map(|result| match result {
                        Ok(Run::Finished(Val::Bits(bits))) => Some(bits.len()),
                        Ok(Run::Finished(Val::Vector(values))) => Some(values.len() as u32),
                        _ => None,
                    })
                    .collect();
                widths.sort_unstable();
                assert_eq!(widths, vec![8, 16], "必须完成两个不同长度候选");
            }
        }
    }

    #[test]
    fn review6_constructor_dynamic_length() {
        for enabled in [false, true] {
            let mut shared = empty_shared_state();
            let a = shared.symtab.intern("za");
            let b = shared.symtab.intern("zb");
            let first = shared.symtab.intern("zfirst");
            let result = shared.symtab.intern("zresult");
            let tag = shared.symtab.intern("ztag");
            let other_tag = shared.symtab.intern("zother");
            let ca = shared.symtab.intern("zca");
            let cb = shared.symtab.intern("zcb");
            let cc = shared.symtab.intern("zcc");
            let buffer = shared.symtab.intern("zbuffer");
            let union = test_name(170);
            shared.type_info.unions.insert(union, vec![(tag, Ty::I128), (other_tag, Ty::I128)]);
            shared.type_info.union_ctors.extend([tag, other_tag]);
            let zeros = *crate::primop::unary_primops::<B64>().get("zeros").unwrap();
            let instrs = vec![
                Instr::Decl(a, Ty::Bool, info()),
                Instr::Decl(b, Ty::Bool, info()),
                Instr::Decl(first, Ty::Union(union), info()),
                Instr::Decl(result, Ty::Union(union), info()),
                Instr::Decl(buffer, Ty::AnyBits, info()),
                Instr::Jump(Exp::Id(a), 8, info()),
                Instr::Copy(Loc::Id(first), Exp::Id(cb), info()),
                Instr::Goto(9),
                Instr::Copy(Loc::Id(first), Exp::Id(ca), info()),
                Instr::Jump(Exp::Id(b), 12, info()),
                Instr::Copy(Loc::Id(result), Exp::Id(cc), info()),
                Instr::Goto(13),
                Instr::Copy(Loc::Id(result), Exp::Id(first), info()),
                Instr::Jump(Exp::Kind(tag, Box::new(Exp::Id(result))), 15, info()),
                Instr::PrimopUnary(Loc::Id(buffer), zeros, Exp::Unwrap(tag, Box::new(Exp::Id(result))), info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                Instr::End,
            ];
            let mut lets = HashMap::default();
            lets.insert(ca, UVal::Init(Val::Ctor(tag, Box::new(Val::I128(8)))));
            lets.insert(cb, UVal::Init(Val::Ctor(other_tag, Box::new(Val::I128(8)))));
            lets.insert(cc, UVal::Init(Val::Ctor(tag, Box::new(Val::I128(16)))));
            let results = run_all_with_bindings(
                instrs,
                ExecutionLimits::default().with_path_merging(enabled),
                shared,
                RegisterBindings::new(),
                lets,
            );
            let finished = results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count();
            let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
            eprintln!("第六轮构造子动态长度：合并={enabled}，完成={finished}，错误={errors:?}");
            assert!(errors.is_empty(), "构造子载荷中的合法动态长度路径不应在合并后失败");
        }
    }

    #[test]
    fn review6_bits_dynamic_length() {
        for enabled in [false, true] {
            let cond = test_name(160);
            let bits = test_name(161);
            let length = test_name(162);
            let buffer = test_name(163);
            let zeros = *crate::primop::unary_primops::<B64>().get("zeros").unwrap();
            let unsigned = *crate::primop::unary_primops::<B64>().get("sail_unsigned").unwrap();
            let instrs = vec![
                Instr::Decl(cond, Ty::Bool, info()),
                Instr::Decl(bits, Ty::Bits(64), info()),
                Instr::Decl(length, Ty::I128, info()),
                Instr::Decl(buffer, Ty::AnyBits, info()),
                Instr::Jump(Exp::Id(cond), 7, info()),
                Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(8, 64)), info()),
                Instr::Goto(8),
                Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(16, 64)), info()),
                Instr::PrimopUnary(Loc::Id(length), unsigned, Exp::Id(bits), info()),
                Instr::PrimopUnary(Loc::Id(buffer), zeros, Exp::Id(length), info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                Instr::End,
            ];
            let results = run_all_with_bindings(
                instrs,
                ExecutionLimits::default().with_path_merging(enabled),
                empty_shared_state(),
                RegisterBindings::new(),
                HashMap::default(),
            );
            let finished = results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count();
            let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
            eprintln!("第六轮位向量动态长度：合并={enabled}，完成={finished}，错误={errors:?}");
            assert!(errors.is_empty(), "由位向量转换的合法动态长度路径不应在合并后失败");
            assert_eq!(finished, 2, "必须完成两个不同长度候选");
        }
    }

    // 第三轮审查反例：只写入临时副本。
    #[test]
    fn review3_lazy_read_must_keep_identity() {
        let shared = empty_shared_state();
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let cond = solver.declare_const(smtlib::Ty::Bool, info());
        let x = test_name(120);
        let y = test_name(121);
        let mut frame = make_frame(vec![
            Instr::Jump(Exp::Bool(true), 3, info()),
            Instr::Copy(Loc::Id(y), Exp::Id(x), info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(y), Exp::Id(x), info()),
            Instr::End,
        ]);
        frame.vars_mut().insert(x, UVal::Uninit(&Ty::I64));
        frame.vars_mut().insert(y, UVal::Uninit(&Ty::I64));
        assert_eq!(try_merge_diamond(cond, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(), Some(4));
        let xv = eval_exp(&Exp::Id(x), &mut frame.local_state, &shared, &mut solver, info()).unwrap().into_owned();
        let yv = eval_exp(&Exp::Id(y), &mut frame.local_state, &shared, &mut solver, info()).unwrap().into_owned();
        let unequal = smtlib::Exp::Neq(
            Box::new(crate::primop_util::smt_value(&xv, info()).unwrap()),
            Box::new(crate::primop_util::smt_value(&yv, info()).unwrap()),
        );
        assert_eq!(
            solver.check_sat_with(&unequal, info()),
            crate::smt::SmtResult::Unsat,
            "两臂均为 y=x，汇合后不能允许 y!=x"
        );
    }

    #[test]
    fn review3_live_out_declared_in_both_arms() {
        for enabled in [false, true] {
            let mut shared = empty_shared_state();
            let cond = shared.symtab.intern("zcond");
            let result = shared.symtab.intern("zresult");
            let instrs = vec![
                Instr::Decl(cond, Ty::Bool, info()),
                Instr::Jump(Exp::Id(cond), 4, info()),
                Instr::Init(result, Ty::I64, Exp::I64(10), info()),
                Instr::Goto(5),
                Instr::Init(result, Ty::I64, Exp::I64(20), info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(result), info()),
                Instr::End,
            ];
            let results = run_all_with_bindings(
                instrs,
                ExecutionLimits::default().with_path_merging(enabled),
                shared,
                RegisterBindings::new(),
                HashMap::default(),
            );
            assert!(
                results.iter().all(|r| matches!(r, Ok(Run::Finished(_)))),
                "汇合点使用的变量不得被丢弃，启用合并={enabled}"
            );
        }
    }

    #[test]
    fn review3_first_enum_use_must_not_panic() {
        let enum_name = test_name(122);
        let shared =
            shared_state_from_defs(vec![crate::ir::Def::Enum(enum_name, vec![test_name(123), test_name(124)])]);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let cond = solver.declare_const(smtlib::Ty::Bool, info());
        let result = test_name(125);
        let mut frame = make_frame(vec![
            Instr::Jump(Exp::Bool(true), 3, info()),
            Instr::Copy(Loc::Id(result), Exp::Undefined(Ty::Enum(enum_name)), info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(result), Exp::Undefined(Ty::Enum(enum_name)), info()),
            Instr::End,
        ]);
        frame.vars_mut().insert(result, UVal::Uninit(Box::leak(Box::new(Ty::Enum(enum_name)))));
        let result = try_merge_diamond(cond, 3, &mut frame, &shared, &mut solver, info(), None, None);
        assert!(result.is_ok(), "不支持的枚举推测应回退");
    }

    #[test]
    fn review3_successful_merge_must_preserve_register_reads() {
        let mut shared = empty_shared_state();
        let reg = shared.symtab.intern("zregister");
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let cond = solver.declare_const(smtlib::Ty::Bool, info());
        let result = test_name(126);
        let mut frame = make_frame(vec![
            Instr::Jump(Exp::Bool(true), 3, info()),
            Instr::Copy(Loc::Id(result), Exp::Id(reg), info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(result), Exp::Id(reg), info()),
            Instr::End,
        ]);
        frame.vars_mut().insert(result, UVal::Uninit(&Ty::I64));
        frame.regs_mut().insert(reg, false, UVal::Init(Val::I64(1)));
        assert_eq!(try_merge_diamond(cond, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(), Some(4));
        assert!(
            solver.trace().to_vec().iter().any(|e| matches!(e, Event::ReadReg(r, _, _) if *r == reg)),
            "两臂必读的寄存器应出现在成功合并后的 Trace 中"
        );
    }

    #[test]
    fn review3_relaxed_register_must_keep_intermediate_writes() {
        let mut shared = empty_shared_state();
        let reg = shared.symtab.intern("zregister");
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let cond = solver.declare_const(smtlib::Ty::Bool, info());
        let mut frame = make_frame(vec![
            Instr::Jump(Exp::Bool(true), 4, info()),
            Instr::Copy(Loc::Id(reg), Exp::I64(1), info()),
            Instr::Copy(Loc::Id(reg), Exp::I64(2), info()),
            Instr::Goto(6),
            Instr::Copy(Loc::Id(reg), Exp::I64(3), info()),
            Instr::Copy(Loc::Id(reg), Exp::I64(4), info()),
            Instr::End,
        ]);
        frame.regs_mut().insert(reg, true, UVal::Init(Val::I64(0)));
        assert_eq!(try_merge_diamond(cond, 4, &mut frame, &shared, &mut solver, info(), None, None).unwrap(), None);
        let mut frame = simulate_diamond_arm(4, 5, 6, frame, &shared, &mut solver, None).unwrap().unwrap();
        frame.regs_mut().forget_last_reads();
        let value = frame.regs_mut().get(reg, &shared, &mut solver, info()).unwrap().unwrap().clone();
        let can_read_intermediate = smtlib::Exp::And(
            Box::new(smtlib::Exp::Var(cond)),
            Box::new(smtlib::Exp::Eq(
                Box::new(crate::primop_util::smt_value(&value, info()).unwrap()),
                Box::new(crate::primop_util::smt_value(&Val::<B64>::I64(3), info()).unwrap()),
            )),
        );
        assert_eq!(
            solver.check_sat_with(&can_read_intermediate, info()),
            crate::smt::SmtResult::Sat,
            "relaxed 寄存器必须允许读取真实执行过的中间写入"
        );
    }

    #[test]
    fn review3_merge_must_respect_depth_limit() {
        for enabled in [false, true] {
            let cond = test_name(127);
            let result = test_name(128);
            let instrs = vec![
                Instr::Decl(cond, Ty::Bool, info()),
                Instr::Decl(result, Ty::I64, info()),
                Instr::Jump(Exp::Id(cond), 5, info()),
                Instr::Copy(Loc::Id(result), Exp::I64(10), info()),
                Instr::Goto(7),
                Instr::Copy(Loc::Id(result), Exp::I64(20), info()),
                Instr::Goto(7),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(result), info()),
                Instr::End,
            ];
            let results = run_all_with_bindings(
                instrs,
                ExecutionLimits::default().with_max_path_depth(1).with_path_merging(enabled),
                empty_shared_state(),
                RegisterBindings::new(),
                HashMap::default(),
            );
            assert!(
                results.iter().all(|r| matches!(r, Err(ExecError::DepthLimitReached))),
                "深度限制不能因合并被跳过，启用合并={enabled}"
            );
        }
    }

    #[test]
    fn path_merging_diamond_reduces_forks() {
        let cond = test_name(100);
        let result = test_name(101);
        let instrs = vec![
            Instr::Decl(cond, Ty::Bool, info()),
            Instr::Decl(result, Ty::Bits(64), info()),
            Instr::Jump(Exp::Id(cond), 5, info()),
            Instr::Copy(Loc::Id(result), Exp::Bits(B64::new(10, 64)), info()),
            Instr::Goto(6),
            Instr::Copy(Loc::Id(result), Exp::Bits(B64::new(20, 64)), info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(result), info()),
            Instr::End,
        ];

        let limits_no_merge = ExecutionLimits::default();
        let results_no_merge = run_all_with_bindings(
            instrs.clone(),
            limits_no_merge,
            empty_shared_state(),
            RegisterBindings::new(),
            HashMap::default(),
        );
        assert_eq!(results_no_merge.len(), 2);

        let limits_merge = ExecutionLimits::default().with_path_merging(true);
        let results_merge = run_all_with_bindings(
            instrs,
            limits_merge,
            empty_shared_state(),
            RegisterBindings::new(),
            HashMap::default(),
        );
        assert_eq!(results_merge.len(), 1);
        assert!(matches!(results_merge[0], Ok(Run::Finished(_))));
    }

    #[test]
    fn path_merging_rejects_branch_local_declaration() {
        let cond = test_name(110);
        let result = test_name(111);
        let temporary = test_name(112);
        let instrs = vec![
            Instr::Decl(cond, Ty::Bool, info()),
            Instr::Decl(result, Ty::I64, info()),
            Instr::Jump(Exp::Id(cond), 5, info()),
            Instr::Copy(Loc::Id(result), Exp::I64(10), info()),
            Instr::Goto(8),
            Instr::Decl(temporary, Ty::I64, info()),
            Instr::Copy(Loc::Id(temporary), Exp::I64(99), info()),
            Instr::Copy(Loc::Id(result), Exp::I64(20), info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(result), info()),
            Instr::End,
        ];
        let results = run_all_with_bindings(
            instrs,
            ExecutionLimits::default().with_path_merging(true),
            empty_shared_state(),
            RegisterBindings::new(),
            HashMap::default(),
        );
        assert_eq!(results.len(), 2);
        assert!(results.iter().all(|result| matches!(result, Ok(Run::Finished(_)))));
    }

    #[test]
    fn path_merging_rejects_cross_arm_jump() {
        let cond = test_name(113);
        let result = test_name(114);
        let instrs = vec![
            Instr::Decl(cond, Ty::Bool, info()),
            Instr::Decl(result, Ty::I64, info()),
            Instr::Jump(Exp::Id(cond), 6, info()),
            Instr::Copy(Loc::Id(result), Exp::I64(10), info()),
            Instr::Goto(6),
            Instr::Goto(8),
            Instr::Copy(Loc::Id(result), Exp::I64(20), info()),
            Instr::Goto(8),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(result), info()),
            Instr::End,
        ];
        let results = run_all_with_bindings(
            instrs,
            ExecutionLimits::default().with_path_merging(true),
            empty_shared_state(),
            RegisterBindings::new(),
            HashMap::default(),
        );
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn diamond_simulation_rejects_memory_and_assertion_primops_before_execution() {
        let shared_state = empty_shared_state();
        let ctx = crate::smt::Context::new(crate::smt::Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let result = test_name(115);
        let read_mem = *crate::primop::variadic_primops::<B64>().get("platform_read_mem").unwrap();
        let programs = [
            vec![Instr::PrimopVariadic(Loc::Id(result), read_mem, Vec::new(), info()), Instr::End],
            vec![Instr::PrimopUnary(Loc::Id(result), crate::primop::assume, Exp::Bool(false), info()), Instr::End],
        ];
        for instrs in &programs {
            let frame = LocalFrame::new(test_name(116), &[], &Ty::Unit, None, instrs);
            let tx = solver.start_transaction();
            assert!(simulate_diamond_arm(0, 0, 1, frame, &shared_state, &mut solver, None).unwrap().is_none());
            assert!(!solver.transaction_invalid());
            solver.rollback_transaction(tx);
        }
    }

    #[test]
    fn path_merging_fallback_when_arm_has_exit() {
        let cond = test_name(102);
        let result = test_name(103);
        let instrs = vec![
            Instr::Decl(cond, Ty::Bool, info()),
            Instr::Decl(result, Ty::I64, info()),
            Instr::Jump(Exp::Id(cond), 5, info()),
            Instr::Copy(Loc::Id(result), Exp::I64(10), info()),
            Instr::Goto(6),
            Instr::Exit(ExitCause::Explicit, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(result), info()),
            Instr::End,
        ];

        let limits_merge = ExecutionLimits::default().with_path_merging(true);
        let results_merge = run_all_with_bindings(
            instrs,
            limits_merge,
            empty_shared_state(),
            RegisterBindings::new(),
            HashMap::default(),
        );
        assert_eq!(results_merge.len(), 2);
    }

    #[test]
    fn review4_single_arm_live_out() {
        for enabled in [false, true] {
            let mut shared = empty_shared_state();
            let cond = shared.symtab.intern("zcond");
            let x = shared.symtab.intern("zx");
            let instrs = vec![
                Instr::Decl(cond, Ty::Bool, info()),
                Instr::Jump(Exp::Id(cond), 3, info()),
                Instr::Goto(4),
                Instr::Init(x, Ty::I64, Exp::I64(42), info()),
                Instr::Jump(Exp::Id(cond), 7, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::I64(0), info()),
                Instr::End,
                Instr::Copy(Loc::Id(RETURN), Exp::Id(x), info()),
                Instr::End,
            ];
            let results = run_all_with_bindings(
                instrs,
                ExecutionLimits::default().with_path_merging(enabled),
                shared,
                RegisterBindings::new(),
                HashMap::default(),
            );
            let finished = results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count();
            let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
            eprintln!("单臂活跃变量：合并={enabled}，完成={finished}，错误={errors:?}");
            assert_eq!(finished, 2, "可达路径不得丢失");
        }
    }

    #[test]
    fn review4_unequal_depth() {
        for enabled in [false, true] {
            let cond = test_name(130);
            let instrs = vec![
                Instr::Decl(cond, Ty::Bool, info()),
                Instr::Jump(Exp::Id(cond), 4, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::I64(10), info()),
                Instr::Goto(5),
                Instr::Copy(Loc::Id(RETURN), Exp::I64(20), info()),
                Instr::Goto(6),
                Instr::End,
            ];
            let results = run_all_with_bindings(
                instrs,
                ExecutionLimits::default().with_max_path_depth(2).with_path_merging(enabled),
                empty_shared_state(),
                RegisterBindings::new(),
                HashMap::default(),
            );
            let finished = results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count();
            let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
            eprintln!("不等深度：合并={enabled}，完成={finished}，错误={errors:?}");
            assert_eq!(finished, 1, "较短路径应在深度预算内正常完成");
        }
    }

    #[test]
    fn review4_different_bit_widths() {
        for enabled in [false, true] {
            let cond = test_name(130);
            let result = test_name(131);
            let instrs = vec![
                Instr::Decl(cond, Ty::Bool, info()),
                Instr::Decl(result, Ty::AnyBits, info()),
                Instr::Jump(Exp::Id(cond), 5, info()),
                Instr::Copy(Loc::Id(result), Exp::Bits(B64::new(1, 8)), info()),
                Instr::Goto(6),
                Instr::Copy(Loc::Id(result), Exp::Bits(B64::new(2, 16)), info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                Instr::End,
            ];
            let results = run_all_with_bindings(
                instrs,
                ExecutionLimits::default().with_path_merging(enabled),
                empty_shared_state(),
                RegisterBindings::new(),
                HashMap::default(),
            );
            eprintln!("不同位宽：合并={enabled}，路径数={}", results.len());
            assert!(results.iter().all(|r| matches!(r, Ok(Run::Finished(_)))));
        }
    }

    #[test]
    fn review4_field_read_accessor() {
        let mut shared = empty_shared_state();
        let reg = shared.symtab.intern("zreg");
        let field = shared.symtab.intern("zfield");
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let cond = solver.declare_const(smtlib::Ty::Bool, info());
        let read = Exp::Field(Box::new(Exp::Id(reg)), field);
        let mut frame = make_frame(vec![
            Instr::Jump(Exp::Bool(true), 3, info()),
            Instr::Copy(Loc::Id(RETURN), read.clone(), info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(RETURN), read, info()),
            Instr::End,
        ]);
        let mut fields = HashMap::default();
        fields.insert(field, Val::I64(1));
        frame.regs_mut().insert(reg, false, UVal::Init(Val::Struct(fields)));
        assert_eq!(try_merge_diamond(cond, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(), Some(4));
        let trace = solver.trace().to_vec();
        let accessors: Vec<_> = trace
            .iter()
            .filter_map(|e| match e {
                Event::ReadReg(r, acc, _) if *r == reg => Some(acc.clone()),
                _ => None,
            })
            .collect();
        eprintln!("合并后的读取访问路径：{accessors:?}");
        assert_eq!(accessors, vec![vec![Accessor::Field(field)]], "读取字段不得扩大为整个寄存器");
    }

    #[test]
    fn review4_lazy_register_read_taint() {
        let mut shared = empty_shared_state();
        let reg = shared.symtab.intern("zreg");
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let cond = solver.declare_const(smtlib::Ty::Bool, info());
        let mut frame = make_frame(vec![
            Instr::Jump(Exp::Bool(true), 3, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
            Instr::End,
        ]);
        frame.regs_mut().insert(reg, false, UVal::Uninit(&Ty::I64));
        assert_eq!(try_merge_diamond(cond, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(), Some(4));
        let result =
            eval_exp(&Exp::Id(RETURN), &mut frame.local_state, &shared, &mut solver, info()).unwrap().into_owned();
        let trace = solver.trace().to_vec();
        let refs = crate::simplify::EventReferences::from_events(&trace);
        let taints = refs.value_taints(&result, &trace);
        eprintln!("寄存器直接复制结果的寄存器依赖：{:?}", taints.registers);
        assert!(taints.registers.contains(&(reg, vec![])), "返回值直接来自寄存器，依赖不得丢失");
    }

    #[test]
    fn review4_lazy_register_identity_and_asymmetry() {
        for symmetric in [true, false] {
            let mut shared = empty_shared_state();
            let reg = shared.symtab.intern("zreg");
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let cond = solver.declare_const(smtlib::Ty::Bool, info());
            let mut frame = make_frame(vec![
                Instr::Jump(Exp::Bool(true), 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
                Instr::Goto(4),
                Instr::Copy(Loc::Id(RETURN), if symmetric { Exp::Id(reg) } else { Exp::I64(0) }, info()),
                Instr::End,
            ]);
            frame.regs_mut().insert(reg, false, UVal::Uninit(&Ty::I64));
            let merged = try_merge_diamond(cond, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap();
            if symmetric {
                assert_eq!(merged, Some(4));
                let value = eval_exp(&Exp::Id(RETURN), &mut frame.local_state, &shared, &mut solver, info())
                    .unwrap()
                    .into_owned();
                let rv = frame.regs().get_last_if_initialized(reg).unwrap();
                let unequal = smtlib::Exp::Neq(
                    Box::new(crate::primop_util::smt_value(&value, info()).unwrap()),
                    Box::new(crate::primop_util::smt_value(rv, info()).unwrap()),
                );
                assert_eq!(solver.check_sat_with(&unequal, info()), crate::smt::SmtResult::Unsat);
            } else {
                assert_eq!(merged, None);
                assert!(frame.regs().get_last_if_initialized(reg).is_none());
            }
        }
    }

    #[test]
    fn review4_enum_rollback_replay() {
        let enum_name = test_name(122);
        let shared =
            shared_state_from_defs(vec![crate::ir::Def::Enum(enum_name, vec![test_name(123), test_name(124)])]);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let tx = solver.start_transaction();
        solver.assert(smtlib::Exp::Bool(false));
        crate::primop_util::symbolic(&Ty::Enum(enum_name), &shared, &mut solver, info()).unwrap();
        solver.rollback_transaction(tx);
        let cp = checkpoint(&mut solver);
        let mut replay = Solver::<B64>::from_checkpoint(&ctx, cp);
        crate::primop_util::symbolic(&Ty::Enum(enum_name), &shared, &mut replay, info()).unwrap();
        assert_eq!(replay.check_sat(info()), crate::smt::SmtResult::Sat);
    }

    #[test]
    fn review5_dynamic_length() {
        for enabled in [false, true] {
            let cond = test_name(140);
            let length = test_name(141);
            let zeros = *crate::primop::unary_primops::<B64>().get("zeros").unwrap();
            let instrs = vec![
                Instr::Decl(cond, Ty::Bool, info()),
                Instr::Decl(length, Ty::I128, info()),
                Instr::Jump(Exp::Id(cond), 5, info()),
                Instr::Copy(Loc::Id(length), Exp::I128(8), info()),
                Instr::Goto(6),
                Instr::Copy(Loc::Id(length), Exp::I128(16), info()),
                Instr::PrimopUnary(Loc::Id(RETURN), zeros, Exp::Id(length), info()),
                Instr::End,
            ];
            let results = run_all_with_bindings(
                instrs,
                ExecutionLimits::default().with_path_merging(enabled),
                empty_shared_state(),
                RegisterBindings::new(),
                HashMap::default(),
            );
            let finished = results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count();
            let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
            eprintln!("动态位宽：合并={enabled}，完成={finished}，错误={errors:?}");
            assert_eq!(finished, 2, "两个合法的动态位宽路径都应完成");
            assert!(errors.is_empty(), "动态位宽路径不应报错");
        }
    }

    #[test]
    fn review5_loop_history() {
        for enabled in [false, true] {
            let cond = test_name(140);
            let rounds = test_name(141);
            let add = *crate::primop::binary_primops::<B64>().get("add_int").unwrap();
            let instrs = vec![
                Instr::Init(rounds, Ty::I128, Exp::I128(0), info()),
                Instr::Decl(cond, Ty::Bool, info()),
                Instr::Jump(Exp::Id(cond), 7, info()),
                Instr::Goto(5),
                Instr::Goto(11),
                Instr::Goto(4),
                Instr::Goto(11),
                Instr::Goto(9),
                Instr::Goto(11),
                Instr::Goto(8),
                Instr::Goto(11),
                Instr::PrimopBinary(Loc::Id(rounds), add, Exp::Id(rounds), Exp::I128(1), info()),
                Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(rounds), Exp::I128(2)]), 14, info()),
                Instr::Goto(2),
                Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
                Instr::End,
            ];
            let limits = ExecutionLimits::default().with_path_merging(enabled).with_max_backjumps_per_loop(1);
            let results = run_all_with_bindings(
                instrs,
                limits,
                empty_shared_state(),
                RegisterBindings::new(),
                HashMap::default(),
            );
            let finished = results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count();
            let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err().map(ToString::to_string)).collect();
            eprintln!("循环预算：合并={enabled}，完成={finished}，错误={errors:?}");
            assert_eq!(finished, 0, "两条路径第二次执行同一实际回跳时均应耗尽预算");
        }
    }

    #[test]
    fn review5_unsigned_128_continuation() {
        use crate::bitvector::b129::B129;
        let defs: &[crate::ir::Def<Name, B129>] = &[];
        let shared = SharedState::new(
            Symtab::new(),
            defs,
            IRTypeInfo::new(defs),
            HashSet::new(),
            HashSet::new(),
            HashSet::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B129>::new(&ctx);
        let condition = solver.declare_const(smtlib::Ty::Bool, info());
        let result = test_name(142);
        let bits = |n| Exp::Call(Op::Concat, vec![Exp::Bits(B64::new(0, 64)), Exp::Bits(B64::new(n, 64))]);
        let instrs: Vec<Instr<Name, B129>> = vec![
            Instr::Jump(Exp::Bool(true), 3, info()),
            Instr::Copy(Loc::Id(result), bits(1), info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(result), bits(2), info()),
            Instr::End,
        ];
        let mut frame = LocalFrame::new(test_name(143), &[], &Ty::I128, None, &instrs);
        frame.vars_mut().insert(result, UVal::Uninit(&Ty::Bits(128)));
        let unsigned = *crate::primop::unary_primops::<B129>().get("sail_unsigned").unwrap();
        for n in [1, 2] {
            assert_eq!(unsigned(Val::Bits(B129::new(n, 128)), &mut solver, info()).unwrap(), Val::I128(n as i128));
        }
        assert_eq!(
            try_merge_diamond(condition, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(),
            Some(4)
        );
        let merged =
            eval_exp(&Exp::Id(result), &mut frame.local_state, &shared, &mut solver, info()).unwrap().into_owned();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsigned(merged, &mut solver, info())));
        assert!(result.is_ok(), "两个合法的 128 位常量经合并后不能使 unsigned 转换 panic");
    }

    #[test]
    fn review5_constructor_condition_truth_table() {
        use crate::smt::smtlib::Exp as SExp;
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let c = solver.declare_const(smtlib::Ty::Bool, info());
        let a = solver.declare_const(smtlib::Ty::Bool, info());
        let b = solver.declare_const(smtlib::Ty::Bool, info());
        let tag_a = test_name(150);
        let tag_b = test_name(151);
        // 通用 ITE 的构造子判别值和载荷仍须满足真值表；路径合并拒绝不同标签。
        let ca = Val::Ctor(tag_a, Box::new(Val::Bits(B64::new(11, 64))));
        let cb = Val::Ctor(tag_b, Box::new(Val::Bits(B64::new(22, 64))));
        let sa = crate::primop_util::build_ite(
            a,
            &ca,
            &Val::Ctor(tag_b, Box::new(Val::Bits(B64::new(12, 64)))),
            &mut solver,
            info(),
        )
        .unwrap();
        let sb = crate::primop_util::build_ite(
            b,
            &Val::Ctor(tag_a, Box::new(Val::Bits(B64::new(21, 64)))),
            &cb,
            &mut solver,
            info(),
        )
        .unwrap();
        for (lhs, rhs) in [(&ca, &cb), (&ca, &sb), (&sa, &cb), (&sa, &sb)] {
            assert!(matches!(
                crate::primop_util::merge_val(c, lhs, rhs, &mut solver, info()),
                Err(ExecError::IncompatibleMerge)
            ));
            let merged = crate::primop_util::build_ite(c, lhs, rhs, &mut solver, info()).unwrap();
            let Val::SymbolicCtor(discriminant, possibilities) = merged else { panic!("期望符号构造子") };
            for cv in [false, true] {
                for av in [false, true] {
                    for bv in [false, true] {
                        let (tag, payload) = match if cv { lhs } else { rhs } {
                            Val::Ctor(tag, value) => (*tag, value.as_ref().clone()),
                            Val::SymbolicCtor(sym, values) => {
                                let flag = if matches!(lhs, Val::SymbolicCtor(l, _) if l == sym) { av } else { bv };
                                let tag = if flag { tag_a } else { tag_b };
                                (tag, values[&tag].clone())
                            }
                            _ => unreachable!(),
                        };
                        let mut assertion = SExp::Bool(true);
                        for (sym, value) in [(c, cv), (a, av), (b, bv)] {
                            assertion = SExp::And(
                                Box::new(assertion),
                                Box::new(SExp::Eq(Box::new(SExp::Var(sym)), Box::new(SExp::Bool(value)))),
                            );
                        }
                        let wrong_tag = SExp::Neq(Box::new(SExp::Var(discriminant)), Box::new(tag.to_smt()));
                        let wrong_payload = SExp::Neq(
                            Box::new(crate::primop_util::smt_value(&possibilities[&tag], info()).unwrap()),
                            Box::new(crate::primop_util::smt_value(&payload, info()).unwrap()),
                        );
                        let bad = SExp::And(
                            Box::new(assertion),
                            Box::new(SExp::Or(Box::new(wrong_tag), Box::new(wrong_payload))),
                        );
                        assert_eq!(
                            solver.check_sat_with(&bad, info()),
                            crate::smt::SmtResult::Unsat,
                            "构造子判别值和载荷必须服从对应条件"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn review5_nary_register_history() {
        let mut shared = empty_shared_state();
        let reg = shared.symtab.intern("zreg");
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut regs = RegisterBindings::new();
        regs.insert(reg, true, UVal::Init(Val::I64(0)));
        regs.assign(reg, Val::I64(1), &shared);
        let merged = crate::primop_util::merge_register_bindings_nary(&[], &[&regs], &mut solver, info()).unwrap();
        eprintln!("通用寄存器合并：relaxed={}，保留历史={}", merged.is_relaxed(reg), merged.has_old_writes(reg));
        assert!(merged.is_relaxed(reg) && merged.has_old_writes(reg), "即便只有一个输入也不能清除 relaxed 语义和历史");
        assert_eq!(merged.get_last_if_initialized(reg), Some(&Val::I64(1)));

        let condition = solver.declare_const(smtlib::Ty::Bool, info());
        let mut relaxed_only = RegisterBindings::new();
        relaxed_only.insert(reg, true, UVal::Init(Val::I64(1)));
        for relaxed_regs in [&regs, &relaxed_only] {
            let mut plain_regs = RegisterBindings::new();
            plain_regs.insert(reg, false, UVal::Init(Val::I64(1)));
            for inputs in [[relaxed_regs, &plain_regs], [&plain_regs, relaxed_regs]] {
                assert!(matches!(
                    crate::primop_util::merge_register_bindings_nary(&[condition], &inputs, &mut solver, info()),
                    Err(ExecError::IncompatibleMerge)
                ));
            }
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
