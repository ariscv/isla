// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
// Copyright (c) 2020 Brian Campbell
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

//! This module is a big set of primitive operations and builtins
//! which are implemented over the [crate::ir::Val] type. Most are not
//! exported directly but instead are exposed via the [Primops] struct
//! which contains all the primops (and is created using it's Default
//! instance). During initialization (via the [crate::init] module)
//! textual references to primops in the IR are replaced with direct
//! function pointers to their implementation in this module. The
//! [Unary], [Binary], and [Variadic] types are function pointers to
//! unary, binary, and other primops, which are contained within
//! [Primops].

#![allow(clippy::comparison_chain)]
#![allow(clippy::cognitive_complexity)]

use std::cmp::min;
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::ops::{Not, Shl, Shr};
use std::str::FromStr;

use crate::bitvector::b64::B64;
use crate::bitvector::BV;
use crate::error::ExecError;
use crate::executor::LocalFrame;
use crate::ir::{BitsSegment, Reset, UVal, Val, ELF_ENTRY};
use crate::primop_util::*;
use crate::smt::smtlib::*;
use crate::smt::*;
use crate::source_loc::SourceLoc;

pub mod float;
pub mod memory;

pub type Unary<B> = fn(Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError>;
pub type Binary<B> = fn(Val<B>, Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError>;
pub type Variadic<B> =
    fn(Vec<Val<B>>, solver: &mut Solver<B>, frame: &mut LocalFrame<B>, info: SourceLoc) -> Result<Val<B>, ExecError>;

#[allow(clippy::needless_range_loop)]
fn smt_mask_lower<V>(len: usize, mask_width: usize) -> Exp<V> {
    if len <= 64 {
        Exp::Bits64(B64::new(u64::MAX >> (64 - mask_width), len as u32))
    } else {
        let mut bitvec = vec![false; len];
        for i in 0..mask_width {
            bitvec[i] = true
        }
        Exp::Bits(bitvec)
    }
}

pub fn smt_zeros<V>(i: i128) -> Exp<V> {
    if i <= 64 {
        Exp::Bits64(B64::zeros(i as u32))
    } else {
        Exp::Bits(vec![false; i as usize])
    }
}

/* pub fn smt_zeros_sym<V>(i: Sym) -> Exp<V> {
    Exp::Bits(vec![false; i as usize])
} */

pub fn smt_ones<V>(i: i128) -> Exp<V> {
    if i <= 64 {
        Exp::Bits64(B64::ones(i as u32))
    } else {
        Exp::Bits(vec![true; i as usize])
    }
}

fn smt_u64_width<V>(value: u64, width: u32) -> Exp<V> {
    if width <= 64 {
        bits64(value, width)
    } else {
        Exp::ZeroExtend(width - 64, Box::new(bits64(value, 64)))
    }
}

// 用当前路径约束尝试把布尔表达式具体化为 true/false。
//
// 这里处理的是“条件”本身，而不是证明某个符号值等于唯一常数：
// one-of 约束下的 `num_elem <= vlen` 可能可证明为 true，
// 但 `num_elem == 2` 仍会保留为 symbolic，避免错误具体化。
//
// 返回值：
// - `Val::Bool(true)`：当前约束能证明 exp 恒真。
// - `Val::Bool(false)`：当前约束能证明 exp 恒假。
// - `Val::Symbolic(_)`：exp 仍可能真也可能假，或 solver 无法证明，保留为符号布尔值。
//
// 例：若已有 assert(num_elem == 1 | num_elem == 2 | num_elem == 4)，
// `0 < num_elem` 会返回 true，而 `num_elem == 2` 仍返回 symbolic。
fn try_concretize_bool_exp<B: BV>(exp: Exp<Sym>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match solver.check_sat_with(&Exp::Not(Box::new(exp.clone())), info) {
        SmtResult::Unsat => return Ok(Val::Bool(true)),
        SmtResult::Sat => (),
        SmtResult::Unknown => return solver.define_const(exp, info).into(),
        SmtResult::Error(error) => return Err(ExecError::Smt(error)),
    }

    match solver.check_sat_with(&exp, info) {
        SmtResult::Unsat => Ok(Val::Bool(false)),
        SmtResult::Sat | SmtResult::Unknown => solver.define_const(exp, info).into(),
        SmtResult::Error(error) => Err(ExecError::Smt(error)),
    }
}

fn concretize_proven_i128<B: BV>(value: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match value {
        Val::Symbolic(sym) => match proven_symbolic_i128(sym, solver, info) {
            Ok(Some(value)) => Ok(Val::I128(value)),
            Ok(None) => Ok(Val::Symbolic(sym)),
            Err(error) => Err(error),
        },
        value => Ok(value),
    }
}

fn panic_negative_nat_invariant(op: &str, value: i128) -> ! {
    panic!(
        "nat invariant violated in {}: current path proves a nat-like value equals {}. \
请与用户讨论：1) 上游是否漏加了 `>= 0` 约束；2) 该 primop 是否被错误地用于 signed int；\
3) proven_symbolic_i128 是否不该在这里具体化。",
        op, value
    )
}

// 这个 helper 故意只做一件事：
// nat-like 参数在 concretize_proven_i128 之后如果已经落成负数常量，就立刻 fail-stop。
// 还保持 symbolic 的情况继续走原调用点自己的 SymbolicLength / symbolic 分支。
fn panic_if_negative_concretized_nat<B: BV>(op: &str, value: &Val<B>) {
    match value {
        Val::I64(value) if *value < 0 => panic_negative_nat_invariant(op, i128::from(*value)),
        Val::I128(value) if *value < 0 => panic_negative_nat_invariant(op, *value),
        _ => (),
    }
}

macro_rules! unary_primop_copy {
    ($f:ident, $name:expr, $unwrap:path, $wrap:path, $concrete_op:path, $smt_op:path) => {
        pub fn $f<B: BV>(x: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
            match replace_mixed_bits(x, solver, info)? {
                Val::Symbolic(x) => solver.define_const($smt_op(Box::new(Exp::Var(x))), info).into(),
                $unwrap(x) => Ok($wrap($concrete_op(x))),
                _ => Err(ExecError::Type($name, info)),
            }
        }
    };
}

macro_rules! binary_primop_copy {
    ($f:ident, $name:expr, $unwrap:path, $wrap:path, $concrete_op:path, $smt_op:path, $to_symbolic:path) => {
        pub fn $f<B: BV>(x: Val<B>, y: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
            match (replace_mixed_bits(x, solver, info)?, replace_mixed_bits(y, solver, info)?) {
                (Val::Symbolic(x), Val::Symbolic(y)) => {
                    solver.define_const($smt_op(Box::new(Exp::Var(x)), Box::new(Exp::Var(y))), info).into()
                }
                (Val::Symbolic(x), $unwrap(y)) => {
                    solver.define_const($smt_op(Box::new(Exp::Var(x)), Box::new($to_symbolic(y))), info).into()
                }
                ($unwrap(x), Val::Symbolic(y)) => {
                    solver.define_const($smt_op(Box::new($to_symbolic(x)), Box::new(Exp::Var(y))), info).into()
                }
                ($unwrap(x), $unwrap(y)) => Ok($wrap($concrete_op(x, y))),
                (_, _) => Err(ExecError::Type($name, info)),
            }
        }
    };
}

macro_rules! binary_primop {
    ($f:ident, $name:expr, $unwrap:path, $wrap:path, $concrete_op:path, $smt_op:path, $to_symbolic:path) => {
        pub fn $f<B: BV>(x: Val<B>, y: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
            match (replace_mixed_bits(x, solver, info)?, replace_mixed_bits(y, solver, info)?) {
                (Val::Symbolic(x), Val::Symbolic(y)) => {
                    try_concretize_bool_exp($smt_op(Box::new(Exp::Var(x)), Box::new(Exp::Var(y))), solver, info)
                }
                (Val::Symbolic(x), $unwrap(y)) => {
                    try_concretize_bool_exp($smt_op(Box::new(Exp::Var(x)), Box::new($to_symbolic(y))), solver, info)
                }
                ($unwrap(x), Val::Symbolic(y)) => {
                    try_concretize_bool_exp($smt_op(Box::new($to_symbolic(x)), Box::new(Exp::Var(y))), solver, info)
                }
                ($unwrap(x), $unwrap(y)) => Ok($wrap($concrete_op(&x, &y))),
                (_, _) => Err(ExecError::Type($name, info)),
            }
        }
    };
}

pub(crate) fn assume<B: BV>(x: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match x {
        Val::Symbolic(v) => {
            solver.add(Def::Assert(Exp::Var(v)));
            Ok(Val::Unit)
        }
        Val::Bool(b) => {
            if b {
                Ok(Val::Unit)
            } else {
                solver.add(Def::Assert(Exp::Bool(false)));
                Ok(Val::Unit)
            }
        }
        _ => Err(ExecError::Type(format!("assert {:?}", &x), info)),
    }
}

// If the assertion can succeed, it will
fn optimistic_assert<B: BV>(
    x: Val<B>,
    message: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let message = match message {
        Val::String(message) => Some(message),
        _ => None,
    };
    match x {
        Val::Symbolic(v) => {
            let test_true = Box::new(Exp::Var(v));
            let can_be_true = solver.check_sat_with(&test_true, info).is_sat()?;
            if can_be_true {
                solver.add(Def::Assert(Exp::Var(v)));
                Ok(Val::Unit)
            } else {
                Err(ExecError::AssertionFailure(message, info))
            }
        }
        Val::Bool(b) => {
            if b {
                Ok(Val::Unit)
            } else {
                Err(ExecError::AssertionFailure(message, info))
            }
        }
        _ => Err(ExecError::Type(format!("optimistic_assert {:?}", &x), info)),
    }
}

// If the assertion can fail, it will
fn pessimistic_assert<B: BV>(
    x: Val<B>,
    message: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let message = match message {
        Val::String(message) => Some(message),
        _ => None,
    };
    match x {
        Val::Symbolic(v) => {
            let test_false = Exp::Not(Box::new(Exp::Var(v)));
            let can_be_false = solver.check_sat_with(&test_false, info).is_sat()?;
            if can_be_false {
                Err(ExecError::AssertionFailure(message, info))
            } else {
                Ok(Val::Unit)
            }
        }
        Val::Bool(b) => {
            if b {
                Ok(Val::Unit)
            } else {
                Err(ExecError::AssertionFailure(message, info))
            }
        }
        _ => Err(ExecError::Type(format!("pessimistic_assert {:?}", &x), info)),
    }
}

// Conversion functions

fn i64_to_i128<B: BV>(x: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match x {
        Val::I64(x) => Ok(Val::I128(i128::from(x))),
        Val::Bits(x) if x.len() == 64 => Ok(Val::I128(x.signed())),
        Val::Symbolic(x) => solver.define_const(Exp::SignExtend(64, Box::new(Exp::Var(x))), info).into(),
        _ => Err(ExecError::Type(format!("%i64->%i {:?}", &x), info)),
    }
}

fn i128_to_i64<B: BV>(x: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match x {
        Val::I128(x) => match i64::try_from(x) {
            Ok(y) => Ok(Val::I64(y)),
            Err(_) => Err(ExecError::Overflow),
        },
        Val::Symbolic(x) => solver.define_const(Exp::Extract(63, 0, Box::new(Exp::Var(x))), info).into(),
        _ => Err(ExecError::Type(format!("%i->%i64 {:?}", &x), info)),
    }
}

// FIXME: The Sail->C compilation uses xs == NULL to check if a list
// is empty, so we replicate that here for now, but we should
// introduce a separate @is_empty operator instead.
pub(crate) fn op_eq<B: BV>(x: Val<B>, y: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (x, y) {
        (Val::List(xs), Val::List(ys)) => {
            if xs.len() != ys.len() {
                Ok(Val::Bool(false))
            } else if xs.is_empty() && ys.is_empty() {
                Ok(Val::Bool(true))
            } else {
                Err(ExecError::Type(format!("op_eq {:?} {:?}", &xs, &ys), info))
            }
        }
        (x, y) => eq_anything(x, y, solver, info),
    }
}

pub(crate) fn op_neq<B: BV>(
    x: Val<B>,
    y: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match (x, y) {
        (Val::List(xs), Val::List(ys)) => {
            if xs.len() != ys.len() {
                Ok(Val::Bool(true))
            } else if xs.is_empty() && ys.is_empty() {
                Ok(Val::Bool(false))
            } else {
                Err(ExecError::Type(format!("op_neq {:?} {:?}", &xs, &ys), info))
            }
        }
        (x, y) => neq_anything(x, y, solver, info),
    }
}

pub(crate) fn op_head<B: BV>(xs: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match xs {
        Val::List(mut xs) => match xs.pop() {
            Some(x) => Ok(x),
            None => Err(ExecError::Type(format!("op_head (list empty) {:?}", &xs), info)),
        },
        _ => Err(ExecError::Type(format!("op_head {:?}", &xs), info)),
    }
}

pub(crate) fn op_tail<B: BV>(xs: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match xs {
        Val::List(mut xs) => {
            xs.pop();
            Ok(Val::List(xs))
        }
        _ => Err(ExecError::Type(format!("op_tail {:?}", &xs), info)),
    }
}

pub(crate) fn op_is_empty<B: BV>(xs: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match xs {
        Val::List(xs) => Ok(Val::Bool(xs.is_empty())),
        _ => Err(ExecError::Type(format!("op_tail {:?}", &xs), info)),
    }
}

binary_primop!(op_lt, "op_lt".to_string(), Val::I64, Val::Bool, i64::lt, Exp::Bvslt, smt_i64);
binary_primop!(op_gt, "op_gt".to_string(), Val::I64, Val::Bool, i64::gt, Exp::Bvsgt, smt_i64);
binary_primop!(op_lteq, "op_lteq".to_string(), Val::I64, Val::Bool, i64::le, Exp::Bvsle, smt_i64);
binary_primop!(op_gteq, "op_gteq".to_string(), Val::I64, Val::Bool, i64::ge, Exp::Bvsge, smt_i64);
binary_primop_copy!(op_add, "op_add".to_string(), Val::I64, Val::I64, i64::wrapping_add, Exp::Bvadd, smt_i64);
binary_primop_copy!(op_sub, "op_sub".to_string(), Val::I64, Val::I64, i64::wrapping_sub, Exp::Bvsub, smt_i64);

pub(crate) fn bit_to_bool<B: BV>(bit: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match bit {
        Val::Bits(bit) => Ok(Val::Bool(bit == B::BIT_ONE)),
        Val::Symbolic(bit) => {
            solver.define_const(Exp::Eq(Box::new(Exp::Bits([true].to_vec())), Box::new(Exp::Var(bit))), info).into()
        }
        _ => Err(ExecError::Type(format!("bit_to_bool {:?}", &bit), info)),
    }
}

pub(crate) fn bool_to_bit<B: BV>(value: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match value {
        Val::Bool(true) => Ok(Val::Bits(B::BIT_ONE)),
        Val::Bool(false) => Ok(Val::Bits(B::BIT_ZERO)),
        Val::Symbolic(value) => solver
            .define_const(
                Exp::Ite(
                    Box::new(Exp::Var(value)),
                    Box::new(Exp::Bits64(B64::BIT_ONE)),
                    Box::new(Exp::Bits64(B64::BIT_ZERO)),
                ),
                info,
            )
            .into(),
        _ => Err(ExecError::Type(format!("bool_to_bit {:?}", &value), info)),
    }
}

pub(crate) fn op_unsigned<B: BV>(bits: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let bits = replace_mixed_bits(bits, solver, info)?;
    match bits {
        Val::Bits(bits) => Ok(Val::I64(bits.unsigned() as i64)),
        Val::Symbolic(bits) => match solver.length(bits) {
            Some(length) => solver.define_const(Exp::ZeroExtend(64 - length, Box::new(Exp::Var(bits))), info).into(),
            None => Err(ExecError::Type(format!("op_unsigned {:?}", &bits), info)),
        },
        _ => Err(ExecError::Type(format!("op_unsigned {:?}", &bits), info)),
    }
}

pub(crate) fn op_signed<B: BV>(bits: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let bits = replace_mixed_bits(bits, solver, info)?;
    match bits {
        Val::Bits(bits) => Ok(Val::I64(bits.signed() as i64)),
        Val::Symbolic(bits) => match solver.length(bits) {
            Some(length) => solver.define_const(Exp::SignExtend(64 - length, Box::new(Exp::Var(bits))), info).into(),
            None => Err(ExecError::Type(format!("op_unsigned (solver cannot determine length) {:?}", &bits), info)),
        },
        _ => Err(ExecError::Type(format!("op_unsigned {:?}", &bits), info)),
    }
}

// Basic comparisons

unary_primop_copy!(not_bool, "not".to_string(), Val::Bool, Val::Bool, bool::not, Exp::Not);
binary_primop!(eq_int, "eq_int".to_string(), Val::I128, Val::Bool, i128::eq, Exp::Eq, smt_i128);
binary_primop!(eq_bool, "eq_bool".to_string(), Val::Bool, Val::Bool, bool::eq, Exp::Eq, Exp::Bool);
binary_primop!(lteq_int, "lteq".to_string(), Val::I128, Val::Bool, i128::le, Exp::Bvsle, smt_i128);
binary_primop!(gteq_int, "gteq".to_string(), Val::I128, Val::Bool, i128::ge, Exp::Bvsge, smt_i128);
binary_primop!(lt_int, "lt".to_string(), Val::I128, Val::Bool, i128::lt, Exp::Bvslt, smt_i128);
binary_primop!(gt_int, "gt".to_string(), Val::I128, Val::Bool, i128::gt, Exp::Bvsgt, smt_i128);

pub fn and_bool<B: BV>(lhs: Val<B>, rhs: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (lhs, rhs) {
        (Val::Bool(false), _) => Ok(Val::Bool(false)),
        (_, Val::Bool(false)) => Ok(Val::Bool(false)),
        (Val::Bool(true), rhs) => Ok(rhs),
        (lhs, Val::Bool(true)) => Ok(lhs),
        (Val::Symbolic(x), Val::Symbolic(y)) => {
            solver.define_const(Exp::And(Box::new(Exp::Var(x)), Box::new(Exp::Var(y))), info).into()
        }
        (lhs, rhs) => Err(ExecError::Type(format!("and_bool {:?} {:?}", lhs, rhs), info)),
    }
}

pub fn or_bool<B: BV>(lhs: Val<B>, rhs: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (lhs, rhs) {
        (Val::Bool(true), _) => Ok(Val::Bool(true)),
        (_, Val::Bool(true)) => Ok(Val::Bool(true)),
        (Val::Bool(false), rhs) => Ok(rhs),
        (lhs, Val::Bool(false)) => Ok(lhs),
        (Val::Symbolic(x), Val::Symbolic(y)) => {
            solver.define_const(Exp::Or(Box::new(Exp::Var(x)), Box::new(Exp::Var(y))), info).into()
        }
        (lhs, rhs) => Err(ExecError::Type(format!("or_bool {:?} {:?}", lhs, rhs), info)),
    }
}

fn abs_int<B: BV>(x: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match x {
        Val::I128(x) => Ok(Val::I128(x.abs())),
        Val::Symbolic(x) => {
            let y = solver.fresh();
            solver.add(Def::DefineConst(
                y,
                Exp::Ite(
                    Box::new(Exp::Bvslt(Box::new(Exp::Var(x)), Box::new(smt_i128(0)))),
                    Box::new(Exp::Bvneg(Box::new(Exp::Var(x)))),
                    Box::new(Exp::Var(x)),
                ),
            ));
            Ok(Val::Symbolic(y))
        }
        _ => Err(ExecError::Type(format!("abs_int {:?}", &x), info)),
    }
}

// Arithmetic operations

fn ediv_i128<V: Clone>(x: Box<Exp<V>>, y: Box<Exp<V>>) -> Exp<V> {
    Exp::Ite(
        Box::new(Exp::Bvslt(Box::new(Exp::Bvsrem(x.clone(), y.clone())), Box::new(smt_i128(0)))),
        Box::new(Exp::Ite(
            Box::new(Exp::Bvsgt(y.clone(), Box::new(smt_i128(0)))),
            Box::new(Exp::Bvsub(Box::new(Exp::Bvsdiv(x.clone(), y.clone())), Box::new(smt_i128(1)))),
            Box::new(Exp::Bvadd(Box::new(Exp::Bvsdiv(x.clone(), y.clone())), Box::new(smt_i128(1)))),
        )),
        Box::new(Exp::Bvsdiv(x, y)),
    )
}

fn emod_i128<V: Clone>(x: Box<Exp<V>>, y: Box<Exp<V>>) -> Exp<V> {
    let srem = Box::new(Exp::Bvsrem(x, y.clone()));
    Exp::Ite(
        Box::new(Exp::Bvslt(srem.clone(), Box::new(smt_i128(0)))),
        Box::new(Exp::Ite(
            Box::new(Exp::Bvslt(y.clone(), Box::new(smt_i128(0)))),
            Box::new(Exp::Bvsub(srem.clone(), y.clone())),
            Box::new(Exp::Bvadd(srem.clone(), y)),
        )),
        srem,
    )
}

binary_primop_copy!(sub_int, "sub_int".to_string(), Val::I128, Val::I128, i128::wrapping_sub, Exp::Bvsub, smt_i128);
binary_primop_copy!(mult_int, "mult_int".to_string(), Val::I128, Val::I128, i128::wrapping_mul, Exp::Bvmul, smt_i128);
unary_primop_copy!(neg_int, "neg_int".to_string(), Val::I128, Val::I128, i128::wrapping_neg, Exp::Bvneg);
binary_primop_copy!(tdiv_int, "tdiv_int".to_string(), Val::I128, Val::I128, i128::wrapping_div, Exp::Bvsdiv, smt_i128);
binary_primop_copy!(
    ediv_int,
    "ediv_int".to_string(),
    Val::I128,
    Val::I128,
    i128::wrapping_div_euclid,
    ediv_i128,
    smt_i128
);
binary_primop_copy!(tmod_int, "tmod_int".to_string(), Val::I128, Val::I128, i128::wrapping_rem, Exp::Bvsrem, smt_i128);
binary_primop_copy!(
    emod_int,
    "emod_int".to_string(),
    Val::I128,
    Val::I128,
    i128::wrapping_rem_euclid,
    emod_i128,
    smt_i128
);
binary_primop_copy!(shl_int, "shl_int".to_string(), Val::I128, Val::I128, i128::shl, Exp::Bvshl, smt_i128);
binary_primop_copy!(shr_int, "shr_int".to_string(), Val::I128, Val::I128, i128::shr, Exp::Bvashr, smt_i128);
binary_primop_copy!(shl_mach_int, "shl_mach_int".to_string(), Val::I64, Val::I64, i64::shl, Exp::Bvshl, smt_i64);
binary_primop_copy!(shr_mach_int, "shr_mach_int".to_string(), Val::I64, Val::I64, i64::shr, Exp::Bvashr, smt_i64);
binary_primop_copy!(udiv_int, "udiv_int".to_string(), Val::I128, Val::I128, i128::wrapping_div, Exp::Bvudiv, smt_i128);

pub(crate) fn add_int<B: BV>(
    x: Val<B>,
    y: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match (x, y) {
        (Val::Symbolic(x), Val::Symbolic(y)) => {
            solver.define_const(Exp::Bvadd(Box::new(Exp::Var(x)), Box::new(Exp::Var(y))), info).into()
        }
        (Val::Symbolic(x), Val::I128(y)) => {
            if y != 0 {
                solver.define_const(Exp::Bvadd(Box::new(Exp::Var(x)), Box::new(smt_i128(y))), info).into()
            } else {
                Ok(Val::Symbolic(x))
            }
        }
        (Val::I128(x), Val::Symbolic(y)) => {
            if x != 0 {
                solver.define_const(Exp::Bvadd(Box::new(smt_i128(x)), Box::new(Exp::Var(y))), info).into()
            } else {
                Ok(Val::Symbolic(y))
            }
        }
        (Val::I128(x), Val::I128(y)) => Ok(Val::I128(i128::wrapping_add(x, y))),
        (x, y) => Err(ExecError::Type(format!("add_int {:?} {:?}", &x, &y), info)),
    }
}

macro_rules! symbolic_compare {
    ($op: path, $x: expr, $y: expr, $solver: ident) => {{
        let z = $solver.fresh();
        $solver
            .add(Def::DefineConst(z, Exp::Ite(Box::new($op(Box::new($x), Box::new($y))), Box::new($x), Box::new($y))));
        Ok(Val::Symbolic(z))
    }};
}

fn max_int<B: BV>(x: Val<B>, y: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let x = concretize_proven_i128(x, solver, info)?;
    let y = concretize_proven_i128(y, solver, info)?;
    match (x, y) {
        (Val::I128(x), Val::I128(y)) => Ok(Val::I128(i128::max(x, y))),
        (Val::I128(x), Val::Symbolic(y)) => symbolic_compare!(Exp::Bvsgt, smt_i128(x), Exp::Var(y), solver),
        (Val::Symbolic(x), Val::I128(y)) => symbolic_compare!(Exp::Bvsgt, Exp::Var(x), smt_i128(y), solver),
        (Val::Symbolic(x), Val::Symbolic(y)) => symbolic_compare!(Exp::Bvsgt, Exp::Var(x), Exp::Var(y), solver),
        (x, y) => Err(ExecError::Type(format!("max_int {:?} {:?}", &x, &y), info)),
    }
}

fn min_int<B: BV>(x: Val<B>, y: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let x = concretize_proven_i128(x, solver, info)?;
    let y = concretize_proven_i128(y, solver, info)?;
    match (x, y) {
        (Val::I128(x), Val::I128(y)) => Ok(Val::I128(i128::min(x, y))),
        (Val::I128(x), Val::Symbolic(y)) => symbolic_compare!(Exp::Bvslt, smt_i128(x), Exp::Var(y), solver),
        (Val::Symbolic(x), Val::I128(y)) => symbolic_compare!(Exp::Bvslt, Exp::Var(x), smt_i128(y), solver),
        (Val::Symbolic(x), Val::Symbolic(y)) => symbolic_compare!(Exp::Bvslt, Exp::Var(x), Exp::Var(y), solver),
        (x, y) => Err(ExecError::Type(format!("max_int {:?} {:?}", &x, &y), info)),
    }
}

fn pow2<B: BV>(x: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let x = concretize_proven_i128(x, solver, info)?;
    panic_if_negative_concretized_nat("pow2", &x);
    match x {
        Val::I128(x) => Ok(Val::I128(1 << x)),
        Val::Symbolic(x) => solver.define_const(Exp::Bvshl(Box::new(smt_i128(1)), Box::new(Exp::Var(x))), info).into(),
        _ => Err(ExecError::Type(format!("pow2 {:?}", &x), info)),
    }
}

fn pow_int<B: BV>(x: Val<B>, y: Val<B>, _solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (x, y) {
        (Val::I128(x), Val::I128(y)) => Ok(Val::I128(x.pow(y.try_into().map_err(|_| ExecError::Overflow)?))),
        (x, y) => Err(ExecError::Type(format!("pow_int {:?} {:?}", &x, &y), info)),
    }
}

fn sub_nat<B: BV>(x: Val<B>, y: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let x = concretize_proven_i128(x, solver, info)?;
    let y = concretize_proven_i128(y, solver, info)?;
    match (x, y) {
        (Val::I128(x), Val::I128(y)) => Ok(Val::I128(i128::max(x - y, 0))),
        (Val::I128(x), Val::Symbolic(y)) => {
            symbolic_compare!(Exp::Bvsgt, Exp::Bvsub(Box::new(smt_i128(x)), Box::new(Exp::Var(y))), smt_i128(0), solver)
        }
        (Val::Symbolic(x), Val::I128(y)) => {
            symbolic_compare!(Exp::Bvsgt, Exp::Bvsub(Box::new(Exp::Var(x)), Box::new(smt_i128(y))), smt_i128(0), solver)
        }
        (Val::Symbolic(x), Val::Symbolic(y)) => {
            symbolic_compare!(Exp::Bvsgt, Exp::Bvsub(Box::new(Exp::Var(x)), Box::new(Exp::Var(y))), smt_i128(0), solver)
        }
        (x, y) => Err(ExecError::Type(format!("sub_nat {:?} {:?}", &x, &y), info)),
    }
}

// Bitvector operations

fn length<B: BV>(x: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match x {
        Val::Symbolic(v) => match solver.length(v) {
            Some(len) => Ok(Val::I128(i128::from(len))),
            None => Err(ExecError::Type(format!("length (solver cannot determine length) {:?}", &v), info)),
        },
        Val::Bits(bv) => Ok(Val::I128(bv.len_i128())),
        Val::MixedBits(segments) => Ok(Val::I128(
            segments.iter().try_fold(0, |n, segment| Ok(n + i128::from(segment_length(segment, solver, info)?)))?,
        )),
        Val::Vector(v) => Ok(Val::I128(v.len() as i128)),
        _ => Err(ExecError::Type(format!("length {:?}", &x), info)),
    }
}

binary_primop!(eq_bits, "eq_bits".to_string(), Val::Bits, Val::Bool, B::eq, Exp::Eq, smt_sbits);
binary_primop!(neq_bits, "neq_bits".to_string(), Val::Bits, Val::Bool, B::ne, Exp::Neq, smt_sbits);
unary_primop_copy!(not_bits, "not_bits".to_string(), Val::Bits, Val::Bits, B::not, Exp::Bvnot);
binary_primop_copy!(xor_bits, "xor_bits".to_string(), Val::Bits, Val::Bits, B::bitxor, Exp::Bvxor, smt_sbits);
binary_primop_copy!(or_bits, "or_bits".to_string(), Val::Bits, Val::Bits, B::bitor, Exp::Bvor, smt_sbits);
binary_primop_copy!(and_bits, "and_bits".to_string(), Val::Bits, Val::Bits, B::bitand, Exp::Bvand, smt_sbits);
binary_primop_copy!(add_bits, "add_bits".to_string(), Val::Bits, Val::Bits, B::add, Exp::Bvadd, smt_sbits);
binary_primop_copy!(sub_bits, "sub_bits".to_string(), Val::Bits, Val::Bits, B::sub, Exp::Bvsub, smt_sbits);

fn add_bits_int<B: BV>(bits: Val<B>, n: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (bits, n) {
        (Val::Bits(bits), Val::I128(n)) => Ok(Val::Bits(bits.add_i128(n))),
        (Val::Symbolic(bits), Val::I128(n)) => {
            let result = solver.fresh();
            let len = match solver.length(bits) {
                Some(len) => len,
                None => {
                    return Err(ExecError::Type(
                        format!("add_bits_int (solver cannot determine length) {:?} {:?}", &bits, &n),
                        info,
                    ))
                }
            };
            assert!(len <= 128);
            solver.add(Def::DefineConst(
                result,
                Exp::Bvadd(Box::new(Exp::Var(bits)), Box::new(Exp::Extract(len - 1, 0, Box::new(smt_i128(n))))),
            ));
            Ok(Val::Symbolic(result))
        }
        (Val::Bits(bits), Val::Symbolic(n)) => {
            let result = solver.fresh();
            assert!(bits.len() <= 128);
            solver.add(Def::DefineConst(
                result,
                Exp::Bvadd(Box::new(smt_sbits(bits)), Box::new(Exp::Extract(bits.len() - 1, 0, Box::new(Exp::Var(n))))),
            ));
            Ok(Val::Symbolic(result))
        }
        (Val::Symbolic(bits), Val::Symbolic(n)) => {
            let result = solver.fresh();
            let len = match solver.length(bits) {
                Some(len) => len,
                None => {
                    return Err(ExecError::Type(
                        format!("add_bits_int (solver cannot determine length) {:?} {:?}", &bits, &n),
                        info,
                    ))
                }
            };
            assert!(len <= 128);
            solver.add(Def::DefineConst(
                result,
                Exp::Bvadd(Box::new(Exp::Var(bits)), Box::new(Exp::Extract(len - 1, 0, Box::new(Exp::Var(n))))),
            ));
            Ok(Val::Symbolic(result))
        }
        (bits, n) => Err(ExecError::Type(format!("add_bits_int {:?} {:?}", &bits, &n), info)),
    }
}

fn sub_bits_int<B: BV>(bits: Val<B>, n: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (bits, n) {
        (Val::Bits(bits), Val::I128(n)) => Ok(Val::Bits(bits.sub_i128(n))),
        (Val::Symbolic(bits), Val::I128(n)) => {
            let result = solver.fresh();
            let len = match solver.length(bits) {
                Some(len) => len,
                None => {
                    return Err(ExecError::Type(
                        format!("sub_bits_int (solver cannot determine length) {:?} {:?}", &bits, &n),
                        info,
                    ))
                }
            };
            assert!(len <= 128);
            solver.add(Def::DefineConst(
                result,
                Exp::Bvsub(Box::new(Exp::Var(bits)), Box::new(Exp::Extract(len - 1, 0, Box::new(smt_i128(n))))),
            ));
            Ok(Val::Symbolic(result))
        }
        (Val::Bits(bits), Val::Symbolic(n)) => {
            let result = solver.fresh();
            assert!(bits.len() <= 128);
            solver.add(Def::DefineConst(
                result,
                Exp::Bvsub(Box::new(smt_sbits(bits)), Box::new(Exp::Extract(bits.len() - 1, 0, Box::new(Exp::Var(n))))),
            ));
            Ok(Val::Symbolic(result))
        }
        (Val::Symbolic(bits), Val::Symbolic(n)) => {
            let result = solver.fresh();
            let len = match solver.length(bits) {
                Some(len) => len,
                None => {
                    return Err(ExecError::Type(
                        format!("sub_bits_int (solver cannot determine length) {:?} {:?}", &bits, &n),
                        info,
                    ))
                }
            };
            assert!(len <= 128);
            solver.add(Def::DefineConst(
                result,
                Exp::Bvsub(Box::new(Exp::Var(bits)), Box::new(Exp::Extract(len - 1, 0, Box::new(Exp::Var(n))))),
            ));
            Ok(Val::Symbolic(result))
        }
        (bits, n) => Err(ExecError::Type(format!("sub_bits_int {:?} {:?}", &bits, &n), info)),
    }
}

fn smt_i128_width<V>(value: i128, width: u32) -> Option<Exp<V>> {
    if width == 0 {
        return None;
    }
    if width < 128 && value >= 0 && value >= (1_i128 << width) {
        return None;
    }

    if width <= 64 {
        Some(Exp::Bits64(B64::new(value as u64, width)))
    } else {
        let mut bits = vec![false; width as usize];
        for i in 0..width {
            if (value >> i & 1) == 1 {
                bits[i as usize] = true;
            }
        }
        Some(Exp::Bits(bits))
    }
}

/// 把模型里的位向量按二进制补码还原成 i128，是 `smt_i128_width` 的逆运算。
fn i128_from_model_bits(bits: &[bool]) -> Option<i128> {
    let width = bits.len();
    if width == 0 || width > 128 {
        return None;
    }
    let mut value: i128 = 0;
    for (index, bit) in bits.iter().enumerate() {
        if *bit {
            value |= 1_i128 << index
        }
    }
    // 位宽不足 128 时最高位是符号位，需要手工符号扩展。
    if width < 128 && bits[width - 1] {
        value |= -1_i128 << width
    }
    Some(value)
}

/// 只有当前路径约束已经把 `sym` 钉成唯一常量时，才把它具体化成 i128。
///
/// 判定方式是"取一个模型值 `v`，再问 solver `sym != v` 是否不可满足"：不可满足说明所有
/// 可行模型都必须让 `sym == v`，可以安全具体化；可满足说明还存在别的取值，必须保持符号量。
/// 整个判定固定只用 1 次 check-sat + 1 次模型求值 + 1 次 check-sat-assuming。
///
/// 历史实现是逐个枚举候选常量（72 个常用值再加上 `0..=512` 的全部整数）各问一次 solver。
/// 对向量元素这类永远证明不出唯一值的符号量，那 515 次查询全部落空；而 `max_int`/`min_int`
/// 要对两个参数各做一次，于是逐 lane 的 `max(signed(a), signed(b))` 一次就是上千次 check-sat，
/// 实测让 VMIN/VMAX 这几条指令的路径撞满 30m 单路径预算。改成模型法后不再受候选集合限制，
/// 超过 512 或很大的负数同样能被证明。
pub(crate) fn proven_symbolic_i128<B: BV>(
    sym: Sym,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<i128>, ExecError> {
    let Some(width) = solver.length(sym) else { return Ok(None) };

    // 取模型前必须先 check-sat；路径已经不可满足时没有模型可取，保持符号量交给调用方。
    match solver.check_sat(info) {
        SmtResult::Sat => (),
        SmtResult::Unsat | SmtResult::Unknown => return Ok(None),
        SmtResult::Error(error) => return Err(ExecError::Smt(error)),
    }

    let candidate = {
        let mut model = Model::new(solver);
        match model.get_var(sym)? {
            ModelVal::Exp(Exp::Bits64(bv)) => bv.signed(),
            ModelVal::Exp(Exp::Bits(bits)) => match i128_from_model_bits(&bits) {
                Some(value) => value,
                None => return Ok(None),
            },
            // 模型没有给它赋值，说明当前约束根本没限制它，不可能唯一。
            ModelVal::Arbitrary(_) => return Ok(None),
            // 非位向量的模型值不属于 i128 具体化的范畴。
            ModelVal::Exp(_) => return Ok(None),
        }
    };

    let Some(candidate_exp) = smt_i128_width(candidate, width) else { return Ok(None) };
    // Unsat 表示 sym 不可能取别的值；Sat 表示还有别的取值，Unknown 同样不能安全具体化。
    match solver.check_sat_with(&Exp::Neq(Box::new(Exp::Var(sym)), Box::new(candidate_exp)), info) {
        SmtResult::Unsat => Ok(Some(candidate)),
        SmtResult::Sat | SmtResult::Unknown => Ok(None),
        SmtResult::Error(error) => Err(ExecError::Smt(error)),
    }
}

fn zeros<B: BV>(len: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let len = concretize_proven_i128(len, solver, info)?;
    panic_if_negative_concretized_nat("zeros", &len);
    match len {
        Val::I128(len) => {
            if len <= B::MAX_WIDTH as i128 {
                Ok(Val::Bits(B::zeros(len as u32)))
            } else {
                solver.define_const(smt_zeros(len), info).into()
            }
        }
        Val::Symbolic(_) => Err(ExecError::SymbolicLength("zeros", info)),
        _ => Err(ExecError::Type(format!("zeros {:?}", &len), info)),
    }
}

fn ones<B: BV>(len: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let len = concretize_proven_i128(len, solver, info)?;
    panic_if_negative_concretized_nat("ones", &len);
    match len {
        Val::I128(len) => {
            if len <= B::MAX_WIDTH as i128 {
                Ok(Val::Bits(B::ones(len as u32)))
            } else {
                solver.define_const(smt_ones(len), info).into()
            }
        }
        Val::Symbolic(_) => Err(ExecError::SymbolicLength("ones", info)),
        _ => Err(ExecError::Type(format!("ones {:?}", &len), info)),
    }
}

/// The zero_extend and sign_extend functions are essentially the
/// same, so use a macro to define both.
macro_rules! extension {
    ($id: ident, $name: expr, $smt_extension: path, $concrete_extension: path) => {
        pub fn $id<B: BV>(
            bits: Val<B>,
            len: Val<B>,
            solver: &mut Solver<B>,
            info: SourceLoc,
        ) -> Result<Val<B>, ExecError> {
            let len = concretize_proven_i128(len, solver, info)?;
            panic_if_negative_concretized_nat("extension", &len);
            let len = match len {
                Val::I128(len) => len,
                Val::Symbolic(_) => return Err(ExecError::SymbolicLength("extension", info)),
                _ => return Err(ExecError::Type($name, info)),
            };
            let len = u32::try_from(len).map_err(|_| ExecError::Overflow)?;

            match replace_mixed_bits(bits, solver, info)? {
                Val::Bits(bits) => {
                    if len < bits.len() {
                        return Err(ExecError::Type($name, info));
                    }
                    if len > B::MAX_WIDTH {
                        let ext = len - bits.len();
                        solver.define_const($smt_extension(ext, Box::new(smt_sbits(bits))), info).into()
                    } else {
                        Ok(Val::Bits($concrete_extension(bits, len)))
                    }
                }
                Val::Symbolic(bits) => {
                    let ext = match solver.length(bits) {
                        Some(orig_len) if len >= orig_len => len - orig_len,
                        None => return Err(ExecError::Type($name, info)),
                        Some(_) => return Err(ExecError::Type($name, info)),
                    };
                    solver.define_const($smt_extension(ext, Box::new(Exp::Var(bits))), info).into()
                }
                _ => Err(ExecError::Type($name, info)),
            }
        }
    };
}

extension!(zero_extend, "zero_extend".to_string(), Exp::ZeroExtend, B::zero_extend);
extension!(sign_extend, "sign_extend".to_string(), Exp::SignExtend, B::sign_extend);

pub(crate) fn op_zero_extend<B: BV>(
    bits: Val<B>,
    len: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let bits = replace_mixed_bits(bits, solver, info)?;
    match bits {
        Val::Bits(bits) => {
            if len > 64 {
                let ext = len - bits.len();
                solver.define_const(Exp::ZeroExtend(ext, Box::new(smt_sbits(bits))), info).into()
            } else {
                Ok(Val::Bits(B::zero_extend(bits, len)))
            }
        }
        Val::Symbolic(bits) => {
            let ext = match solver.length(bits) {
                Some(orig_len) => len - orig_len,
                None => {
                    return Err(ExecError::Type(
                        format!("op_zero_extend (solver cannot determine length) {:?}", &bits),
                        info,
                    ))
                }
            };
            solver.define_const(Exp::ZeroExtend(ext, Box::new(Exp::Var(bits))), info).into()
        }
        _ => Err(ExecError::Type(format!("op_zero_extend {:?}", &bits), info)),
    }
}

fn replicate_exp<V: Clone>(bits: Exp<V>, times: i128) -> Exp<V> {
    if times == 0 {
        bits64(0, 0)
    } else if times == 1 {
        bits
    } else {
        Exp::Concat(Box::new(bits.clone()), Box::new(replicate_exp(bits, times - 1)))
    }
}

fn replicate_bits<B: BV>(
    bits: Val<B>,
    times: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let bits = replace_mixed_bits(bits, solver, info)?;
    let times = concretize_proven_i128(times, solver, info)?;
    panic_if_negative_concretized_nat("replicate_bits", &times);

    match (bits, times) {
        (Val::Bits(bits), Val::I128(times)) => match bits.replicate(times) {
            Some(replicated) => Ok(Val::Bits(replicated)),
            None => solver.define_const(replicate_exp(smt_sbits(bits), times), info).into(),
        },
        (Val::Symbolic(bits), Val::I128(times)) => {
            if times == 0 {
                Ok(Val::Bits(B::zeros(0)))
            } else {
                solver.define_const(replicate_exp(Exp::Var(bits), times), info).into()
            }
        }
        (_, Val::Symbolic(_)) => Err(ExecError::SymbolicLength("replicate_bits", info)),
        (bits, times) => Err(ExecError::Type(format!("replicate_bits {:?} {:?}", &bits, &times), info)),
    }
}

/// This macro implements the symbolic slice operation for anything
/// that is implemented as a bitvector in the SMT solver, so it can be
/// used for slice, get_slice_int, etc.
macro_rules! slice {
    ($bits_length: expr, $bits: expr, $from: expr, $slice_length: expr, $solver: ident, $info: ident) => {{
        assert!(($slice_length as u32) <= $bits_length);
        match $from {
            _ if $slice_length == 0 => Ok(Val::Bits(B::zeros(0))),

            Val::Symbolic(from) => {
                let sliced = $solver.fresh();
                // As from is symbolic we need to use bvlshr to do a
                // left shift before extracting between length - 1 to
                // 0. We therefore need to make from the correct
                // length so the bvlshr is type-correct.
                let shift = if $bits_length > 128 {
                    Exp::ZeroExtend($bits_length - 128, Box::new(Exp::Var(from)))
                } else if $bits_length < 128 {
                    Exp::Extract($bits_length - 1, 0, Box::new(Exp::Var(from)))
                } else {
                    Exp::Var(from)
                };
                $solver.add(Def::DefineConst(
                    sliced,
                    Exp::Extract($slice_length as u32 - 1, 0, Box::new(Exp::Bvlshr(Box::new($bits), Box::new(shift)))),
                ));
                Ok(Val::Symbolic(sliced))
            }

            Val::I128(from) => {
                let sliced = $solver.fresh();
                if from == 0 && ($slice_length as u32) == $bits_length {
                    $solver.add(Def::DefineConst(sliced, $bits))
                } else {
                    $solver.add(Def::DefineConst(
                        sliced,
                        Exp::Extract((from + $slice_length - 1) as u32, from as u32, Box::new($bits)),
                    ))
                }
                Ok(Val::Symbolic(sliced))
            }

            Val::I64(from) => {
                let sliced = $solver.fresh();
                if from == 0 && ($slice_length as u32) == $bits_length {
                    $solver.add(Def::DefineConst(sliced, $bits))
                } else {
                    $solver.add(Def::DefineConst(
                        sliced,
                        Exp::Extract((from as i128 + $slice_length - 1) as u32, from as u32, Box::new($bits)),
                    ))
                }
                Ok(Val::Symbolic(sliced))
            }

            _ => Err(ExecError::Type(format!("slice! {:?}", &$from), $info)),
        }
    }};
}

fn mixed_bits_slice<B: BV>(
    segments: &[BitsSegment<B>],
    bits_length: u32,
    from: u32,
    length: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let mut remaining = bits_length;
    let mut new_segments = vec![];
    let to = from + length;
    for segment in segments {
        let segment_length = segment_length(segment, solver, info)?;
        let segment_bottom = remaining - segment_length;
        if to > segment_bottom {
            if from >= remaining {
                break;
            }
            if to >= remaining && segment_bottom >= from {
                new_segments.push(segment.clone());
            } else {
                let segment_to = min(segment_length, to - segment_bottom) - 1;
                let segment_from = from.saturating_sub(segment_bottom);
                let new_segment = match segment {
                    BitsSegment::Symbolic(v) => BitsSegment::Symbolic(
                        solver.define_const(Exp::Extract(segment_to, segment_from, Box::new(Exp::Var(*v))), info),
                    ),
                    BitsSegment::Concrete(bv) => BitsSegment::Concrete(
                        bv.extract(segment_to, segment_from)
                            .ok_or_else(|| ExecError::Unreachable("op_slice MixedBits Concrete extract".to_string()))?,
                    ),
                };
                new_segments.push(new_segment);
            }
        }
        remaining -= segment_length;
    }
    match new_segments[..] {
        [BitsSegment::Symbolic(v)] => Ok(Val::Symbolic(v)),
        [BitsSegment::Concrete(bv)] => Ok(Val::Bits(bv)),
        _ => Ok(Val::MixedBits(new_segments)),
    }
}

pub(crate) fn op_slice<B: BV>(
    bits: Val<B>,
    from: Val<B>,
    length: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let bits_length = length_bits(&bits, solver, info)?;
    match bits {
        Val::Symbolic(bits) => slice!(bits_length, Exp::Var(bits), from, length as i128, solver, info),
        Val::Bits(bits) => match from {
            Val::I64(from) => match bits.slice(from as u32, length) {
                Some(bits) => Ok(Val::Bits(bits)),
                None => Err(ExecError::Type("op_slice (can't slice)".to_string(), info)),
            },
            _ if bits.is_zero() => Ok(Val::Bits(B::zeros(length))),
            _ => slice!(bits_length, smt_sbits(bits), from, length as i128, solver, info),
        },
        Val::MixedBits(ref segments) => match from {
            Val::I64(from) => mixed_bits_slice(segments, bits_length, from as u32, length, solver, info),
            _ => op_slice(replace_mixed_bits(bits, solver, info)?, from, length, solver, info),
        },
        _ => Err(ExecError::Type(format!("op_slice {:?}", &bits), info)),
    }
}

fn slice_internal<B: BV>(
    bits: Val<B>,
    from: Val<B>,
    length: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let bits_length = length_bits(&bits, solver, info)?;
    match length {
        Val::I128(length) => match bits {
            Val::Symbolic(bits) => slice!(bits_length, Exp::Var(bits), from, length, solver, info),
            Val::Bits(bits) => match from {
                Val::I128(from) => match bits.slice(from as u32, length as u32) {
                    Some(bits) => Ok(Val::Bits(bits)),
                    None => {
                        // Out-of-range slices shouldn't happen in IR from well-typed Sail, but linearization can
                        // produce them (although the result will be thrown away).  This should match the semantics
                        // of the symbolic case but isn't tested because the results aren't used.
                        match bits.shiftr(from).slice(0, length as u32) {
                            Some(bits) => Ok(Val::Bits(bits)),
                            None => Err(ExecError::Type(
                                format!("slice_internal (cannot slice) {:?} {:?}", &from, &length),
                                info,
                            )),
                        }
                    }
                },
                _ if bits.is_zero() => Ok(Val::Bits(B::zeros(length as u32))),
                _ => slice!(bits_length, smt_sbits(bits), from, length, solver, info),
            },
            Val::MixedBits(ref segments) => match from {
                Val::I128(from) => mixed_bits_slice(segments, bits_length, from as u32, length as u32, solver, info),
                _ => {
                    let bits_smt = mixed_bits_to_smt(bits, solver, info)?;
                    slice!(bits_length, bits_smt, from, length, solver, info)
                }
            },
            _ => Err(ExecError::Type(format!("slice_internal {:?}", &bits), info)),
        },
        _ => Err(ExecError::Type(format!("slice_internal {:?}", &length), info)),
    }
}

fn slice<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    slice_internal(args[0].clone(), args[1].clone(), args[2].clone(), solver, info)
}

pub fn subrange_internal<B: BV>(
    bits: Val<B>,
    high: Val<B>,
    low: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let high = concretize_proven_i128(high, solver, info)?;
    panic_if_negative_concretized_nat("subrange_internal", &high);
    let low = concretize_proven_i128(low, solver, info)?;
    panic_if_negative_concretized_nat("subrange_internal", &low);
    match (bits, high, low) {
        (Val::Symbolic(bits), Val::I128(high), Val::I128(low)) => {
            solver.define_const(Exp::Extract(high as u32, low as u32, Box::new(Exp::Var(bits))), info).into()
        }
        (Val::Bits(bits), Val::I128(high), Val::I128(low)) => match bits.extract(high as u32, low as u32) {
            Some(bits) => Ok(Val::Bits(bits)),
            None => Err(ExecError::Type(
                format!("subrange_internal (cannot extract) {:?} {:?} {:?}", &bits, &high, &low),
                info,
            )),
        },
        (Val::MixedBits(ref segments), Val::I128(high), Val::I128(low)) => {
            let bits_length = segments_length(segments, solver, info)?;
            mixed_bits_slice(segments, bits_length, low as u32, (high - low + 1) as u32, solver, info)
        }
        (bits, Val::Symbolic(high), Val::Symbolic(low)) => {
            let width = solver.define_const(
                Exp::Bvadd(
                    Box::new(Exp::Bvsub(Box::new(Exp::Var(high)), Box::new(Exp::Var(low)))),
                    Box::new(smt_i128(1)),
                ),
                info,
            );

            let width = concretize_proven_i128(Val::Symbolic(width), solver, info)?;
            panic_if_negative_concretized_nat("subrange_internal", &width);

            match width {
                Val::I128(width) => {
                    let bits_length = length_bits(&bits, solver, info)?;
                    if 0 <= width && width <= i128::from(bits_length) {
                        slice_internal(bits, Val::Symbolic(low), Val::I128(width), solver, info)
                    } else {
                        Err(ExecError::SymbolicLength("subrange_internal", info))
                    }
                }
                Val::Symbolic(_) => Err(ExecError::SymbolicLength("subrange_internal", info)),
                _ => Err(ExecError::SymbolicLength("subrange_internal", info)),
            }
        }
        (_, Val::Symbolic(_), _) | (_, _, Val::Symbolic(_)) => {
            Err(ExecError::SymbolicLength("subrange_internal", info))
        }
        (bits, high, low) => {
            Err(ExecError::Type(format!("subrange_internal {:?} {:?} {:?}", &bits, &high, &low), info))
        }
    }
}

fn subrange<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    subrange_internal(args[0].clone(), args[1].clone(), args[2].clone(), solver, info)
}

fn sail_truncate<B: BV>(
    bits: Val<B>,
    len: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    slice_internal(bits, Val::I128(0), len, solver, info)
}

fn sail_truncate_lsb<B: BV>(
    bits: Val<B>,
    len: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match (bits, len) {
        (Val::Bits(bits), Val::I128(len)) => match bits.truncate_lsb(len) {
            Some(truncated) => Ok(Val::Bits(truncated)),
            None => Err(ExecError::Type(format!("sail_truncateLSB (cannot truncate) {:?} {:?}", &bits, &len), info)),
        },
        (Val::Symbolic(bits), Val::I128(len)) => {
            if len == 0 {
                Ok(Val::Bits(B::new(0, 0)))
            } else if let Some(orig_len) = solver.length(bits) {
                let low = orig_len - (len as u32);
                solver.define_const(Exp::Extract(orig_len - 1, low, Box::new(Exp::Var(bits))), info).into()
            } else {
                Err(ExecError::Type(format!("sail_truncateLSB (invalid length) {:?} {:?}", &bits, &len), info))
            }
        }
        (Val::MixedBits(ref segments), Val::I128(len)) => {
            let bits_length = segments_length(segments, solver, info)?;
            mixed_bits_slice(segments, bits_length, bits_length - len as u32, len as u32, solver, info)
        }
        (_, Val::Symbolic(_)) => Err(ExecError::SymbolicLength("sail_truncateLSB", info)),
        (bits, len) => Err(ExecError::Type(format!("sail_truncateLSB {:?} {:?}", &bits, &len), info)),
    }
}

fn sail_unsigned<B: BV>(bits: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let bits = replace_mixed_bits(bits, solver, info)?;
    match bits {
        Val::Bits(bits) => Ok(Val::I128(bits.unsigned())),
        Val::Symbolic(bits) => match solver.length(bits) {
            Some(length) => {
                assert!(length < 128);
                solver.define_const(Exp::ZeroExtend(128 - length, Box::new(Exp::Var(bits))), info).into()
            }
            None => Err(ExecError::Type(format!("sail_unsigned (solver cannot determine length) {:?}", &bits), info)),
        },
        _ => Err(ExecError::Type(format!("sail_unsigned {:?}", &bits), info)),
    }
}

fn sail_signed<B: BV>(bits: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let bits = replace_mixed_bits(bits, solver, info)?;
    match bits {
        Val::Bits(bits) => Ok(Val::I128(bits.signed())),
        Val::Symbolic(bits) => match solver.length(bits) {
            Some(length) => {
                assert!(length < 128);
                solver.define_const(Exp::SignExtend(128 - length, Box::new(Exp::Var(bits))), info).into()
            }
            None => Err(ExecError::Type(format!("sail_signed (solver cannot determine length) {:?}", &bits), info)),
        },
        _ => Err(ExecError::Type(format!("sail_signed {:?}", &bits), info)),
    }
}

fn shiftr<B: BV>(bits: Val<B>, shift: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    // We could support (MixedBits, I128) explicitly, if necessary
    let bits = replace_mixed_bits(bits, solver, info)?;
    match (bits, shift) {
        (Val::Symbolic(x), Val::Symbolic(y)) => match solver.length(x) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(Exp::Var(y)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(Exp::Var(y)))
                } else {
                    Exp::Var(y)
                };
                solver.define_const(Exp::Bvlshr(Box::new(Exp::Var(x)), Box::new(shift)), info).into()
            }
            None => Err(ExecError::Type(format!("shiftr {:?} {:?}", &x, &y), info)),
        },
        (Val::Symbolic(x), Val::I128(0)) => Ok(Val::Symbolic(x)),
        (Val::Symbolic(x), Val::I128(y)) => match solver.length(x) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(smt_i128(y)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(smt_i128(y)))
                } else {
                    smt_i128(y)
                };
                solver.define_const(Exp::Bvlshr(Box::new(Exp::Var(x)), Box::new(shift)), info).into()
            }
            None => Err(ExecError::Type(format!("shiftr {:?} {:?}", &x, &y), info)),
        },
        (Val::Bits(x), Val::Symbolic(y)) => solver
            .define_const(
                Exp::Bvlshr(Box::new(smt_sbits(x)), Box::new(Exp::Extract(x.len() - 1, 0, Box::new(Exp::Var(y))))),
                info,
            )
            .into(),
        (Val::Bits(x), Val::I128(y)) => Ok(Val::Bits(x.shiftr(y))),
        (bits, shift) => Err(ExecError::Type(format!("shiftr {:?} {:?}", &bits, &shift), info)),
    }
}

fn arith_shiftr<B: BV>(
    bits: Val<B>,
    shift: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    // We could support (MixedBits, I128) explicitly, if necessary
    let bits = replace_mixed_bits(bits, solver, info)?;
    match (bits, shift) {
        (Val::Symbolic(x), Val::Symbolic(y)) => match solver.length(x) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(Exp::Var(y)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(Exp::Var(y)))
                } else {
                    Exp::Var(y)
                };
                solver.define_const(Exp::Bvashr(Box::new(Exp::Var(x)), Box::new(shift)), info).into()
            }
            None => Err(ExecError::Type(format!("arith_shiftr {:?} {:?}", &x, &y), info)),
        },
        (Val::Symbolic(x), Val::I128(0)) => Ok(Val::Symbolic(x)),
        (Val::Symbolic(x), Val::I128(y)) => match solver.length(x) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(smt_i128(y)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(smt_i128(y)))
                } else {
                    smt_i128(y)
                };
                solver.define_const(Exp::Bvashr(Box::new(Exp::Var(x)), Box::new(shift)), info).into()
            }
            None => Err(ExecError::Type(format!("arith_shiftr {:?} {:?}", &x, &y), info)),
        },
        (Val::Bits(x), Val::Symbolic(y)) => solver
            .define_const(
                Exp::Bvashr(Box::new(smt_sbits(x)), Box::new(Exp::Extract(x.len() - 1, 0, Box::new(Exp::Var(y))))),
                info,
            )
            .into(),
        (Val::Symbolic(x), Val::Bits(y)) => match solver.length(x) {
            Some(length) => {
                let shift = if length < y.len() {
                    Exp::Extract(length - 1, 0, Box::new(smt_sbits(y)))
                } else if length > y.len() {
                    Exp::ZeroExtend(length - y.len(), Box::new(smt_sbits(y)))
                } else {
                    smt_sbits(y)
                };
                solver.define_const(Exp::Bvashr(Box::new(Exp::Var(x)), Box::new(shift)), info).into()
            }
            None => Err(ExecError::Type(format!("arith_shiftr {:?} {:?}", &x, &y), info)),
        },
        (Val::Bits(x), Val::Bits(y)) => {
            let shift: u64 = y.try_into()?;
            Ok(Val::Bits(x.arith_shiftr(i128::from(shift))))
        }
        (Val::Bits(x), Val::I128(y)) => Ok(Val::Bits(x.arith_shiftr(y))),
        (bits, shift) => Err(ExecError::Type(format!("arith_shiftr {:?} {:?}", &bits, &shift), info)),
    }
}

fn shiftl<B: BV>(bits: Val<B>, len: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    // We could support (MixedBits, I128) explicitly, if necessary
    let bits = replace_mixed_bits(bits, solver, info)?;
    match (bits, len) {
        (Val::Symbolic(x), Val::Symbolic(y)) => match solver.length(x) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(Exp::Var(y)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(Exp::Var(y)))
                } else {
                    Exp::Var(y)
                };
                solver.define_const(Exp::Bvshl(Box::new(Exp::Var(x)), Box::new(shift)), info).into()
            }
            None => Err(ExecError::Type(format!("shiftl {:?} {:?}", &x, &y), info)),
        },
        (Val::Symbolic(x), Val::I128(0)) => Ok(Val::Symbolic(x)),
        (Val::Symbolic(x), Val::I128(y)) => match solver.length(x) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(smt_i128(y)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(smt_i128(y)))
                } else {
                    smt_i128(y)
                };
                solver.define_const(Exp::Bvshl(Box::new(Exp::Var(x)), Box::new(shift)), info).into()
            }
            None => Err(ExecError::Type(format!("shiftl {:?} {:?}", &x, &y), info)),
        },
        (Val::Bits(x), Val::Symbolic(y)) => solver
            .define_const(
                Exp::Bvshl(Box::new(smt_sbits(x)), Box::new(Exp::Extract(x.len() - 1, 0, Box::new(Exp::Var(y))))),
                info,
            )
            .into(),
        (Val::Bits(x), Val::I128(y)) => Ok(Val::Bits(x.shiftl(y))),
        (bits, len) => Err(ExecError::Type(format!("shiftl {:?} {:?}", &bits, &len), info)),
    }
}

pub fn shift_bits_right<B: BV>(
    bits: Val<B>,
    shift: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    // We could support (MixedBits, Bits) explicitly, if necessary
    let bits = replace_mixed_bits(bits, solver, info)?;
    let bits_len = length_bits(&bits, solver, info)?;
    let shift = replace_mixed_bits(shift, solver, info)?;
    let shift_len = length_bits(&shift, solver, info)?;
    match (&bits, &shift) {
        (Val::Symbolic(_), Val::Symbolic(_)) | (Val::Bits(_), Val::Symbolic(_)) | (Val::Symbolic(_), Val::Bits(_)) => {
            let shift = if bits_len < shift_len {
                Exp::Extract(bits_len - 1, 0, Box::new(smt_value(&shift, info)?))
            } else if bits_len > shift_len {
                Exp::ZeroExtend(bits_len - shift_len, Box::new(smt_value(&shift, info)?))
            } else {
                smt_value(&shift, info)?
            };
            solver.define_const(Exp::Bvlshr(Box::new(smt_value(&bits, info)?), Box::new(shift)), info).into()
        }
        (Val::Bits(x), Val::Bits(y)) => {
            let shift: u64 = (*y).try_into()?;
            Ok(Val::Bits(x.shiftr(shift as i128)))
        }
        (_, _) => Err(ExecError::Type(format!("shift_bits_right {:?} {:?}", &bits, &shift), info)),
    }
}

pub fn shift_bits_left<B: BV>(
    bits: Val<B>,
    shift: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    // We could support (MixedBits, Bits) explicitly, if necessary
    let bits = replace_mixed_bits(bits, solver, info)?;
    let bits_len = length_bits(&bits, solver, info)?;
    let shift = replace_mixed_bits(shift, solver, info)?;
    let shift_len = length_bits(&shift, solver, info)?;
    match (&bits, &shift) {
        (Val::Symbolic(_), Val::Symbolic(_)) | (Val::Bits(_), Val::Symbolic(_)) | (Val::Symbolic(_), Val::Bits(_)) => {
            let shift = if bits_len < shift_len {
                Exp::Extract(bits_len - 1, 0, Box::new(smt_value(&shift, info)?))
            } else if bits_len > shift_len {
                Exp::ZeroExtend(bits_len - shift_len, Box::new(smt_value(&shift, info)?))
            } else {
                smt_value(&shift, info)?
            };
            solver.define_const(Exp::Bvshl(Box::new(smt_value(&bits, info)?), Box::new(shift)), info).into()
        }
        (Val::Bits(x), Val::Bits(y)) => {
            let shift: u64 = (*y).try_into()?;
            Ok(Val::Bits(x.shiftl(shift as i128)))
        }
        (_, _) => Err(ExecError::Type(format!("shift_bits_left {:?} {:?}", &bits, &shift), info)),
    }
}

pub(crate) fn append<B: BV>(
    lhs: Val<B>,
    rhs: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match (lhs, rhs) {
        (Val::Symbolic(x), Val::Symbolic(y)) => {
            solver.define_const(Exp::Concat(Box::new(Exp::Var(x)), Box::new(Exp::Var(y))), info).into()
        }
        (Val::Symbolic(x), Val::Bits(y)) => {
            if y.len() == 0 {
                solver.define_const(Exp::Var(x), info).into()
            } else {
                solver.define_const(Exp::Concat(Box::new(Exp::Var(x)), Box::new(smt_sbits(y))), info).into()
            }
        }
        (Val::Bits(x), Val::Symbolic(y)) => {
            if x.len() == 0 {
                solver.define_const(Exp::Var(y), info).into()
            } else {
                solver.define_const(Exp::Concat(Box::new(smt_sbits(x)), Box::new(Exp::Var(y))), info).into()
            }
        }
        (Val::Bits(x), Val::Bits(y)) => match x.append(y) {
            Some(z) => Ok(Val::Bits(z)),
            None => solver.define_const(Exp::Concat(Box::new(smt_sbits(x)), Box::new(smt_sbits(y))), info).into(),
        },
        (Val::MixedBits(mut segments), Val::Symbolic(v)) => {
            segments.push(BitsSegment::Symbolic(v));
            Ok(Val::MixedBits(segments))
        }
        (Val::MixedBits(mut segments), Val::Bits(bv)) => {
            segments.push(BitsSegment::Concrete(bv));
            Ok(Val::MixedBits(segments))
        }
        (Val::MixedBits(mut segments_l), Val::MixedBits(mut segments_r)) => {
            segments_l.append(&mut segments_r);
            Ok(Val::MixedBits(segments_l))
        }
        (Val::Symbolic(v), Val::MixedBits(mut segments)) => {
            segments.insert(0, BitsSegment::Symbolic(v));
            Ok(Val::MixedBits(segments))
        }
        (Val::Bits(bv), Val::MixedBits(mut segments)) => {
            segments.insert(0, BitsSegment::Concrete(bv));
            Ok(Val::MixedBits(segments))
        }
        (lhs, rhs) => Err(ExecError::Type(format!("append {:?} {:?}", &lhs, &rhs), info)),
    }
}

fn segment_for_bit<B: BV>(
    segments: &[BitsSegment<B>],
    index: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<(Val<B>, Val<B>), ExecError> {
    let mut segment_from = segments_length(segments, solver, info)?;
    for segment in segments {
        let segment_length = segment_length(segment, solver, info)?;
        segment_from -= segment_length;
        if index >= segment_from {
            return Ok((segment.into(), Val::I128((index - segment_from) as i128)));
        }
    }
    Err(ExecError::OutOfBounds("vector_access"))
}

pub(crate) fn vector_access<B: BV>(
    vec: Val<B>,
    n: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let (vec, n) = match (vec, n) {
        (Val::MixedBits(segments), Val::I128(n)) => segment_for_bit(&segments, n as u32, solver, info)?,
        (vec, n) => (replace_mixed_bits(vec, solver, info)?, n),
    };

    match (vec, n) {
        (Val::Symbolic(bits), Val::Symbolic(n)) => match solver.length(bits) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(Exp::Var(n)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(Exp::Var(n)))
                } else {
                    Exp::Var(n)
                };
                solver
                    .define_const(
                        Exp::Extract(0, 0, Box::new(Exp::Bvlshr(Box::new(Exp::Var(bits)), Box::new(shift)))),
                        info,
                    )
                    .into()
            }
            None => Err(ExecError::Type(format!("vector_access {:?} {:?}", &bits, &n), info)),
        },
        (Val::Symbolic(bits), Val::I128(n)) => match solver.length(bits) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(smt_i128(n)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(smt_i128(n)))
                } else {
                    smt_i128(n)
                };
                solver
                    .define_const(
                        Exp::Extract(0, 0, Box::new(Exp::Bvlshr(Box::new(Exp::Var(bits)), Box::new(shift)))),
                        info,
                    )
                    .into()
            }
            None => Err(ExecError::Type(format!("vector_access {:?} {:?}", &bits, &n), info)),
        },
        (Val::Bits(bits), Val::Symbolic(n)) => {
            let shift = Exp::Extract(bits.len() - 1, 0, Box::new(Exp::Var(n)));
            solver
                .define_const(
                    Exp::Extract(0, 0, Box::new(Exp::Bvlshr(Box::new(smt_sbits(bits)), Box::new(shift)))),
                    info,
                )
                .into()
        }
        (Val::Bits(bits), Val::I128(n)) => match bits.slice(n as u32, 1) {
            Some(bit) => Ok(Val::Bits(bit)),
            None => Err(ExecError::Type(format!("vector_access {:?} {:?}", &bits, &n), info)),
        },
        (Val::Vector(vec), Val::I128(n)) => match vec.get(n as usize) {
            Some(elem) => Ok(elem.clone()),
            None => Err(ExecError::OutOfBounds("vector_access")),
        },
        (Val::Vector(vec), Val::Symbolic(n)) => {
            let mut it = vec.iter().enumerate().rev();
            if let Some((_, last_item)) = it.next() {
                let mut exp = smt_value(last_item, info)?;
                for (i, item) in it {
                    exp = Exp::Ite(
                        Box::new(Exp::Eq(Box::new(Exp::Var(n)), Box::new(bits64(i as u64, 128)))),
                        Box::new(smt_value(item, info)?),
                        Box::new(exp),
                    );
                }
                let var = solver.fresh();
                solver.add(Def::DefineConst(var, exp));
                Ok(Val::Symbolic(var))
            } else {
                Err(ExecError::Type(format!("vector_access {:?} {:?}", &vec, &n), info))
            }
        }
        (vec, n) => Err(ExecError::Type(format!("vector_access {:?} {:?}", &vec, &n), info)),
    }
}

/// The set_slice! macro implements the Sail set_slice builtin for any
/// combination of symbolic or concrete operands, with the result
/// always being symbolic. The argument order is the same as the Sail
/// function it implements, plus the solver as a final argument.
macro_rules! set_slice {
    ($bits_length: expr, $update_length: ident, $bits: expr, $n: expr, $update: expr, $solver: ident, $info: ident) => {
        if $bits_length == 0 {
            Ok(Val::Bits(B::zeros(0)))
        } else if $update_length == 0 {
            $solver.define_const($bits, $info).into()
        } else {
            let mask_lower = smt_mask_lower($bits_length as usize, $update_length as usize);
            let update = if $bits_length == $update_length {
                $update
            } else {
                Exp::ZeroExtend($bits_length - $update_length, Box::new($update))
            };
            let shift = if $bits_length < 128 {
                Exp::Extract($bits_length - 1, 0, Box::new($n))
            } else if $bits_length > 128 {
                Exp::ZeroExtend($bits_length - 128, Box::new($n))
            } else {
                $n
            };
            let sliced = $solver.fresh();
            $solver.add(Def::DefineConst(
                sliced,
                Exp::Bvor(
                    Box::new(Exp::Bvand(
                        Box::new($bits),
                        Box::new(Exp::Bvnot(Box::new(Exp::Bvshl(Box::new(mask_lower), Box::new(shift.clone()))))),
                    )),
                    Box::new(Exp::Bvshl(Box::new(update), Box::new(shift))),
                ),
            ));
            Ok(Val::Symbolic(sliced))
        }
    };
}

/// A special case of set_slice! for when $n == 0, and therefore no shift needs to be applied.
macro_rules! set_slice_n0 {
    ($bits_length: expr, $update_length: ident, $bits: expr, $update: expr, $solver: ident, $info: ident) => {
        if $bits_length == 0 {
            Ok(Val::Bits(B::zeros(0)))
        } else if $update_length == 0 {
            $solver.define_const($bits, $info).into()
        } else {
            let mask_lower = smt_mask_lower($bits_length as usize, $update_length as usize);
            let update = if $bits_length == $update_length {
                $update
            } else {
                Exp::ZeroExtend($bits_length - $update_length, Box::new($update))
            };
            let sliced = $solver.fresh();
            $solver.add(Def::DefineConst(
                sliced,
                Exp::Bvor(
                    Box::new(Exp::Bvand(Box::new($bits), Box::new(Exp::Bvnot(Box::new(mask_lower))))),
                    Box::new(update),
                ),
            ));
            Ok(Val::Symbolic(sliced))
        }
    };
}

pub fn set_slice_internal<B: BV>(
    bits: Val<B>,
    n: Val<B>,
    update: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    // We could support (MixedBits, I128, _) if necessary
    let bits = replace_mixed_bits(bits, solver, info)?;
    let update = replace_mixed_bits(update, solver, info)?;
    let bits_length = length_bits(&bits, solver, info)?;
    let update_length = length_bits(&update, solver, info)?;
    match (bits, n, update) {
        (Val::Symbolic(bits), Val::Symbolic(n), Val::Symbolic(update)) => {
            set_slice!(bits_length, update_length, Exp::Var(bits), Exp::Var(n), Exp::Var(update), solver, info)
        }
        (Val::Symbolic(bits), Val::Symbolic(n), Val::Bits(update)) => {
            set_slice!(bits_length, update_length, Exp::Var(bits), Exp::Var(n), smt_sbits(update), solver, info)
        }
        (Val::Symbolic(bits), Val::I128(n), Val::Symbolic(update)) => {
            if n == 0 {
                set_slice_n0!(bits_length, update_length, Exp::Var(bits), Exp::Var(update), solver, info)
            } else {
                set_slice!(bits_length, update_length, Exp::Var(bits), smt_i128(n), Exp::Var(update), solver, info)
            }
        }
        (Val::Symbolic(bits), Val::I128(n), Val::Bits(update)) => {
            if n == 0 {
                if bits_length == update_length {
                    Ok(Val::Bits(update))
                } else {
                    set_slice_n0!(bits_length, update_length, Exp::Var(bits), smt_sbits(update), solver, info)
                }
            } else {
                set_slice!(bits_length, update_length, Exp::Var(bits), smt_i128(n), smt_sbits(update), solver, info)
            }
        }
        (Val::Bits(bits), Val::Symbolic(n), Val::Symbolic(update)) => {
            set_slice!(bits_length, update_length, smt_sbits(bits), Exp::Var(n), Exp::Var(update), solver, info)
        }
        (Val::Bits(bits), Val::Symbolic(n), Val::Bits(update)) => {
            set_slice!(bits_length, update_length, smt_sbits(bits), Exp::Var(n), smt_sbits(update), solver, info)
        }
        (Val::Bits(bits), Val::I128(n), Val::Symbolic(update)) => {
            if n == 0 {
                set_slice_n0!(bits_length, update_length, smt_sbits(bits), Exp::Var(update), solver, info)
            } else {
                set_slice!(bits_length, update_length, smt_sbits(bits), smt_i128(n), Exp::Var(update), solver, info)
            }
        }
        (Val::Bits(bits), Val::I128(n), Val::Bits(update)) => Ok(Val::Bits(bits.set_slice(n as u32, update))),
        (bits, n, update) => Err(ExecError::Type(format!("set_slice {:?} {:?} {:?}", &bits, &n, &update), info)),
    }
}

fn set_slice<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    // set_slice Sail builtin takes 2 additional integer parameters
    // for the bitvector lengths, which we can ignore.
    set_slice_internal(args[2].clone(), args[3].clone(), args[4].clone(), solver, info)
}

fn set_slice_int_internal<B: BV>(
    int: Val<B>,
    n: Val<B>,
    update: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let update = replace_mixed_bits(update, solver, info)?;
    let update_length = length_bits(&update, solver, info)?;
    match (int, n, update) {
        (Val::Symbolic(int), Val::Symbolic(n), Val::Symbolic(update)) => {
            set_slice!(128, update_length, Exp::Var(int), Exp::Var(n), Exp::Var(update), solver, info)
        }
        (Val::Symbolic(int), Val::Symbolic(n), Val::Bits(update)) => {
            set_slice!(128, update_length, Exp::Var(int), Exp::Var(n), smt_sbits(update), solver, info)
        }
        (Val::Symbolic(int), Val::I128(n), Val::Symbolic(update)) => {
            if n == 0 {
                set_slice_n0!(128, update_length, Exp::Var(int), Exp::Var(update), solver, info)
            } else {
                set_slice!(128, update_length, Exp::Var(int), smt_i128(n), Exp::Var(update), solver, info)
            }
        }
        (Val::Symbolic(int), Val::I128(n), Val::Bits(update)) => {
            if n == 0 {
                set_slice_n0!(128, update_length, Exp::Var(int), smt_sbits(update), solver, info)
            } else {
                set_slice!(128, update_length, Exp::Var(int), smt_i128(n), smt_sbits(update), solver, info)
            }
        }
        (Val::I128(int), Val::Symbolic(n), Val::Symbolic(update)) => {
            set_slice!(128, update_length, smt_i128(int), Exp::Var(n), Exp::Var(update), solver, info)
        }
        (Val::I128(int), Val::Symbolic(n), Val::Bits(update)) => {
            set_slice!(128, update_length, smt_i128(int), Exp::Var(n), smt_sbits(update), solver, info)
        }
        (Val::I128(int), Val::I128(n), Val::Symbolic(update)) => {
            if n == 0 {
                set_slice_n0!(128, update_length, smt_i128(int), Exp::Var(update), solver, info)
            } else {
                set_slice!(128, update_length, smt_i128(int), smt_i128(n), Exp::Var(update), solver, info)
            }
        }
        (Val::I128(int), Val::I128(n), Val::Bits(update)) => Ok(Val::I128(B::set_slice_int(int, n as u32, update))),
        (int, n, update) => Err(ExecError::Type(format!("set_slice_int {:?} {:?} {:?}", &int, &n, &update), info)),
    }
}

fn set_slice_int<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    // set_slice_int Sail builtin takes 1 additional integer parameter for the bitvector length,
    // which we can ignore.
    set_slice_int_internal(args[1].clone(), args[2].clone(), args[3].clone(), solver, info)
}

/// op_set_slice is just set_slice_internal with 64-bit integers rather than 128-bit.
pub(crate) fn op_set_slice<B: BV>(
    bits: Val<B>,
    n: Val<B>,
    update: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    // We could support (MixedBits, I64, _) directly if necessary
    let bits = replace_mixed_bits(bits, solver, info)?;
    let update = replace_mixed_bits(update, solver, info)?;
    let bits_length = length_bits(&bits, solver, info)?;
    let update_length = length_bits(&update, solver, info)?;
    match (bits, n, update) {
        (Val::Symbolic(bits), Val::Symbolic(n), Val::Symbolic(update)) => {
            set_slice!(bits_length, update_length, Exp::Var(bits), Exp::Var(n), Exp::Var(update), solver, info)
        }
        (Val::Symbolic(bits), Val::Symbolic(n), Val::Bits(update)) => {
            set_slice!(bits_length, update_length, Exp::Var(bits), Exp::Var(n), smt_sbits(update), solver, info)
        }
        (Val::Symbolic(bits), Val::I64(n), Val::Symbolic(update)) => {
            if n == 0 {
                set_slice_n0!(bits_length, update_length, Exp::Var(bits), Exp::Var(update), solver, info)
            } else {
                set_slice!(bits_length, update_length, Exp::Var(bits), smt_i64(n), Exp::Var(update), solver, info)
            }
        }
        (Val::Symbolic(bits), Val::I64(n), Val::Bits(update)) => {
            if n == 0 {
                set_slice_n0!(bits_length, update_length, Exp::Var(bits), smt_sbits(update), solver, info)
            } else {
                set_slice!(bits_length, update_length, Exp::Var(bits), smt_i64(n), smt_sbits(update), solver, info)
            }
        }
        (Val::Bits(bits), Val::Symbolic(n), Val::Symbolic(update)) => {
            set_slice!(bits_length, update_length, smt_sbits(bits), Exp::Var(n), Exp::Var(update), solver, info)
        }
        (Val::Bits(bits), Val::Symbolic(n), Val::Bits(update)) => {
            set_slice!(bits_length, update_length, smt_sbits(bits), Exp::Var(n), smt_sbits(update), solver, info)
        }
        (Val::Bits(bits), Val::I64(n), Val::Symbolic(update)) => {
            if n == 0 {
                set_slice_n0!(bits_length, update_length, smt_sbits(bits), Exp::Var(update), solver, info)
            } else {
                set_slice!(bits_length, update_length, smt_sbits(bits), smt_i64(n), Exp::Var(update), solver, info)
            }
        }
        (Val::Bits(bits), Val::I64(n), Val::Bits(update)) => Ok(Val::Bits(bits.set_slice(n as u32, update))),
        (bits, n, update) => Err(ExecError::Type(format!("set_slice {:?} {:?} {:?}", &bits, &n, &update), info)),
    }
}

/// `vector_update` is a special case of `set_slice` where the update
/// is a bitvector of length 1. It can also update ordinary (non bit-)
/// vectors.
pub fn vector_update<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    // We could support some MixedBits cases directly, if necessary
    let arg0 = args[0].clone();
    let arg0 = replace_mixed_bits(arg0, solver, info)?;
    match arg0 {
        Val::Vector(mut vec) => match args[1] {
            Val::I128(n) => {
                vec[n as usize] = args[2].clone();
                Ok(Val::Vector(vec))
            }
            Val::I64(n) => {
                vec[n as usize] = args[2].clone();
                Ok(Val::Vector(vec))
            }
            Val::Symbolic(n) => {
                for (i, item) in vec.iter_mut().enumerate() {
                    let var = solver.fresh();
                    solver.add(Def::DefineConst(
                        var,
                        Exp::Ite(
                            Box::new(Exp::Eq(Box::new(Exp::Var(n)), Box::new(bits64(i as u64, 128)))),
                            Box::new(smt_value(&args[2], info)?),
                            Box::new(smt_value(item, info)?),
                        ),
                    ));
                    *item = Val::Symbolic(var);
                }
                Ok(Val::Vector(vec))
            }
            _ => {
                eprintln!("{:?}", args);
                Err(ExecError::Type(format!("vector_update (index) {:?}", &args[1]), info))
            }
        },
        Val::Bits(_) => {
            // If the argument is a bitvector then `vector_update` is a special case of `set_slice`
            // where the update is a bitvector of length 1
            set_slice_internal(arg0, args[1].clone(), args[2].clone(), solver, info)
        }
        Val::Symbolic(v) if solver.is_bitvector(v) => {
            set_slice_internal(arg0, args[1].clone(), args[2].clone(), solver, info)
        }
        _ => Err(ExecError::Type(format!("vector_update {:?}", &arg0), info)),
    }
}

fn vector_update_subrange<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    set_slice_internal(args[0].clone(), args[2].clone(), args[3].clone(), solver, info)
}

fn undefined_vector<B: BV>(len: Val<B>, elem: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    if let Val::I128(len) = len {
        if let Ok(len) = usize::try_from(len) {
            Ok(Val::Vector(vec![elem; len]))
        } else {
            Err(ExecError::Overflow)
        }
    } else {
        Err(ExecError::SymbolicLength("undefined_vector", info))
    }
}

fn bitvector_update<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    op_set_slice(args[0].clone(), args[1].clone(), args[2].clone(), solver, info)
}

fn get_slice_int_internal<B: BV>(
    length: Val<B>,
    n: Val<B>,
    from: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let length = concretize_proven_i128(length, solver, info)?;
    panic_if_negative_concretized_nat("get_slice_int", &length);
    match length {
        Val::I128(length) => match n {
            Val::Symbolic(n) => slice!(128, Exp::Var(n), from, length, solver, info),
            Val::I128(n) => match from {
                Val::I128(from) if length <= B::MAX_WIDTH as i128 => {
                    Ok(Val::Bits(B::get_slice_int(length as u32, n, from as u32)))
                }
                _ => slice!(128, smt_i128(n), from, length, solver, info),
            },
            _ => Err(ExecError::Type(format!("get_slice_int {:?}", &length), info)),
        },
        Val::Symbolic(_) => Err(ExecError::SymbolicLength("get_slice_int", info)),
        _ => Err(ExecError::Type(format!("get_slice_int length is {:?}", &length), info)),
    }
}

fn get_slice_int<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    get_slice_int_internal(args[0].clone(), args[1].clone(), args[2].clone(), solver, info)
}

fn unit_noop<B: BV>(
    _: Vec<Val<B>>,
    _: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn unimplemented<B: BV>(
    _: Vec<Val<B>>,
    _: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    Err(ExecError::Unimplemented)
}

fn eq_string<B: BV>(lhs: Val<B>, rhs: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (lhs, rhs) {
        (Val::String(lhs), Val::String(rhs)) => Ok(Val::Bool(lhs == rhs)),
        (lhs, rhs) => Err(ExecError::Type(format!("eq_string {:?} {:?}", &lhs, &rhs), info)),
    }
}

fn concat_str<B: BV>(lhs: Val<B>, rhs: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (lhs, rhs) {
        (Val::String(lhs), Val::String(rhs)) => Ok(Val::String(format!("{}{}", lhs, rhs))),
        (lhs, rhs) => Err(ExecError::Type(format!("concat_str {:?} {:?}", &lhs, &rhs), info)),
    }
}

fn hex_str<B: BV>(n: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match n {
        Val::I128(n) => Ok(Val::String(format!("0x{:x}", n))),
        Val::Symbolic(v) => Ok(Val::String(format!("0x[{}]", v))),
        _ => Err(ExecError::Type(format!("hex_str {:?}", &n), info)),
    }
}

fn dec_str<B: BV>(n: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match n {
        Val::I128(n) => Ok(Val::String(format!("{}", n))),
        Val::Symbolic(v) => Ok(Val::String(format!("[{}]", v))),
        _ => Err(ExecError::Type(format!("dec_str {:?}", &n), info)),
    }
}

// Strings can never be symbolic
fn undefined_string<B: BV>(_: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Poison)
}

fn string_to_i128<B: BV>(s: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    if let Val::String(s) = s {
        if let Ok(n) = i128::from_str(&s) {
            Ok(Val::I128(n))
        } else {
            Err(ExecError::Overflow)
        }
    } else {
        Err(ExecError::Type(format!("%string->%int {:?}", &s), info))
    }
}

pub fn eq_anything<B: BV>(
    lhs: Val<B>,
    rhs: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match (replace_mixed_bits(lhs, solver, info)?, replace_mixed_bits(rhs, solver, info)?) {
        (Val::Symbolic(lhs), Val::Symbolic(rhs)) => {
            solver.define_const(Exp::Eq(Box::new(Exp::Var(lhs)), Box::new(Exp::Var(rhs))), info).into()
        }
        (lhs, Val::Symbolic(rhs)) => {
            solver.define_const(Exp::Eq(Box::new(smt_value(&lhs, info)?), Box::new(Exp::Var(rhs))), info).into()
        }
        (Val::Symbolic(lhs), rhs) => {
            solver.define_const(Exp::Eq(Box::new(Exp::Var(lhs)), Box::new(smt_value(&rhs, info)?)), info).into()
        }

        (Val::Bits(lhs), Val::Bits(rhs)) => Ok(Val::Bool(lhs == rhs)),
        (Val::Enum(lhs), Val::Enum(rhs)) => Ok(Val::Bool(lhs == rhs)),
        (Val::Bool(lhs), Val::Bool(rhs)) => Ok(Val::Bool(lhs == rhs)),
        (Val::I128(lhs), Val::I128(rhs)) => Ok(Val::Bool(lhs == rhs)),
        (Val::I64(lhs), Val::I64(rhs)) => Ok(Val::Bool(lhs == rhs)),
        (Val::Struct(lhs), Val::Struct(rhs)) => {
            let mut vars = vec![];
            for (k, lhs_v) in lhs {
                let rhs_v = match rhs.get(&k) {
                    Some(v) => v,
                    None => return Err(ExecError::Type("eq_anything None".to_string(), info)),
                };
                let result = eq_anything(lhs_v, rhs_v.clone(), solver, info)?;
                match result {
                    Val::Bool(true) => (),
                    Val::Bool(false) => return Ok(Val::Bool(false)),
                    Val::Symbolic(r) => vars.push(r),
                    _ => return Err(ExecError::Type(format!("eq_anything {:?}", &result), info)),
                }
            }
            match vars.pop() {
                None => Ok(Val::Bool(true)),
                Some(init) => {
                    let exp = vars
                        .iter()
                        .map(|v| Exp::Var(*v))
                        .fold(Exp::Var(init), |e1, e2| Exp::And(Box::new(e1), Box::new(e2)));
                    solver.define_const(exp, info).into()
                }
            }
        }
        (Val::Ctor(lhs_name, lhs_val), Val::Ctor(rhs_name, rhs_val)) => {
            if lhs_name == rhs_name {
                eq_anything(*lhs_val, *rhs_val, solver, info)
            } else {
                Ok(Val::Bool(false))
            }
        }
        (Val::Unit, Val::Unit) => Ok(Val::Bool(true)),

        // TODO: hack because C backend uses null for nil
        (Val::List(lhs), Val::Poison) => Ok(Val::Bool(lhs.is_empty())),
        (Val::Poison, Val::List(rhs)) => Ok(Val::Bool(rhs.is_empty())),

        (lhs, rhs) => Err(ExecError::Type(format!("eq_anything {:?} {:?}", &lhs, &rhs), info)),
    }
}

fn neq_anything<B: BV>(lhs: Val<B>, rhs: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (replace_mixed_bits(lhs, solver, info)?, replace_mixed_bits(rhs, solver, info)?) {
        (Val::Symbolic(lhs), Val::Symbolic(rhs)) => {
            solver.define_const(Exp::Neq(Box::new(Exp::Var(lhs)), Box::new(Exp::Var(rhs))), info).into()
        }
        (lhs, Val::Symbolic(rhs)) => {
            solver.define_const(Exp::Neq(Box::new(smt_value(&lhs, info)?), Box::new(Exp::Var(rhs))), info).into()
        }
        (Val::Symbolic(lhs), rhs) => {
            solver.define_const(Exp::Neq(Box::new(Exp::Var(lhs)), Box::new(smt_value(&rhs, info)?)), info).into()
        }

        (lhs, rhs) => not_bool(eq_anything(lhs, rhs, solver, info)?, solver, info),
    }
}

fn string_startswith<B: BV>(
    s: Val<B>,
    prefix: Val<B>,
    _: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match (s, prefix) {
        (Val::String(s), Val::String(prefix)) => Ok(Val::Bool(s.starts_with(&prefix))),
        other => Err(ExecError::Type(format!("string_startswith {:?}", &other), info)),
    }
}

fn string_length<B: BV>(s: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    if let Val::String(s) = s {
        Ok(Val::I128(s.len() as i128))
    } else {
        Err(ExecError::Type(format!("string_length {:?}", &s), info))
    }
}

fn string_drop<B: BV>(s: Val<B>, n: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (s, n) {
        (Val::String(s), Val::I128(n)) => Ok(Val::String(s.get((n as usize)..).unwrap_or("").to_string())),
        other => Err(ExecError::Type(format!("string_drop {:?}", &other), info)),
    }
}

fn string_take<B: BV>(s: Val<B>, n: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (s, n) {
        (Val::String(s), Val::I128(n)) => Ok(Val::String(s.get(..(n as usize)).unwrap_or(&s).to_string())),
        other => Err(ExecError::Type(format!("string_take {:?}", &other), info)),
    }
}

fn string_of_segment<B: BV>(segment: &BitsSegment<B>) -> String {
    match segment {
        BitsSegment::Concrete(bv) => format!("{}", bv),
        BitsSegment::Symbolic(v) => format!("v{}", v),
    }
}

fn string_of_bits<B: BV>(bv: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match bv {
        Val::Bits(bv) => Ok(Val::String(format!("{}", bv))),
        Val::Symbolic(v) => Ok(Val::String(format!("v{}", v))),
        Val::MixedBits(segments) => {
            Ok(Val::String(segments.iter().map(|seg| string_of_segment::<B>(seg)).collect::<Vec<String>>().join(" ")))
        }
        other => Err(ExecError::Type(format!("string_of_bits {:?}", &other), info)),
    }
}

fn decimal_string_of_segment<B: BV>(segment: &BitsSegment<B>) -> String {
    match segment {
        BitsSegment::Concrete(bv) => format!("{}", bv),
        BitsSegment::Symbolic(v) => format!("v{}", v),
    }
}

fn decimal_string_of_bits<B: BV>(bv: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match bv {
        Val::Bits(bv) => Ok(Val::String(format!("{}", bv.signed()))),
        Val::Symbolic(v) => Ok(Val::String(format!("v{}", v))),
        Val::MixedBits(segments) => Ok(Val::String(
            segments.iter().map(|seg| decimal_string_of_segment::<B>(seg)).collect::<Vec<String>>().join(" "),
        )),
        other => Err(ExecError::Type(format!("decimal_string_of_bits {:?}", &other), info)),
    }
}

fn string_of_int<B: BV>(n: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match n {
        Val::I128(n) => Ok(Val::String(format!("{}", n))),
        Val::Symbolic(v) => Ok(Val::String(format!("v{}", v))),
        other => Err(ExecError::Type(format!("string_of_int {:?}", &other), info)),
    }
}

fn putchar<B: BV>(_c: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    //if let Val::I128(c) = c {
    //    eprintln!("Stdout: {}", char::from(c as u8))
    //}
    Ok(Val::Unit)
}

fn print<B: BV>(_message: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    //if let Val::String(message) = message {
    //    eprintln!("Stdout: {}", message)
    //}
    Ok(Val::Unit)
}

fn prerr<B: BV>(_message: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    //if let Val::String(message) = message {
    //    eprintln!("Stderr: {}", message)
    //}
    Ok(Val::Unit)
}

fn print_string<B: BV>(
    _prefix: Val<B>,
    _message: Val<B>,
    _: &mut Solver<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn prerr_string<B: BV>(
    _prefix: Val<B>,
    _message: Val<B>,
    _: &mut Solver<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn print_int<B: BV>(_prefix: Val<B>, _n: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn prerr_int<B: BV>(_prefix: Val<B>, _n: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn print_endline<B: BV>(_message: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn prerr_endline<B: BV>(_message: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn print_bits<B: BV>(_message: Val<B>, _bits: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    //if let Val::String(message) = message {
    //    eprintln!("Stdout: {}{:?}", message, bits)
    //}
    Ok(Val::Unit)
}

fn prerr_bits<B: BV>(_message: Val<B>, _bits: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    //if let Val::String(message) = message {
    //    eprintln!("Stderr: {}{:?}", message, bits)
    //}
    Ok(Val::Unit)
}

fn undefined_bitvector<B: BV>(sz: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    if let Val::I128(sz) = sz {
        solver.declare_const(Ty::BitVec(sz as u32), info).into()
    } else {
        Err(ExecError::Type(format!("undefined_bitvector {:?}", &sz), info))
    }
}

fn undefined_bit<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    solver.declare_const(Ty::BitVec(1), info).into()
}

fn undefined_bool<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    solver.declare_const(Ty::Bool, info).into()
}

fn undefined_int<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    solver.declare_const(Ty::BitVec(128), info).into()
}

fn undefined_nat<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let sym = solver.declare_const(Ty::BitVec(128), info);
    solver.add(Def::Assert(Exp::Bvsge(Box::new(Exp::Var(sym)), Box::new(smt_i128(0)))));
    Ok(Val::Symbolic(sym))
}

fn undefined_range<B: BV>(
    lo: Val<B>,
    hi: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let sym = solver.declare_const(Ty::BitVec(128), info);
    solver.add(Def::Assert(Exp::Bvsle(Box::new(smt_value(&lo, info)?), Box::new(Exp::Var(sym)))));
    solver.add(Def::Assert(Exp::Bvsle(Box::new(Exp::Var(sym)), Box::new(smt_value(&hi, info)?))));
    Ok(Val::Symbolic(sym))
}

fn undefined_unit<B: BV>(_: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn one_if<B: BV>(condition: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match condition {
        Val::Bool(true) => Ok(Val::Bits(B::BIT_ONE)),
        Val::Bool(false) => Ok(Val::Bits(B::BIT_ZERO)),
        Val::Symbolic(v) => solver
            .define_const(
                Exp::Ite(Box::new(Exp::Var(v)), Box::new(smt_sbits(B::BIT_ONE)), Box::new(smt_sbits(B::BIT_ZERO))),
                info,
            )
            .into(),
        _ => Err(ExecError::Type(format!("one_if {:?}", &condition), info)),
    }
}

fn zero_if<B: BV>(condition: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match condition {
        Val::Bool(true) => Ok(Val::Bits(B::BIT_ZERO)),
        Val::Bool(false) => Ok(Val::Bits(B::BIT_ONE)),
        Val::Symbolic(v) => solver
            .define_const(
                Exp::Ite(Box::new(Exp::Var(v)), Box::new(smt_sbits(B::BIT_ZERO)), Box::new(smt_sbits(B::BIT_ONE))),
                info,
            )
            .into(),
        other => Err(ExecError::Type(format!("one_if {:?}", &other), info)),
    }
}

fn cons<B: BV>(x: Val<B>, xs: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match xs {
        /* TODO: Make this not a hack */
        Val::Poison => Ok(Val::List(vec![x])),
        Val::List(mut xs) => {
            xs.push(x);
            Ok(Val::List(xs))
        }
        _ => Err(ExecError::Type(format!("cons {:?}", &xs), info)),
    }
}

fn vector_init<B: BV>(len: Val<B>, init: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let len = concretize_proven_i128(len, solver, info)?;
    panic_if_negative_concretized_nat("vector_init", &len);
    match len {
        Val::I128(n) => Ok(Val::Vector(vec![init; n as usize])),
        Val::Symbolic(_) => Err(ExecError::SymbolicLength("vector_init", info)),
        _ => Err(ExecError::SymbolicLength("vector_init", info)),
    }
}

fn expect_i128_arg<B: BV>(
    value: &Val<B>,
    name: &str,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<i128, ExecError> {
    match value {
        Val::I128(value) => Ok(*value),
        Val::I64(value) => Ok(i128::from(*value)),
        Val::Symbolic(sym) => proven_symbolic_i128(*sym, solver, info)?
            .ok_or_else(|| ExecError::Type(format!("{} {:?}", name, value), info)),
        _ => Err(ExecError::Type(format!("{} {:?}", name, value), info)),
    }
}

fn expect_usize_or_symbolic_bound<B: BV>(
    value: &Val<B>,
    upper_bound: usize,
    name: &str,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<usize, ExecError> {
    let value = concretize_proven_i128(value.clone(), solver, info)?;
    panic_if_negative_concretized_nat(name, &value);
    match &value {
        Val::I128(value) => usize::try_from(*value).map_err(|_| ExecError::Overflow),
        Val::I64(value) => usize::try_from(*value).map_err(|_| ExecError::Overflow),
        Val::Symbolic(sym) => {
            let width = solver.length(*sym).ok_or_else(|| ExecError::Type(format!("{} {:?}", name, value), info))?;
            let lower = smt_i128_width(0, width).ok_or(ExecError::Overflow)?;
            let upper = smt_i128_width(upper_bound as i128, width).ok_or(ExecError::Overflow)?;
            solver.add(Def::Assert(Exp::Bvsge(Box::new(Exp::Var(*sym)), Box::new(lower))));
            solver.add(Def::Assert(Exp::Bvsle(Box::new(Exp::Var(*sym)), Box::new(upper))));
            Ok(upper_bound)
        }
        _ => Err(ExecError::Type(format!("{} {:?}", name, value), info)),
    }
}

fn expect_bits_arg<B: BV>(
    value: Val<B>,
    name: &str,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match replace_mixed_bits(value, solver, info)? {
        bits @ (Val::Bits(_) | Val::Symbolic(_)) => Ok(bits),
        value => Err(ExecError::Type(format!("{} {:?}", name, value), info)),
    }
}

fn vreg_element<B: BV>(
    reg: Val<B>,
    offset: u32,
    sew: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match reg {
        Val::Bits(bits) => match bits.slice(offset, sew) {
            Some(element) => Ok(Val::Bits(element)),
            None => Err(ExecError::Type(format!("isla_read_vreg concrete slice {} {}", offset, sew), info)),
        },
        Val::Symbolic(reg) => {
            solver.define_const(Exp::Extract(offset + sew - 1, offset, Box::new(Exp::Var(reg))), info).into()
        }
        value => Err(ExecError::Type(format!("isla_read_vreg element {:?}", value), info)),
    }
}

fn isla_read_vreg_internal<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if args.len() != 11 {
        return Err(ExecError::Type(format!("isla_read_vreg expected 11 arguments, got {}", args.len()), info));
    }

    let sew = u32::try_from(expect_i128_arg(&args[1], "isla_read_vreg SEW", solver, info)?)
        .map_err(|_| ExecError::Overflow)?;
    let vrid = usize::try_from(expect_i128_arg(&args[2], "isla_read_vreg vrid", solver, info)?)
        .map_err(|_| ExecError::Overflow)?;
    let num_elem_arg = args[0].clone();

    if !matches!(sew, 8 | 16 | 32 | 64) {
        return Err(ExecError::Type(format!("isla_read_vreg invalid SEW {}", sew), info));
    }

    let regs = args
        .into_iter()
        .skip(3)
        .map(|arg| expect_bits_arg(arg, "isla_read_vreg register", solver, info))
        .collect::<Result<Vec<_>, _>>()?;

    let vlen = length_bits(&regs[0], solver, info)?;
    if vlen == 0 || vlen % sew != 0 {
        return Err(ExecError::Type(format!("isla_read_vreg invalid VLEN {} for SEW {}", vlen, sew), info));
    }
    for reg in &regs[1..] {
        if length_bits(reg, solver, info)? != vlen {
            return Err(ExecError::Type("isla_read_vreg register width mismatch".to_string(), info));
        }
    }

    let elem_per_reg = (vlen / sew) as usize;
    let max_num_elem = elem_per_reg * regs.len();
    let num_elem =
        expect_usize_or_symbolic_bound(&num_elem_arg, max_num_elem, "isla_read_vreg num_elem", solver, info)?;
    if num_elem > max_num_elem || vrid >= 32 {
        return Err(ExecError::Type(format!("isla_read_vreg out of range num_elem={} vrid={}", num_elem, vrid), info));
    }

    let mut result = Vec::with_capacity(num_elem);
    for i in 0..num_elem {
        let reg_index = i / elem_per_reg;
        let elem_index = i % elem_per_reg;
        result.push(vreg_element(regs[reg_index].clone(), (elem_index as u32) * sew, sew, solver, info)?);
    }

    Ok(Val::Vector(result))
}

fn isla_read_vreg<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    isla_read_vreg_internal(args, solver, info)
}

fn int_exp_128<B: BV>(
    value: &Val<B>,
    solver: &mut Solver<B>,
    name: &str,
    info: SourceLoc,
) -> Result<Exp<Sym>, ExecError> {
    match value {
        Val::I128(value) => Ok(smt_i128(*value)),
        Val::I64(value) => Ok(smt_i128(i128::from(*value))),
        Val::Symbolic(sym) => match solver.length(*sym) {
            Some(128) => Ok(Exp::Var(*sym)),
            Some(width) if width < 128 => Ok(Exp::SignExtend(128 - width, Box::new(Exp::Var(*sym)))),
            Some(width) => Err(ExecError::Type(format!("{} unsupported integer width {}", name, width), info)),
            None => Err(ExecError::Type(format!("{} unknown symbolic integer width", name), info)),
        },
        value => Err(ExecError::Type(format!("{} {:?}", name, value), info)),
    }
}

fn concrete_i128_arg<B: BV>(value: &Val<B>) -> Option<i128> {
    match value {
        Val::I128(value) => Some(*value),
        Val::I64(value) => Some(i128::from(*value)),
        _ => None,
    }
}

fn isla_select_int_internal<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if args.len() != 3 {
        return Err(ExecError::Type(format!("isla_select_int expected 3 arguments, got {}", args.len()), info));
    }

    let condition = args[0].clone();
    let true_value = args[1].clone();
    let false_value = args[2].clone();

    match condition {
        Val::Bool(true) => Ok(true_value),
        Val::Bool(false) => Ok(false_value),
        Val::Symbolic(condition) => {
            let true_exp = int_exp_128(&true_value, solver, "isla_select_int true value", info)?;
            let false_exp = int_exp_128(&false_value, solver, "isla_select_int false value", info)?;
            solver
                .define_const(Exp::Ite(Box::new(Exp::Var(condition)), Box::new(true_exp), Box::new(false_exp)), info)
                .into()
        }
        value => Err(ExecError::Type(format!("isla_select_int condition {:?}", value), info)),
    }
}

fn isla_select_int<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    isla_select_int_internal(args, solver, info)
}

fn concrete_bit<B: BV>(bits: B, bit: u32) -> Result<bool, ExecError> {
    bits.slice(bit, 1).map(|bit| bit == B::BIT_ONE).ok_or(ExecError::Overflow)
}

fn symbolic_bit<B: BV>(bits: &Val<B>, bit: u32, info: SourceLoc) -> Result<Exp<Sym>, ExecError> {
    match bits {
        Val::Bits(bits) => Ok(Exp::Bits64(if concrete_bit(*bits, bit)? { B64::BIT_ONE } else { B64::BIT_ZERO })),
        Val::Symbolic(sym) => Ok(Exp::Extract(bit, bit, Box::new(Exp::Var(*sym)))),
        value => Err(ExecError::Type(format!("isla_init_mask vm bit {:?}", value), info)),
    }
}

fn bool_bit_exp(cond: Exp<Sym>) -> Exp<Sym> {
    Exp::Ite(Box::new(cond), Box::new(Exp::Bits64(B64::BIT_ONE)), Box::new(Exp::Bits64(B64::BIT_ZERO)))
}

fn bits_nonzero_exp<B: BV>(bits: &Val<B>, high: u32, low: u32, info: SourceLoc) -> Result<Exp<Sym>, ExecError> {
    if high < low {
        return Ok(Exp::Bool(false));
    }
    let width = high - low + 1;
    let slice = if high == low {
        symbolic_bit(bits, low, info)?
    } else {
        Exp::Extract(high, low, Box::new(smt_value(bits, info)?))
    };
    Ok(Exp::Neq(Box::new(slice), Box::new(smt_zeros(i128::from(width)))))
}

fn bits_eq_u64<B: BV>(
    bits: &Val<B>,
    expected: u64,
    width: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Exp<Sym>, ExecError> {
    let actual_width = length_bits(bits, solver, info)?;
    if actual_width != width {
        return Err(ExecError::Type(format!("bits_eq_u64 width {} != {}", actual_width, width), info));
    }
    Ok(Exp::Eq(Box::new(smt_value(bits, info)?), Box::new(bits64(expected, width))))
}

fn fixed_rounding_incr_for_shift<B: BV>(
    vec_elem: &Val<B>,
    shift: u32,
    rounding_mode: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Exp<Sym>, ExecError> {
    if shift == 0 {
        return Ok(Exp::Bits64(B64::BIT_ZERO));
    }

    let round_bit = symbolic_bit(vec_elem, shift - 1, info)?;
    let sticky_before_round = if shift == 1 {
        Exp::Bits64(B64::BIT_ZERO)
    } else {
        bool_bit_exp(bits_nonzero_exp(vec_elem, shift - 2, 0, info)?)
    };
    let sticky_through_round = bool_bit_exp(bits_nonzero_exp(vec_elem, shift - 1, 0, info)?);
    let next_bit = symbolic_bit(vec_elem, shift, info)?;

    let rnu = round_bit.clone();
    let rne =
        Exp::Bvand(Box::new(round_bit), Box::new(Exp::Bvor(Box::new(sticky_before_round), Box::new(next_bit.clone()))));
    let rtz = Exp::Bits64(B64::BIT_ZERO);
    let rod = Exp::Bvand(Box::new(Exp::Bvnot(Box::new(next_bit))), Box::new(sticky_through_round));

    Ok(Exp::Ite(
        Box::new(bits_eq_u64(rounding_mode, 0, 2, solver, info)?),
        Box::new(rnu),
        Box::new(Exp::Ite(
            Box::new(bits_eq_u64(rounding_mode, 1, 2, solver, info)?),
            Box::new(rne),
            Box::new(Exp::Ite(Box::new(bits_eq_u64(rounding_mode, 2, 2, solver, info)?), Box::new(rtz), Box::new(rod))),
        )),
    ))
}

fn concrete_low_nonzero<B: BV>(bits: B, high: u32) -> Result<bool, ExecError> {
    for bit in 0..=high {
        if concrete_bit(bits, bit)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn fixed_rounding_incr_concrete<B: BV>(vec_elem: B, shift: i128, rounding_mode: B) -> Result<Val<B>, ExecError> {
    if shift < 0 || shift >= i128::from(vec_elem.len()) {
        return Err(ExecError::Overflow);
    }
    if shift == 0 {
        return Ok(Val::Bits(B::BIT_ZERO));
    }

    let shift = u32::try_from(shift).map_err(|_| ExecError::Overflow)?;
    let increment = match rounding_mode.unsigned() {
        0 => concrete_bit(vec_elem, shift - 1)?,
        1 => {
            concrete_bit(vec_elem, shift - 1)?
                && ((shift != 1 && concrete_low_nonzero(vec_elem, shift - 2)?) || concrete_bit(vec_elem, shift)?)
        }
        2 => false,
        3 => !concrete_bit(vec_elem, shift)? && concrete_low_nonzero(vec_elem, shift - 1)?,
        _ => return Err(ExecError::Overflow),
    };

    Ok(Val::Bits(if increment { B::BIT_ONE } else { B::BIT_ZERO }))
}

fn isla_fixed_rounding_incr_internal<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if args.len() != 3 {
        return Err(ExecError::Type(
            format!("isla_fixed_rounding_incr expected 3 arguments, got {}", args.len()),
            info,
        ));
    }

    let vec_elem = expect_bits_arg(args[0].clone(), "isla_fixed_rounding_incr vec_elem", solver, info)?;
    let shift_amount = concretize_proven_i128(args[1].clone(), solver, info)?;
    let rounding_mode = expect_bits_arg(args[2].clone(), "isla_fixed_rounding_incr rounding_mode", solver, info)?;
    let len = length_bits(&vec_elem, solver, info)?;
    if len == 0 {
        return Err(ExecError::Type("isla_fixed_rounding_incr empty vec_elem".to_string(), info));
    }

    if let (Val::Bits(vec_elem_bits), Some(shift), Val::Bits(rounding_mode_bits)) =
        (&vec_elem, concrete_i128_arg(&shift_amount), &rounding_mode)
    {
        return fixed_rounding_incr_concrete(*vec_elem_bits, shift, *rounding_mode_bits);
    }

    let shift_exp = int_exp_128(&shift_amount, solver, "isla_fixed_rounding_incr shift_amount", info)?;
    solver.add(Def::Assert(Exp::Bvsge(Box::new(shift_exp.clone()), Box::new(smt_i128(0)))));
    solver.add(Def::Assert(Exp::Bvslt(Box::new(shift_exp.clone()), Box::new(smt_i128(i128::from(len))))));

    let mut exp = Exp::Bits64(B64::BIT_ZERO);
    for shift in (0..len).rev() {
        exp = Exp::Ite(
            Box::new(Exp::Eq(Box::new(shift_exp.clone()), Box::new(smt_i128(i128::from(shift))))),
            Box::new(fixed_rounding_incr_for_shift(&vec_elem, shift, &rounding_mode, solver, info)?),
            Box::new(exp),
        );
    }

    solver.define_const(exp, info).into()
}

fn isla_fixed_rounding_incr<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    isla_fixed_rounding_incr_internal(args, solver, info)
}

fn isla_init_mask_internal<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if args.len() != 5 {
        return Err(ExecError::Type(format!("isla_init_mask expected 5 arguments, got {}", args.len()), info));
    }

    let num_elem = concrete_i128_arg(&args[0]);
    let start_element = concrete_i128_arg(&args[1]);
    let end_element = concrete_i128_arg(&args[2]);
    let real_num_elem = concrete_i128_arg(&args[3]);
    let vm_val = expect_bits_arg(args[4].clone(), "isla_init_mask vm", solver, info)?;
    let len = length_bits(&vm_val, solver, info)?;

    if let Some(num_elem) = num_elem {
        if num_elem < 0 || num_elem as u32 != len {
            return Err(ExecError::Type(format!("isla_init_mask num_elem {} != mask length {}", num_elem, len), info));
        }
    }

    if len == 0 {
        return Ok(Val::Bits(B::zeros(0)));
    }

    if let (Some(start_element), Some(end_element), Some(real_num_elem), Val::Bits(vm_bits)) =
        (start_element, end_element, real_num_elem, &vm_val)
    {
        let mut bits = vec![false; len as usize];
        for i in 0..len {
            let index = i128::from(i);
            bits[i as usize] =
                start_element <= index && index <= end_element && index < real_num_elem && concrete_bit(*vm_bits, i)?;
        }

        if len <= B::MAX_WIDTH {
            let mut value = B::zeros(len);
            for (i, bit) in bits.iter().enumerate() {
                if *bit {
                    value = value.set_slice(i as u32, B::BIT_ONE);
                }
            }
            return Ok(Val::Bits(value));
        }

        return solver.define_const(Exp::Bits(bits), info).into();
    }

    let start_element = int_exp_128(&args[1], solver, "isla_init_mask start", info)?;
    let end_element = int_exp_128(&args[2], solver, "isla_init_mask end", info)?;
    let real_num_elem = int_exp_128(&args[3], solver, "isla_init_mask real_num_elem", info)?;

    let mut exp = None;
    for i in (0..len).rev() {
        let index = smt_i128(i128::from(i));
        let active = Exp::And(
            Box::new(Exp::And(
                Box::new(Exp::Bvsle(Box::new(start_element.clone()), Box::new(index.clone()))),
                Box::new(Exp::Bvsle(Box::new(index.clone()), Box::new(end_element.clone()))),
            )),
            Box::new(Exp::And(
                Box::new(Exp::Bvslt(Box::new(index), Box::new(real_num_elem.clone()))),
                Box::new(Exp::Eq(Box::new(symbolic_bit(&vm_val, i, info)?), Box::new(Exp::Bits64(B64::BIT_ONE)))),
            )),
        );
        let bit = Exp::Ite(Box::new(active), Box::new(Exp::Bits64(B64::BIT_ONE)), Box::new(Exp::Bits64(B64::BIT_ZERO)));
        exp = Some(match exp {
            Some(acc) => Exp::Concat(Box::new(acc), Box::new(bit)),
            None => bit,
        });
    }

    solver.define_const(exp.expect("non-empty mask expression"), info).into()
}

fn isla_init_mask<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    isla_init_mask_internal(args, solver, info)
}

fn isla_mask_from_low_bits_internal<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if args.len() != 4 && args.len() != 5 {
        return Err(ExecError::Type(
            format!("isla_mask_from_low_bits expected 4 or 5 arguments, got {}", args.len()),
            info,
        ));
    }

    let num_elem_concrete = concrete_i128_arg(&args[0]);
    let num_elem = int_exp_128(&args[0], solver, "isla_mask_from_low_bits num_elem", info)?;
    let vm = expect_bits_arg(args[1].clone(), "isla_mask_from_low_bits vm", solver, info)?;
    let fill = expect_bits_arg(args[2].clone(), "isla_mask_from_low_bits fill", solver, info)?;
    let source = expect_bits_arg(args[3].clone(), "isla_mask_from_low_bits source", solver, info)?;
    let source_len = length_bits(&source, solver, info)?;
    let len = if args.len() == 5 {
        let width_template = expect_bits_arg(args[4].clone(), "isla_mask_from_low_bits width_template", solver, info)?;
        length_bits(&width_template, solver, info)?
    } else if let Some(num_elem) = num_elem_concrete {
        if num_elem < 0 {
            return Err(ExecError::Type(
                format!("isla_mask_from_low_bits num_elem {} out of width {}", num_elem, source_len),
                info,
            ));
        }
        u32::try_from(num_elem).map_err(|_| ExecError::Overflow)?
    } else {
        source_len
    };

    if length_bits(&vm, solver, info)? != 1 {
        return Err(ExecError::Type("isla_mask_from_low_bits vm must be one bit".to_string(), info));
    }
    if length_bits(&fill, solver, info)? != 1 {
        return Err(ExecError::Type("isla_mask_from_low_bits fill must be one bit".to_string(), info));
    }
    if len == 0 {
        return Ok(Val::Bits(B::zeros(0)));
    }

    if source_len < len {
        return Err(ExecError::Type(
            format!("isla_mask_from_low_bits source width {} < result width {}", source_len, len),
            info,
        ));
    }

    if let (Some(num_elem), Val::Bits(vm_bits), Val::Bits(fill_bits), Val::Bits(source_bits)) =
        (num_elem_concrete, &vm, &fill, &source)
    {
        if num_elem < 0 || num_elem > i128::from(len) {
            return Err(ExecError::Type(
                format!("isla_mask_from_low_bits num_elem {} out of width {}", num_elem, len),
                info,
            ));
        }
        let fill_is_one = concrete_bit(*fill_bits, 0)?;
        let vm_enabled = concrete_bit(*vm_bits, 0)?;
        let mut bits = B::zeros(len);
        for i in 0..len {
            let use_fill = vm_enabled || i128::from(i) >= num_elem;
            let bit_is_one = if use_fill { fill_is_one } else { concrete_bit(*source_bits, i)? };
            if bit_is_one {
                bits = bits.set_slice(i, B::BIT_ONE);
            }
        }
        return Ok(Val::Bits(bits));
    }

    solver.add(Def::Assert(Exp::Bvsge(Box::new(num_elem.clone()), Box::new(smt_i128(0)))));
    solver.add(Def::Assert(Exp::Bvsle(Box::new(num_elem.clone()), Box::new(smt_i128(i128::from(len))))));

    let vm_enabled = Exp::Eq(Box::new(symbolic_bit(&vm, 0, info)?), Box::new(Exp::Bits64(B64::BIT_ONE)));
    let fill_bit = symbolic_bit(&fill, 0, info)?;

    let mut exp = None;
    for i in (0..len).rev() {
        let outside_low_bits = Exp::Bvsle(Box::new(num_elem.clone()), Box::new(smt_i128(i128::from(i))));
        let use_fill = Exp::Or(Box::new(vm_enabled.clone()), Box::new(outside_low_bits));
        let bit = Exp::Ite(Box::new(use_fill), Box::new(fill_bit.clone()), Box::new(symbolic_bit(&source, i, info)?));
        exp = Some(match exp {
            Some(acc) => Exp::Concat(Box::new(acc), Box::new(bit)),
            None => bit,
        });
    }

    solver.define_const(exp.expect("non-empty mask expression"), info).into()
}

fn isla_mask_from_low_bits<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    isla_mask_from_low_bits_internal(args, solver, info)
}

enum Condition {
    Concrete(bool),
    Symbolic(Exp<Sym>),
}

fn mask_bit_condition<B: BV>(
    mask: &Val<B>,
    bit: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Condition, ExecError> {
    match mask {
        Val::Bits(bits) => Ok(Condition::Concrete(concrete_bit(*bits, bit)?)),
        Val::Symbolic(_) => Ok(Condition::Symbolic(Exp::Eq(
            Box::new(symbolic_bit(mask, bit, info)?),
            Box::new(Exp::Bits64(B64::BIT_ONE)),
        ))),
        Val::MixedBits(_) => {
            let symbolic = replace_mixed_bits(mask.clone(), solver, info)?;
            mask_bit_condition(&symbolic, bit, solver, info)
        }
        value => Err(ExecError::Type(format!("isla mask bit condition {:?}", value), info)),
    }
}

fn select_value<B: BV>(
    condition: Condition,
    true_value: &Val<B>,
    false_value: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match condition {
        Condition::Concrete(true) => Ok(true_value.clone()),
        Condition::Concrete(false) => Ok(false_value.clone()),
        Condition::Symbolic(condition) => solver
            .define_const(
                Exp::Ite(
                    Box::new(condition),
                    Box::new(smt_value(true_value, info)?),
                    Box::new(smt_value(false_value, info)?),
                ),
                info,
            )
            .into(),
    }
}

fn expect_vector_arg<B: BV>(value: Val<B>, name: &str, info: SourceLoc) -> Result<Vec<Val<B>>, ExecError> {
    match value {
        Val::Vector(values) => Ok(values),
        value => Err(ExecError::Type(format!("{} {:?}", name, value), info)),
    }
}

fn expect_concrete_len<B: BV>(
    value: Val<B>,
    name: &str,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<usize, ExecError> {
    let value = concretize_proven_i128(value, solver, info)?;
    panic_if_negative_concretized_nat(name, &value);
    match value {
        Val::I128(value) => usize::try_from(value).map_err(|_| ExecError::Overflow),
        Val::I64(value) => usize::try_from(value).map_err(|_| ExecError::Overflow),
        value => Err(ExecError::Type(format!("{} must be concrete, got {:?}", name, value), info)),
    }
}

fn bitvec_value_count(width: u32) -> Option<usize> {
    if width >= usize::BITS {
        None
    } else {
        Some(1usize << width)
    }
}

fn bitvec_index_in_range_exp<B: BV>(
    index: &Val<B>,
    valid_len: usize,
    index_width: u32,
    info: SourceLoc,
) -> Result<Exp<Sym>, ExecError> {
    if valid_len == 0 {
        return Ok(Exp::Bool(false));
    }
    if let Some(value_count) = bitvec_value_count(index_width) {
        if valid_len >= value_count {
            return Ok(Exp::Bool(true));
        }
    }
    let valid_len = u64::try_from(valid_len).map_err(|_| ExecError::Overflow)?;
    Ok(Exp::Bvult(Box::new(smt_value(index, info)?), Box::new(smt_u64_width(valid_len, index_width))))
}

fn vector_array_access_or_default_exp<B: BV>(
    valid_len: usize,
    value_exps: &[Exp<Sym>],
    index: &Val<B>,
    element_width: u32,
    default: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Exp<Sym>, ExecError> {
    let index_width = length_bits(index, solver, info)?;
    if index_width == 0 {
        return Err(ExecError::Type("isla_vector_access_or_default index must be non-empty".to_string(), info));
    }
    if element_width == 0 {
        return smt_value(default, info);
    }

    let store_len = bitvec_value_count(index_width).map(|value_count| min(valid_len, value_count)).unwrap_or(valid_len);
    let array =
        solver.declare_const(Ty::Array(Box::new(Ty::BitVec(index_width)), Box::new(Ty::BitVec(element_width))), info);
    let mut array_exp = Exp::Var(array);
    for (i, value_exp) in value_exps.iter().take(store_len).enumerate() {
        let i = u64::try_from(i).map_err(|_| ExecError::Overflow)?;
        array_exp =
            Exp::Store(Box::new(array_exp), Box::new(smt_u64_width(i, index_width)), Box::new(value_exp.clone()));
    }

    let selected = Exp::Select(Box::new(array_exp), Box::new(smt_value(index, info)?));
    Ok(Exp::Ite(
        Box::new(bitvec_index_in_range_exp(index, valid_len, index_width, info)?),
        Box::new(selected),
        Box::new(smt_value(default, info)?),
    ))
}

fn isla_vector_access_or_default_internal<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if args.len() != 4 {
        return Err(ExecError::Type(
            format!("isla_vector_access_or_default expected 4 arguments, got {}", args.len()),
            info,
        ));
    }

    let valid_len = expect_concrete_len(args[0].clone(), "isla_vector_access_or_default valid_len", solver, info)?;
    let values = expect_vector_arg(args[1].clone(), "isla_vector_access_or_default vector", info)?;
    let index = expect_bits_arg(args[2].clone(), "isla_vector_access_or_default index", solver, info)?;
    let default = expect_bits_arg(args[3].clone(), "isla_vector_access_or_default default", solver, info)?;

    if valid_len > values.len() {
        return Err(ExecError::Type(
            format!("isla_vector_access_or_default valid_len {} > vector length {}", valid_len, values.len()),
            info,
        ));
    }

    let default_len = length_bits(&default, solver, info)?;
    let mut value_exps = Vec::with_capacity(valid_len);
    for value in values.iter().take(valid_len) {
        let value_bits = expect_bits_arg(value.clone(), "isla_vector_access_or_default element", solver, info)?;
        let value_len = length_bits(&value_bits, solver, info)?;
        if value_len != default_len {
            return Err(ExecError::Type(
                format!("isla_vector_access_or_default element width {} != default width {}", value_len, default_len),
                info,
            ));
        }
        value_exps.push(smt_value(&value_bits, info)?);
    }

    if let Val::Bits(bits) = index {
        let index = bits.unsigned();
        if index >= 0 {
            if let Ok(index) = usize::try_from(index) {
                if index < valid_len {
                    return Ok(values[index].clone());
                }
            }
        }
        return Ok(default);
    }

    if valid_len == 0 || default_len == 0 {
        return Ok(default);
    }

    let index_width = length_bits(&index, solver, info)?;
    let exp = vector_array_access_or_default_exp(valid_len, &value_exps, &index, default_len, &default, solver, info)?;
    debug_assert!(index_width > 0);
    solver.define_const(exp, info).into()
}

fn isla_vector_access_or_default<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    isla_vector_access_or_default_internal(args, solver, info)
}

fn isla_vector_select_internal<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if args.len() != 3 {
        return Err(ExecError::Type(format!("isla_vector_select expected 3 arguments, got {}", args.len()), info));
    }

    let mask = expect_bits_arg(args[0].clone(), "isla_vector_select mask", solver, info)?;
    let false_values = expect_vector_arg(args[1].clone(), "isla_vector_select false vector", info)?;
    let true_values = expect_vector_arg(args[2].clone(), "isla_vector_select true vector", info)?;
    let len = length_bits(&mask, solver, info)? as usize;

    if false_values.len() != len || true_values.len() != len {
        return Err(ExecError::Type(
            format!(
                "isla_vector_select length mismatch mask={} false={} true={}",
                len,
                false_values.len(),
                true_values.len()
            ),
            info,
        ));
    }

    let mut result = Vec::with_capacity(len);
    for i in 0..len {
        result.push(select_value(
            mask_bit_condition(&mask, i as u32, solver, info)?,
            &true_values[i],
            &false_values[i],
            solver,
            info,
        )?);
    }

    Ok(Val::Vector(result))
}

fn isla_vector_select<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    isla_vector_select_internal(args, solver, info)
}

fn isla_mux2_internal<B: BV>(
    selector: Val<B>,
    false_value: Val<B>,
    true_value: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let selector = expect_bits_arg(selector, "isla_mux2 selector", solver, info)?;
    let false_value = expect_bits_arg(false_value, "isla_mux2 false value", solver, info)?;
    let true_value = expect_bits_arg(true_value, "isla_mux2 true value", solver, info)?;

    if length_bits(&selector, solver, info)? != 1 {
        return Err(ExecError::Type("isla_mux2 selector must be bits(1)".to_string(), info));
    }

    let false_len = length_bits(&false_value, solver, info)?;
    let true_len = length_bits(&true_value, solver, info)?;
    if false_len != true_len {
        return Err(ExecError::Type(format!("isla_mux2 length mismatch false={} true={}", false_len, true_len), info));
    }

    select_value(mask_bit_condition(&selector, 0, solver, info)?, &true_value, &false_value, solver, info)
}

fn isla_mux2<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if args.len() != 3 {
        return Err(ExecError::Type(format!("isla_mux2 expected 3 arguments, got {}", args.len()), info));
    }

    isla_mux2_internal(args[0].clone(), args[1].clone(), args[2].clone(), solver, info)
}

fn active_body_condition<B: BV>(
    index: u32,
    start_element: &Val<B>,
    end_element: &Val<B>,
    real_num_elem: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Condition, ExecError> {
    if let (Some(start_element), Some(end_element), Some(real_num_elem)) =
        (concrete_i128_arg(start_element), concrete_i128_arg(end_element), concrete_i128_arg(real_num_elem))
    {
        let index = i128::from(index);
        return Ok(Condition::Concrete(start_element <= index && index <= end_element && index < real_num_elem));
    }

    let index = smt_i128(i128::from(index));
    Ok(Condition::Symbolic(Exp::And(
        Box::new(Exp::And(
            Box::new(Exp::Bvsle(
                Box::new(int_exp_128(start_element, solver, "isla_masktypei_result start", info)?),
                Box::new(index.clone()),
            )),
            Box::new(Exp::Bvsle(
                Box::new(index.clone()),
                Box::new(int_exp_128(end_element, solver, "isla_masktypei_result end", info)?),
            )),
        )),
        Box::new(Exp::Bvslt(
            Box::new(index),
            Box::new(int_exp_128(real_num_elem, solver, "isla_masktypei_result real_num_elem", info)?),
        )),
    )))
}

fn isla_masktypei_result_internal<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if args.len() != 8 {
        return Err(ExecError::Type(format!("isla_masktypei_result expected 8 arguments, got {}", args.len()), info));
    }

    let num_elem = concrete_i128_arg(&args[0]);
    let vm_val = expect_bits_arg(args[4].clone(), "isla_masktypei_result vm", solver, info)?;
    let imm_val = expect_bits_arg(args[5].clone(), "isla_masktypei_result imm", solver, info)?;
    let vs2_val = expect_vector_arg(args[6].clone(), "isla_masktypei_result vs2", info)?;
    let vd_val = expect_vector_arg(args[7].clone(), "isla_masktypei_result vd", info)?;
    let len = length_bits(&vm_val, solver, info)? as usize;

    if let Some(num_elem) = num_elem {
        if num_elem < 0 || num_elem as usize != len {
            return Err(ExecError::Type(
                format!("isla_masktypei_result num_elem {} != mask length {}", num_elem, len),
                info,
            ));
        }
    }
    if vs2_val.len() != len || vd_val.len() != len {
        return Err(ExecError::Type(
            format!("isla_masktypei_result length mismatch mask={} vs2={} vd={}", len, vs2_val.len(), vd_val.len()),
            info,
        ));
    }

    let mut result = Vec::with_capacity(len);
    for i in 0..len {
        let body = active_body_condition(i as u32, &args[1], &args[2], &args[3], solver, info)?;
        let body_value = match body {
            Condition::Concrete(false) => vd_val[i].clone(),
            Condition::Concrete(true) => {
                select_value(mask_bit_condition(&vm_val, i as u32, solver, info)?, &imm_val, &vs2_val[i], solver, info)?
            }
            condition @ Condition::Symbolic(_) => {
                let merged = select_value(
                    mask_bit_condition(&vm_val, i as u32, solver, info)?,
                    &imm_val,
                    &vs2_val[i],
                    solver,
                    info,
                )?;
                select_value(condition, &merged, &vd_val[i], solver, info)?
            }
        };
        result.push(body_value);
    }

    Ok(Val::Vector(result))
}

fn isla_masktypei_result<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    isla_masktypei_result_internal(args, solver, info)
}

fn isla_masktypev_result_internal<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if args.len() != 8 {
        return Err(ExecError::Type(format!("isla_masktypev_result expected 8 arguments, got {}", args.len()), info));
    }

    let num_elem = concrete_i128_arg(&args[0]);
    let vm_val = expect_bits_arg(args[4].clone(), "isla_masktypev_result vm", solver, info)?;
    let vs1_val = expect_vector_arg(args[5].clone(), "isla_masktypev_result vs1", info)?;
    let vs2_val = expect_vector_arg(args[6].clone(), "isla_masktypev_result vs2", info)?;
    let vd_val = expect_vector_arg(args[7].clone(), "isla_masktypev_result vd", info)?;
    let len = length_bits(&vm_val, solver, info)? as usize;

    if let Some(num_elem) = num_elem {
        if num_elem < 0 || num_elem as usize != len {
            return Err(ExecError::Type(
                format!("isla_masktypev_result num_elem {} != mask length {}", num_elem, len),
                info,
            ));
        }
    }
    if vs1_val.len() != len || vs2_val.len() != len || vd_val.len() != len {
        return Err(ExecError::Type(
            format!(
                "isla_masktypev_result length mismatch mask={} vs1={} vs2={} vd={}",
                len,
                vs1_val.len(),
                vs2_val.len(),
                vd_val.len()
            ),
            info,
        ));
    }

    let mut result = Vec::with_capacity(len);
    for i in 0..len {
        let body = active_body_condition(i as u32, &args[1], &args[2], &args[3], solver, info)?;
        let body_value = match body {
            Condition::Concrete(false) => vd_val[i].clone(),
            Condition::Concrete(true) => select_value(
                mask_bit_condition(&vm_val, i as u32, solver, info)?,
                &vs1_val[i],
                &vs2_val[i],
                solver,
                info,
            )?,
            condition @ Condition::Symbolic(_) => {
                let merged = select_value(
                    mask_bit_condition(&vm_val, i as u32, solver, info)?,
                    &vs1_val[i],
                    &vs2_val[i],
                    solver,
                    info,
                )?;
                select_value(condition, &merged, &vd_val[i], solver, info)?
            }
        };
        result.push(body_value);
    }

    Ok(Val::Vector(result))
}

fn isla_masktypev_result<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    isla_masktypev_result_internal(args, solver, info)
}

fn pack_vreg_bits<B: BV>(elements: &[Val<B>], solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let mut concrete = Some(B::zeros(0));
    let mut exp = None;

    for element in elements.iter().rev() {
        let element_bits = expect_bits_arg(element.clone(), "isla_pack_vreg element", solver, info)?;
        if let (Some(acc), Val::Bits(bits)) = (concrete, &element_bits) {
            concrete = acc.append(*bits);
        } else {
            concrete = None;
        }

        let element_exp = smt_value(&element_bits, info)?;
        exp = Some(match exp {
            Some(acc) => Exp::Concat(Box::new(acc), Box::new(element_exp)),
            None => element_exp,
        });
    }

    match concrete {
        Some(bits) => Ok(Val::Bits(bits)),
        None => solver.define_const(exp.expect("packed vreg has at least one element"), info).into(),
    }
}

fn pack_vreg_values<B: BV>(
    sew: u32,
    vlen: u32,
    values: Vec<Val<B>>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if !matches!(sew, 8 | 16 | 32 | 64) || vlen == 0 || vlen % sew != 0 {
        return Err(ExecError::Type(format!("isla_pack_vreg invalid SEW/VLEN {}/{}", sew, vlen), info));
    }

    let elem_per_reg = (vlen / sew) as usize;
    let zero = Val::Bits(B::zeros(sew));
    let mut registers = Vec::with_capacity(8);

    for reg in 0..8 {
        let mut elements = Vec::with_capacity(elem_per_reg);
        for i in 0..elem_per_reg {
            let index = reg * elem_per_reg + i;
            elements.push(values.get(index).cloned().unwrap_or_else(|| zero.clone()));
        }
        registers.push(pack_vreg_bits(&elements, solver, info)?);
    }

    Ok(Val::Vector(registers))
}

fn isla_pack_vreg_internal<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if args.len() != 3 {
        return Err(ExecError::Type(format!("isla_pack_vreg expected 3 arguments, got {}", args.len()), info));
    }

    let sew = u32::try_from(expect_i128_arg(&args[0], "isla_pack_vreg SEW", solver, info)?)
        .map_err(|_| ExecError::Overflow)?;
    let vlen = u32::try_from(expect_i128_arg(&args[1], "isla_pack_vreg VLEN", solver, info)?)
        .map_err(|_| ExecError::Overflow)?;
    let values = expect_vector_arg(args[2].clone(), "isla_pack_vreg vector", info)?;

    pack_vreg_values(sew, vlen, values, solver, info)
}

fn isla_pack_vreg<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    isla_pack_vreg_internal(args, solver, info)
}

fn choice<B: BV>(xs: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match xs {
        Val::List(mut xs) if !xs.is_empty() => {
            let x = xs.pop().unwrap();
            ite_choice(&x, &xs, solver, info)
        }
        _ => Err(ExecError::Type(format!("choice {:?}", &xs), info)),
    }
}

fn read_mem<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory().read(args[0].clone(), args[2].clone(), args[3].clone(), solver, false, ReadOpts::default())
}

fn read_mem_ifetch<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory().read(args[0].clone(), args[2].clone(), args[3].clone(), solver, false, ReadOpts::ifetch())
}

fn read_mem_exclusive<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory().read(args[0].clone(), args[2].clone(), args[3].clone(), solver, false, ReadOpts::exclusive())
}

fn read_memt<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory().read(args[0].clone(), args[1].clone(), args[2].clone(), solver, true, ReadOpts::default())
}

fn bad_read<B: BV>(_: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Err(ExecError::BadRead("spec-defined bad read"))
}

fn write_mem<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory_mut().write(args[0].clone(), args[2].clone(), args[4].clone(), solver, None, WriteOpts::default())
}

fn write_mem_exclusive<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory_mut().write(args[0].clone(), args[2].clone(), args[4].clone(), solver, None, WriteOpts::exclusive())
}

fn write_memt<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory_mut().write(
        args[0].clone(),
        args[1].clone(),
        args[3].clone(),
        solver,
        Some(args[4].clone()),
        WriteOpts::default(),
    )
}

fn write_tag<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory_mut().write_tag(args[0].clone(), args[1].clone(), args[2].clone(), solver)
}

fn bad_write<B: BV>(_: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Err(ExecError::BadWrite("spec-defined bad write"))
}

fn cycle_count<B: BV>(_: Val<B>, solver: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    solver.cycle_count();
    Ok(Val::Unit)
}

fn get_cycle_count<B: BV>(_: Val<B>, solver: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::I128(solver.get_cycle_count()))
}

fn get_verbosity<B: BV>(_: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Bits(B::zeros(64)))
}

fn sleeping<B: BV>(_: Val<B>, _solver: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    // let sym = solver.fresh();
    // solver.add(Def::DeclareConst(sym, Ty::Bool));
    // solver.add_event(Event::Sleeping(sym));
    // Ok(Val::Symbolic(sym))
    Ok(Val::Bool(false))
}

fn wakeup_request<B: BV>(_: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn sleep_request<B: BV>(_: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn branch_announce<B: BV>(
    _: Val<B>,
    target: Val<B>,
    solver: &mut Solver<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    solver.add_event(Event::Branch { address: target });
    Ok(Val::Unit)
}

fn address_announce<B: BV>(
    _: Val<B>,
    address: Val<B>,
    solver: &mut Solver<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    solver.add_event(Event::AddressAnnounce { address });
    Ok(Val::Unit)
}

fn synchronize_registers<B: BV>(
    _: Vec<Val<B>>,
    _: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.regs_mut().synchronize();
    Ok(Val::Unit)
}

fn elf_entry<B: BV>(
    _: Vec<Val<B>>,
    _: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match frame.lets().get(&ELF_ENTRY) {
        Some(UVal::Init(value)) => Ok(value.clone()),
        _ => Err(ExecError::NoElfEntry),
    }
}

fn monomorphize<B: BV>(val: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(val)
}

fn mark_register<B: BV>(r: Val<B>, mark: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (r, mark) {
        (Val::Ref(r), Val::String(mark)) => {
            solver.add_event(Event::MarkReg { regs: vec![r], mark });
            Ok(Val::Unit)
        }
        (r, mark) => Err(ExecError::Type(format!("mark_register {:?} {:?}", &r, &mark), info)),
    }
}

fn mark_register_pair_internal<B: BV>(
    r1: Val<B>,
    r2: Val<B>,
    mark: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match (r1, r2, mark) {
        (Val::Ref(r1), Val::Ref(r2), Val::String(mark)) => {
            solver.add_event(Event::MarkReg { regs: vec![r1, r2], mark });
            Ok(Val::Unit)
        }
        (r1, r2, mark) => Err(ExecError::Type(format!("mark_register_pair {:?} {:?} {:?}", &r1, &r2, &mark), info)),
    }
}

fn mark_register_pair<B: BV>(
    mut args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if args.len() == 3 {
        let mark = args.pop().unwrap();
        let r2 = args.pop().unwrap();
        let r1 = args.pop().unwrap();
        mark_register_pair_internal(r1, r2, mark, solver, info)
    } else {
        Err(ExecError::Type("Incorrect number of arguments for mark_register_pair".to_string(), info))
    }
}

fn align_bits<B: BV>(
    bv: Val<B>,
    alignment: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let bv_len = length_bits(&bv, solver, info)?;
    match (bv, alignment) {
        // Fast path for small bitvectors with power of two alignments
        (Val::Symbolic(bv), Val::I128(alignment)) if (bv_len <= 64) & ((alignment & (alignment - 1)) == 0) => {
            let mask = !B::new((alignment as u64) - 1, bv_len);
            solver.define_const(Exp::Bvand(Box::new(Exp::Var(bv)), Box::new(smt_sbits(mask))), info).into()
        }
        (bv, alignment) => {
            let x = sail_unsigned(bv, solver, info)?;
            let aligned_x = mult_int(alignment.clone(), udiv_int(x, alignment, solver, info)?, solver, info)?;
            get_slice_int_internal(Val::I128(bv_len as i128), aligned_x, Val::I128(0), solver, info)
        }
    }
}

/// Implement count leading zeros (clz) in the SMT solver as a binary
/// search, splitting on the midpoint of the bitvector.
fn smt_clz<B: BV>(bv: Sym, len: u32, solver: &mut Solver<B>, info: SourceLoc) -> Sym {
    if len == 1 {
        solver.define_const(
            Exp::Ite(
                Box::new(Exp::Eq(Box::new(Exp::Var(bv)), Box::new(smt_zeros(1)))),
                Box::new(smt_i128(1)),
                Box::new(smt_i128(0)),
            ),
            info,
        )
    } else {
        let low_len = len / 2;
        let top_len = len - low_len;

        let top = solver.define_const(Exp::Extract(len - 1, low_len, Box::new(Exp::Var(bv))), info);
        let low = solver.define_const(Exp::Extract(low_len - 1, 0, Box::new(Exp::Var(bv))), info);

        let top_bits_are_zero = Exp::Eq(Box::new(Exp::Var(top)), Box::new(smt_zeros(top_len as i128)));

        let top_clz = smt_clz(top, top_len, solver, info);
        let low_clz = smt_clz(low, low_len, solver, info);

        solver.define_const(
            Exp::Ite(
                Box::new(top_bits_are_zero),
                Box::new(Exp::Bvadd(Box::new(smt_i128(top_len as i128)), Box::new(Exp::Var(low_clz)))),
                Box::new(Exp::Var(top_clz)),
            ),
            info,
        )
    }
}

/// 在 SMT solver 中实现 count trailing zeros (ctz)，从低半部分开始递归检查。
fn smt_ctz<B: BV>(bv: Sym, len: u32, solver: &mut Solver<B>, info: SourceLoc) -> Sym {
    if len == 1 {
        solver.define_const(
            Exp::Ite(
                Box::new(Exp::Eq(Box::new(Exp::Var(bv)), Box::new(smt_zeros(1)))),
                Box::new(smt_i128(1)),
                Box::new(smt_i128(0)),
            ),
            info,
        )
    } else {
        let low_len = len / 2;
        let top_len = len - low_len;

        let top = solver.define_const(Exp::Extract(len - 1, low_len, Box::new(Exp::Var(bv))), info);
        let low = solver.define_const(Exp::Extract(low_len - 1, 0, Box::new(Exp::Var(bv))), info);

        let low_bits_are_zero = Exp::Eq(Box::new(Exp::Var(low)), Box::new(smt_zeros(low_len as i128)));

        let top_ctz = smt_ctz(top, top_len, solver, info);
        let low_ctz = smt_ctz(low, low_len, solver, info);

        solver.define_const(
            Exp::Ite(
                Box::new(low_bits_are_zero),
                Box::new(Exp::Bvadd(Box::new(smt_i128(low_len as i128)), Box::new(Exp::Var(top_ctz)))),
                Box::new(Exp::Var(low_ctz)),
            ),
            info,
        )
    }
}

fn count_leading_zeros<B: BV>(bv: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let bv = replace_mixed_bits(bv, solver, info)?;
    match bv {
        Val::Bits(bv) => Ok(Val::I128(bv.leading_zeros() as i128)),
        Val::Symbolic(bv) => {
            if let Some(len) = solver.length(bv) {
                smt_clz(bv, len, solver, info).into()
            } else {
                Err(ExecError::Type("count_leading_zeros (solver could not determine length)".to_string(), info))
            }
        }
        _ => Err(ExecError::Type(format!("count_leading_zeros {:?}", &bv), info)),
    }
}

fn count_trailing_zeros<B: BV>(bv: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let bv = replace_mixed_bits(bv, solver, info)?;
    match bv {
        Val::Bits(bv) => Ok(Val::I128(bv.trailing_zeros() as i128)),
        Val::Symbolic(bv) => {
            if let Some(len) = solver.length(bv) {
                smt_ctz(bv, len, solver, info).into()
            } else {
                Err(ExecError::Type("count_trailing_zeros (solver could not determine length)".to_string(), info))
            }
        }
        _ => Err(ExecError::Type(format!("count_trailing_zeros {:?}", &bv), info)),
    }
}

/// 生成 carry-less multiplication 的 SMT 表达式，直接用位运算构造符号路径。
fn smt_carryless_mul<V>(a: Sym, b: Sym, len: u32, solver: &mut Solver<impl BV>, info: SourceLoc) -> Sym {
    let result_len = len * 2;

    // Zero extend b to result_len
    let b_extended = solver.define_const(Exp::ZeroExtend(len, Box::new(Exp::Var(b))), info);

    // Initialize result to zeros
    let mut result = solver.define_const(smt_zeros(result_len as i128), info);

    // For each bit position i in a:
    // - Extract bit a[i]
    // - If a[i] = 1, XOR (b << i) into result
    // - If a[i] = 0, XOR nothing (zeros)
    //
    // We implement this without branching by using:
    //   term = (a[i] * (b << i))  where * is bitwise AND with replicated bit
    //   result = result ^ term
    for i in 0..len {
        // Extract bit i from a
        let bit_i = solver.define_const(
            Exp::Extract(0, 0, Box::new(Exp::Bvlshr(Box::new(Exp::Var(a)), Box::new(smt_u64_width(i as u64, len))))),
            info,
        );

        // Replicate bit_i to result_len bits
        // If bit_i = 1, mask = all_ones, else mask = all_zeros
        let mask = solver.define_const(
            Exp::Ite(
                Box::new(Exp::Eq(Box::new(Exp::Var(bit_i)), Box::new(bits64(1, 1)))),
                Box::new(smt_ones(result_len as i128)),
                Box::new(smt_zeros(result_len as i128)),
            ),
            info,
        );

        // Shift b_extended by i positions
        let shifted = solver.define_const(
            Exp::Bvshl(Box::new(Exp::Var(b_extended)), Box::new(smt_u64_width(i as u64, result_len))),
            info,
        );

        // Mask the shifted value: if bit_i = 1, we get (b << i), else 0
        let term = solver.define_const(Exp::Bvand(Box::new(Exp::Var(shifted)), Box::new(Exp::Var(mask))), info);

        // XOR into result
        result = solver.define_const(Exp::Bvxor(Box::new(Exp::Var(result)), Box::new(Exp::Var(term))), info);
    }

    result
}

/// Carry-less multiplication (GF(2) polynomial multiplication).
/// For two bitvectors a and b, computes the polynomial product in GF(2).
/// This is used by the RISC-V CLMUL instruction.
fn carryless_mul<B: BV>(a: Val<B>, b: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (replace_mixed_bits(a, solver, info)?, replace_mixed_bits(b, solver, info)?) {
        (Val::Bits(a), Val::Bits(b)) => {
            // Concrete case: compute carry-less multiplication directly
            let len = a.len();
            assert_eq!(len, b.len(), "carryless_mul: operands must have same length");
            let result_len = len * 2;

            // Check if result fits in BV::MAX_WIDTH
            if result_len > B::MAX_WIDTH {
                // Fallback to symbolic computation for large results
                let a_sym = solver.define_const(smt_sbits(a), info);
                let b_sym = solver.define_const(smt_sbits(b), info);
                return smt_carryless_mul::<Sym>(a_sym, b_sym, len, solver, info).into();
            }

            // Perform carry-less multiplication using BV operations
            let mut result = B::zeros(result_len);
            for i in 0..len {
                // Extract bit i from a
                let bit_set = (a.shiftr(i as i128).lower_u64() & 1) == 1;
                if bit_set {
                    // Shift b by i and XOR into result
                    let b_extended = b.zero_extend(result_len);
                    let shifted = b_extended.shiftl(i as i128);
                    result = result ^ shifted;
                }
            }
            Ok(Val::Bits(result))
        }
        (Val::Symbolic(a), Val::Symbolic(b)) => {
            // Symbolic case: generate SMT expression without branching
            if let Some(len) = solver.length(a) {
                smt_carryless_mul::<Sym>(a, b, len, solver, info).into()
            } else {
                Err(ExecError::Type("carryless_mul (solver could not determine length)".to_string(), info))
            }
        }
        (Val::Bits(a), Val::Symbolic(b)) => {
            // Mixed case: if a is all zeros, result is zeros
            if a.is_zero() {
                let len = a.len() * 2;
                Ok(Val::Symbolic(solver.define_const(smt_zeros(len as i128), info)))
            } else if a.to_vec().iter().filter(|&&x| x).count() == 1 {
                // If a has only one bit set, we just need to shift b
                let bit_pos = a.trailing_zeros();
                let operand_len = a.len();
                let result_len = operand_len * 2;
                let b_extended = solver.define_const(Exp::ZeroExtend(operand_len, Box::new(Exp::Var(b))), info);
                let result = solver.define_const(
                    Exp::Bvshl(Box::new(Exp::Var(b_extended)), Box::new(smt_u64_width(bit_pos as u64, result_len))),
                    info,
                );
                Ok(Val::Symbolic(result))
            } else {
                // Fallback: treat both as symbolic
                if let Some(len) = solver.length(b) {
                    let a_sym = solver.define_const(smt_sbits(a), info);
                    smt_carryless_mul::<Sym>(a_sym, b, len, solver, info).into()
                } else {
                    Err(ExecError::Type("carryless_mul (solver could not determine length)".to_string(), info))
                }
            }
        }
        (Val::Symbolic(a), Val::Bits(b)) => {
            // Mixed case (symmetric to above)
            if b.is_zero() {
                let len = b.len() * 2;
                Ok(Val::Symbolic(solver.define_const(smt_zeros(len as i128), info)))
            } else if b.to_vec().iter().filter(|&&x| x).count() == 1 {
                let bit_pos = b.trailing_zeros();
                let operand_len = b.len();
                let result_len = operand_len * 2;
                let a_extended = solver.define_const(Exp::ZeroExtend(operand_len, Box::new(Exp::Var(a))), info);
                let result = solver.define_const(
                    Exp::Bvshl(Box::new(Exp::Var(a_extended)), Box::new(smt_u64_width(bit_pos as u64, result_len))),
                    info,
                );
                Ok(Val::Symbolic(result))
            } else {
                if let Some(len) = solver.length(a) {
                    let b_sym = solver.define_const(smt_sbits(b), info);
                    smt_carryless_mul::<Sym>(a, b_sym, len, solver, info).into()
                } else {
                    Err(ExecError::Type("carryless_mul (solver could not determine length)".to_string(), info))
                }
            }
        }
        _ => Err(ExecError::Type("carryless_mul: invalid value types".to_string(), info)),
    }
}

fn isla_clmul<B: BV>(rs1: Val<B>, rs2: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let xlen = length_bits(&replace_mixed_bits(rs1.clone(), solver, info)?, solver, info)?;
    let product = carryless_mul(rs1, rs2, solver, info)?;
    subrange_internal(product, Val::I128(i128::from(xlen - 1)), Val::I128(0), solver, info)
}

fn isla_clmulh<B: BV>(rs1: Val<B>, rs2: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let xlen = length_bits(&replace_mixed_bits(rs1.clone(), solver, info)?, solver, info)?;
    let product = carryless_mul(rs1, rs2, solver, info)?;
    subrange_internal(product, Val::I128(i128::from(2 * xlen - 1)), Val::I128(i128::from(xlen)), solver, info)
}

fn isla_clmulr<B: BV>(rs1: Val<B>, rs2: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let xlen = length_bits(&replace_mixed_bits(rs1.clone(), solver, info)?, solver, info)?;
    let product = carryless_mul(rs1, rs2, solver, info)?;
    subrange_internal(product, Val::I128(i128::from(2 * xlen - 2)), Val::I128(i128::from(xlen - 1)), solver, info)
}

fn isla_carryless_mul<B: BV>(
    rs1: Val<B>,
    rs2: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    carryless_mul(rs1, rs2, solver, info)
}

fn isla_carryless_mulr<B: BV>(
    rs1: Val<B>,
    rs2: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    isla_clmulr(rs1, rs2, solver, info)
}

fn isla_count_ones<B: BV>(bits: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let bits = replace_mixed_bits(bits, solver, info)?;
    let len = length_bits(&bits, solver, info)?;

    match bits {
        Val::Bits(bits) => Ok(Val::I128(bits.to_vec().iter().filter(|bit| **bit).count() as i128)),
        bits @ (Val::Symbolic(_) | Val::MixedBits(_)) => {
            let bits_exp = smt_value(&bits, info)?;
            let mut count = smt_i128(0);
            for bit in 0..len {
                let bit_value = Exp::ZeroExtend(127, Box::new(Exp::Extract(bit, bit, Box::new(bits_exp.clone()))));
                count = Exp::Bvadd(Box::new(count), Box::new(bit_value));
            }
            solver.define_const(count, info).into()
        }
        value => Err(ExecError::Type(format!("isla_count_ones {:?}", value), info)),
    }
}

fn isla_cpop_width<B: BV>(
    bits: Val<B>,
    count_width: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let bits = replace_mixed_bits(bits, solver, info)?;
    let result_width = length_bits(&bits, solver, info)?;
    if count_width > result_width || result_width == 0 {
        return Err(ExecError::Type(format!("isla_cpop invalid widths {}/{}", count_width, result_width), info));
    }

    match bits {
        Val::Bits(bits) => {
            let count =
                bits.slice(0, count_width).ok_or(ExecError::Overflow)?.to_vec().iter().filter(|bit| **bit).count();
            Ok(Val::Bits(B::new(count as u64, result_width)))
        }
        bits @ (Val::Symbolic(_) | Val::MixedBits(_)) => {
            let bits_exp = smt_value(&bits, info)?;
            let mut count = smt_zeros(i128::from(result_width));
            for bit in 0..count_width {
                let bit_value =
                    Exp::ZeroExtend(result_width - 1, Box::new(Exp::Extract(bit, bit, Box::new(bits_exp.clone()))));
                count = Exp::Bvadd(Box::new(count), Box::new(bit_value));
            }
            solver.define_const(count, info).into()
        }
        value => Err(ExecError::Type(format!("isla_cpop {:?}", value), info)),
    }
}

fn isla_cpop<B: BV>(bits: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let count_width = length_bits(&replace_mixed_bits(bits.clone(), solver, info)?, solver, info)?;
    isla_cpop_width(bits, count_width, solver, info)
}

fn isla_cpopw<B: BV>(bits: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    isla_cpop_width(bits, 32, solver, info)
}

fn isla_brev8<B: BV>(bits: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let bits = replace_mixed_bits(bits, solver, info)?;
    let len = length_bits(&bits, solver, info)?;
    if len % 8 != 0 {
        return Err(ExecError::Type(format!("isla_brev8 invalid width {}", len), info));
    }

    match bits {
        Val::Bits(bits) => {
            let mut result = B::zeros(len);
            for byte in 0..(len / 8) {
                for bit in 0..8 {
                    let input_bit = byte * 8 + (7 - bit);
                    let output_bit = byte * 8 + bit;
                    result = result.set_slice(output_bit, bits.slice(input_bit, 1).ok_or(ExecError::Overflow)?);
                }
            }
            Ok(Val::Bits(result))
        }
        Val::Symbolic(_) | Val::MixedBits(_) if len == 0 => Ok(Val::Bits(B::zeros(0))),
        bits @ (Val::Symbolic(_) | Val::MixedBits(_)) => {
            let bits_exp = smt_value(&bits, info)?;
            let mut result = None;
            for output_bit in (0..len).rev() {
                let byte = output_bit / 8;
                let bit = output_bit % 8;
                let input_bit = byte * 8 + (7 - bit);
                let bit_exp = Exp::Extract(input_bit, input_bit, Box::new(bits_exp.clone()));
                result = Some(match result {
                    Some(acc) => Exp::Concat(Box::new(acc), Box::new(bit_exp)),
                    None => bit_exp,
                });
            }
            solver.define_const(result.expect("non-empty brev8 expression"), info).into()
        }
        value => Err(ExecError::Type(format!("isla_brev8 {:?}", value), info)),
    }
}

fn isla_rev8<B: BV>(bits: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let bits = replace_mixed_bits(bits, solver, info)?;
    let len = length_bits(&bits, solver, info)?;
    if len % 8 != 0 {
        return Err(ExecError::Type(format!("isla_rev8 invalid width {}", len), info));
    }

    match bits {
        Val::Bits(bits) => {
            let mut result = B::zeros(len);
            let byte_count = len / 8;
            for output_byte in 0..byte_count {
                let input_byte = byte_count - output_byte - 1;
                let byte = bits.slice(input_byte * 8, 8).ok_or(ExecError::Overflow)?;
                result = result.set_slice(output_byte * 8, byte);
            }
            Ok(Val::Bits(result))
        }
        Val::Symbolic(_) | Val::MixedBits(_) if len == 0 => Ok(Val::Bits(B::zeros(0))),
        bits @ (Val::Symbolic(_) | Val::MixedBits(_)) => {
            let bits_exp = smt_value(&bits, info)?;
            let byte_count = len / 8;
            let mut result = None;
            for output_byte in (0..byte_count).rev() {
                let input_byte = byte_count - output_byte - 1;
                let low = input_byte * 8;
                let byte_exp = Exp::Extract(low + 7, low, Box::new(bits_exp.clone()));
                result = Some(match result {
                    Some(acc) => Exp::Concat(Box::new(acc), Box::new(byte_exp)),
                    None => byte_exp,
                });
            }
            solver.define_const(result.expect("non-empty rev8 expression"), info).into()
        }
        value => Err(ExecError::Type(format!("isla_rev8 {:?}", value), info)),
    }
}

fn isla_vector_rev8<B: BV>(input: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match input {
        Val::Vector(values) => values
            .into_iter()
            .map(|value| isla_rev8(value, solver, info))
            .collect::<Result<Vec<_>, _>>()
            .map(Val::Vector),
        value => Err(ExecError::Type(format!("isla_vector_rev8 {:?}", value), info)),
    }
}

fn xperm_concrete<B: BV>(rs1: B, rs2: B, elem_width: u32) -> Result<B, ExecError> {
    let xlen = rs1.len();
    if rs2.len() != xlen || xlen % elem_width != 0 || xlen > B::MAX_WIDTH {
        return Err(ExecError::Type(format!("isla_xperm{}: invalid operand widths", elem_width), SourceLoc::unknown()));
    }

    let elem_count = xlen / elem_width;
    let mut result = B::zeros(xlen);
    for i in 0..elem_count {
        let index = rs2.slice(i * elem_width, elem_width).ok_or(ExecError::Overflow)?.lower_u64() as u32;
        let element = if index < elem_count {
            rs1.slice(index * elem_width, elem_width).ok_or(ExecError::Overflow)?
        } else {
            B::zeros(elem_width)
        };
        result = result.set_slice(i * elem_width, element);
    }

    Ok(result)
}

fn xperm_lookup_exp(rs1: Exp<Sym>, index: Exp<Sym>, elem_width: u32, elem_count: u32) -> Exp<Sym> {
    let mut result = smt_zeros(elem_width as i128);
    for element_index in (0..elem_count).rev() {
        let low = element_index * elem_width;
        let high = low + elem_width - 1;
        result = Exp::Ite(
            Box::new(Exp::Eq(
                Box::new(index.clone()),
                Box::new(Exp::Bits64(B64::new(element_index as u64, elem_width))),
            )),
            Box::new(Exp::Extract(high, low, Box::new(rs1.clone()))),
            Box::new(result),
        );
    }
    result
}

fn xperm_symbolic_exp(rs1: Exp<Sym>, rs2: Exp<Sym>, xlen: u32, elem_width: u32) -> Exp<Sym> {
    let elem_count = xlen / elem_width;
    let mut result = xperm_lookup_exp(
        rs1.clone(),
        Exp::Extract(xlen - 1, xlen - elem_width, Box::new(rs2.clone())),
        elem_width,
        elem_count,
    );

    for element_index in (0..(elem_count - 1)).rev() {
        let low = element_index * elem_width;
        let high = low + elem_width - 1;
        let element =
            xperm_lookup_exp(rs1.clone(), Exp::Extract(high, low, Box::new(rs2.clone())), elem_width, elem_count);
        result = Exp::Concat(Box::new(result), Box::new(element));
    }

    result
}

fn xperm<B: BV>(
    rs1: Val<B>,
    rs2: Val<B>,
    elem_width: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let rs1 = replace_mixed_bits(rs1, solver, info)?;
    let rs2 = replace_mixed_bits(rs2, solver, info)?;
    let xlen = length_bits(&rs1, solver, info)?;
    if length_bits(&rs2, solver, info)? != xlen || xlen % elem_width != 0 {
        return Err(ExecError::Type(format!("isla_xperm{} {:?}", elem_width, (&rs1, &rs2)), info));
    }

    match (rs1, rs2) {
        (Val::Bits(rs1), Val::Bits(rs2)) => Ok(Val::Bits(xperm_concrete(rs1, rs2, elem_width)?)),
        (rs1, rs2) => {
            let rs1_exp = smt_value(&rs1, info)?;
            let rs2_exp = smt_value(&rs2, info)?;
            solver.define_const(xperm_symbolic_exp(rs1_exp, rs2_exp, xlen, elem_width), info).into()
        }
    }
}

fn isla_xperm4<B: BV>(rs1: Val<B>, rs2: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    xperm(rs1, rs2, 4, solver, info)
}

fn isla_xperm8<B: BV>(rs1: Val<B>, rs2: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    xperm(rs1, rs2, 8, solver, info)
}

fn primop_ite<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    ite(&args[0], &args[1], &args[2], solver, info)
}

pub fn unary_primops<B: BV>() -> HashMap<String, Unary<B>> {
    let mut primops = HashMap::new();
    primops.insert("%i64->%i".to_string(), i64_to_i128 as Unary<B>);
    primops.insert("%i->%i64".to_string(), i128_to_i64 as Unary<B>);
    primops.insert("%string->%i".to_string(), string_to_i128 as Unary<B>);
    primops.insert("bit_to_bool".to_string(), bit_to_bool as Unary<B>);
    primops.insert("isla_bool_to_bit".to_string(), bool_to_bit as Unary<B>);
    primops.insert("assume".to_string(), assume as Unary<B>);
    primops.insert("not".to_string(), not_bool as Unary<B>);
    primops.insert("neg_int".to_string(), neg_int as Unary<B>);
    primops.insert("abs_int".to_string(), abs_int as Unary<B>);
    primops.insert("pow2".to_string(), pow2 as Unary<B>);
    primops.insert("not_bits".to_string(), not_bits as Unary<B>);
    primops.insert("length".to_string(), length as Unary<B>);
    primops.insert("zeros".to_string(), zeros as Unary<B>);
    primops.insert("ones".to_string(), ones as Unary<B>);
    primops.insert("sail_unsigned".to_string(), sail_unsigned as Unary<B>);
    primops.insert("sail_signed".to_string(), sail_signed as Unary<B>);
    primops.insert("sail_putchar".to_string(), putchar as Unary<B>);
    primops.insert("print".to_string(), print as Unary<B>);
    primops.insert("prerr".to_string(), prerr as Unary<B>);
    primops.insert("print_endline".to_string(), print_endline as Unary<B>);
    primops.insert("prerr_endline".to_string(), prerr_endline as Unary<B>);
    primops.insert("count_leading_zeros".to_string(), count_leading_zeros as Unary<B>);
    primops.insert("count_trailing_zeros".to_string(), count_trailing_zeros as Unary<B>);
    primops.insert("isla_count_ones".to_string(), isla_count_ones as Unary<B>);
    primops.insert("isla_cpop".to_string(), isla_cpop as Unary<B>);
    primops.insert("isla_cpopw".to_string(), isla_cpopw as Unary<B>);
    primops.insert("isla_brev8".to_string(), isla_brev8 as Unary<B>);
    primops.insert("isla_rev8".to_string(), isla_rev8 as Unary<B>);
    primops.insert("isla_vector_rev8".to_string(), isla_vector_rev8 as Unary<B>);
    primops.insert("undefined_bitvector".to_string(), undefined_bitvector as Unary<B>);
    primops.insert("undefined_bit".to_string(), undefined_bit as Unary<B>);
    primops.insert("undefined_bool".to_string(), undefined_bool as Unary<B>);
    primops.insert("undefined_int".to_string(), undefined_int as Unary<B>);
    primops.insert("undefined_nat".to_string(), undefined_nat as Unary<B>);
    primops.insert("undefined_unit".to_string(), undefined_unit as Unary<B>);
    primops.insert("undefined_string".to_string(), undefined_string as Unary<B>);
    primops.insert("one_if".to_string(), one_if as Unary<B>);
    primops.insert("zero_if".to_string(), zero_if as Unary<B>);
    primops.insert("internal_pick".to_string(), choice as Unary<B>);
    primops.insert("bad_read".to_string(), bad_read as Unary<B>);
    primops.insert("bad_write".to_string(), bad_write as Unary<B>);
    primops.insert("hex_str".to_string(), hex_str as Unary<B>);
    primops.insert("dec_str".to_string(), dec_str as Unary<B>);
    primops.insert("string_length".to_string(), string_length as Unary<B>);
    primops.insert("string_of_bits".to_string(), string_of_bits as Unary<B>);
    primops.insert("decimal_string_of_bits".to_string(), decimal_string_of_bits as Unary<B>);
    primops.insert("string_of_int".to_string(), string_of_int as Unary<B>);
    primops.insert("cycle_count".to_string(), cycle_count as Unary<B>);
    primops.insert("get_cycle_count".to_string(), get_cycle_count as Unary<B>);
    primops.insert("sail_get_verbosity".to_string(), get_verbosity as Unary<B>);
    primops.insert("sleeping".to_string(), sleeping as Unary<B>);
    primops.insert("sleep_request".to_string(), sleep_request as Unary<B>);
    primops.insert("wakeup_request".to_string(), wakeup_request as Unary<B>);
    primops.insert("monomorphize".to_string(), monomorphize as Unary<B>);
    primops.extend(float::unary_primops());
    primops
}

pub fn binary_primops<B: BV>() -> HashMap<String, Binary<B>> {
    let mut primops = HashMap::new();
    primops.insert("optimistic_assert".to_string(), optimistic_assert as Binary<B>);
    primops.insert("pessimistic_assert".to_string(), pessimistic_assert as Binary<B>);
    primops.insert("and_bool".to_string(), and_bool as Binary<B>);
    primops.insert("strict_and_bool".to_string(), and_bool as Binary<B>);
    primops.insert("or_bool".to_string(), or_bool as Binary<B>);
    primops.insert("strict_or_bool".to_string(), or_bool as Binary<B>);
    primops.insert("eq_int".to_string(), eq_int as Binary<B>);
    primops.insert("eq_bool".to_string(), eq_bool as Binary<B>);
    primops.insert("lteq".to_string(), lteq_int as Binary<B>);
    primops.insert("gteq".to_string(), gteq_int as Binary<B>);
    primops.insert("lt".to_string(), lt_int as Binary<B>);
    primops.insert("gt".to_string(), gt_int as Binary<B>);
    primops.insert("add_int".to_string(), add_int as Binary<B>);
    primops.insert("sub_int".to_string(), sub_int as Binary<B>);
    primops.insert("sub_nat".to_string(), sub_nat as Binary<B>);
    primops.insert("mult_int".to_string(), mult_int as Binary<B>);
    primops.insert("tdiv_int".to_string(), tdiv_int as Binary<B>);
    primops.insert("tmod_int".to_string(), tmod_int as Binary<B>);
    primops.insert("ediv_int".to_string(), ediv_int as Binary<B>);
    primops.insert("emod_int".to_string(), emod_int as Binary<B>);
    primops.insert("pow_int".to_string(), pow_int as Binary<B>);
    primops.insert("shl_int".to_string(), shl_int as Binary<B>);
    primops.insert("shr_int".to_string(), shr_int as Binary<B>);
    primops.insert("shl_mach_int".to_string(), shl_mach_int as Binary<B>);
    primops.insert("shr_mach_int".to_string(), shr_mach_int as Binary<B>);
    primops.insert("max_int".to_string(), max_int as Binary<B>);
    primops.insert("min_int".to_string(), min_int as Binary<B>);
    primops.insert("eq_bit".to_string(), eq_bits as Binary<B>);
    primops.insert("eq_bits".to_string(), eq_bits as Binary<B>);
    primops.insert("neq_bits".to_string(), neq_bits as Binary<B>);
    primops.insert("xor_bits".to_string(), xor_bits as Binary<B>);
    primops.insert("or_bits".to_string(), or_bits as Binary<B>);
    primops.insert("and_bits".to_string(), and_bits as Binary<B>);
    primops.insert("add_bits".to_string(), add_bits as Binary<B>);
    primops.insert("sub_bits".to_string(), sub_bits as Binary<B>);
    primops.insert("add_bits_int".to_string(), add_bits_int as Binary<B>);
    primops.insert("sub_bits_int".to_string(), sub_bits_int as Binary<B>);
    primops.insert("align_bits".to_string(), align_bits as Binary<B>);
    primops.insert("undefined_range".to_string(), undefined_range as Binary<B>);
    primops.insert("zero_extend".to_string(), zero_extend as Binary<B>);
    primops.insert("sign_extend".to_string(), sign_extend as Binary<B>);
    primops.insert("sail_truncate".to_string(), sail_truncate as Binary<B>);
    primops.insert("sail_truncateLSB".to_string(), sail_truncate_lsb as Binary<B>);
    primops.insert("replicate_bits".to_string(), replicate_bits as Binary<B>);
    primops.insert("shiftr".to_string(), shiftr as Binary<B>);
    primops.insert("shiftl".to_string(), shiftl as Binary<B>);
    primops.insert("arith_shiftr".to_string(), arith_shiftr as Binary<B>);
    primops.insert("shift_bits_right".to_string(), shift_bits_right as Binary<B>);
    primops.insert("shift_bits_left".to_string(), shift_bits_left as Binary<B>);
    primops.insert("append".to_string(), append as Binary<B>);
    primops.insert("append_64".to_string(), append as Binary<B>);
    primops.insert("vector_access".to_string(), vector_access as Binary<B>);
    primops.insert("eq_anything".to_string(), eq_anything as Binary<B>);
    primops.insert("eq_string".to_string(), eq_string as Binary<B>);
    primops.insert("concat_str".to_string(), concat_str as Binary<B>);
    primops.insert("string_startswith".to_string(), string_startswith as Binary<B>);
    primops.insert("string_drop".to_string(), string_drop as Binary<B>);
    primops.insert("string_take".to_string(), string_take as Binary<B>);
    primops.insert("cons".to_string(), cons as Binary<B>);
    primops.insert("undefined_vector".to_string(), undefined_vector as Binary<B>);
    primops.insert("print_string".to_string(), print_string as Binary<B>);
    primops.insert("prerr_string".to_string(), prerr_string as Binary<B>);
    primops.insert("print_int".to_string(), print_int as Binary<B>);
    primops.insert("prerr_int".to_string(), prerr_int as Binary<B>);
    primops.insert("print_bits".to_string(), print_bits as Binary<B>);
    primops.insert("prerr_bits".to_string(), prerr_bits as Binary<B>);
    primops.insert("platform_branch_announce".to_string(), branch_announce as Binary<B>);
    primops.insert("branch_announce".to_string(), branch_announce as Binary<B>);
    primops.insert("address_announce".to_string(), address_announce as Binary<B>);
    primops.insert("mark_register".to_string(), mark_register as Binary<B>);
    primops.insert("vector_init".to_string(), vector_init as Binary<B>);
    primops.insert("carryless_mul".to_string(), carryless_mul as Binary<B>);
    primops.insert("isla_carryless_mul".to_string(), isla_carryless_mul as Binary<B>);
    primops.insert("isla_carryless_mulr".to_string(), isla_carryless_mulr as Binary<B>);
    primops.insert("isla_clmul".to_string(), isla_clmul as Binary<B>);
    primops.insert("isla_clmulh".to_string(), isla_clmulh as Binary<B>);
    primops.insert("isla_clmulr".to_string(), isla_clmulr as Binary<B>);
    primops.insert("isla_xperm4".to_string(), isla_xperm4 as Binary<B>);
    primops.insert("isla_xperm8".to_string(), isla_xperm8 as Binary<B>);
    primops.extend(float::binary_primops());
    primops
}

pub fn variadic_primops<B: BV>() -> HashMap<String, Variadic<B>> {
    let mut primops = HashMap::new();
    primops.insert("slice".to_string(), slice as Variadic<B>);
    primops.insert("vector_subrange".to_string(), subrange as Variadic<B>);
    primops.insert("vector_update".to_string(), vector_update as Variadic<B>);
    primops.insert("vector_update_subrange".to_string(), vector_update_subrange as Variadic<B>);
    primops.insert("bitvector_update".to_string(), bitvector_update as Variadic<B>);
    primops.insert("set_slice".to_string(), set_slice as Variadic<B>);
    primops.insert("get_slice_int".to_string(), get_slice_int as Variadic<B>);
    primops.insert("set_slice_int".to_string(), set_slice_int as Variadic<B>);
    primops.insert("platform_read_mem".to_string(), read_mem as Variadic<B>);
    primops.insert("platform_read_mem_ifetch".to_string(), read_mem_ifetch as Variadic<B>);
    primops.insert("platform_read_mem_exclusive".to_string(), read_mem_exclusive as Variadic<B>);
    primops.insert("platform_read_memt".to_string(), read_memt as Variadic<B>);
    primops.insert("platform_write_mem".to_string(), write_mem as Variadic<B>);
    primops.insert("platform_write_mem_exclusive".to_string(), write_mem_exclusive as Variadic<B>);
    primops.insert("platform_write_memt".to_string(), write_memt as Variadic<B>);
    primops.insert("platform_write_tag".to_string(), write_tag as Variadic<B>);
    primops.insert("platform_synchronize_registers".to_string(), synchronize_registers as Variadic<B>);
    primops.insert("platform_barrier".to_string(), unit_noop as Variadic<B>);
    primops.insert("elf_entry".to_string(), elf_entry as Variadic<B>);
    primops.insert("ite".to_string(), primop_ite as Variadic<B>);
    primops.insert("mark_register_pair".to_string(), mark_register_pair as Variadic<B>);
    primops.insert("isla_read_vreg".to_string(), isla_read_vreg as Variadic<B>);
    primops.insert("isla_init_mask".to_string(), isla_init_mask as Variadic<B>);
    primops.insert("isla_select_int".to_string(), isla_select_int as Variadic<B>);
    primops.insert("isla_fixed_rounding_incr".to_string(), isla_fixed_rounding_incr as Variadic<B>);
    primops.insert("isla_mask_from_low_bits".to_string(), isla_mask_from_low_bits as Variadic<B>);
    primops.insert("isla_vector_access_or_default".to_string(), isla_vector_access_or_default as Variadic<B>);
    primops.insert("isla_vector_select".to_string(), isla_vector_select as Variadic<B>);
    primops.insert("isla_mux2".to_string(), isla_mux2 as Variadic<B>);
    primops.insert("isla_masktypei_result".to_string(), isla_masktypei_result as Variadic<B>);
    primops.insert("isla_masktypev_result".to_string(), isla_masktypev_result as Variadic<B>);
    primops.insert("isla_pack_vreg".to_string(), isla_pack_vreg as Variadic<B>);
    // We explicitly don't handle anything real number related right now
    primops.insert("%string->%real".to_string(), unimplemented as Variadic<B>);
    primops.insert("neg_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("mult_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("sub_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("add_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("div_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("sqrt_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("abs_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("round_down".to_string(), unimplemented as Variadic<B>);
    primops.insert("round_up".to_string(), unimplemented as Variadic<B>);
    primops.insert("to_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("eq_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("lt_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("gt_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("lteq_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("gteq_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("real_power".to_string(), unimplemented as Variadic<B>);
    primops.insert("print_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("prerr_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("undefined_real".to_string(), unimplemented as Variadic<B>);
    primops.extend(float::variadic_primops());
    primops.extend(memory::variadic_primops());
    primops
}

pub struct Primops<B> {
    pub unary: HashMap<String, Unary<B>>,
    pub binary: HashMap<String, Binary<B>>,
    pub variadic: HashMap<String, Variadic<B>>,
    pub consts: HashMap<String, Reset<B>>,
}

impl<B: BV> Default for Primops<B> {
    fn default() -> Self {
        Primops {
            unary: unary_primops(),
            binary: binary_primops(),
            variadic: variadic_primops(),
            consts: HashMap::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b129::B129;
    use crate::bitvector::b64::B64;
    use crate::error::ExecError;
    use crate::ir::{BitsSegment, Val};
    use crate::smt::smtlib::Ty;
    use crate::smt::{Config, Context, SmtResult, Solver};
    use crate::source_loc::SourceLoc;

    #[test]
    fn symbolic_integer_compare_uses_asserted_bounds_without_picking_candidate() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let len = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert(Exp::Or(
            Box::new(Exp::Eq(Box::new(Exp::Var(len)), Box::new(smt_i128(1)))),
            Box::new(Exp::Or(
                Box::new(Exp::Eq(Box::new(Exp::Var(len)), Box::new(smt_i128(2)))),
                Box::new(Exp::Eq(Box::new(Exp::Var(len)), Box::new(smt_i128(4)))),
            )),
        ));

        assert_eq!(lt_int(Val::I128(0), Val::Symbolic(len), &mut solver, SourceLoc::unknown())?, Val::Bool(true));
        assert_eq!(lt_int(Val::Symbolic(len), Val::I128(0), &mut solver, SourceLoc::unknown())?, Val::Bool(false));
        assert_eq!(proven_symbolic_i128(len, &mut solver, SourceLoc::unknown())?, None);

        match eq_int(Val::Symbolic(len), Val::I128(2), &mut solver, SourceLoc::unknown())? {
            Val::Symbolic(_) => Ok(()),
            value => panic!("expected non-constant equality under one-of constraint, got {:?}", value),
        }
    }

    /// 模型法不再受候选常量集合限制：以前只枚举 0..=512 等值，超出范围或很大的负数
    /// 即使已经被路径约束钉死也证明不出来。
    #[test]
    fn proven_symbolic_i128_concretizes_values_outside_the_old_candidate_range() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let large = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        let negative = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        let narrow = solver.declare_const(Ty::BitVec(64), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(large), smt_i128(70_000));
        solver.assert_eq(Exp::Var(negative), smt_i128(-4_096));
        solver.assert_eq(Exp::Var(narrow), Exp::Bits64(B64::new(-7_i64 as u64, 64)));

        assert_eq!(proven_symbolic_i128(large, &mut solver, SourceLoc::unknown())?, Some(70_000));
        assert_eq!(proven_symbolic_i128(negative, &mut solver, SourceLoc::unknown())?, Some(-4_096));
        assert_eq!(proven_symbolic_i128(narrow, &mut solver, SourceLoc::unknown())?, Some(-7));

        Ok(())
    }

    /// 只要还存在第二个可行取值就必须保持符号量；完全没有约束的符号量同理。
    #[test]
    fn proven_symbolic_i128_keeps_values_that_are_not_pinned_down() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let two_valued = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        let free = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert(Exp::Or(
            Box::new(Exp::Eq(Box::new(Exp::Var(two_valued)), Box::new(smt_i128(70_000)))),
            Box::new(Exp::Eq(Box::new(Exp::Var(two_valued)), Box::new(smt_i128(70_001)))),
        ));

        assert_eq!(proven_symbolic_i128(two_valued, &mut solver, SourceLoc::unknown())?, None);
        assert_eq!(proven_symbolic_i128(free, &mut solver, SourceLoc::unknown())?, None);

        Ok(())
    }

    /// 证明不出唯一值时的查询次数必须是常数级：这正是逐 lane 的 `min`/`max` 会不会
    /// 把单路径预算耗光的关键。
    #[test]
    fn proven_symbolic_i128_uses_a_constant_number_of_queries() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let vs1 = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        let vs2 = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());

        crate::smt::reset_path_smt_stats();
        assert_eq!(proven_symbolic_i128(vs1, &mut solver, SourceLoc::unknown())?, None);
        let one_proof = crate::smt::path_smt_stats().calls;
        assert!(one_proof <= 4, "证明失败时用了 {} 次求解", one_proof);

        // max_int 会对两个参数各做一次具体化，逐 lane 调用时这里的常数就是路径预算的关键。
        crate::smt::reset_path_smt_stats();
        let _ = max_int(Val::Symbolic(vs1), Val::Symbolic(vs2), &mut solver, SourceLoc::unknown())?;
        let max_calls = crate::smt::path_smt_stats().calls;
        assert!(max_calls <= 8, "一次 max_int 用了 {} 次求解", max_calls);

        Ok(())
    }

    #[test]
    fn zeros_accepts_proven_symbolic_length() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let len = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(len), smt_i128(8));

        match zeros(Val::Symbolic(len), &mut solver, SourceLoc::unknown())? {
            Val::Bits(bits) => assert_eq!(bits, B64::zeros(8)),
            value => panic!("expected concrete zero bits, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn zeros_rejects_unconstrained_symbolic_length() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let len = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());

        let error = zeros(Val::Symbolic(len), &mut solver, SourceLoc::unknown()).expect_err("expected symbolic length");
        assert!(matches!(error, ExecError::SymbolicLength("zeros", _)));
    }

    #[test]
    #[should_panic(expected = "nat invariant violated in zeros")]
    fn zeros_panics_on_negative_proven_symbolic_length() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let len = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(len), smt_i128(-1));

        let _ = zeros(Val::Symbolic(len), &mut solver, SourceLoc::unknown());
    }

    #[test]
    fn ones_accepts_proven_symbolic_length() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let len = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(len), smt_i128(8));

        match ones(Val::Symbolic(len), &mut solver, SourceLoc::unknown())? {
            Val::Bits(bits) => assert_eq!(bits, B64::ones(8)),
            value => panic!("expected concrete one bits, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn ones_rejects_unconstrained_symbolic_length() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let len = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());

        let error = ones(Val::Symbolic(len), &mut solver, SourceLoc::unknown()).expect_err("expected symbolic length");
        assert!(matches!(error, ExecError::SymbolicLength("ones", _)));
    }

    #[test]
    #[should_panic(expected = "nat invariant violated in ones")]
    fn ones_panics_on_negative_proven_symbolic_length() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let len = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(len), smt_i128(-1));

        let _ = ones(Val::Symbolic(len), &mut solver, SourceLoc::unknown());
    }

    #[test]
    #[should_panic(expected = "nat invariant violated in pow2")]
    fn pow2_panics_on_negative_proven_symbolic_exponent() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let exponent = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(exponent), smt_i128(-1));

        let _ = pow2(Val::Symbolic(exponent), &mut solver, SourceLoc::unknown());
    }

    #[test]
    fn replicate_bits_accepts_proven_symbolic_count() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let count = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(count), smt_i128(3));

        match replicate_bits(Val::Bits(B64::new(0b10, 2)), Val::Symbolic(count), &mut solver, SourceLoc::unknown())? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(0b101010, 6)),
            value => panic!("expected concrete replicated bits, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn replicate_bits_accepts_symbolic_bits_with_proven_symbolic_count() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let bit = solver.declare_const(Ty::BitVec(1), SourceLoc::unknown());
        let count = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(count), smt_i128(8));

        match replicate_bits(Val::Symbolic(bit), Val::Symbolic(count), &mut solver, SourceLoc::unknown())? {
            Val::Symbolic(bits) => assert_eq!(solver.length(bits), Some(8)),
            value => panic!("expected symbolic replicated bits, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn replicate_bits_rejects_unconstrained_symbolic_count() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let count = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());

        let error =
            replicate_bits(Val::Bits(B64::new(0b10, 2)), Val::Symbolic(count), &mut solver, SourceLoc::unknown())
                .expect_err("expected symbolic count");
        assert!(matches!(error, ExecError::SymbolicLength("replicate_bits", _)));
    }

    #[test]
    #[should_panic(expected = "nat invariant violated in replicate_bits")]
    fn replicate_bits_panics_on_negative_proven_symbolic_count() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let count = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(count), smt_i128(-1));

        let _ = replicate_bits(Val::Bits(B64::new(0b10, 2)), Val::Symbolic(count), &mut solver, SourceLoc::unknown());
    }

    #[test]
    fn vector_init_accepts_proven_symbolic_length() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let len = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(len), smt_i128(3));

        match vector_init(Val::Symbolic(len), Val::Bits(B64::new(0b1010, 4)), &mut solver, SourceLoc::unknown())? {
            Val::Vector(values) => {
                assert_eq!(values.len(), 3);
                assert!(values.iter().all(|value| *value == Val::Bits(B64::new(0b1010, 4))));
            }
            value => panic!("expected concrete vector, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn vector_init_rejects_unconstrained_symbolic_length() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let len = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());

        let error = vector_init(Val::Symbolic(len), Val::Bits(B64::new(0b1010, 4)), &mut solver, SourceLoc::unknown())
            .expect_err("expected symbolic length");
        assert!(matches!(error, ExecError::SymbolicLength("vector_init", _)));
    }

    #[test]
    #[should_panic(expected = "nat invariant violated in vector_init")]
    fn vector_init_panics_on_negative_proven_symbolic_length() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let len = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(len), smt_i128(-1));

        let _ = vector_init(Val::Symbolic(len), Val::Bits(B64::new(0b1010, 4)), &mut solver, SourceLoc::unknown());
    }

    #[test]
    #[should_panic(expected = "nat invariant violated in subrange_internal")]
    fn subrange_panics_on_negative_proven_symbolic_bounds() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let high = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        let low = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(high), smt_i128(-1));
        solver.assert_eq(Exp::Var(low), smt_i128(-4));

        let _ = subrange_internal(
            Val::Bits(B64::new(0b1011_0010, 8)),
            Val::Symbolic(high),
            Val::Symbolic(low),
            &mut solver,
            SourceLoc::unknown(),
        );
    }

    #[test]
    fn subrange_accepts_proven_symbolic_bounds() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let high = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        let low = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(high), smt_i128(7));
        solver.assert_eq(Exp::Var(low), smt_i128(4));

        match subrange_internal(
            Val::Bits(B64::new(0b1011_0010, 8)),
            Val::Symbolic(high),
            Val::Symbolic(low),
            &mut solver,
            SourceLoc::unknown(),
        )? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(0b1011, 4)),
            value => panic!("expected concrete extracted bits, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn subrange_accepts_symbolic_bounds_with_proven_width() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let high = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        let low = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Bvsub(Box::new(Exp::Var(high)), Box::new(Exp::Var(low))), smt_i128(7));

        match subrange_internal(
            Val::Symbolic(solver.declare_const(Ty::BitVec(64), SourceLoc::unknown())),
            Val::Symbolic(high),
            Val::Symbolic(low),
            &mut solver,
            SourceLoc::unknown(),
        )? {
            Val::Symbolic(bits) => assert_eq!(solver.length(bits), Some(8)),
            value => panic!("expected symbolic extracted byte, got {:?}", value),
        }

        match subrange_internal(
            Val::Bits(B64::zeros(64)),
            Val::Symbolic(high),
            Val::Symbolic(low),
            &mut solver,
            SourceLoc::unknown(),
        )? {
            Val::Bits(bits) => assert_eq!(bits, B64::zeros(8)),
            value => panic!("expected concrete zero byte, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn i64_to_i128_accepts_bits_as_signed_i64() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);

        assert_eq!(i64_to_i128(Val::Bits(B64::new(u64::MAX, 64)), &mut solver, SourceLoc::unknown())?, Val::I128(-1));

        Ok(())
    }

    #[test]
    fn get_slice_int_accepts_proven_symbolic_length() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let len = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(len), smt_i128(8));

        match get_slice_int_internal(
            Val::Symbolic(len),
            Val::I128(0x1234),
            Val::I128(0),
            &mut solver,
            SourceLoc::unknown(),
        )? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(0x34, 8)),
            value => panic!("expected concrete get_slice_int result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    #[should_panic(expected = "nat invariant violated in get_slice_int")]
    fn get_slice_int_panics_on_negative_proven_symbolic_length() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let len = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(len), smt_i128(-1));

        let _ = get_slice_int_internal(
            Val::Symbolic(len),
            Val::I128(0x1234),
            Val::I128(0),
            &mut solver,
            SourceLoc::unknown(),
        );
    }

    #[test]
    #[should_panic(expected = "nat invariant violated in get_slice_int")]
    fn get_slice_int_panics_on_negative_concrete_length() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);

        let _ =
            get_slice_int_internal(Val::I128(-1), Val::I128(0x1234), Val::I128(0), &mut solver, SourceLoc::unknown());
    }

    #[test]
    #[should_panic(expected = "nat invariant violated in expect_usize_or_symbolic_bound test")]
    fn expect_usize_or_symbolic_bound_panics_on_negative_proven_symbolic_value() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let value = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(value), smt_i128(-1));

        let _ = expect_usize_or_symbolic_bound(
            &Val::Symbolic(value),
            8,
            "expect_usize_or_symbolic_bound test",
            &mut solver,
            SourceLoc::unknown(),
        );
    }

    #[test]
    fn extension_accepts_proven_symbolic_length() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let len = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(len), smt_i128(16));

        match zero_extend(Val::Bits(B64::new(0x12, 8)), Val::Symbolic(len), &mut solver, SourceLoc::unknown())? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(0x12, 16)),
            value => panic!("expected concrete zero_extend result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn extension_accepts_proven_symbolic_length_from_fallback_candidate() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B129>::new(&ctx);
        let len = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(len), smt_i128(65));

        match zero_extend(Val::Bits(B129::new(0x12, 8)), Val::Symbolic(len), &mut solver, SourceLoc::unknown())? {
            Val::Bits(bits) => assert_eq!(bits, B129::new(0x12, 65)),
            value => panic!("expected concrete zero_extend result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    #[should_panic(expected = "nat invariant violated in extension")]
    fn extension_panics_on_negative_proven_symbolic_length() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let len = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        solver.assert_eq(Exp::Var(len), smt_i128(-1));

        let _ = zero_extend(Val::Bits(B64::new(0x12, 8)), Val::Symbolic(len), &mut solver, SourceLoc::unknown());
    }

    #[test]
    fn isla_brev8_reverses_bits_inside_each_byte() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);

        match isla_brev8(Val::Bits(B64::new(0x8012, 16)), &mut solver, SourceLoc::unknown())? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(0x0148, 16)),
            value => panic!("expected concrete brev8 result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_rev8_reverses_byte_order() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);

        match isla_rev8(Val::Bits(B64::new(0x1234, 16)), &mut solver, SourceLoc::unknown())? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(0x3412, 16)),
            value => panic!("expected concrete rev8 result, got {:?}", value),
        }

        match isla_rev8(Val::Bits(B64::new(0x1122_3344_5566_7788, 64)), &mut solver, SourceLoc::unknown())? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(0x8877_6655_4433_2211, 64)),
            value => panic!("expected concrete rev8 result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_rev8_symbolic_path_preserves_width() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let bits = solver.declare_const(Ty::BitVec(64), SourceLoc::unknown());

        match isla_rev8(Val::Symbolic(bits), &mut solver, SourceLoc::unknown())? {
            Val::Symbolic(result) => assert_eq!(solver.length(result), Some(64)),
            value => panic!("expected symbolic rev8 result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_vector_rev8_maps_each_element() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let input = Val::Vector(vec![Val::Bits(B64::new(0x1122_3344, 32)), Val::Bits(B64::new(0xaabb_ccdd, 32))]);

        match isla_vector_rev8(input, &mut solver, SourceLoc::unknown())? {
            Val::Vector(values) => {
                assert_eq!(values[0], Val::Bits(B64::new(0x4433_2211, 32)));
                assert_eq!(values[1], Val::Bits(B64::new(0xddcc_bbaa, 32)));
            }
            value => panic!("expected vector rev8 result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_cpop_counts_full_register_or_low_word() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);

        match isla_count_ones(Val::Bits(B64::new(0xF0F1, 64)), &mut solver, SourceLoc::unknown())? {
            Val::I128(count) => assert_eq!(count, 9),
            value => panic!("expected concrete count_ones result, got {:?}", value),
        }

        match isla_cpop(Val::Bits(B64::new(0xF0F1, 64)), &mut solver, SourceLoc::unknown())? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(9, 64)),
            value => panic!("expected concrete cpop result, got {:?}", value),
        }

        match isla_cpopw(Val::Bits(B64::new(0xFFFF_FFFF_0000_F00F, 64)), &mut solver, SourceLoc::unknown())? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(8, 64)),
            value => panic!("expected concrete cpopw result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_cpop_symbolic_path_has_register_width() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let rs1 = solver.declare_const(Ty::BitVec(64), SourceLoc::unknown());

        match isla_count_ones(Val::Symbolic(rs1), &mut solver, SourceLoc::unknown())? {
            Val::Symbolic(result) => assert_eq!(solver.length(result), Some(128)),
            value => panic!("expected symbolic count_ones result, got {:?}", value),
        }

        match isla_cpop(Val::Symbolic(rs1), &mut solver, SourceLoc::unknown())? {
            Val::Symbolic(result) => assert_eq!(solver.length(result), Some(64)),
            value => panic!("expected symbolic cpop result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn count_trailing_zeros_symbolic_counts_from_low_bits() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let bits = solver.declare_const(Ty::BitVec(4), SourceLoc::unknown());

        let result = count_trailing_zeros(Val::Symbolic(bits), &mut solver, SourceLoc::unknown())?;
        let Val::Symbolic(result) = result else {
            panic!("expected symbolic trailing-zero count, got {:?}", result);
        };

        solver.assert_eq(Exp::Var(bits), Exp::Bits64(B64::new(0b0010, 4)));
        assert_eq!(
            solver.check_sat_with(&Exp::Neq(Box::new(Exp::Var(result)), Box::new(smt_i128(1))), SourceLoc::unknown()),
            SmtResult::Unsat
        );

        Ok(())
    }

    #[test]
    fn isla_clmul_variants_extract_expected_product_bits() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);

        match isla_carryless_mul(
            Val::Bits(B64::new(0b1011, 8)),
            Val::Bits(B64::new(0b0110, 8)),
            &mut solver,
            SourceLoc::unknown(),
        )? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(0b0011_1010, 16)),
            value => panic!("expected concrete carryless_mul result, got {:?}", value),
        }

        match isla_clmul(
            Val::Bits(B64::new(0b1011, 8)),
            Val::Bits(B64::new(0b0110, 8)),
            &mut solver,
            SourceLoc::unknown(),
        )? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(0b0011_1010, 8)),
            value => panic!("expected concrete clmul result, got {:?}", value),
        }

        match isla_clmulh(
            Val::Bits(B64::new(0x80, 8)),
            Val::Bits(B64::new(0x80, 8)),
            &mut solver,
            SourceLoc::unknown(),
        )? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(0x40, 8)),
            value => panic!("expected concrete clmulh result, got {:?}", value),
        }

        match isla_clmulr(
            Val::Bits(B64::new(0x80, 8)),
            Val::Bits(B64::new(0x80, 8)),
            &mut solver,
            SourceLoc::unknown(),
        )? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(0x80, 8)),
            value => panic!("expected concrete clmulr result, got {:?}", value),
        }

        match isla_carryless_mulr(
            Val::Bits(B64::new(0x80, 8)),
            Val::Bits(B64::new(0x80, 8)),
            &mut solver,
            SourceLoc::unknown(),
        )? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(0x80, 8)),
            value => panic!("expected concrete carryless_mulr result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_carryless_mul_symbolic_paths_have_double_width() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let rs1 = solver.declare_const(Ty::BitVec(8), SourceLoc::unknown());
        let rs2 = solver.declare_const(Ty::BitVec(8), SourceLoc::unknown());

        match isla_carryless_mul(Val::Symbolic(rs1), Val::Symbolic(rs2), &mut solver, SourceLoc::unknown())? {
            Val::Symbolic(product) => assert_eq!(solver.length(product), Some(16)),
            value => panic!("expected symbolic carryless_mul result, got {:?}", value),
        }

        match isla_carryless_mul(Val::Bits(B64::new(0b1000, 8)), Val::Symbolic(rs2), &mut solver, SourceLoc::unknown())?
        {
            Val::Symbolic(product) => assert_eq!(solver.length(product), Some(16)),
            value => panic!("expected mixed carryless_mul result, got {:?}", value),
        }

        match isla_carryless_mul(Val::Symbolic(rs1), Val::Bits(B64::new(0b1000, 8)), &mut solver, SourceLoc::unknown())?
        {
            Val::Symbolic(product) => assert_eq!(solver.length(product), Some(16)),
            value => panic!("expected mixed carryless_mul result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_xperm4_handles_concrete_operands() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);

        let rs1 = Val::Bits(B64::new(0xFEDC_BA98_7654_3210, 64));
        let rs2 = Val::Bits(B64::new(0x0123_4567_89AB_CDEF, 64));

        match isla_xperm4(rs1, rs2, &mut solver, SourceLoc::unknown())? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(0x0123_4567_89AB_CDEF, 64)),
            value => panic!("expected concrete xperm4 result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_xperm8_handles_concrete_operands() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);

        let rs1 = Val::Bits(B64::new(0x1122_3344_5566_7788, 64));
        let rs2 = Val::Bits(B64::new(0x0706_0504_0302_0100, 64));

        match isla_xperm8(rs1, rs2, &mut solver, SourceLoc::unknown())? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(0x1122_3344_5566_7788, 64)),
            value => panic!("expected concrete xperm8 result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_xperm4_symbolic_path_has_input_width() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let rs2 = solver.declare_const(Ty::BitVec(64), SourceLoc::unknown());

        match isla_xperm4(
            Val::Bits(B64::new(0xFEDC_BA98_7654_3210, 64)),
            Val::Symbolic(rs2),
            &mut solver,
            SourceLoc::unknown(),
        )? {
            Val::Symbolic(result) => assert_eq!(solver.length(result), Some(64)),
            value => panic!("expected symbolic xperm4 result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_read_vreg_splits_concrete_registers() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let zero = Val::Bits(B64::zeros(64));
        let args = vec![
            Val::I128(4),
            Val::I128(16),
            Val::I128(0),
            Val::Bits(B64::new(0x1122_3344_5566_7788, 64)),
            zero.clone(),
            zero.clone(),
            zero.clone(),
            zero.clone(),
            zero.clone(),
            zero.clone(),
            zero,
        ];

        match isla_read_vreg_internal(args, &mut solver, SourceLoc::unknown())? {
            Val::Vector(values) => {
                assert_eq!(values[0], Val::Bits(B64::new(0x7788, 16)));
                assert_eq!(values[1], Val::Bits(B64::new(0x5566, 16)));
                assert_eq!(values[2], Val::Bits(B64::new(0x3344, 16)));
                assert_eq!(values[3], Val::Bits(B64::new(0x1122, 16)));
            }
            value => panic!("expected vector result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_read_vreg_splits_symbolic_registers() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let vreg = solver.declare_const(Ty::BitVec(64), SourceLoc::unknown());
        let zero = Val::Bits(B64::zeros(64));
        let args = vec![
            Val::I128(8),
            Val::I128(8),
            Val::I128(0),
            Val::Symbolic(vreg),
            zero.clone(),
            zero.clone(),
            zero.clone(),
            zero.clone(),
            zero.clone(),
            zero.clone(),
            zero,
        ];

        match isla_read_vreg_internal(args, &mut solver, SourceLoc::unknown())? {
            Val::Vector(values) => {
                assert_eq!(values.len(), 8);
                for value in values {
                    match value {
                        Val::Symbolic(sym) => assert_eq!(solver.length(sym), Some(8)),
                        value => panic!("expected symbolic 8-bit element, got {:?}", value),
                    }
                }
            }
            value => panic!("expected vector result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_read_vreg_allows_symbolic_num_elem() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let num_elem = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        let zero = Val::Bits(B64::zeros(64));
        let args = vec![
            Val::Symbolic(num_elem),
            Val::I128(32),
            Val::I128(0),
            Val::Bits(B64::new(0x1122_3344_5566_7788, 64)),
            zero.clone(),
            zero.clone(),
            zero.clone(),
            zero.clone(),
            zero.clone(),
            zero.clone(),
            zero,
        ];

        match isla_read_vreg_internal(args, &mut solver, SourceLoc::unknown())? {
            Val::Vector(values) => {
                assert_eq!(values.len(), 16);
                assert_eq!(values[0], Val::Bits(B64::new(0x5566_7788, 32)));
                assert_eq!(values[1], Val::Bits(B64::new(0x1122_3344, 32)));
            }
            value => panic!("expected vector result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_init_mask_builds_concrete_active_mask() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let args = vec![Val::I128(8), Val::I128(2), Val::I128(5), Val::I128(6), Val::Bits(B64::new(0b1111_0001, 8))];

        match isla_init_mask_internal(args, &mut solver, SourceLoc::unknown())? {
            Val::Bits(bits) => assert_eq!(bits, B64::new(0b0011_0000, 8)),
            value => panic!("expected concrete mask bits, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_init_mask_builds_concrete_b129_high_mask() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B129>::new(&ctx);
        let vm = B129::zeros(128).set_slice(127, B129::BIT_ONE);
        let args = vec![Val::I128(128), Val::I128(127), Val::I128(127), Val::I128(128), Val::Bits(vm)];

        match isla_init_mask_internal(args, &mut solver, SourceLoc::unknown())? {
            Val::Bits(bits) => assert_eq!(bits, vm),
            value => panic!("expected concrete mask bits, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_init_mask_builds_symbolic_mask_with_fixed_width() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let start = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        let end = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        let real_num_elem = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        let args = vec![
            Val::I128(4),
            Val::Symbolic(start),
            Val::Symbolic(end),
            Val::Symbolic(real_num_elem),
            Val::Bits(B64::new(0b1111, 4)),
        ];

        match isla_init_mask_internal(args, &mut solver, SourceLoc::unknown())? {
            Val::Symbolic(mask) => assert_eq!(solver.length(mask), Some(4)),
            value => panic!("expected symbolic mask, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn bool_to_bit_builds_one_bit_result() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);

        assert_eq!(bool_to_bit(Val::Bool(true), &mut solver, SourceLoc::unknown())?, Val::Bits(B64::BIT_ONE));
        assert_eq!(bool_to_bit(Val::Bool(false), &mut solver, SourceLoc::unknown())?, Val::Bits(B64::BIT_ZERO));

        let condition = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        match bool_to_bit(Val::Symbolic(condition), &mut solver, SourceLoc::unknown())? {
            Val::Symbolic(result) => assert_eq!(solver.length(result), Some(1)),
            value => panic!("expected symbolic bit result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_fixed_rounding_incr_handles_concrete_modes() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let elem = Val::Bits(B64::new(0b10110, 5));

        assert_eq!(
            isla_fixed_rounding_incr_internal(
                vec![elem.clone(), Val::I128(2), Val::Bits(B64::new(0b00, 2))],
                &mut solver,
                SourceLoc::unknown(),
            )?,
            Val::Bits(B64::BIT_ONE)
        );
        assert_eq!(
            isla_fixed_rounding_incr_internal(
                vec![elem.clone(), Val::I128(2), Val::Bits(B64::new(0b01, 2))],
                &mut solver,
                SourceLoc::unknown(),
            )?,
            Val::Bits(B64::BIT_ONE)
        );
        assert_eq!(
            isla_fixed_rounding_incr_internal(
                vec![elem.clone(), Val::I128(2), Val::Bits(B64::new(0b10, 2))],
                &mut solver,
                SourceLoc::unknown(),
            )?,
            Val::Bits(B64::BIT_ZERO)
        );
        assert_eq!(
            isla_fixed_rounding_incr_internal(
                vec![elem, Val::I128(2), Val::Bits(B64::new(0b11, 2))],
                &mut solver,
                SourceLoc::unknown(),
            )?,
            Val::Bits(B64::BIT_ZERO)
        );

        Ok(())
    }

    #[test]
    fn isla_fixed_rounding_incr_builds_symbolic_bit() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let shift = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        let mode = solver.declare_const(Ty::BitVec(2), SourceLoc::unknown());

        match isla_fixed_rounding_incr_internal(
            vec![Val::Bits(B64::new(0b10110, 5)), Val::Symbolic(shift), Val::Symbolic(mode)],
            &mut solver,
            SourceLoc::unknown(),
        )? {
            Val::Symbolic(result) => assert_eq!(solver.length(result), Some(1)),
            value => panic!("expected symbolic rounding increment, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_select_int_selects_concrete_and_symbolic_values() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);

        assert_eq!(
            isla_select_int_internal(
                vec![Val::Bool(true), Val::I128(7), Val::I128(-3)],
                &mut solver,
                SourceLoc::unknown(),
            )?,
            Val::I128(7)
        );
        assert_eq!(
            isla_select_int_internal(
                vec![Val::Bool(false), Val::I128(7), Val::I128(-3)],
                &mut solver,
                SourceLoc::unknown(),
            )?,
            Val::I128(-3)
        );

        let condition = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        match isla_select_int_internal(
            vec![Val::Symbolic(condition), Val::I128(7), Val::I128(-3)],
            &mut solver,
            SourceLoc::unknown(),
        )? {
            Val::Symbolic(result) => assert_eq!(solver.length(result), Some(128)),
            value => panic!("expected symbolic integer select result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_mask_from_low_bits_handles_concrete_fill_and_source() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);

        let masked = isla_mask_from_low_bits_internal(
            vec![
                Val::I128(3),
                Val::Bits(B64::BIT_ZERO),
                Val::Bits(B64::BIT_ONE),
                Val::Bits(B64::new(0b10101, 8)),
                Val::Bits(B64::new(0, 5)),
            ],
            &mut solver,
            SourceLoc::unknown(),
        )?;
        assert_eq!(masked, Val::Bits(B64::new(0b11101, 5)));

        let unmasked = isla_mask_from_low_bits_internal(
            vec![
                Val::I128(3),
                Val::Bits(B64::BIT_ONE),
                Val::Bits(B64::BIT_ZERO),
                Val::Bits(B64::new(0b10101, 8)),
                Val::Bits(B64::new(0, 5)),
            ],
            &mut solver,
            SourceLoc::unknown(),
        )?;
        assert_eq!(unmasked, Val::Bits(B64::new(0, 5)));

        Ok(())
    }

    #[test]
    fn isla_mask_from_low_bits_uses_source_width_for_symbolic_len_without_template() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let num_elem = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        let vm = solver.declare_const(Ty::BitVec(1), SourceLoc::unknown());

        match isla_mask_from_low_bits_internal(
            vec![Val::Symbolic(num_elem), Val::Symbolic(vm), Val::Bits(B64::BIT_ONE), Val::Bits(B64::new(0b10101, 8))],
            &mut solver,
            SourceLoc::unknown(),
        )? {
            Val::Symbolic(mask) => assert_eq!(solver.length(mask), Some(8)),
            value => panic!("expected symbolic mask, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_mask_from_low_bits_builds_symbolic_width_preserving_mask() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let num_elem = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
        let vm = solver.declare_const(Ty::BitVec(1), SourceLoc::unknown());

        match isla_mask_from_low_bits_internal(
            vec![
                Val::Symbolic(num_elem),
                Val::Symbolic(vm),
                Val::Bits(B64::BIT_ONE),
                Val::Bits(B64::new(0b10101, 8)),
                Val::Bits(B64::new(0, 5)),
            ],
            &mut solver,
            SourceLoc::unknown(),
        )? {
            Val::Symbolic(mask) => assert_eq!(solver.length(mask), Some(5)),
            value => panic!("expected symbolic mask, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_vector_select_uses_mask_bits() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let args = vec![
            Val::Bits(B64::new(0b101, 3)),
            Val::Vector(vec![Val::Bits(B64::new(0x10, 8)), Val::Bits(B64::new(0x11, 8)), Val::Bits(B64::new(0x12, 8))]),
            Val::Vector(vec![Val::Bits(B64::new(0x20, 8)), Val::Bits(B64::new(0x21, 8)), Val::Bits(B64::new(0x22, 8))]),
        ];

        match isla_vector_select_internal(args, &mut solver, SourceLoc::unknown())? {
            Val::Vector(values) => {
                assert_eq!(values[0], Val::Bits(B64::new(0x20, 8)));
                assert_eq!(values[1], Val::Bits(B64::new(0x11, 8)));
                assert_eq!(values[2], Val::Bits(B64::new(0x22, 8)));
            }
            value => panic!("expected vector result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_vector_access_or_default_handles_concrete_bounds() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let values =
            Val::Vector(vec![Val::Bits(B64::new(0x10, 8)), Val::Bits(B64::new(0x11, 8)), Val::Bits(B64::new(0x12, 8))]);
        let default = Val::Bits(B64::new(0, 8));

        assert_eq!(
            isla_vector_access_or_default_internal(
                vec![Val::I128(3), values.clone(), Val::Bits(B64::new(1, 8)), default.clone()],
                &mut solver,
                SourceLoc::unknown(),
            )?,
            Val::Bits(B64::new(0x11, 8))
        );
        assert_eq!(
            isla_vector_access_or_default_internal(
                vec![Val::I128(3), values, Val::Bits(B64::new(5, 8)), default.clone()],
                &mut solver,
                SourceLoc::unknown(),
            )?,
            default
        );

        Ok(())
    }

    #[test]
    fn isla_vector_access_or_default_builds_smt_array_select() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let index = solver.declare_const(Ty::BitVec(2), SourceLoc::unknown());
        let values =
            Val::Vector(vec![Val::Bits(B64::new(0x10, 8)), Val::Bits(B64::new(0x11, 8)), Val::Bits(B64::new(0x12, 8))]);
        let default = Val::Bits(B64::new(0, 8));

        let array_exp = vector_array_access_or_default_exp(
            3,
            &[bits64(0x10, 8), bits64(0x11, 8), bits64(0x12, 8)],
            &Val::Symbolic(index),
            8,
            &default,
            &mut solver,
            SourceLoc::unknown(),
        )?;
        let array_exp_debug = format!("{:?}", array_exp);
        assert!(array_exp_debug.contains("Select("));
        assert!(array_exp_debug.contains("Store("));

        match isla_vector_access_or_default_internal(
            vec![Val::I128(3), values, Val::Symbolic(index), default],
            &mut solver,
            SourceLoc::unknown(),
        )? {
            Val::Symbolic(result) => {
                assert_eq!(solver.length(result), Some(8));
                assert_eq!(
                    solver.check_sat_with(
                        &Exp::And(
                            Box::new(Exp::Eq(Box::new(Exp::Var(index)), Box::new(bits64(1, 2)))),
                            Box::new(Exp::Neq(Box::new(Exp::Var(result)), Box::new(bits64(0x11, 8)))),
                        ),
                        SourceLoc::unknown(),
                    ),
                    SmtResult::Unsat
                );
                assert_eq!(
                    solver.check_sat_with(
                        &Exp::And(
                            Box::new(Exp::Eq(Box::new(Exp::Var(index)), Box::new(bits64(3, 2)))),
                            Box::new(Exp::Neq(Box::new(Exp::Var(result)), Box::new(bits64(0, 8)))),
                        ),
                        SourceLoc::unknown(),
                    ),
                    SmtResult::Unsat
                );
            }
            value => panic!("expected symbolic vector access result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_masktypei_result_merges_body_elements() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let vs2 = Val::Vector(vec![
            Val::Bits(B64::new(0x10, 8)),
            Val::Bits(B64::new(0x11, 8)),
            Val::Bits(B64::new(0x12, 8)),
            Val::Bits(B64::new(0x13, 8)),
            Val::Bits(B64::new(0x14, 8)),
            Val::Bits(B64::new(0x15, 8)),
        ]);
        let vd = Val::Vector(vec![
            Val::Bits(B64::new(0x30, 8)),
            Val::Bits(B64::new(0x31, 8)),
            Val::Bits(B64::new(0x32, 8)),
            Val::Bits(B64::new(0x33, 8)),
            Val::Bits(B64::new(0x34, 8)),
            Val::Bits(B64::new(0x35, 8)),
        ]);
        let args = vec![
            Val::I128(6),
            Val::I128(1),
            Val::I128(4),
            Val::I128(5),
            Val::Bits(B64::new(0b010100, 6)),
            Val::Bits(B64::new(0xaa, 8)),
            vs2,
            vd,
        ];

        match isla_masktypei_result_internal(args, &mut solver, SourceLoc::unknown())? {
            Val::Vector(values) => {
                assert_eq!(values[0], Val::Bits(B64::new(0x30, 8)));
                assert_eq!(values[1], Val::Bits(B64::new(0x11, 8)));
                assert_eq!(values[2], Val::Bits(B64::new(0xaa, 8)));
                assert_eq!(values[3], Val::Bits(B64::new(0x13, 8)));
                assert_eq!(values[4], Val::Bits(B64::new(0xaa, 8)));
                assert_eq!(values[5], Val::Bits(B64::new(0x35, 8)));
            }
            value => panic!("expected vector result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_masktypev_result_merges_body_elements() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let vs1 = Val::Vector(vec![
            Val::Bits(B64::new(0x20, 8)),
            Val::Bits(B64::new(0x21, 8)),
            Val::Bits(B64::new(0x22, 8)),
            Val::Bits(B64::new(0x23, 8)),
            Val::Bits(B64::new(0x24, 8)),
            Val::Bits(B64::new(0x25, 8)),
        ]);
        let vs2 = Val::Vector(vec![
            Val::Bits(B64::new(0x10, 8)),
            Val::Bits(B64::new(0x11, 8)),
            Val::Bits(B64::new(0x12, 8)),
            Val::Bits(B64::new(0x13, 8)),
            Val::Bits(B64::new(0x14, 8)),
            Val::Bits(B64::new(0x15, 8)),
        ]);
        let vd = Val::Vector(vec![
            Val::Bits(B64::new(0x30, 8)),
            Val::Bits(B64::new(0x31, 8)),
            Val::Bits(B64::new(0x32, 8)),
            Val::Bits(B64::new(0x33, 8)),
            Val::Bits(B64::new(0x34, 8)),
            Val::Bits(B64::new(0x35, 8)),
        ]);
        let args = vec![
            Val::I128(6),
            Val::I128(1),
            Val::I128(4),
            Val::I128(5),
            Val::Bits(B64::new(0b010100, 6)),
            vs1,
            vs2,
            vd,
        ];

        match isla_masktypev_result_internal(args, &mut solver, SourceLoc::unknown())? {
            Val::Vector(values) => {
                assert_eq!(values[0], Val::Bits(B64::new(0x30, 8)));
                assert_eq!(values[1], Val::Bits(B64::new(0x11, 8)));
                assert_eq!(values[2], Val::Bits(B64::new(0x22, 8)));
                assert_eq!(values[3], Val::Bits(B64::new(0x13, 8)));
                assert_eq!(values[4], Val::Bits(B64::new(0x24, 8)));
                assert_eq!(values[5], Val::Bits(B64::new(0x35, 8)));
            }
            value => panic!("expected vector result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_pack_vreg_packs_elements_little_endian_per_register() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let values = (0x11u64..=0x18).map(|value| Val::Bits(B64::new(value, 8))).collect::<Vec<_>>();
        let args = vec![Val::I128(8), Val::I128(32), Val::Vector(values)];

        match isla_pack_vreg_internal(args, &mut solver, SourceLoc::unknown())? {
            Val::Vector(registers) => {
                assert_eq!(registers[0], Val::Bits(B64::new(0x1413_1211, 32)));
                assert_eq!(registers[1], Val::Bits(B64::new(0x1817_1615, 32)));
                assert_eq!(registers[2], Val::Bits(B64::new(0, 32)));
            }
            value => panic!("expected packed register vector, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn isla_mux2_selects_bitvector_operand() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let false_value = Val::Bits(B64::new(0xaa, 8));
        let true_value = Val::Bits(B64::new(0x55, 8));

        assert_eq!(
            isla_mux2_internal(
                Val::Bits(B64::BIT_ZERO),
                false_value.clone(),
                true_value.clone(),
                &mut solver,
                SourceLoc::unknown(),
            )?,
            false_value
        );
        assert_eq!(
            isla_mux2_internal(
                Val::Bits(B64::BIT_ONE),
                Val::Bits(B64::new(0xaa, 8)),
                true_value,
                &mut solver,
                SourceLoc::unknown(),
            )?,
            Val::Bits(B64::new(0x55, 8))
        );

        let selector = solver.declare_const(Ty::BitVec(1), SourceLoc::unknown());
        match isla_mux2_internal(
            Val::Symbolic(selector),
            Val::Bits(B64::new(0xaa, 8)),
            Val::Bits(B64::new(0x55, 8)),
            &mut solver,
            SourceLoc::unknown(),
        )? {
            Val::Symbolic(result) => assert_eq!(solver.length(result), Some(8)),
            value => panic!("expected symbolic mux result, got {:?}", value),
        }

        Ok(())
    }

    #[test]
    fn mixed_bits() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let b1 = B64::new(0b11, 2);
        let p1 = BitsSegment::Concrete(b1);
        let v2 = solver.declare_const(Ty::BitVec(5), SourceLoc::unknown());
        let p2 = BitsSegment::Symbolic(v2);
        let p3 = BitsSegment::Concrete(B64::new(0b101, 3));
        let p4 = BitsSegment::Symbolic(solver.declare_const(Ty::BitVec(4), SourceLoc::unknown()));
        let val = Val::MixedBits(vec![p4, p3, p2, p1]);
        // Check basic flattening
        let _ = optimistic_assert(
            op_eq(val.clone(), Val::Bits(B64::new(0b0110_101_10011_11, 14)), &mut solver, SourceLoc::unknown())?,
            Val::String("mixed_bits 1".to_string()),
            &mut solver,
            SourceLoc::unknown(),
        )?;
        // Check that we can extract a concrete segment
        match op_slice(val.clone(), Val::I64(0), 2, &mut solver, SourceLoc::unknown())? {
            Val::Bits(bits) => assert!(bits == b1),
            _ => assert!(false),
        };
        // Check that we can extract a symbolic segment
        match op_slice(val.clone(), Val::I64(2), 5, &mut solver, SourceLoc::unknown())? {
            Val::Symbolic(v) => assert!(v == v2),
            _ => assert!(false),
        };
        let _ = pessimistic_assert(
            op_eq(
                op_slice(val.clone(), Val::I64(1), 5, &mut solver, SourceLoc::unknown())?,
                append(
                    Val::Bits(B64::new(1, 1)),
                    op_slice(Val::Symbolic(v2), Val::I64(0), 4, &mut solver, SourceLoc::unknown())?,
                    &mut solver,
                    SourceLoc::unknown(),
                )?,
                &mut solver,
                SourceLoc::unknown(),
            )?,
            Val::String("mixed_bits 2".to_string()),
            &mut solver,
            SourceLoc::unknown(),
        );
        // vector_access
        match vector_access(val.clone(), Val::I128(1), &mut solver, SourceLoc::unknown())? {
            Val::Bits(bit) => assert!(bit == B64::BIT_ONE),
            _ => assert!(false),
        };
        match vector_access(val.clone(), Val::I128(8), &mut solver, SourceLoc::unknown())? {
            Val::Bits(bit) => assert!(bit == B64::BIT_ZERO),
            _ => assert!(false),
        };
        let _ = pessimistic_assert(
            op_eq(
                vector_access(val.clone(), Val::I128(5), &mut solver, SourceLoc::unknown())?,
                op_slice(val, Val::I64(0), 1, &mut solver, SourceLoc::unknown())?,
                &mut solver,
                SourceLoc::unknown(),
            )?,
            Val::String("mixed bits 3".to_string()),
            &mut solver,
            SourceLoc::unknown(),
        );

        assert!(solver.check_sat(SourceLoc::unknown()) == SmtResult::Sat);
        Ok(())
    }
}
