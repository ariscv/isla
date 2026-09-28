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

//! This module defines all the Sail primitives for working with
//! floating point numbers.  Internally Isla uses the same
//! representation for floating points that Z3/SMTLIB uses, which
//! allows floating point numbers with arbitrary exponent and
//! significand widths. However, in Sail we want to ensure we can use
//! SoftFloat for emulation, so we restrict the primitives here to 16,
//! 32, 64, and 128-bit variants, prefixed either `fp16`, `fp32`,
//! `fp64`, and `fp128` respectively, as these are supported by
//! SoftFloat. Functions just prefixed with `fp_` work with any input
//! width.
//!
//! Floating point expressions are supported by the current `Qfaufbv`
//! solver tactic.

use std::collections::HashMap;

use crate::bitvector::BV;
use crate::error::ExecError;
use crate::executor::LocalFrame;
use crate::ir::{BitsSegment, FPTy, Val};
use crate::primop_util::smt_value;
use crate::smt::smtlib::*;
use crate::smt::*;
use crate::source_loc::SourceLoc;

use super::{Binary, Unary, Variadic};

fn fp_arg<B: BV>(value: Val<B>, solver: &Solver<B>, name: &str, info: SourceLoc) -> Result<(Sym, u32, u32), ExecError> {
    match value {
        Val::Symbolic(sym) => match solver.scalar_sort(sym) {
            Some(Ty::Float(ebits, sbits)) => Ok((sym, ebits, sbits)),
            _ => Err(ExecError::Type(name.to_string(), info)),
        },
        _ => Err(ExecError::Type(name.to_string(), info)),
    }
}

fn rm_arg<B: BV>(value: Val<B>, solver: &Solver<B>, name: &str, info: SourceLoc) -> Result<Sym, ExecError> {
    match value {
        Val::Symbolic(sym) if matches!(solver.scalar_sort(sym), Some(Ty::RoundingMode)) => Ok(sym),
        _ => Err(ExecError::Type(name.to_string(), info)),
    }
}

fn bv_arg<B: BV>(
    value: &Val<B>,
    solver: &Solver<B>,
    name: &str,
    info: SourceLoc,
) -> Result<(Exp<Sym>, u32), ExecError> {
    let width = match value {
        Val::Bits(bits) if bits.len() > 0 => bits.len(),
        Val::Symbolic(sym) => match solver.scalar_sort(*sym) {
            Some(Ty::BitVec(width)) if width > 0 => width,
            _ => return Err(ExecError::Type(name.to_string(), info)),
        },
        Val::MixedBits(segments) if !segments.is_empty() => {
            let mut width = 0_u32;
            for segment in segments {
                let part = match segment {
                    BitsSegment::Concrete(bits) if bits.len() > 0 => bits.len(),
                    BitsSegment::Symbolic(sym) => match solver.scalar_sort(*sym) {
                        Some(Ty::BitVec(width)) if width > 0 => width,
                        _ => return Err(ExecError::Type(name.to_string(), info)),
                    },
                    _ => return Err(ExecError::Type(name.to_string(), info)),
                };
                width = width.checked_add(part).ok_or_else(|| ExecError::Type(name.to_string(), info))?;
            }
            width
        }
        _ => return Err(ExecError::Type(name.to_string(), info)),
    };
    Ok((smt_value(value, info)?, width))
}

macro_rules! rounding_mode_primop {
    ($f:ident, $mode:expr) => {
        pub fn $f<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
            solver.define_const(Exp::FPRoundingMode($mode), info).into()
        }
    };
}

rounding_mode_primop!(round_nearest_ties_to_even, FPRoundingMode::RoundNearestTiesToEven);
rounding_mode_primop!(round_nearest_ties_to_away, FPRoundingMode::RoundNearestTiesToAway);
rounding_mode_primop!(round_toward_positive, FPRoundingMode::RoundTowardPositive);
rounding_mode_primop!(round_toward_negative, FPRoundingMode::RoundTowardNegative);
rounding_mode_primop!(round_toward_zero, FPRoundingMode::RoundTowardZero);

pub fn fp16_undefined<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    solver.declare_const(FPTy::fp16().to_smt(), info).into()
}

pub fn fp32_undefined<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    solver.declare_const(FPTy::fp32().to_smt(), info).into()
}

pub fn fp64_undefined<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    solver.declare_const(FPTy::fp64().to_smt(), info).into()
}

pub fn fp128_undefined<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    solver.declare_const(FPTy::fp128().to_smt(), info).into()
}

macro_rules! fp_constant_primop {
    ($f:ident, $constant:expr) => {
        pub mod $f {
            use super::*;
            pub fn constant16<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
                let ty = FPTy::fp16();
                solver
                    .define_const(Exp::FPConstant($constant, ty.exponent_width(), ty.significand_width()), info)
                    .into()
            }
            pub fn constant32<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
                let ty = FPTy::fp32();
                solver
                    .define_const(Exp::FPConstant($constant, ty.exponent_width(), ty.significand_width()), info)
                    .into()
            }
            pub fn constant64<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
                let ty = FPTy::fp64();
                solver
                    .define_const(Exp::FPConstant($constant, ty.exponent_width(), ty.significand_width()), info)
                    .into()
            }
            pub fn constant128<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
                let ty = FPTy::fp128();
                solver
                    .define_const(Exp::FPConstant($constant, ty.exponent_width(), ty.significand_width()), info)
                    .into()
            }
        }
    };
}

fp_constant_primop!(fp_nan, FPConstant::NaN);
fp_constant_primop!(fp_inf, FPConstant::Inf { negative: false });
fp_constant_primop!(fp_negative_inf, FPConstant::Inf { negative: true });
fp_constant_primop!(fp_zero, FPConstant::Zero { negative: false });
fp_constant_primop!(fp_negative_zero, FPConstant::Zero { negative: true });

macro_rules! fp_unary_primop {
    ($f:ident, $op:expr) => {
        pub fn $f<B: BV>(v: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
            let (v, _, _) = fp_arg(v, solver, stringify!($f), info)?;
            solver.define_const(Exp::FPUnary($op, Box::new(Exp::Var(v))), info).into()
        }
    };
}

fp_unary_primop!(fp_abs, FPUnary::Abs);
fp_unary_primop!(fp_neg, FPUnary::Neg);
fp_unary_primop!(fp_is_normal, FPUnary::IsNormal);
fp_unary_primop!(fp_is_subnormal, FPUnary::IsSubnormal);
fp_unary_primop!(fp_is_zero, FPUnary::IsZero);
fp_unary_primop!(fp_is_infinite, FPUnary::IsInfinite);
fp_unary_primop!(fp_is_nan, FPUnary::IsNaN);
fp_unary_primop!(fp_is_negative, FPUnary::IsNegative);
fp_unary_primop!(fp_is_positive, FPUnary::IsPositive);

macro_rules! fp_from_ieee_primop {
    ($f:ident, $ty:expr) => {
        pub fn $f<B: BV>(v: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
            let ty = $ty;
            let (bits, width) = bv_arg(&v, solver, stringify!($f), info)?;
            if width != ty.exponent_width() + ty.significand_width() {
                return Err(ExecError::Type(stringify!($f).to_string(), info));
            }
            solver
                .define_const(
                    Exp::FPUnary(FPUnary::FromIEEE(ty.exponent_width(), ty.significand_width()), Box::new(bits)),
                    info,
                )
                .into()
        }
    };
}

fp_from_ieee_primop!(fp16_from_ieee, FPTy::fp16());
fp_from_ieee_primop!(fp32_from_ieee, FPTy::fp32());
fp_from_ieee_primop!(fp64_from_ieee, FPTy::fp64());
fp_from_ieee_primop!(fp128_from_ieee, FPTy::fp128());

macro_rules! fp_to_ieee_primop {
    ($f:ident, $ty:expr) => {
        pub fn $f<B: BV>(v: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
            let ty = $ty;
            let (sym, ebits, sbits) = fp_arg(v, solver, stringify!($f), info)?;
            if ebits != ty.exponent_width() || sbits != ty.significand_width() {
                return Err(ExecError::Type(stringify!($f).to_string(), info));
            }
            solver.define_const(Exp::FPUnary(FPUnary::ToIEEE(ebits, sbits), Box::new(Exp::Var(sym))), info).into()
        }
    };
}

fp_to_ieee_primop!(fp16_to_ieee, FPTy::fp16());
fp_to_ieee_primop!(fp32_to_ieee, FPTy::fp32());
fp_to_ieee_primop!(fp64_to_ieee, FPTy::fp64());
fp_to_ieee_primop!(fp128_to_ieee, FPTy::fp128());

macro_rules! fp_rounding_unary_primop {
    ($f:ident, $op:expr) => {
        pub fn $f<B: BV>(rm: Val<B>, v: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
            let rm = rm_arg(rm, solver, stringify!($f), info)?;
            let op = $op;
            let value = match op {
                FPRoundingUnary::FromSigned(..) | FPRoundingUnary::FromUnsigned(..) => {
                    bv_arg(&v, solver, stringify!($f), info)?.0
                }
                _ => Exp::Var(fp_arg(v, solver, stringify!($f), info)?.0),
            };
            solver.define_const(Exp::FPRoundingUnary(op, Box::new(Exp::Var(rm)), Box::new(value)), info).into()
        }
    };
}

fp_rounding_unary_primop!(fp_sqrt, FPRoundingUnary::Sqrt);
fp_rounding_unary_primop!(fp_round_to_integral, FPRoundingUnary::RoundToIntegral);

fp_rounding_unary_primop!(fp16_convert, {
    let ty = FPTy::fp16();
    FPRoundingUnary::Convert(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp32_convert, {
    let ty = FPTy::fp32();
    FPRoundingUnary::Convert(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp64_convert, {
    let ty = FPTy::fp64();
    FPRoundingUnary::Convert(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp128_convert, {
    let ty = FPTy::fp128();
    FPRoundingUnary::Convert(ty.exponent_width(), ty.significand_width())
});

fp_rounding_unary_primop!(fp16_from_signed, {
    let ty = FPTy::fp16();
    FPRoundingUnary::FromSigned(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp32_from_signed, {
    let ty = FPTy::fp32();
    FPRoundingUnary::FromSigned(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp64_from_signed, {
    let ty = FPTy::fp64();
    FPRoundingUnary::FromSigned(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp128_from_signed, {
    let ty = FPTy::fp128();
    FPRoundingUnary::FromSigned(ty.exponent_width(), ty.significand_width())
});

fp_rounding_unary_primop!(fp16_from_unsigned, {
    let ty = FPTy::fp16();
    FPRoundingUnary::FromUnsigned(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp32_from_unsigned, {
    let ty = FPTy::fp32();
    FPRoundingUnary::FromUnsigned(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp64_from_unsigned, {
    let ty = FPTy::fp64();
    FPRoundingUnary::FromUnsigned(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp128_from_unsigned, {
    let ty = FPTy::fp128();
    FPRoundingUnary::FromUnsigned(ty.exponent_width(), ty.significand_width())
});

fp_rounding_unary_primop!(fp_to_signed16, FPRoundingUnary::ToSigned(16));
fp_rounding_unary_primop!(fp_to_signed32, FPRoundingUnary::ToSigned(32));
fp_rounding_unary_primop!(fp_to_signed64, FPRoundingUnary::ToSigned(64));
fp_rounding_unary_primop!(fp_to_signed128, FPRoundingUnary::ToSigned(128));
fp_rounding_unary_primop!(fp_to_unsigned16, FPRoundingUnary::ToUnsigned(16));
fp_rounding_unary_primop!(fp_to_unsigned32, FPRoundingUnary::ToUnsigned(32));
fp_rounding_unary_primop!(fp_to_unsigned64, FPRoundingUnary::ToUnsigned(64));
fp_rounding_unary_primop!(fp_to_unsigned128, FPRoundingUnary::ToUnsigned(128));

pub fn fp32_to_bf16<B: BV>(
    rm: Val<B>,
    v: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let rm = rm_arg(rm, solver, "fp32_to_bf16", info)?;
    let (value, ebits, sbits) = fp_arg(v, solver, "fp32_to_bf16", info)?;
    if (ebits, sbits) != (8, 24) {
        return Err(ExecError::Type("fp32_to_bf16".to_string(), info));
    }
    let converted =
        Exp::FPRoundingUnary(FPRoundingUnary::Convert(8, 8), Box::new(Exp::Var(rm)), Box::new(Exp::Var(value)));
    solver.define_const(Exp::FPUnary(FPUnary::ToIEEE(8, 8), Box::new(converted)), info).into()
}

macro_rules! fp_binary_primop {
    ($f:ident, $op:expr) => {
        pub fn $f<B: BV>(
            lhs: Val<B>,
            rhs: Val<B>,
            solver: &mut Solver<B>,
            info: SourceLoc,
        ) -> Result<Val<B>, ExecError> {
            let (lhs, lhs_ebits, lhs_sbits) = fp_arg(lhs, solver, stringify!($f), info)?;
            let (rhs, rhs_ebits, rhs_sbits) = fp_arg(rhs, solver, stringify!($f), info)?;
            if (lhs_ebits, lhs_sbits) != (rhs_ebits, rhs_sbits) {
                return Err(ExecError::Type(stringify!($f).to_string(), info));
            }
            solver.define_const(Exp::FPBinary($op, Box::new(Exp::Var(lhs)), Box::new(Exp::Var(rhs))), info).into()
        }
    };
}

fp_binary_primop!(fp_rem, FPBinary::Rem);
fp_binary_primop!(fp_min, FPBinary::Min);
fp_binary_primop!(fp_max, FPBinary::Max);
fp_binary_primop!(fp_lteq, FPBinary::Leq);
fp_binary_primop!(fp_lt, FPBinary::Lt);
fp_binary_primop!(fp_gteq, FPBinary::Geq);
fp_binary_primop!(fp_gt, FPBinary::Gt);
fp_binary_primop!(fp_eq, FPBinary::Eq);

macro_rules! fp_rounding_binary_primop {
    ($f:ident, $op:expr) => {
        pub fn $f<B: BV>(
            mut args: Vec<Val<B>>,
            solver: &mut Solver<B>,
            _: &mut LocalFrame<B>,
            info: SourceLoc,
        ) -> Result<Val<B>, ExecError> {
            if args.len() != 3 {
                return Err(ExecError::Type(format!("Incorrect number of arguments for {}", stringify!($f)), info));
            }
            let rhs = args.pop().unwrap();
            let lhs = args.pop().unwrap();
            let rm = args.pop().unwrap();
            let rm = rm_arg(rm, solver, stringify!($f), info)?;
            let (lhs, lhs_ebits, lhs_sbits) = fp_arg(lhs, solver, stringify!($f), info)?;
            let (rhs, rhs_ebits, rhs_sbits) = fp_arg(rhs, solver, stringify!($f), info)?;
            if (lhs_ebits, lhs_sbits) != (rhs_ebits, rhs_sbits) {
                return Err(ExecError::Type(stringify!($f).to_string(), info));
            }
            solver
                .define_const(
                    Exp::FPRoundingBinary(
                        $op,
                        Box::new(Exp::Var(rm)),
                        Box::new(Exp::Var(lhs)),
                        Box::new(Exp::Var(rhs)),
                    ),
                    info,
                )
                .into()
        }
    };
}

fp_rounding_binary_primop!(fp_add, FPRoundingBinary::Add);
fp_rounding_binary_primop!(fp_sub, FPRoundingBinary::Sub);
fp_rounding_binary_primop!(fp_mul, FPRoundingBinary::Mul);
fp_rounding_binary_primop!(fp_div, FPRoundingBinary::Div);

pub fn fp_fma<B: BV>(
    mut args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if args.len() != 4 {
        return Err(ExecError::Type("Incorrect number of arguments for fp_fma".to_string(), info));
    }
    let z = args.pop().unwrap();
    let y = args.pop().unwrap();
    let x = args.pop().unwrap();
    let rm = args.pop().unwrap();
    let rm = rm_arg(rm, solver, "fp_fma", info)?;
    let (x, x_ebits, x_sbits) = fp_arg(x, solver, "fp_fma", info)?;
    let (y, y_ebits, y_sbits) = fp_arg(y, solver, "fp_fma", info)?;
    let (z, z_ebits, z_sbits) = fp_arg(z, solver, "fp_fma", info)?;
    if (x_ebits, x_sbits) != (y_ebits, y_sbits) || (x_ebits, x_sbits) != (z_ebits, z_sbits) {
        return Err(ExecError::Type("fp_fma".to_string(), info));
    }
    solver
        .define_const(
            Exp::FPfma(Box::new(Exp::Var(rm)), Box::new(Exp::Var(x)), Box::new(Exp::Var(y)), Box::new(Exp::Var(z))),
            info,
        )
        .into()
}

pub fn unary_primops<B: BV>() -> HashMap<String, Unary<B>> {
    let mut primops = HashMap::new();
    primops.insert("round_nearest_ties_to_even".to_string(), round_nearest_ties_to_even as Unary<B>);
    primops.insert("round_nearest_ties_to_away".to_string(), round_nearest_ties_to_away as Unary<B>);
    primops.insert("round_toward_positive".to_string(), round_toward_positive as Unary<B>);
    primops.insert("round_toward_negative".to_string(), round_toward_negative as Unary<B>);
    primops.insert("round_toward_zero".to_string(), round_toward_zero as Unary<B>);

    primops.insert("fp16_nan".to_string(), fp_nan::constant16 as Unary<B>);
    primops.insert("fp32_nan".to_string(), fp_nan::constant32 as Unary<B>);
    primops.insert("fp64_nan".to_string(), fp_nan::constant64 as Unary<B>);
    primops.insert("fp128_nan".to_string(), fp_nan::constant128 as Unary<B>);

    primops.insert("fp16_inf".to_string(), fp_inf::constant16 as Unary<B>);
    primops.insert("fp32_inf".to_string(), fp_inf::constant32 as Unary<B>);
    primops.insert("fp64_inf".to_string(), fp_inf::constant64 as Unary<B>);
    primops.insert("fp128_inf".to_string(), fp_inf::constant128 as Unary<B>);

    primops.insert("fp16_negative_inf".to_string(), fp_negative_inf::constant16 as Unary<B>);
    primops.insert("fp32_negative_inf".to_string(), fp_negative_inf::constant32 as Unary<B>);
    primops.insert("fp64_negative_inf".to_string(), fp_negative_inf::constant64 as Unary<B>);
    primops.insert("fp128_negative_inf".to_string(), fp_negative_inf::constant128 as Unary<B>);

    primops.insert("fp16_zero".to_string(), fp_zero::constant16 as Unary<B>);
    primops.insert("fp32_zero".to_string(), fp_zero::constant32 as Unary<B>);
    primops.insert("fp64_zero".to_string(), fp_zero::constant64 as Unary<B>);
    primops.insert("fp128_zero".to_string(), fp_zero::constant128 as Unary<B>);

    primops.insert("fp16_negative_zero".to_string(), fp_negative_zero::constant16 as Unary<B>);
    primops.insert("fp32_negative_zero".to_string(), fp_negative_zero::constant32 as Unary<B>);
    primops.insert("fp64_negative_zero".to_string(), fp_negative_zero::constant64 as Unary<B>);
    primops.insert("fp128_negative_zero".to_string(), fp_negative_zero::constant128 as Unary<B>);

    primops.insert("fp16_undefined".to_string(), fp16_undefined as Unary<B>);
    primops.insert("fp32_undefined".to_string(), fp32_undefined as Unary<B>);
    primops.insert("fp64_undefined".to_string(), fp64_undefined as Unary<B>);
    primops.insert("fp128_undefined".to_string(), fp128_undefined as Unary<B>);

    primops.insert("fp_abs".to_string(), fp_abs as Unary<B>);
    primops.insert("fp_neg".to_string(), fp_neg as Unary<B>);
    primops.insert("fp_is_normal".to_string(), fp_is_normal as Unary<B>);
    primops.insert("fp_is_subnormal".to_string(), fp_is_subnormal as Unary<B>);
    primops.insert("fp_is_zero".to_string(), fp_is_zero as Unary<B>);
    primops.insert("fp_is_infinite".to_string(), fp_is_infinite as Unary<B>);
    primops.insert("fp_is_nan".to_string(), fp_is_nan as Unary<B>);
    primops.insert("fp_is_negative".to_string(), fp_is_negative as Unary<B>);
    primops.insert("fp_is_positive".to_string(), fp_is_positive as Unary<B>);

    primops.insert("fp16_from_ieee".to_string(), fp16_from_ieee as Unary<B>);
    primops.insert("fp32_from_ieee".to_string(), fp32_from_ieee as Unary<B>);
    primops.insert("fp64_from_ieee".to_string(), fp64_from_ieee as Unary<B>);
    primops.insert("fp128_from_ieee".to_string(), fp128_from_ieee as Unary<B>);
    primops.insert("fp16_to_ieee".to_string(), fp16_to_ieee as Unary<B>);
    primops.insert("fp32_to_ieee".to_string(), fp32_to_ieee as Unary<B>);
    primops.insert("fp64_to_ieee".to_string(), fp64_to_ieee as Unary<B>);
    primops.insert("fp128_to_ieee".to_string(), fp128_to_ieee as Unary<B>);

    primops
}

pub fn binary_primops<B: BV>() -> HashMap<String, Binary<B>> {
    let mut primops = HashMap::new();
    primops.insert("fp_sqrt".to_string(), fp_sqrt as Binary<B>);
    primops.insert("fp_round_to_integral".to_string(), fp_round_to_integral as Binary<B>);

    primops.insert("fp16_convert".to_string(), fp16_convert as Binary<B>);
    primops.insert("fp32_convert".to_string(), fp32_convert as Binary<B>);
    primops.insert("fp64_convert".to_string(), fp64_convert as Binary<B>);
    primops.insert("fp128_convert".to_string(), fp128_convert as Binary<B>);

    primops.insert("fp16_from_signed".to_string(), fp16_from_signed as Binary<B>);
    primops.insert("fp32_from_signed".to_string(), fp32_from_signed as Binary<B>);
    primops.insert("fp64_from_signed".to_string(), fp64_from_signed as Binary<B>);
    primops.insert("fp128_from_signed".to_string(), fp128_from_signed as Binary<B>);

    primops.insert("fp16_from_unsigned".to_string(), fp16_from_unsigned as Binary<B>);
    primops.insert("fp32_from_unsigned".to_string(), fp32_from_unsigned as Binary<B>);
    primops.insert("fp64_from_unsigned".to_string(), fp64_from_unsigned as Binary<B>);
    primops.insert("fp128_from_unsigned".to_string(), fp128_from_unsigned as Binary<B>);

    primops.insert("fp_to_signed16".to_string(), fp_to_signed16 as Binary<B>);
    primops.insert("fp_to_signed32".to_string(), fp_to_signed32 as Binary<B>);
    primops.insert("fp_to_signed64".to_string(), fp_to_signed64 as Binary<B>);
    primops.insert("fp_to_signed128".to_string(), fp_to_signed128 as Binary<B>);
    primops.insert("fp_to_unsigned16".to_string(), fp_to_unsigned16 as Binary<B>);
    primops.insert("fp_to_unsigned32".to_string(), fp_to_unsigned32 as Binary<B>);
    primops.insert("fp_to_unsigned64".to_string(), fp_to_unsigned64 as Binary<B>);
    primops.insert("fp_to_unsigned128".to_string(), fp_to_unsigned128 as Binary<B>);
    primops.insert("fp32_to_bf16".to_string(), fp32_to_bf16 as Binary<B>);

    primops.insert("fp_rem".to_string(), fp_rem as Binary<B>);
    primops.insert("fp_min".to_string(), fp_min as Binary<B>);
    primops.insert("fp_max".to_string(), fp_max as Binary<B>);

    primops.insert("fp_lteq".to_string(), fp_lteq as Binary<B>);
    primops.insert("fp_lt".to_string(), fp_lt as Binary<B>);
    primops.insert("fp_gteq".to_string(), fp_gteq as Binary<B>);
    primops.insert("fp_gt".to_string(), fp_gt as Binary<B>);
    primops.insert("fp_eq".to_string(), fp_eq as Binary<B>);
    primops
}

pub fn variadic_primops<B: BV>() -> HashMap<String, Variadic<B>> {
    let mut primops = HashMap::new();
    primops.insert("fp_add".to_string(), fp_add as Variadic<B>);
    primops.insert("fp_sub".to_string(), fp_sub as Variadic<B>);
    primops.insert("fp_mul".to_string(), fp_mul as Variadic<B>);
    primops.insert("fp_div".to_string(), fp_div as Variadic<B>);
    primops.insert("fp_fma".to_string(), fp_fma as Variadic<B>);
    primops
}

#[cfg(test)]
mod generic_float_tests {
    use super::*;
    use crate::bitvector::b129::B129;
    use crate::bitvector::b64::B64;
    use crate::ir::BitsSegment;
    use crate::ir::{Instr, Name};
    use crate::primop_util::{ite, smt_value};
    use crate::smt::{configure_tastic, Config, Context, SmtResult, Tactic};

    fn assert_bits128(solver: &mut Solver<B129>, value: Val<B129>, expected: B129) {
        let Val::Symbolic(sym) = value else { panic!("expected symbolic result") };
        let info = SourceLoc::unknown();
        assert!(matches!(solver.scalar_sort(sym), Some(Ty::BitVec(128))));
        assert_eq!(solver.check_sat(info), SmtResult::Sat);
        let differs = Exp::Neq(Box::new(Exp::Var(sym)), Box::new(Exp::Bits(expected.to_vec())));
        assert_eq!(solver.check_sat_with(&differs, info), SmtResult::Unsat);
    }

    fn assert_bits(solver: &mut Solver<B64>, value: Val<B64>, expected: u64, width: u32) {
        let Val::Symbolic(sym) = value else { panic!("expected symbolic result") };
        let info = SourceLoc::unknown();
        assert_eq!(solver.check_sat(info), SmtResult::Sat);
        let differs = Exp::Neq(Box::new(Exp::Var(sym)), Box::new(Exp::Bits64(B64::new(expected, width))));
        assert_eq!(solver.check_sat_with(&differs, info), SmtResult::Unsat);
    }

    #[test]
    fn from_ieee_accepts_concrete_and_mixed_bits() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let concrete = fp32_from_ieee(Val::Bits(B64::new(0x3f80_0000, 32)), &mut solver, info).unwrap();
        assert!(matches!(concrete, Val::Symbolic(_)));
        let mid = solver.declare_const(Ty::BitVec(16), info);
        solver.assert(Exp::Eq(Box::new(Exp::Var(mid)), Box::new(Exp::Bits64(B64::new(0x0000, 16)))));
        let mixed = Val::MixedBits(vec![BitsSegment::Concrete(B64::new(0x3f80, 16)), BitsSegment::Symbolic(mid)]);
        let mixed_fp = fp32_from_ieee(mixed, &mut solver, info).unwrap();
        assert!(matches!(mixed_fp, Val::Symbolic(_)));
        let concrete_bits = fp32_to_ieee(concrete, &mut solver, info).unwrap();
        let mixed_bits = fp32_to_ieee(mixed_fp, &mut solver, info).unwrap();
        assert_bits(&mut solver, concrete_bits, 0x3f80_0000, 32);
        assert_bits(&mut solver, mixed_bits, 0x3f80_0000, 32);
    }

    #[test]
    fn from_integer_accepts_concrete_bits() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let rm = round_nearest_ties_to_even(Val::Unit, &mut solver, info).unwrap();
        let signed = fp32_from_signed(rm.clone(), Val::Bits(B64::new(0xffff_ffff, 32)), &mut solver, info).unwrap();
        let unsigned = fp32_from_unsigned(rm.clone(), Val::Bits(B64::new(0xffff_ffff, 32)), &mut solver, info).unwrap();
        let symbolic = solver.declare_const(Ty::BitVec(32), info);
        solver.assert(Exp::Eq(Box::new(Exp::Var(symbolic)), Box::new(Exp::Bits64(B64::new(0xffff_ffff, 32)))));
        let signed_symbolic = fp32_from_signed(rm.clone(), Val::Symbolic(symbolic), &mut solver, info).unwrap();
        let low = solver.declare_const(Ty::BitVec(16), info);
        solver.assert(Exp::Eq(Box::new(Exp::Var(low)), Box::new(Exp::Bits64(B64::new(0xffff, 16)))));
        let mixed = Val::MixedBits(vec![BitsSegment::Concrete(B64::new(0xffff, 16)), BitsSegment::Symbolic(low)]);
        let unsigned_mixed = fp32_from_unsigned(rm, mixed, &mut solver, info).unwrap();
        for value in [signed, signed_symbolic] {
            let bits = fp32_to_ieee(value, &mut solver, info).unwrap();
            assert_bits(&mut solver, bits, 0xbf80_0000, 32);
        }
        for value in [unsigned, unsigned_mixed] {
            let bits = fp32_to_ieee(value, &mut solver, info).unwrap();
            assert_bits(&mut solver, bits, 0x4f80_0000, 32);
        }
    }

    #[test]
    fn generic_interface_registers_outputs() {
        let unary = unary_primops::<B64>();
        let binary = binary_primops::<B64>();
        assert_eq!(unary.len(), 46);
        assert_eq!(binary.len(), 31);
        assert_eq!(variadic_primops::<B64>().len(), 5);
        for width in [16, 32, 64, 128] {
            assert!(unary.contains_key(&format!("fp{}_to_ieee", width)));
            assert!(binary.contains_key(&format!("fp_to_unsigned{}", width)));
        }
        assert!(binary.contains_key("fp32_to_bf16"));
    }

    #[test]
    fn mismatched_sorts_fail_as_type_errors() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let bv = solver.declare_const(Ty::BitVec(32), info);
        let boolean = solver.declare_const(Ty::Bool, info);
        assert!(matches!(fp16_from_ieee(Val::Symbolic(bv), &mut solver, info), Err(ExecError::Type(..))));
        assert!(matches!(fp32_from_ieee(Val::Symbolic(boolean), &mut solver, info), Err(ExecError::Type(..))));
        assert!(matches!(fp_abs(Val::Symbolic(bv), &mut solver, info), Err(ExecError::Type(..))));
        let fp32 = fp32_from_ieee(Val::Bits(B64::new(0x3f80_0000, 32)), &mut solver, info).unwrap();
        let fp64 = fp64_from_ieee(Val::Bits(B64::new(0x3ff0_0000_0000_0000, 64)), &mut solver, info).unwrap();
        let rm = round_nearest_ties_to_even(Val::Unit, &mut solver, info).unwrap();
        assert!(matches!(fp16_to_ieee(fp32.clone(), &mut solver, info), Err(ExecError::Type(..))));
        assert!(matches!(fp32_to_bf16(rm.clone(), fp64.clone(), &mut solver, info), Err(ExecError::Type(..))));
        assert!(matches!(fp_sqrt(Val::Symbolic(boolean), fp32.clone(), &mut solver, info), Err(ExecError::Type(..))));
        assert!(matches!(
            fp_to_unsigned32(Val::Symbolic(bv), fp32.clone(), &mut solver, info),
            Err(ExecError::Type(..))
        ));
        assert!(matches!(fp_eq(fp32.clone(), fp64.clone(), &mut solver, info), Err(ExecError::Type(..))));
        assert!(matches!(
            fp32_from_signed(rm.clone(), Val::Symbolic(boolean), &mut solver, info),
            Err(ExecError::Type(..))
        ));
        assert!(matches!(
            fp32_from_unsigned(rm.clone(), Val::Bits(B64::zeros(0)), &mut solver, info),
            Err(ExecError::Type(..))
        ));
        assert!(matches!(fp32_from_ieee(Val::MixedBits(vec![]), &mut solver, info), Err(ExecError::Type(..))));
        assert!(matches!(
            fp32_from_ieee(
                Val::MixedBits(vec![BitsSegment::Concrete(B64::zeros(0)), BitsSegment::Symbolic(bv)]),
                &mut solver,
                info
            ),
            Err(ExecError::Type(..))
        ));
        assert!(matches!(
            fp32_from_ieee(
                Val::MixedBits(vec![BitsSegment::Concrete(B64::new(0, 16)), BitsSegment::Symbolic(boolean)]),
                &mut solver,
                info
            ),
            Err(ExecError::Type(..))
        ));
        let ret_ty = crate::ir::Ty::Unit;
        let instrs: [Instr<Name, B64>; 0] = [];
        let mut frame = LocalFrame::new(Name::from_u32(1), &[], &ret_ty, None, &instrs);
        assert!(matches!(
            fp_add(vec![rm.clone(), fp32.clone(), fp64.clone()], &mut solver, &mut frame, info),
            Err(ExecError::Type(..))
        ));
        assert!(matches!(
            fp_fma(vec![rm, fp32.clone(), fp32, fp64], &mut solver, &mut frame, info),
            Err(ExecError::Type(..))
        ));
    }

    #[test]
    fn ieee_roundtrip_and_comparisons() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        for bits in [0_u64, 0x8000_0000, 0x3f80_0000, 0x7f80_0000] {
            let fp = fp32_from_ieee(Val::Bits(B64::new(bits, 32)), &mut solver, info).unwrap();
            let output = fp32_to_ieee(fp, &mut solver, info).unwrap();
            assert_bits(&mut solver, output, bits, 32);
        }
        let positive_zero = fp32_from_ieee(Val::Bits(B64::new(0, 32)), &mut solver, info).unwrap();
        let negative_zero = fp32_from_ieee(Val::Bits(B64::new(0x8000_0000, 32)), &mut solver, info).unwrap();
        let equal_zero = fp_eq(positive_zero, negative_zero, &mut solver, info).unwrap();
        let Val::Symbolic(eq) = equal_zero else { panic!("expected symbolic comparison") };
        assert_eq!(solver.check_sat_with(&Exp::Not(Box::new(Exp::Var(eq))), info), SmtResult::Unsat);
        let nan = fp32_from_ieee(Val::Bits(B64::new(0x7fc0_0001, 32)), &mut solver, info).unwrap();
        let nan_equal = fp_eq(nan.clone(), nan.clone(), &mut solver, info).unwrap();
        let Val::Symbolic(eq) = nan_equal else { panic!("expected symbolic comparison") };
        assert_eq!(solver.check_sat_with(&Exp::Var(eq), info), SmtResult::Unsat);
        let nan_bits = fp32_to_ieee(nan, &mut solver, info).unwrap();
        let Val::Symbolic(nan_bits) = nan_bits else { panic!("expected symbolic bits") };
        assert!(matches!(solver.scalar_sort(nan_bits), Some(Ty::BitVec(32))));
    }

    #[test]
    fn unsigned_conversion_and_bf16_result() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let rm = round_nearest_ties_to_even(Val::Unit, &mut solver, info).unwrap();
        let one = fp32_from_ieee(Val::Bits(B64::new(0x3f80_0000, 32)), &mut solver, info).unwrap();
        let integer = fp_to_unsigned32(rm.clone(), one.clone(), &mut solver, info).unwrap();
        assert_bits(&mut solver, integer, 1, 32);
        let integer16 = fp_to_unsigned16(rm.clone(), one.clone(), &mut solver, info).unwrap();
        assert_bits(&mut solver, integer16, 1, 16);
        let large = fp64_from_ieee(Val::Bits(B64::new(123_456_789_f64.to_bits(), 64)), &mut solver, info).unwrap();
        let integer64 = fp_to_unsigned64(rm.clone(), large, &mut solver, info).unwrap();
        assert_bits(&mut solver, integer64, 123_456_789, 64);
        let bf16 = fp32_to_bf16(rm, one, &mut solver, info).unwrap();
        assert_bits(&mut solver, bf16, 0x3f80, 16);
    }

    #[test]
    fn f128_and_integer_128_keep_their_widths() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B129>::new(&ctx);
        let info = SourceLoc::unknown();
        let rm = round_nearest_ties_to_even(Val::Unit, &mut solver, info).unwrap();
        let sign_bit = B129::new(0x8000_0000_0000_0000, 64).append(B129::new(0, 64)).unwrap();
        let positive_fp_bits = B129::new(0x407e_0000_0000_0000, 64).append(B129::new(0, 64)).unwrap();
        let negative_fp_bits = B129::new(0xc07e_0000_0000_0000, 64).append(B129::new(0, 64)).unwrap();
        let fp = fp128_from_ieee(Val::Bits(positive_fp_bits), &mut solver, info).unwrap();
        let roundtrip = fp128_to_ieee(fp, &mut solver, info).unwrap();
        assert_bits128(&mut solver, roundtrip, positive_fp_bits);
        let positive = fp128_from_unsigned(rm.clone(), Val::Bits(sign_bit), &mut solver, info).unwrap();
        let positive_bits = fp128_to_ieee(positive.clone(), &mut solver, info).unwrap();
        assert_bits128(&mut solver, positive_bits, positive_fp_bits);
        let unsigned = fp_to_unsigned128(rm.clone(), positive, &mut solver, info).unwrap();
        assert_bits128(&mut solver, unsigned, sign_bit);
        let negative = fp128_from_signed(rm.clone(), Val::Bits(sign_bit), &mut solver, info).unwrap();
        let negative_bits = fp128_to_ieee(negative.clone(), &mut solver, info).unwrap();
        assert_bits128(&mut solver, negative_bits, negative_fp_bits);
        let signed = fp_to_signed128(rm, negative, &mut solver, info).unwrap();
        assert_bits128(&mut solver, signed, sign_bit);
    }

    #[test]
    fn symbolic_rounding_mode_matches_all_five_concrete_modes() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let symbolic_rm = solver.declare_const(Ty::RoundingMode, info);
        let modes: [fn(Val<B64>, &mut Solver<B64>, SourceLoc) -> Result<Val<B64>, ExecError>; 5] = [
            round_nearest_ties_to_even::<B64>,
            round_nearest_ties_to_away::<B64>,
            round_toward_positive::<B64>,
            round_toward_negative::<B64>,
            round_toward_zero::<B64>,
        ];
        let cases = [
            (false, 0x0100_0001, [0x4b80_0000, 0x4b80_0001, 0x4b80_0001, 0x4b80_0000, 0x4b80_0000]),
            (false, 0x0100_0003, [0x4b80_0002, 0x4b80_0002, 0x4b80_0002, 0x4b80_0001, 0x4b80_0001]),
            (true, 0xfeff_ffff, [0xcb80_0000, 0xcb80_0001, 0xcb80_0000, 0xcb80_0001, 0xcb80_0000]),
        ];
        for (signed, input, expected_by_mode) in cases {
            let bits = Val::Bits(B64::new(input, 32));
            let fp = if signed {
                fp32_from_signed(Val::Symbolic(symbolic_rm), bits, &mut solver, info).unwrap()
            } else {
                fp32_from_unsigned(Val::Symbolic(symbolic_rm), bits, &mut solver, info).unwrap()
            };
            let output = fp32_to_ieee(fp, &mut solver, info).unwrap();
            let Val::Symbolic(output) = output else { panic!("expected symbolic bits") };
            for (mode, expected) in modes.iter().zip(expected_by_mode) {
                let Val::Symbolic(concrete_rm) = mode(Val::Unit, &mut solver, info).unwrap() else {
                    panic!("expected RM")
                };
                let selected = Exp::Eq(Box::new(Exp::Var(symbolic_rm)), Box::new(Exp::Var(concrete_rm)));
                assert_eq!(solver.check_sat_with(&selected, info), SmtResult::Sat);
                let differs = Exp::And(
                    Box::new(selected),
                    Box::new(Exp::Neq(Box::new(Exp::Var(output)), Box::new(Exp::Bits64(B64::new(expected, 32))))),
                );
                assert_eq!(solver.check_sat_with(&differs, info), SmtResult::Unsat);
            }
        }
    }

    #[test]
    fn symbolic_ite_selects_fp_rm_bv_and_bool() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let condition = solver.declare_const(Ty::Bool, info);
        let fp_one = fp32_from_ieee(Val::Bits(B64::new(0x3f80_0000, 32)), &mut solver, info).unwrap();
        let fp_two = fp32_from_ieee(Val::Bits(B64::new(0x4000_0000, 32)), &mut solver, info).unwrap();
        let rne = round_nearest_ties_to_even(Val::Unit, &mut solver, info).unwrap();
        let rtz = round_toward_zero(Val::Unit, &mut solver, info).unwrap();
        let choices = [
            (fp_one, fp_two),
            (rne, rtz),
            (Val::Bits(B64::new(0xaa, 8)), Val::Bits(B64::new(0x55, 8))),
            (Val::Bool(true), Val::Bool(false)),
        ];
        for (when_true, when_false) in choices {
            let selected = ite(&Val::Symbolic(condition), &when_true, &when_false, &mut solver, info).unwrap();
            let Val::Symbolic(selected) = selected else { panic!("expected symbolic ITE") };
            for (choice, expected) in [(true, &when_true), (false, &when_false)] {
                let branch = Exp::Eq(Box::new(Exp::Var(condition)), Box::new(Exp::Bool(choice)));
                assert_eq!(solver.check_sat_with(&branch, info), SmtResult::Sat);
                let differs = Exp::And(
                    Box::new(branch),
                    Box::new(Exp::Neq(Box::new(Exp::Var(selected)), Box::new(smt_value(expected, info).unwrap()))),
                );
                assert_eq!(solver.check_sat_with(&differs, info), SmtResult::Unsat);
            }
        }
    }

    #[test]
    fn fma_rounds_only_once() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let rm = round_nearest_ties_to_even(Val::Unit, &mut solver, info).unwrap();
        let a = fp32_from_ieee(Val::Bits(B64::new(0x3f80_0001, 32)), &mut solver, info).unwrap();
        let b = fp32_from_ieee(Val::Bits(B64::new(0x3f7f_fffe, 32)), &mut solver, info).unwrap();
        let neg_one = fp32_from_ieee(Val::Bits(B64::new(0xbf80_0000, 32)), &mut solver, info).unwrap();
        let ret_ty = crate::ir::Ty::Unit;
        let instrs: [Instr<Name, B64>; 0] = [];
        let mut frame = LocalFrame::new(Name::from_u32(1), &[], &ret_ty, None, &instrs);
        let fused = fp_fma(vec![rm, a, b, neg_one], &mut solver, &mut frame, info).unwrap();
        let bits = fp32_to_ieee(fused, &mut solver, info).unwrap();
        assert_bits(&mut solver, bits, 0xa880_0000, 32);
    }
}
