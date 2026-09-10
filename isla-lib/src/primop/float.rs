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
//! Using floating point types requires that the Solver is
//! instantiated with the `ALL` theory rather than just
//! bitvectors+datatypes as per usual.

use std::collections::HashMap;

use crate::bitvector::b64::B64;
use crate::bitvector::BV;
use crate::error::ExecError;
use crate::executor::LocalFrame;
use crate::ir::{FPTy, Val};
use crate::smt::smtlib::*;
use crate::smt::*;
use crate::source_loc::SourceLoc;

use super::{Binary, Unary, Variadic};

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
            match v {
                Val::Symbolic(v) => solver.define_const(Exp::FPUnary($op, Box::new(Exp::Var(v))), info).into(),
                _ => Err(ExecError::Type(stringify!($f).to_string(), info)),
            }
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

fp_unary_primop!(fp16_from_ieee, {
    let ty = FPTy::fp16();
    FPUnary::FromIEEE(ty.exponent_width(), ty.significand_width())
});
fp_unary_primop!(fp32_from_ieee, {
    let ty = FPTy::fp32();
    FPUnary::FromIEEE(ty.exponent_width(), ty.significand_width())
});
fp_unary_primop!(fp64_from_ieee, {
    let ty = FPTy::fp64();
    FPUnary::FromIEEE(ty.exponent_width(), ty.significand_width())
});
fp_unary_primop!(fp128_from_ieee, {
    let ty = FPTy::fp128();
    FPUnary::FromIEEE(ty.exponent_width(), ty.significand_width())
});

macro_rules! fp_rounding_unary_primop {
    ($f:ident, $op:expr) => {
        pub fn $f<B: BV>(rm: Val<B>, v: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
            match (rm, v) {
                (Val::Symbolic(rm), Val::Symbolic(v)) => solver
                    .define_const(Exp::FPRoundingUnary($op, Box::new(Exp::Var(rm)), Box::new(Exp::Var(v))), info)
                    .into(),
                _ => Err(ExecError::Type(stringify!($f).to_string(), info)),
            }
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

macro_rules! fp_binary_primop {
    ($f:ident, $op:expr) => {
        pub fn $f<B: BV>(
            lhs: Val<B>,
            rhs: Val<B>,
            solver: &mut Solver<B>,
            info: SourceLoc,
        ) -> Result<Val<B>, ExecError> {
            match (lhs, rhs) {
                (Val::Symbolic(lhs), Val::Symbolic(rhs)) => solver
                    .define_const(Exp::FPBinary($op, Box::new(Exp::Var(lhs)), Box::new(Exp::Var(rhs))), info)
                    .into(),
                _ => Err(ExecError::Type(stringify!($f).to_string(), info)),
            }
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
            match (rm, lhs, rhs) {
                (Val::Symbolic(rm), Val::Symbolic(lhs), Val::Symbolic(rhs)) => solver
                    .define_const(
                        Exp::FPRoundingBinary(
                            $op,
                            Box::new(Exp::Var(rm)),
                            Box::new(Exp::Var(lhs)),
                            Box::new(Exp::Var(rhs)),
                        ),
                        info,
                    )
                    .into(),
                _ => Err(ExecError::Type(stringify!($f).to_string(), info)),
            }
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
    match (rm, x, y, z) {
        (Val::Symbolic(rm), Val::Symbolic(x), Val::Symbolic(y), Val::Symbolic(z)) => solver
            .define_const(
                Exp::FPfma(Box::new(Exp::Var(rm)), Box::new(Exp::Var(x)), Box::new(Exp::Var(y)), Box::new(Exp::Var(z))),
                info,
            )
            .into(),
        _ => Err(ExecError::Type("fp_fma".to_string(), info)),
    }
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

// ============================================================================
// SoftFloat helper 绑定（`riscv_*` 浮点外部函数）
//
// rv64d.ir 中 Sail RISC-V 模型以 `val riscv_fXXX... : ...` 声明了一组无函数体的
// 外部函数（Berkeley SoftFloat 包装），形如
//   val zriscv_f32Add : (%bv3, %bv32, %bv32) -> %struct ztuplez3z5bv5_z5bv32
// 即 (舍入模式, IEEE 位, IEEE 位) -> (fflags, 结果位)。符号执行遇到对它们的
// Call 会因找不到函数体而报 NoFunction（见 ir.rs insert_instr_primops 中的
// 上游注释）。这里把它们绑定到 z3 浮点理论（FPA）上：
//
// 语义精确度：
//  * 数值结果：精确（z3 FPA 遵循 IEEE 754 运算语义；NaN/无效场景强制返回
//    规范 NaN（0x7fc00000 等），与 SoftFloat defaultNaN 构建一致）。
//  * NV（无效）与 DZ（除零）：精确（基于 IEEE 位模式的位级判定）。
//  * Add/Sub 的 NX（不精确）：精确 —— 在宽格式（f32→f64，f64→fp128）中重算，
//    指数差 ≤ 宽度阈限时宽格式和精确，往返比较即精确判定；指数差超阈值时
//    结果必为较大操作数本身，仅当另一操作数非零时不精确。
//  * Mul 的 NX：精确 —— 乘积在宽格式中恒精确（2p ≤ 宽格式尾数）。
//  * Sqrt 的 NX：精确 —— 结果平方后与原值比较（平方在宽格式中恒精确）。
//  * 所有转换的 NX：精确 —— 结果经 FromSigned/FromUnsigned 往返比较（整数值
//    的有效位数不会超过源格式精度 p，往返无损）。
//  * FpToI/IToFp 的 OF 与范围 NV：精确 —— 宽格式中与 2^a±2^b 形式的界常数比较
//    （界常数在宽格式中恒可精确表示），逐舍入模式编码。
//  * 二元算术 OF（溢出）：近似 —— isinf(res) 且输入有限。RNE/RMM 下精确；
//    定向舍入（RTZ/RUP/RDN）饱和到最大有限数时漏报（数值结果本身仍精确）。
//  * UF（下溢）：近似 —— issubnormal(res) 且非零。会漏报舍入到零的极小值，
//    且 subnormal 恰好精确时误报。
//  * Div/FMA 的 NX：近似 —— 仅 OF|UF（SMT 浮点理论无精确不精确谓词，宽格式
//    商不可证精确）。
//
// fflags 位序（RISC-V，SoftFloat 同序）：NX=bit0, UF=bit1, OF=bit2, DZ=bit3,
// NV=bit4。
// ============================================================================

use crate::ir::Name;

/// RISC-V rm 编码到 SMT 舍入模式：0=RNE, 1=RTZ, 2=RDN, 3=RUP, 4=RMM。
/// 模型侧 checkrm（Option None 检查）保证到达 helper 的 rm ∈ 0..4，DYN 已被
/// frm 解析，保留编码 5..7 是非法路径，不可能到达这里。
const RM_MODES: [FPRoundingMode; 5] = [
    FPRoundingMode::RoundNearestTiesToEven,
    FPRoundingMode::RoundTowardZero,
    FPRoundingMode::RoundTowardNegative,
    FPRoundingMode::RoundTowardPositive,
    FPRoundingMode::RoundNearestTiesToAway,
];

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum SfFmt {
    F16,
    F32,
    F64,
}

impl SfFmt {
    fn from_name(name: &str) -> Option<Self> {
        match name {
            "f16" | "F16" => Some(SfFmt::F16),
            "f32" | "F32" => Some(SfFmt::F32),
            "f64" | "F64" => Some(SfFmt::F64),
            _ => None,
        }
    }

    fn ebits(self) -> u32 {
        match self {
            SfFmt::F16 => 5,
            SfFmt::F32 => 8,
            SfFmt::F64 => 11,
        }
    }

    fn sbits(self) -> u32 {
        match self {
            SfFmt::F16 => 11,
            SfFmt::F32 => 24,
            SfFmt::F64 => 53,
        }
    }

    fn width(self) -> u32 {
        match self {
            SfFmt::F16 => 16,
            SfFmt::F32 => 32,
            SfFmt::F64 => 64,
        }
    }

    /// 用于重算的宽格式：f16/f32 → f64，f64 → fp128。
    fn wide(self) -> (u32, u32) {
        match self {
            SfFmt::F64 => (15, 113),
            _ => (11, 53),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum SfOp {
    Bin { fmt: SfFmt, op: FPRoundingBinary },
    MulAdd { fmt: SfFmt },
    Sqrt { fmt: SfFmt },
    Cmp { fmt: SfFmt, kind: FPBinary, quiet: bool },
    RoundToInt { fmt: SfFmt },
    FpToI { src: SfFmt, signed: bool, int_width: u32 },
    IFp { signed: bool, int_width: u32, dst: SfFmt },
    FpToFp { src: SfFmt, dst: SfFmt },
    ToBF16,
}

/// 解析解码后的 helper 名（如 `riscv_f32Add`、`riscv_ui64ToF16`）。
pub fn softfloat_dispatch(name: &str) -> Option<SfOp> {
    let rest = name.strip_prefix("riscv_")?;
    if let Some(fmt) = SfFmt::from_name(&rest[..3]) {
        parse_fp_op(fmt, &rest[3..])
    } else {
        parse_int_to_fp(rest)
    }
}

fn parse_fp_op(fmt: SfFmt, rest: &str) -> Option<SfOp> {
    use FPRoundingBinary::*;
    Some(match rest {
        "Add" => SfOp::Bin { fmt, op: Add },
        "Sub" => SfOp::Bin { fmt, op: Sub },
        "Mul" => SfOp::Bin { fmt, op: Mul },
        "Div" => SfOp::Bin { fmt, op: Div },
        "MulAdd" => SfOp::MulAdd { fmt },
        "Sqrt" => SfOp::Sqrt { fmt },
        "Lt" => SfOp::Cmp { fmt, kind: FPBinary::Lt, quiet: false },
        "Lt_quiet" => SfOp::Cmp { fmt, kind: FPBinary::Lt, quiet: true },
        "Le" => SfOp::Cmp { fmt, kind: FPBinary::Leq, quiet: false },
        "Le_quiet" => SfOp::Cmp { fmt, kind: FPBinary::Leq, quiet: true },
        "Eq" => SfOp::Cmp { fmt, kind: FPBinary::Eq, quiet: false },
        "roundToInt" => SfOp::RoundToInt { fmt },
        "ToI32" => SfOp::FpToI { src: fmt, signed: true, int_width: 32 },
        "ToUi32" => SfOp::FpToI { src: fmt, signed: false, int_width: 32 },
        "ToI64" => SfOp::FpToI { src: fmt, signed: true, int_width: 64 },
        "ToUi64" => SfOp::FpToI { src: fmt, signed: false, int_width: 64 },
        "ToF16" if fmt != SfFmt::F16 => SfOp::FpToFp { src: fmt, dst: SfFmt::F16 },
        "ToF32" if fmt != SfFmt::F32 => SfOp::FpToFp { src: fmt, dst: SfFmt::F32 },
        "ToF64" if fmt != SfFmt::F64 => SfOp::FpToFp { src: fmt, dst: SfFmt::F64 },
        "ToBF16" if fmt == SfFmt::F32 => SfOp::ToBF16,
        _ => return None,
    })
}

fn parse_int_to_fp(rest: &str) -> Option<SfOp> {
    let (signed, rest) = match rest.strip_prefix("ui") {
        Some(rest) => (false, rest),
        None => (true, rest.strip_prefix("i")?),
    };
    let (int_width, rest) =
        if let Some(rest) = rest.strip_prefix("32") { (32, rest) } else { (64, rest.strip_prefix("64")?) };
    let dst = SfFmt::from_name(rest.strip_prefix("To")?)?;
    Some(SfOp::IFp { signed, int_width, dst })
}

/// helper 返回值 tuple-struct 在 IR 中的名字（字段名 = 名字 + 序号）。
pub fn softfloat_result_struct(op: SfOp) -> String {
    match op {
        SfOp::Cmp { .. } => "ztuplez3z5bv5_z5bool".to_string(),
        _ => format!("ztuplez3z5bv5_z5bv{}", softfloat_result_width(op)),
    }
}

fn softfloat_result_width(op: SfOp) -> u32 {
    match op {
        SfOp::Bin { fmt, .. } | SfOp::MulAdd { fmt } | SfOp::Sqrt { fmt } | SfOp::RoundToInt { fmt } => fmt.width(),
        SfOp::Cmp { .. } => 1,
        SfOp::FpToI { int_width, .. } => int_width,
        SfOp::IFp { dst, .. } => dst.width(),
        SfOp::FpToFp { dst, .. } => dst.width(),
        SfOp::ToBF16 => 16,
    }
}

// ---------------------------------------------------------------------------
// SMT 表达式小工具
// ---------------------------------------------------------------------------

fn bv(bits: u64, width: u32) -> Exp<Sym> {
    Exp::Bits64(B64::new(bits, width))
}

fn bv_wide(bits: u128, width: u32) -> Exp<Sym> {
    if width <= 64 {
        Exp::Bits64(B64::new(bits as u64, width))
    } else {
        let mut v = vec![false; width as usize];
        for (n, bit) in v.iter_mut().enumerate() {
            *bit = bits >> n & 1 == 1
        }
        Exp::Bits(v)
    }
}

fn bool(b: bool) -> Exp<Sym> {
    Exp::Bool(b)
}

fn and(l: Exp<Sym>, r: Exp<Sym>) -> Exp<Sym> {
    Exp::And(Box::new(l), Box::new(r))
}

fn or(l: Exp<Sym>, r: Exp<Sym>) -> Exp<Sym> {
    Exp::Or(Box::new(l), Box::new(r))
}

fn not(e: Exp<Sym>) -> Exp<Sym> {
    Exp::Not(Box::new(e))
}

fn eq(l: Exp<Sym>, r: Exp<Sym>) -> Exp<Sym> {
    Exp::Eq(Box::new(l), Box::new(r))
}

fn ite(c: Exp<Sym>, t: Exp<Sym>, f: Exp<Sym>) -> Exp<Sym> {
    Exp::Ite(Box::new(c), Box::new(t), Box::new(f))
}

fn fp_ieee_eq(l: Exp<Sym>, r: Exp<Sym>) -> Exp<Sym> {
    Exp::FPBinary(FPBinary::Eq, Box::new(l), Box::new(r))
}

fn fp_pred(p: FPUnary, x: Exp<Sym>) -> Exp<Sym> {
    Exp::FPUnary(p, Box::new(x))
}

fn fp_from_bits(bits: Exp<Sym>, ebits: u32, sbits: u32) -> Exp<Sym> {
    Exp::FPUnary(FPUnary::FromIEEE(ebits, sbits), Box::new(bits))
}

fn fp_to_bits(x: Exp<Sym>, ebits: u32, sbits: u32) -> Exp<Sym> {
    Exp::FPUnary(FPUnary::ToIEEE(ebits, sbits), Box::new(x))
}

fn fp_convert(x: Exp<Sym>, rm: Exp<Sym>, ebits: u32, sbits: u32) -> Exp<Sym> {
    Exp::FPRoundingUnary(FPRoundingUnary::Convert(ebits, sbits), Box::new(rm), Box::new(x))
}

/// 某格式 IEEE 位模式的位域判定。位布局：[sign | exp(ebits) | mantissa(sbits-1)]。
struct FpPat {
    fmt: SfFmt,
}

impl FpPat {
    fn new(fmt: SfFmt) -> Self {
        FpPat { fmt }
    }

    fn exp_field(&self, bits: &Exp<Sym>) -> Exp<Sym> {
        Exp::Extract(self.fmt.width() - 2, self.fmt.sbits() - 1, Box::new(bits.clone()))
    }

    fn man_field(&self, bits: &Exp<Sym>) -> Exp<Sym> {
        Exp::Extract(self.fmt.sbits() - 2, 0, Box::new(bits.clone()))
    }

    fn sign_bit(&self, bits: &Exp<Sym>) -> Exp<Sym> {
        Exp::Extract(self.fmt.width() - 1, self.fmt.width() - 1, Box::new(bits.clone()))
    }

    fn exp_ones(&self) -> Exp<Sym> {
        bv((1 << self.fmt.ebits()) - 1, self.fmt.ebits())
    }

    fn is_nan(&self, bits: &Exp<Sym>) -> Exp<Sym> {
        and(
            eq(self.exp_field(bits), self.exp_ones()),
            Exp::Neq(Box::new(self.man_field(bits)), Box::new(bv(0, self.fmt.sbits() - 1))),
        )
    }

    /// sNaN：NaN 且静默位（尾数最高位）为 0。
    fn is_snan(&self, bits: &Exp<Sym>) -> Exp<Sym> {
        let quiet_bit = Exp::Extract(self.fmt.sbits() - 2, self.fmt.sbits() - 2, Box::new(bits.clone()));
        and(self.is_nan(bits), eq(quiet_bit, bv(0, 1)))
    }

    fn is_inf(&self, bits: &Exp<Sym>) -> Exp<Sym> {
        and(eq(self.exp_field(bits), self.exp_ones()), eq(self.man_field(bits), bv(0, self.fmt.sbits() - 1)))
    }

    fn is_zero(&self, bits: &Exp<Sym>) -> Exp<Sym> {
        and(eq(self.exp_field(bits), bv(0, self.fmt.ebits())), eq(self.man_field(bits), bv(0, self.fmt.sbits() - 1)))
    }

    /// 规范 NaN 位模式（defaultNaN 构建的 SoftFloat 行为）：指数全 1、静默位 1。
    fn canonical_nan(&self) -> Exp<Sym> {
        let e = self.fmt.ebits();
        let s = self.fmt.sbits();
        bv(((1 << e) - 1) << (s - 1) | 1 << (s - 2), self.fmt.width())
    }
}

/// 把 Val（符号或具体位）转成 SMT 位向量表达式。
fn bits_exp<B: BV>(val: &Val<B>, what: &str, info: SourceLoc) -> Result<Exp<Sym>, ExecError> {
    match val {
        Val::Symbolic(v) => Ok(Exp::Var(*v)),
        // SoftFloat helper 的实参宽度至多 64 位（rm/IEEE 位/整数位）
        Val::Bits(bv) => Ok(Exp::Bits64(B64::new(bv.lower_u64(), bv.len()))),
        Val::Bool(b) => Ok(bool(*b)),
        v => Err(ExecError::Type(format!("softfloat {}: 不支持的参数类型 {:?}", what, v), info)),
    }
}

/// 舍入模式 Val → SMT 舍入模式表达式。符号 rm 时显式断言 rm ∈ 0..4（模型
/// checkrm 已保证的不变式），并用 ite 链表达总函数。
fn rm_smt<B: BV>(rm: &Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Exp<Sym>, ExecError> {
    match rm {
        Val::Bits(bv) => {
            let v = bv.lower_u64();
            Ok(Exp::FPRoundingMode(*RM_MODES.get(v as usize).unwrap_or_else(|| {
                panic!("softfloat: 非法舍入模式 {}（checkrm 保证 rm ∈ 0..4，到达此处为模型不变量违反）", v)
            })))
        }
        Val::Symbolic(v) => {
            let rmv = Exp::Var(*v);
            let domain =
                RM_MODES.iter().enumerate().map(|(k, _)| eq(rmv.clone(), bv(k as u64, 3))).fold(bool(false), or);
            solver.assert(domain);
            Ok([
                eq(rmv.clone(), bv(4, 3)),
                eq(rmv.clone(), bv(3, 3)),
                eq(rmv.clone(), bv(2, 3)),
                eq(rmv.clone(), bv(1, 3)),
            ]
            .iter()
            .cloned()
            .fold(Exp::FPRoundingMode(RM_MODES[0]), |acc, c| ite(c, acc, Exp::FPRoundingMode(RM_MODES[0]))))
        }
        v => Err(ExecError::Type(format!("softfloat: 不支持的舍入模式参数 {:?}", v), info)),
    }
}

/// rm 位向量等于 k 的布尔表达式。
fn rm_is(rm: &Exp<Sym>, k: u64) -> Exp<Sym> {
    eq(rm.clone(), bv(k, 3))
}

/// fflags 位向量组装。
fn flags_word(nv: Exp<Sym>, dz: Exp<Sym>, of: Exp<Sym>, uf: Exp<Sym>, nx: Exp<Sym>) -> Exp<Sym> {
    fn bit(index: u32, flag: Exp<Sym>) -> Exp<Sym> {
        ite(flag, bv(1 << index, 5), bv(0, 5))
    }
    Exp::Bvor(
        Box::new(Exp::Bvor(Box::new(bit(0, nx)), Box::new(bit(1, uf)))),
        Box::new(Exp::Bvor(Box::new(Exp::Bvor(Box::new(bit(2, of)), Box::new(bit(3, dz)))), Box::new(bit(4, nv)))),
    )
}

// ---------------------------------------------------------------------------
// NX（不精确）的精确编码：宽格式重算 / 往返比较
// ---------------------------------------------------------------------------

/// 加法 NX：宽格式和精确 ⇔ 指数差 ≤ 阈值；往返比较。超阈值时结果为较大操作数，
/// 仅当另一操作数非零时不精确。
fn add_nx(fmt: SfFmt, ra: &Exp<Sym>, rb: &Exp<Sym>, a: &Exp<Sym>, b: &Exp<Sym>, rm: &Exp<Sym>) -> Exp<Sym> {
    let pat = FpPat::new(fmt);
    let (we, ws) = fmt.wide();
    let aw = fp_convert(a.clone(), rm.clone(), we, ws);
    let bw = fp_convert(b.clone(), rm.clone(), we, ws);
    let wide = Exp::FPRoundingBinary(FPRoundingBinary::Add, Box::new(rm.clone()), Box::new(aw), Box::new(bw));
    let back = fp_convert(fp_convert(wide.clone(), rm.clone(), fmt.ebits(), fmt.sbits()), rm.clone(), we, ws);
    let base = not(fp_ieee_eq(back, wide));
    let threshold = ws - fmt.sbits() - 1;
    let far = and(
        and(
            Exp::Bvugt(Box::new(exp_diff(fmt, ra, rb)), Box::new(bv(threshold as u64, fmt.ebits() + 1))),
            and(not(pat.is_zero(ra)), not(pat.is_zero(rb))),
        ),
        and(not(pat.is_nan(ra)), not(pat.is_inf(ra))),
    );
    or(base, far)
}

/// 无偏指数差（ebits+1 位）。用 `exp_field==0 时记 1，否则记 field` 的偏置平移
/// 后作差，等价于真实指数差（含 subnormal）。
fn exp_diff(fmt: SfFmt, ra: &Exp<Sym>, rb: &Exp<Sym>) -> Exp<Sym> {
    let adj = |bits: &Exp<Sym>| -> Exp<Sym> {
        let field = FpPat::new(fmt).exp_field(bits);
        ite(eq(field.clone(), bv(0, fmt.ebits())), bv(1, fmt.ebits()), field)
    };
    let ea = Exp::ZeroExtend(1, Box::new(adj(ra)));
    let eb = Exp::ZeroExtend(1, Box::new(adj(rb)));
    ite(
        Exp::Bvuge(Box::new(ea.clone()), Box::new(eb.clone())),
        Exp::Bvsub(Box::new(ea.clone()), Box::new(eb.clone())),
        Exp::Bvsub(Box::new(eb), Box::new(ea)),
    )
}

/// 乘法 NX：乘积在宽格式中恒精确（f16×f16→22 位、f32×f32→48 位 ≤ f64 的 53；
/// f64×f64→106 位 ≤ fp128 的 113；指数范围同样被宽格式覆盖）。
fn mul_nx(fmt: SfFmt, a: &Exp<Sym>, b: &Exp<Sym>, rm: &Exp<Sym>) -> Exp<Sym> {
    let (we, ws) = fmt.wide();
    let wide = Exp::FPRoundingBinary(
        FPRoundingBinary::Mul,
        Box::new(rm.clone()),
        Box::new(fp_convert(a.clone(), rm.clone(), we, ws)),
        Box::new(fp_convert(b.clone(), rm.clone(), we, ws)),
    );
    let back = fp_convert(fp_convert(wide.clone(), rm.clone(), fmt.ebits(), fmt.sbits()), rm.clone(), we, ws);
    not(fp_ieee_eq(back, wide))
}

/// 开方 NX：结果平方后与原值比较（平方在宽格式中恒精确；精确开方 ⇔ 结果²=原值）。
fn sqrt_nx(fmt: SfFmt, x: &Exp<Sym>, res: &Exp<Sym>) -> Exp<Sym> {
    let (we, ws) = fmt.wide();
    let rne = Exp::FPRoundingMode(FPRoundingMode::RoundNearestTiesToEven);
    let rw = fp_convert(res.clone(), rne.clone(), we, ws);
    let squared = Exp::FPRoundingBinary(FPRoundingBinary::Mul, Box::new(rne), Box::new(rw.clone()), Box::new(rw));
    let xw = fp_convert(x.clone(), Exp::FPRoundingMode(FPRoundingMode::RoundNearestTiesToEven), we, ws);
    and(
        not(fp_pred(FPUnary::IsNaN, x.clone())),
        and(not(fp_pred(FPUnary::IsInfinite, x.clone())), not(fp_ieee_eq(squared, xw))),
    )
}

// ---------------------------------------------------------------------------
// FpToI / IFp 的界常数与范围判定
// ---------------------------------------------------------------------------

/// ±2^k 的宽格式 IEEE 位模式。
fn wide_pow(we: u32, ws: u32, sign: bool, k: i32) -> Exp<Sym> {
    let bias = (1 << (we - 1)) - 1;
    let field = (k + bias) as u128;
    let raw = (sign as u128) << (we + ws - 1) | field << (ws - 1);
    fp_from_bits(bv_wide(raw, we + ws), we, ws)
}

/// ±(2^hi - 2^lo)（sub）或 ±(2^hi + 2^lo)（plus，hi > lo）的宽格式 IEEE 位模式。
/// 值 = 2^lo·(2^j ∓/± 1)，j = hi - lo；尾数域恒可精确容纳（j ≤ ws-1）。
fn wide_bound(we: u32, ws: u32, sign: bool, hi: i32, lo: i32, sub: bool) -> Exp<Sym> {
    let j = (hi - lo) as u32;
    let bias = (1 << (we - 1)) - 1;
    // sub：值 = 2^(hi-1)·(2 - 2^-(j-1))，指数域 hi-1+bias，尾数 j-1 个 1；
    // plus：值 = 2^hi·(1 + 2^-j)，指数域 hi+bias，尾数在 ws-1-j 位
    let field = if sub { (hi - 1 + bias) as u128 } else { (hi + bias) as u128 };
    let mantissa = if sub { ((1u128 << (j - 1)) - 1) << (ws - j) } else { 1u128 << (ws - 1 - j) };
    let raw = (sign as u128) << (we + ws - 1) | field << (ws - 1) | mantissa;
    fp_from_bits(bv_wide(raw, we + ws), we, ws)
}

#[derive(Copy, Clone)]
enum Bound {
    /// ±2^k
    Pow { sign: bool, k: i32 },
    /// ±(2^hi ± 2^lo)
    Diff { sign: bool, hi: i32, lo: i32, sub: bool },
}

impl Bound {
    fn to_exp(self, we: u32, ws: u32) -> Exp<Sym> {
        match self {
            Bound::Pow { sign, k } => wide_pow(we, ws, sign, k),
            Bound::Diff { sign, hi, lo, sub } => wide_bound(we, ws, sign, hi, lo, sub),
        }
    }
}

#[derive(Copy, Clone)]
enum Cmp {
    Geq,
    Gt,
    Leq,
    Lt,
}

impl Cmp {
    fn apply(self, x: &Exp<Sym>, bound: Exp<Sym>) -> Exp<Sym> {
        let op = match self {
            Cmp::Geq => FPBinary::Geq,
            Cmp::Gt => FPBinary::Gt,
            Cmp::Leq => FPBinary::Leq,
            Cmp::Lt => FPBinary::Lt,
        };
        Exp::FPBinary(op, Box::new(x.clone()), Box::new(bound))
    }
}

/// 整数转换的范围 NV 判定。在宽格式中与界常数比较（x 先精确拓宽），界为
/// ±(2^a ± 2^b) 形式、在宽格式中恒可精确表示，逐舍入模式给出精确条件：
///  * RNE：平局靠偶（正界含平局点 NV、负界不含——平局恰好舍到 -2^(W-1) 合法）；
///  * RMM/RNA：平局离零（正负界都含平局点）；
///  * RTZ：截断（|x| 达到 2^(W-1)（有符号）/2^W（无符号）即 NV）；
///  * RDN/RUP：方向性（各自只在一侧收紧到最近可表示整数界）。
fn conv_range_nv(fmt: SfFmt, x_wide: &Exp<Sym>, rm: &Exp<Sym>, signed: bool, int_width: u32) -> Exp<Sym> {
    let (we, ws) = fmt.wide();
    let w = int_width as i32;
    let p = fmt.sbits() as i32;
    // 每个模式给出 (正侧 NV 条件, 负侧 NV 条件)；界为 ±(2^a ± 2^b)，在宽格式中
    // 恒可精确表示，比较即精确判定。
    let table: [(u64, (Cmp, Bound), (Cmp, Bound)); 5] = if signed {
        [
            (
                0,
                (Cmp::Geq, Bound::Diff { sign: false, hi: w - 1, lo: w - p - 2, sub: true }),
                (Cmp::Lt, Bound::Diff { sign: true, hi: w - 1, lo: w - p - 2, sub: false }),
            ),
            (1, (Cmp::Geq, Bound::Pow { sign: false, k: w - 1 }), (Cmp::Lt, Bound::Pow { sign: true, k: w - 1 })),
            (2, (Cmp::Geq, Bound::Pow { sign: false, k: w - 1 }), (Cmp::Lt, Bound::Pow { sign: true, k: w - 1 })),
            (
                3,
                (Cmp::Gt, Bound::Diff { sign: false, hi: w - 1, lo: w - 1 - p, sub: true }),
                (Cmp::Lt, Bound::Diff { sign: true, hi: w - 1, lo: -1, sub: false }),
            ),
            (
                4,
                (Cmp::Geq, Bound::Diff { sign: false, hi: w - 1, lo: w - p - 2, sub: true }),
                (Cmp::Leq, Bound::Diff { sign: true, hi: w - 1, lo: w - p - 2, sub: false }),
            ),
        ]
    } else {
        [
            (
                0,
                (Cmp::Geq, Bound::Diff { sign: false, hi: w, lo: w - p - 1, sub: true }),
                (Cmp::Lt, Bound::Pow { sign: true, k: -1 }),
            ),
            (1, (Cmp::Geq, Bound::Pow { sign: false, k: w }), (Cmp::Leq, Bound::Pow { sign: true, k: 0 })),
            (2, (Cmp::Geq, Bound::Pow { sign: false, k: w }), (Cmp::Lt, Bound::Pow { sign: false, k: 0 })),
            (
                3,
                (Cmp::Gt, Bound::Diff { sign: false, hi: w, lo: 0, sub: true }),
                (Cmp::Leq, Bound::Pow { sign: true, k: 0 }),
            ),
            (
                4,
                (Cmp::Geq, Bound::Diff { sign: false, hi: w, lo: w - p - 1, sub: true }),
                (Cmp::Leq, Bound::Pow { sign: true, k: -1 }),
            ),
        ]
    };
    table
        .iter()
        .map(|(mode, (pos_op, pos_bound), (neg_op, neg_bound))| {
            let cond =
                or(pos_op.apply(x_wide, pos_bound.to_exp(we, ws)), neg_op.apply(x_wide, neg_bound.to_exp(we, ws)));
            and(rm_is(rm, *mode), cond)
        })
        .fold(bool(false), or)
}

/// IToFp 的 OF 判定（仅 f16 目标可能溢出——i32/i64 的量级都落在 f32/f64 的
/// 有限范围内）。整数源在位级与阈值比较，逐舍入模式精确编码：
///  * RNE/RMM：|i| ≥ 65520（平局点，向上/靠偶都进入 inf）；
///  * RTZ：|i| ≥ 65536（截断饱和到 65504 不算溢出）；
///  * RDN：i ≥ 65536 或 i ≤ -65520（负方向溢出更早，正方向截断式饱和）；
///  * RUP：镜像 RDN。
fn itofp_of(dst: SfFmt, signed: bool, int_width: u32, i: &Exp<Sym>, rm: &Exp<Sym>) -> Exp<Sym> {
    if dst != SfFmt::F16 {
        return bool(false);
    }
    let wide_i = if signed {
        Exp::SignExtend(64 - int_width, Box::new(i.clone()))
    } else {
        Exp::ZeroExtend(64 - int_width, Box::new(i.clone()))
    };
    let mag = if signed {
        ite(
            Exp::Bvslt(Box::new(wide_i.clone()), Box::new(bv(0, 64))),
            Exp::Bvneg(Box::new(wide_i.clone())),
            wide_i.clone(),
        )
    } else {
        wide_i.clone()
    };
    let geq = |x: &Exp<Sym>, k: i64| Exp::Bvuge(Box::new(x.clone()), Box::new(bv(k as u64, 64)));
    let pos_of = |mode: u64| -> Exp<Sym> {
        let bound = match mode {
            0 | 4 => 65520,
            1 | 2 => 65536,
            _ => 65520,
        };
        match mode {
            2 => geq(&wide_i, 65536),
            _ => geq(&mag, bound),
        }
    };
    let neg_of = |mode: u64| -> Exp<Sym> {
        if !signed {
            return bool(false);
        }
        match mode {
            0 | 4 => Exp::Bvsle(Box::new(wide_i.clone()), Box::new(bv((-65520i64) as u64, 64))),
            1 => Exp::Bvsle(Box::new(wide_i.clone()), Box::new(bv((-65536i64) as u64, 64))),
            2 => Exp::Bvsle(Box::new(wide_i.clone()), Box::new(bv((-65520i64) as u64, 64))),
            _ => Exp::Bvsle(Box::new(wide_i.clone()), Box::new(bv((-65536i64) as u64, 64))),
        }
    };
    (0..5).map(|mode| and(rm_is(rm, mode), or(pos_of(mode), neg_of(mode)))).fold(bool(false), or)
}

// ---------------------------------------------------------------------------
// 主入口
// ---------------------------------------------------------------------------

/// 执行一个 SoftFloat helper：args 为已求值的 IR 实参（rm + IEEE 位/整数位），
/// 返回 tuple-struct 值 {flags_field: bv5, result_field: 结果}。
/// 字段的 Name 由调用方从 IR 的 struct 定义中查出后传入。
pub fn softfloat_call<B: BV>(
    op: SfOp,
    args: Vec<Val<B>>,
    flags_field: Name,
    result_field: Name,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let expect_args = |n: usize, name: &str| -> Result<(), ExecError> {
        if args.len() != n {
            Err(ExecError::Type(format!("softfloat {}: 期望 {} 个参数，实得 {}", name, n, args.len()), info))
        } else {
            Ok(())
        }
    };

    let (flags, result) = match op {
        SfOp::Bin { fmt, op } => {
            expect_args(3, "Bin")?;
            let pat = FpPat::new(fmt);
            let rm = rm_smt(&args[0], solver, info)?;
            let ra = bits_exp(&args[1], "lhs", info)?;
            let rb = bits_exp(&args[2], "rhs", info)?;
            let a = fp_from_bits(ra.clone(), fmt.ebits(), fmt.sbits());
            let b = fp_from_bits(rb.clone(), fmt.ebits(), fmt.sbits());
            let snan_a = pat.is_snan(&ra);
            let snan_b = pat.is_snan(&rb);
            let nan_a = pat.is_nan(&ra);
            let nan_b = pat.is_nan(&rb);
            let any_nan = or(nan_a.clone(), nan_b.clone());
            let inf_a = pat.is_inf(&ra);
            let inf_b = pat.is_inf(&rb);
            let zero_a = pat.is_zero(&ra);
            let zero_b = pat.is_zero(&rb);
            let inv = match op {
                FPRoundingBinary::Add => and(
                    inf_a.clone(),
                    and(
                        inf_b.clone(),
                        eq(Exp::Bvxor(Box::new(pat.sign_bit(&ra)), Box::new(pat.sign_bit(&rb))), bv(1, 1)),
                    ),
                ),
                FPRoundingBinary::Sub => {
                    and(inf_a.clone(), and(inf_b.clone(), eq(pat.sign_bit(&ra), pat.sign_bit(&rb))))
                }
                FPRoundingBinary::Mul => or(and(inf_a.clone(), zero_b.clone()), and(zero_a.clone(), inf_b.clone())),
                FPRoundingBinary::Div => or(and(zero_a.clone(), zero_b.clone()), and(inf_a.clone(), inf_b.clone())),
            };
            let nv = or(or(snan_a, snan_b), inv.clone());
            let fp_res = Exp::FPRoundingBinary(op, Box::new(rm.clone()), Box::new(a.clone()), Box::new(b.clone()));
            let raw = fp_to_bits(fp_res.clone(), fmt.ebits(), fmt.sbits());
            let result = ite(or(any_nan.clone(), inv.clone()), pat.canonical_nan(), raw);
            let dz = if op == FPRoundingBinary::Div {
                and(
                    zero_b.clone(),
                    and(not(zero_a.clone()), and(not(inf_a.clone()), and(not(nan_a.clone()), not(nan_b)))),
                )
            } else {
                bool(false)
            };
            let finite_inputs = and(not(any_nan.clone()), and(not(inf_a.clone()), not(inf_b.clone())));
            let of = and(and(fp_pred(FPUnary::IsInfinite, fp_res.clone()), finite_inputs.clone()), not(dz.clone()));
            let uf = and(
                fp_pred(FPUnary::IsSubnormal, fp_res.clone()),
                and(not(fp_pred(FPUnary::IsZero, fp_res.clone())), finite_inputs.clone()),
            );
            let nx = match op {
                FPRoundingBinary::Add => add_nx(fmt, &ra, &rb, &a, &b, &rm),
                FPRoundingBinary::Sub => add_nx(fmt, &ra, &rb, &a, &b, &rm),
                FPRoundingBinary::Mul => mul_nx(fmt, &a, &b, &rm),
                // Div 的 NX 仅 OF|UF 近似（SMT 无精确不精确谓词，宽格式商不可证精确）
                FPRoundingBinary::Div => or(of.clone(), uf.clone()),
            };
            (flags_word(nv, dz, of, uf, nx), result)
        }
        SfOp::MulAdd { fmt } => {
            expect_args(4, "MulAdd")?;
            let pat = FpPat::new(fmt);
            let rm = rm_smt(&args[0], solver, info)?;
            let ra = bits_exp(&args[1], "x", info)?;
            let rb = bits_exp(&args[2], "y", info)?;
            let rc = bits_exp(&args[3], "z", info)?;
            let a = fp_from_bits(ra.clone(), fmt.ebits(), fmt.sbits());
            let b = fp_from_bits(rb.clone(), fmt.ebits(), fmt.sbits());
            let c = fp_from_bits(rc.clone(), fmt.ebits(), fmt.sbits());
            let any_nan = or(pat.is_nan(&ra), or(pat.is_nan(&rb), pat.is_nan(&rc)));
            let inv = or(
                or(pat.is_snan(&ra), or(pat.is_snan(&rb), pat.is_snan(&rc))),
                or(and(pat.is_inf(&ra), pat.is_zero(&rb)), and(pat.is_zero(&ra), pat.is_inf(&rb))),
            );
            let nv = inv.clone();
            let fp_res =
                Exp::FPfma(Box::new(rm.clone()), Box::new(a.clone()), Box::new(b.clone()), Box::new(c.clone()));
            let raw = fp_to_bits(fp_res.clone(), fmt.ebits(), fmt.sbits());
            let result = ite(or(any_nan.clone(), inv.clone()), pat.canonical_nan(), raw);
            let finite_inputs =
                and(not(any_nan.clone()), and(not(pat.is_inf(&ra)), and(not(pat.is_inf(&rb)), not(pat.is_inf(&rc)))));
            let of = and(fp_pred(FPUnary::IsInfinite, fp_res.clone()), finite_inputs.clone());
            let uf = and(
                fp_pred(FPUnary::IsSubnormal, fp_res.clone()),
                and(not(fp_pred(FPUnary::IsZero, fp_res.clone())), finite_inputs.clone()),
            );
            // FMA 的 NX 仅 OF|UF 近似（三输入的宽格式重算不可行）
            let nx = or(of.clone(), uf.clone());
            (flags_word(nv, bool(false), of, uf, nx), result)
        }
        SfOp::Sqrt { fmt } => {
            expect_args(2, "Sqrt")?;
            let pat = FpPat::new(fmt);
            let rm = rm_smt(&args[0], solver, info)?;
            let ra = bits_exp(&args[1], "x", info)?;
            let x = fp_from_bits(ra.clone(), fmt.ebits(), fmt.sbits());
            let nan_a = pat.is_nan(&ra);
            let neg_nonzero = and(eq(pat.sign_bit(&ra), bv(1, 1)), not(pat.is_zero(&ra)));
            let inv = or(pat.is_snan(&ra), neg_nonzero.clone());
            let nv = inv.clone();
            let fp_res = Exp::FPRoundingUnary(FPRoundingUnary::Sqrt, Box::new(rm), Box::new(x.clone()));
            let raw = fp_to_bits(fp_res.clone(), fmt.ebits(), fmt.sbits());
            let result = ite(or(nan_a.clone(), neg_nonzero), pat.canonical_nan(), raw);
            // sqrt 结果幅值 ≥ sqrt(min_subnormal) > min_normal，永不下溢
            let nx = sqrt_nx(fmt, &x, &fp_res);
            (flags_word(nv, bool(false), bool(false), bool(false), nx), result)
        }
        SfOp::Cmp { fmt, kind, quiet } => {
            expect_args(2, "Cmp")?;
            let pat = FpPat::new(fmt);
            let ra = bits_exp(&args[0], "lhs", info)?;
            let rb = bits_exp(&args[1], "rhs", info)?;
            let a = fp_from_bits(ra.clone(), fmt.ebits(), fmt.sbits());
            let b = fp_from_bits(rb.clone(), fmt.ebits(), fmt.sbits());
            // 信令比较对任何 NaN 置 NV，静默比较仅对 sNaN；结果 NaN 时均为 false，
            // 与 SMT fp.lt/leq/eq 的 NaN 语义一致
            let nv = if quiet { or(pat.is_snan(&ra), pat.is_snan(&rb)) } else { or(pat.is_nan(&ra), pat.is_nan(&rb)) };
            let result = Exp::FPBinary(kind, Box::new(a), Box::new(b));
            (flags_word(nv, bool(false), bool(false), bool(false), bool(false)), result)
        }
        SfOp::RoundToInt { fmt } => {
            expect_args(3, "roundToInt")?;
            let pat = FpPat::new(fmt);
            let rm = rm_smt(&args[0], solver, info)?;
            let ra = bits_exp(&args[1], "x", info)?;
            let exact = bits_exp(&args[2], "exact", info)?;
            let x = fp_from_bits(ra.clone(), fmt.ebits(), fmt.sbits());
            let nv = pat.is_snan(&ra);
            let fp_res = Exp::FPRoundingUnary(FPRoundingUnary::RoundToIntegral, Box::new(rm), Box::new(x.clone()));
            let raw = fp_to_bits(fp_res.clone(), fmt.ebits(), fmt.sbits());
            let result = ite(pat.is_nan(&ra), pat.canonical_nan(), raw);
            let nx = and(exact, and(not(pat.is_nan(&ra)), not(fp_ieee_eq(fp_res, x))));
            (flags_word(nv, bool(false), bool(false), bool(false), nx), result)
        }
        SfOp::FpToI { src, signed, int_width } => {
            expect_args(2, "FpToI")?;
            let pat = FpPat::new(src);
            let rm = rm_smt(&args[0], solver, info)?;
            let ra = bits_exp(&args[1], "x", info)?;
            let x = fp_from_bits(ra.clone(), src.ebits(), src.sbits());
            let rm_bits = bits_exp(&args[0], "rm", info)?;
            let isnan = fp_pred(FPUnary::IsNaN, x.clone());
            let isneg = fp_pred(FPUnary::IsNegative, x.clone());
            let (we, ws) = src.wide();
            let x_wide = fp_convert(x.clone(), rm.clone(), we, ws);
            let range_nv = conv_range_nv(src, &x_wide, &rm_bits, signed, int_width);
            let nv = or(isnan.clone(), range_nv.clone());
            let to_int = Exp::FPRoundingUnary(
                if signed { FPRoundingUnary::ToSigned(int_width) } else { FPRoundingUnary::ToUnsigned(int_width) },
                Box::new(rm.clone()),
                Box::new(x.clone()),
            );
            // NV 时的默认值：RISC-V 规定 NaN → 同符号最大幅值（规范 NaN 为正 → 最大正），
            // 溢出按符号取边界
            let max = bv(((1u128 << (int_width - 1)) - 1) as u64, int_width);
            let min = bv((1u128 << (int_width - 1)) as u64, int_width);
            let ones = bv(((1u128 << int_width) - 1) as u64, int_width);
            let default = if signed {
                ite(isnan.clone(), max.clone(), ite(isneg.clone(), min, max))
            } else {
                ite(isnan.clone(), ones.clone(), ite(isneg.clone(), bv(0, int_width), ones))
            };
            let result = ite(nv.clone(), default, to_int.clone());
            // 往返比较精确判定 NX：范围内的整数值有效位数 ≤ 源格式精度 p，
            // FromSigned/FromUnsigned 往返无损
            let back = Exp::FPRoundingUnary(
                if signed {
                    FPRoundingUnary::FromSigned(src.ebits(), src.sbits())
                } else {
                    FPRoundingUnary::FromUnsigned(src.ebits(), src.sbits())
                },
                Box::new(rm.clone()),
                Box::new(to_int),
            );
            let nx = and(and(not(isnan), not(range_nv)), not(fp_ieee_eq(back, x)));
            (flags_word(nv, bool(false), bool(false), bool(false), nx), result)
        }
        SfOp::IFp { signed, int_width, dst } => {
            expect_args(2, "IFp")?;
            let rm = rm_smt(&args[0], solver, info)?;
            let i = bits_exp(&args[1], "i", info)?;
            let rm_bits = bits_exp(&args[0], "rm", info)?;
            let fp_res = Exp::FPRoundingUnary(
                if signed {
                    FPRoundingUnary::FromSigned(dst.ebits(), dst.sbits())
                } else {
                    FPRoundingUnary::FromUnsigned(dst.ebits(), dst.sbits())
                },
                Box::new(rm.clone()),
                Box::new(i.clone()),
            );
            let result = fp_to_bits(fp_res.clone(), dst.ebits(), dst.sbits());
            let of = itofp_of(dst, signed, int_width, &i, &rm_bits);
            // RTZ 与 RUP 两种极端舍入相同 ⇔ 整数可被目标格式精确表示
            let rtz = Exp::FPRoundingMode(FPRoundingMode::RoundTowardZero);
            let rup = Exp::FPRoundingMode(FPRoundingMode::RoundTowardPositive);
            let under_rtz = Exp::FPRoundingUnary(
                if signed {
                    FPRoundingUnary::FromSigned(dst.ebits(), dst.sbits())
                } else {
                    FPRoundingUnary::FromUnsigned(dst.ebits(), dst.sbits())
                },
                Box::new(rtz),
                Box::new(i.clone()),
            );
            let under_rup = Exp::FPRoundingUnary(
                if signed {
                    FPRoundingUnary::FromSigned(dst.ebits(), dst.sbits())
                } else {
                    FPRoundingUnary::FromUnsigned(dst.ebits(), dst.sbits())
                },
                Box::new(rup),
                Box::new(i),
            );
            let nx = not(fp_ieee_eq(under_rtz, under_rup));
            (flags_word(bool(false), bool(false), of, bool(false), nx), result)
        }
        SfOp::FpToFp { src, dst } => {
            expect_args(2, "FpToFp")?;
            softfloat_fp_to_fp(src, dst.ebits(), dst.sbits(), &args, solver, info)?
        }
        SfOp::ToBF16 => {
            expect_args(2, "ToBF16")?;
            softfloat_fp_to_fp(SfFmt::F32, 8, 8, &args, solver, info)?
        }
    };

    let flags_val = solver.define_const(flags, info);
    let result_val = solver.define_const(result, info);
    let mut fields = HashMap::default();
    fields.insert(flags_field, Val::Symbolic(flags_val));
    fields.insert(result_field, Val::Symbolic(result_val));
    Ok(Val::Struct(fields))
}

/// fp→fp 格式转换（含 BF16：(8,8)）。拓宽恒精确（NX=OF=UF=0）；窄化用往返
/// 比较精确判定 NX，OF 用 isinf(res) 且输入有限近似（定向舍入饱和到最大有限
/// 数时漏报，数值结果本身仍精确）。
fn softfloat_fp_to_fp<B: BV>(
    src: SfFmt,
    dst_e: u32,
    dst_s: u32,
    args: &[Val<B>],
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<(Exp<Sym>, Exp<Sym>), ExecError> {
    let pat = FpPat::new(src);
    let rm = rm_smt(&args[0], solver, info)?;
    let ra = bits_exp(&args[1], "x", info)?;
    let x = fp_from_bits(ra.clone(), src.ebits(), src.sbits());
    let nv = pat.is_snan(&ra);
    let fp_res = fp_convert(x.clone(), rm.clone(), dst_e, dst_s);
    let raw = fp_to_bits(fp_res.clone(), dst_e, dst_s);
    let dst_canonical_nan = bv(((1 << dst_e) - 1) << (dst_s - 1) | 1 << (dst_s - 2), dst_e + dst_s);
    let result = ite(pat.is_nan(&ra), dst_canonical_nan, raw);
    let widening = dst_e >= src.ebits() && dst_s >= src.sbits();
    let (of, uf, nx) = if widening {
        (bool(false), bool(false), bool(false))
    } else {
        let back = fp_convert(fp_res.clone(), rm.clone(), src.ebits(), src.sbits());
        let nx = not(fp_ieee_eq(back, x.clone()));
        let of = and(
            fp_pred(FPUnary::IsInfinite, fp_res.clone()),
            and(not(fp_pred(FPUnary::IsNaN, x.clone())), not(fp_pred(FPUnary::IsInfinite, x.clone()))),
        );
        let uf = and(fp_pred(FPUnary::IsSubnormal, fp_res.clone()), not(fp_pred(FPUnary::IsZero, fp_res.clone())));
        (of, uf, nx)
    };
    Ok((flags_word(nv, bool(false), of, uf, nx), result))
}

#[cfg(test)]
mod softfloat_tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::smt::{Config, Context, Model, SmtResult};

    fn fields() -> (Name, Name) {
        (Name::from_u32(9001), Name::from_u32(9002))
    }

    fn rm(v: u64) -> Val<B64> {
        Val::Bits(B64::new(v, 3))
    }

    fn f32v(x: f32) -> Val<B64> {
        Val::Bits(B64::new(x.to_bits() as u64, 32))
    }

    fn f64v(x: f64) -> Val<B64> {
        Val::Bits(B64::new(x.to_bits(), 64))
    }

    fn bitsv(bits: u64, width: u32) -> Val<B64> {
        Val::Bits(B64::new(bits, width))
    }

    fn boolv(b: bool) -> Val<B64> {
        Val::Bool(b)
    }

    /// 跑一个 helper 并求解，返回 (flags, 结果位)。结果为布尔时结果位为 0/1。
    fn solve_call(name: &str, args: Vec<Val<B64>>) -> (u64, u64) {
        let op = softfloat_dispatch(name).unwrap_or_else(|| panic!("无法解析 {}", name));
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let (flags_name, result_name) = fields();
        let v = softfloat_call(op, args, flags_name, result_name, &mut solver, SourceLoc::unknown()).unwrap();
        let (flags, result) = match &v {
            Val::Struct(fields) => (fields[&flags_name].clone(), fields[&result_name].clone()),
            v => panic!("期望 struct 返回值，得到 {:?}", v),
        };
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        let mut model = Model::new(&solver);
        let mut read = |val: Val<B64>| -> u64 {
            let materialized = model.get_val(&val).unwrap();
            match materialized {
                Val::Bits(bv) => bv.lower_u64(),
                Val::Bool(b) => b as u64,
                v => panic!("无法物化 {:?}", v),
            }
        };
        (read(flags), read(result))
    }

    const NX: u64 = 1;
    const UF: u64 = 2;
    const OF: u64 = 4;
    const DZ: u64 = 8;
    const NV: u64 = 16;

    #[test]
    fn f32_add_basic() {
        let (f, r) = solve_call("riscv_f32Add", vec![rm(0), f32v(1.0), f32v(2.0)]);
        assert_eq!((f, r), (0, 3.0f32.to_bits() as u64));
    }

    #[test]
    fn f32_add_inexact_nx() {
        // (1+2^-23)(1+2^-22) 的积需要 25 位尾数，f32 舍入不精确
        let (f, _r) = solve_call("riscv_f32Mul", vec![rm(0), f32v(1.0000001), f32v(1.0000002)]);
        assert_eq!(f & NX, NX);
        // 精确乘积不置位
        let (f, r) = solve_call("riscv_f32Mul", vec![rm(0), f32v(2.0), f32v(4.0)]);
        assert_eq!((f, r), (0, 8.0f32.to_bits() as u64));
    }

    #[test]
    fn f32_add_overflow_of_nx() {
        // MAX+MAX 在 RNE 下溢出到 +inf：OF 置位；溢出蕴含不精确，NX 置位
        let (f, r) = solve_call("riscv_f32Add", vec![rm(0), f32v(f32::MAX), f32v(f32::MAX)]);
        assert_eq!(r, f32::INFINITY.to_bits() as u64);
        assert_eq!(f & OF, OF);
        assert_eq!(f & NX, NX);
        assert_eq!(f & NV, 0);
    }

    #[test]
    fn f32_add_inf_inf_invalid() {
        let (f, r) = solve_call("riscv_f32Add", vec![rm(0), f32v(f32::INFINITY), f32v(f32::NEG_INFINITY)]);
        assert_eq!(r, 0x7fc00000);
        assert_eq!(f & NV, NV);
    }

    #[test]
    fn f32_div_by_zero() {
        let (f, r) = solve_call("riscv_f32Div", vec![rm(0), f32v(1.0), f32v(0.0)]);
        assert_eq!(r, f32::INFINITY.to_bits() as u64);
        assert_eq!(f, DZ);
    }

    #[test]
    fn f32_div_zero_zero_invalid() {
        let (f, r) = solve_call("riscv_f32Div", vec![rm(0), f32v(0.0), f32v(0.0)]);
        assert_eq!(r, 0x7fc00000);
        assert_eq!(f & NV, NV);
    }

    #[test]
    fn f32_mul_underflow_uf() {
        // 最小次正规数 × 0.75 = 1.5×2^-150，RNE 舍到次正规数 2^-149，不精确 → UF|NX
        let min_sub = f32::from_bits(1);
        let (f, r) = solve_call("riscv_f32Mul", vec![rm(0), f32v(min_sub), f32v(0.75)]);
        assert_eq!(r, 1);
        assert_eq!(f & UF, UF);
        assert_eq!(f & NX, NX);
    }

    #[test]
    fn f32_snan_quiet_nan_flags() {
        // sNaN 输入：NV 置位，结果为规范 NaN
        let snan = f32::from_bits(0x7f800001);
        let (f, r) = solve_call("riscv_f32Add", vec![rm(0), f32v(snan), f32v(1.0)]);
        assert_eq!(r, 0x7fc00000);
        assert_eq!(f & NV, NV);
        // qNaN 输入：无 NV，结果为规范 NaN
        let qnan = f32::from_bits(0x7fc00001);
        let (f, r) = solve_call("riscv_f32Add", vec![rm(0), f32v(qnan), f32v(1.0)]);
        assert_eq!(r, 0x7fc00000);
        assert_eq!(f & NV, 0);
    }

    #[test]
    fn f32_sqrt_exact_and_inexact() {
        let (f, r) = solve_call("riscv_f32Sqrt", vec![rm(0), f32v(4.0)]);
        assert_eq!((f, r), (0, 2.0f32.to_bits() as u64));
        let (f, _r) = solve_call("riscv_f32Sqrt", vec![rm(0), f32v(2.0)]);
        assert_eq!(f & NX, NX);
    }

    #[test]
    fn f32_sqrt_negative_invalid() {
        let (f, r) = solve_call("riscv_f32Sqrt", vec![rm(0), f32v(-4.0)]);
        assert_eq!(r, 0x7fc00000);
        assert_eq!(f & NV, NV);
    }

    #[test]
    fn f32_cmp_nan_semantics() {
        let nan = f32::from_bits(0x7fc00001);
        // 信令比较：任何 NaN → NV
        let (f, r) = solve_call("riscv_f32Lt", vec![f32v(nan), f32v(1.0)]);
        assert_eq!(r, 0);
        assert_eq!(f & NV, NV);
        // 静默比较：qNaN 不置 NV
        let (f, r) = solve_call("riscv_f32Lt_quiet", vec![f32v(nan), f32v(1.0)]);
        assert_eq!(r, 0);
        assert_eq!(f & NV, 0);
        // 正常比较
        let (f, r) = solve_call("riscv_f32Le", vec![f32v(1.0), f32v(2.0)]);
        assert_eq!((f, r), (0, 1));
    }

    #[test]
    fn fma_basic() {
        let (f, r) = solve_call("riscv_f32MulAdd", vec![rm(0), f32v(2.0), f32v(3.0), f32v(1.0)]);
        assert_eq!((f, r), (0, 7.0f32.to_bits() as u64));
    }

    #[test]
    fn f32_to_i32_overflow_and_boundary() {
        // 2^31 恰好超出 i32：NV，默认值 = 0x7fffffff
        let (f, r) = solve_call("riscv_f32ToI32", vec![rm(0), f32v(2147483648.0)]);
        assert_eq!(r, 0x7fffffff);
        assert_eq!(f & NV, NV);
        // RNE 下最大合法值：2^31 - 64 处平局，最大可接受的 f32 是 2^31-128
        let (f, r) = solve_call("riscv_f32ToI32", vec![rm(0), f32v(2147483520.0)]);
        assert_eq!((f, r), (0, 2147483520));
        // 负溢出：-2^31-128 → NV，默认值 = 0x80000000
        let (f, r) = solve_call("riscv_f32ToI32", vec![rm(0), f32v(-2147483904.0)]);
        assert_eq!(r, 0x80000000);
        assert_eq!(f & NV, NV);
        // -2^31 本身合法
        let (f, r) = solve_call("riscv_f32ToI32", vec![rm(0), f32v(-2147483648.0)]);
        assert_eq!((f, r), (0, 0x80000000));
    }

    #[test]
    fn f32_to_i32_inexact_nx() {
        let (f, r) = solve_call("riscv_f32ToI32", vec![rm(0), f32v(-1.5)]);
        assert_eq!(r, (-2i32) as u32 as u64);
        assert_eq!(f & NX, NX);
        assert_eq!(f & NV, 0);
        // NaN → NV，默认 0x7fffffff
        let (f, r) = solve_call("riscv_f32ToI32", vec![rm(0), f32v(f32::NAN)]);
        assert_eq!(r, 0x7fffffff);
        assert_eq!(f & NV, NV);
    }

    #[test]
    fn i32_to_f32_inexact_nx() {
        // 2^31-1 需要 32 位有效数字，f32 只能表示 24 位 → 舍入到 2^31
        let (f, r) = solve_call("riscv_i32ToF32", vec![rm(0), bitsv(0x7fffffff, 32)]);
        assert_eq!(r, 2147483648.0f32.to_bits() as u64);
        assert_eq!(f & NX, NX);
        // 可精确表示的整数不置位
        let (f, r) = solve_call("riscv_i32ToF32", vec![rm(0), bitsv(1 << 23, 32)]);
        assert_eq!((f, r), (0, 8388608.0f32.to_bits() as u64));
    }

    #[test]
    fn i64_to_f16_overflow_of() {
        // RNE：|i| ≥ 65520 溢出到 +inf（f16 inf = 0x7C00）
        let (f, r) = solve_call("riscv_i64ToF16", vec![rm(0), bitsv(65520, 64)]);
        assert_eq!(r, 0x7c00);
        assert_eq!(f & OF, OF);
        // RTZ：65520 截断到最大有限数 65504（f16 编码 0x7BFF），不溢出
        let (f, r) = solve_call("riscv_i64ToF16", vec![rm(1), bitsv(65520, 64)]);
        assert_eq!(r, 0x7bff);
        assert_eq!(f & OF, 0);
        let (f, _r) = solve_call("riscv_i64ToF16", vec![rm(1), bitsv(65536, 64)]);
        assert_eq!(f & OF, OF);
    }

    #[test]
    fn f64_to_f32_narrowing_nx() {
        let (f, r) = solve_call("riscv_f64ToF32", vec![rm(0), f64v(1.5)]);
        assert_eq!((f, r), (0, 1.5f32.to_bits() as u64));
        // f64 1/3 无法用 f32 精确表示 → NX
        let (f, _r) = solve_call("riscv_f64ToF32", vec![rm(0), f64v(1.0 / 3.0)]);
        assert_eq!(f & NX, NX);
    }

    #[test]
    fn f32_round_to_int() {
        let (f, r) = solve_call("riscv_f32roundToInt", vec![rm(0), f32v(2.5), boolv(true)]);
        assert_eq!(r, 2.0f32.to_bits() as u64);
        assert_eq!(f & NX, NX);
        let (f, r) = solve_call("riscv_f32roundToInt", vec![rm(0), f32v(2.0), boolv(true)]);
        assert_eq!((f, r), (0, 2.0f32.to_bits() as u64));
        // exact=false 时抑制 NX
        let (f, _r) = solve_call("riscv_f32roundToInt", vec![rm(0), f32v(2.5), boolv(false)]);
        assert_eq!(f & NX, 0);
    }

    #[test]
    fn f32_to_bf16() {
        let (f, r) = solve_call("riscv_f32ToBF16", vec![rm(0), f32v(1.0)]);
        assert_eq!((f, r), (0, 0x3f80));
    }

    #[test]
    fn f16_add_basic() {
        let one_h = 0x3c00;
        let two_h = 0x4000;
        let (f, r) = solve_call("riscv_f16Add", vec![rm(0), bitsv(one_h, 16), bitsv(one_h, 16)]);
        assert_eq!((f, r), (0, two_h));
    }

    #[test]
    fn dispatch_unknown_name() {
        assert!(softfloat_dispatch("riscv_f32Nonsense").is_none());
        assert!(softfloat_dispatch("eq_int").is_none());
        assert!(matches!(softfloat_dispatch("riscv_f32Add"), Some(SfOp::Bin { fmt: SfFmt::F32, .. })));
        assert!(matches!(
            softfloat_dispatch("riscv_ui64ToF16"),
            Some(SfOp::IFp { signed: false, int_width: 64, dst: SfFmt::F16 })
        ));
        assert_eq!(softfloat_result_struct(softfloat_dispatch("riscv_f32Add").unwrap()), "ztuplez3z5bv5_z5bv32");
        assert_eq!(softfloat_result_struct(softfloat_dispatch("riscv_f32Lt").unwrap()), "ztuplez3z5bv5_z5bool");
    }
}
