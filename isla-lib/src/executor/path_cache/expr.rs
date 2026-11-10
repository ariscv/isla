//! 缓存的外部标签镜像；保留所有变体与字段，不改变核心执行类型。
use crate::{bitvector::b64::B64, ir::Name};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Ty {
    Bool,
    BitVec(u32),
    Enum(Name),
    Array(Box<Ty>, Box<Ty>),
    Float(u32, u32),
    RoundingMode,
}
impl From<crate::smt::smtlib::Ty> for Ty {
    fn from(value: crate::smt::smtlib::Ty) -> Self {
        match value {
            crate::smt::smtlib::Ty::Bool => Ty::Bool,
            crate::smt::smtlib::Ty::BitVec(field0) => Ty::BitVec(field0),
            crate::smt::smtlib::Ty::Enum(field0) => Ty::Enum(field0.to_name()),
            crate::smt::smtlib::Ty::Array(field0, field1) => {
                Ty::Array(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Ty::Float(field0, field1) => Ty::Float(field0, field1),
            crate::smt::smtlib::Ty::RoundingMode => Ty::RoundingMode,
        }
    }
}
impl From<Ty> for crate::smt::smtlib::Ty {
    fn from(value: Ty) -> Self {
        match value {
            Ty::Bool => crate::smt::smtlib::Ty::Bool,
            Ty::BitVec(field0) => crate::smt::smtlib::Ty::BitVec(field0),
            Ty::Enum(field0) => crate::smt::smtlib::Ty::Enum(crate::smt::EnumId::from_name(field0)),
            Ty::Array(field0, field1) => {
                crate::smt::smtlib::Ty::Array(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Ty::Float(field0, field1) => crate::smt::smtlib::Ty::Float(field0, field1),
            Ty::RoundingMode => crate::smt::smtlib::Ty::RoundingMode,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum FPRoundingMode {
    RoundNearestTiesToEven,
    RoundNearestTiesToAway,
    RoundTowardPositive,
    RoundTowardNegative,
    RoundTowardZero,
}
impl From<crate::smt::smtlib::FPRoundingMode> for FPRoundingMode {
    fn from(value: crate::smt::smtlib::FPRoundingMode) -> Self {
        match value {
            crate::smt::smtlib::FPRoundingMode::RoundNearestTiesToEven => FPRoundingMode::RoundNearestTiesToEven,
            crate::smt::smtlib::FPRoundingMode::RoundNearestTiesToAway => FPRoundingMode::RoundNearestTiesToAway,
            crate::smt::smtlib::FPRoundingMode::RoundTowardPositive => FPRoundingMode::RoundTowardPositive,
            crate::smt::smtlib::FPRoundingMode::RoundTowardNegative => FPRoundingMode::RoundTowardNegative,
            crate::smt::smtlib::FPRoundingMode::RoundTowardZero => FPRoundingMode::RoundTowardZero,
        }
    }
}
impl From<FPRoundingMode> for crate::smt::smtlib::FPRoundingMode {
    fn from(value: FPRoundingMode) -> Self {
        match value {
            FPRoundingMode::RoundNearestTiesToEven => crate::smt::smtlib::FPRoundingMode::RoundNearestTiesToEven,
            FPRoundingMode::RoundNearestTiesToAway => crate::smt::smtlib::FPRoundingMode::RoundNearestTiesToAway,
            FPRoundingMode::RoundTowardPositive => crate::smt::smtlib::FPRoundingMode::RoundTowardPositive,
            FPRoundingMode::RoundTowardNegative => crate::smt::smtlib::FPRoundingMode::RoundTowardNegative,
            FPRoundingMode::RoundTowardZero => crate::smt::smtlib::FPRoundingMode::RoundTowardZero,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum FPConstant {
    NaN,
    Inf { negative: bool },
    Zero { negative: bool },
}
impl From<crate::smt::smtlib::FPConstant> for FPConstant {
    fn from(value: crate::smt::smtlib::FPConstant) -> Self {
        match value {
            crate::smt::smtlib::FPConstant::NaN => FPConstant::NaN,
            crate::smt::smtlib::FPConstant::Inf { negative } => FPConstant::Inf { negative: negative },
            crate::smt::smtlib::FPConstant::Zero { negative } => FPConstant::Zero { negative: negative },
        }
    }
}
impl From<FPConstant> for crate::smt::smtlib::FPConstant {
    fn from(value: FPConstant) -> Self {
        match value {
            FPConstant::NaN => crate::smt::smtlib::FPConstant::NaN,
            FPConstant::Inf { negative } => crate::smt::smtlib::FPConstant::Inf { negative: negative },
            FPConstant::Zero { negative } => crate::smt::smtlib::FPConstant::Zero { negative: negative },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum FPUnary {
    Abs,
    Neg,
    IsNormal,
    IsSubnormal,
    IsZero,
    IsInfinite,
    IsNaN,
    IsNegative,
    IsPositive,
    FromIEEE(u32, u32),
    ToIEEE(u32, u32),
}
impl From<crate::smt::smtlib::FPUnary> for FPUnary {
    fn from(value: crate::smt::smtlib::FPUnary) -> Self {
        match value {
            crate::smt::smtlib::FPUnary::Abs => FPUnary::Abs,
            crate::smt::smtlib::FPUnary::Neg => FPUnary::Neg,
            crate::smt::smtlib::FPUnary::IsNormal => FPUnary::IsNormal,
            crate::smt::smtlib::FPUnary::IsSubnormal => FPUnary::IsSubnormal,
            crate::smt::smtlib::FPUnary::IsZero => FPUnary::IsZero,
            crate::smt::smtlib::FPUnary::IsInfinite => FPUnary::IsInfinite,
            crate::smt::smtlib::FPUnary::IsNaN => FPUnary::IsNaN,
            crate::smt::smtlib::FPUnary::IsNegative => FPUnary::IsNegative,
            crate::smt::smtlib::FPUnary::IsPositive => FPUnary::IsPositive,
            crate::smt::smtlib::FPUnary::FromIEEE(field0, field1) => FPUnary::FromIEEE(field0, field1),
            crate::smt::smtlib::FPUnary::ToIEEE(field0, field1) => FPUnary::ToIEEE(field0, field1),
        }
    }
}
impl From<FPUnary> for crate::smt::smtlib::FPUnary {
    fn from(value: FPUnary) -> Self {
        match value {
            FPUnary::Abs => crate::smt::smtlib::FPUnary::Abs,
            FPUnary::Neg => crate::smt::smtlib::FPUnary::Neg,
            FPUnary::IsNormal => crate::smt::smtlib::FPUnary::IsNormal,
            FPUnary::IsSubnormal => crate::smt::smtlib::FPUnary::IsSubnormal,
            FPUnary::IsZero => crate::smt::smtlib::FPUnary::IsZero,
            FPUnary::IsInfinite => crate::smt::smtlib::FPUnary::IsInfinite,
            FPUnary::IsNaN => crate::smt::smtlib::FPUnary::IsNaN,
            FPUnary::IsNegative => crate::smt::smtlib::FPUnary::IsNegative,
            FPUnary::IsPositive => crate::smt::smtlib::FPUnary::IsPositive,
            FPUnary::FromIEEE(field0, field1) => crate::smt::smtlib::FPUnary::FromIEEE(field0, field1),
            FPUnary::ToIEEE(field0, field1) => crate::smt::smtlib::FPUnary::ToIEEE(field0, field1),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum FPRoundingUnary {
    Sqrt,
    RoundToIntegral,
    Convert(u32, u32),
    FromSigned(u32, u32),
    FromUnsigned(u32, u32),
    ToSigned(u32),
    ToUnsigned(u32),
}
impl From<crate::smt::smtlib::FPRoundingUnary> for FPRoundingUnary {
    fn from(value: crate::smt::smtlib::FPRoundingUnary) -> Self {
        match value {
            crate::smt::smtlib::FPRoundingUnary::Sqrt => FPRoundingUnary::Sqrt,
            crate::smt::smtlib::FPRoundingUnary::RoundToIntegral => FPRoundingUnary::RoundToIntegral,
            crate::smt::smtlib::FPRoundingUnary::Convert(field0, field1) => FPRoundingUnary::Convert(field0, field1),
            crate::smt::smtlib::FPRoundingUnary::FromSigned(field0, field1) => {
                FPRoundingUnary::FromSigned(field0, field1)
            }
            crate::smt::smtlib::FPRoundingUnary::FromUnsigned(field0, field1) => {
                FPRoundingUnary::FromUnsigned(field0, field1)
            }
            crate::smt::smtlib::FPRoundingUnary::ToSigned(field0) => FPRoundingUnary::ToSigned(field0),
            crate::smt::smtlib::FPRoundingUnary::ToUnsigned(field0) => FPRoundingUnary::ToUnsigned(field0),
        }
    }
}
impl From<FPRoundingUnary> for crate::smt::smtlib::FPRoundingUnary {
    fn from(value: FPRoundingUnary) -> Self {
        match value {
            FPRoundingUnary::Sqrt => crate::smt::smtlib::FPRoundingUnary::Sqrt,
            FPRoundingUnary::RoundToIntegral => crate::smt::smtlib::FPRoundingUnary::RoundToIntegral,
            FPRoundingUnary::Convert(field0, field1) => crate::smt::smtlib::FPRoundingUnary::Convert(field0, field1),
            FPRoundingUnary::FromSigned(field0, field1) => {
                crate::smt::smtlib::FPRoundingUnary::FromSigned(field0, field1)
            }
            FPRoundingUnary::FromUnsigned(field0, field1) => {
                crate::smt::smtlib::FPRoundingUnary::FromUnsigned(field0, field1)
            }
            FPRoundingUnary::ToSigned(field0) => crate::smt::smtlib::FPRoundingUnary::ToSigned(field0),
            FPRoundingUnary::ToUnsigned(field0) => crate::smt::smtlib::FPRoundingUnary::ToUnsigned(field0),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum FPBinary {
    Rem,
    Min,
    Max,
    Leq,
    Lt,
    Geq,
    Gt,
    Eq,
}
impl From<crate::smt::smtlib::FPBinary> for FPBinary {
    fn from(value: crate::smt::smtlib::FPBinary) -> Self {
        match value {
            crate::smt::smtlib::FPBinary::Rem => FPBinary::Rem,
            crate::smt::smtlib::FPBinary::Min => FPBinary::Min,
            crate::smt::smtlib::FPBinary::Max => FPBinary::Max,
            crate::smt::smtlib::FPBinary::Leq => FPBinary::Leq,
            crate::smt::smtlib::FPBinary::Lt => FPBinary::Lt,
            crate::smt::smtlib::FPBinary::Geq => FPBinary::Geq,
            crate::smt::smtlib::FPBinary::Gt => FPBinary::Gt,
            crate::smt::smtlib::FPBinary::Eq => FPBinary::Eq,
        }
    }
}
impl From<FPBinary> for crate::smt::smtlib::FPBinary {
    fn from(value: FPBinary) -> Self {
        match value {
            FPBinary::Rem => crate::smt::smtlib::FPBinary::Rem,
            FPBinary::Min => crate::smt::smtlib::FPBinary::Min,
            FPBinary::Max => crate::smt::smtlib::FPBinary::Max,
            FPBinary::Leq => crate::smt::smtlib::FPBinary::Leq,
            FPBinary::Lt => crate::smt::smtlib::FPBinary::Lt,
            FPBinary::Geq => crate::smt::smtlib::FPBinary::Geq,
            FPBinary::Gt => crate::smt::smtlib::FPBinary::Gt,
            FPBinary::Eq => crate::smt::smtlib::FPBinary::Eq,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum FPRoundingBinary {
    Add,
    Sub,
    Mul,
    Div,
}
impl From<crate::smt::smtlib::FPRoundingBinary> for FPRoundingBinary {
    fn from(value: crate::smt::smtlib::FPRoundingBinary) -> Self {
        match value {
            crate::smt::smtlib::FPRoundingBinary::Add => FPRoundingBinary::Add,
            crate::smt::smtlib::FPRoundingBinary::Sub => FPRoundingBinary::Sub,
            crate::smt::smtlib::FPRoundingBinary::Mul => FPRoundingBinary::Mul,
            crate::smt::smtlib::FPRoundingBinary::Div => FPRoundingBinary::Div,
        }
    }
}
impl From<FPRoundingBinary> for crate::smt::smtlib::FPRoundingBinary {
    fn from(value: FPRoundingBinary) -> Self {
        match value {
            FPRoundingBinary::Add => crate::smt::smtlib::FPRoundingBinary::Add,
            FPRoundingBinary::Sub => crate::smt::smtlib::FPRoundingBinary::Sub,
            FPRoundingBinary::Mul => crate::smt::smtlib::FPRoundingBinary::Mul,
            FPRoundingBinary::Div => crate::smt::smtlib::FPRoundingBinary::Div,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Exp {
    Var(u32),
    Bits(Vec<bool>),
    Bits64(B64),
    Enum(Member),
    Bool(bool),
    Eq(Box<Exp>, Box<Exp>),
    Neq(Box<Exp>, Box<Exp>),
    And(Box<Exp>, Box<Exp>),
    Or(Box<Exp>, Box<Exp>),
    Not(Box<Exp>),
    Bvnot(Box<Exp>),
    Bvand(Box<Exp>, Box<Exp>),
    Bvor(Box<Exp>, Box<Exp>),
    Bvxor(Box<Exp>, Box<Exp>),
    Bvnand(Box<Exp>, Box<Exp>),
    Bvnor(Box<Exp>, Box<Exp>),
    Bvxnor(Box<Exp>, Box<Exp>),
    Bvneg(Box<Exp>),
    Bvadd(Box<Exp>, Box<Exp>),
    Bvsub(Box<Exp>, Box<Exp>),
    Bvmul(Box<Exp>, Box<Exp>),
    Bvudiv(Box<Exp>, Box<Exp>),
    Bvsdiv(Box<Exp>, Box<Exp>),
    Bvurem(Box<Exp>, Box<Exp>),
    Bvsrem(Box<Exp>, Box<Exp>),
    Bvsmod(Box<Exp>, Box<Exp>),
    Bvult(Box<Exp>, Box<Exp>),
    Bvslt(Box<Exp>, Box<Exp>),
    Bvule(Box<Exp>, Box<Exp>),
    Bvsle(Box<Exp>, Box<Exp>),
    Bvuge(Box<Exp>, Box<Exp>),
    Bvsge(Box<Exp>, Box<Exp>),
    Bvugt(Box<Exp>, Box<Exp>),
    Bvsgt(Box<Exp>, Box<Exp>),
    Extract(u32, u32, Box<Exp>),
    ZeroExtend(u32, Box<Exp>),
    SignExtend(u32, Box<Exp>),
    Bvshl(Box<Exp>, Box<Exp>),
    Bvlshr(Box<Exp>, Box<Exp>),
    Bvashr(Box<Exp>, Box<Exp>),
    Concat(Box<Exp>, Box<Exp>),
    Ite(Box<Exp>, Box<Exp>, Box<Exp>),
    App(u32, Vec<Exp>),
    Select(Box<Exp>, Box<Exp>),
    Store(Box<Exp>, Box<Exp>, Box<Exp>),
    Distinct(Vec<Exp>),
    FPConstant(FPConstant, u32, u32),
    FPRoundingMode(FPRoundingMode),
    FPUnary(FPUnary, Box<Exp>),
    FPRoundingUnary(FPRoundingUnary, Box<Exp>, Box<Exp>),
    FPBinary(FPBinary, Box<Exp>, Box<Exp>),
    FPRoundingBinary(FPRoundingBinary, Box<Exp>, Box<Exp>, Box<Exp>),
    FPfma(Box<Exp>, Box<Exp>, Box<Exp>, Box<Exp>),
}
impl From<crate::smt::smtlib::Exp<crate::smt::Sym>> for Exp {
    fn from(value: crate::smt::smtlib::Exp<crate::smt::Sym>) -> Self {
        match value {
            crate::smt::smtlib::Exp::Var(field0) => Exp::Var(field0.id),
            crate::smt::smtlib::Exp::Bits(field0) => Exp::Bits(field0.into_iter().map(|item| item).collect()),
            crate::smt::smtlib::Exp::Bits64(field0) => Exp::Bits64(field0),
            crate::smt::smtlib::Exp::Enum(field0) => Exp::Enum((field0).into()),
            crate::smt::smtlib::Exp::Bool(field0) => Exp::Bool(field0),
            crate::smt::smtlib::Exp::Eq(field0, field1) => {
                Exp::Eq(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Neq(field0, field1) => {
                Exp::Neq(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::And(field0, field1) => {
                Exp::And(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Or(field0, field1) => {
                Exp::Or(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Not(field0) => Exp::Not(Box::new((*field0).into())),
            crate::smt::smtlib::Exp::Bvnot(field0) => Exp::Bvnot(Box::new((*field0).into())),
            crate::smt::smtlib::Exp::Bvand(field0, field1) => {
                Exp::Bvand(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvor(field0, field1) => {
                Exp::Bvor(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvxor(field0, field1) => {
                Exp::Bvxor(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvnand(field0, field1) => {
                Exp::Bvnand(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvnor(field0, field1) => {
                Exp::Bvnor(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvxnor(field0, field1) => {
                Exp::Bvxnor(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvneg(field0) => Exp::Bvneg(Box::new((*field0).into())),
            crate::smt::smtlib::Exp::Bvadd(field0, field1) => {
                Exp::Bvadd(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvsub(field0, field1) => {
                Exp::Bvsub(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvmul(field0, field1) => {
                Exp::Bvmul(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvudiv(field0, field1) => {
                Exp::Bvudiv(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvsdiv(field0, field1) => {
                Exp::Bvsdiv(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvurem(field0, field1) => {
                Exp::Bvurem(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvsrem(field0, field1) => {
                Exp::Bvsrem(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvsmod(field0, field1) => {
                Exp::Bvsmod(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvult(field0, field1) => {
                Exp::Bvult(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvslt(field0, field1) => {
                Exp::Bvslt(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvule(field0, field1) => {
                Exp::Bvule(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvsle(field0, field1) => {
                Exp::Bvsle(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvuge(field0, field1) => {
                Exp::Bvuge(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvsge(field0, field1) => {
                Exp::Bvsge(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvugt(field0, field1) => {
                Exp::Bvugt(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvsgt(field0, field1) => {
                Exp::Bvsgt(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Extract(field0, field1, field2) => {
                Exp::Extract(field0, field1, Box::new((*field2).into()))
            }
            crate::smt::smtlib::Exp::ZeroExtend(field0, field1) => Exp::ZeroExtend(field0, Box::new((*field1).into())),
            crate::smt::smtlib::Exp::SignExtend(field0, field1) => Exp::SignExtend(field0, Box::new((*field1).into())),
            crate::smt::smtlib::Exp::Bvshl(field0, field1) => {
                Exp::Bvshl(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvlshr(field0, field1) => {
                Exp::Bvlshr(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvashr(field0, field1) => {
                Exp::Bvashr(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Concat(field0, field1) => {
                Exp::Concat(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Ite(field0, field1, field2) => {
                Exp::Ite(Box::new((*field0).into()), Box::new((*field1).into()), Box::new((*field2).into()))
            }
            crate::smt::smtlib::Exp::App(field0, field1) => {
                Exp::App(field0.id, field1.into_iter().map(|item| (item).into()).collect())
            }
            crate::smt::smtlib::Exp::Select(field0, field1) => {
                Exp::Select(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Store(field0, field1, field2) => {
                Exp::Store(Box::new((*field0).into()), Box::new((*field1).into()), Box::new((*field2).into()))
            }
            crate::smt::smtlib::Exp::Distinct(field0) => {
                Exp::Distinct(field0.into_iter().map(|item| (item).into()).collect())
            }
            crate::smt::smtlib::Exp::FPConstant(field0, field1, field2) => {
                Exp::FPConstant((field0).into(), field1, field2)
            }
            crate::smt::smtlib::Exp::FPRoundingMode(field0) => Exp::FPRoundingMode((field0).into()),
            crate::smt::smtlib::Exp::FPUnary(field0, field1) => {
                Exp::FPUnary((field0).into(), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::FPRoundingUnary(field0, field1, field2) => {
                Exp::FPRoundingUnary((field0).into(), Box::new((*field1).into()), Box::new((*field2).into()))
            }
            crate::smt::smtlib::Exp::FPBinary(field0, field1, field2) => {
                Exp::FPBinary((field0).into(), Box::new((*field1).into()), Box::new((*field2).into()))
            }
            crate::smt::smtlib::Exp::FPRoundingBinary(field0, field1, field2, field3) => Exp::FPRoundingBinary(
                (field0).into(),
                Box::new((*field1).into()),
                Box::new((*field2).into()),
                Box::new((*field3).into()),
            ),
            crate::smt::smtlib::Exp::FPfma(field0, field1, field2, field3) => Exp::FPfma(
                Box::new((*field0).into()),
                Box::new((*field1).into()),
                Box::new((*field2).into()),
                Box::new((*field3).into()),
            ),
        }
    }
}
impl From<Exp> for crate::smt::smtlib::Exp<crate::smt::Sym> {
    fn from(value: Exp) -> Self {
        match value {
            Exp::Var(field0) => crate::smt::smtlib::Exp::Var(crate::smt::Sym::from_u32(field0)),
            Exp::Bits(field0) => crate::smt::smtlib::Exp::Bits(field0.into_iter().map(|item| item).collect()),
            Exp::Bits64(field0) => crate::smt::smtlib::Exp::Bits64(field0),
            Exp::Enum(field0) => crate::smt::smtlib::Exp::Enum((field0).into()),
            Exp::Bool(field0) => crate::smt::smtlib::Exp::Bool(field0),
            Exp::Eq(field0, field1) => {
                crate::smt::smtlib::Exp::Eq(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Neq(field0, field1) => {
                crate::smt::smtlib::Exp::Neq(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::And(field0, field1) => {
                crate::smt::smtlib::Exp::And(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Or(field0, field1) => {
                crate::smt::smtlib::Exp::Or(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Not(field0) => crate::smt::smtlib::Exp::Not(Box::new((*field0).into())),
            Exp::Bvnot(field0) => crate::smt::smtlib::Exp::Bvnot(Box::new((*field0).into())),
            Exp::Bvand(field0, field1) => {
                crate::smt::smtlib::Exp::Bvand(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvor(field0, field1) => {
                crate::smt::smtlib::Exp::Bvor(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvxor(field0, field1) => {
                crate::smt::smtlib::Exp::Bvxor(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvnand(field0, field1) => {
                crate::smt::smtlib::Exp::Bvnand(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvnor(field0, field1) => {
                crate::smt::smtlib::Exp::Bvnor(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvxnor(field0, field1) => {
                crate::smt::smtlib::Exp::Bvxnor(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvneg(field0) => crate::smt::smtlib::Exp::Bvneg(Box::new((*field0).into())),
            Exp::Bvadd(field0, field1) => {
                crate::smt::smtlib::Exp::Bvadd(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvsub(field0, field1) => {
                crate::smt::smtlib::Exp::Bvsub(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvmul(field0, field1) => {
                crate::smt::smtlib::Exp::Bvmul(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvudiv(field0, field1) => {
                crate::smt::smtlib::Exp::Bvudiv(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvsdiv(field0, field1) => {
                crate::smt::smtlib::Exp::Bvsdiv(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvurem(field0, field1) => {
                crate::smt::smtlib::Exp::Bvurem(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvsrem(field0, field1) => {
                crate::smt::smtlib::Exp::Bvsrem(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvsmod(field0, field1) => {
                crate::smt::smtlib::Exp::Bvsmod(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvult(field0, field1) => {
                crate::smt::smtlib::Exp::Bvult(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvslt(field0, field1) => {
                crate::smt::smtlib::Exp::Bvslt(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvule(field0, field1) => {
                crate::smt::smtlib::Exp::Bvule(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvsle(field0, field1) => {
                crate::smt::smtlib::Exp::Bvsle(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvuge(field0, field1) => {
                crate::smt::smtlib::Exp::Bvuge(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvsge(field0, field1) => {
                crate::smt::smtlib::Exp::Bvsge(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvugt(field0, field1) => {
                crate::smt::smtlib::Exp::Bvugt(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvsgt(field0, field1) => {
                crate::smt::smtlib::Exp::Bvsgt(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Extract(field0, field1, field2) => {
                crate::smt::smtlib::Exp::Extract(field0, field1, Box::new((*field2).into()))
            }
            Exp::ZeroExtend(field0, field1) => crate::smt::smtlib::Exp::ZeroExtend(field0, Box::new((*field1).into())),
            Exp::SignExtend(field0, field1) => crate::smt::smtlib::Exp::SignExtend(field0, Box::new((*field1).into())),
            Exp::Bvshl(field0, field1) => {
                crate::smt::smtlib::Exp::Bvshl(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvlshr(field0, field1) => {
                crate::smt::smtlib::Exp::Bvlshr(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Bvashr(field0, field1) => {
                crate::smt::smtlib::Exp::Bvashr(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Concat(field0, field1) => {
                crate::smt::smtlib::Exp::Concat(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Ite(field0, field1, field2) => crate::smt::smtlib::Exp::Ite(
                Box::new((*field0).into()),
                Box::new((*field1).into()),
                Box::new((*field2).into()),
            ),
            Exp::App(field0, field1) => crate::smt::smtlib::Exp::App(
                crate::smt::Sym::from_u32(field0),
                field1.into_iter().map(|item| (item).into()).collect(),
            ),
            Exp::Select(field0, field1) => {
                crate::smt::smtlib::Exp::Select(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            Exp::Store(field0, field1, field2) => crate::smt::smtlib::Exp::Store(
                Box::new((*field0).into()),
                Box::new((*field1).into()),
                Box::new((*field2).into()),
            ),
            Exp::Distinct(field0) => {
                crate::smt::smtlib::Exp::Distinct(field0.into_iter().map(|item| (item).into()).collect())
            }
            Exp::FPConstant(field0, field1, field2) => {
                crate::smt::smtlib::Exp::FPConstant((field0).into(), field1, field2)
            }
            Exp::FPRoundingMode(field0) => crate::smt::smtlib::Exp::FPRoundingMode((field0).into()),
            Exp::FPUnary(field0, field1) => {
                crate::smt::smtlib::Exp::FPUnary((field0).into(), Box::new((*field1).into()))
            }
            Exp::FPRoundingUnary(field0, field1, field2) => crate::smt::smtlib::Exp::FPRoundingUnary(
                (field0).into(),
                Box::new((*field1).into()),
                Box::new((*field2).into()),
            ),
            Exp::FPBinary(field0, field1, field2) => crate::smt::smtlib::Exp::FPBinary(
                (field0).into(),
                Box::new((*field1).into()),
                Box::new((*field2).into()),
            ),
            Exp::FPRoundingBinary(field0, field1, field2, field3) => crate::smt::smtlib::Exp::FPRoundingBinary(
                (field0).into(),
                Box::new((*field1).into()),
                Box::new((*field2).into()),
                Box::new((*field3).into()),
            ),
            Exp::FPfma(field0, field1, field2, field3) => crate::smt::smtlib::Exp::FPfma(
                Box::new((*field0).into()),
                Box::new((*field1).into()),
                Box::new((*field2).into()),
                Box::new((*field3).into()),
            ),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Def {
    DeclareConst(u32, Ty),
    DeclareFun(u32, Vec<Ty>, Ty),
    DefineConst(u32, Exp),
    DefineEnum(Name, u64),
    Assert(Exp),
}
impl From<crate::smt::smtlib::Def> for Def {
    fn from(value: crate::smt::smtlib::Def) -> Self {
        match value {
            crate::smt::smtlib::Def::DeclareConst(field0, field1) => Def::DeclareConst(field0.id, (field1).into()),
            crate::smt::smtlib::Def::DeclareFun(field0, field1, field2) => {
                Def::DeclareFun(field0.id, field1.into_iter().map(|item| (item).into()).collect(), (field2).into())
            }
            crate::smt::smtlib::Def::DefineConst(field0, field1) => Def::DefineConst(field0.id, (field1).into()),
            crate::smt::smtlib::Def::DefineEnum(field0, field1) => {
                Def::DefineEnum(field0, field1.try_into().expect("缓存索引越界"))
            }
            crate::smt::smtlib::Def::Assert(field0) => Def::Assert((field0).into()),
        }
    }
}
impl From<Def> for crate::smt::smtlib::Def {
    fn from(value: Def) -> Self {
        match value {
            Def::DeclareConst(field0, field1) => {
                crate::smt::smtlib::Def::DeclareConst(crate::smt::Sym::from_u32(field0), (field1).into())
            }
            Def::DeclareFun(field0, field1, field2) => crate::smt::smtlib::Def::DeclareFun(
                crate::smt::Sym::from_u32(field0),
                field1.into_iter().map(|item| (item).into()).collect(),
                (field2).into(),
            ),
            Def::DefineConst(field0, field1) => {
                crate::smt::smtlib::Def::DefineConst(crate::smt::Sym::from_u32(field0), (field1).into())
            }
            Def::DefineEnum(field0, field1) => {
                crate::smt::smtlib::Def::DefineEnum(field0, field1.try_into().expect("缓存索引越界"))
            }
            Def::Assert(field0) => crate::smt::smtlib::Def::Assert((field0).into()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum AssumeExp {
    Var(crate::ir::Loc<String>),
    Bits(Vec<bool>),
    Bits64(B64),
    Enum(Member),
    Bool(bool),
    Eq(Box<AssumeExp>, Box<AssumeExp>),
    Neq(Box<AssumeExp>, Box<AssumeExp>),
    And(Box<AssumeExp>, Box<AssumeExp>),
    Or(Box<AssumeExp>, Box<AssumeExp>),
    Not(Box<AssumeExp>),
    Bvnot(Box<AssumeExp>),
    Bvand(Box<AssumeExp>, Box<AssumeExp>),
    Bvor(Box<AssumeExp>, Box<AssumeExp>),
    Bvxor(Box<AssumeExp>, Box<AssumeExp>),
    Bvnand(Box<AssumeExp>, Box<AssumeExp>),
    Bvnor(Box<AssumeExp>, Box<AssumeExp>),
    Bvxnor(Box<AssumeExp>, Box<AssumeExp>),
    Bvneg(Box<AssumeExp>),
    Bvadd(Box<AssumeExp>, Box<AssumeExp>),
    Bvsub(Box<AssumeExp>, Box<AssumeExp>),
    Bvmul(Box<AssumeExp>, Box<AssumeExp>),
    Bvudiv(Box<AssumeExp>, Box<AssumeExp>),
    Bvsdiv(Box<AssumeExp>, Box<AssumeExp>),
    Bvurem(Box<AssumeExp>, Box<AssumeExp>),
    Bvsrem(Box<AssumeExp>, Box<AssumeExp>),
    Bvsmod(Box<AssumeExp>, Box<AssumeExp>),
    Bvult(Box<AssumeExp>, Box<AssumeExp>),
    Bvslt(Box<AssumeExp>, Box<AssumeExp>),
    Bvule(Box<AssumeExp>, Box<AssumeExp>),
    Bvsle(Box<AssumeExp>, Box<AssumeExp>),
    Bvuge(Box<AssumeExp>, Box<AssumeExp>),
    Bvsge(Box<AssumeExp>, Box<AssumeExp>),
    Bvugt(Box<AssumeExp>, Box<AssumeExp>),
    Bvsgt(Box<AssumeExp>, Box<AssumeExp>),
    Extract(u32, u32, Box<AssumeExp>),
    ZeroExtend(u32, Box<AssumeExp>),
    SignExtend(u32, Box<AssumeExp>),
    Bvshl(Box<AssumeExp>, Box<AssumeExp>),
    Bvlshr(Box<AssumeExp>, Box<AssumeExp>),
    Bvashr(Box<AssumeExp>, Box<AssumeExp>),
    Concat(Box<AssumeExp>, Box<AssumeExp>),
    Ite(Box<AssumeExp>, Box<AssumeExp>, Box<AssumeExp>),
    App(u32, Vec<AssumeExp>),
    Select(Box<AssumeExp>, Box<AssumeExp>),
    Store(Box<AssumeExp>, Box<AssumeExp>, Box<AssumeExp>),
    Distinct(Vec<AssumeExp>),
    FPConstant(FPConstant, u32, u32),
    FPRoundingMode(FPRoundingMode),
    FPUnary(FPUnary, Box<AssumeExp>),
    FPRoundingUnary(FPRoundingUnary, Box<AssumeExp>, Box<AssumeExp>),
    FPBinary(FPBinary, Box<AssumeExp>, Box<AssumeExp>),
    FPRoundingBinary(FPRoundingBinary, Box<AssumeExp>, Box<AssumeExp>, Box<AssumeExp>),
    FPfma(Box<AssumeExp>, Box<AssumeExp>, Box<AssumeExp>, Box<AssumeExp>),
}
impl From<crate::smt::smtlib::Exp<crate::ir::Loc<String>>> for AssumeExp {
    fn from(value: crate::smt::smtlib::Exp<crate::ir::Loc<String>>) -> Self {
        match value {
            crate::smt::smtlib::Exp::Var(field0) => AssumeExp::Var(field0),
            crate::smt::smtlib::Exp::Bits(field0) => AssumeExp::Bits(field0.into_iter().map(|item| item).collect()),
            crate::smt::smtlib::Exp::Bits64(field0) => AssumeExp::Bits64(field0),
            crate::smt::smtlib::Exp::Enum(field0) => AssumeExp::Enum((field0).into()),
            crate::smt::smtlib::Exp::Bool(field0) => AssumeExp::Bool(field0),
            crate::smt::smtlib::Exp::Eq(field0, field1) => {
                AssumeExp::Eq(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Neq(field0, field1) => {
                AssumeExp::Neq(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::And(field0, field1) => {
                AssumeExp::And(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Or(field0, field1) => {
                AssumeExp::Or(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Not(field0) => AssumeExp::Not(Box::new((*field0).into())),
            crate::smt::smtlib::Exp::Bvnot(field0) => AssumeExp::Bvnot(Box::new((*field0).into())),
            crate::smt::smtlib::Exp::Bvand(field0, field1) => {
                AssumeExp::Bvand(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvor(field0, field1) => {
                AssumeExp::Bvor(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvxor(field0, field1) => {
                AssumeExp::Bvxor(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvnand(field0, field1) => {
                AssumeExp::Bvnand(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvnor(field0, field1) => {
                AssumeExp::Bvnor(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvxnor(field0, field1) => {
                AssumeExp::Bvxnor(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvneg(field0) => AssumeExp::Bvneg(Box::new((*field0).into())),
            crate::smt::smtlib::Exp::Bvadd(field0, field1) => {
                AssumeExp::Bvadd(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvsub(field0, field1) => {
                AssumeExp::Bvsub(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvmul(field0, field1) => {
                AssumeExp::Bvmul(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvudiv(field0, field1) => {
                AssumeExp::Bvudiv(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvsdiv(field0, field1) => {
                AssumeExp::Bvsdiv(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvurem(field0, field1) => {
                AssumeExp::Bvurem(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvsrem(field0, field1) => {
                AssumeExp::Bvsrem(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvsmod(field0, field1) => {
                AssumeExp::Bvsmod(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvult(field0, field1) => {
                AssumeExp::Bvult(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvslt(field0, field1) => {
                AssumeExp::Bvslt(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvule(field0, field1) => {
                AssumeExp::Bvule(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvsle(field0, field1) => {
                AssumeExp::Bvsle(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvuge(field0, field1) => {
                AssumeExp::Bvuge(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvsge(field0, field1) => {
                AssumeExp::Bvsge(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvugt(field0, field1) => {
                AssumeExp::Bvugt(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvsgt(field0, field1) => {
                AssumeExp::Bvsgt(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Extract(field0, field1, field2) => {
                AssumeExp::Extract(field0, field1, Box::new((*field2).into()))
            }
            crate::smt::smtlib::Exp::ZeroExtend(field0, field1) => {
                AssumeExp::ZeroExtend(field0, Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::SignExtend(field0, field1) => {
                AssumeExp::SignExtend(field0, Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvshl(field0, field1) => {
                AssumeExp::Bvshl(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvlshr(field0, field1) => {
                AssumeExp::Bvlshr(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Bvashr(field0, field1) => {
                AssumeExp::Bvashr(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Concat(field0, field1) => {
                AssumeExp::Concat(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Ite(field0, field1, field2) => {
                AssumeExp::Ite(Box::new((*field0).into()), Box::new((*field1).into()), Box::new((*field2).into()))
            }
            crate::smt::smtlib::Exp::App(field0, field1) => {
                AssumeExp::App(field0.id, field1.into_iter().map(|item| (item).into()).collect())
            }
            crate::smt::smtlib::Exp::Select(field0, field1) => {
                AssumeExp::Select(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::Store(field0, field1, field2) => {
                AssumeExp::Store(Box::new((*field0).into()), Box::new((*field1).into()), Box::new((*field2).into()))
            }
            crate::smt::smtlib::Exp::Distinct(field0) => {
                AssumeExp::Distinct(field0.into_iter().map(|item| (item).into()).collect())
            }
            crate::smt::smtlib::Exp::FPConstant(field0, field1, field2) => {
                AssumeExp::FPConstant((field0).into(), field1, field2)
            }
            crate::smt::smtlib::Exp::FPRoundingMode(field0) => AssumeExp::FPRoundingMode((field0).into()),
            crate::smt::smtlib::Exp::FPUnary(field0, field1) => {
                AssumeExp::FPUnary((field0).into(), Box::new((*field1).into()))
            }
            crate::smt::smtlib::Exp::FPRoundingUnary(field0, field1, field2) => {
                AssumeExp::FPRoundingUnary((field0).into(), Box::new((*field1).into()), Box::new((*field2).into()))
            }
            crate::smt::smtlib::Exp::FPBinary(field0, field1, field2) => {
                AssumeExp::FPBinary((field0).into(), Box::new((*field1).into()), Box::new((*field2).into()))
            }
            crate::smt::smtlib::Exp::FPRoundingBinary(field0, field1, field2, field3) => AssumeExp::FPRoundingBinary(
                (field0).into(),
                Box::new((*field1).into()),
                Box::new((*field2).into()),
                Box::new((*field3).into()),
            ),
            crate::smt::smtlib::Exp::FPfma(field0, field1, field2, field3) => AssumeExp::FPfma(
                Box::new((*field0).into()),
                Box::new((*field1).into()),
                Box::new((*field2).into()),
                Box::new((*field3).into()),
            ),
        }
    }
}
impl From<AssumeExp> for crate::smt::smtlib::Exp<crate::ir::Loc<String>> {
    fn from(value: AssumeExp) -> Self {
        match value {
            AssumeExp::Var(field0) => crate::smt::smtlib::Exp::Var(field0),
            AssumeExp::Bits(field0) => crate::smt::smtlib::Exp::Bits(field0.into_iter().map(|item| item).collect()),
            AssumeExp::Bits64(field0) => crate::smt::smtlib::Exp::Bits64(field0),
            AssumeExp::Enum(field0) => crate::smt::smtlib::Exp::Enum((field0).into()),
            AssumeExp::Bool(field0) => crate::smt::smtlib::Exp::Bool(field0),
            AssumeExp::Eq(field0, field1) => {
                crate::smt::smtlib::Exp::Eq(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Neq(field0, field1) => {
                crate::smt::smtlib::Exp::Neq(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::And(field0, field1) => {
                crate::smt::smtlib::Exp::And(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Or(field0, field1) => {
                crate::smt::smtlib::Exp::Or(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Not(field0) => crate::smt::smtlib::Exp::Not(Box::new((*field0).into())),
            AssumeExp::Bvnot(field0) => crate::smt::smtlib::Exp::Bvnot(Box::new((*field0).into())),
            AssumeExp::Bvand(field0, field1) => {
                crate::smt::smtlib::Exp::Bvand(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvor(field0, field1) => {
                crate::smt::smtlib::Exp::Bvor(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvxor(field0, field1) => {
                crate::smt::smtlib::Exp::Bvxor(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvnand(field0, field1) => {
                crate::smt::smtlib::Exp::Bvnand(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvnor(field0, field1) => {
                crate::smt::smtlib::Exp::Bvnor(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvxnor(field0, field1) => {
                crate::smt::smtlib::Exp::Bvxnor(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvneg(field0) => crate::smt::smtlib::Exp::Bvneg(Box::new((*field0).into())),
            AssumeExp::Bvadd(field0, field1) => {
                crate::smt::smtlib::Exp::Bvadd(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvsub(field0, field1) => {
                crate::smt::smtlib::Exp::Bvsub(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvmul(field0, field1) => {
                crate::smt::smtlib::Exp::Bvmul(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvudiv(field0, field1) => {
                crate::smt::smtlib::Exp::Bvudiv(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvsdiv(field0, field1) => {
                crate::smt::smtlib::Exp::Bvsdiv(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvurem(field0, field1) => {
                crate::smt::smtlib::Exp::Bvurem(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvsrem(field0, field1) => {
                crate::smt::smtlib::Exp::Bvsrem(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvsmod(field0, field1) => {
                crate::smt::smtlib::Exp::Bvsmod(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvult(field0, field1) => {
                crate::smt::smtlib::Exp::Bvult(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvslt(field0, field1) => {
                crate::smt::smtlib::Exp::Bvslt(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvule(field0, field1) => {
                crate::smt::smtlib::Exp::Bvule(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvsle(field0, field1) => {
                crate::smt::smtlib::Exp::Bvsle(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvuge(field0, field1) => {
                crate::smt::smtlib::Exp::Bvuge(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvsge(field0, field1) => {
                crate::smt::smtlib::Exp::Bvsge(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvugt(field0, field1) => {
                crate::smt::smtlib::Exp::Bvugt(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvsgt(field0, field1) => {
                crate::smt::smtlib::Exp::Bvsgt(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Extract(field0, field1, field2) => {
                crate::smt::smtlib::Exp::Extract(field0, field1, Box::new((*field2).into()))
            }
            AssumeExp::ZeroExtend(field0, field1) => {
                crate::smt::smtlib::Exp::ZeroExtend(field0, Box::new((*field1).into()))
            }
            AssumeExp::SignExtend(field0, field1) => {
                crate::smt::smtlib::Exp::SignExtend(field0, Box::new((*field1).into()))
            }
            AssumeExp::Bvshl(field0, field1) => {
                crate::smt::smtlib::Exp::Bvshl(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvlshr(field0, field1) => {
                crate::smt::smtlib::Exp::Bvlshr(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Bvashr(field0, field1) => {
                crate::smt::smtlib::Exp::Bvashr(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Concat(field0, field1) => {
                crate::smt::smtlib::Exp::Concat(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Ite(field0, field1, field2) => crate::smt::smtlib::Exp::Ite(
                Box::new((*field0).into()),
                Box::new((*field1).into()),
                Box::new((*field2).into()),
            ),
            AssumeExp::App(field0, field1) => crate::smt::smtlib::Exp::App(
                crate::smt::Sym::from_u32(field0),
                field1.into_iter().map(|item| (item).into()).collect(),
            ),
            AssumeExp::Select(field0, field1) => {
                crate::smt::smtlib::Exp::Select(Box::new((*field0).into()), Box::new((*field1).into()))
            }
            AssumeExp::Store(field0, field1, field2) => crate::smt::smtlib::Exp::Store(
                Box::new((*field0).into()),
                Box::new((*field1).into()),
                Box::new((*field2).into()),
            ),
            AssumeExp::Distinct(field0) => {
                crate::smt::smtlib::Exp::Distinct(field0.into_iter().map(|item| (item).into()).collect())
            }
            AssumeExp::FPConstant(field0, field1, field2) => {
                crate::smt::smtlib::Exp::FPConstant((field0).into(), field1, field2)
            }
            AssumeExp::FPRoundingMode(field0) => crate::smt::smtlib::Exp::FPRoundingMode((field0).into()),
            AssumeExp::FPUnary(field0, field1) => {
                crate::smt::smtlib::Exp::FPUnary((field0).into(), Box::new((*field1).into()))
            }
            AssumeExp::FPRoundingUnary(field0, field1, field2) => crate::smt::smtlib::Exp::FPRoundingUnary(
                (field0).into(),
                Box::new((*field1).into()),
                Box::new((*field2).into()),
            ),
            AssumeExp::FPBinary(field0, field1, field2) => crate::smt::smtlib::Exp::FPBinary(
                (field0).into(),
                Box::new((*field1).into()),
                Box::new((*field2).into()),
            ),
            AssumeExp::FPRoundingBinary(field0, field1, field2, field3) => crate::smt::smtlib::Exp::FPRoundingBinary(
                (field0).into(),
                Box::new((*field1).into()),
                Box::new((*field2).into()),
                Box::new((*field3).into()),
            ),
            AssumeExp::FPfma(field0, field1, field2, field3) => crate::smt::smtlib::Exp::FPfma(
                Box::new((*field0).into()),
                Box::new((*field1).into()),
                Box::new((*field2).into()),
                Box::new((*field3).into()),
            ),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Member {
    pub enum_id: Name,
    pub member: u64,
}
impl From<crate::smt::EnumMember> for Member {
    fn from(value: crate::smt::EnumMember) -> Self {
        Self { enum_id: value.enum_id.to_name(), member: value.member.try_into().unwrap() }
    }
}
impl From<Member> for crate::smt::EnumMember {
    fn from(value: Member) -> Self {
        Self {
            enum_id: crate::smt::EnumId::from_name(value.enum_id),
            member: value.member.try_into().expect("缓存枚举索引越界"),
        }
    }
}
