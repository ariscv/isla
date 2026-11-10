//! 全变体编解码契约，所有名字均为合成编号。
use isla_lib::executor::path_cache::{event::*, expr::*, value::*};
use isla_lib::{
    bitvector::{b64::B64, BV},
    ir::{Loc, Name},
    smt::Accessor,
    source_loc::SourceLoc,
};
use serde::{de::DeserializeOwned, Serialize};
fn roundtrip<T: Serialize + DeserializeOwned + PartialEq + std::fmt::Debug>(value: &T) {
    let json = serde_json::to_vec(value).unwrap();
    let bin = bincode::serialize(value).unwrap();
    assert_eq!(*value, serde_json::from_slice(&json).unwrap());
    assert_eq!(*value, bincode::deserialize(&bin).unwrap());
}
#[test]
fn all_ty_variants() {
    let values: Vec<Ty> = vec![
        Ty::Bool,
        Ty::BitVec(7),
        Ty::Enum(Name::from_u32(9)),
        Ty::Array(Box::new(Ty::BitVec(8)), Box::new(Ty::BitVec(8))),
        Ty::Float(7, 7),
        Ty::RoundingMode,
    ];
    for value in values {
        roundtrip(&value);
        let core: isla_lib::smt::smtlib::Ty = value.clone().into();
        let restored: Ty = core.into();
        assert_eq!(value, restored);
    }
}
#[test]
fn all_fproundingmode_variants() {
    let values: Vec<FPRoundingMode> = vec![
        FPRoundingMode::RoundNearestTiesToEven,
        FPRoundingMode::RoundNearestTiesToAway,
        FPRoundingMode::RoundTowardPositive,
        FPRoundingMode::RoundTowardNegative,
        FPRoundingMode::RoundTowardZero,
    ];
    for value in values {
        roundtrip(&value);
        let core: isla_lib::smt::smtlib::FPRoundingMode = value.clone().into();
        let restored: FPRoundingMode = core.into();
        assert_eq!(value, restored);
    }
}
#[test]
fn all_fpconstant_variants() {
    let values: Vec<FPConstant> =
        vec![FPConstant::NaN, FPConstant::Inf { negative: true }, FPConstant::Zero { negative: true }];
    for value in values {
        roundtrip(&value);
        let core: isla_lib::smt::smtlib::FPConstant = value.clone().into();
        let restored: FPConstant = core.into();
        assert_eq!(value, restored);
    }
}
#[test]
fn all_fpunary_variants() {
    let values: Vec<FPUnary> = vec![
        FPUnary::Abs,
        FPUnary::Neg,
        FPUnary::IsNormal,
        FPUnary::IsSubnormal,
        FPUnary::IsZero,
        FPUnary::IsInfinite,
        FPUnary::IsNaN,
        FPUnary::IsNegative,
        FPUnary::IsPositive,
        FPUnary::FromIEEE(7, 7),
        FPUnary::ToIEEE(7, 7),
    ];
    for value in values {
        roundtrip(&value);
        let core: isla_lib::smt::smtlib::FPUnary = value.clone().into();
        let restored: FPUnary = core.into();
        assert_eq!(value, restored);
    }
}
#[test]
fn all_fproundingunary_variants() {
    let values: Vec<FPRoundingUnary> = vec![
        FPRoundingUnary::Sqrt,
        FPRoundingUnary::RoundToIntegral,
        FPRoundingUnary::Convert(7, 7),
        FPRoundingUnary::FromSigned(7, 7),
        FPRoundingUnary::FromUnsigned(7, 7),
        FPRoundingUnary::ToSigned(7),
        FPRoundingUnary::ToUnsigned(7),
    ];
    for value in values {
        roundtrip(&value);
        let core: isla_lib::smt::smtlib::FPRoundingUnary = value.clone().into();
        let restored: FPRoundingUnary = core.into();
        assert_eq!(value, restored);
    }
}
#[test]
fn all_fpbinary_variants() {
    let values: Vec<FPBinary> = vec![
        FPBinary::Rem,
        FPBinary::Min,
        FPBinary::Max,
        FPBinary::Leq,
        FPBinary::Lt,
        FPBinary::Geq,
        FPBinary::Gt,
        FPBinary::Eq,
    ];
    for value in values {
        roundtrip(&value);
        let core: isla_lib::smt::smtlib::FPBinary = value.clone().into();
        let restored: FPBinary = core.into();
        assert_eq!(value, restored);
    }
}
#[test]
fn all_fproundingbinary_variants() {
    let values: Vec<FPRoundingBinary> =
        vec![FPRoundingBinary::Add, FPRoundingBinary::Sub, FPRoundingBinary::Mul, FPRoundingBinary::Div];
    for value in values {
        roundtrip(&value);
        let core: isla_lib::smt::smtlib::FPRoundingBinary = value.clone().into();
        let restored: FPRoundingBinary = core.into();
        assert_eq!(value, restored);
    }
}
#[test]
fn all_exp_variants() {
    let values: Vec<Exp> = vec![
        Exp::Var(3),
        Exp::Bits(vec![true]),
        Exp::Bits64(B64::new(0xab, 8)),
        Exp::Enum(Member { enum_id: Name::from_u32(9), member: 1 }),
        Exp::Bool(true),
        Exp::Eq(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Neq(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::And(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Or(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Not(Box::new(Exp::Bool(true))),
        Exp::Bvnot(Box::new(Exp::Bool(true))),
        Exp::Bvand(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvor(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvxor(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvnand(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvnor(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvxnor(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvneg(Box::new(Exp::Bool(true))),
        Exp::Bvadd(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvsub(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvmul(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvudiv(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvsdiv(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvurem(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvsrem(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvsmod(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvult(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvslt(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvule(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvsle(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvuge(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvsge(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvugt(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvsgt(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Extract(7, 7, Box::new(Exp::Bool(true))),
        Exp::ZeroExtend(7, Box::new(Exp::Bool(true))),
        Exp::SignExtend(7, Box::new(Exp::Bool(true))),
        Exp::Bvshl(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvlshr(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Bvashr(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Concat(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Ite(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::App(3, vec![Exp::Bool(true)]),
        Exp::Select(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Store(Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::Distinct(vec![Exp::Bool(true)]),
        Exp::FPConstant(FPConstant::NaN, 7, 7),
        Exp::FPRoundingMode(FPRoundingMode::RoundTowardZero),
        Exp::FPUnary(FPUnary::Abs, Box::new(Exp::Bool(true))),
        Exp::FPRoundingUnary(FPRoundingUnary::Sqrt, Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::FPBinary(FPBinary::Eq, Box::new(Exp::Bool(true)), Box::new(Exp::Bool(true))),
        Exp::FPRoundingBinary(
            FPRoundingBinary::Add,
            Box::new(Exp::Bool(true)),
            Box::new(Exp::Bool(true)),
            Box::new(Exp::Bool(true)),
        ),
        Exp::FPfma(
            Box::new(Exp::Bool(true)),
            Box::new(Exp::Bool(true)),
            Box::new(Exp::Bool(true)),
            Box::new(Exp::Bool(true)),
        ),
    ];
    for value in values {
        roundtrip(&value);
        let core: isla_lib::smt::smtlib::Exp<isla_lib::smt::Sym> = value.clone().into();
        let restored: Exp = core.into();
        assert_eq!(value, restored);
    }
}
#[test]
fn all_def_variants() {
    let values: Vec<Def> = vec![
        Def::DeclareConst(3, Ty::BitVec(8)),
        Def::DeclareFun(3, vec![Ty::BitVec(8)], Ty::BitVec(8)),
        Def::DefineConst(3, Exp::Bool(true)),
        Def::DefineEnum(Name::from_u32(9), 5),
        Def::Assert(Exp::Bool(true)),
    ];
    for value in values {
        roundtrip(&value);
        let core: isla_lib::smt::smtlib::Def = value.clone().into();
        let restored: Def = core.into();
        assert_eq!(value, restored);
    }
}
#[test]
fn all_assumeexp_variants() {
    let values: Vec<AssumeExp> = vec![
        AssumeExp::Var(Loc::Id("input".into())),
        AssumeExp::Bits(vec![true]),
        AssumeExp::Bits64(B64::new(0xab, 8)),
        AssumeExp::Enum(Member { enum_id: Name::from_u32(9), member: 1 }),
        AssumeExp::Bool(true),
        AssumeExp::Eq(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Neq(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::And(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Or(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Not(Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvnot(Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvand(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvor(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvxor(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvnand(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvnor(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvxnor(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvneg(Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvadd(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvsub(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvmul(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvudiv(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvsdiv(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvurem(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvsrem(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvsmod(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvult(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvslt(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvule(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvsle(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvuge(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvsge(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvugt(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvsgt(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Extract(7, 7, Box::new(AssumeExp::Bool(true))),
        AssumeExp::ZeroExtend(7, Box::new(AssumeExp::Bool(true))),
        AssumeExp::SignExtend(7, Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvshl(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvlshr(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Bvashr(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Concat(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Ite(
            Box::new(AssumeExp::Bool(true)),
            Box::new(AssumeExp::Bool(true)),
            Box::new(AssumeExp::Bool(true)),
        ),
        AssumeExp::App(3, vec![AssumeExp::Bool(true)]),
        AssumeExp::Select(Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::Store(
            Box::new(AssumeExp::Bool(true)),
            Box::new(AssumeExp::Bool(true)),
            Box::new(AssumeExp::Bool(true)),
        ),
        AssumeExp::Distinct(vec![AssumeExp::Bool(true)]),
        AssumeExp::FPConstant(FPConstant::NaN, 7, 7),
        AssumeExp::FPRoundingMode(FPRoundingMode::RoundTowardZero),
        AssumeExp::FPUnary(FPUnary::Abs, Box::new(AssumeExp::Bool(true))),
        AssumeExp::FPRoundingUnary(
            FPRoundingUnary::Sqrt,
            Box::new(AssumeExp::Bool(true)),
            Box::new(AssumeExp::Bool(true)),
        ),
        AssumeExp::FPBinary(FPBinary::Eq, Box::new(AssumeExp::Bool(true)), Box::new(AssumeExp::Bool(true))),
        AssumeExp::FPRoundingBinary(
            FPRoundingBinary::Add,
            Box::new(AssumeExp::Bool(true)),
            Box::new(AssumeExp::Bool(true)),
            Box::new(AssumeExp::Bool(true)),
        ),
        AssumeExp::FPfma(
            Box::new(AssumeExp::Bool(true)),
            Box::new(AssumeExp::Bool(true)),
            Box::new(AssumeExp::Bool(true)),
            Box::new(AssumeExp::Bool(true)),
        ),
    ];
    for value in values {
        roundtrip(&value);
        let core: isla_lib::smt::smtlib::Exp<isla_lib::ir::Loc<String>> = value.clone().into();
        let restored: AssumeExp = core.into();
        assert_eq!(value, restored);
    }
}
#[test]
fn all_bitssegment_variants() {
    let values: Vec<BitsSegment<B64>> = vec![BitsSegment::Symbolic(3), BitsSegment::Concrete(B64::new(0xab, 8))];
    for value in values {
        roundtrip(&value);
        let core: isla_lib::ir::BitsSegment<B64> = value.clone().into();
        let restored: BitsSegment<B64> = core.into();
        assert_eq!(value, restored);
    }
}
#[test]
fn all_val_variants() {
    let values: Vec<Val<B64>> = vec![
        Val::Symbolic(3),
        Val::I64(-55),
        Val::I128(i128::MIN + 5),
        Val::Bool(true),
        Val::Bits(B64::new(0xab, 8)),
        Val::MixedBits(vec![BitsSegment::Concrete(B64::new(7, 3))]),
        Val::String("text".into()),
        Val::Unit,
        Val::Vector(vec![Val::Unit]),
        Val::List(vec![Val::Unit]),
        Val::Enum(Member { enum_id: Name::from_u32(9), member: 1 }),
        Val::Struct(vec![(Name::from_u32(9), Val::Unit)]),
        Val::Ctor(Name::from_u32(9), Box::new(Val::Unit)),
        Val::SymbolicCtor(3, vec![(Name::from_u32(9), Val::Unit)]),
        Val::Ref(Name::from_u32(9)),
        Val::Poison,
    ];
    for value in values {
        roundtrip(&value);
        let core: isla_lib::ir::Val<B64> = value.clone().into();
        let restored: Val<B64> = core.into();
        assert_eq!(value, restored);
    }
}
#[test]
fn all_event_variants() {
    let values: Vec<Event<B64>> = vec![
        Event::Smt(Def::Assert(Exp::Bool(true)), DefAttrs { bits: 3 }, SourceLoc::unknown()),
        Event::Fork(7, 3, 7, SourceLoc::unknown()),
        Event::Merge(7, 5, SourceLoc::unknown()),
        Event::Function { name: Name::from_u32(9), call: true },
        Event::Abstract { name: Name::from_u32(9), primitive: true, args: vec![Val::Unit], return_value: Val::Unit },
        Event::ReadReg(Name::from_u32(9), vec![Accessor::Field(Name::from_u32(9))], Val::Unit),
        Event::WriteReg(Name::from_u32(9), vec![Accessor::Field(Name::from_u32(9))], Val::Unit),
        Event::AssumeReg(Name::from_u32(9), vec![Accessor::Field(Name::from_u32(9))], Val::Unit),
        Event::ReadMem {
            value: Val::Unit,
            read_kind: Val::Unit,
            address: Val::Unit,
            bytes: 7,
            tag_value: Some(Val::Unit),
            opts: ReadOpts { is_exclusive: true, is_ifetch: true },
            region: "generic-region".into(),
        },
        Event::WriteMem {
            value: 3,
            write_kind: Val::Unit,
            address: Val::Unit,
            data: Val::Unit,
            bytes: 7,
            tag_value: Some(Val::Unit),
            opts: WriteOpts { is_exclusive: true },
            region: "generic-region".into(),
        },
        Event::MarkReg { regs: vec![Name::from_u32(9)], mark: "text".into() },
        Event::AddressAnnounce { address: Val::Unit },
        Event::Branch { address: Val::Unit },
        Event::Cycle,
        Event::Instr(Val::Unit),
        Event::Assume(AssumeExp::Var(Loc::Id("a".into()))),
        Event::AssumeFun { name: Name::from_u32(9), args: vec![Val::Unit], return_value: Val::Unit },
        Event::UseFunAssumption { name: Name::from_u32(9), args: vec![Val::Unit], return_value: Val::Unit },
    ];
    for value in values {
        roundtrip(&value);
        let core: isla_lib::smt::Event<B64> = value.clone().into();
        let restored: Event<B64> = core.into();
        assert_eq!(value, restored);
    }
}
#[test]
fn all_regionpoint_variants() {
    let values: Vec<RegionPoint> = vec![RegionPoint::Instruction(5), RegionPoint::FunctionExit];
    for value in values {
        roundtrip(&value);
        let core: isla_lib::ir::regions::RegionPoint = value.clone().into();
        let restored: RegionPoint = core.into();
        assert_eq!(value, restored);
    }
}
