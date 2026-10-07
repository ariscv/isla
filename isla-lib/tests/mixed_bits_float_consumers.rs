use isla_lib::bitvector::{b129::B129, BV};
use isla_lib::ir::{FPTy, Val};
use isla_lib::primop::{binary_primops, unary_primops};
use isla_lib::smt::{
    configure_tastic,
    smtlib::{Exp, FPUnary, Ty},
    Config, Context, Model, SmtResult, Solver, Tactic,
};
use isla_lib::source_loc::SourceLoc;

// 测实际拼接结果进入所有 IEEE 宽度及两个整数转换族 的调用链。
#[test]
fn appended_ieee_bits_keep_their_value_in_each_format() {
    configure_tastic(Tactic::Qfaufbv);
    for width in [16_u32, 32, 64, 128] {
        for prefix in [false, true] {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let info = SourceLoc::unknown();
            let raw = B129::zeros(width).set_slice(width - 3, B129::BIT_ONE);
            let symbolic = if prefix { raw.slice(0, width - 1).unwrap() } else { raw.slice(1, width - 1).unwrap() };
            let fixed = if prefix { raw.slice(width - 1, 1).unwrap() } else { raw.slice(0, 1).unwrap() };
            let sym = solver.declare_const(Ty::BitVec(width - 1), info);
            let binary = binary_primops::<B129>();
            let (left, right) =
                if prefix { (Val::Bits(fixed), Val::Symbolic(sym)) } else { (Val::Symbolic(sym), Val::Bits(fixed)) };
            let appended = binary["append"](left, right, &mut solver, info).unwrap();
            assert!(matches!(appended, Val::MixedBits(_)));
            let fp = unary_primops::<B129>()[&format!("fp{width}_from_ieee")](appended, &mut solver, info).unwrap();
            let ty = match width {
                16 => FPTy::fp16(),
                32 => FPTy::fp32(),
                64 => FPTy::fp64(),
                128 => FPTy::fp128(),
                _ => unreachable!(),
            };
            let Val::Symbolic(fp) = fp else { panic!("转换应返回符号FP值") };
            let bits = solver.define_const(
                Exp::FPUnary(FPUnary::ToIEEE(ty.exponent_width(), ty.significand_width()), Box::new(Exp::Var(fp))),
                info,
            );
            solver.assert_eq(Exp::Var(sym), Exp::Bits(symbolic.to_vec()));
            assert_eq!(solver.check_sat(info), SmtResult::Sat);
            assert_eq!(Model::new(&solver).get_val(&Val::Symbolic(bits)).unwrap(), Val::Bits(raw));
        }
    }
}

#[test]
fn appended_integer_bits_can_be_converted_to_float() {
    configure_tastic(Tactic::Qfaufbv);
    for operation in ["fp32_from_signed", "fp32_from_unsigned"] {
        for prefix in [false, true] {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let info = SourceLoc::unknown();
            let primops = binary_primops::<B129>();
            let sym = solver.declare_const(Ty::BitVec(7), info);
            let (left, right, source) = if prefix {
                (Val::Bits(B129::new(0, 1)), Val::Symbolic(sym), 3)
            } else {
                (Val::Symbolic(sym), Val::Bits(B129::new(1, 1)), 1)
            };
            let appended = primops["append"](left, right, &mut solver, info).unwrap();
            let rm = unary_primops::<B129>()["round_nearest_ties_to_even"](Val::Unit, &mut solver, info).unwrap();
            let fp = primops[operation](rm, appended, &mut solver, info).unwrap();
            let Val::Symbolic(fp) = fp else { panic!("转换应返回符号FP值") };
            let bits = solver.define_const(Exp::FPUnary(FPUnary::ToIEEE(8, 24), Box::new(Exp::Var(fp))), info);
            solver.assert_eq(Exp::Var(sym), Exp::Bits(source_u7(source)));
            assert_eq!(solver.check_sat(info), SmtResult::Sat);
            assert_eq!(
                Model::new(&solver).get_val(&Val::Symbolic(bits)).unwrap(),
                Val::Bits(B129::new(3_f32.to_bits() as u64, 32))
            );
        }
    }
}

fn source_u7(value: u64) -> Vec<bool> {
    (0..7).map(|index| (value >> index) & 1 != 0).collect()
}
