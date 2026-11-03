use isla_lib::bitvector::{b64::B64, BV};
use isla_lib::ir::Val;
use isla_lib::primop::binary_primops;
use isla_lib::smt::{
    configure_tastic,
    smtlib::{Exp, Ty},
    Config, Context, Model, SmtResult, Solver, Tactic,
};
use isla_lib::source_loc::SourceLoc;

// 同一合法调用链在基线和审查分支都必须支持，避免只验证拼接本身。
fn check_append_arithmetic(operation: &str, prefix: bool, symbolic_integer: bool) {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let sym = solver.declare_const(Ty::BitVec(7), info);
    let primops = binary_primops::<B64>();
    let inputs = if prefix {
        (Val::Bits(B64::new(1, 1)), Val::Symbolic(sym))
    } else {
        (Val::Symbolic(sym), Val::Bits(B64::new(1, 1)))
    };
    let appended = primops["append"](inputs.0, inputs.1, &mut solver, info).unwrap();
    let integer = if symbolic_integer {
        let sym = solver.declare_const(Ty::BitVec(128), info);
        let mut bits = vec![false; 128];
        bits[0] = true;
        solver.assert_eq(Exp::Var(sym), Exp::Bits(bits));
        Val::Symbolic(sym)
    } else {
        Val::I128(1)
    };
    let result = primops[operation](appended, integer, &mut solver, info);
    assert!(result.is_ok(), "{operation}, prefix={prefix}, symbolic_integer={symbolic_integer}: {result:?}");
    solver.assert_eq(Exp::Var(sym), Exp::Bits64(B64::new(0x25, 7)));
    assert_eq!(solver.check_sat(info), SmtResult::Sat);
    let base: u64 = if prefix { 0xa5 } else { 0x4b };
    let expected = if operation == "add_bits_int" { base + 1 } else { base - 1 };
    assert_eq!(Model::new(&solver).get_val(&result.unwrap()).unwrap(), Val::Bits(B64::new(expected, 8)));
}

#[test]
fn add_bits_int_suffix_concrete_integer() {
    check_append_arithmetic("add_bits_int", false, false);
}

#[test]
fn add_bits_int_suffix_symbolic_integer() {
    check_append_arithmetic("add_bits_int", false, true);
}

#[test]
fn add_bits_int_prefix_concrete_integer() {
    check_append_arithmetic("add_bits_int", true, false);
}

#[test]
fn add_bits_int_prefix_symbolic_integer() {
    check_append_arithmetic("add_bits_int", true, true);
}

#[test]
fn sub_bits_int_suffix_concrete_integer() {
    check_append_arithmetic("sub_bits_int", false, false);
}

#[test]
fn sub_bits_int_suffix_symbolic_integer() {
    check_append_arithmetic("sub_bits_int", false, true);
}

#[test]
fn sub_bits_int_prefix_concrete_integer() {
    check_append_arithmetic("sub_bits_int", true, false);
}

#[test]
fn sub_bits_int_prefix_symbolic_integer() {
    check_append_arithmetic("sub_bits_int", true, true);
}
