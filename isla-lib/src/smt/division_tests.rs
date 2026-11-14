//! 符号扩展后的除法降宽必须保留正溢出和零除数的完整位向量语义。
use super::*;

fn variable<'ctx>(solver: &mut Solver<'ctx, B64>, width: u32) -> Ast<'ctx> {
    let symbol = solver.declare_bitvector(width, SourceLoc::unknown());
    solver.translate_exp(&smtlib::Exp::Var(symbol))
}

fn prove(context: &Context, premises: &[Ast], original: &Ast, rewritten: &Ast) {
    unsafe {
        let solver = Z3_mk_solver(context.z3_ctx);
        Z3_solver_inc_ref(context.z3_ctx, solver);
        for premise in premises {
            Z3_solver_assert(context.z3_ctx, solver, premise.z3_ast);
        }
        let unequal = original.mk_eq(rewritten).mk_not();
        Z3_solver_assert(context.z3_ctx, solver, unequal.z3_ast);
        let result = Z3_solver_check(context.z3_ctx, solver);
        Z3_solver_dec_ref(context.z3_ctx, solver);
        assert_eq!(result, Z3_L_FALSE, "必须由原生原式证明等价，不靠同一新编码自证");
    }
}

#[test]
fn signed_extended_division_matches_original_for_all_small_inputs() {
    configure_tastic(Tactic::Qfaufbv);
    for (left_width, right_width) in [(2, 2), (4, 4), (4, 8), (8, 4), (8, 8)] {
        for canonical in [false, true] {
            let context = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&context);
            let mut left = variable(&mut solver, left_width).sign_extend(32 - left_width);
            let mut right = variable(&mut solver, right_width).sign_extend(32 - right_width);
            if canonical {
                left.simplify();
                right.simplify();
            }
            let original = z3_binary_op!(Z3_mk_bvsdiv, left, right);
            let rewritten = left.mk_bvsdiv(&right);
            assert!(
                !unsafe { Z3_is_eq_ast(context.z3_ctx, original.z3_ast, rewritten.z3_ast) },
                "符号扩展运算应被降宽"
            );
            prove(&context, &[], &original, &rewritten);
        }
    }
}

#[test]
fn signed_division_64_min_over_minus_one_stays_positive_128() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let x = variable(&mut solver, 64);
    let y = variable(&mut solver, 64);
    let left = x.sign_extend(64);
    let right = y.sign_extend(64);
    let original = z3_binary_op!(Z3_mk_bvsdiv, left, right);
    let rewritten = left.mk_bvsdiv(&right);
    let premises =
        [x.mk_eq(&Ast::mk_bv_u64(&context, 64, 1u64 << 63)), y.mk_eq(&Ast::mk_bv_u64(&context, 64, u64::MAX))];
    let expected = solver.translate_exp(&crate::primop_util::smt_i128(1i128 << 63));
    prove(&context, &premises, &original, &rewritten);
    prove(&context, &premises, &rewritten, &expected);
}

#[test]
fn signed_extended_division_preserves_zero_divisor_signs() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let x = variable(&mut solver, 8);
    let y = variable(&mut solver, 8);
    let zero = Ast::mk_bv_u64(&context, 8, 0);
    let left = x.sign_extend(24);
    let right = y.sign_extend(24);
    let expected =
        x.mk_bvslt(&zero).ite(&Ast::mk_bv_u64(&context, 32, 1), &Ast::mk_bv_u64(&context, 32, u32::MAX as u64));
    prove(&context, &[y.mk_eq(&zero)], &left.mk_bvsdiv(&right), &expected);
}

#[test]
fn signed_division_does_not_infer_signed_range_from_zero_extension() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    for width in [1, 8, 32] {
        let x = variable(&mut solver, width);
        let y = variable(&mut solver, width);
        let left = if width == 32 {
            x
        } else if width == 1 {
            x.sign_extend(31)
        } else {
            x.zero_extend(24)
        };
        let right = if width == 32 {
            y
        } else if width == 1 {
            y.sign_extend(31)
        } else {
            y.zero_extend(24)
        };
        let original = z3_binary_op!(Z3_mk_bvsdiv, left, right);
        assert!(unsafe { Z3_is_eq_ast(context.z3_ctx, original.z3_ast, left.mk_bvsdiv(&right).z3_ast) });
    }
}

#[test]
fn default_signed_extension_of_mux_is_recognized_structurally() {
    const CHILD: &str = "ISLA_DIVISION_DEFAULT_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "smt::division_tests::default_signed_extension_of_mux_is_recognized_structurally",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        return;
    }
    configure_tastic(Tactic::Default);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let a = variable(&mut solver, 8);
    let b = variable(&mut solver, 8);
    let c = variable(&mut solver, 8);
    let selected = a.mk_bvslt(&Ast::mk_bv_u64(&context, 8, 0)).ite(&a, &b);
    let mut left = selected.sign_extend(24);
    left.simplify();
    let mut right = c.sign_extend(24);
    right.simplify();
    let original = z3_binary_op!(Z3_mk_bvsdiv, left, right);
    let rewritten = left.mk_bvsdiv(&right);
    assert!(!unsafe { Z3_is_eq_ast(context.z3_ctx, original.z3_ast, rewritten.z3_ast) });
    prove(&context, &[], &original, &rewritten);
}
