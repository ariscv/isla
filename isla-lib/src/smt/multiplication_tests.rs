//! 乘积降宽必须保持所有位，不能靠路径前提跳过整数溢出检查。
use super::*;

fn variable<'ctx>(solver: &mut Solver<'ctx, B64>, width: u32) -> Ast<'ctx> {
    let symbol = solver.declare_bitvector(width, SourceLoc::unknown());
    solver.translate_exp(&smtlib::Exp::Var(symbol))
}

fn extend<'ctx>(value: &Ast<'ctx>, by: u32, signed: bool) -> Ast<'ctx> {
    if signed {
        value.sign_extend(by)
    } else {
        value.zero_extend(by)
    }
}

#[test]
fn extended_multiplication_preserves_all_bits_for_signed_unsigned_and_mixed_inputs() {
    configure_tastic(Tactic::Qfaufbv);
    for (lw, rw) in [(2, 2), (3, 4), (4, 3), (4, 4)] {
        for (ls, rs) in [(true, true), (false, false), (true, false), (false, true)] {
            for canonical in [false, true] {
                let context = Context::new(Config::new());
                let mut solver = Solver::<B64>::new(&context);
                let mut left = extend(&variable(&mut solver, lw), 16 - lw, ls);
                let mut right = extend(&variable(&mut solver, rw), 16 - rw, rs);
                if canonical {
                    left.simplify();
                    right.simplify();
                }
                let original = z3_binary_op!(Z3_mk_bvmul, left, right);
                let rewritten = left.mk_bvmul(&right);
                assert!(!unsafe { Z3_is_eq_ast(context.z3_ctx, original.z3_ast, rewritten.z3_ast) });
                unsafe {
                    let query = Z3_mk_solver(context.z3_ctx);
                    Z3_solver_inc_ref(context.z3_ctx, query);
                    let unequal = original.mk_eq(&rewritten).mk_not();
                    Z3_solver_assert(context.z3_ctx, query, unequal.z3_ast);
                    let result = Z3_solver_check(context.z3_ctx, query);
                    Z3_solver_dec_ref(context.z3_ctx, query);
                    assert_eq!(result, Z3_L_FALSE, "与原生乘法在完整输入域等价");
                }
            }
        }
    }
}

#[test]
fn default_mux_multiplication_range_proof_simplifies_without_bit_blasting() {
    const CHILD: &str = "ISLA_MULTIPLICATION_DEFAULT_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "smt::multiplication_tests::default_mux_multiplication_range_proof_simplifies_without_bit_blasting",
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
    for (ls, rs) in [(true, true), (true, false), (false, true)] {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let a = variable(&mut solver, 32);
        let b = variable(&mut solver, 32);
        let c = variable(&mut solver, 32);
        let selected = a.mk_bvslt(&Ast::mk_bv_u64(&context, 32, 0)).ite(&a, &b);
        let mut left = extend(&selected, 96, ls);
        let mut right = extend(&c, 96, rs);
        left.simplify();
        right.simplify();
        let product = left.mk_bvmul(&right);
        let mut in_range = product.mk_eq(&product.extract(63, 0).sign_extend(64));
        in_range.simplify();
        assert!(
            unsafe { Z3_is_eq_ast(context.z3_ctx, in_range.z3_ast, Ast::mk_bool(&context, true).z3_ast) },
            "完整32位乘积应直接证明可放入i64"
        );
    }
}

#[test]
fn multiplication_keeps_native_encoding_when_full_product_does_not_fit() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    for (lw, rw) in [(16, 16), (9, 9), (8, 8)] {
        let left = variable(&mut solver, lw).sign_extend(16 - lw);
        let right = variable(&mut solver, rw).zero_extend(16 - rw);
        let original = z3_binary_op!(Z3_mk_bvmul, left, right);
        assert!(unsafe { Z3_is_eq_ast(context.z3_ctx, original.z3_ast, left.mk_bvmul(&right).z3_ast) });
    }
}

#[test]
fn unsigned_32_bit_product_may_exceed_signed_64_bit_range() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let left = Ast::mk_bv_u64(&context, 32, u32::MAX as u64).zero_extend(96);
    let right = Ast::mk_bv_u64(&context, 32, u32::MAX as u64).zero_extend(96);
    let product = left.mk_bvmul(&right);
    let mut in_range = product.mk_eq(&product.extract(63, 0).sign_extend(64));
    in_range.simplify();
    assert!(unsafe { Z3_is_eq_ast(context.z3_ctx, in_range.z3_ast, Ast::mk_bool(&context, false).z3_ast) });
}
