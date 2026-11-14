//! 余数编码必须对完整位向量域恒等，包括零除数和符号位。
use super::*;

fn prove_equal(solver: &Solver<B64>, original: &Ast, rewritten: &Ast) {
    unsafe {
        let query = Z3_mk_solver(solver.ctx.z3_ctx);
        Z3_solver_inc_ref(solver.ctx.z3_ctx, query);
        let unequal = original.mk_eq(rewritten).mk_not();
        Z3_solver_assert(solver.ctx.z3_ctx, query, unequal.z3_ast);
        let result = Z3_solver_check(solver.ctx.z3_ctx, query);
        Z3_solver_dec_ref(solver.ctx.z3_ctx, query);
        assert_eq!(result, Z3_L_FALSE, "原始编码与改写必须在无额外前提下恒等");
    }
}

fn variable<'ctx>(solver: &mut Solver<'ctx, B64>, width: u32) -> Ast<'ctx> {
    let symbol = solver.declare_bitvector(width, SourceLoc::unknown());
    solver.translate_exp(&smtlib::Exp::Var(symbol))
}

#[test]
fn signed_remainder_symbolic_power_of_two_is_equivalent() {
    configure_tastic(Tactic::Qfaufbv);
    for width in [1, 4, 8] {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let value = variable(&mut solver, width);
        let shift = variable(&mut solver, width);
        let one = Ast::mk_bv_u64(&context, width, 1);
        let divisor = one.mk_bvshl(&shift);
        let original = z3_binary_op!(Z3_mk_bvsrem, value, divisor);
        let rewritten = value.mk_bvsrem(&divisor);
        assert!(
            !unsafe { Z3_is_eq_ast(context.z3_ctx, original.z3_ast, rewritten.z3_ast) },
            "应去掉符号幂除数的除余电路"
        );
        prove_equal(&solver, &original, &rewritten);
    }
}

#[test]
fn signed_remainder_128_bit_boundaries_are_equivalent() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let value = variable(&mut solver, 128);
    let one = Ast::mk_bv_u64(&context, 128, 1);
    for shift in [0, 1, 3, 63, 64, 126, 127, 128, 255] {
        let divisor = one.mk_bvshl(&Ast::mk_bv_u64(&context, 128, shift));
        let original = z3_binary_op!(Z3_mk_bvsrem, value, divisor);
        prove_equal(&solver, &original, &value.mk_bvsrem(&divisor));
    }
    let minus_one = one.mk_bvneg();
    let divisor = one.mk_bvshl(&minus_one);
    let original = z3_binary_op!(Z3_mk_bvsrem, value, divisor);
    prove_equal(&solver, &original, &value.mk_bvsrem(&divisor));
}

#[test]
fn signed_remainder_nested_ite_divisor_is_equivalent() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let value = variable(&mut solver, 8);
    let shift = variable(&mut solver, 8);
    let zero = Ast::mk_bv_u64(&context, 8, 0);
    let one = Ast::mk_bv_u64(&context, 8, 1);
    let condition = value.mk_bvslt(&zero);
    let divisor = condition.ite(&zero, &shift.mk_bvslt(&zero).ite(&one, &one.mk_bvshl(&shift)));
    let original = z3_binary_op!(Z3_mk_bvsrem, value, divisor);
    let rewritten = value.mk_bvsrem(&divisor);
    assert!(!unsafe { Z3_is_eq_ast(context.z3_ctx, original.z3_ast, rewritten.z3_ast) });
    prove_equal(&solver, &original, &rewritten);
}

#[test]
fn general_divisors_keep_original_encoding() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let value = variable(&mut solver, 8);
    let arbitrary = variable(&mut solver, 8);
    let zero = Ast::mk_bv_u64(&context, 8, 0);
    let one = Ast::mk_bv_u64(&context, 8, 1);
    let three = Ast::mk_bv_u64(&context, 8, 3);
    for divisor in
        [arbitrary.clone(), three.clone(), three.mk_bvshl(&arbitrary), value.mk_bvslt(&zero).ite(&one, &three)]
    {
        let original = z3_binary_op!(Z3_mk_bvsrem, value, divisor);
        let result = value.mk_bvsrem(&divisor);
        assert!(unsafe { Z3_is_eq_ast(context.z3_ctx, original.z3_ast, result.z3_ast) });
    }
}

#[test]
fn operator_named_uninterpreted_function_is_not_rewritten() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let value = variable(&mut solver, 8);
    let one = Ast::mk_bv_u64(&context, 8, 1);
    unsafe {
        let ctx = context.z3_ctx;
        let name = CString::new("bvshl").unwrap();
        let symbol = Z3_mk_string_symbol(ctx, name.as_ptr());
        let sort = Z3_get_sort(ctx, value.z3_ast);
        let declaration = Z3_mk_func_decl(ctx, symbol, 2, [sort, sort].as_ptr(), sort);
        Z3_inc_ref(ctx, Z3_func_decl_to_ast(ctx, declaration));
        let node = Z3_mk_app(ctx, declaration, 2, [one.z3_ast, value.z3_ast].as_ptr());
        Z3_inc_ref(ctx, node);
        let divisor = Ast { z3_ast: node, ctx: &context };
        let original = z3_binary_op!(Z3_mk_bvsrem, value, divisor);
        assert!(Z3_is_eq_ast(ctx, original.z3_ast, value.mk_bvsrem(&divisor).z3_ast));
        Z3_dec_ref(ctx, Z3_func_decl_to_ast(ctx, declaration));
    }
}

#[test]
fn syntax_recognition_budget_keeps_original_encoding() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let value = variable(&mut solver, 8);
    let shift = variable(&mut solver, 8);
    let mut divisor = Ast::mk_bv_u64(&context, 8, 1);
    for _ in 0..40 {
        divisor = divisor.mk_bvshl(&shift);
    }
    let original = z3_binary_op!(Z3_mk_bvsrem, value, divisor);
    assert!(unsafe { Z3_is_eq_ast(context.z3_ctx, original.z3_ast, value.mk_bvsrem(&divisor).z3_ast) });
}
