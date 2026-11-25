//! 每条改写都在无路径前提下证明差异不可满足。
use super::*;
use rewrite::{apply, BvRewrite};

fn variable<'ctx>(solver: &mut Solver<'ctx, B64>, width: u32) -> Ast<'ctx> {
    let sym = solver.declare_bitvector(width, SourceLoc::unknown());
    solver.translate_exp(&Exp::Var(sym))
}

fn equivalent(context: &Context, a: &Ast, b: &Ast) {
    unsafe {
        let solver = Z3_mk_solver(context.z3_ctx);
        Z3_solver_inc_ref(context.z3_ctx, solver);
        let different = a.mk_eq(b).mk_not();
        Z3_solver_assert(context.z3_ctx, solver, different.z3_ast);
        assert_eq!(Z3_solver_check(context.z3_ctx, solver), Z3_L_FALSE);
        Z3_solver_dec_ref(context.z3_ctx, solver);
    }
}

#[test]
fn mask_identity_all_symbolic_values_and_operand_orders() {
    configure_tastic(Tactic::Qfaufbv);
    for width in [1, 2, 3, 8, 64, 128] {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let a = variable(&mut solver, width);
        let b = variable(&mut solver, width);
        for xor in [a.mk_bvxor(&b), b.mk_bvxor(&a)] {
            for inner in [a.mk_bvnot().mk_bvor(&xor), xor.mk_bvor(&a.mk_bvnot())] {
                let original = inner.mk_bvnot();
                let rewritten = apply(original.clone(), BvRewrite::parse("mask-and").unwrap());
                assert!(unsafe { Z3_is_eq_ast(context.z3_ctx, rewritten.z3_ast, a.mk_bvand(&b).z3_ast) });
                equivalent(&context, &original, &rewritten);
                let unchanged = apply(original.clone(), BvRewrite::parse("false").unwrap());
                assert_eq!(original.z3_ast, unchanged.z3_ast);
            }
        }
    }
}

#[test]
fn sign_bound_exhaustive_small_widths_and_rejected_boundaries() {
    configure_tastic(Tactic::Qfaufbv);
    for m in 1..=4 {
        for n in m + 1..=6 {
            let context = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&context);
            let base = variable(&mut solver, m);
            for c in 0..1u64 << n {
                for mut extended in [base.sign_extend(n - m), base.sign_extend(n - m)] {
                    // 默认化简会把符号扩展变成重复符号位的 concat。
                    if c % 2 == 0 {
                        extended.simplify();
                    }
                    let original = extended.mk_bvule(&Ast::mk_bv_u64(&context, n, c));
                    let result = apply(original.clone(), BvRewrite::parse("sign-bound").unwrap());
                    let expected = c >= (1 << (m - 1)) - 1 && c < (1 << (n - 1));
                    assert_eq!(result.z3_ast != original.z3_ast, expected, "m={m} n={n} c={c}");
                    equivalent(&context, &original, &result);
                }
            }
        }
    }
}

#[test]
fn data_ite_nested_shared_dag_is_equivalent_and_linear() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let info = SourceLoc::unknown();
    let ty = solver.get_enum(crate::ir::Name::from_u32(900), 3);
    let first = Ast::mk_enum_member(&solver.enums, ty, 0);
    let second = Ast::mk_enum_member(&solver.enums, ty, 1);
    let mut a = first.clone();
    let mut b = second.clone();
    for _ in 0..80 {
        let c = solver.declare_const(Ty::Bool, info);
        let c = solver.translate_exp(&Exp::Var(c));
        let next_a = c.ite(&a, &b);
        b = c.ite(&b, &a);
        a = next_a;
    }
    for original in [a.mk_eq(&first), first.mk_eq(&a), a.mk_eq(&b)] {
        let result = apply(original.clone(), BvRewrite::parse("data-ite-eq").unwrap());
        assert_ne!(result.z3_ast, original.z3_ast);
        equivalent(&context, &original, &result);
        let mut pending = vec![result.z3_ast];
        let mut seen = HashSet::new();
        while let Some(node) = pending.pop() {
            if !seen.insert(node) {
                continue;
            }
            unsafe {
                if Z3_get_ast_kind(context.z3_ctx, node) == AstKind::App {
                    let app = Z3_to_app(context.z3_ctx, node);
                    pending.extend(
                        (0..Z3_get_app_num_args(context.z3_ctx, app)).map(|i| Z3_get_app_arg(context.z3_ctx, app, i)),
                    );
                }
            }
        }
        assert!(seen.len() < 20000, "共享DAG不能按出现次数展开");
    }
}

#[test]
fn sign_bound_wide_and_non_sign_extension_inputs() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let x = variable(&mut solver, 12);
    let mut extended = x.sign_extend(116);
    extended.simplify();
    let original = extended.mk_bvule(&Ast::mk_bv_u64(&context, 128, 0x10000000));
    let result = apply(original.clone(), BvRewrite::parse("sign-bound").unwrap());
    assert_ne!(original.z3_ast, result.z3_ast);
    equivalent(&context, &original, &result);
    let high = variable(&mut solver, 1);
    let wrong = high.mk_concat(&x);
    let original = wrong.mk_bvule(&Ast::mk_bv_u64(&context, 13, 4095));
    assert_eq!(apply(original.clone(), BvRewrite::parse("sign-bound").unwrap()).z3_ast, original.z3_ast);
    let limit = variable(&mut solver, 128);
    let original = extended.mk_bvule(&limit);
    assert_eq!(apply(original.clone(), BvRewrite::parse("sign-bound").unwrap()).z3_ast, original.z3_ast);
}

#[test]
fn definitions_published_buffered_guards_goals_and_no_smt_share_rewrite() {
    configure_tastic(Tactic::Qfaufbv);
    for no_smt in [false, true] {
        let mut config = Config::new();
        config.solver_options.no_smt = no_smt;
        let context = Context::new(config);
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let x = solver.declare_bitvector(12, info);
        let extended = solver.define_const(Exp::SignExtend(52, Box::new(Exp::Var(x))), info);
        let goal = Exp::Bvule(Box::new(Exp::Var(extended)), Box::new(smtlib::bits64(0x10000000, 64)));
        let value = solver.define_const(goal.clone(), info);
        let ast = solver.translate_exp(&Exp::Var(value));
        assert!(ast.rewrite_kind(DeclKind::EQ));
        solver.assert(goal.clone());
        let transaction = solver.start_transaction_with_guard(Some(goal.clone()));
        solver.assert(goal.clone());
        let buffered = solver.transaction_assertions();
        assert!(!buffered.is_empty());
        assert!(buffered.iter().all(|a| a.rewrite_kind(DeclKind::EQ)));
        let queried = solver.with_transaction_condition(&goal, |s| s.translate_exp(&goal));
        assert!(queried.rewrite_kind(DeclKind::EQ));
        let tautology = Exp::Or(Box::new(goal.clone()), Box::new(Exp::Not(Box::new(goal))));
        assert_eq!(solver.structural_bool(&tautology), Some(true));
        solver.rollback_transaction(transaction);
    }
}

#[test]
fn data_ite_equality_is_also_rewritten_inside_neq_translation() {
    configure_tastic(Tactic::Qfaufbv);
    let mut cfg = Config::new();
    cfg.solver_options.bv_rewrite = BvRewrite::parse("data-ite-eq").unwrap();
    let context = Context::new(cfg);
    let mut solver = Solver::<B64>::new(&context);
    let info = SourceLoc::unknown();
    let id = solver.get_enum(crate::ir::Name::from_u32(901), 3);
    let first = Exp::Enum(EnumMember { enum_id: id, member: 0 });
    let second = Exp::Enum(EnumMember { enum_id: id, member: 1 });
    let condition = solver.declare_const(Ty::Bool, info);
    let source = Exp::Ite(Box::new(Exp::Var(condition)), Box::new(first.clone()), Box::new(second));
    let defined = solver.define_const(source, info);
    let eq = solver.translate_exp(&Exp::Eq(Box::new(first.clone()), Box::new(Exp::Var(defined))));
    assert!(eq.rewrite_kind(DeclKind::ITE));
    let neq = solver.translate_exp(&Exp::Neq(Box::new(first), Box::new(Exp::Var(defined))));
    assert_eq!(neq.z3_ast, eq.mk_not().z3_ast, "neq 必须复用展开后的相等判断");
}

#[test]
fn repeated_first_binding_read_reuses_identical_small_input() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let x = variable(&mut solver, 8);
    let raw = x.mk_bvadd(&Ast::mk_bv_u64(&ctx, 8, 7));
    let mut expected = raw.clone();
    expected.simplify();
    AST_SIMPLIFY_CALLS.set(0);
    for _ in 0..16 {
        let binding = ConstBinding::new(raw.clone(), true, false);
        assert_eq!(binding.ast().z3_ast, expected.z3_ast);
    }
    assert_eq!(AST_SIMPLIFY_CALLS.get(), 1);
}

#[test]
fn data_enum_leaf_equalities_match_original_constant_without_simplifying() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let id = solver.get_enum(Name::from_u32(17), 2);
    let first = Ast::mk_enum_member(&solver.enums, id, 0);
    let second = Ast::mk_enum_member(&solver.enums, id, 1);
    let guard = variable(&mut solver, 1).mk_eq(&Ast::mk_bv_u64(&ctx, 1, 1));
    let original = guard.ite(&first, &second).mk_eq(&first);
    let mut equal = first.mk_eq(&first);
    equal.simplify();
    let mut different = second.mk_eq(&first);
    different.simplify();
    let expected = guard.ite(&equal, &different);
    AST_SIMPLIFY_CALLS.set(0);
    assert_eq!(apply(original, BvRewrite::parse("data-ite-eq").unwrap()).z3_ast, expected.z3_ast);
    assert_eq!(AST_SIMPLIFY_CALLS.get(), 0);
}

#[test]
fn multiplication_reuses_exact_implicit_extension_checks() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let a = variable(&mut solver, 8);
    let b = variable(&mut solver, 8);
    let mut a = a.zero_extend(8);
    let mut b = b.zero_extend(8);
    a.simplify();
    b.simplify();
    let expected = a.mk_bvmul(&b);
    AST_SIMPLIFY_CALLS.set(0);
    for _ in 0..16 {
        assert_eq!(a.mk_bvmul(&b).z3_ast, expected.z3_ast);
    }
    assert_eq!(AST_SIMPLIFY_CALLS.get(), 0);
}

#[test]
fn verified_small_fixpoint_is_shared_by_plain_simplification() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let mut term = variable(&mut solver, 8);
    let raw = term.z3_ast;
    term.simplify_small();
    assert_eq!(term.z3_ast, raw);
    let mut independent = term.clone();
    AST_SIMPLIFY_CALLS.set(0);
    independent.simplify();
    assert_eq!(independent.z3_ast, raw);
    assert_eq!(AST_SIMPLIFY_CALLS.get(), 1, "此前的原生输出必须复验一次");
    AST_SIMPLIFY_CALLS.set(0);
    term.simplify();
    assert_eq!(term.z3_ast, raw);
    assert_eq!(AST_SIMPLIFY_CALLS.get(), 0);
}

#[test]
fn first_read_reuses_terminal_choices_and_preserves_native_results() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let left = variable(&mut solver, 8);
    let right = variable(&mut solver, 8);
    let guard = variable(&mut solver, 32);
    let low = guard.extract(3, 1);
    let choices: Vec<_> = (0..8).map(|i| low.mk_eq(&Ast::mk_bv_u64(&ctx, 3, i))).collect();
    let mut rng = 0xf010_9c21_u32;
    let mut native_calls = 0;
    for _ in 0..768 {
        rng ^= rng << 13;
        rng ^= rng >> 17;
        rng ^= rng << 5;
        let condition = &choices[(rng & 7) as usize];
        let a = if rng & 8 == 0 { &left } else { &right };
        let b = Ast::mk_bv_u64(&ctx, 8, (rng >> 4 & 3) as u64);
        let input = condition.ite(a, &b);
        let mut native = input.clone();
        native.simplify_native();
        let before = AST_SIMPLIFY_CALLS.get();
        let binding = ConstBinding::new(input.clone(), true, true);
        let result = binding.ast();
        native_calls += AST_SIMPLIFY_CALLS.get() - before;
        assert_eq!(binding.raw_ast().z3_ast, input.z3_ast);
        assert_eq!(result.z3_ast, native.z3_ast);
        equivalent(&ctx, &input, &result);
    }
    assert_eq!(native_calls, 8, "768 次首次读只需化简八个不同选择条件");
}

#[test]
fn first_read_preserves_staged_literal_recognition() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let a = variable(&mut solver, 8);
    let b = variable(&mut solver, 8);
    let p = a.mk_bvsub(&b).mk_eq(&a.mk_bvadd(&Ast::mk_bv_u64(&ctx, 8, 3)));
    let mut q = p.clone();
    q.simplify_native();
    q.simplify_native();
    let binding = ConstBinding::new(p.clone(), true, false);
    let staged = ConstBinding::new(binding.ast().mk_eq(&q), true, false).ast();
    let mut reference = p.clone();
    reference.simplify_native();
    reference = reference.mk_eq(&q);
    reference.simplify_native();
    assert_eq!(staged.get_bool_value(), reference.get_bool_value());
    assert_eq!(staged.get_bool_value(), Some(true));
    equivalent(&ctx, &p.mk_eq(&q), &staged);
}

#[test]
fn first_read_terminal_choices_release_their_branches() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let [a, b, c] = std::array::from_fn(|_| {
        let sym = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        solver.translate_exp(&Exp::Var(sym))
    });
    let [x, y, z, w] = std::array::from_fn(|_| variable(&mut solver, 8));
    let left = ConstBinding::new(a.ite(&x, &y), true, false).ast();
    let right = ConstBinding::new(b.ite(&z, &w), true, false).ast();
    let cut = c.ite(&left, &right).extract(2, 0);
    // 两个内层 ITE 仍被引用时，原生 extract 保持在树根。
    let kept = ConstBinding::new(cut.clone(), true, false).ast();
    assert_eq!(kept.z3_ast, cut.z3_ast);
    drop((left, right));
    // 释放内层引用后必须重新运行原生 extract，允许它下推到叶端。
    let freed = ConstBinding::new(cut.clone(), true, false).ast();
    let mut reference = cut.clone();
    reference.simplify_native();
    assert_ne!(kept.z3_ast, freed.z3_ast);
    assert_eq!(reference.z3_ast, freed.z3_ast);
    equivalent(&ctx, &cut, &freed);
}

#[test]
fn definition_and_branch_consume_only_the_bits_they_need() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let a = solver.declare_bitvector(64, info);
    let b = solver.declare_bitvector(64, info);
    let data = solver.define_const(Exp::Bvadd(Box::new(Exp::Var(a)), Box::new(Exp::Var(b))), info);
    let wide = solver.define_const(Exp::ZeroExtend(128, Box::new(Exp::Var(data))), info);
    let mut calls = AST_SIMPLIFY_CALLS.get();
    let high = solver.define_const(Exp::Extract(191, 64, Box::new(Exp::Var(wide))), info);
    let value = solver.translate_exp(&Exp::Var(high));
    assert_eq!(value.get_numeral_u64().unwrap(), 0);
    assert_eq!(AST_SIMPLIFY_CALLS.get(), calls, "只取零扩展区，不需要化简低位");
    let raw = solver.decls[&wide].raw_ast().extract(191, 64);
    equivalent(&ctx, &value, &raw);

    let slice = Exp::Extract(19, 12, Box::new(Exp::Var(a)));
    let check = Exp::Eq(Box::new(slice), Box::new(smtlib::bits64(37, 8)));
    let predicate = solver.define_const(check, info);
    calls = AST_SIMPLIFY_CALLS.get();
    assert_eq!(solver.branch_structural_bool(&Exp::Var(predicate)), None);
    assert_eq!(AST_SIMPLIFY_CALLS.get(), calls, "切片等于常量既可真也可假");
    // 展开表达式的消费者仍取得原生残余。
    let mut expected = solver.decls[&predicate].raw_ast();
    expected.simplify_native();
    assert_eq!(solver.translate_exp(&Exp::Var(predicate)).z3_ast, expected.z3_ast);
}

#[test]
fn native_assert_consumes_boolean_binding_without_forcing_it() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let loc = SourceLoc::unknown();
    let a = solver.declare_bitvector(8, loc);
    let b = solver.declare_bitvector(8, loc);
    let source =
        Exp::Eq(Box::new(Exp::Bvsub(Box::new(Exp::Var(a)), Box::new(Exp::Var(b)))), Box::new(smtlib::bits64(7, 8)));
    let p = solver.define_const(source, loc);
    let before = AST_SIMPLIFY_CALLS.get();
    solver.assert(Exp::Var(p));
    solver.assert(Exp::Not(Box::new(Exp::Var(p))));
    assert_eq!(AST_SIMPLIFY_CALLS.get(), before, "原生断言可直接消费绑定的布尔表达式");
    assert_eq!(unsafe { Z3_solver_check(ctx.z3_ctx, solver.z3_solver) }, Z3_L_FALSE);
}
