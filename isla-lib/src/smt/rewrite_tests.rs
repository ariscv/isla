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
    configure_tastic(Tactic::Default);
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
                let unchanged = apply(original.clone(), BvRewrite::default());
                assert_eq!(original.z3_ast, unchanged.z3_ast);
            }
        }
    }
}

#[test]
fn sign_bound_exhaustive_small_widths_and_rejected_boundaries() {
    configure_tastic(Tactic::Default);
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
    configure_tastic(Tactic::Default);
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
    configure_tastic(Tactic::Default);
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
    configure_tastic(Tactic::Default);
    for no_smt in [false, true] {
        let mut config = Config::new();
        config.solver_options.no_smt = no_smt;
        config.solver_options.bv_rewrite = BvRewrite::parse("true").unwrap();
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
    configure_tastic(Tactic::Default);
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
