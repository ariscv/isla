use super::*;
use crate::bitvector::b64::B64;
use Exp::*;

fn eq(sym: Sym, n: u64) -> Exp<Sym> {
    Eq(Box::new(Var(sym)), Box::new(bits64(n, 8)))
}

fn allowed(sym: Sym) -> Exp<Sym> {
    Or(Box::new(eq(sym, 1)), Box::new(eq(sym, 2)))
}

fn native_config() -> Config {
    configure_tastic(Tactic::Qfaufbv);
    let mut cfg = Config::new();
    cfg.solver_options.finite_domain_ground_eval = false;
    cfg
}

#[test]
fn branch_sparse_rebuild_shares_neighbouring_assertions() {
    let ctx = Context::new(native_config());
    let mut solver = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    let y = solver.declare_bitvector(8, info);
    let mut shared = Var(y);
    for _ in 0..45 {
        shared = Bvmul(Box::new(shared), Box::new(bits64(3, 8)));
    }
    let diamond = Bvadd(Box::new(Var(x)), Box::new(shared.clone()));
    for i in 0..32 {
        let fact = Eq(Box::new(Bvadd(Box::new(diamond.clone()), Box::new(diamond.clone()))), Box::new(bits64(i, 8)));
        solver.assert(Or(Box::new(fact), Box::new(eq(x, 1))));
    }
    let prefix = PathConditions::new(&solver).unwrap();
    let anchor = solver.translate_exp(&Var(x));
    let candidate = Ast::mk_bv_u64(&ctx, 8, 2);
    let old = prefix.assertions().any(|exp| {
        let original = solver.translate_projection_assertion(exp);
        let mut residual = original.substitute(&anchor, &candidate);
        original.z3_ast != residual.z3_ast && residual.structural_bool() == Some(false)
    });
    PROJECT_SUBSTITUTIONS.set(0);
    assert_eq!(prefix.excludes_branch_candidate(&solver, &anchor, &candidate), old);
    assert!(PROJECT_SUBSTITUTIONS.get() < 4, "整式代入次数 {}", PROJECT_SUBSTITUTIONS.get());
}

#[test]
fn joint_sparse_rebuild_preserves_simultaneous_pairs_and_binders() {
    let ctx = Context::new(native_config());
    let solver = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let mut solver = solver;
    let [x, y, z, local] = std::array::from_fn(|_| {
        let sym = solver.declare_bitvector(8, info);
        solver.translate_exp(&Var(sym))
    });
    let shared = (0..48).fold(x.clone(), |term, _| term.mk_bvadd(&term).mk_bvadd(&z));
    let body = y.mk_eq(&local);
    let quantified = unsafe {
        let bound = Z3_to_app(ctx.z3_ctx, local.z3_ast);
        let term = Z3_mk_forall_const(ctx.z3_ctx, 0, 1, &bound, 0, ptr::null(), body.z3_ast);
        {
            Z3_inc_ref(ctx.z3_ctx, term);
            Ast { ctx: &ctx, z3_ast: term }
        }
    };
    let roots: Vec<_> = (0..24)
        .map(|i| {
            let k = Ast::mk_bv_u64(&ctx, 8, i);
            shared.mk_eq(&k).mk_and(&quantified.mk_or(&shared.mk_eq(&z)))
        })
        .collect();
    let pairs = [(x.z3_ast, y.z3_ast), (y.z3_ast, z.z3_ast)];
    let rewrites = rewrites::Rewrites::new(&ctx);
    PROJECT_SUBSTITUTIONS.set(0);
    let mut deps = rewrites::InputDependencies::new(pairs.iter().map(|&(from, _)| from).enumerate());
    let actual: Vec<_> = roots.iter().map(|root| rewrites.narrow(&pairs, root, &mut deps)).collect();
    let calls = PROJECT_SUBSTITUTIONS.get();
    for (root, (unchanged, truth, actual)) in roots.iter().zip(actual) {
        let mut expected = root.substitute_many(&[x.z3_ast, y.z3_ast], &[y.z3_ast, z.z3_ast]);
        assert_eq!(unchanged, expected.z3_ast == root.z3_ast);
        assert_eq!(truth, expected.structural_bool());
        assert_eq!(actual.z3_ast, expected.z3_ast);
    }
    assert!(calls < roots.len() / 2, "原生代入次数 {calls}");
}

#[test]
fn exact_boolean_simplification_reuses_input_not_assumed_output() {
    let ctx = Context::new(native_config());
    let mut solver = Solver::<B64>::new(&ctx);
    let x = solver.declare_bitvector(8, SourceLoc::unknown());
    let ast = solver.translate_exp(&eq(x, 1)).mk_not().mk_not();
    AST_SIMPLIFY_CALLS.set(0);
    let mut first = ast.clone();
    let expected = first.structural_bool();
    for _ in 0..8 {
        let mut next = ast.clone();
        assert_eq!(next.structural_bool(), expected);
        assert_eq!(next.z3_ast, first.z3_ast);
    }
    assert_eq!(AST_SIMPLIFY_CALLS.get(), 1);
}

#[test]
fn ordinary_prefix_survives_guards_and_rechecks_replaced_suffix() {
    let ctx = Context::new(native_config());
    let mut solver = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    let g = solver.declare_const(Ty::Bool, info);
    for n in 0..32 {
        solver.assert(Or(Box::new(eq(x, n)), Box::new(allowed(x))));
    }
    let check = |solver: &Solver<'_, B64>| {
        let prefix = PathConditions::new(solver).unwrap();
        let anchor = solver.translate_exp(&Var(x));
        let value = Ast::mk_bv_u64(&ctx, 8, 1);
        prefix.excludes_branch_candidate(solver, &anchor, &value)
    };
    assert!(!check(&solver));
    PROJECT_TRANSLATIONS.set(0);
    STRUCTURAL_BOOLS.set(0);
    let inner = solver.start_transaction_with_guard(Some(Var(g)));
    assert!(!check(&solver));
    assert_eq!(PROJECT_TRANSLATIONS.get(), 1, "只翻译新增守卫");
    assert_eq!(STRUCTURAL_BOOLS.get(), 0, "守卫切换不重新检查普通断言");
    solver.assert(Not(Box::new(eq(x, 1))));
    assert!(check(&solver));
    solver.rollback_transaction(inner);
    let inner = solver.start_transaction_with_guard(Some(Var(g)));
    solver.assert(Not(Box::new(eq(x, 2))));
    assert!(!check(&solver), "撤回后缀后必须允许候选复活");
    solver.rollback_transaction(inner);
}

#[test]
fn after_narrow_does_not_simplify_decided_truth_again() {
    let ctx = Context::new(native_config());
    let mut solver = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    let y = solver.declare_bitvector(8, info);
    solver.assert(allowed(x));
    solver.assert(allowed(y));
    solver.assert(Not(Box::new(Eq(Box::new(Var(x)), Box::new(Var(y))))));
    let sum = solver.define_const(Bvadd(Box::new(Var(x)), Box::new(Var(y))), info);
    AFTER_NARROW.set(0);
    assert_eq!(solver.finite_domain(sum), FiniteDomain::Known(vec![bits64(3, 8)]));
    assert_eq!(AFTER_NARROW.get(), 0);
}

#[test]
fn independent_branch_predicate_omits_noop_substitution_but_keeps_empty_domain() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    let b = solver.declare_const(Ty::Bool, info);
    solver.assert(allowed(x));
    let p = solver.define_const(Or(Box::new(And(Box::new(eq(x, 1)), Box::new(Bool(false)))), Box::new(Var(b))), info);
    PROJECT_SUBSTITUTIONS.set(0);
    assert_eq!(solver.finite_domain_bool(&Var(p)), None);
    assert_eq!(PROJECT_SUBSTITUTIONS.get(), 0);
    solver.assert(Not(Box::new(eq(x, 1))));
    solver.assert(Not(Box::new(eq(x, 2))));
    assert_eq!(solver.finite_domain_bool(&Var(p)), Some(false));
    assert_eq!(solver.finite_domain_bool(&Not(Box::new(Var(p)))), Some(false));
}

#[test]
fn randomized_joint_rewrites_match_original_structure_with_options_on_and_off() {
    let mut cfg = native_config();
    cfg.solver_options.structural_bool_cache = false;
    cfg.solver_options.joint_candidate_sparse_rewrite = false;
    let original_ctx = Context::new(cfg);
    let candidate_ctx = Context::new(native_config());
    let original_rewrites = rewrites::Rewrites::new(&original_ctx);
    let candidate_rewrites = rewrites::Rewrites::new(&candidate_ctx);
    let mut original_solver = Solver::<B64>::new(&original_ctx);
    let mut candidate_solver = Solver::<B64>::new(&candidate_ctx);
    let info = SourceLoc::unknown();
    let symbols: [Sym; 4] = std::array::from_fn(|_| {
        let sym = original_solver.declare_bitvector(8, info);
        assert_eq!(sym, candidate_solver.declare_bitvector(8, info));
        sym
    });
    let [x, y, z, independent] = symbols.map(Var);
    let add = |a, b| Bvadd(Box::new(a), Box::new(b));
    let parent = add(x.clone(), y.clone());
    let diamond = add(parent.clone(), parent.clone());
    let unrelated = (0..24).fold(independent, |term, i| add(term, bits64(i * 11, 8)));
    let mut rng = 0xf010_9c21_u32;
    for _ in 0..768 {
        rng ^= rng << 13;
        rng ^= rng >> 17;
        rng ^= rng << 5;
        let number = bits64(u64::from(rng & 255), 8);
        let equality = Eq(Box::new(add(diamond.clone(), unrelated.clone())), Box::new(number.clone()));
        let another = Eq(Box::new(add(x.clone(), z.clone())), Box::new(number.clone()));
        let exp = match (rng >> 8) & 3 {
            0 => equality,
            1 => And(Box::new(equality), Box::new(another)),
            2 => Or(Box::new(equality), Box::new(another)),
            _ => Not(Box::new(equality)),
        };
        let parent_replacement = if (rng >> 10) & 1 == 0 { &parent } else { &number };
        let mut replacements = [(&parent, parent_replacement), (&x, &y), (&y, &z), (&x, &z)];
        replacements.rotate_left(((rng >> 11) & 3) as usize);
        let run = |solver: &Solver<'_, B64>, rewrites: &rewrites::Rewrites<'_>| {
            let original = solver.translate_exp(&exp);
            let replacements: Vec<_> =
                replacements.iter().map(|(a, b)| (solver.translate_exp(a), solver.translate_exp(b))).collect();
            let pairs: Vec<_> = replacements.iter().map(|(a, b)| (a.z3_ast, b.z3_ast)).collect();
            let mut deps = rewrites::InputDependencies::new(pairs.iter().map(|&(source, _)| source).enumerate());
            let (unchanged, truth, residual) = rewrites.narrow(&pairs, &original, &mut deps);
            (unchanged, truth, unsafe {
                CStr::from_ptr(Z3_ast_to_string(residual.ctx.z3_ctx, residual.z3_ast)).to_string_lossy().into_owned()
            })
        };
        assert_eq!(run(&candidate_solver, &candidate_rewrites), run(&original_solver, &original_rewrites));
    }
}
