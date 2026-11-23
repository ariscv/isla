use super::*;
use crate::bitvector::b64::B64;

fn equal(symbol: Sym, value: u64) -> Exp<Sym> {
    Exp::Eq(Box::new(Exp::Var(symbol)), Box::new(bits64(value, 8)))
}

fn not(exp: Exp<Sym>) -> Exp<Sym> {
    Exp::Not(Box::new(exp))
}

fn values(solver: &Solver<'_, B64>, symbol: Sym, expected: &[u64]) {
    let FiniteDomain::Known(values) = solver.finite_domain(symbol) else {
        panic!("应得到已确认的有限域");
    };
    assert_eq!(values, expected.iter().map(|value| bits64(*value, 8)).collect::<Vec<_>>());
}

#[test]
fn finite_domain_prefix_shares_fork_candidates_and_does_not_revisit_events() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let x = solver.declare_bitvector(8, SourceLoc::unknown());
    let allowed = Exp::Or(Box::new(equal(x, 1)), Box::new(equal(x, 2)));
    solver.assert(allowed);
    let point = checkpoint(&mut solver);
    let mut solver = Solver::<B64>::from_checkpoint(&context, point);
    let root = solver.start_transaction();
    for i in 0..257 {
        solver.define_bitvector(bits64(i, 16), SourceLoc::unknown());
    }
    let positive = equal(x, 1);
    let negative = not(positive.clone());
    PREFIX_EVENT_VISITS.set(0);
    BOUND_SEARCHES.set(0);
    assert_eq!(solver.finite_domain_bool(&positive), None);
    assert_eq!(solver.finite_domain_bool(&negative), None);
    assert_eq!((PREFIX_EVENT_VISITS.get(), BOUND_SEARCHES.get()), (0, 1));

    let first = solver.start_transaction_with_guard(Some(positive.clone()));
    assert_eq!(solver.finite_domain_bool(&positive), Some(true));
    assert_eq!(solver.finite_domain_bool(&negative), Some(false));
    solver.rollback_transaction(first);
    let second = solver.start_transaction_with_guard(Some(negative.clone()));
    assert_eq!(solver.finite_domain_bool(&positive), Some(false));
    assert_eq!(solver.finite_domain_bool(&negative), Some(true));
    solver.rollback_transaction(second);
    assert_eq!(solver.finite_domain_bool(&positive), None);
    solver.rollback_transaction(root);
}

#[test]
fn finite_domain_prefix_tracks_guarded_commit_rebinding_and_rollback() {
    configure_tastic(Tactic::Qfaufbv);
    let mut config = Config::new();
    config.solver_options.finite_domain_enumeration = true;
    let context = Context::new(config);
    let mut solver = Solver::<B64>::new(&context);
    let x = solver.declare_bitvector(8, SourceLoc::unknown());
    let g = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let allowed = Exp::Or(Box::new(equal(x, 1)), Box::new(equal(x, 2)));
    solver.assert(allowed);
    values(&solver, x, &[1, 2]);

    let root = solver.start_transaction();
    solver.start_transaction_with_guard(Some(Exp::Var(g)));
    solver.assert(equal(x, 2));
    values(&solver, x, &[2]);
    solver.commit_transaction();
    values(&solver, x, &[1, 2]);

    solver.start_transaction();
    solver.add(Def::DefineConst(x, bits64(3, 8)));
    assert!(matches!(solver.finite_domain(x), FiniteDomain::Unknown));
    assert_eq!(solver.finite_domain_bool(&equal(x, 3)), None);
    solver.commit_transaction();
    assert!(matches!(solver.finite_domain(x), FiniteDomain::Unknown));
    solver.rollback_transaction(root);
    values(&solver, x, &[1, 2]);

    solver.start_transaction();
    solver.with_transaction_condition(&Exp::Var(g), |solver| {
        solver.assert(equal(x, 2));
        assert_eq!(solver.finite_domain_bool(&equal(x, 1)), Some(false));
    });
    solver.commit_transaction();
    values(&solver, x, &[1, 2]);
    let point = checkpoint(&mut solver);
    let mut replayed = Solver::<B64>::from_checkpoint(&context, point);
    values(&replayed, x, &[1, 2]);
    let guarded = replayed.start_transaction_with_guard(Some(equal(x, 1)));
    assert_eq!(replayed.finite_domain_bool(&equal(x, 2)), Some(false));
    replayed.rollback_transaction(guarded);
}

#[test]
fn finite_domain_prefix_follows_trace_compaction_and_group_selection() {
    configure_tastic(Tactic::Qfaufbv);
    let mut config = Config::new();
    config.solver_options.finite_domain_enumeration = true;
    let context = Context::new(config);
    let mut solver = Solver::<B64>::new(&context);
    let x = solver.declare_bitvector(8, SourceLoc::unknown());
    solver.start_transaction();
    let discarded = solver.new_logical_arm(None);
    let left = solver.new_logical_arm(None);
    let right = solver.new_logical_arm(None);
    solver.with_logical_arm(discarded, |solver| solver.cycle_count());
    let alias = solver.with_logical_arm(left, |solver| {
        solver.assert(equal(x, 5));
        solver.define_bitvector(Exp::Var(x), SourceLoc::unknown())
    });
    values(&solver, alias, &[5]);
    solver.discard_logical_arm_effects(discarded);
    values(&solver, alias, &[5]);

    for group in solver.commit_region_groups(&[left, right]) {
        solver.select_region_group(group);
        values(&solver, alias, &[5]);
        let replayed = Solver::<B64>::from_checkpoint(&context, solver.region_group_checkpoint());
        values(&replayed, alias, &[5]);
    }
}

// 冻结的旧投影逐项计算每个候选，作为语义与调用次数的对照。
impl<B: BV> Solver<'_, B> {
    fn reference_projection(
        &self,
        prefix: &PathConditions<'_, B>,
        target: Sym,
        source: Sym,
        candidates: Vec<Exp<Sym>>,
    ) -> FiniteDomain {
        // 对派生锚点代入时保留原等式，防止把它错误地当成独立自由变量。
        let source_var = Exp::Var(source);
        let free = matches!(resolve(&source_var, prefix), Exp::Var(_));
        let anchor = self.translate_exp(&source_var);
        let target_ast = self.translate_exp(&Exp::Var(target));
        let assertions: Vec<_> = prefix.assertions().map(|exp| self.translate_exp(exp)).collect();
        let mut bool_atoms = Vec::new();
        let mut bool_literals = HashMap::new();
        for sym in prefix.bool_symbols() {
            let atom = self.decls[&sym].ast();
            let negative = Ast::mk_not(&atom);
            bool_literals.insert(atom.z3_ast, (sym, true));
            bool_literals.insert(negative.z3_ast, (sym, false));
            bool_atoms.push(negative);
        }
        let mut admissible = Vec::new();
        let mut exact = true;
        'candidate: for candidate in candidates {
            let value = self.translate_exp(&candidate);
            let binding = (!free).then(|| Ast::mk_eq(&anchor, &value));
            let mut literals = HashMap::new();
            let mut satisfiable_by_literals = true;
            let mut can_reuse_witness = self.has_stashed_model();
            for (index, original) in assertions.iter().chain(&binding).enumerate() {
                let is_path_fact = index < assertions.len();
                let mut residual = if is_path_fact { original.substitute(&anchor, &value) } else { original.clone() };
                let unchanged = residual.z3_ast == original.z3_ast && is_path_fact;
                match residual.structural_bool() {
                    Some(false) => continue 'candidate,
                    Some(true) => (),
                    None => {
                        can_reuse_witness &= unchanged;
                        if let Some(&(literal, positive)) = bool_literals.get(&residual.z3_ast) {
                            if literals.insert(literal, positive).is_some_and(|previous| previous != positive) {
                                continue 'candidate;
                            }
                        } else {
                            satisfiable_by_literals = false;
                        }
                    }
                }
            }
            let value = match target_ast.substitute(&anchor, &value).finite_bits() {
                Some(value) => value,
                None if !free => {
                    let mut projected = HashMap::from([(source, Some(candidate))]);
                    let Some(value) = self.project_finite_definition(target, prefix, &mut projected) else {
                        return FiniteDomain::Unknown;
                    };
                    // 重试的排除式可能引用遭化简的目标。先在原表达式中代入，再判是否必假。
                    for assertion in prefix.assertions() {
                        let mut changed = false;
                        let substituted = assertion
                            .map_var(&mut |sym| {
                                Ok::<_, std::convert::Infallible>(match projected.get(sym) {
                                    Some(Some(value)) => {
                                        changed = true;
                                        value.clone()
                                    }
                                    _ => Exp::Var(*sym),
                                })
                            })
                            .unwrap();
                        if changed && self.translate_exp(&substituted).structural_bool() == Some(false) {
                            continue 'candidate;
                        }
                    }
                    value
                }
                None => return FiniteDomain::Unknown,
            };
            exact &= satisfiable_by_literals || can_reuse_witness;
            if !admissible.contains(&value) {
                admissible.push(value);
            }
        }
        if exact {
            FiniteDomain::Known(admissible)
        } else {
            FiniteDomain::Bounded(admissible)
        }
    }
}

fn projection_counts<T>(f: impl FnOnce() -> T) -> (T, usize, usize) {
    PROJECT_SUBSTITUTIONS.set(0);
    STRUCTURAL_BOOLS.set(0);
    (f(), PROJECT_SUBSTITUTIONS.get(), STRUCTURAL_BOOLS.get())
}

#[test]
fn projection_factors_independent_assertions() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    solver.assert(not(equal(x, 16)));
    for _ in 0..256 {
        let b = solver.declare_const(Ty::Bool, info);
        solver.assert(Exp::Var(b));
    }
    let prefix = PathConditions::new(&solver).unwrap();
    let candidates: Vec<_> = (0..16).map(|v| bits64(v, 8)).collect();
    let (expected, old_sub, old_bool) =
        projection_counts(|| solver.reference_projection(&prefix, x, x, candidates.clone()));
    let (actual, sub, boolean) = projection_counts(|| solver.project_finite_values(&prefix, x, x, candidates.clone()));
    assert_eq!(actual, FiniteDomain::Known(candidates));
    assert_eq!(actual, expected);
    assert_eq!((old_sub, old_bool), (16 * 258, 16 * 257));
    eprintln!("投影代入 {old_sub} → {sub}，结构判定 {old_bool} → {boolean}");
    assert!(sub <= 256 + 16 * 2 && boolean <= 256 + 16);
}

#[test]
fn projection_matches_reference_for_literals_bindings_and_witness() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    let y = solver.declare_bitvector(8, info);
    let b = solver.declare_const(Ty::Bool, info);
    let derived =
        solver.define_bitvector(Exp::Ite(Box::new(Exp::Var(b)), Box::new(bits64(0, 8)), Box::new(bits64(1, 8))), info);
    let folded = solver.define_bitvector(bits64(0, 8), info);
    let compare = |solver: &Solver<'_, B64>, source, expected| {
        let prefix = PathConditions::new(solver).unwrap();
        let candidates = vec![bits64(0, 8), bits64(1, 8)];
        let reference = solver.reference_projection(&prefix, source, source, candidates.clone());
        let result = solver.project_finite_values(&prefix, source, source, candidates);
        assert_eq!(result, reference);
        assert_eq!(result, expected);
    };
    let both = || vec![bits64(0, 8), bits64(1, 8)];
    solver.assert(Exp::Bool(true));
    solver.assert(Exp::Var(b));
    compare(&solver, x, FiniteDomain::Known(both()));
    compare(&solver, derived, FiniteDomain::Known(vec![bits64(0, 8)]));
    compare(&solver, folded, FiniteDomain::Known(vec![bits64(0, 8)]));
    let tx = solver.start_transaction();
    solver.assert(Exp::Or(Box::new(equal(x, 0)), Box::new(equal(y, 3))));
    assert!(matches!(solver.check_sat(info), Sat));
    // x=1 的非字面量残余式由代入产生，原路径见证不能认证它。
    compare(&solver, x, FiniteDomain::Bounded(both()));
    let prefix = PathConditions::new(&solver).unwrap();
    assert_eq!(solver.project_finite_values(&prefix, y, x, both()), FiniteDomain::Unknown);
    assert_eq!(solver.reference_projection(&prefix, y, x, both()), FiniteDomain::Unknown);
    solver.rollback_transaction(tx);
    // 代入 x=0 后只剩 ¬b，与公共字面量 b 矛盾。
    solver.assert(Exp::Or(Box::new(equal(x, 1)), Box::new(not(Exp::Var(b)))));
    compare(&solver, x, FiniteDomain::Known(vec![bits64(1, 8)]));
    solver.assert(equal(y, 3));
    compare(&solver, x, FiniteDomain::Bounded(vec![bits64(1, 8)]));
    assert!(matches!(solver.check_sat(info), Sat));
    assert!(solver.has_stashed_model());
    compare(&solver, x, FiniteDomain::Known(vec![bits64(1, 8)]));
    solver.assert(not(Exp::Var(b)));
    compare(&solver, x, FiniteDomain::Known(vec![]));
    solver.assert(Exp::Bool(false));
    compare(&solver, x, FiniteDomain::Known(vec![]));
}

#[test]
fn projection_reuses_ast_work_across_prefix_growth_and_anchors() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    let y = solver.declare_bitvector(8, info);
    for sym in [x, y] {
        solver.assert(Exp::Or(Box::new(equal(sym, 0)), Box::new(equal(sym, 1))));
    }
    for _ in 0..256 {
        let b = solver.declare_const(Ty::Bool, info);
        solver.assert(Exp::Var(b));
    }
    let count = |solver: &Solver<'_, B64>, sym| {
        PROJECT_TRANSLATIONS.set(0);
        let (result, sub, boolean) = projection_counts(|| solver.finite_domain(sym));
        assert_eq!(result, FiniteDomain::Bounded(vec![bits64(0, 8), bits64(1, 8)]));
        (PROJECT_TRANSLATIONS.get(), sub, boolean)
    };
    let cold = count(&solver, x);
    let warm = count(&solver, x);
    eprintln!("同一锚点首次／再次（翻译、代入、结构判定） {cold:?}／{warm:?}");
    assert_eq!(cold, (258, 261, 259));
    assert_eq!(warm, (0, 4, 2));
    assert_eq!(count(&solver, y), (0, 261, 3));
    let b = solver.declare_const(Ty::Bool, info);
    solver.assert(not(Exp::Var(b)));
    assert_eq!(count(&solver, x), (1, 5, 3));
    assert_eq!(count(&solver, y), (0, 5, 2));
}

#[test]
fn projection_cache_tracks_rollback_rewritten_guard_and_new_context() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    let b = solver.declare_const(Ty::Bool, info);
    solver.assert(Exp::Or(Box::new(equal(x, 0)), Box::new(equal(x, 1))));
    let root = solver.start_transaction();
    let inner = solver.start_transaction();
    solver.assert(equal(x, 0));
    values(&solver, x, &[0]);
    solver.rollback_transaction(inner);
    solver.start_transaction_with_guard(Some(Exp::Var(b)));
    solver.assert(equal(x, 1));
    values(&solver, x, &[1]);
    solver.commit_transaction();
    values(&solver, x, &[0, 1]);
    solver.with_transaction_condition(&Exp::Var(b), |solver| values(solver, x, &[1]));
    values(&solver, x, &[0, 1]);
    solver.rollback_transaction(root);
    values(&solver, x, &[0, 1]);
    let point = checkpoint(&mut solver);
    let other = Context::new(Config::new());
    let mut replay = Solver::from_checkpoint(&other, point);
    PROJECT_TRANSLATIONS.set(0);
    values(&replay, x, &[0, 1]);
    assert_eq!(PROJECT_TRANSLATIONS.get(), 1);
    replay.assert(equal(x, 1));
    values(&replay, x, &[1]);
    values(&solver, x, &[0, 1]);
}
