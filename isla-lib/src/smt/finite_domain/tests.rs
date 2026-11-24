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

    for group in solver.commit_region_groups(&[left, right]).unwrap() {
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

#[test]
fn projection_handles_5000_definitions_on_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            configure_tastic(Tactic::Qfaufbv);
            let context = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&context);
            let info = SourceLoc::unknown();
            let anchor = solver.declare_bitvector(16, info);
            let mut tail = anchor;
            for _ in 0..5000 {
                tail = solver.define_bitvector(Exp::Bvadd(Box::new(Exp::Var(tail)), Box::new(bits64(1, 16))), info);
            }
            let prefix = PathConditions::new(&solver).unwrap();
            let mut projected = HashMap::from([(anchor, Some(bits64(42, 16)))]);

            assert_eq!(solver.project_finite_definition(tail, &prefix, &mut projected), Some(bits64(5042, 16)));
            assert_eq!(projected.len(), 5001);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn projection_matches_recursive_definition_walk_on_a_diamond() {
    fn recursive(
        solver: &Solver<'_, B64>,
        sym: Sym,
        prefix: &PathConditions<'_, B64>,
        projected: &mut HashMap<Sym, Option<Exp<Sym>>>,
    ) -> Option<Exp<Sym>> {
        if let Some(value) = projected.get(&sym) {
            return value.clone();
        }
        let value = prefix.definition(sym).and_then(|definition| {
            let mut changed = false;
            let expression = definition
                .map_var(&mut |input| {
                    Ok::<_, std::convert::Infallible>(match recursive(solver, *input, prefix, projected) {
                        Some(value) => {
                            changed = true;
                            value
                        }
                        None => Exp::Var(*input),
                    })
                })
                .unwrap();
            if !changed {
                return None;
            }
            let mut ast = solver.translate_exp(&expression);
            ast.finite_bits().or_else(|| ast.structural_bool().map(Exp::Bool))
        });
        projected.insert(sym, value.clone());
        value
    }

    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let info = SourceLoc::unknown();
    let anchor = solver.declare_bitvector(8, info);
    let unknown = solver.declare_bitvector(8, info);
    let shared = solver.define_bitvector(Exp::Bvadd(Box::new(Exp::Var(anchor)), Box::new(bits64(1, 8))), info);
    let left = solver.define_bitvector(Exp::Bvadd(Box::new(Exp::Var(shared)), Box::new(Exp::Var(shared))), info);
    let right = solver.define_bitvector(Exp::Bvadd(Box::new(Exp::Var(shared)), Box::new(Exp::Var(unknown))), info);
    let guard = solver.define_const(equal(left, 12), info);
    let target = solver.define_bitvector(
        Exp::Ite(Box::new(Exp::Var(guard)), Box::new(Exp::Var(left)), Box::new(Exp::Var(right))),
        info,
    );
    let prefix = PathConditions::new(&solver).unwrap();
    let mut actual = HashMap::from([(anchor, Some(bits64(5, 8)))]);
    let mut expected = actual.clone();

    PROJECT_TRANSLATIONS.set(0);
    let (reference, reference_subs, reference_bools) =
        projection_counts(|| recursive(&solver, target, &prefix, &mut expected));
    let reference_translations = PROJECT_TRANSLATIONS.get();
    PROJECT_TRANSLATIONS.set(0);
    let (result, subs, bools) = projection_counts(|| solver.project_finite_definition(target, &prefix, &mut actual));

    assert_eq!(result, Some(bits64(12, 8)));
    assert_eq!(result, reference);
    assert_eq!(actual, expected);
    assert_eq!(actual.get(&guard), Some(&Some(Exp::Bool(true))));
    assert_eq!(actual.get(&right), Some(&None));
    assert_eq!(actual.get(&unknown), Some(&None));
    assert_eq!((PROJECT_TRANSLATIONS.get(), subs), (reference_translations, reference_subs));
    assert_eq!(bools + 1, reference_bools);
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
    assert_eq!(cold, (258, 2, 257));
    assert_eq!(warm, (0, 0, 0));
    assert_eq!(count(&solver, y), (0, 2, 1));
    let b = solver.declare_const(Ty::Bool, info);
    solver.assert(not(Exp::Var(b)));
    assert_eq!(count(&solver, x), (1, 2, 1));
    assert_eq!(count(&solver, y), (0, 2, 0));
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

#[test]
fn projection_related_candidates_share_a_dag_and_reuse_results() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    let alias = solver.define_bitvector(Exp::Bvadd(Box::new(Exp::Var(x)), Box::new(bits64(1, 8))), info);
    let b = solver.declare_const(Ty::Bool, info);
    let shared = Exp::Ite(Box::new(equal(x, 1)), Box::new(Exp::Var(b)), Box::new(Exp::Bool(true)));
    for i in 16..48 {
        solver.assert(Exp::Or(Box::new(shared.clone()), Box::new(equal(x, i))));
    }
    let candidates: Vec<_> = (0..16).map(|v| bits64(v, 8)).collect();
    let check = |solver: &Solver<'_, B64>, target| {
        let prefix = PathConditions::new(solver).unwrap();
        let expected = solver.reference_projection(&prefix, target, x, candidates.clone());
        let (actual, sub, boolean) =
            projection_counts(|| solver.project_finite_values(&prefix, target, x, candidates.clone()));
        assert_eq!(expected, actual);
        (sub, boolean)
    };
    let cold = check(&solver, x);
    let warm = check(&solver, alias);
    let tx = solver.start_transaction();
    solver.assert(not(Exp::Var(b)));
    let appended = check(&solver, alias);
    solver.rollback_transaction(tx);
    let restored = check(&solver, alias);
    eprintln!("相关断言（全量代入、结构判定），首次 {cold:?}，换目标 {warm:?}，追加 {appended:?}，回滚 {restored:?}");
    assert!(cold.0 <= 16 && restored.0 <= 16);
    assert!(cold.1 <= 32 && restored.1 <= 32);
    assert_eq!(warm, (16, 0));
    assert!(appended.0 <= 16 && appended.1 <= 1);
}

#[test]
fn projection_reuses_nonliteral_without_keeping_its_residual() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    let y = solver.declare_bitvector(8, info);
    solver.assert(Exp::Or(Box::new(equal(x, 0)), Box::new(equal(y, 4))));
    for with_witness in [false, true] {
        if with_witness {
            assert!(matches!(solver.check_sat(info), Sat));
        }
        let prefix = PathConditions::new(&solver).unwrap();
        for value in 0..4 {
            let candidates = vec![bits64(value, 8)];
            let expected = solver.reference_projection(&prefix, x, x, candidates.clone());
            for warm in [false, true] {
                let (actual, _, boolean) =
                    projection_counts(|| solver.project_finite_values(&prefix, x, x, candidates.clone()));
                assert_eq!(actual, expected);
                if warm {
                    assert_eq!(boolean, 0, "同一候选重复投影，value={value}");
                }
            }
        }
    }
}

#[test]
fn slice_queries_reuse_candidate_facts_across_sibling_guards() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    let g = solver.declare_const(Ty::Bool, info);
    let other = solver.declare_bitvector(8, info);
    for n in 0..128 {
        solver.assert(Exp::Or(Box::new(equal(x, n)), Box::new(equal(other, n))));
    }
    let candidates: Vec<_> = (0..4).map(|v| bits64(v, 8)).collect();
    let mut counts = Vec::new();
    for guard in [Exp::Var(g), not(Exp::Var(g)), equal(x, 2)] {
        let tx = solver.start_transaction_with_guard(Some(guard));
        let prefix = PathConditions::new(&solver).unwrap();
        let expected = solver.reference_projection(&prefix, x, x, candidates.clone());
        AST_SIMPLIFY_CALLS.set(0);
        let (actual, sub, _) = projection_counts(|| solver.project_finite_values(&prefix, x, x, candidates.clone()));
        counts.push((sub, AST_SIMPLIFY_CALLS.get()));
        assert_eq!(actual, expected);
        solver.rollback_transaction(tx);
    }
    eprintln!("相邻活动臂的全量代入／化简 {counts:?}");
    assert!(counts[1].1 < 16);
}

#[test]
fn slice_queries_bound_shared_boolean_dag_once() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    let mut both = solver.define_const(Exp::Or(Box::new(equal(x, 3)), Box::new(equal(x, 1))), info);
    for _ in 0..10 {
        both = solver.define_const(Exp::And(Box::new(Exp::Var(both)), Box::new(Exp::Var(both))), info);
    }
    solver.assert(Exp::Var(both));
    let prefix = PathConditions::new(&solver).unwrap();
    let expected = vec![bits64(3, 8), bits64(1, 8)];
    BOUND_NODE_VISITS.set(0);
    assert_eq!(prefix.bounds(&Exp::Var(x)), Some(expected));
    let visits = BOUND_NODE_VISITS.get();
    eprintln!("共享子式上界访问 {visits}");
    assert!(visits <= 16);
}

#[test]
fn slice_queries_reuse_exact_prefix_and_refresh_on_assertion() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    solver.assert(Exp::Or(Box::new(equal(x, 2)), Box::new(equal(x, 1))));
    values(&solver, x, &[2, 1]);
    let (_, sub, _) = projection_counts(|| values(&solver, x, &[2, 1]));
    let tx = solver.start_transaction();
    solver.assert(equal(x, 1));
    values(&solver, x, &[1]);
    solver.rollback_transaction(tx);
    values(&solver, x, &[2, 1]);
    assert_eq!(sub, 0);
}

#[test]
fn slice_queries_joint_combinations_reuse_native_rewrites() {
    configure_tastic(Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    let y = solver.declare_bitvector(8, info);
    let g = solver.declare_const(Ty::Bool, info);
    for s in [x, y] {
        solver.assert(Exp::Or(Box::new(equal(s, 2)), Box::new(equal(s, 1))));
    }
    for _ in 0..100 {
        let b = solver.declare_const(Ty::Bool, info);
        solver.assert(Exp::Var(b));
    }
    let sum = Exp::Bvadd(Box::new(Exp::Var(x)), Box::new(Exp::Var(y)));
    let mut counts = Vec::new();
    for guard in [Exp::Var(g), not(Exp::Var(g)), equal(x, 1)] {
        let tx = solver.start_transaction_with_guard(Some(guard));
        let prefix = PathConditions::new(&solver).unwrap();
        let collect = |v: &mut Vec<_>, mut a: Ast, certified| {
            v.push((a.finite_bits().unwrap(), certified));
            true
        };
        let mut expected = Vec::new();
        solver.reference_combined_values(&prefix, &sum, |a, b| collect(&mut expected, a, b)).unwrap();
        let mut actual = Vec::new();
        AST_SIMPLIFY_CALLS.set(0);
        let (_, sub, _) =
            projection_counts(|| solver.combined_values(&prefix, &sum, |a, b| collect(&mut actual, a, b)).unwrap());
        counts.push((sub, AST_SIMPLIFY_CALLS.get()));
        assert_eq!(actual, expected);
        solver.rollback_transaction(tx);
    }
    eprintln!("联合切片相邻臂的全量代入／化简 {counts:?}");
    // 第一次联合查询也应只代入引用当前锚点的断言：两条上界各有两种局部赋值。
    assert!(counts[0].0 <= 4, "无关断言不应随四组输入被重复代入");
    assert!(counts[1].0 <= 12 && counts[1].1 <= 32);
}

#[test]
fn slice_queries_append_bounds_in_latest_assertion_order() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    for _ in 0..128 {
        let b = solver.declare_const(Ty::Bool, info);
        solver.assert(Exp::Var(b));
    }
    let or = |i, j| Exp::Or(Box::new(equal(x, i)), Box::new(equal(x, j)));
    solver.assert(or(1, 2));
    let bounds = |s: &Solver<B64>| PathConditions::new(s).unwrap().bounds(&Exp::Var(x)).unwrap();
    assert_eq!(bounds(&solver), [bits64(1, 8), bits64(2, 8)]);
    solver.assert(or(2, 1));
    BOUND_NODE_VISITS.set(0);
    assert_eq!(bounds(&solver), [bits64(2, 8), bits64(1, 8)]);
    let visits = BOUND_NODE_VISITS.get();
    eprintln!("追加约束后的上界访问 {visits}");
    assert!(visits <= 3);
}

#[test]
fn slice_queries_bound_guarded_disjunction_short_circuits() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    let g = solver.declare_const(Ty::Bool, info);
    let mut body = equal(x, 1);
    for i in 2..60 {
        body = Exp::Or(Box::new(body), Box::new(equal(x, i)));
    }
    let prefix = PathConditions::new(&solver).unwrap();
    let target = Exp::Var(x);
    let or = Exp::Or(Box::new(not(Exp::Var(g))), Box::new(body.clone()));
    let and = Exp::And(Box::new(Exp::Bool(false)), Box::new(body.clone()));
    let ite = Exp::Ite(Box::new(Exp::Var(g)), Box::new(Exp::Var(g)), Box::new(body));
    for (exp, negated) in [(or.clone(), false), (not(or), true), (and, false), (ite, false)] {
        let expected = reference_bound(&exp, &target, &prefix, negated);
        BOUND_NODE_VISITS.set(0);
        assert_eq!(bound(&exp, &target, &prefix, negated, &mut HashMap::new()), expected);
        let visits = BOUND_NODE_VISITS.get();
        eprintln!("守卫子树访问 {visits}");
        assert!(visits <= 5);
    }
}

#[test]
fn slice_queries_bound_retains_only_stable_assertions_across_guards() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    for _ in 0..100 {
        let b = solver.declare_const(Ty::Bool, info);
        solver.assert(Exp::Var(b));
    }
    solver.assert(Exp::Or(Box::new(equal(x, 1)), Box::new(equal(x, 2))));
    let bounds = |s: &Solver<B64>| {
        let prefix = PathConditions::new(s).unwrap();
        let target = Exp::Var(x);
        let expected =
            prefix.assertions().fold(None, |acc, e| intersect(acc, reference_bound(e, &target, &prefix, false)));
        BOUND_NODE_VISITS.set(0);
        let actual = prefix.bounds(&target);
        assert_eq!(actual, expected);
        BOUND_NODE_VISITS.get()
    };
    bounds(&solver);
    let tx = solver.start_transaction_with_guard(Some(equal(x, 2)));
    let visits = bounds(&solver);
    eprintln!("只换守卫后的上界访问 {visits}");
    solver.assert(equal(x, 1));
    bounds(&solver);
    solver.rollback_transaction(tx);
    bounds(&solver);
    let tx = solver.start_transaction_with_guard(Some(equal(x, 1)));
    bounds(&solver);
    solver.rollback_transaction(tx);
    assert!(visits <= 2);
}

fn reference_bound<B: BV>(exp: &Exp<Sym>, target: &Exp<Sym>, prefix: &PathConditions<'_, B>, negated: bool) -> Bound {
    use Exp::*;
    let visit = |child, negated| reference_bound(child, target, prefix, negated);
    let exp = resolve(exp, prefix);
    match exp {
        Eq(lhs, rhs) | Neq(lhs, rhs) if matches!(exp, Eq(..)) != negated => {
            let (lhs, rhs) = (resolve(lhs, prefix), resolve(rhs, prefix));
            let value = if lhs == target {
                constant(rhs)
            } else if rhs == target {
                constant(lhs)
            } else {
                masked_slice(target, lhs, rhs, prefix).or_else(|| masked_slice(target, rhs, lhs, prefix))
            };
            value.map(|value| vec![value])
        }
        Not(inner) => visit(inner, !negated),
        And(lhs, rhs) | Or(lhs, rhs) => {
            let combine = if matches!(exp, And(..)) != negated { intersect } else { union };
            combine(visit(lhs, negated), visit(rhs, negated))
        }
        Ite(condition, yes, no) => union(
            intersect(visit(condition, false), visit(yes, negated)),
            intersect(visit(condition, true), visit(no, negated)),
        ),
        Bool(value) if *value == negated => Some(Vec::new()),
        _ => None,
    }
}

#[test]
fn slice_queries_mixed_single_and_joint_keep_the_previous_joint_results() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    let y = solver.declare_bitvector(8, info);
    let g = solver.declare_const(Ty::Bool, info);
    for s in [x, y] {
        solver.assert(Exp::Or(Box::new(equal(s, 1)), Box::new(equal(s, 2))));
    }
    for _ in 0..150 {
        let b = solver.declare_const(Ty::Bool, info);
        solver.assert(Exp::Var(b));
    }
    let sum = Exp::Bvadd(Box::new(Exp::Var(x)), Box::new(Exp::Var(y)));
    let mut counts = Vec::new();
    for joint in [true, false, false, true] {
        let tx = solver.start_transaction_with_guard(Some(Exp::Var(g)));
        let prefix = PathConditions::new(&solver).unwrap();
        if joint {
            let collect = |v: &mut Vec<_>, mut a: Ast, certified| {
                v.push((a.finite_bits().unwrap(), certified));
                true
            };
            let mut expected = Vec::new();
            solver.reference_combined_values(&prefix, &sum, |a, b| collect(&mut expected, a, b)).unwrap();
            AST_SIMPLIFY_CALLS.set(0);
            let mut actual = Vec::new();
            let (_, sub, _) =
                projection_counts(|| solver.combined_values(&prefix, &sum, |a, b| collect(&mut actual, a, b)).unwrap());
            counts.push((sub, AST_SIMPLIFY_CALLS.get()));
            assert_eq!(actual, expected);
        } else {
            let candidates = vec![bits64(1, 8), bits64(2, 8)];
            let expected = solver.reference_projection(&prefix, x, x, candidates.clone());
            AST_SIMPLIFY_CALLS.set(0);
            let (actual, sub, _) = projection_counts(|| solver.project_finite_values(&prefix, x, x, candidates));
            assert_eq!(actual, expected);
            counts.push((sub, AST_SIMPLIFY_CALLS.get()));
        }
        solver.rollback_transaction(tx);
    }
    eprintln!("交替查询各轮的全量代入／化简 {counts:?}");
    assert!(counts[2].1 < 10 && counts[3].0 < 10 && counts[3].1 < 20);
}

#[test]
fn finite_domain_operand_bound_is_local_to_the_retry_arm() {
    if !resolver_test_options(
        "finite_domain_operand_bound_is_local_to_the_retry_arm",
        crate::config::RegionOptions { symbolic_scalar_resolver: false, ..Default::default() },
    ) {
        return;
    }
    configure_tastic(Tactic::Qfaufbv);
    let mut config = Config::new();
    config.solver_options.finite_domain_enumeration = true;
    let context = Context::new(config);
    let mut solver = Solver::<B64>::new(&context);
    let site = SourceLoc::new(2, 1, 0, 1, 8);
    let x = solver.declare_bitvector(8, site);
    let y = solver.declare_bitvector(8, site);
    solver.assert(Exp::Or(Box::new(equal(x, 1)), Box::new(Exp::Or(Box::new(equal(x, 2)), Box::new(equal(x, 3))))));
    solver.with_deferred_region_queries(|solver| {
        let root = solver.start_transaction();
        let arm = solver.start_transaction_with_guard(Some(equal(x, 3)));
        let singleton = vec![bits64(3, 8)];
        solver.set_operand_bound(x, site, singleton.clone());
        assert_eq!(solver.operand_bound(y, site), None);
        assert_eq!(solver.operand_bound(x, SourceLoc::unknown()), None);
        assert_eq!(solver.operand_bound(x, site), Some(FiniteDomain::Bounded(singleton)));
        solver.add(Def::DefineConst(x, bits64(4, 8)));
        assert_eq!(solver.operand_bound(x, site), None);
        solver.rollback_transaction(arm);
        solver.start_transaction_with_guard(Some(not(equal(x, 3))));
        assert_eq!(solver.operand_bound(x, site), None);
        solver.set_operand_bound(x, site, (1..3).map(|v| bits64(v, 8)).collect());
        solver.commit_transaction();
        assert_eq!(solver.operand_bound(x, site), None);
        solver.rollback_transaction(root);
    });
}

#[test]
fn zero_extend_width_under_mask_choices_matches_eager_solver() {
    use Exp::*;
    configure_tastic(Tactic::Qfaufbv);
    let mut config = Config::new();
    config.solver_options.finite_domain_enumeration = true;
    let context = Context::new(config);
    let mut solver = Solver::<B64>::new(&context);
    let loc = SourceLoc::unknown();
    let short = solver.declare_const(Ty::Bool, loc);
    let medium = solver.declare_const(Ty::Bool, loc);
    let deep = solver.declare_const(Ty::Bool, loc);
    let width = solver.define_const(
        Ite(
            Box::new(Var(short)),
            Box::new(bits64(27, 8)),
            Box::new(Ite(Box::new(Var(medium)), Box::new(bits64(36, 8)), Box::new(bits64(45, 8)))),
        ),
        loc,
    );
    // 同一模式决定扩展宽度和初始掩码。掩码还受另一选择条件控制。
    let base = solver.define_const(Bvsub(Box::new(Var(width)), Box::new(bits64(9, 8))), loc);
    let mask = solver.define_const(
        Ite(Box::new(Var(deep)), Box::new(Bvsub(Box::new(Var(base)), Box::new(bits64(9, 8)))), Box::new(Var(base))),
        loc,
    );
    let all: Vec<_> = [27, 36, 45].into_iter().map(|n| bits64(n, 8)).collect();
    let unknown_mask = solver.declare_bitvector(8, loc);
    let consumed = [9, 18, 27].map(|n| solver.define_const(equal(mask, n), loc));
    let chosen = Or(Box::new(Var(consumed[0])), Box::new(Or(Box::new(Var(consumed[1])), Box::new(Var(consumed[2])))));
    for guard in [Some(not(chosen)), Some(equal(mask, 27)), Some(equal(unknown_mask, 36)), None] {
        let arm = solver.start_transaction_with_guard(guard.clone());
        let mut actual = all.clone();
        let checks = crate::smt::test_query_count();
        solver.refine_guarded_values(width, &mut actual, |_| false, true);
        assert_eq!(crate::smt::test_query_count(), checks);
        let expected: Vec<_> = all
            .iter()
            .filter(|v| solver.check_sat_with(&Eq(Box::new(Var(width)), Box::new((*v).clone())), loc).is_sat().unwrap())
            .cloned()
            .collect();
        assert_eq!(actual, expected, "掩码选择守卫 {guard:?}");
        solver.rollback_transaction(arm);
    }
}

#[test]
fn joint_rejects_inconsistent_derived_guards_before_rewriting_path() {
    use Exp::*;
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_bitvector(8, info);
    s.assert(Or(Box::new(equal(x, 1)), Box::new(equal(x, 2))));
    let odd =
        s.define_const(Eq(Box::new(Bvand(Box::new(Var(x)), Box::new(bits64(1, 8)))), Box::new(bits64(1, 8))), info);
    let chosen = Ite(Box::new(Var(odd)), Box::new(bits64(1, 8)), Box::new(bits64(2, 8)));
    for _ in 0..16 {
        let flag = s.declare_const(Ty::Bool, info);
        s.assert(Or(Box::new(Var(flag)), Box::new(Eq(Box::new(Var(x)), Box::new(chosen.clone())))));
    }
    let sum = Bvadd(Box::new(Var(x)), Box::new(chosen));
    let prefix = PathConditions::new(&s).unwrap();
    let mut old = Vec::new();
    let mut new = Vec::new();
    s.reference_combined_values(&prefix, &sum, |mut value, cert| {
        old.push((value.finite_bits().unwrap(), cert));
        true
    })
    .unwrap();
    let (_, subs, _) = projection_counts(|| {
        s.combined_values(&prefix, &sum, |mut value, cert| {
            new.push((value.finite_bits().unwrap(), cert));
            true
        })
        .unwrap()
    });
    eprintln!("派生守卫四组赋值的代入次数 {subs}");
    assert_eq!(new, old);
    assert_eq!(new.len(), 2);
    assert!(subs <= 40, "先用自由输入验证绑定，只让一致的两组触碰普通断言");
}

#[test]
fn joint_nested_anchors_match_reference_across_partial_assignments() {
    use Exp::*;
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let inner = s.declare_const(Ty::Bool, info);
    let fun = s.fresh();
    s.add(Def::DeclareFun(fun, vec![Ty::Bool], Ty::Bool));
    let outer = App(fun, vec![Var(inner)]);
    s.assert(outer.clone());
    s.assert(not(App(fun, vec![Bool(false)])));
    let choose = |g, a, b| Ite(Box::new(g), Box::new(a), Box::new(b));
    // 内层锚点既在外层锚点里面，也能在外层未赋值时单独被选择。
    let branch = s.declare_const(Ty::Bool, info);
    let mut size =
        choose(Var(branch), choose(outer, bits64(1, 8), bits64(5, 8)), choose(Var(inner), bits64(2, 8), bits64(3, 8)));

    // 独立守卫的数量超过摘要位数，碰撞只能增加工作，不能漏掉代入。
    for _ in 0..129 {
        let guard = s.declare_const(Ty::Bool, info);
        size = choose(Var(guard), bits64(4, 8), size);
    }
    let prefix = PathConditions::new(&s).unwrap();
    let collect = |out: &mut Vec<_>, mut value: Ast, certified| {
        out.push((value.finite_bits().unwrap(), certified));
        true
    };
    let mut old = Vec::new();
    s.reference_combined_values(&prefix, &size, |v, c| collect(&mut old, v, c)).unwrap();
    assert!(old.iter().any(|(v, _)| *v == bits64(2, 8)));
    assert!(!old.iter().any(|(v, _)| *v == bits64(3, 8)));

    let mut new = Vec::new();
    s.combined_values(&prefix, &size, |v, c| collect(&mut new, v, c)).unwrap();
    assert_eq!(new, old);
}

fn resolver_test(name: &str) -> bool {
    resolver_test_options(name, crate::config::RegionOptions { symbolic_scalar_resolver: true, ..Default::default() })
}

fn resolver_test_options(name: &str, options: crate::config::RegionOptions) -> bool {
    let full = format!("smt::finite_domain::tests::{name}");
    if !std::env::args().any(|arg| arg == "--exact") || !std::env::args().any(|arg| arg == full) {
        let result = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", &full, "--nocapture"])
            .output()
            .unwrap();
        assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
        return false;
    }
    options.configure();
    true
}

fn guarded_width(solver: &mut Solver<B64>, ty_width: u32, yes: u64, no: u64) -> (Sym, Sym) {
    let site = SourceLoc::unknown();
    let level = solver.declare_const(Ty::Bool, site);
    let input = solver.define_const(
        Exp::Ite(Box::new(Exp::Var(level)), Box::new(bits64(yes, ty_width)), Box::new(bits64(no, ty_width))),
        site,
    );
    let width = solver.define_const(Exp::Bvmul(Box::new(Exp::Var(input)), Box::new(bits64(3, ty_width))), site);
    (level, width)
}

#[test]
fn scalar_resolver_arm_scope() {
    if !resolver_test("scalar_resolver_arm_scope") {
        return;
    }
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let loc = SourceLoc::unknown();
    let next = SourceLoc::new(2, 8, 0, 8, 1);
    let (level, width) = guarded_width(&mut solver, 8, 3, 253);
    let nested = solver.declare_const(Ty::Bool, loc);
    solver.with_deferred_region_queries(|s| {
        let parent = s.start_transaction();
        let valid = s.start_transaction_with_guard(Some(Exp::Var(level)));
        s.set_operand_bound(width, loc, vec![bits64(9, 8)]);
        let inner = s.start_transaction_with_guard(Some(Exp::Var(nested)));
        assert_eq!(s.operand_bound(width, next), Some(FiniteDomain::Bounded(vec![bits64(9, 8)])));
        s.rollback_transaction(inner);
        s.rollback_transaction(valid);
        assert!(s.operand_bound(width, next).is_none());
        s.start_transaction_with_guard(Some(not(Exp::Var(level))));
        s.commit_dead_transaction();
        assert!(s.check_candidate_sat_with(&equal(width, 247), loc).is_some_and(|r| r != SmtResult::Sat));
        s.rollback_transaction(parent);
    });
    assert!(solver.check_sat_with(&equal(width, 247), loc).is_sat().unwrap());
}

#[test]
fn scalar_resolver_keeps_translated_assertions_on_guard_switch() {
    if !resolver_test("scalar_resolver_keeps_translated_assertions_on_guard_switch") {
        return;
    }
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let loc = SourceLoc::unknown();
    let x = s.declare_bitvector(8, loc);
    let flag = s.declare_const(Ty::Bool, loc);
    s.assert(Exp::Or(Box::new(equal(x, 1)), Box::new(equal(x, 2))));
    values(&s, x, &[1, 2]);
    let parent = s.start_transaction();
    for g in [Exp::Var(flag), not(Exp::Var(flag))] {
        let child = s.start_transaction_with_guard(Some(g));
        PROJECT_TRANSLATIONS.set(0);
        values(&s, x, &[1, 2]);
        assert_eq!(PROJECT_TRANSLATIONS.get(), 1, "子臂只翻译新守卫");
        s.rollback_transaction(child);
    }
    s.rollback_transaction(parent);
}

#[test]
fn scalar_resolver_consumers_share_guarded_length() {
    if !resolver_test("scalar_resolver_consumers_share_guarded_length") {
        return;
    }
    use crate::ir::Val;
    use crate::primop::{binary_primops, unary_primops};
    use Exp::*;
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let loc = SourceLoc::unknown();
    let (level, width) = guarded_width(&mut s, 128, 3, 1);
    let other = s.declare_const(Ty::Bool, loc);
    let unary = unary_primops();
    let binary = binary_primops();
    s.assert(Var(level));
    // 移位原语允许保留符号量，用模型核对结果与具体移位完全一致。
    for op in ["shiftl", "shiftr", "arith_shiftr"] {
        let bits = Val::Bits(B64::ones(12));
        let result = binary[op](bits.clone(), Val::Symbolic(width), &mut s, loc).unwrap();
        let expected = binary[op](bits, Val::I128(9), &mut s, loc).unwrap();
        let unequal = Neq(
            Box::new(crate::primop_util::smt_value(&result, loc).unwrap()),
            Box::new(crate::primop_util::smt_value(&expected, loc).unwrap()),
        );
        assert!(s.check_sat_with(&unequal, loc).is_unsat().unwrap(), "{op}");
    }
    s.with_deferred_region_queries(|s| {
        let child = s.start_transaction_with_guard(Some(Var(other)));
        for name in [
            "zeros",
            "ones",
            "undefined_bitvector",
            "zero_extend",
            "sign_extend",
            "replicate_bits",
            "sail_truncate",
            "sail_truncateLSB",
            "pow_int",
            "string_take",
            "string_drop",
            "vector_access",
            "vector_init",
            "undefined_vector",
            "subrange_internal",
            "%i->%i64",
        ] {
            PROJECT_TRANSLATIONS.set(0);
            let mut call = |arg| match name {
                "zeros" | "ones" | "undefined_bitvector" => unary[name](arg, s, loc),
                "string_take" | "string_drop" => binary[name](Val::String("abcdefghijk".into()), arg, s, loc),
                "vector_init" | "undefined_vector" => binary[name](arg, Val::Unit, s, loc),
                "subrange_internal" => {
                    crate::primop::subrange_internal(Val::Bits(B64::ones(12)), arg, Val::I128(2), s, loc)
                }
                "%i->%i64" => unary[name](arg, s, loc),
                "vector_access" => {
                    binary[name](Val::Vector((0..12).map(|i| Val::String(i.to_string())).collect()), arg, s, loc)
                }
                "pow_int" => binary[name](Val::I128(2), arg, s, loc),
                "sail_truncate" | "sail_truncateLSB" => binary[name](Val::Bits(B64::ones(12)), arg, s, loc),
                _ => binary[name](Val::Bits(B64::ones(3)), arg, s, loc),
            };
            let actual = call(Val::Symbolic(width)).unwrap();
            let expected = call(Val::I128(9)).unwrap();
            if name == "undefined_bitvector" {
                assert_eq!(crate::primop_util::length_bits(&actual, s, loc).unwrap(), 9);
            } else if let Val::Symbolic(sym) = actual {
                let result = crate::primop::proven_symbolic_i128(sym, s, loc).unwrap().unwrap();
                assert_eq!(expected, Val::I64(result.try_into().unwrap()), "{name}");
            } else {
                assert_eq!(actual, expected, "{name}");
            }
            assert_eq!(PROJECT_TRANSLATIONS.get(), 0, "{name} 的长度已由本臂唯一确定");
        }
        s.rollback_transaction(child);
    });
}

#[test]
fn scalar_resolver_matches_eager_values_and_reachability() {
    if !resolver_test("scalar_resolver_matches_eager_values_and_reachability") {
        return;
    }
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let site = SourceLoc::unknown();
    let (level, width) = guarded_width(&mut solver, 8, 3, 253);
    for guard in [None, Some(true), Some(false)] {
        let point = solver.start_transaction();
        if let Some(positive) = guard {
            solver.assert(if positive { Exp::Var(level) } else { not(Exp::Var(level)) });
        }
        let values = |domain| match domain {
            FiniteDomain::Known(values) | FiniteDomain::Bounded(values) => values,
            FiniteDomain::Unknown => panic!("有限夹具必须能得到候选"),
        };
        let baseline = values(solver.finite_domain(width));
        let actual = values(solver.resolve_scalar(width, site));
        assert!(actual.iter().all(|v| baseline.contains(v)));
        for n in [0, 9, 247] {
            let reachable = solver.check_sat_with(&equal(width, n), site).is_sat().unwrap();
            assert_eq!(actual.contains(&bits64(n, 8)), reachable);
        }
        solver.rollback_transaction(point);
    }
}

#[test]
fn scalar_resolver_range_obligation_checks_original_read_domain() {
    if !resolver_test("scalar_resolver_range_obligation_checks_original_read_domain") {
        return;
    }
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let site = SourceLoc::unknown();
    for reachable_bad in [true, false] {
        let mut s = Solver::<B64>::new(&ctx);
        let input = s.declare_bitvector(64, site);
        let level = s.declare_const(Ty::Bool, site);
        let len =
            s.define_const(Exp::Ite(Box::new(Exp::Var(level)), Box::new(bits64(4, 64)), Box::new(bits64(0, 64))), site);
        // 一个独立的非字面量断言使无见证的候选保持 Bounded。
        s.assert(Exp::Bvult(Box::new(Exp::Var(input)), Box::new(bits64(7, 64))));
        let root = s.start_transaction();
        s.with_deferred_region_queries(|s| {
            if !reachable_bad {
                s.assert(Exp::Var(level));
            }
            let choice = s
                .resolve_scalar_choice(
                    len,
                    Some(OperandBounds::RequireWithin(1..=i128::from(u32::MAX / 8))),
                    true,
                    site,
                )
                .unwrap();
            assert_eq!(choice.values, vec![bits64(4, 64)]);
            if reachable_bad {
                assert_eq!(s.check_deferred_assertions(site), Some(SmtResult::Sat));
            } else {
                assert!(matches!(s.check_deferred_assertions(site), None | Some(SmtResult::Unsat)));
            }
        });
        s.rollback_transaction(root);
        assert!(s.check_sat_with(&not(Exp::Var(level)), site).is_sat().unwrap());
    }
}

#[test]
fn scalar_resolver_read_checks_all_shift_widths() {
    if !resolver_test("scalar_resolver_read_checks_all_shift_widths") {
        return;
    }
    use Exp::*;
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let site = SourceLoc::unknown();
    // 64 位左移的上界包含零与全部二次幂。地址读长只允许前 29 个二次幂。
    let domain: Vec<_> = std::iter::once(bits64(0, 64)).chain((0..64).map(|n| bits64(1 << n, 64))).collect();
    let valid: Vec<_> = (0..29).map(|n| bits64(1 << n, 64)).collect();
    assert_eq!(domain.len() - valid.len(), 36);
    for guarded in [false, true] {
        let mut s = Solver::<B64>::new(&ctx);
        let shift = s.declare_bitvector(64, site);
        let width = s.define_const(Bvshl(Box::new(bits64(1, 64)), Box::new(Var(shift))), site);
        let root = s.start_transaction();
        s.with_deferred_region_queries(|s| {
            if guarded {
                s.assert(Bvult(Box::new(Var(shift)), Box::new(bits64(29, 64))));
            }
            s.set_operand_bound(width, site, domain.clone());
            let choice = s
                .resolve_scalar_choice(
                    width,
                    Some(OperandBounds::RequireWithin(1..=i128::from(u32::MAX / 8))),
                    true,
                    site,
                )
                .unwrap();
            assert_eq!(choice.values, valid);
            if !guarded {
                assert!(choice.requires_checked_replay);
            }
            let checked = s.check_deferred_assertions(site);
            if guarded {
                assert!(matches!(checked, None | Some(SmtResult::Unsat)));
            } else {
                assert_eq!(checked, Some(SmtResult::Sat));
            }
        });
        s.rollback_transaction(root);
    }
}

#[test]
fn scalar_resolver_remapped_arrival_rebuilds_guarded_facts() {
    if !resolver_test("scalar_resolver_remapped_arrival_rebuilds_guarded_facts") {
        return;
    }
    configure_tastic(Tactic::Qfaufbv);
    let site = SourceLoc::unknown();
    let ctx = Context::new(Config::new());
    let mut main = Solver::<B64>::new(&ctx);
    let g = main.declare_const(Ty::Bool, site);
    let point = checkpoint(&mut main);
    let (remote, suffix, layouts) = std::thread::spawn(move || {
        let other = Context::new(Config::new());
        let mut s = Solver::<B64>::from_checkpoint(&other, point);
        let root = s.start_transaction();
        let owner = s.new_logical_arm(None);
        let sym = s.with_logical_arm(owner, |s| {
            let width =
                s.define_const(Exp::Ite(Box::new(Exp::Var(g)), Box::new(bits64(247, 8)), Box::new(bits64(9, 8))), site);
            s.start_transaction_with_guard(Some(Exp::Var(g)));
            s.commit_dead_transaction();
            width
        });
        let packet = (sym, s.export_arm_suffix(owner).unwrap(), s.export_scalar_layouts(sym.as_u32()));
        s.rollback_transaction(root);
        packet
    })
    .join()
    .unwrap();
    let root = main.start_transaction();
    let local = main.declare_bitvector(8, site);
    assert_eq!(local, remote);
    let target = main.fresh();
    let remap = SymRemap::from_pairs([(remote, target)]);
    let suffix: Vec<_> = suffix
        .into_iter()
        .map(|item| ArmSuffixEvent {
            guard: item.guard.as_ref().map(|g| remap.exp(g)),
            event: remap.event(&item.event),
            ..item
        })
        .collect();
    let arm = main.new_logical_arm(None);
    main.import_arm_suffix(arm, suffix);
    main.import_scalar_layouts(layouts.into_iter().map(|(sym, v)| (remap.get(sym), v)).collect());
    assert!(
        matches!(main.resolve_scalar(target,site),FiniteDomain::Known(v)|FiniteDomain::Bounded(v) if v==vec![bits64(9,8)])
    );
    assert!(main.check_sat_with(&equal(local, 247), site).is_sat().unwrap());
    assert!(main.check_sat_with(&equal(target, 247), site).is_unsat().unwrap());
    main.rollback_transaction(root);
    assert!(main.check_sat_with(&Exp::Var(g), site).is_sat().unwrap());
}

#[test]
fn scalar_resolver_only_records_new_predicates() {
    if !resolver_test("scalar_resolver_only_records_new_predicates") {
        return;
    }
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let site = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, site);
    let flags: Vec<_> = (0..4).map(|_| solver.declare_const(Ty::Bool, site)).collect();
    solver.assert(Exp::Var(flags[0]));
    solver.with_deferred_region_queries(|s| {
        let p = s.start_transaction_with_guard(Some(Exp::Var(flags[1])));
        s.resolve_scalar(x, site);
        super::scalar::PREDICATE_VISITS.set(0);
        for flag in &flags[2..] {
            let child = s.start_transaction_with_guard(Some(Exp::Var(*flag)));
            s.assert(equal(x, 3));
            assert_eq!(s.resolve_scalar(x, site), FiniteDomain::Bounded(vec![bits64(3, 8)]));
            s.rollback_transaction(child);
            assert_eq!(s.resolve_scalar(x, site), FiniteDomain::Unknown);
        }
        assert_eq!(super::scalar::PREDICATE_VISITS.get(), 4, "每个子臂各新增一条断言和一个守卫");
        s.rollback_transaction(p);
    });
}

#[test]
fn scalar_resolver_replays_range_before_assuming_it() {
    let directory = std::env::temp_dir().join(format!("isla-scalar-range-{}", std::process::id()));
    let options = crate::config::RegionOptions {
        symbolic_scalar_resolver: true,
        obligation_dump_dir: Some(directory.clone()),
        ..Default::default()
    };
    if !resolver_test_options("scalar_resolver_replays_range_before_assuming_it", options) {
        return;
    }
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let site = SourceLoc::unknown();
    std::fs::create_dir(&directory).unwrap();
    // 两个前缀都有活模型。只有第二个允许零字节请求。
    for expected in [Z3_L_FALSE, Z3_L_TRUE] {
        let mut solver = Solver::<B64>::new(&ctx);
        let length = solver.declare_bitvector(8, site);
        let root = solver.start_transaction_with_guard(Some(equal(length, if expected == Z3_L_FALSE { 4 } else { 0 })));
        solver.with_deferred_region_queries(|s| {
            assert!(s.defer_scalar_range(length, &(1..=8), None, site));
        });
        solver.rollback_transaction(root);
        let paths: Vec<_> = std::fs::read_dir(&directory).unwrap().map(|e| e.unwrap().path()).collect();
        assert_eq!(paths.len(), 1);
        let text = std::ffi::CString::new(std::fs::read(&paths[0]).unwrap()).unwrap();
        let replay = Solver::<B64>::new(&ctx);
        unsafe {
            Z3_solver_from_string(ctx.z3_ctx, replay.z3_solver, text.as_ptr());
            assert_eq!(Z3_solver_check(ctx.z3_ctx, replay.z3_solver), expected);
        }
        std::fs::remove_file(&paths[0]).unwrap();
    }
    std::fs::remove_dir(directory).unwrap();
}

#[test]
fn scalar_resolver_reuses_finite_sets_of_outer_guards() {
    if !resolver_test("scalar_resolver_reuses_finite_sets_of_outer_guards") {
        return;
    }
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let x = s.declare_bitvector(8, SourceLoc::unknown());
    let subject = Exp::Var(x);
    let choices = |a, b| Exp::Or(Box::new(equal(x, a)), Box::new(equal(x, b)));
    let outer = s.start_transaction_with_guard(Some(choices(2, 3)));
    assert_eq!(PathConditions::new(&s).unwrap().bounds(&subject), Some(vec![bits64(2, 8), bits64(3, 8)]));
    for value in [2, 3] {
        let inner = s.start_transaction_with_guard(Some(choices(value, 7)));
        assert_eq!(PathConditions::new(&s).unwrap().bounds(&subject), Some(vec![bits64(value, 8)]));
        s.rollback_transaction(inner);
        BOUND_NODE_VISITS.set(0);
        assert_eq!(PathConditions::new(&s).unwrap().bounds(&subject), Some(vec![bits64(2, 8), bits64(3, 8)]));
        assert_eq!(BOUND_NODE_VISITS.get(), 0, "返回父臂应直接恢复该符号的守卫有限集");
    }
    s.rollback_transaction(outer);
}

#[test]
fn scalar_resolver_certifies_declared_choice_arm_before_publish() {
    if !resolver_test("scalar_resolver_certifies_declared_choice_arm_before_publish") {
        return;
    }
    use Exp::*;
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let site = SourceLoc::unknown();
    for reachable_extra in [true, false] {
        let mut s = Solver::<B64>::new(&ctx);
        let flag = s.declare_const(Ty::Bool, site);
        let typed = s.declare_bitvector(8, site);
        let shift = s.declare_bitvector(8, site);
        s.assert(Or(Box::new(equal(typed, 2)), Box::new(equal(typed, 16))));
        // 另一个值臂含 0、全部单比特值。另一条断言决定其中是否真有额外可达值。
        if !reachable_extra {
            s.assert(Or(Box::new(equal(shift, 1)), Box::new(equal(shift, 4))));
        }
        let alt = Bvshl(Box::new(bits64(1, 8)), Box::new(Var(shift)));
        let val = s.define_const(Ite(Box::new(Var(flag)), Box::new(Var(typed)), Box::new(alt)), site);
        let length = s.define_const(ZeroExtend(8, Box::new(Var(val))), site);
        let root = s.start_transaction();
        s.with_deferred_region_queries(|s| {
            s.set_operand_bound(length, site, [0, 1, 2, 4, 8, 16, 32, 64, 128].map(|v| bits64(v, 16)).into());
            let choice =
                s.resolve_scalar_choice(length, Some(OperandBounds::RequireWithin(1..=64)), true, site).unwrap();
            assert_eq!(choice.values, [bits64(2, 16), bits64(16, 16)]);
            assert!(!choice.requires_checked_replay);
            assert_eq!(
                s.check_deferred_assertions(site),
                Some(if reachable_extra { SmtResult::Sat } else { SmtResult::Unsat })
            );
        });
        s.rollback_transaction(root);
        assert_eq!(
            s.check_sat_with(&Eq(Box::new(Var(length)), Box::new(bits64(32, 16))), site).is_sat().unwrap(),
            reachable_extra
        );
    }
}
