use super::ground::{eval_assertion, AstEvaluator};
use super::*;
use Exp::*;

fn random(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

fn constant(width: u32, state: &mut u64) -> Exp<Sym> {
    Bits((0..width).map(|_| random(state) & 1 != 0).collect())
}

#[test]
fn ground_assertions_match_z3_for_thousands_of_assignments() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let mut state = 0xcafe_9ad0_c6fe_bb01;
    for width in [1, 8, 32, 64, 65, 127, 128, 129] {
        let x = solver.declare_bitvector(width, info);
        let y = solver.declare_bitvector(width, info);
        let u = solver.declare_bitvector(width, info);
        let shifted = solver.define_const(Bvadd(Box::new(Var(x)), Box::new(bits64(1, width))), info);
        for case in 0..512 {
            let x_bits = if case % 17 == 0 { Bits(vec![true; width as usize]) } else { constant(width, &mut state) };
            let y_bits = if case % 7 == 0 { bits64(1, width) } else { constant(width, &mut state) };
            let u_bits = constant(width, &mut state);
            let variant = random(&mut state);
            let cmp = match variant % 8 {
                0 => Bvslt,
                1 => Bvsle,
                2 => Bvsgt,
                3 => Bvsge,
                4 => Bvult,
                5 => Bvule,
                6 => Bvugt,
                _ => Bvuge,
            };
            let op = match (variant >> 8) % 13 {
                0 => Bvadd,
                1 => Bvsub,
                2 => Bvmul,
                3 => Bvand,
                4 => Bvor,
                5 => Bvxor,
                6 => Bvshl,
                7 => Bvlshr,
                8 => Bvashr,
                9 => Bvnand,
                10 => Bvnor,
                11 => Bvxnor,
                _ => Bvadd,
            };
            let a = op(Box::new(Var(shifted)), Box::new(Var(y)));
            let b = if case % 13 == 12 { Bvneg(Box::new(Var(u))) } else { Var(u) };
            let middle = cmp(Box::new(Var(x)), Box::new(Var(y)));
            let expr = Ite(Box::new(middle), Box::new(a), Box::new(b));
            let expr = if width == 1 {
                expr
            } else {
                Concat(Box::new(Extract(width - 1, 1, Box::new(expr))), Box::new(Extract(0, 0, Box::new(Var(x)))))
            };
            let extension = u32::from(width < 129);
            let expr = if case % 3 == 0 {
                SignExtend(extension, Box::new(expr))
            } else {
                ZeroExtend(extension, Box::new(expr))
            };
            let other = if case % 3 == 0 {
                SignExtend(extension, Box::new(Var(u)))
            } else {
                ZeroExtend(extension, Box::new(Var(u)))
            };
            let first = cmp(Box::new(expr), Box::new(other));
            let second = Neq(Box::new(Var(x)), Box::new(Var(y)));
            let assertion = if variant >> 16 & 1 == 0 {
                And(Box::new(first), Box::new(second))
            } else {
                Or(Box::new(first), Box::new(Not(Box::new(second))))
            };
            let pairs = [(x, x_bits), (y, y_bits), (u, u_bits)];
            let source = pairs.iter().map(|(sym, _)| solver.translate_exp(&Var(*sym))).collect::<Vec<_>>();
            let concrete = pairs.iter().map(|(_, bits)| solver.translate_exp(bits)).collect::<Vec<_>>();
            let from = source.iter().map(|ast| ast.z3_ast).collect::<Vec<_>>();
            let to = concrete.iter().map(|ast| ast.z3_ast).collect::<Vec<_>>();
            let replacements = from.iter().copied().zip(to.iter().copied()).collect::<Vec<_>>();
            let ast = solver.translate_exp(&assertion);
            let expected = ast.substitute_many(&from, &to).structural_bool().expect("具体断言应可判定");
            let assignments = pairs.into_iter().collect::<HashMap<_, _>>();
            let prefix = PathConditions::new(&solver).unwrap();
            assert_eq!(
                eval_assertion(&assertion, |sym| assignments.get(&sym), |sym| prefix.definition(sym)),
                Some(expected),
                "宽度 {width}，样本 {case}"
            );
            assert_eq!(
                AstEvaluator::new(&ctx).evaluate(ast.z3_ast, &replacements),
                Some((expected, true)),
                "宽度 {width}，样本 {case}"
            );
        }
    }
}

#[test]
fn ground_assertions_decline_unknowns_and_keep_the_z3_result() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let x = solver.declare_bitvector(8, SourceLoc::unknown());
    let condition = Eq(Box::new(Var(x)), Box::new(bits64(2, 8)));
    let division = Eq(Box::new(Bvudiv(Box::new(Var(x)), Box::new(bits64(1, 8)))), Box::new(bits64(2, 8)));
    assert_eq!(eval_assertion(&condition, |_| None, |_| None), None);
    let bits = bits64(2, 8);
    assert_eq!(eval_assertion(&division, |sym| (sym == x).then_some(&bits), |_| None), None);
    let anchor = solver.translate_exp(&Var(x));
    let value = Ast::mk_bv_u64(&ctx, 8, 2);
    let original = solver.translate_exp(&division);
    assert_eq!(AstEvaluator::new(&ctx).evaluate(original.z3_ast, &[(anchor.z3_ast, value.z3_ast)]), None);
    assert_eq!(original.substitute(&anchor, &value).structural_bool(), Some(true));
}

#[test]
fn ground_assertions_follow_deep_definition_chains() {
    let mut definitions = HashMap::new();
    for i in 1..=20_000 {
        definitions.insert(Sym::from_u32(i), Bvadd(Box::new(Var(Sym::from_u32(i - 1))), Box::new(bits64(1, 16))));
    }
    let assertion = Eq(Box::new(Var(Sym::from_u32(20_000))), Box::new(bits64(20_001, 16)));
    let assignments = HashMap::from([(Sym::from_u32(0), bits64(1, 16))]);
    assert_eq!(eval_assertion(&assertion, |sym| assignments.get(&sym), |sym| definitions.get(&sym)), Some(true));
}

fn candidate_fixture<T>(stage3: bool, direct: bool, check: impl FnOnce(&mut Solver<'_, B64>, Sym, Sym, Sym) -> T) -> T {
    configure_tastic(Tactic::Qfaufbv);
    let mut config = Config::new();
    config.solver_options.finite_domain_ground_eval = direct;
    // 这里对照直接求值与整式 Z3 代入；稀疏代入有独立回归测试。
    config.solver_options.branch_candidate_sparse_rewrite = false;
    config.solver_options.incremental_choice_dag = stage3;
    config.solver_options.coi_query_slicing = stage3;
    let ctx = Context::new(config);
    let mut solver = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(8, info);
    let y = solver.declare_bitvector(8, info);
    let eq = |sym, n| Eq(Box::new(Var(sym)), Box::new(bits64(n, 8)));
    for sym in [x, y] {
        solver.assert(Or(Box::new(eq(sym, 1)), Box::new(eq(sym, 2))));
    }
    let add = Bvadd(Box::new(Var(x)), Box::new(bits64(1, 8)));
    solver.assert(Not(Box::new(Eq(Box::new(add), Box::new(bits64(3, 8))))));
    let target = solver.define_const(Bvshl(Box::new(Var(x)), Box::new(bits64(1, 8))), info);
    let joint = solver.define_const(Bvadd(Box::new(Var(x)), Box::new(Var(y))), info);
    check(&mut solver, x, target, joint)
}

#[test]
fn ground_branch_exclusions_preserve_candidate_order() {
    let run = |stage3, direct| {
        candidate_fixture(stage3, direct, |solver, x, _, _| {
            let prefix = PathConditions::new(solver).unwrap();
            let anchor = solver.translate_exp(&Var(x));
            let before = PROJECT_SUBSTITUTIONS.get();
            let excluded = [1, 2].map(|n| {
                let value = Ast::mk_bv_u64(solver.ctx, 8, n);
                prefix.excludes_branch_candidate(solver, &anchor, &value)
            });
            (excluded, PROJECT_SUBSTITUTIONS.get() - before)
        })
    };
    for stage3 in [false, true] {
        let (direct, direct_substitutions) = run(stage3, true);
        let (native, native_substitutions) = run(stage3, false);
        assert_eq!(direct, [false, true], "阶段 3={stage3}");
        assert_eq!(direct, native, "阶段 3={stage3}");
        assert!(direct_substitutions < native_substitutions, "阶段 3={stage3} 时应跳过原生代入");
    }
}

#[test]
fn ground_single_projection_preserves_candidates_and_certification() {
    let run = |stage3, direct| {
        candidate_fixture(stage3, direct, |solver, x, target, _| {
            let prefix = PathConditions::new(solver).unwrap();
            solver.project_finite_values(&prefix, target, x, vec![bits64(1, 8), bits64(2, 8)])
        })
    };
    for stage3 in [false, true] {
        let direct = run(stage3, true);
        assert_eq!(direct, FiniteDomain::Bounded(vec![bits64(2, 8)]), "阶段 3={stage3}");
        assert_eq!(direct, run(stage3, false), "阶段 3={stage3}");
    }
}

#[test]
fn ground_joint_narrowing_preserves_candidates_and_certification() {
    let base = vec![(bits64(2, 8), true), (bits64(3, 8), true)];
    let guarded = vec![(bits64(3, 8), true)];
    let run = |stage3, direct| {
        candidate_fixture(stage3, direct, |solver, x, _, joint| {
            let collect = |solver: &Solver<'_, B64>| {
                let prefix = PathConditions::new(solver).unwrap();
                let mut combined = Vec::new();
                solver
                    .combined_values(&prefix, &Var(joint), |mut ast, exact| {
                        combined.push((ast.finite_bits().unwrap(), exact));
                        true
                    })
                    .unwrap();
                combined
            };
            let mut results = vec![collect(solver), collect(solver)];
            let y_is_two = Eq(Box::new(Bvsub(Box::new(Var(joint)), Box::new(Var(x)))), Box::new(bits64(2, 8)));
            let tx = solver.start_transaction_with_guard(Some(y_is_two));
            results.extend([collect(solver), collect(solver)]);
            solver.rollback_transaction(tx);
            results.push(collect(solver));

            // 候选之外的独立断言只在开启 COI 的分支查询中移除。
            let loc = SourceLoc::unknown();
            let independent = solver.declare_const(Ty::Bool, loc);
            solver.assert(Var(independent));
            let impossible = Eq(Box::new(Var(x)), Box::new(bits64(2, 8)));
            let sliced = solver.coi_feasibility(&[impossible.clone()], Some(&impossible), loc, "branch_feasibility");
            if stage3 {
                assert_eq!(sliced, Some(Unsat));
                assert!(solver.coi_removed_assertions() > 0);
            } else {
                assert_eq!(sliced, None);
            }
            (results, sliced.unwrap_or_else(|| solver.check_sat_with(&impossible, loc)))
        })
    };
    let expected = (vec![base.clone(), base.clone(), guarded.clone(), guarded, base], Unsat);
    for stage3 in [false, true] {
        let direct = run(stage3, true);
        assert_eq!(direct, expected, "阶段 3={stage3}");
        assert_eq!(direct, run(stage3, false), "阶段 3={stage3}");
    }
}

#[test]
#[ignore = "手动对照四处候选检查的耗时"]
fn ground_call_site_timings() {
    use std::hint::black_box;

    configure_tastic(Tactic::Qfaufbv);
    let run = |enabled| {
        let mut config = Config::new();
        config.solver_options.finite_domain_ground_eval = enabled;
        let ctx = Context::new(config);
        let mut solver = Solver::<B64>::new(&ctx);
        let x = solver.declare_bitvector(64, SourceLoc::unknown());
        let formula = |x, n| {
            let a = Bvadd(Box::new(x), Box::new(bits64(n, 64)));
            let b = Bvmul(Box::new(a), Box::new(bits64(3, 64)));
            Bvult(Box::new(b), Box::new(bits64(100_000, 64)))
        };
        let exp = (0..32).map(|n| formula(Var(x), n)).collect::<Vec<_>>();
        for term in &exp {
            solver.assert(term.clone());
        }
        let prefix = PathConditions::new(&solver).unwrap();
        let asts = &prefix.index.asts;
        let anchor = solver.translate_exp(&Var(x));
        let values = (0..32).map(|n| Ast::mk_bv_u64(&ctx, 64, n)).collect::<Vec<_>>();
        let roots = exp.iter().map(|exp| asts.keep(solver.translate_exp(exp))).collect::<Vec<_>>();
        let folded = (0..1024).map(|n| solver.translate_exp(&formula(bits64(n, 64), 3 * n + 1))).collect::<Vec<_>>();
        let mut projection = AnchorProjection::default();
        let mut independent = HashSet::new();
        for &root in &roots {
            assert!(projection.contains_anchor(root, &anchor, &values[0], &mut independent));
        }
        let timed = |operation: &str, mut call: std::boxed::Box<dyn FnMut() -> usize + '_>| {
            let now = Instant::now();
            let result = black_box(call());
            let elapsed = now.elapsed().as_micros();
            eprintln!("ground_call_site {enabled} {operation} {elapsed} {result}");
            result
        };
        let branch = timed(
            "excludes_branch_candidate",
            Box::new(|| values.iter().filter(|v| !prefix.excludes_branch_candidate(&solver, &anchor, v)).count()),
        );
        let joint = timed(
            "narrow",
            Box::new(|| {
                values
                    .iter()
                    .map(|v| {
                        let replacements = [(anchor.z3_ast, v.z3_ast)];
                        roots
                            .iter()
                            .filter(|&&r| {
                                prefix
                                    .index
                                    .rewrites
                                    .for_assertion(false)
                                    .narrow(
                                        &replacements,
                                        &asts.get(r),
                                        &mut rewrites::InputDependencies::new(
                                            replacements.iter().map(|&(from, _)| from).enumerate(),
                                        ),
                                    )
                                    .1
                                    == Some(true)
                            })
                            .count()
                    })
                    .sum()
            }),
        );
        let single = timed(
            "project_assertion",
            Box::new(|| {
                values
                    .iter()
                    .map(|v| {
                        let mut rebuilt = HashMap::new();
                        roots
                            .iter()
                            .filter(|&&r| {
                                projection.project_assertion(asts, r, &anchor, v, &mut rebuilt).truth == Some(true)
                            })
                            .count()
                    })
                    .sum()
            }),
        );
        let simplified = timed(
            "simplified",
            Box::new(|| {
                folded
                    .iter()
                    .filter(|ast| prefix.index.rewrites.for_assertion(false).simplified((*ast).clone()).0 == Some(true))
                    .count()
            }),
        );
        [branch, joint, single, simplified]
    };
    for sample in 0..7 {
        let first = sample % 2 == 0;
        assert_eq!(run(first), [32, 1024, 1024, 1024]);
        assert_eq!(run(!first), [32, 1024, 1024, 1024]);
    }
}

#[test]
fn ground_assertions_respect_overlapping_ast_replacements() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let x = solver.declare_bitvector(8, SourceLoc::unknown());
    let x = solver.translate_exp(&Var(x));
    let one = Ast::mk_bv_u64(&ctx, 8, 1);
    let two = Ast::mk_bv_u64(&ctx, 8, 2);
    let three = Ast::mk_bv_u64(&ctx, 8, 3);
    let sum = Ast::mk_bvadd(&x, &one);
    let assertion = Ast::mk_eq(&sum, &three);
    let identity = [(sum.z3_ast, sum.z3_ast), (x.z3_ast, two.z3_ast)];
    let replace = [(sum.z3_ast, three.z3_ast), (x.z3_ast, one.z3_ast)];
    for (replacements, expected) in [(identity, None), (replace, Some(true))] {
        let (from, to): (Vec<_>, Vec<_>) = replacements.into_iter().unzip();
        assert_eq!(assertion.substitute_many(&from, &to).structural_bool(), expected);
        assert_eq!(
            AstEvaluator::new(&ctx).evaluate(assertion.z3_ast, &replacements),
            expected.map(|value| (value, true))
        );
    }
}
