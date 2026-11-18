use super::*;
use smtlib::Exp as Formula;

fn equal(symbol: Sym, value: u64) -> Formula<Sym> {
    Formula::Eq(Box::new(Formula::Var(symbol)), Box::new(smtlib::bits64(value, 64)))
}

fn lengths(
    no_smt: bool,
    enabled: bool,
    assertions: impl FnOnce(&mut Solver<B64>, Sym),
) -> (Vec<Result<(u32, Vec<u64>), ExecError>>, usize) {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let mut cfg = Config::new();
    cfg.solver_options.no_smt = no_smt;
    cfg.solver_options.finite_domain_enumeration = enabled;
    let context = Context::new(cfg);
    let verification = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let symbol = solver.declare_bitvector(64, info());
    assertions(&mut solver, symbol);

    let variable = test_name(745);
    let mut frame = make_frame(vec![
        Instr::PrimopUnary(Loc::Id(RETURN), primop::unary_primops::<B64>()["zeros"], Exp::Id(variable), info()),
        Instr::End,
    ]);
    frame.vars_mut().insert(variable, UVal::Init(Val::Symbolic(symbol)));
    let state = TaskState::new();
    let shared = empty_shared_state();
    let queue = Worker::new_lifo();
    queue.push(frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)));
    let mut results = Vec::new();
    let mut queries = 0;
    while let Some(task) = queue.pop() {
        let mut solver = Solver::from_checkpoint(&context, task.checkpoint);
        if let Some((def, event)) = task.fork_cond {
            solver.add_event(event);
            solver.add(def);
        }
        let start = crate::smt::test_query_count();
        let result = run_loop(
            0,
            task.id,
            &mut task.fraction.clone(),
            PathTimeout::unlimited(),
            task.stop_conditions,
            &SingleForkSink { queue: &queue },
            &mut unfreeze_frame(&task.frame),
            &state,
            &shared,
            &mut solver,
        );
        queries += crate::smt::test_query_count() - start;
        match result {
            Ok(Run::Finished(Val::Bits(value))) => {
                let mut solver = Solver::from_checkpoint(&verification, checkpoint(&mut solver));
                let values = (0..=9)
                    .filter(|value| solver.check_sat_with(&equal(symbol, *value), info()).is_sat().unwrap())
                    .collect();
                results.push(Ok((value.len(), values)));
            }
            Ok(Run::Dead) => (),
            Ok(_) => panic!("意外的终态"),
            Err(error) => results.push(Err(error)),
        }
    }
    (results, queries)
}

fn four_lengths(solver: &mut Solver<B64>, symbol: Sym) {
    let domain = [1, 2, 4, 8]
        .into_iter()
        .map(|value| equal(symbol, value))
        .reduce(|a, b| Formula::Or(Box::new(a), Box::new(b)))
        .unwrap();
    let guard = solver.define_const(domain, info());
    solver.assert(Formula::Var(guard));
}

#[test]
fn symbolic_finite_domain_enumerates_length_without_smt() {
    let (results, queries) = lengths(true, true, four_lengths);
    let mut concrete: Vec<_> = results.into_iter().collect::<Result<_, _>>().unwrap();
    concrete.sort();
    assert_eq!(concrete, [(1, vec![1]), (2, vec![2]), (4, vec![4]), (8, vec![8])]);
    assert_eq!(queries, 0);
}

#[test]
fn symbolic_finite_domain_keeps_every_explicit_candidate_above_the_old_limit() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let mut cfg = Config::new();
    cfg.solver_options.no_smt = true;
    cfg.solver_options.finite_domain_enumeration = true;
    let context = Context::new(cfg);
    let mut solver = Solver::<B64>::new(&context);
    let symbol = solver.declare_bitvector(64, info());
    let start = crate::smt::test_query_count();
    assert!(matches!(solver.finite_domain(symbol), crate::smt::FiniteDomain::Unknown));
    let domain =
        (0..65).map(|value| equal(symbol, value)).reduce(|lhs, rhs| Formula::Or(Box::new(lhs), Box::new(rhs))).unwrap();
    solver.assert(domain);
    let crate::smt::FiniteDomain::Known(values) = solver.finite_domain(symbol) else {
        panic!("结构上已知的 65 个具体值必须全部保留");
    };
    assert_eq!(values, (0..65).map(|value| smtlib::bits64(value, 64)).collect::<Vec<_>>());
    assert_eq!(crate::smt::test_query_count() - start, 0);
}

#[test]
fn symbolic_finite_domain_matches_smt_enumeration() {
    let expected = vec![(1, vec![1]), (2, vec![2]), (4, vec![4]), (8, vec![8])];
    for enabled in [false, true] {
        let (results, queries) = lengths(false, enabled, four_lengths);
        let mut concrete: Vec<_> = results.into_iter().collect::<Result<_, _>>().unwrap();
        concrete.sort();
        assert_eq!(concrete, expected);
        assert_eq!(queries == 0, enabled, "启用状态 {enabled}，查询次数 {queries}");
    }
}

#[test]
fn symbolic_finite_domain_handles_ite_intersection_and_exclusions() {
    let (results, queries) = lengths(true, true, |solver, symbol| {
        four_lengths(solver, symbol);
        let selector = solver.declare_const(smtlib::Ty::Bool, info());
        let ite = Formula::Ite(
            Box::new(Formula::Var(selector)),
            Box::new(Formula::Or(Box::new(equal(symbol, 1)), Box::new(equal(symbol, 2)))),
            Box::new(Formula::Or(Box::new(equal(symbol, 2)), Box::new(equal(symbol, 4)))),
        );
        solver.assert(Formula::And(Box::new(ite), Box::new(Formula::Not(Box::new(equal(symbol, 2))))));
    });
    let mut concrete: Vec<_> = results.into_iter().collect::<Result<_, _>>().unwrap();
    concrete.sort();
    assert_eq!(concrete, [(1, vec![1]), (4, vec![4])]);
    assert_eq!(queries, 0);
}

#[test]
fn symbolic_finite_domain_unknown_reports_error_and_does_not_certify() {
    for (enabled, constrained) in [(false, true), (true, false)] {
        let (results, queries) = lengths(true, enabled, |solver, symbol| {
            if constrained {
                four_lengths(solver, symbol);
            }
        });
        assert!(matches!(results.as_slice(), [Err(ExecError::Smt(crate::error::SmtError::NoSmt { .. }))]));
        assert_eq!(queries, 0);
    }

    let (results, queries) = lengths(true, true, |solver, symbol| {
        four_lengths(solver, symbol);
        let dependent = solver.declare_bitvector(64, info());
        let expr = Formula::Bvadd(Box::new(Formula::Var(symbol)), Box::new(Formula::Var(dependent)));
        solver.assert_eq(expr, smtlib::bits64(9, 64));
    });
    assert!(matches!(results.as_slice(), [Err(ExecError::Smt(crate::error::SmtError::NoSmt { .. }))]));
    assert_eq!(queries, 0);
}

#[test]
fn symbolic_finite_domain_region_preserves_retry_and_rollback() {
    use crate::smt::FiniteDomain;
    use symbolic_length::ValueRetry;
    let mut cfg = Config::new();
    cfg.solver_options.no_smt = true;
    cfg.solver_options.finite_domain_enumeration = true;
    let context = Context::new(cfg);
    let mut solver = Solver::<B64>::new(&context);
    let symbol = solver.declare_bitvector(64, info());
    let mut frame = make_frame(vec![Instr::End]);
    frame.region_execution = Some(region_merge::RegionExecution {
        region: Arc::new(crate::ir::regions::Region {
            branch_pc: 0,
            has_back_edge: false,
            join: crate::ir::regions::RegionPoint::Instruction(0),
            nodes: Default::default(),
            kind: crate::ir::regions::RegionKind::Reconvergent,
            local_variables: Default::default(),
        }),
        entry_depth: 0,
        write_depth: 0,
        depth: 1,
        remaining: None,
        iteration_budget: None,
        additional_fragments: None,
        mode: crate::config::MergeMode::Adaptive,
        origin: (frame.function_name, 0, info()),
        pending_branch: None,
    });

    let shared = empty_shared_state();
    let state = TaskState::new();
    let queue = Worker::new_lifo();
    let mut fraction = Fraction::one();
    let mut retry = |solver: &mut Solver<B64>| {
        symbolic_length::fork_symbolic_value(
            symbol,
            &[Val::Symbolic(symbol)],
            info(),
            TaskId::fresh(),
            &mut fraction,
            None,
            &SingleForkSink { queue: &queue },
            &mut frame,
            &state,
            solver,
            &shared,
        )
    };

    let tx = solver.start_transaction();
    four_lengths(&mut solver, symbol);
    let start = crate::smt::test_query_count();
    assert!(matches!(
        retry(&mut solver),
        Err(ExecError::SpeculativeReject { reason: SpeculativeRejectReason::RetryOperand, .. })
    ));
    let inner = solver.start_transaction_with_guard(Some(equal(symbol, 4)));
    assert!(matches!(retry(&mut solver), Ok(ValueRetry::Unique)));
    let zeros = primop::unary_primops::<B64>()["zeros"];
    assert_eq!(zeros(Val::Symbolic(symbol), &mut solver, info()).unwrap(), Val::Bits(B64::zeros(4)));
    solver.rollback_transaction(inner);
    assert!(matches!(solver.finite_domain(symbol), FiniteDomain::Known(values) if values.len() == 4));
    solver.rollback_transaction(tx);
    assert!(matches!(solver.finite_domain(symbol), FiniteDomain::Unknown));
    let after = solver.start_transaction_with_guard(Some(equal(symbol, 9)));
    assert_eq!(zeros(Val::Symbolic(symbol), &mut solver, info()).unwrap(), Val::Bits(B64::zeros(9)));
    solver.rollback_transaction(after);
    assert!(queue.is_empty());
    assert!(fraction.is_one());
    assert_eq!(crate::smt::test_query_count() - start, 0);
}

#[test]
fn symbolic_finite_domain_does_not_reinterpret_published_assertions_after_rebinding() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let mut cfg = Config::new();
    cfg.solver_options.finite_domain_enumeration = true;
    let context = Context::new(cfg);
    let mut solver = Solver::<B64>::new(&context);
    let symbol = solver.declare_bitvector(64, info());
    solver.assert(equal(symbol, 1));
    let tx = solver.start_transaction();
    // 已发布等式仍使用旧声明，重新绑定只影响当前符号和新断言。
    solver.add(Def::DefineConst(symbol, smtlib::bits64(2, 64)));
    assert!(solver.check_sat(info()).is_sat().unwrap());
    assert!(matches!(solver.finite_domain(symbol), crate::smt::FiniteDomain::Unknown));
    solver.rollback_transaction(tx);
    assert!(matches!(
        solver.finite_domain(symbol),
        crate::smt::FiniteDomain::Known(values) if values == vec![smtlib::bits64(1, 64)]
    ));
}

#[test]
fn symbolic_finite_domain_prunes_exhaustive_match_default_with_active_guards() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let mut cfg = Config::new();
    cfg.solver_options.no_smt = true;
    cfg.solver_options.finite_domain_enumeration = true;
    let context = Context::new(cfg);
    let mut solver = Solver::<B64>::new(&context);
    let state = solver.declare_bitvector(64, info());
    let field = Formula::Extract(12, 11, Box::new(Formula::Var(state)));
    let alias = solver.define_bitvector(field.clone(), info());
    let equal = |exp, value| Formula::Eq(Box::new(exp), Box::new(smtlib::bits64(value, 2)));
    solver.assert(
        [0, 1, 3]
            .into_iter()
            .map(|value| equal(field.clone(), value))
            .reduce(|lhs, rhs| Formula::Or(Box::new(lhs), Box::new(rhs)))
            .unwrap(),
    );
    let start = crate::smt::test_query_count();
    let invalid = solver.define_const(equal(Formula::Var(alias), 2), info());
    assert!(matches!(
        solver.check_sat_with_for_branch(&Formula::Var(invalid), info(), true),
        Some(crate::smt::SmtResult::Unsat)
    ));
    assert!(solver.check_sat_with_for_branch(&Formula::Not(Box::new(Formula::Var(invalid))), info(), true).is_none());
    let mut txs = Vec::new();
    for value in [0, 1] {
        let cond = Formula::Not(Box::new(equal(Formula::Var(alias), value)));
        txs.push(solver.start_transaction_with_guard(Some(cond)));
    }
    let default = Formula::Not(Box::new(equal(Formula::Var(alias), 3)));
    assert!(matches!(solver.check_sat_with_for_branch(&default, info(), true), Some(crate::smt::SmtResult::Unsat)));
    for tx in txs.into_iter().rev() {
        solver.rollback_transaction(tx);
    }
    assert!(solver.check_sat_with_for_branch(&default, info(), true).is_none());
    assert_eq!(crate::smt::test_query_count() - start, 0);
}

#[test]
fn symbolic_finite_domain_concretizes_scaled_length_and_range() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let mut cfg = Config::new();
    cfg.solver_options.no_smt = true;
    cfg.solver_options.finite_domain_enumeration = true;
    let context = Context::new(cfg);
    let mut solver = Solver::<B64>::new(&context);
    let width = solver.declare_bitvector(64, info());
    four_lengths(&mut solver, width);
    let mut txs = Vec::new();
    for value in [1, 2, 4] {
        txs.push(solver.start_transaction_with_guard(Some(Formula::Not(Box::new(equal(width, value))))));
    }
    // 另一条约束不影响宽度蕴含；结构层无需先认证完整路径。
    let unrelated = solver.declare_bitvector(64, info());
    solver.assert(Formula::Bvule(Box::new(Formula::Var(unrelated)), Box::new(smtlib::bits64(100, 64))));
    let length = solver.define_const(
        Formula::Bvmul(
            Box::new(Formula::SignExtend(64, Box::new(Formula::Var(width)))),
            Box::new(smtlib::bits64(8, 128)),
        ),
        info(),
    );
    let high =
        solver.define_const(Formula::Bvsub(Box::new(Formula::Var(length)), Box::new(smtlib::bits64(1, 128))), info());
    let start = crate::smt::test_query_count();
    let zeros = primop::unary_primops::<B64>()["zeros"];
    assert_eq!(zeros(Val::Symbolic(length), &mut solver, info()).unwrap(), Val::Bits(B64::zeros(64)));
    assert_eq!(
        primop::subrange_internal(Val::Bits(B64::ones(64)), Val::Symbolic(high), Val::I128(0), &mut solver, info())
            .unwrap(),
        Val::Bits(B64::ones(64))
    );
    assert_eq!(crate::smt::test_query_count() - start, 0);
    for tx in txs.into_iter().rev() {
        solver.rollback_transaction(tx);
    }
}
