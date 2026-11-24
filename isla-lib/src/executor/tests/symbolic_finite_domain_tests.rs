use super::region_merge_tests::run_in_diagnostics_process;
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
    run_length_consumer(no_smt, enabled, |solver, symbol, variable| {
        assertions(solver, symbol);
        (symbol, Instr::PrimopUnary(Loc::Id(RETURN), primop::unary_primops()["zeros"], Exp::Id(variable), info()))
    })
}

pub(super) fn run_length_consumer(
    no_smt: bool,
    enabled: bool,
    consumer: impl FnOnce(&mut Solver<B64>, Sym, Name) -> (Sym, Instr<Name, B64>),
) -> (Vec<Result<(u32, Vec<u64>), ExecError>>, usize) {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let mut cfg = Config::new();
    cfg.solver_options.no_smt = no_smt;
    cfg.solver_options.finite_domain_enumeration = enabled;
    let context = Context::new(cfg);
    let verification = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let symbol = solver.declare_bitvector(64, info());
    let variable = test_name(745);
    let (operand, instruction) = consumer(&mut solver, symbol, variable);
    let mut frame = make_frame(vec![instruction, Instr::End]);
    frame.vars_mut().insert(variable, UVal::Init(Val::Symbolic(operand)));
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
    if !run_in_diagnostics_process(concat!(module_path!(), "::symbolic_finite_domain_matches_smt_enumeration")) {
        return;
    }
    crate::config::RegionOptions { symbolic_scalar_resolver: false, ..Default::default() }.configure();
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
        assert!(matches!(results.as_slice(), [Err(ExecError::Smt(cause))] if cause.reject_reason() == if enabled {
            SpeculativeRejectReason::UnknownFiniteDomain
        } else { SpeculativeRejectReason::UnknownDeferredMode }));
        let label = if enabled { "SmtError::FiniteDomain:" } else { "SmtError::NoSmt:" };
        assert!(results[0].as_ref().unwrap_err().to_string().starts_with(label));
        assert_eq!(queries, 0);
    }
    let (results, queries) = lengths(true, true, |solver, symbol| {
        four_lengths(solver, symbol);
        let dependent = solver.declare_bitvector(64, info());
        let expr = Formula::Bvadd(Box::new(Formula::Var(symbol)), Box::new(Formula::Var(dependent)));
        solver.assert_eq(expr, smtlib::bits64(9, 64));
    });
    assert!(matches!(results.as_slice(), [Err(ExecError::Smt(crate::error::SmtError::FiniteDomain { .. }))]));
    assert_eq!(queries, 0);
}

#[test]
fn symbolic_finite_domain_region_preserves_retry_and_rollback() {
    if !run_in_diagnostics_process(concat!(
        module_path!(),
        "::symbolic_finite_domain_region_preserves_retry_and_rollback"
    )) {
        return;
    }
    crate::config::RegionOptions { symbolic_scalar_resolver: false, ..Default::default() }.configure();
    use crate::smt::FiniteDomain;
    use symbolic_length::ValueRetry;
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let mut cfg = Config::new();
    cfg.solver_options.no_smt = true;
    cfg.solver_options.finite_domain_enumeration = true;
    let context = Context::new(cfg);
    let mut solver = Solver::<B64>::new(&context);
    let symbol = solver.declare_bitvector(64, info());
    let mut frame = make_frame(vec![Instr::End]);
    frame.region_execution = Some(region_merge::RegionExecution {
        remote_cancel: None,
        region: Arc::new(crate::ir::regions::Region {
            branch_pc: 0,
            has_back_edge: false,
            join: crate::ir::regions::RegionPoint::Instruction(0),
            nodes: Default::default(),
            kind: crate::ir::regions::RegionKind::Reconvergent,
            local_variables: Default::default(),
        }),
        entry_depth: 0,
        catch_return: None,
        write_depth: 0,
        depth: 1,
        remaining: None,
        iteration_budget: None,
        additional_fragments: None,
        mode: crate::config::MergeMode::Adaptive,
        origin: (frame.function_name, 0, info()),
        pending_branch: None,
        verified_prefix: None,
    });

    let shared = empty_shared_state();
    let state = TaskState::new();
    let queue = Worker::new_lifo();
    let mut fraction = Fraction::one();
    let mut retry = |solver: &mut Solver<B64>| {
        symbolic_length::fork_symbolic_value(
            symbol,
            None,
            None,
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

    // 同一个消费者在有 Z3 的延后区域内也能区分推导不足与普通必需查询。
    let mut config = Config::new();
    config.solver_options.finite_domain_enumeration = true;
    let query_context = Context::new(config);
    let mut query_solver = Solver::<B64>::new(&query_context);
    assert_eq!(query_solver.declare_bitvector(64, info()), symbol);
    let tx = query_solver.start_transaction();
    let before = crate::smt::test_query_count();
    query_solver.with_deferred_region_queries(|solver| {
        let Err(missing) = retry(solver) else { panic!("无有限域的延后枚举必须拒绝") };
        assert_eq!(missing.rejection_reason(), Some(SpeculativeRejectReason::UnknownFiniteDomain));
        assert_eq!(missing.query_failure().unwrap().diagnostic()["symbol"], symbol.as_u32());
        let mandatory = solver.check_sat(info()).is_sat().unwrap_err();
        assert_eq!(mandatory.rejection_reason(), Some(SpeculativeRejectReason::UnknownDeferredMode));
    });
    query_solver.rollback_transaction(tx);
    assert_eq!(crate::smt::test_query_count(), before);
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

#[test]
fn symbolic_finite_domain_zero_extend_with_bounded_width() {
    for (no_smt, constrain_other, input_width, expected) in [
        (true, false, 1, Some(vec![(32, vec![4]), (64, vec![8])])),
        (false, false, 1, Some(vec![(32, vec![4]), (64, vec![8])])),
        (true, true, 1, Some(vec![(32, vec![4]), (64, vec![])])),
        (false, true, 1, Some(vec![(32, vec![4])])),
        (true, true, 40, None),
    ] {
        let (results, queries) = run_length_consumer(no_smt, true, |solver, bytes, variable| {
            let address = solver.declare_bitvector(64, info());
            let is_device = equal(address, 4096);
            // 设备臂的短路条件确保访问宽度是 4 或 8 字节。
            solver.assert(Formula::Ite(
                Box::new(is_device),
                Box::new(Formula::Ite(
                    Box::new(equal(bytes, 8)),
                    Box::new(Formula::Bool(true)),
                    Box::new(equal(bytes, 4)),
                )),
                Box::new(Formula::Bool(false)),
            ));
            let other = solver.declare_bitvector(64, info());
            solver.assert_eq(
                Formula::Bvadd(Box::new(Formula::Var(bytes)), Box::new(Formula::Var(other))),
                smtlib::bits64(8192, 64),
            );
            if constrain_other {
                solver.assert(equal(other, 8188));
            }
            let width = solver.define_const(
                Formula::Bvmul(
                    Box::new(Formula::SignExtend(64, Box::new(Formula::Var(bytes)))),
                    Box::new(smtlib::bits64(8, 128)),
                ),
                info(),
            );
            assert!(matches!(solver.finite_domain(width), crate::smt::FiniteDomain::Bounded(v) if v.len() == 2));
            (
                width,
                Instr::PrimopBinary(
                    Loc::Id(RETURN),
                    primop::binary_primops()["zero_extend"],
                    Exp::Bits(B64::new(1, input_width)),
                    Exp::Id(variable),
                    info(),
                ),
            )
        });
        if let Some(expected) = expected {
            let mut concrete: Vec<_> = results.into_iter().collect::<Result<_, _>>().unwrap();
            concrete.sort();
            assert_eq!(concrete, expected);
        } else {
            let [Err(ExecError::Smt(crate::error::SmtError::FiniteDomain { width, candidates: Some(values), .. }))] =
                results.as_slice()
            else {
                panic!("位宽上界不足时必须报告原候选，实际 {results:?}")
            };
            assert_eq!(*width, 128);
            assert_eq!(values.len(), 2);
        }
        if no_smt {
            assert_eq!(queries, 0);
        }
    }
}

#[test]
fn symbolic_finite_domain_subrange_with_guarded_high_bound() {
    for (no_smt, source_width) in [(true, 64), (false, 64), (true, 48)] {
        let (results, queries) = run_length_consumer(no_smt, true, |solver, mode, high| {
            let is_short = equal(mode, 1);
            solver.assert(Formula::Or(Box::new(is_short.clone()), Box::new(equal(mode, 2))));
            let other = solver.declare_bitvector(64, info());
            solver.assert(Formula::Bvule(Box::new(Formula::Var(other)), Box::new(smtlib::bits64(100, 64))));
            let width = solver.define_const(
                Formula::Ite(Box::new(is_short), Box::new(smtlib::bits64(39, 64)), Box::new(smtlib::bits64(57, 64))),
                info(),
            );
            let upper = solver.define_const(
                Formula::Bvsub(
                    Box::new(Formula::SignExtend(64, Box::new(Formula::Var(width)))),
                    Box::new(smtlib::bits64(1, 128)),
                ),
                info(),
            );
            assert!(matches!(solver.finite_domain(upper), crate::smt::FiniteDomain::Bounded(v) if v.len() == 2));
            (
                upper,
                Instr::PrimopVariadic(
                    Loc::Id(RETURN),
                    primop::variadic_primops()["vector_subrange"],
                    vec![Exp::Bits(B64::ones(source_width)), Exp::Id(high), Exp::I128(0)],
                    info(),
                ),
            )
        });
        if source_width == 64 {
            let mut actual = results.into_iter().collect::<Result<Vec<_>, _>>().unwrap();
            actual.sort();
            assert_eq!(actual, [(39, vec![1]), (57, vec![2])]);
        } else {
            assert!(results.iter().all(|result| !matches!(result, Ok((57, _)))));
        }
        if no_smt {
            assert_eq!(queries, 0);
        }
    }
}

#[test]
fn symbolic_finite_domain_projects_through_integer_conversions() {
    let (results, queries) = run_length_consumer(true, true, |solver, bytes, variable| {
        let wide = solver.define_const(Formula::SignExtend(64, Box::new(Formula::Var(bytes))), info());
        let four_or_eight = [4, 8]
            .into_iter()
            .map(|x| Formula::Eq(Box::new(Formula::Var(wide)), Box::new(smtlib::bits64(x, 128))))
            .reduce(|a, b| Formula::Or(Box::new(a), Box::new(b)))
            .unwrap();
        solver.assert(four_or_eight);
        let low = solver.define_const(Formula::Extract(63, 0, Box::new(Formula::Var(wide))), info());
        let width = solver.define_const(
            Formula::Bvmul(
                Box::new(smtlib::bits64(8, 128)),
                Box::new(Formula::SignExtend(64, Box::new(Formula::Var(low)))),
            ),
            info(),
        );
        let low = solver.define_const(Formula::Extract(63, 0, Box::new(Formula::Var(width))), info());
        let width = solver.define_const(Formula::SignExtend(64, Box::new(Formula::Var(low))), info());
        (
            width,
            Instr::PrimopBinary(
                Loc::Id(RETURN),
                primop::binary_primops()["zero_extend"],
                Exp::Bits(B64::new(1, 1)),
                Exp::Id(variable),
                info(),
            ),
        )
    });
    let mut concrete: Vec<_> = results.into_iter().collect::<Result<_, _>>().unwrap();
    concrete.sort();
    assert_eq!(concrete, [(32, vec![4]), (64, vec![8])]);
    assert_eq!(queries, 0);
}
#[test]
fn symbolic_finite_domain_projects_masked_slices_through_ite() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    use Formula::*;
    let bits = smtlib::bits64;
    let equal = |lhs, rhs| Eq(Box::new(lhs), Box::new(rhs));
    let slice = |sym, high, low| Extract(high, low, Box::new(Var(sym)));

    for no_smt in [false, true] {
        let mut cfg = Config::new();
        cfg.solver_options.no_smt = no_smt;
        cfg.solver_options.finite_domain_enumeration = true;
        let context = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&context);
        let a = solver.declare_bitvector(64, info());
        let b = solver.declare_bitvector(64, info());
        let condition = solver.declare_const(smtlib::Ty::Bool, info());
        let pin = |sym, mask, value| equal(Bvand(Box::new(bits(mask, 64)), Box::new(Var(sym))), bits(value, 64));
        solver.assert(pin(a, 0x0f00_0000_0000_0000, 0x0a00_0000_0000_0000));
        solver.assert(pin(b, 0x0000_000f_0000_0000, 0x0000_000a_0000_0000));
        let merged = solver.define_bitvector(
            Ite(Box::new(Var(condition)), Box::new(slice(a, 59, 58)), Box::new(slice(b, 33, 32))),
            info(),
        );
        let start = crate::smt::test_query_count();
        assert_eq!(solver.finite_domain_bool(&equal(Var(merged), bits(0, 2))), Some(false));
        assert_eq!(solver.finite_domain_bool(&equal(Var(merged), bits(2, 2))), Some(true));
        assert_eq!(solver.finite_domain_bool(&equal(slice(a, 56, 55), bits(0, 2))), None);

        let c = solver.declare_bitvector(64, info());
        let guard = solver.start_transaction_with_guard(Some(pin(c, 3, 2)));
        assert_eq!(solver.finite_domain_bool(&equal(slice(c, 1, 0), bits(2, 2))), Some(true));
        solver.rollback_transaction(guard);
        assert_eq!(solver.finite_domain_bool(&equal(slice(c, 1, 0), bits(2, 2))), None);
        assert_eq!(crate::smt::test_query_count() - start, 0);
    }
}
