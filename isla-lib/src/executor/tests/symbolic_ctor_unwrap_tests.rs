use super::*;

#[test]
fn 符号构造子的直接与字段解包必须检查标签可满足性() {
    let tag_a = test_name(740);
    let tag_b = test_name(741);
    let value = test_name(742);
    let field = test_name(743);
    let shared = empty_shared_state();
    for through_field in [false, true] {
        for selected_tag in [Some(tag_a), Some(tag_b), None] {
            crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let tag = solver.declare_const(Name::smt_ty(), info());
            if let Some(selected_tag) = selected_tag {
                solver.assert(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(tag)), Box::new(selected_tag.to_smt())));
            }
            let mut frame = make_frame(vec![Instr::End]);
            frame.vars_mut().insert(
                value,
                UVal::Init(Val::SymbolicCtor(
                    tag,
                    HashMap::from_iter([(tag_a, Val::Bits(B64::new(11, 8))), (tag_b, Val::Bits(B64::new(22, 8)))]),
                )),
            );
            let exp = if through_field {
                Exp::Field(Box::new(Exp::Struct(test_name(744), vec![(field, Exp::Id(value))])), field)
            } else {
                Exp::Id(value)
            };
            let result = eval_exp(
                &Exp::Unwrap(tag_a, Box::new(exp)),
                Arc::make_mut(&mut frame.local_state),
                &shared,
                &mut solver,
                info(),
            )
            .map(Cow::into_owned);
            if selected_tag == Some(tag_b) {
                assert!(matches!(result, Err(ExecError::Type(..))), "标签不可匹配时必须保留类型错误");
            } else if selected_tag.is_none() {
                let Err(ExecError::RetryCondition(condition, _)) = result else {
                    panic!("标签不确定时必须请求条件分叉")
                };
                assert!(solver.check_sat_with(&condition, info()).is_sat().unwrap());
                assert!(solver.check_sat_with(&smtlib::Exp::Not(Box::new(condition)), info()).is_sat().unwrap());
            } else {
                assert_eq!(result.unwrap(), Val::Bits(B64::new(11, 8)));
            }
        }
    }
}

#[test]
fn region_util_defer_ctor_obligation_checks_original_guard() {
    const CHILD: &str = "REGION_UTIL_CTOR_TEST_CHILD";
    let Ok(mode) = std::env::var(CHILD) else {
        for mode in ["false", "true"] {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "executor::tests::symbolic_ctor_unwrap_tests::region_util_defer_ctor_obligation_checks_original_guard", "--nocapture"])
                .env(CHILD, mode).output().unwrap();
            assert!(
                output.status.success(),
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }
        return;
    };
    let enabled = mode == "true";
    let mut options = crate::config::RegionOptions::default();
    options.defer_ctor_checks = enabled;
    options.configure();
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    for safe in [false, true] {
        let shared = empty_shared_state();
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let tag = solver.declare_const(Name::smt_ty(), info());
        let a = test_name(740);
        let b = test_name(741);
        let matches = smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(tag)), Box::new(a.to_smt()));
        if safe {
            solver.assert(matches.clone());
        }
        let root = solver.start_transaction();
        let mut frame = make_frame(vec![Instr::End]);
        let slot = test_name(742);
        frame.vars_mut().insert(
            slot,
            UVal::Init(Val::SymbolicCtor(
                tag,
                HashMap::from_iter([(a, Val::Bits(B64::new(11, 8))), (b, Val::Bits(B64::new(22, 8)))]),
            )),
        );
        // 设置推演访问日志；测试直接覆盖表达式解包和出口证明。
        frame.local_state = Arc::new(LocalState {
            speculative_access: Some(region_merge::AccessLog {
                writes: WriteSet::default(),
                reads: Vec::new(),
                published_reads: Vec::new(),
                read_guards: Vec::new(),
                guard: Some(smtlib::Exp::Bool(true)),
                initial_registers: HashMap::new(),
                initial_variables: HashMap::new(),
                initial_lets: HashMap::new(),
                call_scope: 0,
                function: frame.function_name,
                pc: 0,
                location: info(),
                writes_allowed: true,
                global_state: true,
                ordered_events: false,
            }),
            ..(*frame.local_state).clone()
        });
        solver.with_deferred_region_queries(|solver| {
            let result = eval_exp(
                &Exp::Unwrap(a, Box::new(Exp::Id(slot))),
                Arc::make_mut(&mut frame.local_state),
                &shared,
                solver,
                info(),
            )
            .map(Cow::into_owned);
            if enabled {
                assert_eq!(result.unwrap(), Val::Bits(B64::new(11, 8)));
                solver.assert(smtlib::Exp::Bool(false));
                assert_eq!(
                    solver.check_deferred_assertions(info()),
                    Some(if safe { SmtResult::Unsat } else { SmtResult::Sat })
                );
            } else {
                assert!(matches!(result, Err(ExecError::Z3Unknown)));
            }
        });
        solver.rollback_transaction(root);
        assert_eq!(solver.check_sat(info()), SmtResult::Sat);
    }
}

#[test]
fn no_smt_constructor_unwrap_assumes_matching_tag_without_query() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let tag_a = test_name(740);
    let tag_b = test_name(741);
    let value = test_name(742);
    let shared = empty_shared_state();
    let mut cfg = Config::new();
    cfg.solver_options.no_smt = true;
    let ctx = Context::new(cfg);
    let mut solver = Solver::<B64>::new(&ctx);
    let tag = solver.declare_const(Name::smt_ty(), info());
    let mut frame = make_frame(vec![Instr::End]);
    frame.vars_mut().insert(
        value,
        UVal::Init(Val::SymbolicCtor(
            tag,
            HashMap::from_iter([(tag_a, Val::Bits(B64::new(11, 8))), (tag_b, Val::Bits(B64::new(22, 8)))]),
        )),
    );
    crate::smt::reset_path_smt_stats();
    let result = eval_exp(
        &Exp::Unwrap(tag_a, Box::new(Exp::Id(value))),
        Arc::make_mut(&mut frame.local_state),
        &shared,
        &mut solver,
        info(),
    )
    .map(Cow::into_owned);
    assert_eq!(result.unwrap(), Val::Bits(B64::new(11, 8)));
    assert_eq!(crate::smt::path_smt_stats().calls, 0);
    let point = checkpoint(&mut solver);
    let verification = Context::new(Config::new());
    let mut restored = Solver::from_checkpoint(&verification, point);
    assert!(restored
        .check_sat_with(&smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(tag)), Box::new(tag_b.to_smt())), info())
        .is_unsat()
        .unwrap());
}
