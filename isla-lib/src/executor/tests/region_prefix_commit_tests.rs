use super::*;

#[test]
fn prefix_remembers_a_live_merge_before_later_dead_or_unclosed_records() {
    let record = super::super::merge_history_tests::record;
    let mut history = MergeHistory::default();
    let mut cut = region_merge::prefix_commit::Cut {
        record_start: 0,
        resume_in_parent: false,
        can_resume_normally: true,
        saw_live_merge: false,
        rejection: None,
    };
    let mut dead = record(1);
    dead.dead = true;
    history.push(dead.clone());
    history.mark_closed(0);
    cut.remember_live_merge(&history);
    assert!(!cut.saw_live_merge);
    history.push(record(2));
    history.mark_closed(1);
    cut.remember_live_merge(&history);
    assert!(cut.saw_live_merge);
    dead.record_id = 3;
    history.push(dead);
    history.mark_closed(2);
    assert!(!history.has_live_closed_tail_since(0));
    cut.remember_live_merge(&history);
    history.push(record(4));
    assert!(!history.has_live_closed_tail_since(0));
    cut.remember_live_merge(&history);
    assert!(cut.saw_live_merge);
}

#[test]
fn verified_prefix_rolls_back_only_the_rejected_instruction() {
    if !run_in_diagnostics_process(concat!(
        module_path!(),
        "::verified_prefix_rolls_back_only_the_rejected_instruction"
    )) {
        return;
    }
    crate::config::RegionOptions {
        defer_exit_check: true,
        partial_commit_deferred_mode: true,
        partial_commit_prefix: true,
        ..Default::default()
    }
    .configure();

    run_deep_region_test(|| {
        let mut shared = empty_shared_state();
        let register = shared.symtab.intern("zverified_prefix_register");
        shared.registers.insert(register, Ty::Bool);
        let chosen = test_name(2210);
        let data = test_name(2211);
        let ignored = test_name(2212);
        let prefix_executions = Arc::new(AtomicUsize::new(0));
        let finished_prefix = prefix_executions.clone();
        let address = Exp::Bits(B64::new(0x1000, 64));
        let byte = Exp::Bits(B64::new(7, 8));
        let program = vec![
            Instr::Decl(chosen, Ty::Bool, info()),
            Instr::Decl(data, Ty::Bits(8), info()),
            Instr::Jump(input(0), 5, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            Instr::Goto(15),
            Instr::Jump(input(1), 8, info()),
            Instr::Copy(Loc::Id(chosen), Exp::Bool(false), info()),
            Instr::Goto(9),
            Instr::Copy(Loc::Id(chosen), Exp::Bool(true), info()),
            Instr::PrimopReset(
                Loc::Id(ignored),
                Arc::new(move |_, _, solver| {
                    finished_prefix.fetch_add(1, Ordering::Relaxed);
                    solver.cycle_count();
                    Ok(Val::Unit)
                }),
                primop::Effect::Pure,
                info(),
            ),
            Instr::Copy(Loc::Id(register), Exp::Id(chosen), info()),
            Instr::PrimopVariadic(
                Loc::Id(ignored),
                primop::variadic_primops()["platform_write_mem"],
                vec![Exp::Unit, Exp::I128(64), address.clone(), Exp::I128(1), byte.clone()],
                info(),
            ),
            Instr::PrimopReset(
                Loc::Id(ignored),
                Arc::new(|_, _, solver| {
                    if solver.region_queries_deferred() {
                        solver.assert(Formula::Bool(false));
                        solver.cycle_count();
                    }
                    solver.check_sat(info()).is_sat()?;
                    Ok(Val::Unit)
                }),
                primop::Effect::Pure,
                info(),
            ),
            Instr::PrimopVariadic(
                Loc::Id(data),
                primop::variadic_primops()["platform_read_mem"],
                vec![Exp::Unit, Exp::I128(64), address, Exp::I128(1)],
                info(),
            ),
            Instr::Copy(
                Loc::Id(RETURN),
                Exp::Call(Op::And, vec![Exp::Id(register), Exp::Call(Op::Eq, vec![Exp::Id(data), byte])]),
                info(),
            ),
            Instr::End,
        ];
        let run = |merge| {
            paths_with_solver_state(
                program.clone(),
                &shared,
                2,
                ExecutionLimits::default().with_path_merging(merge).with_region_global_state(true),
                crate::memory::Memory::new(),
                |frame, solver| {
                    frame.regs_mut().insert(register, false, UVal::Init(Val::Bool(false)));
                    frame.vars_mut().insert(ignored, UVal::Init(Val::Unit));
                    crate::memory::install_seq_memory(frame.memory_mut(), 64, solver, true);
                },
                false,
            )
        };
        let (ordinary, _, _) = run(false);
        assert_eq!(prefix_executions.swap(0, Ordering::Relaxed), 2);
        let (resumed, _, reasons) = run(true);
        equivalent_paths(&ordinary, &resumed, 2, true);
        equivalent_register_paths(&ordinary, &resumed, 2);
        assert_eq!(prefix_executions.load(Ordering::Relaxed), 1, "已汇合的前缀不能从根入口重算");
        let reason = SpeculativeRejectReason::UnknownDeferredMode.to_string();
        assert_eq!(reasons[&reason], 1, "延后模式未判定必须留在统计中");
        assert_eq!(resumed.len(), 2);
        let with_memory =
            resumed.iter().find(|path| path.events.iter().any(Event::is_memory_write)).expect("恢复臂必须保留 RAM 写");
        let event_counts = |path: &Path| {
            (
                path.events.iter().filter(|event| event.is_cycle()).count(),
                path.events.iter().filter(|event| event.is_memory_read()).count(),
                path.events.iter().filter(|event| event.is_memory_write()).count(),
                path.events.iter().filter(|event| matches!(event, Event::WriteReg(..))).count(),
            )
        };
        assert_eq!(event_counts(with_memory), (1, 1, 1, 1));
        assert!(resumed.iter().any(|path| event_counts(path) == (0, 0, 0, 0)));
        assert_eq!(with_memory.records.iter().map(|record| record.branch_pc).collect::<Vec<_>>(), [5]);
        let write_guard = with_memory
            .checkpoint
            .trace()
            .as_ref()
            .unwrap()
            .events_with_guards_rev()
            .find_map(|(event, guard)| event.is_memory_write().then_some(guard).flatten())
            .expect("RAM 写的完整到达守卫必须保留");
        let context = Context::new(Config::new());
        let mut solver = Solver::from_checkpoint(&context, with_memory.checkpoint.clone());
        assert_eq!(solver.check_sat_with(&Formula::Not(Box::new(write_guard.clone())), info()), SmtResult::Unsat);
        let read_value = with_memory
            .events
            .iter()
            .find_map(|event| match event {
                Event::ReadMem { value, .. } => Some(smt_value(value, info()).unwrap()),
                _ => None,
            })
            .unwrap();
        assert_eq!(
            solver.check_sat_with(&Formula::Neq(Box::new(read_value), Box::new(smtlib::bits64(7, 8))), info()),
            SmtResult::Unsat,
        );
    });
}

#[derive(Clone, Copy)]
enum CutCase {
    Disabled,
    InfeasibleSibling,
    FailedObligation,
    PathTimeout,
    BufferedError,
    BufferedErrorOnly,
    Injected { reason: SpeculativeRejectReason, expect_cut: bool },
}

fn check_direct_cut(case: CutCase) {
    let failure_pc = 8;
    let shared = empty_shared_state();
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let root = solver.declare_const(smtlib::Ty::Bool, info());
    let nested = solver.declare_const(smtlib::Ty::Bool, info());
    let clock = Arc::new(Mutex::new(None::<path_timing::PathTiming>));
    let set_clock = clock.clone();
    if matches!(case, CutCase::InfeasibleSibling | CutCase::Injected { .. }) {
        solver.assert(Formula::Var(root));
    } else if matches!(case, CutCase::BufferedErrorOnly) {
        solver.assert(Formula::Not(Box::new(Formula::Var(root))));
    }
    let mut frame = make_frame(vec![
        Instr::Jump(input(0), 3, info()),
        Instr::PrimopReset(
            Loc::Id(RETURN),
            Arc::new(move |_, _, _| {
                if matches!(case, CutCase::BufferedError | CutCase::BufferedErrorOnly) {
                    Err(ExecError::Type("prefix test arm error".into(), info()))
                } else {
                    Ok(Val::Bool(false))
                }
            }),
            primop::Effect::Pure,
            info(),
        ),
        Instr::Goto(9),
        Instr::Jump(input(1), 6, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(7),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
        Instr::PrimopReset(
            Loc::Id(RETURN),
            Arc::new(move |_, _, solver| {
                if matches!(case, CutCase::FailedObligation) {
                    solver.defer_assertion(Formula::Bool(false), info());
                } else if matches!(case, CutCase::PathTimeout) {
                    set_clock
                        .lock()
                        .unwrap()
                        .as_ref()
                        .unwrap()
                        .start_active_at(Instant::now() - Duration::from_secs(2), crate::timing::thread_cpu_time());
                }
                Ok(Val::Bool(true))
            }),
            primop::Effect::Pure,
            info(),
        ),
        Instr::PrimopReset(
            Loc::Id(RETURN),
            Arc::new(move |_, _, solver| {
                if let CutCase::Injected { reason, .. } = case {
                    return Err(ExecError::SpeculativeReject {
                        reason,
                        function: TOP_LEVEL_LET,
                        pc: failure_pc,
                        location: info(),
                        cause: None,
                    });
                }
                solver.check_sat(info()).is_sat()?;
                Ok(Val::Bool(true))
            }),
            primop::Effect::Pure,
            info(),
        ),
        Instr::End,
    ]);
    frame.function_name = TOP_LEVEL_LET;
    *clock.lock().unwrap() = Some(frame.path_timing.clone());
    frame.vars_mut().insert(test_name(900), UVal::Init(Val::Symbolic(root)));
    frame.vars_mut().insert(test_name(901), UVal::Init(Val::Symbolic(nested)));
    let mut state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(true));
    state.reverse_region_ready = matches!(case, CutCase::BufferedError | CutCase::BufferedErrorOnly);
    state.speculation_stats = speculation::SpeculationStats::new(true);
    let queue = Worker::new_lifo();
    let result = region_merge::try_region(
        root,
        3,
        0,
        TaskId::fresh(),
        &mut Fraction::one(),
        PathTimeout::from_seconds(matches!(case, CutCase::PathTimeout).then_some(1)),
        None,
        &SingleForkSink { queue: &queue },
        &mut frame,
        &state,
        &shared,
        &mut solver,
        info(),
    )
    .unwrap();
    assert_eq!(solver.transaction_depth(), 0);
    let reasons = &state.speculation_stats.reject_json()["reason_counts"];
    match case {
        CutCase::Injected { reason, expect_cut } => {
            if expect_cut {
                assert!(matches!(result, region_merge::RegionResult::Merged), "合成路由 {reason:?} 应固化前缀");
                assert_eq!(frame.pc, failure_pc, "{reason:?}");
                assert_eq!(frame.region_merge_records.len(), 1, "{reason:?}");
            } else {
                assert!(matches!(result, region_merge::RegionResult::Rejected), "合成路由 {reason:?} 应回到入口");
                assert_eq!(frame.pc, 0, "{reason:?}");
                assert!(frame.region_merge_records.is_empty(), "{reason:?}");
            }
            assert!(queue.is_empty(), "{reason:?}");
            assert_eq!(reasons[reason.to_string()], 1, "{reason:?}");
        }
        CutCase::Disabled | CutCase::FailedObligation | CutCase::PathTimeout => {
            assert!(matches!(result, region_merge::RegionResult::Rejected));
            assert_eq!(frame.pc, 0);
            assert!(frame.region_merge_records.is_empty());
            assert!(queue.is_empty());
            let reason = match case {
                CutCase::Disabled => SpeculativeRejectReason::UnknownDeferredMode,
                CutCase::FailedObligation => {
                    assert_eq!(reasons[SpeculativeRejectReason::UnknownDeferredMode.to_string()], 1);
                    SpeculativeRejectReason::SymbolicAssertion
                }
                _ => {
                    assert!(frame.path_timing.snapshot().active_wall >= Duration::from_secs(2));
                    SpeculativeRejectReason::PathTimeout
                }
            };
            assert_eq!(reasons[reason.to_string()], 1);
        }
        CutCase::InfeasibleSibling => {
            assert!(matches!(result, region_merge::RegionResult::Merged));
            assert_eq!(frame.pc, failure_pc, "应恢复可满足组的真正失败 PC");
            assert_eq!(frame.region_merge_records.len(), 1);
            assert!(queue.is_empty(), "整根可满足也不能发布守卫不可满足的兄弟臂");
            assert_eq!(solver.check_sat(info()), SmtResult::Sat);
        }
        CutCase::BufferedError | CutCase::BufferedErrorOnly => {
            if matches!(case, CutCase::BufferedErrorOnly) {
                assert!(matches!(result, region_merge::RegionResult::Dead), "正常组为空但仍须发布错误叶");
                assert_eq!(solver.check_sat(info()), SmtResult::Unsat);
            } else {
                assert!(matches!(result, region_merge::RegionResult::Merged));
                assert_eq!(frame.pc, failure_pc);
                assert_eq!(solver.check_sat(info()), SmtResult::Sat);
            }
            let task = queue.pop().expect("失败指令前已缓冲的错误叶必须被发布");
            assert!(queue.is_empty(), "错误叶只发布一次");
            assert!(matches!(task.frame.arm_error, Some((ExecError::Type(..), true))));
            let mut replay = Solver::from_checkpoint(&context, task.checkpoint);
            let Some((Def::Assert(error_guard), _)) = task.fork_cond else {
                panic!("错误叶必须保留完整守卫")
            };
            replay.assert(error_guard);
            assert_eq!(replay.check_sat(info()), SmtResult::Sat);
            assert_eq!(replay.check_sat_with(&Formula::Var(root), info()), SmtResult::Unsat);
        }
    }
}

#[test]
fn prefix_routes_all_rejection_reasons_at_a_safe_instruction_boundary() {
    use SpeculativeRejectReason::*;
    // 在同一可撤销原语上注入标签，含目前无生产发射点的标签。
    // 这里只验证安全边界的路由。真实求解器策略、准入、到限、外部效应与汇合分别由专测覆盖。
    const ROUTES: [(SpeculativeRejectReason, bool); 51] = [
        (UnknownFiniteDomain, true),
        (UnknownZ3, true),
        (Z3Timeout, true),
        (Z3ResourceExhausted, true),
        (UnknownDeferredMode, true),
        (ExitUnsat, false),
        (SymbolicAssertion, false),
        (PathTimeout, false),
        (NoJoin, true),
        (HasBackEdge, true),
        (ExceptionCheck, true),
        (RegionEscaped, true),
        (StackEscaped, false),
        (StepBudget, false),
        (NestingLimit, true),
        (FragmentLimit, false),
        (StateEffect, true),
        (UnknownExtern, true),
        (RecursiveEffect, false),
        (CalleeStateWrite, true),
        (RegisterReadAfterWrite, true),
        (RepeatedRegisterWrite, true),
        (RegisterReadWrite, true),
        (RegisterSequence, false),
        (RelaxedRegister, false),
        (IncompatibleState, false),
        (UnionPayload, false),
        (DepthMismatch, false),
        (LoopHistoryMismatch, false),
        (SamplingState, false),
        (PolicyOff, true),
        (SymbolicJump, false),
        (Monomorphize, true),
        (ExpressionRetry, true),
        (UnaryRetry, true),
        (BinaryRetry, true),
        (VariadicRetry, true),
        (SpecialCallRetry, true),
        (IntegerConversion, true),
        (RetryCondition, true),
        (SymbolicValueEnumeration, true),
        (RetryOperand, true),
        (AnnouncePc, false),
        (Interrupt, true),
        (ZeroInstruction, true),
        (LimitSampling, false),
        (LimitTruncation, false),
        (Assume, true),
        (Assert, true),
        (Arbitrary, true),
        (Exit, true),
    ];
    const CHILD: &str = "ISLA_TEST_PREFIX_REASON_ROUTING";
    let (enabled, expect_enabled) = match std::env::var(CHILD).as_deref() {
        Ok("off") => (false, false),
        Ok("on") => (true, true),
        // 定向红测保留开关开启时的预期，但关闭实际能力。
        Ok("red") => (false, true),
        Ok(_) => panic!("前缀路由夹具模式无效"),
        Err(std::env::VarError::NotUnicode(_)) => panic!("前缀路由夹具模式必须是文本"),
        Err(std::env::VarError::NotPresent) => {
            let test = concat!(module_path!(), "::prefix_routes_all_rejection_reasons_at_a_safe_instruction_boundary");
            let test = test.strip_prefix("isla_lib::").unwrap();
            for mode in ["off", "on"] {
                let output = std::process::Command::new(std::env::current_exe().unwrap())
                    .args(["--exact", test, "--nocapture"])
                    .env(CHILD, mode)
                    .output()
                    .unwrap();
                let stdout = String::from_utf8_lossy(&output.stdout);
                assert!(
                    output.status.success() && stdout.contains("test result: ok. 1 passed;"),
                    "前缀路由模式 {mode} 失败\n{stdout}{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                println!("前缀路由模式 {mode} 已验证 {} 种标签", ROUTES.len());
            }
            return;
        }
    };
    crate::config::RegionOptions {
        defer_exit_check: true,
        partial_commit_prefix: enabled,
        partial_commit_finite_domain: true,
        partial_commit_unknown_z3: true,
        partial_commit_z3_timeout: true,
        partial_commit_z3_resource_exhausted: true,
        partial_commit_deferred_mode: true,
        partial_commit_retry_operand: true,
        partial_commit_structure: true,
        partial_commit_state_effect: true,
        partial_commit_control: true,
        ..Default::default()
    }
    .configure();
    run_deep_region_test(move || {
        for (reason, supported) in ROUTES {
            check_direct_cut(CutCase::Injected { reason, expect_cut: expect_enabled && supported });
        }
    });
}

#[test]
fn prefix_disabled_by_default_replays_the_root() {
    if !run_in_diagnostics_process(concat!(module_path!(), "::prefix_disabled_by_default_replays_the_root")) {
        return;
    }
    crate::config::RegionOptions { defer_exit_check: true, partial_commit_deferred_mode: true, ..Default::default() }
        .configure();
    run_deep_region_test(|| check_direct_cut(CutCase::Disabled));
}

#[test]
fn prefix_checks_guards_obligations_and_buffered_errors() {
    if !run_in_diagnostics_process(concat!(module_path!(), "::prefix_checks_guards_obligations_and_buffered_errors")) {
        return;
    }
    crate::config::RegionOptions {
        defer_exit_check: true,
        arm_error_leaf: true,
        partial_commit_deferred_mode: true,
        partial_commit_prefix: true,
        ..Default::default()
    }
    .configure();
    run_deep_region_test(|| {
        for case in [
            CutCase::InfeasibleSibling,
            CutCase::FailedObligation,
            CutCase::PathTimeout,
            CutCase::BufferedError,
            CutCase::BufferedErrorOnly,
        ] {
            check_direct_cut(case);
        }
    });
}
