use super::*;

fn admit_structure(max_merge_depth: Option<i64>) {
    crate::config::RegionOptions {
        partial_commit_prefix: true,
        partial_commit_structure: true,
        max_merge_depth,
        ..Default::default()
    }
    .configure();
}

#[test]
fn nesting_limit_splits_the_inner_branch_before_a_child_savepoint() {
    if !run_in_diagnostics_process(concat!(
        module_path!(),
        "::nesting_limit_splits_the_inner_branch_before_a_child_savepoint"
    )) {
        return;
    }
    admit_structure(Some(1));
    run_deep_region_test(|| {
        let mut shared = empty_shared_state();
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let touched = Arc::new(AtomicUsize::new(0));
        let counter = touched.clone();
        let program = vec![
            Instr::Jump(input(0), 3, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            Instr::Goto(8),
            Instr::PrimopReset(
                Loc::Id(RETURN),
                Arc::new(move |_, _, solver| {
                    counter.fetch_add(1, Ordering::Relaxed);
                    solver.cycle_count();
                    Ok(Val::Unit)
                }),
                primop::Effect::Pure,
                info(),
            ),
            Instr::Jump(input(1), 7, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::Goto(8),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            Instr::End,
        ];
        let ordinary = paths(program.clone(), &shared, 2, false);
        assert_eq!(touched.swap(0, Ordering::Relaxed), 1);
        let resumed = paths(program, &shared, 2, true);
        assert_eq!(equivalent_paths(&ordinary, &resumed, 2, true), (3, 1));
        assert_eq!(touched.load(Ordering::Relaxed), 1, "内层准入拒绝不能重跑父臂");
        assert_eq!(resumed[0].events.iter().filter(|event| event.is_cycle()).count(), 1);
        assert!(!resumed[0].records.is_empty());
        assert!(resumed[0].records.iter().all(|record| record.branch_pc == 0));
        let rejected = shared.execution_stats.arm_unsupported_json(&shared.symtab);
        let rows = rejected["top"].as_array().unwrap();
        assert_eq!(rows.len(), 1, "{rejected}");
        assert_eq!(rows[0]["branch_pc"], 4);
        assert_eq!(rows[0]["reason"], serde_json::json!(SpeculativeRejectReason::NestingLimit));
    });
}

#[test]
fn structural_rejection_and_its_negative_cache_hit_keep_both_parent_branches() {
    if !run_in_diagnostics_process(concat!(
        module_path!(),
        "::structural_rejection_and_its_negative_cache_hit_keep_both_parent_branches"
    )) {
        return;
    }
    admit_structure(None);
    run_deep_region_test(|| {
        let mut shared = empty_shared_state();
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let child = shared.symtab.intern("zadmission_exception_branch");
        let body = vec![
            Instr::Jump(Exp::Id(HAVE_EXCEPTION), 3, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::End,
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            Instr::End,
        ];
        shared
            .functions
            .insert(child, (vec![(HAVE_EXCEPTION, &Ty::Bool)], &Ty::Bool, Box::leak(body.into_boxed_slice())));
        let call = |operand| Instr::Call(Loc::Id(RETURN), false, child, vec![operand], info());
        let program =
            vec![Instr::Jump(input(0), 3, info()), call(input(1)), Instr::Goto(4), call(input(2)), Instr::End];
        let ordinary = paths(program.clone(), &shared, 3, false);
        let resumed = paths(program, &shared, 3, true);
        assert_eq!(equivalent_paths(&ordinary, &resumed, 3, true), (4, 1));
        assert!(!resumed[0].records.is_empty());
        assert!(resumed[0].records.iter().all(|record| record.function == TOP_LEVEL_LET));
        assert_eq!(shared.execution_stats.merge_json()["negative_cache_hits"], 1);
        let rejected = shared.execution_stats.arm_unsupported_json(&shared.symtab);
        let rows = rejected["top"].as_array().unwrap();
        assert_eq!(rows.len(), 1, "{rejected}");
        assert_eq!(rows[0]["function"], "admission_exception_branch");
        assert_eq!(rows[0]["branch_pc"], 0);
        assert_eq!(rows[0]["target_pc"], 0);
        assert_eq!(rows[0]["reason"], serde_json::json!(SpeculativeRejectReason::ExceptionCheck));
        assert_eq!(rows[0]["count"], 2);
    });
}

#[test]
fn explicit_off_splits_without_attempting_to_merge_the_child() {
    if !run_in_diagnostics_process(concat!(
        module_path!(),
        "::explicit_off_splits_without_attempting_to_merge_the_child"
    )) {
        return;
    }
    crate::config::RegionOptions { partial_commit_prefix: true, partial_commit_control: true, ..Default::default() }
        .configure();
    run_deep_region_test(|| {
        let mut shared = empty_shared_state();
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let callee = shared.symtab.intern("zadmission_explicit_off");
        let guard = test_name(2280);
        let body = vec![
            Instr::Jump(Exp::Id(guard), 3, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::End,
        ];
        shared.functions.insert(callee, (vec![(guard, &Ty::Bool)], &Ty::Bool, Box::leak(body.into_boxed_slice())));
        let program = vec![
            Instr::Jump(input(0), 3, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            Instr::Goto(4),
            Instr::Call(Loc::Id(RETURN), false, callee, vec![input(1)], info()),
            Instr::End,
        ];
        let ordinary = paths(program.clone(), &shared, 2, false);
        let limits = policy_limits(&shared, vec![(callee, crate::config::MergeMode::Off)]).with_path_merging(true);
        let resumed = paths_with_state(program, &shared, 2, limits, crate::memory::Memory::new(), |_| ());
        assert_eq!(equivalent_paths(&ordinary, &resumed, 2, true), (3, 1));
        assert_eq!(shared.execution_stats.merge_json()["attempts"], 1);
        let rejected = shared.execution_stats.arm_unsupported_json(&shared.symtab);
        assert_eq!(rejected["top"][0]["function"], "admission_explicit_off");
        assert_eq!(rejected["top"][0]["reason"], serde_json::json!(SpeculativeRejectReason::PolicyOff));
    });
}

#[test]
fn dynamic_state_effect_runs_outside_ancestor_transactions_without_replaying_prefix() {
    if !run_in_diagnostics_process(concat!(
        module_path!(),
        "::dynamic_state_effect_runs_outside_ancestor_transactions_without_replaying_prefix"
    )) {
        return;
    }
    crate::config::RegionOptions {
        defer_exit_check: true,
        partial_commit_prefix: true,
        partial_commit_state_effect: true,
        ..Default::default()
    }
    .configure();
    run_deep_region_test(|| {
        let mut shared = empty_shared_state();
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let prefix_calls = Arc::new(AtomicUsize::new(0));
        let read_calls = Arc::new(AtomicUsize::new(0));
        let prefix_counter = prefix_calls.clone();
        let read_counter = read_calls.clone();
        let data = test_name(2281);
        let address = 0x1000;
        let byte = B64::new(0x5a, 8);
        let copy_bool = |value| Instr::Copy(Loc::Id(RETURN), Exp::Bool(value), info());
        let program = vec![
            Instr::Jump(input(0), 3, info()),
            copy_bool(false),
            Instr::Goto(13),
            Instr::Jump(input(1), 6, info()),
            copy_bool(false),
            Instr::Goto(13),
            Instr::Jump(input(2), 9, info()),
            copy_bool(false),
            Instr::Goto(10),
            copy_bool(true),
            Instr::PrimopReset(
                Loc::Id(data),
                Arc::new(move |_, _, solver| {
                    prefix_counter.fetch_add(1, Ordering::Relaxed);
                    solver.cycle_count();
                    Ok(Val::Unit)
                }),
                primop::Effect::Pure,
                info(),
            ),
            Instr::PrimopVariadic(
                Loc::Id(data),
                primop::variadic_primops()["platform_read_mem"],
                vec![Exp::Unit, Exp::I128(64), Exp::Bits(B64::new(address, 64)), Exp::I128(1)],
                info(),
            ),
            Instr::Copy(
                Loc::Id(RETURN),
                Exp::Call(Op::And, vec![Exp::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(data), Exp::Bits(byte)])]),
                info(),
            ),
            Instr::End,
        ];
        let mut memory = crate::memory::Memory::new();
        memory.add_region(crate::memory::Region::Constrained(
            address..address + 1,
            Arc::new(move |solver| {
                assert_eq!(solver.transaction_depth(), 0, "读取回调只能在普通路径执行");
                read_counter.fetch_add(1, Ordering::Relaxed);
                solver.define_const(crate::primop_util::smt_sbits(byte), info())
            }),
        ));
        let run = |merge| {
            paths_with_state(
                program.clone(),
                &shared,
                3,
                ExecutionLimits::default().with_path_merging(merge),
                memory.clone(),
                |frame| {
                    frame.vars_mut().insert(data, UVal::Init(Val::Unit));
                },
            )
        };
        let ordinary = run(false);
        assert_eq!(prefix_calls.swap(0, Ordering::Relaxed), 2);
        assert_eq!(read_calls.swap(0, Ordering::Relaxed), 2);
        let resumed = run(true);
        assert_eq!(equivalent_paths(&ordinary, &resumed, 3, true), (4, 3));
        assert_eq!(prefix_calls.load(Ordering::Relaxed), 1, "失败分支的已认证前缀不能重跑");
        assert_eq!(read_calls.load(Ordering::Relaxed), 1, "读取回调只能执行一次");
        let done = resumed.iter().find(|path| path.events.iter().any(Event::is_memory_read)).unwrap();
        assert_eq!(done.events.iter().filter(|event| event.is_cycle()).count(), 1);
        assert_eq!(done.events.iter().filter(|event| event.is_memory_read()).count(), 1);
        assert!(done.records.iter().any(|record| record.branch_pc == 6));
        let rejected = shared.execution_stats.arm_unsupported_json(&shared.symtab);
        assert!(rejected["top"].as_array().unwrap().iter().any(|row| {
            row["reason"] == serde_json::json!(SpeculativeRejectReason::StateEffect) && row["target_pc"] == 11
        }));
    });
}

#[test]
fn explicit_exit_and_unfiltered_nonreturning_call_keep_their_terminal_frontier() {
    if !run_in_diagnostics_process(concat!(
        module_path!(),
        "::explicit_exit_and_unfiltered_nonreturning_call_keep_their_terminal_frontier"
    )) {
        return;
    }
    crate::config::RegionOptions {
        defer_exit_check: true,
        partial_commit_prefix: true,
        partial_commit_structure: true,
        partial_commit_control: true,
        ..Default::default()
    }
    .configure();
    run_deep_region_test(|| {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        for call_terminal in [false, true] {
            let mut shared = empty_shared_state();
            shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
            let callee = shared.symtab.intern("zadmission_terminal");
            let exit = Instr::Exit(ExitCause::Explicit, info());
            shared.functions.insert(callee, (vec![], &Ty::Unit, Box::leak(vec![exit.clone()].into_boxed_slice())));
            let visits = Arc::new(AtomicUsize::new(0));
            let prefix_counter = visits.clone();
            let copy_bool = |value| Instr::Copy(Loc::Id(RETURN), Exp::Bool(value), info());
            let program = vec![
                Instr::Jump(input(0), 3, info()),
                copy_bool(false),
                Instr::Goto(9),
                Instr::Jump(input(1), 6, info()),
                copy_bool(false),
                Instr::Goto(7),
                copy_bool(true),
                Instr::PrimopReset(
                    Loc::Id(RETURN),
                    Arc::new(move |_, _, solver| {
                        prefix_counter.fetch_add(1, Ordering::Relaxed);
                        solver.cycle_count();
                        Ok(Val::Unit)
                    }),
                    primop::Effect::Pure,
                    info(),
                ),
                if call_terminal { Instr::Call(Loc::Id(RETURN), false, callee, vec![], info()) } else { exit },
                Instr::End,
            ];
            let run = |merge| {
                let context = Context::new(Config::new());
                let mut solver = Solver::new(&context);
                let mut frame = make_frame(program.clone());
                frame.function_name = TOP_LEVEL_LET;
                for index in 0..2 {
                    let guard = solver.declare_const(smtlib::Ty::Bool, info());
                    frame.vars_mut().insert(test_name(900 + index), UVal::Init(Val::Symbolic(guard)));
                }
                let limits = ExecutionLimits::default().with_path_merging(merge);
                let state = TaskState::new().with_execution_limits(limits);
                let outcomes = Mutex::new((0, 0));
                start_single(
                    frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
                    &shared,
                    &outcomes,
                    &|_, _, result, _, solver, outcomes| match result {
                        Ok((Run::Finished(Val::Bool(false)), _)) => outcomes.lock().unwrap().0 += 1,
                        Ok((Run::Exit, frame)) => {
                            assert_eq!(solver.transaction_depth(), 0);
                            assert_eq!(solver.trace().to_vec().iter().filter(|event| event.is_cycle()).count(), 1);
                            if merge {
                                assert!(frame.region_merge_records.iter().any(|record| record.branch_pc == 3));
                            }
                            outcomes.lock().unwrap().1 += 1;
                        }
                        _ => panic!("夹具必须保留普通返回和显式终止"),
                    },
                );
                outcomes.into_inner().unwrap()
            };
            assert_eq!(run(false), (1, 2));
            assert_eq!(visits.swap(0, Ordering::Relaxed), 2);
            assert_eq!(run(true), (1, 1));
            assert_eq!(visits.load(Ordering::Relaxed), 1, "终止前的已认证汇合不能重跑");
            let reason =
                if call_terminal { SpeculativeRejectReason::RegionEscaped } else { SpeculativeRejectReason::Exit };
            let rejected = shared.execution_stats.arm_unsupported_json(&shared.symtab);
            assert!(rejected["top"]
                .as_array()
                .unwrap()
                .iter()
                .any(|row| { row["reason"] == serde_json::json!(reason) && row["target_pc"] == 8 }));
        }
    });
}
