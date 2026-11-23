//! 从普通任务入口核对两臂执行、事件、合并记录及可达返回值。
use super::*;
use std::collections::BTreeSet;

type Hook = Arc<dyn Fn(&str) -> Result<(), ExecError> + Send + Sync>;

#[derive(Debug, PartialEq, Eq)]
struct Observation {
    records: Vec<String>,
    events: Vec<String>,
    results: BTreeSet<(bool, bool, bool)>,
}

fn diamond(workers: usize, enabled: bool, hook: Option<Hook>) -> (Vec<Observation>, serde_json::Value) {
    diamond_case(workers, enabled, hook, Body::Inline, None)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Body {
    Inline,
    Call,
    Nested,
    Loop,
    ErrorLeaf,
}

fn diamond_case(
    workers: usize,
    enabled: bool,
    hook: Option<Hook>,
    body: Body,
    timeout: Option<u64>,
) -> (Vec<Observation>, serde_json::Value) {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let mut limits = ExecutionLimits::default().with_path_merging(true);
    limits.arms_as_tasks = enabled;
    limits.region_loop_analysis = body == Body::Loop;
    limits.region_global_state = body == Body::Loop;
    let mut state = TaskState::new().with_execution_limits(limits);
    state.arm_test_hook = hook;
    let ctx = Context::new(Config::new());
    let mut solver = Solver::new(&ctx);
    let c = solver.declare_const(smtlib::Ty::Bool, info());
    let x = solver.declare_const(smtlib::Ty::Bool, info());
    let flag = test_name(9010);
    let input = shared.symtab.intern("zarm_input");
    shared.registers.insert(input, Ty::Bool);
    let b_result = Exp::Call(Op::Or, vec![Exp::Id(input), Exp::Id(flag)]);
    let b = if body != Body::Inline {
        let counter = shared.symtab.intern("zscan_index");
        let set = |value| Instr::Copy(Loc::Id(RETURN), value, info());
        let code = match body {
            Body::Call => vec![set(b_result), Instr::End],
            Body::Nested | Body::ErrorLeaf => vec![
                Instr::Jump(Exp::Id(input), 3, info()),
                set(Exp::Id(flag)),
                Instr::Goto(4),
                if body == Body::ErrorLeaf {
                    Instr::PrimopUnary(Loc::Id(RETURN), primop::not_bool::<B64>, Exp::I128(1), info())
                } else {
                    set(b_result)
                },
                Instr::End,
            ],
            Body::Loop => vec![
                Instr::Init(counter, Ty::I64, Exp::I64(0), info()),
                Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(counter), Exp::I64(2)]), 7, info()),
                Instr::Jump(Exp::Id(input), 5, info()),
                Instr::Copy(Loc::Id(counter), Exp::Call(Op::Add, vec![Exp::Id(counter), Exp::I64(1)]), info()),
                Instr::Goto(1),
                set(b_result),
                Instr::Goto(8),
                set(Exp::Id(flag)),
                Instr::End,
            ],
            Body::Inline => unreachable!(),
        };
        let helper = shared.symtab.intern("zlinear_arm");
        shared.functions.insert(helper, (vec![(flag, &Ty::Bool)], &Ty::Bool, Box::leak(code.into_boxed_slice())));
        Instr::Call(Loc::Id(RETURN), false, helper, vec![Exp::Id(flag)], info())
    } else {
        Instr::Copy(Loc::Id(RETURN), b_result, info())
    };
    let mut frame = make_frame(vec![
        Instr::Jump(Exp::Id(flag), 3, info()),
        b,
        Instr::Goto(4),
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Not, vec![Exp::Id(input)]), info()),
        Instr::End,
    ]);
    frame.vars_mut().insert(flag, UVal::Init(Val::Symbolic(c)));
    frame.regs_mut().insert(input, false, UVal::Init(Val::Symbolic(x)));
    let output = Arc::new(Mutex::new(Vec::new()));
    let task = frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver));
    start_multi(workers, timeout, vec![task], &shared, output.clone(), &|_, _, result, _, mut solver, output| {
        let (value, frame) = match result {
            Ok((Run::Finished(value), frame)) => (value, frame),
            Err((ExecError::Type(..), frame)) if body == Body::ErrorLeaf => {
                assert!(frame.arm_error_certified());
                // 单独收集错误叶的输入域，约定其观察值为 true。
                (Val::Bool(true), frame)
            }
            _ => panic!("菱形程序应正常完成或交付已认证的错误叶"),
        };
        let records = frame
            .region_merge_records
            .iter()
            .map(|r| {
                let parent = r
                    .parent_record
                    .map(|id| frame.region_merge_records.iter().position(|p| p.record_id == id).unwrap());
                let values: BTreeSet<_> = r.value_symbols.iter().map(|s| s.as_u32()).collect();
                let inputs: BTreeSet<_> = r.input_symbols.iter().map(|s| s.as_u32()).collect();
                format!(
                    "{parent:?}/{:?}",
                    (
                        r.arm,
                        r.function,
                        r.branch_pc,
                        r.join,
                        r.condition,
                        r.source_loc,
                        r.depth,
                        r.dead,
                        values,
                        inputs,
                        &r.single_arm_reads,
                        &r.memory_reads
                    )
                )
            })
            .collect();
        let events = solver.trace().events_with_guards_rev().map(|(e, g)| format!("{e:?}/{g:?}")).collect();
        let mut results = BTreeSet::new();
        use smtlib::Exp::{And, Bool, Eq, Var};
        for flag in [true, false] {
            for input in [true, false] {
                for ret in [true, false] {
                    let equals = |x, y| Eq(Box::new(x), Box::new(Bool(y)));
                    let args = And(Box::new(equals(Var(c), flag)), Box::new(equals(Var(x), input)));
                    let query = And(Box::new(args), Box::new(equals(smt_value(&value, info()).unwrap(), ret)));
                    if solver.check_sat_with(&query, info()).is_sat().unwrap() {
                        results.insert((flag, input, ret));
                    }
                }
            }
        }
        output.lock().unwrap().push(Observation { records, events, results });
    });
    let observations = std::mem::take(&mut *output.lock().unwrap());
    (observations, shared.execution_stats.merge_json())
}

// 用通道指定先后关系，超时即测试失败。
fn ordered(
    workers: usize,
    first: &'static str,
    second: &'static str,
    fail: &'static str,
) -> (Vec<Observation>, Vec<(String, std::thread::ThreadId)>, serde_json::Value) {
    let log = Arc::new(Mutex::new(Vec::new()));
    let (tx, rx) = std::sync::mpsc::sync_channel(1);
    let (claimed, ready) = std::sync::mpsc::sync_channel(1);
    let ready = Mutex::new(ready);
    let rx = Mutex::new(rx);
    let entries = log.clone();
    let hook = Arc::new(move |point: &str| {
        entries.lock().unwrap().push((point.to_owned(), std::thread::current().id()));
        if point == "worker_claimed" {
            claimed.send(()).unwrap();
        }
        if point == "a_join" && first == "waiting" {
            ready.lock().unwrap().recv_timeout(Duration::from_secs(10)).unwrap();
        }
        if point == first {
            tx.send(()).unwrap();
        }
        if point == second {
            rx.lock().unwrap().recv_timeout(Duration::from_secs(10)).unwrap();
        }
        if point == "context" {
            match fail {
                "error" => return Err(ExecError::Type("B 臂执行失败".into(), info())),
                "timeout" => std::thread::sleep(Duration::from_millis(1100)),
                "cancel" => return Err(ExecError::Stopped("取消远端臂".into())),
                _ => (),
            }
        }
        Ok(())
    });
    let (data, stats) = diamond_case(
        workers,
        true,
        Some(hook),
        match fail {
            "call" => Body::Call,
            "nested" => Body::Nested,
            "loop" => Body::Loop,
            "error_leaf" => Body::ErrorLeaf,
            _ => Body::Inline,
        },
        (fail == "timeout").then_some(1),
    );
    let entries = std::mem::take(&mut *log.lock().unwrap());
    (data, entries, stats)
}

#[test]
fn region_arm_normal_arrivals() {
    let (base, _) = diamond(1, false, None);
    let (out, _, _) = ordered(2, "worker_claimed", "a_join", "");
    assert_eq!(base, out);
    assert_eq!(out.len(), 1);
    assert_eq!(out[0].records.len(), 1);
    assert_eq!(out[0].events.iter().filter(|e| e.contains("ReadReg")).count(), 1);
    assert_eq!(
        out[0].results,
        [(true, true, false), (true, false, true), (false, true, true), (false, false, false)].into_iter().collect()
    );
}

#[test]
fn region_arm_queued_reclaimed() {
    let (out, log, _) = ordered(2, "reclaimed", "before_claim", "");
    assert_eq!(out, diamond(1, false, None).0);
    assert!(log.iter().any(|(s, _)| s == "reclaimed"));
    assert!(log.iter().all(|(s, _)| !matches!(s.as_str(), "worker_claimed" | "context" | "imported")));
}

#[test]
fn region_arm_worker_claims_a_imports() {
    let (_, log, stats) = ordered(2, "worker_claimed", "a_join", "");
    let thread = |name| log.iter().find(|(s, _)| s == name).unwrap().1;
    assert_ne!(thread("context"), thread("a_join"));
    assert_eq!(thread("a_join"), thread("imported"));
    assert_eq!(log.iter().filter(|(s, _)| s == "imported").count(), 1);
    assert_eq!(stats["runtime"]["submitted_tasks"], 1);
    assert_eq!(stats["runtime"]["completed_tasks"], 1);
}

#[test]
fn region_arm_arrival_orders() {
    let (a, first, _) = ordered(2, "delivered", "a_join", "");
    let (b, second, _) = ordered(2, "waiting", "before_delivery", "");
    assert!(first.iter().any(|(s, _)| s == "imported") && second.iter().any(|(s, _)| s == "waiting"));
    assert_eq!(a, b);
}

#[test]
fn region_arm_fresh_symbols() {
    let (base, _) = diamond(1, false, None);
    let (out, log, _) = ordered(2, "worker_claimed", "a_join", "");
    assert!(log.iter().any(|(s, _)| s == "imported"));
    assert_eq!(out, base);
    assert!(out[0].events.iter().filter(|e| e.contains("DefineConst")).count() >= 3);
}

#[test]
fn region_arm_worker_counts() {
    let (base, _) = diamond(1, false, None);
    for workers in [1, 2, 4] {
        for _ in 0..3 {
            assert_eq!(diamond(workers, true, None).0, base);
        }
    }
}

#[test]
fn region_arm_worker_failures() {
    for failure in ["timeout", "error", "cancel"] {
        let (out, log, stats) = ordered(2, "worker_claimed", "a_join", failure);
        assert!(log.iter().any(|(s, _)| s == "failed"));
        assert!(log.iter().all(|(s, _)| s != "imported"));
        assert_eq!(stats["runtime"]["submitted_tasks"], stats["runtime"]["completed_tasks"]);
        if failure == "timeout" {
            assert_eq!(stats["failure_reasons"]["path_timeout"], 1);
        }
        assert_eq!(out.len(), 2);
        assert_eq!(
            out.into_iter().flat_map(|o| o.results).collect::<BTreeSet<_>>(),
            diamond(1, false, None).0[0].results
        );
    }
}

#[test]
fn region_arm_rejects_suspended_frame_before_clone() {
    let mut frame = make_frame(vec![Instr::End]);
    frame.region_arrivals.push(make_frame(vec![Instr::End]));
    assert!(!region_arm::transferable_entry(&frame));
    let ctx = Context::new(Config::new());
    let mut solver = Solver::new(&ctx);
    let flag = solver.declare_const(smtlib::Ty::Bool, info());
    let mut limits = ExecutionLimits::default().with_path_merging(true);
    limits.arms_as_tasks = true;
    let state = TaskState::new().with_execution_limits(limits);
    let queue = Worker::new_lifo();
    let result = region_merge::try_region(
        flag,
        0,
        0,
        TaskId::fresh(),
        &mut Fraction::one(),
        PathTimeout::unlimited(),
        None,
        &SingleForkSink { queue: &queue },
        &mut frame,
        &state,
        &empty_shared_state(),
        &mut solver,
        info(),
    );
    assert!(matches!(result, Ok(region_merge::RegionResult::Suspended)));
    assert_eq!(frame.region_arrivals.len(), 1);
    assert_eq!(solver.transaction_depth(), 0);
}

#[test]
fn region_arm_cancel_wakes_waiter_and_discards_late_arrival() {
    let cell = region_arm::JoinCell::<()>::new();
    assert!(cell.try_claim());
    std::thread::scope(|scope| {
        let waiter = scope.spawn(|| cell.take());
        cell.cancel(ExecError::Stopped("A 已退出".into()));
        assert!(matches!(waiter.join().unwrap(), Err(ExecError::Stopped(_))));
        cell.deliver(Ok(()));
    });
    assert_eq!(cell.state(), region_arm::ArmJobState::Cancelled);
}

#[test]
fn region_arm_function_application_remaps_function_and_argument() {
    let f = Sym::from_u32(3);
    let x = Sym::from_u32(4);
    let remap = crate::smt::SymRemap::from_pairs([(f, x), (x, Sym::from_u32(5))]);
    let actual = remap.exp(&smtlib::Exp::App(f, vec![smtlib::Exp::Var(x)]));
    assert_eq!(actual, smtlib::Exp::App(x, vec![smtlib::Exp::Var(Sym::from_u32(5))]));
}

#[test]
fn region_arm_imports_straight_line_call_and_register_read() {
    let base = diamond_case(1, false, None, Body::Call, None).0;
    let (out, log, _) = ordered(2, "worker_claimed", "a_join", "call");
    assert!(log.iter().any(|(s, _)| s == "imported"));
    assert_eq!(out, base);
}

#[test]
fn region_arm_wait_excludes_queue_time_and_retains_longer_arm() {
    use super::path_timing::{PathTimeTotals, PathTiming};
    let timing = PathTiming::default();
    let at = Instant::now();
    let ms = Duration::from_millis;
    timing.start_active_at(at, ms(0));
    timing.pause_active_at(at + ms(5), ms(2));
    timing.include_parallel(PathTimeTotals { active_wall: ms(8), executor_cpu: ms(7) });
    timing.start_active_at(at + ms(1000), ms(2));
    let end = timing.snapshot_at(at + ms(1001), ms(3));
    assert_eq!((end.active_wall, end.executor_cpu), (ms(9), ms(8)));
}

/// 真正的寄存器向量读取在 A 产生一项义务，在 B 连续产生两项。
/// 只放宽 B 的下标时，出口必须仍看见第一项可能越界的读取。
#[test]
fn region_arm_imports_deferred_register_indices() {
    check_deferred_indices(false, "region_arm_imports_deferred_register_indices");
}

#[test]
fn region_arm_nested_deferred_indices() {
    check_deferred_indices(true, "region_arm_nested_deferred_indices");
}

fn check_deferred_indices(nested: bool, name: &str) {
    const CHILD: &str = "ISLA_ARM_INDEX_OBLIGATION_TEST";
    if std::env::var_os(CHILD).is_none() {
        let test = format!("executor::tests::region_arm_runtime_tests::{name}");
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", &test, "--nocapture"])
            .env(CHILD, "1")
            .output()
            .unwrap();
        let log = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{log}");
        let checks: Vec<_> = log
            .lines()
            .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
            .filter(|row| row["kind"] == "region_assert_obligation_check")
            .map(|row| (row["obligations"].as_u64().unwrap(), row["result"].as_str().unwrap().to_owned()))
            .collect();
        assert_eq!(checks, ["Unsat", "Unsat", "Sat", "Sat"].map(|result| (3, result.to_owned())));
        return;
    }
    crate::config::RegionOptions { defer_exit_check: true, ..Default::default() }.configure();
    struct TestSink;
    impl<'ir, 'task> ForkSink<'ir, 'task, B64> for TestSink {
        fn submit(&self, _: Task<'ir, 'task, B64>) {
            panic!("本区域只有一个汇合点");
        }
        fn reserve_arm_thread(&self) -> Option<region_arm::ThreadSlot<'_>> {
            Some(region_arm::ThreadSlot { tid: 1, release: Some(Box::new(|| ())) })
        }
    }
    let execute = |parallel, safe| {
        let mut shared = empty_shared_state();
        let flag = test_name(9010);
        let index_a = test_name(9011);
        let index_b = test_name(9012);
        let refs = test_name(9013);
        let regs = [shared.symtab.intern("zarm_r0"), shared.symtab.intern("zarm_r1")];
        let read = |index| {
            Instr::Call(Loc::Id(RETURN), false, READ_REGISTER_FROM_VECTOR, vec![Exp::Id(index), Exp::Id(refs)], info())
        };
        let inner = test_name(9014);
        let mut code = if nested {
            vec![Instr::Jump(Exp::Id(inner), 4, info()), read(index_b), Instr::Goto(5), read(index_b)]
        } else {
            vec![read(index_b), read(index_b)]
        };
        let target = code.len() + 2;
        code.insert(0, Instr::Jump(Exp::Id(flag), target, info()));
        code.extend([Instr::Goto(target + 1), read(index_a), Instr::End]);
        let mut frame = make_frame(code);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::new(&ctx);
        let guard = solver.declare_const(smtlib::Ty::Bool, info());
        frame.vars_mut().insert(flag, UVal::Init(Val::Symbolic(guard)));
        if nested {
            let choice = solver.declare_const(smtlib::Ty::Bool, info());
            frame.vars_mut().insert(inner, UVal::Init(Val::Symbolic(choice)));
        }
        for (name, bounded) in [(index_a, true), (index_b, safe)] {
            let index = solver.declare_bitvector(2, info());
            if bounded {
                solver.assert(smtlib::Exp::Bvult(Box::new(smtlib::Exp::Var(index)), Box::new(smtlib::bits64(2, 2))));
            }
            frame.vars_mut().insert(name, UVal::Init(Val::Symbolic(index)));
        }
        for (n, reg) in regs.into_iter().enumerate() {
            shared.registers.insert(reg, Ty::Bits(8));
            frame.regs_mut().insert(reg, false, UVal::Init(Val::Bits(B64::new(n as u64, 8))));
        }
        frame.lets_mut().insert(refs, UVal::Init(Val::Vector(regs.into_iter().map(Val::Ref).collect())));
        let mut limits = ExecutionLimits::default().with_path_merging(true);
        limits.arms_as_tasks = parallel;
        let mut state = TaskState::new().with_execution_limits(limits);
        let (tx, rx) = std::sync::mpsc::channel();
        let rx = Mutex::new(rx);
        let imported = Arc::new(AtomicUsize::new(0));
        let count = imported.clone();
        state.arm_test_hook = Some(Arc::new(move |point| {
            match point {
                "worker_claimed" => tx.send(()).unwrap(),
                "a_join" => rx.lock().unwrap().recv_timeout(Duration::from_secs(10)).unwrap(),
                "imported" => {
                    count.fetch_add(1, Ordering::Relaxed);
                }
                _ => (),
            }
            Ok(())
        }));
        frame.path_timing.start_active();
        let result = region_merge::try_region(
            guard,
            target,
            0,
            TaskId::fresh(),
            &mut Fraction::one(),
            PathTimeout::unlimited(),
            None,
            &TestSink,
            &mut frame,
            &state,
            &shared,
            &mut solver,
            info(),
        )
        .unwrap();
        assert_eq!(matches!(result, region_merge::RegionResult::Merged), safe);
        assert_eq!(frame.region_replay.is_some(), !safe, "越界时应按符号断言拒绝");
        assert_eq!(imported.load(Ordering::Relaxed), usize::from(parallel), "B 必须被 A 实际导入");
        solver
            .trace()
            .events_with_guards_rev()
            .filter(|(e, _)| matches!(e, Event::Smt(..)))
            .map(|(e, g)| format!("{e:?}/{g:?}"))
            .collect::<Vec<_>>()
    };
    for safe in [true, false] {
        assert_eq!(execute(false, safe), execute(true, safe), "逐项比较义务定义及其守卫");
    }
}

fn check_nested_b(body: Body, label: &'static str) {
    let baseline = diamond_case(1, false, None, body, None).0;
    assert_eq!(baseline.len(), 1);
    assert!(baseline[0].records.len() >= 2, "基准必须执行内层汇合");
    assert_eq!(
        baseline[0].results,
        [(true, true, false), (true, false, true), (false, true, true), (false, false, false)].into_iter().collect()
    );
    assert_eq!(diamond_case(1, true, None, body, None).0, baseline);
    for workers in [2, 4] {
        let (observed, log, _) = ordered(workers, "worker_claimed", "a_join", label);
        assert_eq!(log.iter().filter(|(point, _)| point == "imported").count(), 1, "B 必须在外层出口交付一次");
        assert_eq!(observed, baseline);
    }
}

#[test]
fn region_arm_nested_two_arms() {
    check_nested_b(Body::Nested, "nested");
}

#[test]
fn region_arm_nested_foreach_early_exit() {
    check_nested_b(Body::Loop, "loop");
}

#[test]
fn region_arm_nested_error_leaf_replays_once() {
    const CHILD: &str = "ISLA_NESTED_ARM_ERROR_LEAF";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "executor::tests::region_arm_runtime_tests::region_arm_nested_error_leaf_replays_once"])
            .env(CHILD, "1")
            .output()
            .unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stdout));
        return;
    }
    crate::config::RegionOptions { arm_error_leaf: true, defer_exit_check: true, ..Default::default() }.configure();
    let mut baseline = diamond_case(1, false, None, Body::ErrorLeaf, None).0;
    let (mut output, log, _) = ordered(2, "worker_claimed", "a_join", "error_leaf");
    assert_eq!(log.iter().filter(|(point, _)| point == "serial_retry").count(), 1);
    assert!(!log.iter().any(|(point, _)| point == "imported"));
    assert_eq!(output.len(), 2, "串行重跑须各交付一次正常终态和错误叶");
    baseline.sort_by_key(|o| o.results.len());
    output.sort_by_key(|o| o.results.len());
    assert_eq!(output[0].results, BTreeSet::from([(false, true, true)]));
    assert_eq!(baseline, output);
}

#[test]
fn region_arm_nested_loop_observes_cancellation_and_path_deadline() {
    use crate::ir::regions::{Region, RegionKind, RegionPoint};
    let frame = make_frame(vec![Instr::Goto(1), Instr::End]);
    let region = Arc::new(Region {
        branch_pc: 0,
        has_back_edge: false,
        join: RegionPoint::Instruction(1),
        nodes: [0].into_iter().collect(),
        kind: RegionKind::Reconvergent,
        local_variables: Default::default(),
    });
    let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(true));
    let mode = crate::config::MergeMode::Adaptive;
    let mut outer = region_merge::prepare_region_base(&frame, &region, 1, mode, &state, info());
    let cancel = Arc::new(AtomicBool::new(false));
    outer.region_execution.as_mut().unwrap().remote_cancel = Some(cancel.clone());
    outer.path_timing = path_timing::PathTiming::from_totals(path_timing::PathTimeTotals {
        active_wall: Duration::from_secs(1),
        ..Default::default()
    });
    let loop_region = Arc::new(Region { has_back_edge: true, ..(*region).clone() });
    let mut nested = region_merge::prepare_region_base(&outer, &loop_region, 2, mode, &state, info());
    cancel.store(true, Ordering::Release);
    assert!(matches!(
        region_merge::step(&mut nested),
        Err(ExecError::SpeculativeReject { reason: SpeculativeRejectReason::IncompatibleState, .. })
    ));
    cancel.store(false, Ordering::Release);
    let context = Context::new(Config::new());
    let result = run_loop(
        1,
        TaskId::fresh(),
        &mut Fraction::one(),
        PathTimeout::from_seconds(Some(1)),
        None,
        &SingleForkSink { queue: &Worker::new_lifo() },
        &mut nested,
        &state,
        &empty_shared_state(),
        &mut Solver::new(&context),
    );
    assert!(matches!(result, Err(ExecError::Timeout)));
}
