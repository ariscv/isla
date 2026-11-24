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
    NestedAssert,
    ThreeLevels,
    ThreeLevelsAssert,
    Large,
    OrderedReads,
    Loop,
    ErrorLeaf,
    ErrorInB,
}

fn diamond_case(
    workers: usize,
    enabled: bool,
    hook: Option<Hook>,
    body: Body,
    timeout: Option<u64>,
) -> (Vec<Observation>, serde_json::Value) {
    diamond_case_with_gate(workers, enabled, hook, body, timeout, false)
}

fn diamond_case_with_gate(
    workers: usize,
    enabled: bool,
    hook: Option<Hook>,
    body: Body,
    timeout: Option<u64>,
    default_gate: bool,
) -> (Vec<Observation>, serde_json::Value) {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let mut limits = ExecutionLimits::default().with_path_merging(true);
    limits.arms_as_tasks = enabled;
    if !default_gate {
        limits.parallel.min_arm_instructions = 0;
    }
    limits.ordered_events = body == Body::OrderedReads;
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
    let third = test_name(9015);
    let b_result = Exp::Call(Op::Or, vec![Exp::Id(input), Exp::Id(flag)]);
    let b = if body != Body::Inline {
        let counter = shared.symtab.intern("zscan_index");
        let set = |value| Instr::Copy(Loc::Id(RETURN), value, info());
        let scratch = test_name(9016);
        let not_flag = || Exp::Call(Op::Not, vec![Exp::Id(flag)]);
        let assume = || Instr::PrimopUnary(Loc::Id(scratch), primop::assume::<B64>, not_flag(), info());
        let assertion = || {
            Instr::PrimopBinary(
                Loc::Id(scratch),
                primop::optimistic_assert::<B64>,
                not_flag(),
                Exp::String("nested assertion".into()),
                info(),
            )
        };
        let code = match body {
            Body::Call => vec![set(b_result), Instr::End],
            Body::Large => {
                let mut code = vec![set(b_result); 96];
                code.push(Instr::End);
                code
            }
            Body::Nested | Body::ErrorLeaf | Body::ErrorInB => vec![
                Instr::Jump(Exp::Id(input), 3, info()),
                if body == Body::ErrorInB {
                    Instr::PrimopUnary(Loc::Id(RETURN), primop::not_bool::<B64>, Exp::I128(1), info())
                } else {
                    set(Exp::Id(flag))
                },
                Instr::Goto(4),
                if body == Body::ErrorLeaf {
                    Instr::PrimopUnary(Loc::Id(RETURN), primop::not_bool::<B64>, Exp::I128(1), info())
                } else {
                    set(b_result)
                },
                Instr::End,
            ],
            Body::NestedAssert => vec![
                Instr::Jump(Exp::Id(input), 5, info()),
                assume(),
                assertion(),
                set(Exp::Id(flag)),
                Instr::Goto(8),
                assume(),
                assertion(),
                set(b_result),
                Instr::End,
            ],
            Body::ThreeLevelsAssert => vec![
                Instr::Jump(Exp::Id(input), 12, info()),
                assume(),
                Instr::Jump(Exp::Id(third), 7, info()),
                assume(),
                assertion(),
                set(Exp::Id(flag)),
                Instr::Goto(10),
                assume(),
                assertion(),
                set(Exp::Id(third)),
                assertion(),
                Instr::Goto(15),
                assume(),
                assertion(),
                set(b_result),
                Instr::End,
            ],
            Body::ThreeLevels => vec![
                Instr::Jump(Exp::Id(input), 6, info()),
                Instr::Jump(Exp::Id(third), 4, info()),
                set(Exp::Id(flag)),
                Instr::Goto(5),
                set(Exp::Id(third)),
                Instr::Goto(7),
                set(b_result),
                Instr::End,
            ],
            Body::OrderedReads => vec![
                Instr::Jump(Exp::Id(input), 4, info()),
                set(Exp::Id(input)),
                set(Exp::Id(flag)),
                Instr::Goto(6),
                set(Exp::Id(input)),
                set(b_result),
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
        shared.functions.insert(
            helper,
            (vec![(flag, &Ty::Bool), (scratch, &Ty::Unit)], &Ty::Bool, Box::leak(code.into_boxed_slice())),
        );
        Instr::Call(Loc::Id(RETURN), false, helper, vec![Exp::Id(flag), Exp::Unit], info())
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
    let third_sym = matches!(body, Body::ThreeLevels | Body::ThreeLevelsAssert)
        .then(|| solver.declare_const(smtlib::Ty::Bool, info()));
    if let Some(choice) = third_sym {
        frame.lets_mut().insert(third, UVal::Init(Val::Symbolic(choice)));
    }
    frame.vars_mut().insert(flag, UVal::Init(Val::Symbolic(c)));
    frame.regs_mut().insert(input, false, UVal::Init(Val::Symbolic(x)));
    let output = Arc::new(Mutex::new(Vec::new()));
    let task = frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver));
    start_multi(workers, timeout, vec![task], &shared, output.clone(), &|_, _, result, _, mut solver, output| {
        let (value, frame) = match result {
            Ok((Run::Finished(value), frame)) => (value, frame),
            Err((ExecError::Type(..), frame)) if matches!(body, Body::ErrorLeaf | Body::ErrorInB) => {
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
                        r.outcome,
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
                    if let Some(choice) = third_sym {
                        for third in [false, true] {
                            let with_choice = And(Box::new(query.clone()), Box::new(equals(Var(choice), third)));
                            let expected = if flag { !input } else { input || third };
                            assert_eq!(solver.check_sat_with(&with_choice, info()).is_sat().unwrap(), ret == expected);
                        }
                    }
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

fn wait_for_arm_claim() -> impl Fn(&str) {
    let cells = (Mutex::new(HashSet::new()), std::sync::Condvar::new());
    move |point| {
        if let Some(id) = point.strip_prefix("claim/") {
            cells.0.lock().unwrap().insert(id.to_owned());
            cells.1.notify_all();
        } else if let Some(id) = point.strip_prefix("join/") {
            let (mut claims, _) = cells
                .1
                .wait_timeout_while(cells.0.lock().unwrap(), Duration::from_secs(5), |claims| !claims.contains(id))
                .unwrap();
            assert!(claims.remove(id), "B 未认领 {id}");
        }
    }
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
    let (claimed, ready) = std::sync::mpsc::channel();
    let ready = Mutex::new(ready);
    let rx = Mutex::new(rx);
    let observe_claim = wait_for_arm_claim();
    let entries = log.clone();
    let hook = Arc::new(move |point: &str| {
        if first == "worker_claimed" && second == "a_join" {
            observe_claim(point);
        }
        entries.lock().unwrap().push((point.to_owned(), std::thread::current().id()));
        if point == "worker_claimed" {
            claimed.send(()).unwrap();
        }
        if point == "a_join" && first == "waiting" {
            ready.lock().unwrap().recv_timeout(Duration::from_secs(10)).unwrap();
        }
        if point == first && first != "worker_claimed" {
            tx.send(()).unwrap();
        }
        if point == second && first != "worker_claimed" {
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
            "nested_assert" => Body::NestedAssert,
            "loop" => Body::Loop,
            "three" => Body::ThreeLevels,
            "three_assert" => Body::ThreeLevelsAssert,
            "ordered_reads" => Body::OrderedReads,
            "error_leaf" => Body::ErrorLeaf,
            "error_in_b" => Body::ErrorInB,
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
            assert_eq!(stats["failure_reasons"]["SpeculativeRejectReason::PathTimeout"], 1);
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
    struct TestSink<'ir>(region_arm::ArmQueue<'ir, B64>);
    impl region_arm::ArmThreads for TestSink<'_> {
        fn reserve(&self) -> Option<region_arm::ThreadSlot<'_>> {
            Some(region_arm::ThreadSlot { tid: 1, release: Some(Box::new(|| ())) })
        }
    }
    impl<'ir, 'task> ForkSink<'ir, 'task, B64> for TestSink<'ir> {
        fn submit(&self, _: Task<'ir, 'task, B64>) {
            panic!("本区域只有一个汇合点");
        }
        fn arm_scheduler(&self) -> Option<region_arm::Scheduler<'_, 'ir, B64>> {
            Some(region_arm::Scheduler { threads: self, queue: &self.0 })
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
        limits.parallel.min_arm_instructions = 0;
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
            &TestSink(region_arm::ArmQueue::new()),
            &mut frame,
            &state,
            &shared,
            &mut solver,
            info(),
        )
        .unwrap();
        assert_eq!(matches!(result, region_merge::RegionResult::Merged), safe);
        assert_eq!(frame.region_replay.is_some(), !safe, "越界时应按符号断言拒绝");
        assert_eq!(
            imported.load(Ordering::Relaxed),
            usize::from(parallel) * (1 + usize::from(nested)),
            "B 必须被 A 实际导入"
        );
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
    let (baseline, stats) = diamond_case(1, false, None, body, None);
    assert_eq!(baseline.len(), 1, "{stats}");
    assert!(baseline[0].records.len() >= 2, "基准必须执行内层汇合");
    let mut expected =
        BTreeSet::from([(true, true, false), (true, false, true), (false, true, true), (false, false, false)]);
    if matches!(body, Body::ThreeLevels | Body::ThreeLevelsAssert) {
        expected.insert((false, false, true));
    }
    assert_eq!(baseline[0].results, expected);
    let exhausted = Arc::new(AtomicUsize::new(0));
    let denied = exhausted.clone();
    let single = Arc::new(move |point: &str| {
        if point == "no_slot" {
            denied.fetch_add(1, Ordering::Relaxed);
        }
        assert_ne!(point, "context", "没有线程名额时必须留在当前 Solver");
        Ok(())
    });
    assert_eq!(diamond_case(1, true, Some(single), body, None).0, baseline);
    assert!(exhausted.load(Ordering::Relaxed) > 0);
    assert_eq!(diamond_case(2, true, None, body, None).0, baseline);
    let (observed, log, _) = ordered(4, "worker_claimed", "a_join", label);
    let imports = log.iter().filter(|(point, _)| point == "imported").count();
    let minimum = match body {
        Body::ThreeLevels | Body::ThreeLevelsAssert => 3,
        Body::Nested | Body::NestedAssert => 2,
        _ => 1,
    };
    assert!(imports >= minimum, "{imports} 次导入");
    assert_eq!(observed, baseline);
}

#[test]
fn region_arm_nested_two_arms() {
    check_nested_b(Body::Nested, "nested");
}

#[test]
fn region_arm_nested_imports_guarded_assertions() {
    const CHILD: &str = "ISLA_STAGE4_NESTED_ASSERT";
    let Some(mode) = std::env::var_os(CHILD) else {
        for mode in ["existing", "choice_dag_and_coi"] {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "executor::tests::region_arm_runtime_tests::region_arm_nested_imports_guarded_assertions",
                ])
                .env(CHILD, mode)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{mode}: {}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }
        return;
    };
    if mode == "choice_dag_and_coi" {
        crate::smt::configure_solver_options(crate::smt::SolverOptions {
            incremental_choice_dag: true,
            coi_query_slicing: true,
            ..Default::default()
        });
    }
    crate::config::RegionOptions { defer_exit_check: true, ..Default::default() }.configure();
    check_nested_b(Body::NestedAssert, "nested_assert");
    check_nested_b(Body::ThreeLevelsAssert, "three_assert");
}

#[test]
fn region_arm_nested_preserves_repeated_register_reads() {
    let mut baseline = diamond_case(4, false, None, Body::OrderedReads, None).0;
    let (mut out, log, _) = ordered(4, "worker_claimed", "a_join", "ordered_reads");
    // 多个 worker 可按任意顺序交付终态。按可达输入输出对齐路径，保留每条路径内的事件顺序。
    baseline.sort_by(|a, b| a.results.cmp(&b.results));
    out.sort_by(|a, b| a.results.cmp(&b.results));
    assert_eq!(out, baseline);
    assert!(out.iter().any(|o| o.events.iter().filter(|e| e.contains("ReadReg")).count() > 1));
    assert_eq!(log.iter().filter(|(p, _)| p == "imported").count(), 2);
}

#[test]
fn region_arm_nested_three_levels() {
    check_nested_b(Body::ThreeLevels, "three");
}

#[test]
fn region_arm_nested_foreach_early_exit() {
    check_nested_b(Body::Loop, "loop");
}

#[test]
fn region_arm_nested_error_leaf_delivered_once() {
    const CHILD: &str = "ISLA_NESTED_ARM_ERROR_LEAF";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "executor::tests::region_arm_runtime_tests::region_arm_nested_error_leaf_delivered_once"])
            .env(CHILD, "1")
            .output()
            .unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stdout));
        return;
    }
    crate::config::RegionOptions { arm_error_leaf: true, defer_exit_check: true, ..Default::default() }.configure();
    let mut baseline = diamond_case(1, false, None, Body::ErrorLeaf, None).0;
    let (mut output, log, _) = ordered(2, "worker_claimed", "a_join", "error_leaf");
    assert_eq!(log.iter().filter(|(p, _)| p == "imported_error").count(), 1, "{log:?}");
    assert!(log.iter().any(|(point, _)| point == "imported"));
    assert_eq!(output.len(), 2, "须各交付一次正常终态和错误叶");
    baseline.sort_by_key(|o| o.results.len());
    output.sort_by_key(|o| o.results.len());
    assert_eq!(output[0].results, BTreeSet::from([(false, true, true)]));
    assert_eq!(baseline, output);
    let mut expected = diamond_case(4, false, None, Body::ErrorInB, None).0;
    let (mut output, log, _) = ordered(4, "worker_claimed", "a_join", "error_in_b");
    assert_eq!(log.iter().filter(|(p, _)| p == "imported_error").count(), 2, "错误叶须穿过内外两个出口");
    expected.sort_by_key(|o| o.results.len());
    output.sort_by_key(|o| o.results.len());
    assert_eq!(expected, output);
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
    outer.region_execution.as_mut().unwrap().remote_cancel = Some(region_arm::Cancellation::new(cancel.clone(), None));
    outer.path_timing = path_timing::PathTiming::from_totals(path_timing::PathTimeTotals {
        active_wall: Duration::from_secs(1),
        ..Default::default()
    });
    let loop_region = Arc::new(Region { has_back_edge: true, ..(*region).clone() });
    let mut nested = region_merge::prepare_region_base(&outer, &loop_region, 2, mode, &state, info());
    let execution = nested.region_execution.as_mut().unwrap();
    execution.remote_cancel =
        Some(region_arm::Cancellation::new(Arc::new(AtomicBool::new(false)), execution.remote_cancel.take()));
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

#[test]
fn region_arm_waiter_runs_nested_b_without_another_thread() {
    let (idle, wait_idle) = std::sync::mpsc::channel();
    let (claimed, wait_claim) = std::sync::mpsc::channel();
    let wait_idle = Mutex::new(wait_idle);
    let wait_claim = Mutex::new(wait_claim);
    let threads = Arc::new(Mutex::new(Vec::new()));
    let trace = threads.clone();
    let first = AtomicBool::new(true);
    let hook = Arc::new(move |point: &str| {
        let thread = std::thread::current().id();
        trace.lock().unwrap().push((point.to_owned(), thread));
        match point {
            "worker_claimed" => claimed.send(()).unwrap(),
            "context" if first.swap(false, Ordering::Relaxed) => {
                wait_idle.lock().unwrap().recv_timeout(Duration::from_secs(5)).unwrap();
            }
            "a_join" => wait_claim.lock().unwrap().recv_timeout(Duration::from_secs(5)).unwrap(),
            "idle_helper" => idle.send(()).unwrap(),
            _ => (),
        }
        Ok(())
    });
    let observed = diamond_case(2, true, Some(hook), Body::Nested, None).0;
    assert_eq!(observed, diamond_case(2, false, None, Body::Nested, None).0);
    let log = threads.lock().unwrap();
    let root = log.iter().find(|(p, _)| p == "a_join").unwrap().1;
    let helpers: Vec<_> = log.iter().filter(|(p, _)| p == "helping").map(|(_, id)| *id).collect();
    assert_eq!(helpers, [root]);
    assert_eq!(log.iter().filter(|(p, _)| p == "imported").count(), 2);
}

#[test]
fn region_arm_nested_worker_panic_wakes_parent() {
    let count = Arc::new(AtomicUsize::new(0));
    let contexts = count.clone();
    let observe_claim = wait_for_arm_claim();
    let hook = Arc::new(move |point: &str| {
        observe_claim(point);
        if point == "context" && contexts.fetch_add(1, Ordering::Relaxed) == 1 {
            panic!("内层 B 注入 panic");
        }
        Ok(())
    });
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        diamond_case(4, true, Some(hook), Body::Nested, None)
    }));
    assert!(count.load(Ordering::Relaxed) >= 2, "必须由内层 B 触发");
    assert!(result.is_err(), "作用域必须把 worker panic 传播到运行入口");
}

#[test]
#[ignore = "比较同线程数的真实菱形程序墙钟"]
fn region_arm_nested_wall_time() {
    for (name, body) in [("two", Body::Nested), ("three", Body::ThreeLevels)] {
        let baseline = diamond_case_with_gate(4, false, None, body, None, true).0;
        assert_eq!(baseline.len(), 1);
        eprintln!(
            "fixture {name} records={} events={} reads={}",
            baseline[0].records.len(),
            baseline[0].events.len(),
            baseline[0].events.iter().filter(|event| event.contains("ReadReg")).count()
        );
        for round in 0..9 {
            let order = if round % 2 == 0 { [false, true] } else { [true, false] };
            for parallel in order {
                let imported = Arc::new(AtomicUsize::new(0));
                let count = imported.clone();
                let hook = Arc::new(move |point: &str| {
                    if point == "imported" {
                        count.fetch_add(1, Ordering::Relaxed);
                    }
                    Ok(())
                });
                let now = Instant::now();
                let observed = diamond_case_with_gate(4, parallel, Some(hook), body, None, true).0;
                let elapsed = now.elapsed().as_micros();
                assert_eq!(observed, baseline);
                eprintln!("diamond {name} {round} {parallel} {elapsed} {}", imported.load(Ordering::Relaxed));
            }
        }
    }
}

#[test]
fn region_arm_default_gate_skips_small_and_schedules_large() {
    for (body, expected) in [(Body::Nested, 0), (Body::ThreeLevels, 0), (Body::Large, 1)] {
        let imports = Arc::new(AtomicUsize::new(0));
        let count = imports.clone();
        let observe_claim = wait_for_arm_claim();
        let hook = Arc::new(move |point: &str| {
            observe_claim(point);
            if point == "imported" {
                count.fetch_add(1, Ordering::Relaxed);
            }
            Ok(())
        });
        let parallel = diamond_case_with_gate(4, true, Some(hook), body, None, true).0;
        assert_eq!(parallel, diamond_case_with_gate(4, false, None, body, None, true).0);
        assert_eq!(imports.load(Ordering::Relaxed), expected);
    }
}

/// 用同一根的失败点交付，覆盖认证为真及被丢弃的叶，并保留实际发布次序。
#[test]
fn region_arm_error_certification_preserves_leaf_order() {
    const CHILD: &str = "ISLA_STAGE4_CERTIFICATION";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "executor::tests::region_arm_runtime_tests::region_arm_error_certification_preserves_leaf_order",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        return;
    }
    crate::smt::configure_tastic(crate::smt::Tactic::Default);

    struct Sink<'ir, 'task> {
        queue: region_arm::ArmQueue<'ir, B64>,
        slots: AtomicUsize,
        leaves: Mutex<Vec<Task<'ir, 'task, B64>>>,
    }
    impl region_arm::ArmThreads for Sink<'_, '_> {
        fn reserve(&self) -> Option<region_arm::ThreadSlot<'_>> {
            self.slots.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |free| free.checked_sub(1)).ok()?;
            Some(region_arm::ThreadSlot {
                tid: 1,
                release: Some(Box::new(|| {
                    self.slots.fetch_add(1, Ordering::Relaxed);
                })),
            })
        }
    }
    impl<'ir, 'task> ForkSink<'ir, 'task, B64> for Sink<'ir, 'task> {
        fn submit(&self, task: Task<'ir, 'task, B64>) {
            self.leaves.lock().unwrap().push(task);
        }

        fn arm_scheduler(&self) -> Option<region_arm::Scheduler<'_, 'ir, B64>> {
            Some(region_arm::Scheduler { threads: self, queue: &self.queue })
        }
    }

    use crate::config::PathFailureAction;
    use crate::error::{SmtError, Z3QueryFailure, Z3Timeout};

    let run = |leaves, slots, policy, inject: bool, worker_panic: bool| {
        let shared = SharedState::new(
            Symtab::new(),
            &[],
            IRTypeInfo::new::<B64>(&[]),
            HashSet::new(),
            HashSet::new(),
            HashSet::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        let mut config = Config::new();
        config.solver_options.on_unknown = policy;
        let ctx = Context::new(config);
        let mut solver = Solver::new(&ctx);
        let input = solver.declare_const(smtlib::Ty::Bool, info());
        let mut root = make_frame(vec![Instr::End]);
        let entry = checkpoint(&mut solver);
        let mut limits = ExecutionLimits::default().with_path_merging(true);
        limits.arms_as_tasks = true;
        let mut state = TaskState::new().with_execution_limits(limits);
        let workers = Arc::new(Mutex::new(HashSet::new()));
        let used = workers.clone();
        state.arm_test_hook = Some(Arc::new(move |point| {
            if point == "certification_worker" {
                used.lock().unwrap().insert(std::thread::current().id());
                assert!(!worker_panic, "认证线程注入 panic");
            }
            if inject {
                let reason = match point {
                    "certification_check/40" => "timeout",
                    "certification_check/51" => "canceled",
                    _ => return Ok(()),
                };
                let query = Z3QueryFailure {
                    reason: reason.into(),
                    source_loc: info(),
                    purpose: "arm_error",
                    wall: Duration::from_millis(5),
                    limit: (reason == "timeout").then_some(Duration::from_millis(5)),
                };
                return Err(ExecError::Smt(SmtError::Z3Timeout(Z3Timeout::Native(query))));
            }
            Ok(())
        }));
        let errors = (0..leaves)
            .map(|index| {
                let mut failed = Solver::from_checkpoint(&ctx, entry.clone());
                let positive = smtlib::Exp::Var(input);
                let constraint =
                    if index % 3 == 1 { smtlib::Exp::Not(Box::new(positive.clone())) } else { positive.clone() };
                failed.assert(constraint);
                let mut task = root.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut failed));
                task.fork_cond = Some((smtlib::Def::Assert(positive), Event::Fork(0, input, index, info())));
                task.frame.arm_error = Some((ExecError::Type("失败叶".into(), info()), false));
                task
            })
            .collect();
        let sink =
            Sink { queue: region_arm::ArmQueue::new(), slots: AtomicUsize::new(slots), leaves: Mutex::new(Vec::new()) };
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            region_merge::publish_arm_errors(&mut root, errors, &solver, &mut Fraction::one(), &sink, &shared);
        }));
        assert_eq!(sink.slots.load(Ordering::Relaxed), slots);
        let observed: Vec<_> = sink
            .leaves
            .into_inner()
            .unwrap()
            .into_iter()
            .map(|task| {
                let Some((_, Event::Fork(id, _, index, _))) = task.fork_cond else { unreachable!() };
                (id, index, task.frame.arm_error.unwrap().1, task.frame.execution_limit_state.path_signature())
            })
            .collect();
        assert!(observed.iter().all(|(_, _, certified, _)| *certified));
        let count = workers.lock().unwrap().len();
        let drops = shared.execution_stats.solver_path_drops_since(0);
        let panic = outcome.err().map(|panic| {
            panic
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| panic.downcast_ref::<&str>().map(|text| (*text).to_owned()))
                .unwrap()
        });
        (observed, count, drops.count, drops.first_locations, panic)
    };

    let serial = run(72, 0, PathFailureAction::Dead, false, false);
    let parallel = run(72, 3, PathFailureAction::Dead, false, false);
    assert_eq!(
        serial.0.iter().map(|(_, index, _, _)| *index).collect::<Vec<_>>(),
        (0..72).filter(|index| index % 3 != 1).collect::<Vec<_>>()
    );
    assert_eq!(parallel.0, serial.0);
    assert_eq!((serial.1, serial.2, parallel.2), (0, 0, 0));
    assert_eq!((serial.4, parallel.4), (None, None));
    assert!(parallel.1 > 0, "大根必须有远端认证线程");
    assert_eq!(run(12, 3, PathFailureAction::Dead, false, false).1, 0);

    let serial = run(72, 0, PathFailureAction::Dead, true, false);
    let parallel = run(72, 3, PathFailureAction::Dead, true, false);
    assert_eq!(parallel.0, serial.0);
    assert_eq!(parallel.2, 2);
    assert_eq!(parallel.3, serial.3);
    assert_eq!(
        parallel.3.iter().map(|drop| drop.reason_unknown.as_deref()).collect::<Vec<_>>(),
        [Some("timeout"), Some("canceled")]
    );
    assert_eq!((serial.4, parallel.4), (None, None));

    let serial = run(72, 0, PathFailureAction::Panic, true, false);
    let parallel = run(72, 3, PathFailureAction::Panic, true, false);
    assert_eq!(parallel.0, serial.0);
    assert_eq!(parallel.4, serial.4);
    assert!(parallel.4.unwrap().contains("reason_unknown=Some(\"timeout\")"));
    let panicked = run(72, 3, PathFailureAction::Dead, false, true);
    assert!(panicked.4.unwrap().contains("认证线程注入 panic"));
}
