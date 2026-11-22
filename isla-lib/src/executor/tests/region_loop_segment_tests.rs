//! 有限逐项搜索带提前返回：切段必须保存全部输入/结果关系及完整状态。
use super::*;

pub(super) fn segment_paths(
    instrs: Vec<Instr<Name, B64>>,
    shared: &SharedState<'static, B64>,
    inputs: usize,
    limits: ExecutionLimits,
    budget: usize,
    memory: crate::memory::Memory<B64>,
    configure: impl FnOnce(&mut LocalFrame<'static, B64>),
) -> Vec<Path> {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let mut frame = make_frame(instrs);
    frame.set_memory(memory);
    frame.function_name = TOP_LEVEL_LET;
    for (name, ty) in &shared.registers {
        frame.regs_mut().insert(*name, false, UVal::Uninit(Box::leak(Box::new(ty.clone()))));
    }
    for index in 0..inputs {
        let symbol = solver.declare_const(smtlib::Ty::Bool, info());
        frame.vars_mut().insert(test_name(900 + index as u32), UVal::Init(Val::Symbolic(symbol)));
    }
    configure(&mut frame);
    let state = TaskState::new().with_execution_limits(limits).with_region_step_budget(budget);
    let output = Mutex::new(Vec::new());
    start_single(
        frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
        shared,
        &output,
        &|_, _, result, _, mut solver, output| match result {
            Ok((Run::Finished(value), frame)) => match solver.check_sat(info()) {
                SmtResult::Sat => output.lock().unwrap().push(Path {
                    exception: frame.get_exception().map(|(value, _)| value.clone()),
                    records: frame.region_merge_records().to_vec(),
                    value,
                    events: solver.trace().to_vec().into_iter().rev().cloned().collect(),
                    variables: frame.vars().clone(),
                    registers: frame.regs().clone(),
                    lets: frame.lets().clone(),
                    checkpoint: checkpoint(&mut solver),
                }),
                SmtResult::Unsat => (),
                result => panic!("完成路径的可满足性查询失败：{result:?}"),
            },
            Ok((Run::Dead, _)) | Err((ExecError::AssertionFailure(..), _)) => (),
            Err((ExecError::Type(..), _)) if solver.check_sat(info()).is_unsat().unwrap() => (),
            Err((error, _)) => panic!("差分执行失败：{error:?}"),
            _ => panic!("差分执行未正常返回"),
        },
    );
    output.into_inner().unwrap()
}

pub(super) fn scan_program(
    counter: Name,
    choices: Name,
    choice: Name,
    n: usize,
    reg: Option<Name>,
) -> Vec<Instr<Name, B64>> {
    let mut code = vec![
        Instr::Init(counter, Ty::I128, Exp::I128(0), info()),
        Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(counter), Exp::I128(n as i128)]), 9, info()),
        Instr::PrimopBinary(
            Loc::Id(choice),
            primop::binary_primops()["vector_access"],
            Exp::Id(choices),
            Exp::Id(counter),
            info(),
        ),
        Instr::Jump(Exp::Id(choice), 7, info()),
        Instr::PrimopBinary(
            Loc::Id(counter),
            primop::binary_primops()["add_int"],
            Exp::Id(counter),
            Exp::I128(1),
            info(),
        ),
        Instr::Goto(1),
        Instr::Arbitrary,
        Instr::Copy(Loc::Id(RETURN), Exp::Id(counter), info()),
        Instr::Goto(11),
        Instr::Copy(Loc::Id(RETURN), Exp::I128(n as i128), info()),
        Instr::Goto(11),
        Instr::End,
    ];
    if let Some(reg) = reg {
        // 在读取本轮判断前写状态；修正受插入影响的全部目标。
        code.insert(2, Instr::Copy(Loc::Id(reg), Exp::Id(counter), info()));
        for instr in &mut code {
            match instr {
                Instr::Jump(_, target, _) | Instr::Goto(target) if *target >= 2 => *target += 1,
                _ => (),
            }
        }
    }
    code
}
fn scan_paths(
    shared: &SharedState<'static, B64>,
    n: usize,
    budget: usize,
    merge: bool,
    reg: Option<Name>,
) -> Vec<Path> {
    scan_paths_with_limits(shared, n, budget, reg, ExecutionLimits::default().with_path_merging(merge))
}

pub(super) fn scan_paths_with_limits(
    shared: &SharedState<'static, B64>,
    n: usize,
    budget: usize,
    reg: Option<Name>,
    limits: ExecutionLimits,
) -> Vec<Path> {
    let counter = test_name(1800);
    let choices = test_name(1801);
    let choice = test_name(1802);
    segment_paths(
        scan_program(counter, choices, choice, n, reg),
        shared,
        n,
        limits.with_region_loop_analysis(true).with_region_global_state(true),
        budget,
        crate::memory::Memory::new(),
        |frame| {
            let values = (0..n)
                .map(|i| match frame.vars()[&test_name(900 + i as u32)].clone() {
                    UVal::Init(v) => v,
                    _ => panic!("输入必须初始化"),
                })
                .collect();
            frame.vars_mut().insert(choices, UVal::Init(Val::Vector(values)));
            frame.vars_mut().insert(choice, UVal::Uninit(&Ty::Bool));
            if let Some(reg) = reg {
                frame.regs_mut().assign(reg, Val::I128(-1), shared);
            }
        },
    )
}
pub(super) fn equivalent_scalar_paths(off: &[Path], on: &[Path], n: usize) {
    use smtlib::Exp::*;
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let inputs = (0..n).map(|_| solver.declare_const(smtlib::Ty::Bool, info())).collect::<Vec<_>>();
    let result = solver.declare_const(smtlib::Ty::BitVec(128), info());
    let relation = |paths: &[Path], solver: &mut Solver<B64>| {
        let mut covered = Bool(false);
        let mut outputs = Bool(false);
        for path in paths {
            let (condition, value) = import(path, &inputs, solver);
            outputs = Or(
                Box::new(outputs),
                Box::new(And(Box::new(condition.clone()), Box::new(Eq(Box::new(value), Box::new(Var(result)))))),
            );
            covered = Or(Box::new(covered), Box::new(condition));
        }
        (covered, outputs)
    };
    let (a, av) = relation(off, &mut solver);
    let (b, bv) = relation(on, &mut solver);
    assert!(
        solver.check_sat_with(&Neq(Box::new(av), Box::new(bv)), info()).is_unsat().unwrap(),
        "每个输入的首次命中返回值必须相同"
    );
    assert!(
        solver.check_sat_with(&Neq(Box::new(a.clone()), Box::new(b)), info()).is_unsat().unwrap(),
        "不能漏掉继续/返回任一补集"
    );
    assert!(solver.check_sat_with(&Not(Box::new(a)), info()).is_unsat().unwrap());
}
#[test]
fn loop_segment_sixty_four_rounds_keep_first_match_and_reduce_paths() {
    if !run_in_diagnostics_process(concat!(
        module_path!(),
        "::loop_segment_sixty_four_rounds_keep_first_match_and_reduce_paths"
    )) {
        return;
    }
    run_deep_region_test(loop_segment_sixty_four_rounds_keep_first_match_and_reduce_paths_body);
}

fn loop_segment_sixty_four_rounds_keep_first_match_and_reduce_paths_body() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let off = scan_paths(&shared, 64, 128, false, None);
    assert_eq!(off.len(), 65);
    shared.execution_stats.reset();
    stats::merge_diagnostics::configure("summary").unwrap();
    let on = scan_paths(&shared, 64, 128, true, None);
    equivalent_scalar_paths(&off, &on, 64);
    assert!(on.len() <= 16, "分段应在边界合流，而不是逐轮放出：{}", on.len());
    let stats = shared.execution_stats.merge_json();
    stats::merge_diagnostics::configure("off").unwrap();
    assert_eq!(stats["failure_reasons"]["step_budget"].as_u64().unwrap_or(0), 0, "已完成的段不能整体作废");
}
#[test]
fn loop_segment_multiple_real_ends_use_virtual_exit() {
    run_deep_region_test(loop_segment_multiple_real_ends_use_virtual_exit_body);
}

fn loop_segment_multiple_real_ends_use_virtual_exit_body() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let n = 64;
    let counter = test_name(1800);
    let choices = test_name(1801);
    let choice = test_name(1802);
    let mut program = scan_program(counter, choices, choice, n, None);
    program[8] = Instr::End;
    program[10] = Instr::End;
    let run = |merge| {
        segment_paths(
            program.clone(),
            &shared,
            n,
            ExecutionLimits::default()
                .with_path_merging(merge)
                .with_region_loop_analysis(true)
                .with_region_global_state(true),
            128,
            crate::memory::Memory::new(),
            |frame| {
                let values = (0..n)
                    .map(|i| match frame.vars()[&test_name(900 + i as u32)].clone() {
                        UVal::Init(v) => v,
                        _ => unreachable!(),
                    })
                    .collect();
                frame.vars_mut().insert(choices, UVal::Init(Val::Vector(values)));
                frame.vars_mut().insert(choice, UVal::Uninit(&Ty::Bool));
            },
        )
    };
    let off = run(false);
    let on = run(true);
    equivalent_scalar_paths(&off, &on, n);
    assert!(on.len() <= 16, "虚出口也必须真实分段：{}", on.len());
    assert!(on.iter().any(|p| p.records.iter().any(|r| r.join == crate::ir::regions::RegionPoint::FunctionExit)));
}

#[test]
fn loop_segment_register_state_and_continue_guard_are_exact() {
    let mut shared = empty_shared_state();
    let reg = shared.symtab.intern("ziteration_state");
    shared.registers.insert(reg, Ty::I128);
    let off = scan_paths(&shared, 8, 40, false, Some(reg));
    let counts = [crate::config::MergeStrategy::Recursive, crate::config::MergeStrategy::Flat].map(|strategy| {
        let mut limits = ExecutionLimits::default().with_path_merging(true);
        limits.merge_strategy = strategy;
        let on = scan_paths_with_limits(&shared, 8, 40, Some(reg), limits);
        equivalent_scalar_paths(&off, &on, 8);
        equivalent_register_paths(&off, &on, 8);
        let mut counts: Vec<_> = on.iter().map(|path| path.records.len()).collect();
        counts.sort_unstable();
        counts
    });
    assert_eq!(counts[0], counts[1], "有限预算下，两组织者必须留下相同数量的前沿和记录");
}
#[test]
fn loop_segment_zero_budget_keeps_ordinary_fallback() {
    let shared = empty_shared_state();
    let off = scan_paths(&shared, 4, 0, false, None);
    let on = scan_paths(&shared, 4, 0, true, None);
    equivalent_scalar_paths(&off, &on, 4);
    assert!(on.iter().all(|p| p.records.is_empty()));
}

#[test]
fn loop_segment_read_only_register_guard_survives_continue() {
    let mut shared = empty_shared_state();
    let reg = shared.symtab.intern("zguarded_input");
    shared.registers.insert(reg, Ty::Bool);
    let n = 8;
    let counter = test_name(1800);
    let choices = test_name(1801);
    let choice = test_name(1802);
    let mut program = scan_program(counter, choices, choice, n, None);
    program[7] = Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info());
    program[9] = Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info());
    let run = |merge| {
        segment_paths(
            program.clone(),
            &shared,
            n + 1,
            ExecutionLimits::default()
                .with_path_merging(merge)
                .with_region_loop_analysis(true)
                .with_region_global_state(true),
            40,
            crate::memory::Memory::new(),
            |frame| {
                let values = (0..n)
                    .map(|i| match frame.vars()[&test_name(900 + i as u32)].clone() {
                        UVal::Init(v) => v,
                        _ => unreachable!(),
                    })
                    .collect();
                frame.vars_mut().insert(choices, UVal::Init(Val::Vector(values)));
                frame.vars_mut().insert(choice, UVal::Uninit(&Ty::Bool));
                let UVal::Init(value) = frame.vars()[&test_name(900 + n as u32)].clone() else { unreachable!() };
                frame.regs_mut().assign(reg, value, &shared);
            },
        )
    };
    let off = run(false);
    let on = run(true);
    equivalent_paths(&off, &on, n + 1, true);
    equivalent_register_paths(&off, &on, n + 1);
    assert!(
        on.iter().any(|p| p.records.iter().any(|r| r.join == crate::ir::regions::RegionPoint::Instruction(3))),
        "必须真实经过继续前沿"
    );
}

#[test]
fn loop_segment_failed_exit_merge_does_not_submit_a_continuation() {
    let shared = empty_shared_state();
    let n = 16;
    let counter = test_name(1800);
    let choices = test_name(1801);
    let choice = test_name(1802);
    let labels = test_name(1803);
    let mut program = scan_program(counter, choices, choice, n, None);
    program[7] = Instr::PrimopBinary(
        Loc::Id(RETURN),
        primop::binary_primops()["vector_access"],
        Exp::Id(labels),
        Exp::Id(counter),
        info(),
    );
    program[9] = Instr::Copy(Loc::Id(RETURN), Exp::String("none".into()), info());
    let run = |merge| {
        segment_paths(
            program.clone(),
            &shared,
            n,
            ExecutionLimits::default()
                .with_path_merging(merge)
                .with_region_loop_analysis(true)
                .with_region_global_state(true),
            32,
            crate::memory::Memory::new(),
            |frame| {
                let values = (0..n)
                    .map(|i| match frame.vars()[&test_name(900 + i as u32)].clone() {
                        UVal::Init(v) => v,
                        _ => unreachable!(),
                    })
                    .collect();
                frame.vars_mut().insert(choices, UVal::Init(Val::Vector(values)));
                frame.vars_mut().insert(choice, UVal::Uninit(&Ty::Bool));
                frame.vars_mut().insert(
                    labels,
                    UVal::Init(Val::Vector(
                        (0..n).map(|i| Val::String(if i == 0 { "first" } else { "later" }.into())).collect(),
                    )),
                );
            },
        )
    };
    let off = run(false);
    let on = run(true);
    use smtlib::Exp::*;
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let inputs = (0..n).map(|_| solver.declare_const(smtlib::Ty::Bool, info())).collect::<Vec<_>>();
    let relation = |paths: &[Path], solver: &mut Solver<B64>| {
        let mut result = HashMap::<String, Formula>::new();
        let mut guards = Vec::new();
        for path in paths {
            let (guard, _) = import_values(path, &inputs, solver, &[]);
            let Val::String(label) = &path.value else { panic!("必须返回字符串") };
            let old = result.remove(label).unwrap_or(Bool(false));
            result.insert(label.clone(), Or(Box::new(old), Box::new(guard.clone())));
            guards.push(guard);
        }
        (result, guards)
    };
    let (a, _) = relation(&off, &mut solver);
    let (b, guards) = relation(&on, &mut solver);
    assert_eq!(a.len(), b.len());
    for (label, value) in a {
        assert!(solver.check_sat_with(&Neq(Box::new(value), Box::new(b[&label].clone())), info()).is_unsat().unwrap());
    }
    for (i, x) in guards.iter().enumerate() {
        for y in guards.iter().skip(i + 1) {
            assert!(
                solver.check_sat_with(&And(Box::new(x.clone()), Box::new(y.clone())), info()).is_unsat().unwrap(),
                "失败段不得泄漏重复继续任务"
            );
        }
    }
}

#[test]
fn loop_segment_discards_dead_preexisting_locals_at_function_exit() {
    run_deep_region_test(loop_segment_discards_dead_preexisting_locals_at_function_exit_body);
}

fn loop_segment_discards_dead_preexisting_locals_at_function_exit_body() {
    let shared = empty_shared_state();
    let n = 64;
    let counter = test_name(1800);
    let choices = test_name(1801);
    let choice = test_name(1802);
    let scratch = test_name(1803);
    let labels = test_name(1804);
    let mut program = scan_program(counter, choices, choice, n, None);
    // 返回前留下各轮不同的具体临时值；它在函数退出后不再可读。
    program.insert(
        7,
        Instr::PrimopBinary(
            Loc::Id(scratch),
            primop::binary_primops()["vector_access"],
            Exp::Id(labels),
            Exp::Id(counter),
            info(),
        ),
    );
    for instr in &mut program {
        match instr {
            Instr::Jump(_, target, _) | Instr::Goto(target) if *target >= 7 => *target += 1,
            _ => (),
        }
    }
    program[3] = Instr::Jump(Exp::Id(choice), 7, info());
    let run = |merge| {
        segment_paths(
            program.clone(),
            &shared,
            n,
            ExecutionLimits::default()
                .with_path_merging(merge)
                .with_region_loop_analysis(true)
                .with_region_global_state(true),
            128,
            crate::memory::Memory::new(),
            |frame| {
                let values = (0..n)
                    .map(|i| match frame.vars()[&test_name(900 + i as u32)].clone() {
                        UVal::Init(v) => v,
                        _ => unreachable!(),
                    })
                    .collect();
                frame.vars_mut().insert(choices, UVal::Init(Val::Vector(values)));
                frame.vars_mut().insert(choice, UVal::Uninit(&Ty::Bool));
                frame.vars_mut().insert(scratch, UVal::Init(Val::I64(-1)));
                frame.vars_mut().insert(labels, UVal::Init(Val::Vector((0..n).map(|i| Val::I64(i as i64)).collect())));
            },
        )
    };
    let off = run(false);
    let on = run(true);
    equivalent_scalar_paths(&off, &on, n);
    assert!(on.len() <= 16, "死局部槽位不能阻碍返回前沿合并：{}", on.len());
}

#[test]
fn loop_iteration_frontiers_finish_sixty_four_rounds_in_one_region() {
    run_deep_region_test(loop_iteration_frontiers_finish_sixty_four_rounds_in_one_region_body);
}

fn loop_iteration_frontiers_finish_sixty_four_rounds_in_one_region_body() {
    let shared = empty_shared_state();
    let off = scan_paths(&shared, 64, 128, false, None);
    crate::executor::region_merge::FOLD_HISTORY_ID_VISITS.set(0);
    let on = scan_paths(&shared, 64, 128, true, None);
    equivalent_scalar_paths(&off, &on, 64);
    assert_eq!(on.len(), 1, "累计返回与继续前沿应逐轮收敛，完整函数只有一个合并状态");
    let records = &on[0].records;
    let visits = crate::executor::region_merge::FOLD_HISTORY_ID_VISITS.get();
    assert!(visits <= records.len(), "累计侧 ID 只应登记一次：{visits} 次访问，{} 条记录", records.len());
    let ids: std::collections::HashSet<_> = records.iter().map(|r| r.record_id).collect();
    assert_eq!(ids.len(), records.len(), "共享前缀在不同条件下出现时必须保持记录ID唯一");
    assert!(records.iter().all(|r| r.parent_record.is_none_or(|id| ids.contains(&id))), "任何父记录都必须存在");
    // 每轮的返回选择器仍链接先前的到达条件，但本轮的原始表达式不能复制整条链。
    let guard_nodes: Vec<_> = on[0]
        .events
        .iter()
        .filter_map(|event| match event {
            Event::Smt(smtlib::Def::DefineConst(_, exp @ smtlib::Exp::Not(inner)), ..)
                if matches!(inner.as_ref(), smtlib::Exp::And(..)) =>
            {
                Some(stats::memory_stats::exp_stats(exp).0)
            }
            _ => None,
        })
        .collect();
    assert!(!guard_nodes.is_empty(), "夹具必须经过带前序条件的迭代汇合");
    assert!(guard_nodes.iter().all(|nodes| *nodes <= 6), "单轮到达条件不应复制前序各轮：{guard_nodes:?}");
}

#[test]
fn loop_iteration_frontiers_keep_constant_history_after_each_round() {
    const TEST: &str = "executor::tests::region_merge_tests::loop_segment_tests::loop_iteration_frontiers_keep_constant_history_after_each_round";
    let args = ["--exact", TEST, "--nocapture", "--test-threads=1"];
    if !std::env::args().skip(1).eq(args) {
        let output = std::process::Command::new(std::env::current_exe().unwrap()).args(args).output().unwrap();
        assert!(
            output.status.success(),
            "循环历史压缩子进程失败：\n{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        return;
    }
    run_deep_region_test(loop_iteration_frontiers_keep_constant_history_after_each_round_body);
}

/// `pmpCheck` 的循环体没有架构写入。每轮的命中出口与未命中继续臂汇合后，
/// 运行时只应保留常数个前沿；完整历史由已发布的选择器表达，不应把每轮区域
/// 记录和事务层继续挂在下一轮帧上。
fn loop_iteration_frontiers_keep_constant_history_after_each_round_body() {
    crate::config::RegionOptions { prefix_compact: true, ..Default::default() }.configure();
    let shared = empty_shared_state();
    let run = |n| scan_paths(&shared, n, 128, true, None);
    let off = scan_paths(&shared, 16, 128, false, None);
    let four = run(4);
    let sixteen = run(16);
    assert_eq!(four.len(), 1);
    assert_eq!(sixteen.len(), 1);
    equivalent_scalar_paths(&off, &sixteen, 16);
    assert_eq!(
        four[0].records.len(),
        sixteen[0].records.len(),
        "无架构写入循环的保留区域记录不能随轮数增长：N=4 为 {}，N=16 为 {}",
        four[0].records.len(),
        sixteen[0].records.len()
    );
}

#[test]
fn loop_iteration_frontiers_nested_call_preserves_complete_relation() {
    run_deep_region_test(loop_iteration_frontiers_nested_call_preserves_complete_relation_body);
}

fn loop_iteration_frontiers_nested_call_preserves_complete_relation_body() {
    let mut shared = empty_shared_state();
    let function = shared.symtab.intern("zfinite_scan");
    let counter = test_name(1800);
    let choices = test_name(1801);
    let choice = test_name(1802);
    let n = 64;
    let mut body = scan_program(counter, choices, choice, n, None);
    // 参数只传输入向量，局部判断槽仍属于被调用帧。
    body.insert(0, Instr::Decl(choice, Ty::Bool, info()));
    for instr in &mut body {
        match instr {
            Instr::Jump(_, target, _) | Instr::Goto(target) => *target += 1,
            _ => (),
        }
    }
    let ty = Box::leak(Box::new(Ty::Vector(Box::new(Ty::Bool))));
    shared.functions.insert(function, (vec![(choices, &*ty)], &Ty::I128, Box::leak(body.into_boxed_slice())));
    let program = vec![
        Instr::Jump(input(n as u32), 3, info()),
        Instr::Call(Loc::Id(RETURN), false, function, vec![Exp::Id(choices)], info()),
        Instr::Goto(4),
        Instr::Copy(Loc::Id(RETURN), Exp::I128(-1), info()),
        Instr::End,
    ];
    let run = |merge| {
        segment_paths(
            program.clone(),
            &shared,
            n + 1,
            ExecutionLimits::default()
                .with_path_merging(merge)
                .with_region_loop_analysis(true)
                .with_region_global_state(true),
            128,
            crate::memory::Memory::new(),
            |frame| {
                let values = (0..n)
                    .map(|i| match frame.vars()[&test_name(900 + i as u32)].clone() {
                        UVal::Init(v) => v,
                        _ => unreachable!(),
                    })
                    .collect();
                frame.vars_mut().insert(choices, UVal::Init(Val::Vector(values)));
            },
        )
    };
    let off = run(false);
    let on = run(true);
    equivalent_scalar_paths(&off, &on, n + 1);
    assert_eq!(on.len(), 1, "子循环必须收敛后交还调用者，不能耗尽父区域总预算");
}

#[test]
fn loop_iteration_frontiers_concrete_tail_keeps_iteration_budget() {
    let shared = empty_shared_state();
    let n = 64;
    let counter = test_name(1800);
    let choices = test_name(1801);
    let choice = test_name(1802);
    let run = |merge| {
        segment_paths(
            scan_program(counter, choices, choice, n, None),
            &shared,
            1,
            ExecutionLimits::default()
                .with_path_merging(merge)
                .with_region_loop_analysis(true)
                .with_region_global_state(true),
            128,
            crate::memory::Memory::new(),
            |frame| {
                let UVal::Init(value) = frame.vars()[&test_name(900)].clone() else { unreachable!() };
                // 首轮未命中后，其余轮的同一条件全部已知为false，不再产生pending_branch。
                frame.vars_mut().insert(choices, UVal::Init(Val::Vector(vec![value; n])));
                frame.vars_mut().insert(choice, UVal::Uninit(&Ty::Bool));
            },
        )
    };
    let off = run(false);
    let on = run(true);
    equivalent_scalar_paths(&off, &on, 1);
    assert_eq!(on.len(), 1, "没有新符号分叉的后续轮次仍应按迭代预算收敛");
}
