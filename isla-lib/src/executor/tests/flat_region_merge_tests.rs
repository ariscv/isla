//! 平铺队列的返回关系、覆盖和回退回归；配置在独立子进程冻结。
use super::*;

fn limits(merge: bool) -> ExecutionLimits {
    let mut limits = ExecutionLimits::default()
        .with_path_merging(merge)
        .with_region_global_state(true)
        .with_region_loop_analysis(true);
    limits.merge_strategy = crate::config::MergeStrategy::Flat;
    limits.ordered_events = std::env::var("ISLA_FLAT_ORDER_TEST").unwrap() == "true";
    limits
}

fn paths(instrs: Vec<Instr<Name, B64>>, shared: &SharedState<'static, B64>, inputs: usize, merge: bool) -> Vec<Path> {
    paths_with_state(instrs, shared, inputs, limits(merge), crate::memory::Memory::new(), |_| ())
}

fn differential(
    instrs: Vec<Instr<Name, B64>>,
    shared: &SharedState<'static, B64>,
    inputs: usize,
    complete: bool,
) -> (usize, usize) {
    let forked = paths(instrs.clone(), shared, inputs, false);
    let merged = paths(instrs, shared, inputs, true);
    equivalent_paths(&forked, &merged, inputs, complete)
}

fn flat_child(test: &str) -> bool {
    const CHILD: &str = "ISLA_FLAT_TEST_CHILD";
    if let Ok(mode) = std::env::var(CHILD) {
        crate::config::RegionOptions {
            defer_exit_check: mode == "defer",
            lazy_z3_scope: mode == "defer",
            ..Default::default()
        }
        .configure();
        return true;
    }
    for mode in ["eager", "defer"] {
        for ordered in ["false", "true"] {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    &format!("executor::tests::region_merge_tests::flat_region_merge_tests::{test}"),
                    "--nocapture",
                ])
                .env(CHILD, mode)
                .env("ISLA_FLAT_ORDER_TEST", ordered)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{mode}: {}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }
    false
}

#[test]
fn flat_single_if() {
    if !flat_child("flat_single_if") {
        return;
    }
    let shared = empty_shared_state();
    let program = vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(4),
        Instr::Copy(Loc::Id(RETURN), input(1), info()),
        Instr::End,
    ];
    assert_eq!(differential(program, &shared, 2, true), (2, 1));
}

#[test]
fn flat_deep_nesting_records_logical_depth() {
    if !flat_child("flat_deep_nesting_records_logical_depth") {
        return;
    }
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let count = 24;
    let end = count * 3 + 1;
    let mut program = Vec::new();
    for index in 0..count {
        program.extend([
            Instr::Jump(input(index as u32), index * 3 + 3, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            Instr::Goto(end),
        ]);
    }
    program.extend([Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()), Instr::End]);
    let forked = paths(program.clone(), &shared, count, false);
    let merged = paths(program, &shared, count, true);
    assert_eq!(equivalent_paths(&forked, &merged, count, true), (25, 1));
    assert_eq!(merged[0].records.len(), count);
    assert_eq!(merged[0].records.iter().map(|record| record.depth).max(), Some(count));
    assert!(shared.execution_stats.merge_json()["failure_reasons"].get("nesting_limit").is_none());
}

#[test]
fn flat_calls_keep_caller_locals_and_context() {
    if !flat_child("flat_calls_keep_caller_locals_and_context") {
        return;
    }
    let mut shared = empty_shared_state();
    let function = helper(&mut shared);
    let argument = shared.functions[&function].0[0].0;
    shared.functions.get_mut(&function).unwrap().2 = Box::leak(
        vec![
            Instr::Jump(Exp::Id(argument), 3, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            Instr::End,
        ]
        .into_boxed_slice(),
    );
    let saved = test_name(1800);
    let program = vec![
        Instr::Init(saved, Ty::Bool, input(1), info()),
        Instr::Jump(input(0), 5, info()),
        Instr::Call(Loc::Id(RETURN), false, function, vec![input(2)], info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::And, vec![Exp::Id(RETURN), Exp::Id(saved)]), info()),
        Instr::Goto(7),
        Instr::Call(Loc::Id(RETURN), false, function, vec![input(1)], info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Or, vec![Exp::Id(RETURN), Exp::Id(saved)]), info()),
        Instr::End,
    ];
    assert_eq!(differential(program, &shared, 3, true), (4, 1));
}

#[test]
fn flat_symbolic_assert_before_later_assume() {
    if !flat_child("flat_symbolic_assert_before_later_assume") {
        return;
    }
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let tmp = test_name(1801);
    let program = vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(7),
        Instr::PrimopBinary(
            Loc::Id(tmp),
            primop::pessimistic_assert::<B64>,
            input(1),
            Exp::String("前序断言".into()),
            info(),
        ),
        Instr::PrimopUnary(Loc::Id(tmp), primop::unary_primops()["assume"], input(1), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
        Instr::Goto(7),
        Instr::End,
    ];
    let forked = paths(program.clone(), &shared, 2, false);
    let merged = paths(program, &shared, 2, true);
    equivalent_paths(&forked, &merged, 2, false);
    assert!(shared.execution_stats.merge_json()["failure_reasons"]["symbolic_assertion"].as_u64().unwrap() > 0);
    assert!(merged.iter().all(|path| path.records.is_empty()), "拒绝不得泄漏候选记录");
}

#[test]
fn flat_dead_arm_keeps_live_sibling() {
    if !flat_child("flat_dead_arm_keeps_live_sibling") {
        return;
    }
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let program = vec![
        Instr::Jump(input(0), 4, info()),
        Instr::PrimopBinary(
            Loc::Id(RETURN),
            primop::pessimistic_assert::<B64>,
            Exp::Bool(false),
            Exp::String("具体失败臂".into()),
            info(),
        ),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(5),
        Instr::Copy(Loc::Id(RETURN), input(1), info()),
        Instr::End,
    ];
    let forked = paths(program.clone(), &shared, 2, false);
    let merged = paths(program, &shared, 2, true);
    assert_eq!(equivalent_paths(&forked, &merged, 2, false), (1, 1));
    assert!(!merged[0].records.is_empty());
    assert_eq!(shared.execution_stats.merge_json()["failures"], 0);
}

#[test]
fn flat_drops_dead_entry_local_before_interior_join() {
    if !flat_child("flat_drops_dead_entry_local_before_interior_join") {
        return;
    }
    let shared = empty_shared_state();
    let dead = test_name(1802);
    let program = vec![
        Instr::Decl(dead, Ty::I64, info()),
        Instr::Jump(input(0), 4, info()),
        Instr::Copy(Loc::Id(dead), Exp::I64(0), info()),
        Instr::Goto(5),
        Instr::Copy(Loc::Id(dead), Exp::I64(1), info()),
        Instr::Copy(Loc::Id(RETURN), input(1), info()),
        Instr::End,
    ];
    let forked = paths(program.clone(), &shared, 2, false);
    let merged = paths(program, &shared, 2, true);
    assert_eq!(equivalent_paths(&forked, &merged, 2, true), (2, 1));
    assert!(!merged[0].variables.contains_key(&dead));
    assert_eq!(merged[0].records.len(), 1);
}

#[test]
fn flat_ordered_events_opposite_register_orders() {
    if !flat_child("flat_ordered_events_opposite_register_orders") {
        return;
    }
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let a = shared.symtab.intern("zflat_a");
    let b = shared.symtab.intern("zflat_b");
    for reg in [a, b] {
        shared.registers.insert(reg, Ty::Bool);
    }
    let write = |reg, value| Instr::Copy(Loc::Id(reg), Exp::Bool(value), info());
    let program = diamond(
        vec![write(a, true), write(b, true)],
        vec![write(b, false), write(a, false)],
        vec![Instr::Copy(Loc::Id(RETURN), input(0), info()), Instr::End],
    );
    let configure = |frame: &mut LocalFrame<'static, B64>| {
        for reg in [a, b] {
            frame.regs_mut().assign(reg, Val::Bool(false), &shared);
        }
    };
    let run =
        |merge| paths_with_state(program.clone(), &shared, 1, limits(merge), crate::memory::Memory::new(), configure);
    let forked = run(false);
    let merged = run(true);
    equivalent_register_paths(&forked, &merged, 1);
    let ordered = limits(true).ordered_events;
    assert_eq!(equivalent_paths(&forked, &merged, 1, true), (2, if ordered { 2 } else { 1 }));
    if ordered {
        assert!(shared.execution_stats.merge_json()["failure_reasons"]["register_sequence"].as_u64().unwrap() > 0);
    } else {
        assert_eq!(merged[0].records.len(), 1);
        assert_eq!(merged[0].events.iter().filter(|event| matches!(event, Event::WriteReg(..))).count(), 2);
    }
}

fn diamond(
    then_arm: Vec<Instr<Name, B64>>,
    else_arm: Vec<Instr<Name, B64>>,
    tail: Vec<Instr<Name, B64>>,
) -> Vec<Instr<Name, B64>> {
    let target = else_arm.len() + 2;
    let join = target + then_arm.len();
    let mut p = vec![Instr::Jump(input(0), target, info())];
    p.extend(else_arm);
    p.push(Instr::Goto(join));
    p.extend(then_arm);
    p.extend(tail);
    p
}

#[test]
fn flat_preserves_slot_assigned_after_join() {
    if !flat_child("flat_preserves_slot_assigned_after_join") {
        return;
    }
    let shared = empty_shared_state();
    let slot = test_name(1803);
    let program = vec![
        Instr::Decl(slot, Ty::Bool, info()),
        Instr::Jump(input(0), 4, info()),
        Instr::Copy(Loc::Id(slot), Exp::Bool(false), info()),
        Instr::Goto(5),
        Instr::Copy(Loc::Id(slot), Exp::Bool(true), info()),
        Instr::Copy(Loc::Id(slot), input(1), info()),
        Instr::Copy(Loc::Id(RETURN), input(0), info()),
        Instr::End,
    ];
    assert_eq!(differential(program, &shared, 2, true), (2, 1));
}

#[test]
fn flat_distinct_return_pcs_reject_without_panic() {
    if !flat_child("flat_distinct_return_pcs_reject_without_panic") {
        return;
    }
    let shared = empty_shared_state();
    let program = vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::End,
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
        Instr::End,
    ];
    let forked = paths(program.clone(), &shared, 1, false);
    let merged = paths(program, &shared, 1, true);
    assert_eq!(equivalent_paths(&forked, &merged, 1, true), (2, 2));
    assert!(merged.iter().all(|path| path.records.is_empty()));
}

fn loop_fixture(early: bool, nested: bool) -> Vec<Instr<Name, B64>> {
    let i = test_name(1900);
    let j = test_name(1901);
    let mut program = vec![
        Instr::Init(i, Ty::I64, Exp::I64(0), info()),
        Instr::Init(j, Ty::I64, Exp::I64(0), info()),
        Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(i), Exp::I64(3)]), 15, info()),
        Instr::Jump(
            if early {
                Exp::Call(Op::And, vec![Exp::Call(Op::Eq, vec![Exp::Id(i), Exp::I64(1)]), input(0)])
            } else {
                Exp::Bool(false)
            },
            15,
            info(),
        ),
        Instr::Jump(input(1), 7, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(8),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
        Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(j), Exp::I64(if nested { 2 } else { 0 })]), 12, info()),
        Instr::Copy(Loc::Id(j), Exp::Call(Op::Add, vec![Exp::Id(j), Exp::I64(1)]), info()),
        Instr::Jump(input(0), 8, info()),
        Instr::Goto(8),
        Instr::Copy(Loc::Id(j), Exp::I64(0), info()),
        Instr::Copy(Loc::Id(i), Exp::Call(Op::Add, vec![Exp::Id(i), Exp::I64(1)]), info()),
        Instr::Goto(2),
        Instr::End,
    ];
    program.insert(0, Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()));
    for instr in &mut program[1..] {
        match instr {
            Instr::Jump(_, target, _) | Instr::Goto(target) => *target += 1,
            _ => (),
        }
    }
    program
}

fn assert_loop(early: bool, nested: bool) {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let off = paths(loop_fixture(early, nested), &shared, 2, false);
    let on = paths(loop_fixture(early, nested), &shared, 2, true);
    equivalent_paths(&off, &on, 2, true);
    assert_eq!(shared.execution_stats.merge_json()["failure_reasons"]["has_back_edge"].as_u64().unwrap_or(0), 0);
    assert_eq!(on.len(), 1, "循环必须实际合并为一条路径");
    assert!(on.iter().any(|p| !p.records.is_empty()), "循环必须实际合并");
}
#[test]
fn flat_loop_fixed_count() {
    if flat_child("flat_loop_fixed_count") {
        assert_loop(false, false);
    }
}
#[test]
fn flat_loop_symbolic_early_exit() {
    if flat_child("flat_loop_symbolic_early_exit") {
        assert_loop(true, false);
    }
}
#[test]
fn flat_loop_body_if() {
    if flat_child("flat_loop_body_if") {
        assert_loop(false, false);
    }
}
#[test]
fn flat_loop_nested() {
    if flat_child("flat_loop_nested") {
        assert_loop(false, true);
    }
}

#[test]
fn flat_loop_four_independent_exits_fold_per_round() {
    if !flat_child("flat_loop_four_independent_exits_fold_per_round") {
        return;
    }
    assert_independent_scan(false);
}

#[test]
fn flat_loop_inside_if_preserves_sibling_domain() {
    if flat_child("flat_loop_inside_if_preserves_sibling_domain") {
        assert_independent_scan(true);
    }
}

fn assert_independent_scan(wrapped: bool) {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let counter = test_name(1950);
    let choices = test_name(1951);
    let choice = test_name(1952);
    let mut program = super::loop_segment_tests::scan_program(counter, choices, choice, 4, None);
    if wrapped {
        for instr in &mut program {
            match instr {
                Instr::Jump(_, target, _) | Instr::Goto(target) => *target += 1,
                _ => (),
            }
        }
        program.insert(0, Instr::Jump(input(4), 13, info()));
        program.extend([Instr::Copy(Loc::Id(RETURN), Exp::I128(-1), info()), Instr::Goto(12)]);
    }
    let inputs = if wrapped { 5 } else { 4 };
    let run = |merge| {
        paths_with_state(program.clone(), &shared, inputs, limits(merge), crate::memory::Memory::new(), |frame| {
            let values = (0..4)
                .map(|i| match frame.vars()[&test_name(900 + i)].clone() {
                    UVal::Init(v) => v,
                    _ => unreachable!(),
                })
                .collect();
            frame.vars_mut().insert(choices, UVal::Init(Val::Vector(values)));
            frame.vars_mut().insert(choice, UVal::Uninit(&Ty::Bool));
        })
    };
    let off = run(false);
    let on = run(true);
    super::loop_segment_tests::equivalent_scalar_paths(&off, &on, inputs);
    assert_eq!(off.len(), if wrapped { 6 } else { 5 });
    assert_eq!(on.len(), 1, "{}", shared.execution_stats.merge_json());
    assert_eq!(shared.execution_stats.merge_json()["failure_reasons"]["has_back_edge"].as_u64().unwrap_or(0), 0);
    assert!(on[0].records.len() >= 4);
}

#[test]
fn flat_loop_unbounded_rejects_and_restores_root() {
    if !flat_child("flat_loop_unbounded_rejects_and_restores_root") {
        return;
    }
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let mut frame = make_frame(vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(4),
        Instr::Goto(0),
        Instr::End,
    ]);
    let condition = solver.declare_const(smtlib::Ty::Bool, info());
    frame.vars_mut().insert(test_name(900), UVal::Init(Val::Symbolic(condition)));
    let state = TaskState::new().with_execution_limits(limits(true)).with_region_step_budget(12);
    let queue = Worker::new_lifo();
    let result = region_merge::try_region(
        condition,
        3,
        0,
        TaskId::fresh(),
        &mut Fraction::one(),
        PathTimeout::unlimited(),
        None,
        &SingleForkSink { queue: &queue },
        &mut frame,
        &state,
        &shared,
        &mut solver,
        info(),
    )
    .unwrap();
    assert!(matches!(result, region_merge::RegionResult::Rejected));
    assert_eq!(shared.execution_stats.merge_json()["failures"], 1);
    assert_eq!(solver.transaction_depth(), 0);
    assert_eq!(frame.pc, 0);
    assert!(frame.region_merge_records().is_empty());
    assert!(queue.is_empty());
}

#[test]
fn flat_four_way_top_merge_survives_incompatible_inner_joins() {
    if flat_child("flat_four_way_top_merge_survives_incompatible_inner_joins") {
        super::region_engine_tests::check_symmetric_top_merge(limits(true));
    }
}
