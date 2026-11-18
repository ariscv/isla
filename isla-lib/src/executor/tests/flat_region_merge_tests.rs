//! 平铺队列的返回关系、覆盖和回退回归；配置在独立子进程冻结。
use super::*;

fn limits(merge: bool) -> ExecutionLimits {
    let mut limits = ExecutionLimits::default().with_path_merging(merge).with_region_global_state(true);
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
fn flat_nested_beyond_recursive_depth() {
    if !flat_child("flat_nested_beyond_recursive_depth") {
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
    assert!(merged[0].records.iter().all(|record| record.depth == 1));
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
fn flat_dead_arm_rejects_and_replays() {
    if !flat_child("flat_dead_arm_rejects_and_replays") {
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
    assert!(merged[0].records.is_empty());
    assert!(shared.execution_stats.merge_json()["failures"].as_u64().unwrap() > 0);
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
