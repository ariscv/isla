//! 共享单臂关闭边界的行为契约：先固定旧递归行为，再抽取实现。
use super::*;
use crate::executor::region_engine;

#[test]
fn engine_dead_arm_restores_cycles_and_keeps_sibling() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let shared = empty_shared_state();
    let frame = make_frame(vec![Instr::End]);
    let guard = solver.declare_const(smtlib::Ty::Bool, info());
    solver.start_transaction();
    let sibling = solver.start_transaction_with_guard(Some(smtlib::Exp::Not(Box::new(smtlib::Exp::Var(guard)))));
    solver.cycle_count();
    assert!(region_engine::close_arm(Ok(Run::Suspended), sibling, &frame, &shared, &mut solver, info()).unwrap());
    let dead = solver.start_transaction_with_guard(Some(smtlib::Exp::Var(guard)));
    solver.cycle_count();
    assert!(!region_engine::close_arm(Ok(Run::Dead), dead, &frame, &shared, &mut solver, info()).unwrap());
    assert_eq!(solver.get_cycle_count(), 1, "只恢复死臂自己增加的周期");
    solver.commit_transaction();
    assert_eq!(solver.trace().to_vec().iter().filter(|e| matches!(e, Event::Cycle)).count(), 1);
    assert_eq!(solver.check_sat_with(&smtlib::Exp::Var(guard), info()), SmtResult::Unsat);
}

#[test]
fn engine_close_preserves_earlier_obligation_after_later_exit() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let shared = empty_shared_state();
    let frame = make_frame(vec![Instr::End]);
    let guard = solver.declare_const(smtlib::Ty::Bool, info());
    let root = solver.start_transaction();
    solver.with_deferred_region_queries(|solver| {
        let first = solver.start_transaction_with_guard(Some(smtlib::Exp::Var(guard)));
        solver.defer_assertion(smtlib::Exp::Bool(false), info());
        assert!(region_engine::close_arm(Ok(Run::Suspended), first, &frame, &shared, solver, info()).unwrap());
        let later = solver.start_transaction_with_guard(Some(smtlib::Exp::Not(Box::new(smtlib::Exp::Var(guard)))));
        assert!(!region_engine::close_arm(Ok(Run::Dead), later, &frame, &shared, solver, info()).unwrap());
        solver.assert_region_exit(smtlib::Exp::Bool(false));
        assert_eq!(solver.check_deferred_assertions(info()), Some(SmtResult::Sat), "后序正常域不能抹去前序错误");
    });
    solver.rollback_transaction(root);
}

#[test]
fn engine_close_rejects_non_assertion_failure_without_dropping_arm() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let shared = empty_shared_state();
    let frame = make_frame(vec![Instr::End]);
    solver.start_transaction();
    let tx = solver.start_transaction_with_guard(Some(smtlib::Exp::Bool(true)));
    let result = region_engine::close_arm(
        Err(ExecError::AssertionFailure(None, info())),
        tx,
        &frame,
        &shared,
        &mut solver,
        info(),
    );
    assert!(matches!(
        result,
        Err(ExecError::SpeculativeReject { reason: SpeculativeRejectReason::SymbolicAssertion, .. })
    ));
    assert_eq!(solver.transaction_depth(), 1);
}

#[test]
fn loop_dependencies_keep_both_children_and_outer_completion() {
    use crate::executor::region_engine::LoopDependencies;
    let (mut graph, root) = LoopDependencies::new("入口");
    let then_arm = graph.attach(root, 0, "先到出口");
    let else_arm = graph.attach(root, 1, "继续轮次");
    let nested = graph.attach(else_arm, 0, "嵌套出口");
    assert!(!graph.can_complete(root));
    assert_eq!(graph.ancestors(nested).copied().collect::<Vec<_>>(), ["嵌套出口", "继续轮次", "入口"]);
    assert_eq!(graph.complete(then_arm), ("先到出口", Some((root, 0))));
    assert!(!graph.can_complete(root));
    assert_eq!(graph.complete(nested), ("嵌套出口", Some((else_arm, 0))));
    assert_eq!(graph.complete(else_arm), ("继续轮次", Some((root, 1))));
    assert_eq!(graph.complete(root), ("入口", None));
}

/// 四路顶层只有返回常量不同；各路内有一个必然不能合并的字符串汇合。
#[test]
fn region_four_way_top_merge_survives_incompatible_inner_joins() {
    check_symmetric_top_merge(ExecutionLimits::default().with_path_merging(true));
}

#[test]
fn region_four_way_top_merge_survives_incompatible_inner_joins_deferred() {
    if !run_in_diagnostics_process(concat!(
        module_path!(),
        "::region_four_way_top_merge_survives_incompatible_inner_joins_deferred"
    )) {
        return;
    }
    crate::config::RegionOptions { defer_exit_check: true, lazy_z3_scope: true, ..Default::default() }.configure();
    check_symmetric_top_merge(ExecutionLimits::default().with_path_merging(true));
}

#[test]
fn region_four_way_top_merge_honors_explicit_fragment_limit() {
    let mut limits = ExecutionLimits::default().with_path_merging(true);
    limits.max_region_fragments = Some(1);
    check_symmetric_top_merge(limits);
}

pub(super) fn check_symmetric_top_merge(mut limits: ExecutionLimits) {
    // 让内层活跃字符串阻止局部合并，检查外层可以继续合并。
    limits.merge_concrete_values = false;
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let text = test_name(1900);
    let observed = test_name(1901);
    let mut program = vec![
        Instr::Init(text, Ty::String, Exp::String("初态".into()), info()),
        Instr::Init(observed, Ty::String, Exp::String("初态".into()), info()),
    ];
    let top = program.len();
    let mut inner_pcs = Vec::new();
    let mut exits = Vec::new();
    fn emit(
        program: &mut Vec<Instr<Name, B64>>,
        text: Name,
        observed: Name,
        level: usize,
        value: u64,
        inner_pcs: &mut Vec<usize>,
        exits: &mut Vec<usize>,
    ) {
        let branch = program.len();
        let condition = input(level as u32);
        program.push(Instr::Jump(condition.clone(), 0, info()));
        if level == 2 {
            inner_pcs.push(branch);
            program.push(Instr::Copy(Loc::Id(text), Exp::String("左".into()), info()));
            let skip = program.len();
            program.push(Instr::Goto(0));
            let right = program.len();
            program[branch] = Instr::Jump(condition, right, info());
            program.push(Instr::Copy(Loc::Id(text), Exp::String("右".into()), info()));
            program[skip] = Instr::Goto(program.len());
            program.push(Instr::Copy(Loc::Id(observed), Exp::Id(text), info()));
            program.push(Instr::Copy(Loc::Id(text), Exp::String("清理".into()), info()));
            program.push(Instr::Copy(Loc::Id(observed), Exp::String("清理".into()), info()));
            program.push(Instr::Copy(Loc::Id(RETURN), Exp::I128(i128::from(value)), info()));
            exits.push(program.len());
            program.push(Instr::Goto(0));
        } else {
            emit(program, text, observed, level + 1, value, inner_pcs, exits);
            program[branch] = Instr::Jump(condition, program.len(), info());
            emit(program, text, observed, level + 1, value | (1 << level), inner_pcs, exits);
        }
    }
    emit(&mut program, text, observed, 0, 0, &mut inner_pcs, &mut exits);
    let exit = program.len();
    for pc in exits {
        program[pc] = Instr::Goto(exit);
    }
    program.push(Instr::End);
    let plain = paths(program.clone(), &shared, 3, false);
    let limited = limits.max_region_fragments == Some(1);
    let merged = paths_with_state(program, &shared, 3, limits, crate::memory::Memory::new(), |_| ());
    super::loop_segment_tests::equivalent_scalar_paths(&plain, &merged, 3);
    assert_eq!(plain.len(), 8, "四路中的字符串分支都须可达");
    if limited {
        assert!(
            shared.execution_stats.merge_json()["failure_reasons"]["SpeculativeRejectReason::FragmentLimit"]
                .as_u64()
                .unwrap_or(0)
                > 0
        );
        assert!(merged.len() > 1, "超限不能截断或无视普通分叉");
        return;
    }
    assert_eq!(merged.len(), 1, "顶层应在自己的出口合并八个片段：{}", shared.execution_stats.merge_json());
    let records = &merged[0].records;
    assert!(
        records.iter().any(|r| r.branch_pc == top && r.outcome == RegionRecordOutcome::Merged),
        "顶层必须实际完成合并"
    );
    assert!(!records.iter().any(|r| inner_pcs.contains(&r.branch_pc)), "内层失败不能生成成功记录");
}

#[test]
fn incompatible_root_two_arrivals_keep_the_completed_child() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    for strategy in [crate::config::MergeStrategy::Recursive, crate::config::MergeStrategy::Flat] {
        let shared = empty_shared_state();
        let [text, chosen, ignored, matched] = [1920, 1921, 1922, 1923].map(test_name);
        let calls = Arc::new(AtomicUsize::new(0));
        let observe = Arc::clone(&calls);
        let copy = |name, exp| Instr::Copy(Loc::Id(name), exp, info());
        let program = vec![
            Instr::Decl(text, Ty::String, info()),
            Instr::Decl(chosen, Ty::Bool, info()),
            Instr::Decl(ignored, Ty::Unit, info()),
            Instr::Decl(matched, Ty::Bool, info()),
            Instr::Jump(input(0), 8, info()),
            copy(text, Exp::String("其他".into())),
            copy(chosen, Exp::Bool(false)),
            Instr::Goto(14),
            Instr::Jump(input(1), 11, info()),
            copy(chosen, Exp::Bool(false)),
            Instr::Goto(12),
            copy(chosen, Exp::Bool(true)),
            Instr::PrimopReset(
                Loc::Id(ignored),
                Arc::new(move |_, _, solver| {
                    observe.fetch_add(1, Ordering::Relaxed);
                    solver.cycle_count();
                    Ok(Val::Unit)
                }),
                primop::Effect::Pure,
                info(),
            ),
            copy(text, Exp::String("进入".into())),
            Instr::PrimopBinary(
                Loc::Id(matched),
                primop::binary_primops()["eq_string"],
                Exp::Id(text),
                Exp::String("其他".into()),
                info(),
            ),
            copy(RETURN, Exp::Call(Op::Or, vec![Exp::Id(chosen), Exp::Id(matched)])),
            Instr::End,
        ];
        let plain = paths(program.clone(), &shared, 2, false);
        calls.store(0, Ordering::Relaxed);
        let mut limits = ExecutionLimits::default().with_path_merging(true);
        limits.merge_concrete_values = false;
        limits.merge_strategy = strategy;
        let merged = paths_with_state(program, &shared, 2, limits, crate::memory::Memory::new(), |_| ());
        assert_eq!(equivalent_paths(&plain, &merged, 2, true), (3, 2));
        assert_eq!(calls.load(Ordering::Relaxed), 1, "两个不兼容组应保留已完成子区域的状态");
        let child = merged
            .iter()
            .find(|path| path.records.iter().any(|record| record.branch_pc == 8))
            .expect("根区挑选组时不能丢弃已完成的子区域");
        assert_eq!(child.events.iter().filter(|event| matches!(event, Event::Cycle)).count(), 1);
        assert!(merged.iter().all(|path| path.records.iter().any(|record| record.branch_pc == 4)));
    }
}
