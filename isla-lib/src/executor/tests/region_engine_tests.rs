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
