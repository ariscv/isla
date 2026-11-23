use super::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

pub(super) fn panic_message(run: impl FnOnce()) -> String {
    let payload = catch_unwind(AssertUnwindSafe(run)).expect_err("应触发 panic");
    payload.downcast_ref::<String>().unwrap().clone()
}

pub(super) fn with_solver_dead<T>(run: impl FnOnce() -> T) -> T {
    crate::smt::test_queries::with_solver_options(
        crate::smt::SolverOptions { on_unknown: crate::config::PathFailureAction::Dead, ..Default::default() },
        run,
    )
}

#[test]
fn unknown_z3_panics_for_one_or_both_branch_sides() {
    let mut shared = empty_shared_state();
    shared.symtab.set_files(vec!["branch.sail"]);
    let source = SourceLoc::new(0, 7, 3, 7, 9);
    let flag = test_name(100);
    let program = vec![Instr::Decl(flag, Ty::Bool, info()), Instr::Jump(Exp::Id(flag), 2, source), Instr::End];
    for queries in [
        vec![Some(z3_sys::Z3_L_UNDEF)],
        vec![None, Some(z3_sys::Z3_L_UNDEF)],
        vec![Some(z3_sys::Z3_L_UNDEF), Some(z3_sys::Z3_L_UNDEF)],
    ] {
        let message = panic_message(|| {
            crate::smt::test_queries::with_results(queries, || {
                run_all_with_shared_bindings(
                    program.clone(),
                    ExecutionLimits::default(),
                    &shared,
                    RegisterBindings::new(),
                    Bindings::default(),
                );
            });
        });
        for detail in
            ["pc=1", "branch.sail:7", "branch_feasibility", "reason=unknown_z3", "elapsed=", "limit=", "path_depth="]
        {
            assert!(message.contains(detail), "{message}");
        }
    }
    assert_eq!(shared.execution_stats.solver_path_drop_count(), 0);
}

#[test]
fn path_timeout_panics_before_the_next_instruction() {
    let mut shared = empty_shared_state();
    shared.symtab.set_files(vec!["timeout.sail"]);
    let source = SourceLoc::new(0, 5, 1, 5, 5);
    let frame = make_frame(vec![Instr::Copy(Loc::Id(RETURN), Exp::Unit, source), Instr::End]);
    let state = TaskState::new();
    for no_smt in [false, true] {
        let message = panic_message(|| {
            crate::smt::test_queries::with_solver_options(
                crate::smt::SolverOptions { no_smt, ..Default::default() },
                || {
                    start_single_with_timeout(
                        frame.task_with_checkpoint(TaskId::fresh(), &state, Checkpoint::new()),
                        PathTimeout::from_seconds(Some(0)),
                        &shared,
                        &(),
                        &|_, _, _, _, _, _| (),
                    );
                },
            );
        });
        for detail in
            ["reason=path_timeout", "pc=0", "timeout.sail:5", "path_execution", "elapsed=", "limit=", "path_depth=0"]
        {
            assert!(message.contains(detail), "{message}");
        }
    }
}
