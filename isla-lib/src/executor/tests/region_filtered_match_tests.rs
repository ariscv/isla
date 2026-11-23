use super::super::nested_merge_failure_tests::{strategies, Strategy};
use super::*;
use crate::config::{ExecutionLimitsConfig, RegionOptions};
use crate::memory::Memory;

fn limits(shared: &SharedState<B64>, merge: bool, filter: bool) -> ExecutionLimits {
    let config = ExecutionLimitsConfig { filter_match_failures: filter, ..Default::default() };
    ExecutionLimits::default().with_config(&config, &shared.symtab).with_path_merging(merge)
}

fn outcomes(
    program: Vec<Instr<Name, B64>>,
    shared: &SharedState<'static, B64>,
    merge: bool,
    filter: bool,
) -> Vec<&'static str> {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let mut frame = make_frame(program);
    frame.function_name = TOP_LEVEL_LET;
    let symbol = solver.declare_const(smtlib::Ty::Bool, info());
    frame.vars_mut().insert(test_name(900), UVal::Init(Val::Symbolic(symbol)));
    let state = TaskState::new().with_execution_limits(limits(shared, merge, filter));
    let output = Mutex::new(Vec::new());
    start_single(
        frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
        shared,
        &output,
        &|_, _, result, _, _, output| {
            let label = match result {
                Ok((Run::Dead, _)) => "dead",
                Ok((Run::Finished(Val::Bool(true)), _)) => "return",
                Ok((Run::Exit, _)) => "explicit_exit",
                Err((ExecError::MatchFailure(_), _)) => "match_failure",
                Err((ExecError::AssertionFailure(..), _)) => "assertion_failure",
                _ => panic!("fixture 返回意外结果"),
            };
            output.lock().unwrap().push(label);
        },
    );
    let mut output = output.into_inner().unwrap();
    output.sort_unstable();
    output
}

fn returns() -> Instr<Name, B64> {
    Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info())
}

fn failure() -> Instr<Name, B64> {
    Instr::Exit(ExitCause::MatchFailure, info())
}

#[test]
fn region_filtered_match_plain_and_opt_out() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let program = vec![Instr::Jump(input(0), 3, info()), returns(), Instr::End, failure()];
    assert_eq!(outcomes(program.clone(), &shared, false, false), ["match_failure", "return"]);
    assert_eq!(outcomes(program.clone(), &shared, true, false), ["match_failure", "return"]);
    assert_eq!(
        shared.execution_stats.arm_unsupported_json(&shared.symtab)["top"][0]["reason"],
        "SpeculativeRejectReason::Exit"
    );
    assert_eq!(outcomes(program, &shared, false, true), ["dead", "return"]);
    assert_eq!(shared.execution_stats.merge_json()["filtered_match_failure_paths"], 1);
    for (cause, outcome) in [(ExitCause::Explicit, "explicit_exit"), (ExitCause::AssertionFailure, "assertion_failure")]
    {
        assert_eq!(outcomes(vec![Instr::Exit(cause, info())], &shared, false, true), [outcome]);
    }
}

fn check_merge(strategy: Strategy) {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let function = shared.symtab.intern("zonly_failed_match");
    shared.functions.insert(function, (Vec::new(), &Ty::Bool, Box::leak(vec![failure()].into_boxed_slice())));
    let program = vec![
        Instr::Jump(input(0), 3, info()),
        returns(),
        Instr::Goto(7),
        Instr::Jump(input(1), 6, info()),
        returns(),
        Instr::Goto(7),
        Instr::Call(Loc::Id(RETURN), false, function, Vec::new(), info()),
        Instr::End,
    ];
    let run = |program, merge| {
        let mut limits = limits(&shared, merge, true);
        if merge {
            limits = strategy.apply(limits);
        }
        paths_with_state(program, &shared, 2, limits, Memory::new(), |_| ())
    };
    let forked = run(program.clone(), false);
    let merged = run(program, true);
    assert_eq!(equivalent_paths(&forked, &merged, 2, false), (2, 1));
    assert!(merged[0].records.iter().any(|record| record.branch_pc == 0));
    assert!(merged[0].records.iter().any(|record| record.branch_pc == 3 && record.parent_record.is_some()));
    // 这个指令片段复用了测试入口名，清掉前一个程序的区域缓存。
    shared.function_regions.lock().unwrap().clear();
    let both = vec![Instr::Jump(input(0), 2, info()), failure(), failure()];
    assert_eq!(equivalent_paths(&run(both.clone(), false), &run(both, true), 2, false), (0, 0));
    assert_eq!(shared.execution_stats.merge_json()["filtered_match_failure_arms"], 3);
    shared.execution_stats.print(&shared);
}

#[test]
fn region_filtered_match_merge_in_both_exit_modes() {
    let test = concat!(module_path!(), "::region_filtered_match_merge_in_both_exit_modes");
    let name = test.split_once("::").unwrap().1;
    let args = ["--exact", name, "--nocapture", "--test-threads=1"];
    let actual: Vec<_> = std::env::args().skip(1).collect();
    if actual.starts_with(&args.map(str::to_owned)) {
        let defer_exit_check = actual.iter().any(|arg| arg == "--include-ignored");
        RegionOptions { defer_exit_check, ..Default::default() }.configure();
        stats::merge_diagnostics::configure("detail").unwrap();
        for strategy in strategies() {
            check_merge(strategy);
        }
        return;
    }
    for deferred in [false, true] {
        let mut child = std::process::Command::new(std::env::current_exe().unwrap());
        child.args(args);
        if deferred {
            child.arg("--include-ignored");
        }
        let output = child.output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "defer={deferred}: {stdout}\n{stderr}");
        assert!(stderr.contains("\"kind\":\"filtered_match_failure_arm\""));
        assert!(stderr.contains("\"kind\":\"filtered_match_failure_summary\""));
    }
}
