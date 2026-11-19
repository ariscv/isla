//! 独立进程安装冻结选项，避免测试之间共享配置；不设置环境变量。
use super::*;

#[test]
fn prune_constant_branches_modes() {
    for case in ["defer", "no_smt", "ordinary", "skip_checks", "disabled"] {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                &format!("executor::tests::region_merge_tests::prune_constant_branch_tests::prune_constant_{case}"),
                "--ignored",
                "--nocapture",
            ])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{case}: {}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

fn run_case(defer: bool, no_smt: bool, skip_checks: bool, enabled: bool) {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    crate::config::RegionOptions { defer_exit_check: defer, prune_constant_branches: enabled, ..Default::default() }
        .configure();
    crate::smt::configure_solver_options(crate::smt::SolverOptions {
        no_smt,
        skip_branch_checks: skip_checks,
        ..Default::default()
    });
    for constant in [Some(false), Some(true), None] {
        let mut cfg = Config::new();
        cfg.solver_options.no_smt = no_smt;
        cfg.solver_options.skip_branch_checks = skip_checks;
        let context = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&context);
        let input_sym = solver.declare_const(smtlib::Ty::Bool, info());
        let condition = match constant {
            Some(value) => {
                let a = smtlib::Exp::Bits64(B64::new(0x8d0, 32));
                let eq = smtlib::Exp::Eq(Box::new(a.clone()), Box::new(a));
                solver.define_const(if value { eq } else { smtlib::Exp::Not(Box::new(eq)) }, info())
            }
            None => input_sym,
        };
        assert_eq!(solver.structural_bool(&smtlib::Exp::Var(condition)), constant);
        let mut shared = empty_shared_state();
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let simple = vec![
            Instr::Jump(input(1), 3, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::End,
        ];
        // 外层真符号分支启动 defer 区域，内层两个常量分支必须复用具体布尔路径。
        let code = if defer {
            vec![
                Instr::Jump(input(0), 6, info()),
                Instr::Jump(input(1), 4, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                Instr::Goto(10),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
                Instr::Goto(10),
                Instr::Jump(input(1), 9, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                Instr::Goto(10),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
                Instr::End,
            ]
        } else {
            simple
        };
        let mut frame = make_frame(code);
        frame.function_name = TOP_LEVEL_LET;
        frame.vars_mut().insert(test_name(900), UVal::Init(Val::Symbolic(input_sym)));
        frame.vars_mut().insert(test_name(901), UVal::Init(Val::Symbolic(condition)));
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(defer));
        let output = Mutex::new(Vec::new());
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            &shared,
            &output,
            &|_, _, result, _, _, output| match result {
                Ok((Run::Finished(value), _)) => output.lock().unwrap().push(value),
                Err((error, _)) => panic!("合成分支执行失败：{error:?}"),
                _ => panic!("合成分支未正常完成"),
            },
        );
        let values = output.into_inner().unwrap();
        let report = shared.execution_stats.merge_json();
        let folded =
            report["folded_true_conditions"].as_u64().unwrap() + report["folded_false_conditions"].as_u64().unwrap();
        if enabled && constant.is_some() {
            assert_eq!(folded, if defer { 2 } else { 1 }, "{report}");
            assert_eq!(values.len(), 1);
            assert_eq!(values[0], Val::Bool(constant.unwrap()));
            assert_eq!(report["attempts"], if defer { 1 } else { 0 });
            assert_eq!(report["failures"], 0);
        } else {
            assert_eq!(folded, 0, "非恒值或关闭时不得折叠");
            // 关闭预先折叠仍允许查询入口识别恒假的一侧，即使配置关闭 SMT。
            assert_eq!(values.len(), if defer || constant.is_some() { 1 } else { 2 });
            if let Some(value) = constant {
                assert_eq!(values[0], Val::Bool(value));
            }
        }
    }
}

#[test]
#[ignore = "由父测试在独立进程运行"]
fn prune_constant_defer() {
    run_case(true, false, false, true);
}
#[test]
#[ignore = "由父测试在独立进程运行"]
fn prune_constant_no_smt() {
    run_case(false, true, false, true);
}
#[test]
#[ignore = "由父测试在独立进程运行"]
fn prune_constant_ordinary() {
    run_case(false, false, false, true);
}
#[test]
#[ignore = "由父测试在独立进程运行"]
fn prune_constant_skip_checks() {
    run_case(false, false, true, true);
}
#[test]
#[ignore = "由父测试在独立进程运行"]
fn prune_constant_disabled() {
    run_case(false, true, false, false);
}
