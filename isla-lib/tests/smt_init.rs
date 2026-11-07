use isla_lib::bitvector::b64::B64;
use isla_lib::smt::{self, Config, Context, SmtResult, Solver};
use isla_lib::source_loc::SourceLoc;

// 每种启动场景放进独立进程，避免全局初始化状态在并行测试间相互污染。
#[test]
fn smt_initialization() {
    if let Ok(case) = std::env::var("ISLA_SMT_INIT_CASE") {
        match case.as_str() {
            "missing" => {
                let ctx = Context::new(Config::new());
                let solver = Solver::<B64>::new(&ctx);
                drop(solver);
            }
            "unsupported" => {
                "skip".parse::<smt::Tactic>().unwrap();
            }
            "invalid" => {
                "isla-invalid-tactic".parse::<smt::Tactic>().unwrap();
            }
            "changed" => {
                smt::configure_tastic(smt::Tactic::Qfaufbv);
                smt::configure_tastic(smt::Tactic::Smt);
            }
            "ready" => {
                smt::configure_tastic(smt::Tactic::Qfaufbv);
                smt::configure_tastic(smt::Tactic::Qfaufbv);
                std::thread::scope(|scope| {
                    for _ in 0..4 {
                        scope.spawn(|| {
                            let ctx = Context::new(Config::new());
                            let mut solver = Solver::<B64>::new(&ctx);
                            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
                            solver.assert(smt::smtlib::Exp::Bool(false));
                            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Unsat);
                        });
                    }
                });
            }
            "executor" => {
                use isla_lib::executor::{start_multi, LocalFrame, Run, TaskId, TaskState};
                use isla_lib::ir::{Exp, Instr, Loc, SharedState, Symtab, Ty, Val, RETURN};
                use std::sync::{Arc, Mutex};
                smt::configure_tastic(smt::Tactic::Default);
                let mut symtab = Symtab::new();
                let function = symtab.intern("ztest");
                let shared = SharedState::<B64>::empty(symtab);
                let instructions = [Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), SourceLoc::unknown()), Instr::End];
                let state = TaskState::new();
                for threads in [0, 1, 4] {
                    let frame = LocalFrame::new(function, &[], &Ty::Bool, None, &instructions);
                    let collected = Arc::new(Mutex::new(0usize));
                    start_multi(
                        threads,
                        None,
                        vec![frame.task(TaskId::fresh(), &state)],
                        &shared,
                        collected.clone(),
                        &|_, _, result, _, _, collected| {
                            assert!(matches!(result, Ok((Run::Finished(Val::Bool(true)), _))));
                            *collected.lock().unwrap() += 1;
                        },
                    );
                    assert_eq!(*collected.lock().unwrap(), 1);
                }
            }
            "smt" => {
                smt::configure_tastic(smt::Tactic::Smt);
                let ctx = Context::new(Config::new());
                let mut solver = Solver::<B64>::new(&ctx);
                assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
                solver.assert(smt::smtlib::Exp::Bool(false));
                assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Unsat);
            }
            _ => panic!("未知初始化测试场景：{case}"),
        }
        return;
    }

    for (case, error) in [
        ("missing", Some("SMT 尚未初始化")),
        ("unsupported", Some("不支持的 tactic")),
        ("invalid", Some("不支持的 tactic")),
        ("changed", Some("SMT 已初始化，不能更改 tactic")),
        ("ready", None),
        ("smt", None),
        ("executor", None),
    ] {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "smt_initialization", "--nocapture"])
            .env("ISLA_SMT_INIT_CASE", case)
            .output()
            .unwrap();
        let stderr = String::from_utf8(output.stderr).unwrap();
        if let Some(error) = error {
            assert!(!output.status.success(), "场景 {case} 应在初始化阶段失败");
            assert!(stderr.contains(error), "场景 {case} 缺少诊断 {error}：{stderr}");
        } else {
            assert!(output.status.success(), "场景 {case} 失败：{stderr}");
        }
    }
}

#[test]
fn default_and_explicit_tactics() {
    assert_eq!(smt::Tactic::default(), smt::Tactic::Default);
    assert_eq!("default".parse::<smt::Tactic>().unwrap(), smt::Tactic::Default);
    assert_eq!("qffp".parse::<smt::Tactic>().unwrap(), smt::Tactic::Qffp);
    assert_eq!("qfaufbv".parse::<smt::Tactic>().unwrap(), smt::Tactic::Qfaufbv);
    assert_eq!("smt".parse::<smt::Tactic>().unwrap(), smt::Tactic::Smt);
}
