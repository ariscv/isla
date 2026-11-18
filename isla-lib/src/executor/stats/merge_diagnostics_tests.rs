//! 只检查通用值形态与诊断边界，不使用模型专用名称。
use super::merge_diagnostics::*;
use crate::bitvector::b64::B64;
use crate::bitvector::BV;
use crate::ir::{Symtab, Ty, UVal, Val};
use crate::primop_util::merge_val;
use crate::smt::{smtlib, Config, Context, Solver};
use crate::source_loc::SourceLoc;
use serde_json::json;

#[test]
fn merge_diagnostics_value_failures_and_paths() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let cond = solver.declare_const(smtlib::Ty::Bool, info);
    let sym = solver.declare_const(smtlib::Ty::BitVec(16), info);
    let mut names = Symtab::new();
    let item = names.intern("Item");
    let data = names.intern("data");
    let cases = [
        (Val::Bits(B64::new(0, 8)), Val::Symbolic(sym), "width_mismatch", ""),
        (Val::I64(0), Val::I64(1), "concrete_required", ""),
        (Val::Vector(vec![]), Val::Vector(vec![Val::Unit]), "vector_length", ""),
        (Val::Bool(false), Val::Unit, "type_mismatch", ""),
        (
            Val::Ctor(item, Box::new(Val::Struct(ahash::HashMap::from_iter([(data, Val::I64(0))])))),
            Val::Ctor(item, Box::new(Val::Struct(ahash::HashMap::from_iter([(data, Val::I64(1))])))),
            "concrete_required",
            "<Item>.data",
        ),
    ];
    for (left, right, difference, path) in cases {
        let before = solver.trace().to_vec().len();
        let trace = ValueTrace::start_for_test();
        assert!(merge_val(cond, &left, &right, &mut solver, info).is_err());
        let failure = trace.finish().expect("实际失败必须有原始递归位置");
        assert_eq!(failure.difference, difference);
        assert_eq!(failure.path_string(&names), path);
        assert_eq!(solver.trace().to_vec().len(), before, "诊断不得声明符号或增加事件");
    }
    // 标签不同本来就可合并；诊断不能凭形态差异制造拒绝。
    let other = names.intern("Empty");
    let trace = ValueTrace::start_for_test();
    assert!(merge_val(
        cond,
        &Val::Ctor(item, Box::new(Val::Unit)),
        &Val::Ctor(other, Box::new(Val::Unit)),
        &mut solver,
        info
    )
    .is_ok());
    assert!(trace.finish().is_none());
    let raw = describe_uval(Some(&UVal::<B64>::Uninit(&Ty::I64)), &solver, &names);
    assert_eq!(raw["raw"], "Uninit");
    assert_eq!(raw["decl_type"], "I64");
    assert_eq!(describe_uval(None::<&UVal<B64>>, &solver, &names)["raw"], "Missing");
    assert!(describe_value(None::<&Val<B64>>, &solver, &names).is_null(), "尚未进入值合并时不能编造初始化后形态");
}

#[test]
fn merge_diagnostics_off_sampling_and_summary_limits() {
    let record = json!({"schema":1,"kind":"merge_value_reject","stage":"merge_states",
        "origin":{"function":"caller","pc":2},"at":{"function":"caller","pc":2},
        "slot":{"space":"vars","name":"tmp"},"path":"", "left":{"shape":"I64"},
        "right":{"shape":"I64"},"difference":"concrete_required"});
    let mut off = DiagnosticCounts::new(Mode::Off);
    for _ in 0..5 {
        assert!(off.record(&record).is_none());
    }
    assert!(off.summary().is_none());
    let mut detail = DiagnosticCounts::new(Mode::Detail);
    for i in 0..5 {
        assert_eq!(detail.record(&record).is_some(), i < 3);
    }
    let summary = detail.summary().unwrap();
    assert_eq!(summary["differences"]["concrete_required"], 5);
    assert_eq!(summary["details_emitted"], 3);
    assert_eq!(summary["details_suppressed"], 2);
    let mut summary_only = DiagnosticCounts::new(Mode::Summary);
    assert!(summary_only.record(&record).is_none());
    assert_eq!(summary_only.summary().unwrap()["total"], 1);
    for index in 0..4200 {
        let mut r = record.clone();
        r["slot"]["name"] = json!(format!("slot_{index}"));
        detail.record(&r);
    }
    let summary = detail.summary().unwrap();
    assert_eq!(summary["keys"].as_array().unwrap().len(), 4096);
    assert!(summary["other"].as_u64().unwrap() > 0);
    assert!(summary["details_emitted"].as_u64().unwrap() <= 1000);
}

// 子进程隔离进程级开关与信号，不干扰原有并行测试。
#[test]
fn merge_diagnostics_snapshot_child() {
    let Ok(mode) = std::env::var("MERGE_DIAG_SNAPSHOT_CHILD") else { return };
    configure(&mode).unwrap();
    let stats = std::sync::Arc::new(super::ExecutionStats::new(false));
    let reporter = SnapshotReporter::start(stats, std::time::Duration::from_millis(20));
    emit(json!({"stage":"merge_states","difference":"missing_arm","reason":"incompatible_state"}));
    if enabled() {
        record_depth(23, 7, 44);
        record_depth(23, 9, 48);
        record_deferred_query("range_proof", SourceLoc::unknown());
    }
    if std::env::var_os("MERGE_DIAG_SIGNAL_CHILD").is_some() {
        println!("ready");
        use std::io::Write;
        std::io::stdout().flush().unwrap();
        std::thread::sleep(std::time::Duration::from_secs(5));
        panic!("SIGTERM 未保持默认退出行为");
    }
    std::thread::sleep(std::time::Duration::from_millis(70));
    drop(reporter);
}

#[test]
fn merge_diagnostics_periodic_output_and_off() {
    for mode in ["summary", "off"] {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["merge_diagnostics_snapshot_child", "--nocapture", "--test-threads=1"])
            .env("MERGE_DIAG_SNAPSHOT_CHILD", mode)
            .output()
            .unwrap();
        assert!(output.status.success());
        let text = String::from_utf8(output.stderr).unwrap();
        let summaries: Vec<serde_json::Value> = text
            .lines()
            .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
            .filter(|record| record["kind"] == "merge_value_summary")
            .collect();
        if mode == "off" {
            assert!(text.is_empty(), "关闭时不得输出诊断：{text}");
        } else {
            assert!(!summaries.is_empty(), "周期快照未输出：{text}");
            let rows: Vec<serde_json::Value> =
                text.lines().filter_map(|line| serde_json::from_str(line).ok()).collect();
            let depth = rows.iter().find(|row| row["kind"] == "region_depth_summary").unwrap();
            assert_eq!(depth["depths"]["23"], 2);
            assert_eq!(depth["max_depth"], 23);
            assert_eq!(depth["max_call_depth"], 9);
            assert_eq!(depth["max_transaction_depth"], 48);
            let blocked = rows.iter().find(|row| row["kind"] == "region_deferred_query_summary").unwrap();
            assert_eq!(blocked["queries"][0]["count"], 1);
            assert!(text
                .lines()
                .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
                .any(|row| row["kind"] == "merge_timing_summary" && row["trigger"] == "periodic"));
            assert!(summaries.iter().any(|s| s["total"] == 1 && s["trigger"] == "periodic"));
            // 多次快照是累计值，输出本身不能清空计数。
            assert!(summaries.iter().all(|s| s["total"] == 1));
        }
    }
}

#[test]
fn merge_diagnostics_sigterm_flushes_before_exit() {
    use std::io::BufRead;
    use std::os::unix::process::ExitStatusExt;
    let mut child = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["merge_diagnostics_snapshot_child", "--nocapture", "--test-threads=1"])
        .env("MERGE_DIAG_SNAPSHOT_CHILD", "summary")
        .env("MERGE_DIAG_SIGNAL_CHILD", "1")
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let mut stdout = std::io::BufReader::new(child.stdout.take().unwrap());
    let mut line = String::new();
    loop {
        assert!(stdout.read_line(&mut line).unwrap() > 0, "子进程未就绪");
        if line.contains("ready") {
            break;
        }
        line.clear();
    }
    assert_eq!(unsafe { libc::kill(child.id() as i32, libc::SIGTERM) }, 0);
    let output = child.wait_with_output().unwrap();
    assert_eq!(output.status.signal(), Some(libc::SIGTERM));
    let text = String::from_utf8(output.stderr).unwrap();
    assert!(
        text.lines()
            .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
            .any(|s| s["kind"] == "merge_value_summary" && s["total"] == 1 && s["trigger"] == "signal"),
        "{text}"
    );
}
