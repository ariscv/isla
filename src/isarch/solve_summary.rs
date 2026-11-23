//! 求解产物的执行范围摘要；正常结束不等于源码控制流已全覆盖。
use isla_lib::executor::stats::solver_failures::SolverPathDrops;
use serde::Serialize;
use serde_json::{json, Value};

#[derive(Default, Clone, Serialize)]
#[serde(rename_all = "kebab-case")]
pub(super) struct SolveSummary {
    #[serde(skip)]
    pub solver_path_drops: SolverPathDrops,
    pub uncertified: bool,
    pub sampled_paths: usize,
    pub errors: usize,
    pub failure_reasons: std::collections::BTreeMap<isla_lib::executor::SpeculativeRejectReason, usize>,
    pub execution_timeouts: usize,
    pub smt_timeouts: usize,
    pub unfinished_paths: usize,
    pub model_exception_paths: usize,
    pub filtered_model_exception_paths: usize,
    pub filtered_model_exception_sites: std::collections::BTreeMap<String, usize>,
    pub assertion_filtered_paths: usize,
    pub omitted_cases: usize,
    pub model_query_timeouts: usize,
    pub encoding_filtered_paths: usize,
    pub pending_batches: usize,
    pub applicable_batches: usize,
    pub inapplicable_batches: usize,
}

impl SolveSummary {
    pub fn status(&self) -> &'static str {
        if self.solver_path_drops.count > 0
            || self.uncertified
            || self.sampled_paths
                + self.errors
                + self.unfinished_paths
                + self.omitted_cases
                + self.model_query_timeouts
                + self.pending_batches
                > 0
        {
            "partial"
        } else if self.inapplicable_batches > 0 && self.applicable_batches == 0 {
            "not-applicable"
        } else {
            "finished"
        }
    }

    pub fn json(&self) -> Value {
        let mut value = serde_json::to_value(self).unwrap();
        value["status"] = json!(self.status());
        if self.status() == "not-applicable" {
            value["reason"] = json!("no-encoding-in-current-config");
            value["scope"] = json!("current-config-prestate-and-input-domain");
        }
        value["model-coverage"] = json!("not-measured");
        if self.solver_path_drops.count > 0 {
            value["valid"] = json!(false);
            value["invalid_reasons"] = json!(["solver_timeout_dropped_paths"]);
            value["solver_timeout_dropped_paths"] = json!(self.solver_path_drops.count);
            value["solver_timeout_drop_locations"] = json!(self.solver_path_drops.first_locations);
            value["invalid_message"] = json!(solver_path_drop_message(&self.solver_path_drops));
        }
        value
    }

    pub fn record_filtered_model_exception(&mut self, site: String) {
        self.filtered_model_exception_paths += 1;
        *self.filtered_model_exception_sites.entry(site).or_default() += 1;
    }

    pub fn print_model_exception_filter(&self) {
        if self.filtered_model_exception_paths > 0 {
            eprintln!(
                "[MODEL_EXCEPTION_FILTER] {}",
                serde_json::json!({
                    "filtered-model-exception-paths": self.filtered_model_exception_paths,
                    "filtered-model-exception-sites": self.filtered_model_exception_sites,
                })
            );
        }
    }

    pub fn merge(&mut self, other: &Self) {
        self.solver_path_drops.merge(&other.solver_path_drops);
        self.uncertified |= other.uncertified;
        self.filtered_model_exception_paths += other.filtered_model_exception_paths;
        for (site, count) in &other.filtered_model_exception_sites {
            *self.filtered_model_exception_sites.entry(site.clone()).or_default() += count;
        }
        self.applicable_batches += other.applicable_batches;
        self.inapplicable_batches += other.inapplicable_batches;
        self.sampled_paths += other.sampled_paths;
        self.errors += other.errors;
        for (reason, count) in &other.failure_reasons {
            *self.failure_reasons.entry(*reason).or_default() += count;
        }
        self.execution_timeouts += other.execution_timeouts;
        self.smt_timeouts += other.smt_timeouts;
        self.unfinished_paths += other.unfinished_paths;
        self.model_exception_paths += other.model_exception_paths;
        self.assertion_filtered_paths += other.assertion_filtered_paths;
        self.omitted_cases += other.omitted_cases;
        self.model_query_timeouts += other.model_query_timeouts;
        self.encoding_filtered_paths += other.encoding_filtered_paths;
    }
}

pub const SOLVER_TIMEOUT_DROPPED_PATHS_EXIT_CODE: i32 = 66;

fn solver_path_drop_message(drops: &SolverPathDrops) -> String {
    let first = drops.first_locations.first().expect("丢弃统计必须保存首个位置");
    format!(
        "结果作废：求解器超时或 Unknown 导致 {} 条路径被丢弃（首个位置 {}，IR {}@{}，用途 {}）。请检查并修复后重跑。",
        drops.count, first.sail_location, first.function, first.pc, first.purpose,
    )
}

pub(super) fn exploration_exit_code(code: i32, drops: &SolverPathDrops) -> i32 {
    if drops.count == 0 {
        return code;
    }
    eprintln!("{}", solver_path_drop_message(drops));
    match code {
        0 | 1 => SOLVER_TIMEOUT_DROPPED_PATHS_EXIT_CODE,
        _ => code,
    }
}

/// 记录实际命令行及输入字节哈希；不把分支名称当成编译来源证明。
pub(super) fn input_manifest() -> Value {
    use sha2::{Digest, Sha256};
    use std::collections::BTreeMap;
    use std::io::Read;
    let args: Vec<String> = std::env::args().collect();
    let mut inputs = BTreeMap::new();
    for (index, arg) in args.iter().enumerate() {
        let (name, path) = match arg.split_once('=') {
            Some((name @ ("--arch" | "--config" | "--execution-limits-config"), path)) => (name, path),
            _ if matches!(arg.as_str(), "-A" | "--arch" | "-C" | "--config" | "--execution-limits-config") => {
                (arg.as_str(), args.get(index + 1).expect("已解析选项必须具有参数").as_str())
            }
            _ => continue,
        };
        let mut file = std::fs::File::open(path).expect("求解输入文件必须可读取");
        let mut hasher = Sha256::new();
        let mut buffer = [0u8; 65536];
        loop {
            let count = file.read(&mut buffer).expect("读取求解输入失败");
            if count == 0 {
                break;
            }
            hasher.input(&buffer[..count]);
        }
        inputs.insert(name, json!({"path":path, "sha256":format!("{:x}", hasher.result())}));
    }
    json!({"command":args, "inputs":inputs})
}

/// 与求解摘要一同收尾；保持默认日志不变，统计使用单行 JSON 便于机器读取。
pub(super) fn print_execution_stats<B>(shared_state: &isla_lib::ir::SharedState<'_, B>) {
    shared_state.execution_stats.print(shared_state);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn solver_timeout_exit_and_invalid_summary() {
        const NAME: &str = "isarch::solve_summary::tests::solver_timeout_exit_and_invalid_summary";
        let args = ["--exact", NAME, "--nocapture", "--test-threads=1"];
        if std::env::args().skip(1).eq(args) {
            use isla_lib::executor::stats::solver_failures::SolverPathDrop;
            let mut summary = SolveSummary::default();
            assert_eq!(exploration_exit_code(0, &summary.solver_path_drops), 0);
            assert_eq!(exploration_exit_code(1, &summary.solver_path_drops), 1);
            assert!(summary.json().get("valid").is_none());
            summary.solver_path_drops = SolverPathDrops {
                count: 1,
                first_locations: vec![SolverPathDrop {
                    path_count: 1,
                    function: "access_check".into(),
                    pc: 3,
                    path_signature: 1,
                    sail_location: "test.sail:7".into(),
                    source_loc: isla_lib::source_loc::SourceLoc::new(0, 7, 0, 7, 3),
                    purpose: "range_proof".into(),
                    reason: "unknown_solver".into(),
                    reason_unknown: None,
                    seconds: 5.0,
                    limit_seconds: Some(5.0),
                }],
            };
            assert_eq!(summary.status(), "partial");
            assert_eq!(exploration_exit_code(1, &summary.solver_path_drops), SOLVER_TIMEOUT_DROPPED_PATHS_EXIT_CODE);
            for code in [86, 101, 124, 125, 143] {
                assert_eq!(exploration_exit_code(code, &summary.solver_path_drops), code);
            }
            println!("SUMMARY {}", summary.json());
            std::process::exit(exploration_exit_code(0, &summary.solver_path_drops));
        }
        let result = std::process::Command::new(std::env::current_exe().unwrap()).args(args).output().unwrap();
        assert_eq!(result.status.code(), Some(SOLVER_TIMEOUT_DROPPED_PATHS_EXIT_CODE));
        let stderr = String::from_utf8(result.stderr).unwrap();
        assert!(stderr.contains("结果作废：求解器超时或 Unknown 导致 1 条路径被丢弃"));
        assert!(
            stderr.contains("test.sail:7") && stderr.contains("range_proof") && stderr.contains("请检查并修复后重跑")
        );
        let stdout = String::from_utf8(result.stdout).unwrap();
        let json: Value = serde_json::from_str(stdout.split_once("SUMMARY ").unwrap().1.trim()).unwrap();
        assert_eq!(json["valid"], false);
        assert_eq!(json["invalid_reasons"], json!(["solver_timeout_dropped_paths"]));
        assert_eq!(json["solver_timeout_dropped_paths"], 1);
        assert_eq!(json["solver_timeout_drop_locations"][0]["limit_seconds"], 5.0);
    }

    #[test]
    fn filtered_model_exception_sites_merge_without_hiding_failures() {
        let mut summary = SolveSummary::default();
        summary.record_filtered_model_exception("Generic: file.sail:7".into());
        summary.merge(&summary.clone());
        assert_eq!(summary.filtered_model_exception_paths, 2);
        assert_eq!(summary.filtered_model_exception_sites["Generic: file.sail:7"], 2);
        assert_eq!(summary.status(), "finished");
        summary.errors = 1;
        assert_eq!(summary.status(), "partial");
        summary.errors = 0;
        summary.unfinished_paths = 1;
        assert_eq!(summary.status(), "partial");
    }

    #[test]
    fn not_applicable_requires_empty_domain_without_errors_or_pending_work() {
        let mut summary = SolveSummary { inapplicable_batches: 1, ..SolveSummary::default() };
        assert_eq!(summary.status(), "not-applicable");
        assert_eq!(summary.json()["reason"], "no-encoding-in-current-config");
        summary.errors = 1;
        assert_eq!(summary.status(), "partial");
        summary.errors = 0;
        summary.pending_batches = 1;
        assert_eq!(summary.status(), "partial");
        summary.pending_batches = 0;
        summary.merge(&SolveSummary { applicable_batches: 1, ..SolveSummary::default() });
        assert_eq!(summary.status(), "finished");
        assert!(summary.json().get("reason").is_none());
    }
}

#[cfg(test)]
mod no_smt_tests {
    use super::*;
    #[test]
    fn uncertified_is_partial_without_execution_errors() {
        let mut summary = SolveSummary { uncertified: true, applicable_batches: 1, ..Default::default() };
        assert_eq!(summary.status(), "partial");
        assert_eq!(summary.json()["uncertified"], true);
        summary.merge(&SolveSummary::default());
        assert_eq!(summary.status(), "partial");
    }
}
