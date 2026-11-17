//! 求解产物的执行范围摘要；正常结束不等于源码控制流已全覆盖。
use serde::Serialize;
use serde_json::{json, Value};

#[derive(Default, Clone, Serialize)]
#[serde(rename_all = "kebab-case")]
pub(super) struct SolveSummary {
    pub uncertified: bool,
    pub sampled_paths: usize,
    pub errors: usize,
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
        if self.uncertified
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
        self.uncertified |= other.uncertified;
        self.filtered_model_exception_paths += other.filtered_model_exception_paths;
        for (site, count) in &other.filtered_model_exception_sites {
            *self.filtered_model_exception_sites.entry(site.clone()).or_default() += count;
        }
        self.applicable_batches += other.applicable_batches;
        self.inapplicable_batches += other.inapplicable_batches;
        self.sampled_paths += other.sampled_paths;
        self.errors += other.errors;
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
