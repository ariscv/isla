//! 求解产物的执行范围摘要；正常结束不等于源码控制流已全覆盖。
use serde::Serialize;
use serde_json::{json, Value};

#[derive(Default, Clone, Serialize)]
#[serde(rename_all = "kebab-case")]
pub(super) struct SolveSummary {
    pub sampled_paths: usize,
    pub errors: usize,
    pub execution_timeouts: usize,
    pub smt_timeouts: usize,
    pub unfinished_paths: usize,
    pub assertion_filtered_paths: usize,
    pub omitted_cases: usize,
    pub model_query_timeouts: usize,
    pub encoding_filtered_paths: usize,
    pub pending_batches: usize,
}

impl SolveSummary {
    pub fn status(&self) -> &'static str {
        if self.sampled_paths
            + self.errors
            + self.unfinished_paths
            + self.omitted_cases
            + self.model_query_timeouts
            + self.pending_batches
            > 0
        {
            "partial"
        } else {
            "finished"
        }
    }

    pub fn json(&self) -> Value {
        let mut value = serde_json::to_value(self).unwrap();
        value["status"] = json!(self.status());
        value["model-coverage"] = json!("not-measured");
        value
    }

    pub fn merge(&mut self, other: &Self) {
        self.sampled_paths += other.sampled_paths;
        self.errors += other.errors;
        self.execution_timeouts += other.execution_timeouts;
        self.smt_timeouts += other.smt_timeouts;
        self.unfinished_paths += other.unfinished_paths;
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
    let stats = &shared_state.execution_stats;
    if stats.enabled() {
        eprintln!("[MERGE_STATS] {}", stats.merge_json());
        eprintln!("[FORK_STATS] {}", stats.fork_json(&shared_state.symtab));
    }
}
