//! 推演的分支拒绝标签与统计。C1 只建立入口，不执行推演合并。

use std::collections::BTreeMap;
use std::fmt;
use std::sync::Mutex;

use serde::Serialize;
use serde_json::{json, Value};

/// 推演状态属于执行帧；调用、冻结和恢复时原样传递。
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SpeculationMode {
    #[default]
    Off,
    On,
}

/// 上层位置优先报告来源；直接使用底层分叉接口时报告对应底层标签。
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SpeculativeRejectReason {
    SymbolicJump,
    Monomorphize,
    ExpressionRetry,
    UnaryRetry,
    BinaryRetry,
    VariadicRetry,
    SpecialCallRetry,
    IntegerConversion,
    RetryCondition,
    SymbolicValueEnumeration,
    RetryOperand,
    AnnouncePc,
    Interrupt,
    ZeroInstruction,
    LimitSampling,
    LimitTruncation,
}

impl fmt::Display for SpeculativeRejectReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Value::String(label) = serde_json::to_value(self).expect("拒绝标签必须可序列化") else {
            panic!("拒绝标签必须序列化为字符串")
        };
        f.write_str(&label)
    }
}

/// 每组 TaskState 独立持有统计，fork 的任务共享它；无需借用 IR 即可生成快照。
/// 收尾打印和周期快照可调用 TaskState::speculation_stats().reject_json()。
pub struct SpeculationStats {
    enabled: bool,
    reason_counts: Mutex<BTreeMap<SpeculativeRejectReason, usize>>,
}

impl Default for SpeculationStats {
    fn default() -> Self {
        Self::new(std::env::var_os("ISLA_STATS").as_deref() == Some(std::ffi::OsStr::new("1")))
    }
}

impl SpeculationStats {
    pub fn new(enabled: bool) -> Self {
        Self { enabled, reason_counts: Mutex::new(BTreeMap::new()) }
    }

    pub(super) fn record_reject(&self, reason: SpeculativeRejectReason) {
        if self.enabled {
            let mut counts = self.reason_counts.lock().unwrap();
            let count = counts.entry(reason).or_default();
            *count = count.checked_add(1).expect("推演拒绝计数溢出");
        }
    }

    pub fn reject_json(&self) -> Value {
        let counts = self.reason_counts.lock().unwrap();
        json!({"total": counts.values().sum::<usize>(), "reason_counts": *counts})
    }

    /// 只在尚无执行线程运行时清零，沿用 ExecutionStats 的约定。
    pub fn reset(&self) {
        self.reason_counts.lock().unwrap().clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn speculation_stats_disabled_does_not_count() {
        let stats = SpeculationStats::new(false);
        stats.record_reject(SpeculativeRejectReason::SymbolicJump);
        assert_eq!(stats.reject_json(), json!({"total": 0, "reason_counts": {}}));
    }

    #[test]
    fn speculation_stats_counts_reasons_across_threads_and_resets() {
        let stats = SpeculationStats::new(true);
        std::thread::scope(|scope| {
            for _ in 0..4 {
                let stats = &stats;
                scope.spawn(move || {
                    stats.record_reject(SpeculativeRejectReason::SymbolicJump);
                    stats.record_reject(SpeculativeRejectReason::RetryOperand);
                });
            }
        });
        assert_eq!(
            stats.reject_json(),
            json!({"total": 8,
            "reason_counts": {"symbolic_jump": 4, "retry_operand": 4}})
        );
        stats.reset();
        assert_eq!(stats.reject_json(), json!({"total": 0, "reason_counts": {}}));
    }
}
