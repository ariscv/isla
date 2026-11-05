//! 可选执行统计；与路径状态分离，所有 worker 共享同一组计数。

use std::collections::{BTreeMap, HashMap};
use std::sync::Mutex;

use serde::Serialize;
use serde_json::{json, Value};

use super::{ForkSink, Task};
use crate::bitvector::BV;
use crate::ir::{Name, Symtab};
use crate::smt::Event;
use crate::source_loc::SourceLoc;
use crate::zencode;

/// 按 try_merge_diamond 的实际拒绝点分类，不改变原来的回滚或返回行为。
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum MergeFailure {
    NoJoin,
    ElseArmUnsupported,
    ElseArmError,
    ElseTransactionInvalid,
    ThenArmUnsupported,
    ThenArmError,
    ThenTransactionInvalid,
    LimitedPcModified,
    DepthMismatch,
    LoopHistoryMismatch,
    FrameMergeRejected,
    FrameMergeError,
    FrameTransactionInvalid,
    EqualityError,
    EqualityTransactionInvalid,
    RegisterReadMergeError,
}

const MERGE_FAILURES: [MergeFailure; 16] = [
    MergeFailure::NoJoin,
    MergeFailure::ElseArmUnsupported,
    MergeFailure::ElseArmError,
    MergeFailure::ElseTransactionInvalid,
    MergeFailure::ThenArmUnsupported,
    MergeFailure::ThenArmError,
    MergeFailure::ThenTransactionInvalid,
    MergeFailure::LimitedPcModified,
    MergeFailure::DepthMismatch,
    MergeFailure::LoopHistoryMismatch,
    MergeFailure::FrameMergeRejected,
    MergeFailure::FrameMergeError,
    MergeFailure::FrameTransactionInvalid,
    MergeFailure::EqualityError,
    MergeFailure::EqualityTransactionInvalid,
    MergeFailure::RegisterReadMergeError,
];

#[derive(Serialize)]
struct MergeStats {
    attempts: usize,
    successes: usize,
    failures: usize,
    candidate_attempts: usize,
    // 每个被拒绝的候选记一次；NoJoin 和 RegisterReadMergeError 属于调用级失败。
    failure_reasons: BTreeMap<MergeFailure, usize>,
}

impl Default for MergeStats {
    fn default() -> Self {
        Self {
            attempts: 0,
            successes: 0,
            failures: 0,
            candidate_attempts: 0,
            failure_reasons: MERGE_FAILURES.into_iter().map(|reason| (reason, 0)).collect(),
        }
    }
}

pub struct ExecutionStats {
    enabled: bool,
    merge: Mutex<MergeStats>,
    forks: Mutex<HashMap<(Name, SourceLoc), usize>>,
}

impl Default for ExecutionStats {
    fn default() -> Self {
        Self::new(std::env::var_os("ISLA_STATS").as_deref() == Some(std::ffi::OsStr::new("1")))
    }
}

impl ExecutionStats {
    pub fn new(enabled: bool) -> Self {
        Self { enabled, merge: Mutex::new(MergeStats::default()), forks: Mutex::new(HashMap::new()) }
    }

    pub fn enabled(&self) -> bool {
        self.enabled
    }

    /// 仅在启动新的求解、尚无 worker 运行时清零，排除初始化阶段的执行。
    pub fn reset(&self) {
        if self.enabled {
            *self.merge.lock().unwrap() = MergeStats::default();
            self.forks.lock().unwrap().clear();
        }
    }

    pub(super) fn merge_attempt(&self) {
        if self.enabled {
            self.merge.lock().unwrap().attempts += 1;
        }
    }

    pub(super) fn merge_candidate(&self) {
        if self.enabled {
            self.merge.lock().unwrap().candidate_attempts += 1;
        }
    }

    pub(super) fn merge_rejected(&self, reason: MergeFailure) {
        if self.enabled {
            *self.merge.lock().unwrap().failure_reasons.get_mut(&reason).unwrap() += 1;
        }
    }

    pub(super) fn merge_finished(&self, success: bool) {
        if self.enabled {
            let mut merge = self.merge.lock().unwrap();
            if success {
                merge.successes += 1;
            } else {
                merge.failures += 1;
            }
        }
    }

    fn record_fork(&self, function: Name, info: SourceLoc) {
        if self.enabled {
            *self.forks.lock().unwrap().entry((function, info)).or_default() += 1;
        }
    }

    #[cfg(test)]
    pub(super) fn fork_count(&self) -> usize {
        self.forks.lock().unwrap().values().sum()
    }

    /// 调用方在 worker 全部退出后读取，避免得到未完成调用的中间计数。
    pub fn merge_json(&self) -> Value {
        serde_json::to_value(&*self.merge.lock().unwrap()).unwrap()
    }

    pub fn fork_json(&self, symtab: &Symtab<'_>) -> Value {
        let forks = self.forks.lock().unwrap();
        let total: usize = forks.values().sum();
        let mut locations: Vec<_> = forks
            .iter()
            .map(|((function, info), count)| {
                (zencode::decode(symtab.to_str(*function)), info.location_string(symtab.files()), *count, *info)
            })
            .collect();
        locations.sort_by(|a, b| b.2.cmp(&a.2).then_with(|| a.0.cmp(&b.0)).then_with(|| a.1.cmp(&b.1)));
        let top: Vec<_> = locations
            .into_iter()
            .take(30)
            .map(|(function, location, count, source_loc)| {
                json!({"function": function, "location": location, "source_loc": source_loc, "count": count})
            })
            .collect();
        json!({"total": total, "unique_locations": forks.len(), "top": top})
    }
}

/// 复用实际的 fork 提交入口，覆盖 Jump、Monomorphize 和操作数重试。
/// 不计初始任务、合并事件以及被限制拒绝的 fork。
pub(super) struct StatsForkSink<'a, S> {
    pub inner: &'a S,
    pub stats: &'a ExecutionStats,
}

impl<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B>> ForkSink<'ir, 'task, B> for StatsForkSink<'_, S> {
    fn submit(&self, task: Task<'ir, 'task, B>) {
        if self.stats.enabled {
            let Some((_, Event::Fork(_, _, _, info))) = &task.fork_cond else {
                panic!("分叉子任务必须携带 Fork 事件及源码位置")
            };
            self.stats.record_fork(task.frame.function_name, *info);
        }
        self.inner.submit(task);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn execution_stats_threads_and_top_locations() {
        let stats = ExecutionStats::new(true);
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["model.sail"]);
        let function = symtab.intern("ztest");
        std::thread::scope(|scope| {
            for worker in 0..4 {
                let stats = &stats;
                scope.spawn(move || {
                    for line in 1..=40 {
                        for count in 0..line {
                            stats.merge_attempt();
                            stats.merge_candidate();
                            stats.merge_rejected(MergeFailure::NoJoin);
                            stats.merge_finished(count % 2 == 0);
                            stats.record_fork(function, SourceLoc::new(0, line, worker, line, worker + 1));
                        }
                    }
                });
            }
        });
        let merge = stats.merge_json();
        assert_eq!(merge["attempts"], 3280);
        assert_eq!(merge["candidate_attempts"], 3280);
        assert_eq!(merge["failure_reasons"]["no_join"], 3280);
        assert_eq!(merge["successes"], 1680);
        assert_eq!(merge["failures"], 1600);
        let forks = stats.fork_json(&symtab);
        assert_eq!(forks["total"], 3280);
        assert_eq!(forks["unique_locations"], 160);
        let top = forks["top"].as_array().unwrap();
        assert_eq!(top.len(), 30);
        assert_eq!(top[0]["function"], "test");
        assert_eq!(top[0]["location"], "model.sail 40:0 - 40:1");
        assert_eq!(top[0]["source_loc"]["line1"], 40);
        assert!(top.windows(2).all(|pair| pair[0]["count"].as_u64() >= pair[1]["count"].as_u64()));
        stats.reset();
        assert_eq!(stats.merge_json()["attempts"], 0);
        assert_eq!(stats.fork_count(), 0);
    }

    #[test]
    fn execution_stats_disabled_does_not_count() {
        let stats = ExecutionStats::new(false);
        stats.merge_attempt();
        stats.merge_candidate();
        stats.merge_rejected(MergeFailure::NoJoin);
        stats.merge_finished(true);
        stats.record_fork(Name::from_u32(0), SourceLoc::unknown());
        assert_eq!(stats.merge_json()["attempts"], 0);
        assert_eq!(stats.fork_count(), 0);
    }
}
