//! 可选执行统计；所有线程共享，拒绝统一使用推演原因标签。
use super::{ForkSink, SpeculativeRejectReason, Task};
use crate::bitvector::BV;
use crate::ir::{Instr, Name, Symtab};
use crate::smt::Event;
use crate::source_loc::SourceLoc;
use crate::zencode;
use serde::Serialize;
use serde_json::{json, Value};
use std::collections::{BTreeMap, HashMap};
use std::sync::Mutex;

pub(super) fn instr_source_loc<B>(instr: &Instr<Name, B>) -> Option<SourceLoc> {
    match instr {
        Instr::Decl(_, _, info)
        | Instr::Init(_, _, _, info)
        | Instr::Copy(_, _, info)
        | Instr::Jump(_, _, info)
        | Instr::Monomorphize(_, _, info)
        | Instr::Call(_, _, _, _, info)
        | Instr::PrimopUnary(_, _, _, info)
        | Instr::PrimopBinary(_, _, _, _, info)
        | Instr::PrimopVariadic(_, _, _, info)
        | Instr::PrimopReset(_, _, _, info)
        | Instr::Exit(_, info) => Some(*info),
        Instr::Goto(_) | Instr::Arbitrary | Instr::End => None,
    }
}

#[derive(Default, Serialize)]
struct RuleStats {
    attempts: usize,
    successes: usize,
    failures: usize,
    failure_reasons: BTreeMap<SpeculativeRejectReason, usize>,
}

#[derive(Default, Serialize)]
struct MergeStats {
    attempts: usize,
    successes: usize,
    failures: usize,
    candidate_attempts: usize,
    negative_cache_hits: usize,
    rules: BTreeMap<usize, RuleStats>,
    failure_reasons: BTreeMap<SpeculativeRejectReason, usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    merge_enumeration: Option<EnumerationCountStats>,
}

#[derive(Default, Serialize)]
struct EnumerationCountStats {
    completed_paths: usize,
    sample_stride: usize,
    exported_samples: usize,
    counted_classes: usize,
    counted_paths: usize,
    truncated_classes: usize,
    truncated_paths: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct RejectSite {
    reason: SpeculativeRejectReason,
    function: Name,
    branch_pc: usize,
    rejected_function: Name,
    rejected_pc: usize,
    location: SourceLoc,
}

pub struct ExecutionStats {
    enabled: bool,
    snapshot_symbols: Mutex<Option<(Vec<String>, Vec<String>)>>,
    merge: Mutex<MergeStats>,
    forks: Mutex<HashMap<(Name, SourceLoc), usize>>,
    rejections: Mutex<HashMap<RejectSite, usize>>,
}
impl Default for ExecutionStats {
    fn default() -> Self {
        Self::new(std::env::var_os("ISLA_STATS").as_deref() == Some(std::ffi::OsStr::new("1")))
    }
}
impl ExecutionStats {
    pub fn new(enabled: bool) -> Self {
        Self {
            enabled,
            snapshot_symbols: Mutex::new(None),
            merge: Mutex::new(MergeStats::default()),
            forks: Mutex::new(HashMap::new()),
            rejections: Mutex::new(HashMap::new()),
        }
    }
    pub fn enabled(&self) -> bool {
        self.enabled
    }
    pub(super) fn enumeration_counted(
        &self,
        classes: usize,
        paths: usize,
        truncated_classes: usize,
        path_truncated: bool,
        sample_stride: usize,
        exported_samples: usize,
    ) {
        if self.enabled {
            let mut merge = self.merge.lock().unwrap();
            let stats = merge.merge_enumeration.get_or_insert_with(EnumerationCountStats::default);
            if stats.completed_paths > 0 {
                assert_eq!(stats.sample_stride, sample_stride, "同一次执行的采样步长必须一致");
            }
            stats.sample_stride = sample_stride;
            stats.exported_samples += exported_samples;
            stats.completed_paths += 1;
            stats.counted_classes += classes;
            stats.counted_paths += paths;
            stats.truncated_classes += truncated_classes;
            stats.truncated_paths += usize::from(path_truncated);
        }
    }
    pub fn prepare_snapshot(&self, symtab: &Symtab<'_>) {
        *self.snapshot_symbols.lock().unwrap() = Some(symtab.to_raw_table());
    }
    pub fn snapshot_json(&self) -> (Value, Value, Value) {
        let symbols = self.snapshot_symbols.lock().unwrap();
        let (raw, files) = symbols.as_ref().expect("统计快照必须先准备符号表");
        // from_raw_table 会合并同名符号；逐项复用 intern/gensym，保持重复 gensym 后的 Name 编号。
        let mut symtab = Symtab::from_raw_table(&[], files);
        for (index, symbol) in raw.iter().enumerate() {
            let name = if symtab.get(symbol).is_some() { symtab.gensym() } else { symtab.intern(symbol) };
            assert_eq!(name, Name::from_u32(u32::try_from(index).expect("快照符号编号超过 u32 范围")));
            assert_eq!(symtab.to_str(name), symbol, "重复的 IR 符号必须来自 gensym");
        }
        (self.merge_json(), self.fork_json(&symtab), self.arm_unsupported_json(&symtab))
    }
    /// 加载时登记全部规则，包括从未尝试及显式 Off 的规则。
    pub fn prepare_merge_rules(&self, count: usize) {
        if self.enabled {
            let mut merge = self.merge.lock().unwrap();
            for index in 0..count {
                merge.rules.entry(index).or_default();
            }
        }
    }
    /// 正常收尾与 Force 强退共用，确保强退不依赖析构或 worker panic。
    pub fn print<B>(&self, shared: &crate::ir::SharedState<B>) {
        if self.enabled {
            eprintln!("[MERGE_STATS] {}", self.merge_json());
            eprintln!("[FORK_STATS] {}", self.fork_json(&shared.symtab));
            eprintln!("[SPECULATION_REJECT_STATS] {}", self.arm_unsupported_json(&shared.symtab));
        }
    }
    pub fn reset(&self) {
        let mut merge = self.merge.lock().unwrap();
        let rules = merge.rules.keys().map(|index| (*index, RuleStats::default())).collect();
        *merge = MergeStats { rules, ..MergeStats::default() };
        self.forks.lock().unwrap().clear();
        self.rejections.lock().unwrap().clear();
    }
    pub(super) fn rule_attempt(&self, rule: Option<usize>) {
        if self.enabled {
            if let Some(rule) = rule {
                self.merge.lock().unwrap().rules.entry(rule).or_default().attempts += 1;
            }
        }
    }
    pub(super) fn rule_finished(&self, rule: Option<usize>, rejection: Option<SpeculativeRejectReason>) {
        if self.enabled {
            if let Some(rule) = rule {
                let mut merge = self.merge.lock().unwrap();
                let stats = merge.rules.get_mut(&rule).expect("规则完成前必须记尝试");
                match rejection {
                    Some(reason) => {
                        stats.failures += 1;
                        *stats.failure_reasons.entry(reason).or_default() += 1;
                    }
                    None => stats.successes += 1,
                }
            }
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
    pub(super) fn merge_cache_hit(&self) {
        if self.enabled {
            self.merge.lock().unwrap().negative_cache_hits += 1;
        }
    }
    pub(super) fn merge_rejected(&self, function: Name, branch_pc: usize, error: &crate::error::ExecError) {
        let crate::error::ExecError::SpeculativeReject { reason, function: rejected_function, pc, location } = error
        else {
            panic!("统计必须记录推演拒绝");
        };
        if self.enabled {
            *self.merge.lock().unwrap().failure_reasons.entry(*reason).or_default() += 1;
            *self
                .rejections
                .lock()
                .unwrap()
                .entry(RejectSite {
                    reason: *reason,
                    function,
                    branch_pc,
                    rejected_function: *rejected_function,
                    rejected_pc: *pc,
                    location: *location,
                })
                .or_default() += 1;
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
    fn record_fork(&self, function: Name, location: SourceLoc) {
        if self.enabled {
            *self.forks.lock().unwrap().entry((function, location)).or_default() += 1;
        }
    }
    #[cfg(test)]
    pub(super) fn fork_count(&self) -> usize {
        self.forks.lock().unwrap().values().sum()
    }
    pub fn merge_json(&self) -> Value {
        serde_json::to_value(&*self.merge.lock().unwrap()).unwrap()
    }
    pub fn fork_json(&self, symtab: &Symtab<'_>) -> Value {
        let forks = self.forks.lock().unwrap();
        let total: usize = forks.values().sum();
        let mut entries: Vec<_> = forks
            .iter()
            .map(|((function, info), count)| {
                (zencode::decode(symtab.to_str(*function)), info.location_string(symtab.files()), *count, *info)
            })
            .collect();
        entries.sort_by(|a, b| b.2.cmp(&a.2).then_with(|| a.0.cmp(&b.0)).then_with(|| a.1.cmp(&b.1)));
        let top: Vec<_> = entries.into_iter().take(30).map(|(function, location, count, source_loc)| json!({"function":function,"location":location,"source_loc":source_loc,"count":count})).collect();
        json!({"total":total,"unique_locations":forks.len(),"top":top})
    }
    /// 保留现有统计消费者的 API；内容已迁移为区域推演拒绝（不再含 arm_unsupported 标签）。
    pub fn arm_unsupported_json(&self, symtab: &Symtab<'_>) -> Value {
        let rejections = self.rejections.lock().unwrap();
        let total: usize = rejections.values().sum();
        let mut counts = BTreeMap::new();
        let mut entries: Vec<_> = rejections
            .iter()
            .map(|(site, count)| {
                *counts.entry(site.reason).or_insert(0) += count;
                (site, *count, zencode::decode(symtab.to_str(site.function)))
            })
            .collect();
        entries.sort_by(|a, b| {
            b.1.cmp(&a.1)
                .then_with(|| a.2.cmp(&b.2))
                .then_with(|| a.0.branch_pc.cmp(&b.0.branch_pc))
                .then_with(|| a.0.reason.cmp(&b.0.reason))
        });
        let top: Vec<_> = entries.into_iter().take(30).map(|(site,count,function)| json!({"reason":site.reason,"function":function,"branch_pc":site.branch_pc,"rejected_function":zencode::decode(symtab.to_str(site.rejected_function)),"target_pc":site.rejected_pc,"source_loc":site.location,"location":site.location.location_string(symtab.files()),"count":count})).collect();
        json!({"total":total,"unique_locations":rejections.len(),"reason_counts":counts,"top":top})
    }
}
/// 复用实际的 fork 提交入口，覆盖 Jump、Monomorphize 和操作数重试。
/// 不计初始任务、合并事件以及被限制拒绝的 fork。
pub(super) struct StatsForkSink<'a, S: ?Sized> {
    pub inner: &'a S,
    pub stats: &'a ExecutionStats,
}

impl<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized> ForkSink<'ir, 'task, B> for StatsForkSink<'_, S> {
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
    fn count枚举汇总与重置() {
        let disabled = ExecutionStats::new(false);
        disabled.enumeration_counted(2, 3, 1, false, 7, 1);
        assert!(disabled.merge_json().get("merge_enumeration").is_none());
        let stats = ExecutionStats::new(true);
        stats.enumeration_counted(2, 3, 1, false, 7, 1);
        stats.enumeration_counted(1, 2, 1, true, 7, 1);
        assert_eq!(
            stats.merge_json()["merge_enumeration"],
            json!({"completed_paths":2, "sample_stride":7, "exported_samples":2,
            "counted_classes":3, "counted_paths":5, "truncated_classes":2, "truncated_paths":1})
        );
        stats.reset();
        assert!(stats.merge_json().get("merge_enumeration").is_none());
    }
    fn rejection(function: Name, pc: usize) -> crate::error::ExecError {
        crate::error::ExecError::SpeculativeReject {
            reason: SpeculativeRejectReason::StateEffect,
            function,
            pc,
            location: SourceLoc::unknown(),
        }
    }
    #[test]
    fn stats_disabled_has_no_side_effects() {
        let stats = ExecutionStats::new(false);
        stats.merge_attempt();
        stats.merge_candidate();
        stats.merge_cache_hit();
        stats.merge_rejected(Name::from_u32(0), 1, &rejection(Name::from_u32(0), 2));
        stats.merge_finished(false);
        assert_eq!(stats.merge_json()["attempts"], 0);
        assert_eq!(stats.arm_unsupported_json(&Symtab::new())["total"], 0);
    }
    #[test]
    fn stats_threads_rejections_cache_and_reset() {
        let stats = ExecutionStats::new(true);
        let symtab = Symtab::new();
        std::thread::scope(|scope| {
            for _ in 0..4 {
                let stats = &stats;
                scope.spawn(move || {
                    for _ in 0..10 {
                        stats.merge_attempt();
                        stats.merge_candidate();
                        stats.merge_cache_hit();
                        stats.merge_rejected(Name::from_u32(0), 1, &rejection(Name::from_u32(0), 2));
                        stats.merge_finished(false);
                    }
                });
            }
        });
        assert_eq!(stats.merge_json()["attempts"], 40);
        assert_eq!(stats.merge_json()["negative_cache_hits"], 40);
        assert_eq!(stats.merge_json()["failure_reasons"]["state_effect"], 40);
        assert_eq!(stats.arm_unsupported_json(&symtab)["top"][0]["target_pc"], 2);
        stats.reset();
        assert_eq!(stats.merge_json()["attempts"], 0);
        assert_eq!(stats.arm_unsupported_json(&symtab)["total"], 0);
    }
    #[test]
    fn stats_snapshot_owns_names_and_locations() {
        let stats = std::sync::Arc::new(ExecutionStats::new(true));
        {
            let function = String::from("zfunction");
            let mut symtab = Symtab::new();
            symtab.gensym();
            symtab.gensym();
            symtab.set_files(vec!["区域.sail"]);
            let name = symtab.intern(&function);
            let location = SourceLoc::new(0, 12, 1, 12, 8);
            stats.record_fork(name, location);
            let rejection = crate::error::ExecError::SpeculativeReject {
                reason: SpeculativeRejectReason::StateEffect,
                function: name,
                pc: 2,
                location,
            };
            stats.merge_rejected(name, 1, &rejection);
            stats.prepare_snapshot(&symtab);
        }
        let snapshot = std::thread::spawn(move || stats.snapshot_json()).join().unwrap();
        assert_eq!(snapshot.1["top"][0]["function"], "function");
        assert_eq!(snapshot.2["top"][0]["reason"], "state_effect");
        assert_eq!(snapshot.1["top"][0]["location"], "区域.sail 12:1 - 12:8");
        assert_eq!(snapshot.2["top"][0]["rejected_function"], "function");
    }
    #[test]
    fn stats_top_is_sorted_and_limited() {
        let stats = ExecutionStats::new(true);
        let symtab = Symtab::new();
        for pc in 0..40 {
            for _ in 0..=pc {
                stats.merge_rejected(Name::from_u32(0), pc, &rejection(Name::from_u32(0), pc));
            }
        }
        let report = stats.arm_unsupported_json(&symtab);
        assert_eq!(report["top"].as_array().unwrap().len(), 30);
        assert_eq!(report["top"][0]["count"], 40);
    }
}

#[cfg(test)]
mod merge_rule_tests {
    use super::*;

    #[test]
    fn stats_include_unattempted_rules_after_reset() {
        let stats = ExecutionStats::new(true);
        stats.prepare_merge_rules(3);
        stats.rule_attempt(Some(1));
        stats.rule_finished(Some(1), None);
        assert_eq!(stats.merge_json()["rules"]["0"]["attempts"], 0);
        assert_eq!(stats.merge_json()["rules"]["1"]["successes"], 1);
        stats.reset();
        for index in 0..3 {
            assert_eq!(stats.merge_json()["rules"][index.to_string()]["attempts"], 0);
        }
    }
}
