//! 可选执行统计；与路径状态分离，所有 worker 共享同一组计数。

use std::collections::{BTreeMap, HashMap};
use std::sync::Mutex;

use serde::Serialize;
use serde_json::{json, Value};

use super::{ForkSink, Task};
use crate::bitvector::BV;
use crate::ir::{Instr, Name, Symtab};
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

/// 分支臂模拟中的具体拒绝出口；Call 表示所有调用均不支持，不推断其纯度。
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum ArmUnsupported {
    StepLimit,
    PcPastInstrs,
    PcBeforeStart,
    PcAfterEnd,
    ImpureUnary,
    ImpureBinary,
    PrimopVariadic,
    GotoOutOfRange,
    GotoLimit,
    JumpLimit,
    JumpTargetOutOfRange,
    JumpFallthroughOutOfRange,
    JumpNonConcrete,
    Monomorphize,
    Call,
    PrimopReset,
    Exit,
    Arbitrary,
    End,
    RegisterReadAfterWrite,
}

#[derive(PartialEq, Eq, Hash)]
struct ArmUnsupportedSite {
    reason: ArmUnsupported,
    location: Option<(Name, SourceLoc)>,
    callee: Option<Name>,
    control_flow: Option<ArmControlFlowSite>,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct ArmControlFlowSite {
    pub(super) function: Name,
    pub(super) start_pc: usize,
    pub(super) end_pc: usize,
    pub(super) join_pc: usize,
    pub(super) target_pc: usize,
}

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
        | Instr::PrimopReset(_, _, info)
        | Instr::Exit(_, info) => Some(*info),
        Instr::Goto(_) | Instr::Arbitrary | Instr::End => None,
    }
}

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
    // 源码位置只保留首次记录的值，不参与控制流出口的聚合。
    arm_unsupported: Mutex<HashMap<ArmUnsupportedSite, (usize, Option<SourceLoc>)>>,
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
            merge: Mutex::new(MergeStats::default()),
            forks: Mutex::new(HashMap::new()),
            arm_unsupported: Mutex::new(HashMap::new()),
        }
    }

    pub fn enabled(&self) -> bool {
        self.enabled
    }

    /// 仅在启动新的求解、尚无 worker 运行时清零，排除初始化阶段的执行。
    pub fn reset(&self) {
        if self.enabled {
            *self.merge.lock().unwrap() = MergeStats::default();
            self.forks.lock().unwrap().clear();
            self.arm_unsupported.lock().unwrap().clear();
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

    pub(super) fn record_arm_unsupported<B>(
        &self,
        reason: ArmUnsupported,
        function: Name,
        instr: Option<&Instr<Name, B>>,
    ) {
        if self.enabled {
            let info = instr.and_then(instr_source_loc);
            let location = info.filter(|info| !info.is_unknown()).map(|info| (function, info));
            let callee = match instr {
                Some(Instr::Call(_, _, callee, _, _)) => Some(*callee),
                _ => None,
            };
            self.arm_unsupported
                .lock()
                .unwrap()
                .entry(ArmUnsupportedSite { reason, location, callee, control_flow: None })
                .or_default()
                .0 += 1;
        }
    }

    pub(super) fn record_arm_control_flow(
        &self,
        reason: ArmUnsupported,
        control_flow: ArmControlFlowSite,
        prev_instr_location: Option<SourceLoc>,
    ) {
        if self.enabled {
            self.arm_unsupported
                .lock()
                .unwrap()
                .entry(ArmUnsupportedSite { reason, location: None, callee: None, control_flow: Some(control_flow) })
                .or_insert((0, prev_instr_location))
                .0 += 1;
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

    pub fn arm_unsupported_json(&self, symtab: &Symtab<'_>) -> Value {
        let unsupported = self.arm_unsupported.lock().unwrap();
        let total: usize = unsupported.values().map(|(count, _)| count).sum();
        let mut reason_counts = BTreeMap::new();
        let mut locations: Vec<_> = unsupported
            .iter()
            .map(|(site, (count, prev_instr_location))| {
                *reason_counts.entry(site.reason).or_insert(0) += count;
                (
                    site.reason,
                    site.control_flow
                        .map(|flow| flow.function)
                        .or_else(|| site.location.map(|(function, _)| function))
                        .map(|function| zencode::decode(symtab.to_str(function))),
                    site.location.map(|(_, info)| info.location_string(symtab.files())),
                    site.location.map(|(_, info)| info),
                    site.callee.map(|callee| zencode::decode(symtab.to_str(callee))),
                    *count,
                    site.control_flow,
                    *prev_instr_location,
                )
            })
            .collect();
        locations.sort_by(|a, b| {
            b.5.cmp(&a.5)
                .then_with(|| a.0.cmp(&b.0))
                .then_with(|| a.1.cmp(&b.1))
                .then_with(|| a.2.cmp(&b.2))
                .then_with(|| a.4.cmp(&b.4))
                .then_with(|| a.6.cmp(&b.6))
        });
        let top: Vec<_> = locations
            .into_iter()
            .take(30)
            .map(|(reason, function, location, source_loc, callee, count, control_flow, prev_instr_location)| {
                let mut entry = json!({"reason": reason, "function": function, "location": location,
                    "source_loc": source_loc, "callee": callee, "count": count});
                if let Some(flow) = control_flow {
                    entry["start_pc"] = json!(flow.start_pc);
                    entry["end_pc"] = json!(flow.end_pc);
                    entry["join_pc"] = json!(flow.join_pc);
                    entry["target_pc"] = json!(flow.target_pc);
                    entry["prev_instr_location"] = json!(prev_instr_location
                        .filter(|info| !info.is_unknown())
                        .map(|info| info.location_string(symtab.files())));
                }
                entry
            })
            .collect();
        json!({"total": total, "unique_locations": unsupported.len(), "reason_counts": reason_counts, "top": top})
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
    use crate::bitvector::b64::B64;
    use crate::ir::{Instr, Loc};

    #[test]
    fn arm_unsupported_disabled_does_not_count() {
        let stats = ExecutionStats::new(false);
        stats.record_arm_unsupported::<B64>(ArmUnsupported::StepLimit, Name::from_u32(0), None);
        let report = stats.arm_unsupported_json(&Symtab::new());
        assert_eq!(report["total"], 0);
        assert_eq!(report["reason_counts"], json!({}));
        assert!(report["top"].as_array().unwrap().is_empty());
    }

    #[test]
    fn arm_unsupported_control_flow_disabled_does_not_count() {
        let stats = ExecutionStats::new(false);
        for reason in [
            ArmUnsupported::StepLimit,
            ArmUnsupported::PcPastInstrs,
            ArmUnsupported::PcBeforeStart,
            ArmUnsupported::PcAfterEnd,
            ArmUnsupported::GotoOutOfRange,
        ] {
            stats.record_arm_control_flow(
                reason,
                ArmControlFlowSite { function: Name::from_u32(0), start_pc: 1, end_pc: 4, join_pc: 5, target_pc: 6 },
                Some(SourceLoc::new(0, 12, 3, 12, 9)),
            );
        }
        let report = stats.arm_unsupported_json(&Symtab::new());
        assert_eq!(report["total"], 0);
        assert_eq!(report["reason_counts"], json!({}));
        assert!(report["top"].as_array().unwrap().is_empty());
    }

    #[test]
    fn arm_unsupported_control_flow_aggregates_reason_function_and_pcs() {
        let stats = ExecutionStats::new(true);
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["model.sail"]);
        let function = symtab.intern("zpte_is_invalid");
        let other_function = symtab.intern("zhave_exception");
        let site = ArmControlFlowSite { function, start_pc: 1, end_pc: 4, join_pc: 5, target_pc: 6 };
        let prev = SourceLoc::new(0, 12, 3, 12, 9);
        let reasons = [
            (ArmUnsupported::StepLimit, "step_limit"),
            (ArmUnsupported::PcPastInstrs, "pc_past_instrs"),
            (ArmUnsupported::PcBeforeStart, "pc_before_start"),
            (ArmUnsupported::PcAfterEnd, "pc_after_end"),
            (ArmUnsupported::GotoOutOfRange, "goto_out_of_range"),
        ];
        for (reason, label) in reasons {
            stats.record_arm_control_flow(reason, site, Some(prev));
            // 上一条指令的位置只用于展示，不加入聚合键。
            stats.record_arm_control_flow(reason, site, Some(SourceLoc::new(0, 20, 0, 20, 1)));
            for other_site in [
                ArmControlFlowSite { function: other_function, ..site },
                ArmControlFlowSite { start_pc: 0, ..site },
                ArmControlFlowSite { end_pc: 3, ..site },
                ArmControlFlowSite { join_pc: 7, ..site },
                ArmControlFlowSite { target_pc: 8, ..site },
            ] {
                stats.record_arm_control_flow(reason, other_site, None);
            }
            let report = stats.arm_unsupported_json(&symtab);
            assert_eq!(report["reason_counts"][label], 7);
            let top = report["top"].as_array().unwrap();
            let entry = top.iter().find(|entry| entry["reason"] == label && entry["count"] == 2).unwrap();
            assert_eq!(entry["function"], "pte_is_invalid");
            assert_eq!(entry["start_pc"], 1);
            assert_eq!(entry["end_pc"], 4);
            assert_eq!(entry["join_pc"], 5);
            assert_eq!(entry["target_pc"], 6);
            assert_eq!(entry["prev_instr_location"], "model.sail 12:3 - 12:9");
            assert!(top.iter().filter(|entry| entry["count"] == 1).all(|entry| entry["prev_instr_location"].is_null()));
        }
        let report = stats.arm_unsupported_json(&symtab);
        assert_eq!(report["total"], 35);
        assert_eq!(report["unique_locations"], 30);
        stats.reset();
        assert_eq!(stats.arm_unsupported_json(&symtab)["total"], 0);
    }

    #[test]
    fn arm_unsupported_counts_reasons_locations_and_decoded_callees() {
        let stats = ExecutionStats::new(true);
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["model.sail"]);
        let function = symtab.intern("ztest");
        let callee = symtab.intern("zcurrentlyEnabled");
        let other_callee = symtab.intern("zother");
        let info = SourceLoc::new(0, 12, 3, 12, 9);
        let call = Instr::<_, B64>::Call(Loc::Id(function), false, callee, vec![], info);
        let other_call = Instr::<_, B64>::Call(Loc::Id(function), false, other_callee, vec![], info);
        for _ in 0..2 {
            stats.record_arm_unsupported(ArmUnsupported::Call, function, Some(&call));
        }
        stats.record_arm_unsupported(ArmUnsupported::Call, function, Some(&other_call));
        stats.record_arm_unsupported::<B64>(ArmUnsupported::StepLimit, function, None);
        stats.record_arm_unsupported(ArmUnsupported::End, function, Some(&Instr::<_, B64>::End));
        let report = stats.arm_unsupported_json(&symtab);
        assert_eq!(report["total"], 5);
        assert_eq!(report["unique_locations"], 4);
        assert_eq!(report["reason_counts"], json!({"call": 3, "step_limit": 1, "end": 1}));
        let top = report["top"].as_array().unwrap();
        assert_eq!(top[0]["reason"], "call");
        assert_eq!(top[0]["function"], "test");
        assert_eq!(top[0]["callee"], "currentlyEnabled");
        assert_eq!(top[0]["location"], "model.sail 12:3 - 12:9");
        assert_eq!(top[0]["source_loc"], json!(info));
        assert_eq!(top[0]["count"], 2);
        let no_location = top.iter().find(|entry| entry["reason"] == "step_limit").unwrap();
        assert!(no_location["function"].is_null());
        assert!(no_location["source_loc"].is_null());
        assert!(no_location["callee"].is_null());
        stats.reset();
        assert_eq!(stats.arm_unsupported_json(&symtab)["total"], 0);
    }

    #[test]
    fn arm_unsupported_top_is_sorted_and_limited() {
        let stats = ExecutionStats::new(true);
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["model.sail"]);
        let function = symtab.intern("ztest");
        for line in 1..=40 {
            let instr = Instr::<_, B64>::Exit(super::super::ExitCause::Explicit, SourceLoc::new(0, line, 0, line, 1));
            for _ in 0..line {
                stats.record_arm_unsupported(ArmUnsupported::Exit, function, Some(&instr));
            }
        }
        let report = stats.arm_unsupported_json(&symtab);
        assert_eq!(report["total"], 820);
        assert_eq!(report["unique_locations"], 40);
        let top = report["top"].as_array().unwrap();
        assert_eq!(top.len(), 30);
        for (index, entry) in top.iter().enumerate() {
            assert_eq!(entry["count"], 40 - index);
            assert_eq!(entry["source_loc"]["line1"], 40 - index);
        }
    }

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
