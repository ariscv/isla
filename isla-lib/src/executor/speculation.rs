//! 推演的拒绝标签、统计与强制失败诊断；区域边界负责捕获拒绝并回滚。

use crate::error::qualified_reason_enum;
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

macro_rules! speculative_reject_reasons {
    ($($(#[$attr:meta])* $variant:ident,)*) => {
        qualified_reason_enum! {
            /// 上层位置优先报告来源；直接使用底层分叉接口时报告对应底层标签。
            #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
            pub enum SpeculativeRejectReason {
                $($(#[$attr])* $variant,)*
            }
        }

        impl SpeculativeRejectReason {
            const ALL: &'static [Self] = &[$(Self::$variant),*];
        }
    };
}

speculative_reject_reasons! {
    UnknownFiniteDomain,
    UnknownZ3,
    Z3Timeout,
    Z3ResourceExhausted,
    UnknownDeferredMode,
    ExitUnsat,
    SymbolicAssertion,
    PathTimeout,
    NoJoin,
    HasBackEdge,
    ExceptionCheck,
    RegionEscaped,
    StackEscaped,
    StepBudget,
    NestingLimit,
    FragmentLimit,
    /// 平铺循环的继续/退出前沿不能在同一边界收敛。
    StateEffect,
    UnknownExtern,
    RecursiveEffect,
    CalleeStateWrite,
    RegisterReadAfterWrite,
    RepeatedRegisterWrite,
    RegisterReadWrite,
    RegisterSequence,
    RelaxedRegister,
    IncompatibleState,
    UnionPayload,
    DepthMismatch,
    LoopHistoryMismatch,
    SamplingState,
    PolicyOff,
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
    Assume,
    Assert,
    Arbitrary,
    Exit,
}

impl SpeculativeRejectReason {
    pub(crate) fn is_indeterminate(self) -> bool {
        matches!(
            self,
            Self::UnknownFiniteDomain
                | Self::UnknownZ3
                | Self::Z3Timeout
                | Self::Z3ResourceExhausted
                | Self::UnknownDeferredMode
                | Self::PathTimeout
        )
    }

    pub(crate) fn partial_commit(self, options: &crate::config::RegionOptions) -> bool {
        match self {
            Self::UnknownFiniteDomain => options.partial_commit_finite_domain,
            Self::UnknownZ3 => options.partial_commit_unknown_z3,
            Self::Z3Timeout => options.partial_commit_z3_timeout,
            Self::Z3ResourceExhausted => options.partial_commit_z3_resource_exhausted,
            Self::UnknownDeferredMode => options.partial_commit_deferred_mode,
            _ => false,
        }
    }
}

impl Serialize for SpeculativeRejectReason {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_unit_variant("SpeculativeRejectReason", *self as u32, self.reason_name())
    }
}

impl<'de> serde::Deserialize<'de> for SpeculativeRejectReason {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        if deserializer.is_human_readable() {
            let key = String::deserialize(deserializer)?;
            Self::ALL
                .iter()
                .copied()
                .find(|reason| reason.reason_name() == key)
                .ok_or_else(|| serde::de::Error::custom(format!("未知推演原因 {key}")))
        } else {
            let index = u32::deserialize(deserializer)?;
            Self::ALL.get(index as usize).copied().ok_or_else(|| serde::de::Error::custom("未知推演原因编号"))
        }
    }
}

impl fmt::Display for SpeculativeRejectReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.reason_name())
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
    fn every_rejection_reason_uses_its_variant_name() {
        for &reason in SpeculativeRejectReason::ALL {
            let name = format!("SpeculativeRejectReason::{reason:?}");
            let serialized = serde_json::to_value(reason).unwrap();
            assert_eq!(serialized, json!(name));
            assert_eq!(reason.to_string(), name);
            assert_eq!(serde_json::from_value::<SpeculativeRejectReason>(serialized).unwrap(), reason);
        }
    }

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
            "reason_counts": {"SpeculativeRejectReason::SymbolicJump": 4, "SpeculativeRejectReason::RetryOperand": 4}})
        );
        stats.reset();
        assert_eq!(stats.reject_json(), json!({"total": 0, "reason_counts": {}}));
    }
}

/// 强制合并失败必须终止整个运行，不能只终止某个 worker。
pub const FORCE_MERGE_EXIT_CODE: i32 = 86;

pub(super) fn force_diagnostic(
    rule: Option<usize>,
    function: &str,
    pc: usize,
    location: crate::source_loc::SourceLoc,
    error: &crate::error::ExecError,
    origin: Option<(String, usize, crate::source_loc::SourceLoc)>,
) -> String {
    use crate::error::ExecError;
    let (reason, rejected_function, rejected_pc, rejected_location) = match error {
        ExecError::SpeculativeReject { reason, function, pc, location, .. } => {
            (*reason, Some(*function), *pc, *location)
        }
        ExecError::Smt(error) | ExecError::Unproven(error) => (error.reject_reason(), None, pc, error.source_loc()),
        ExecError::Timeout => (SpeculativeRejectReason::PathTimeout, None, pc, location),
        _ => (SpeculativeRejectReason::IncompatibleState, None, pc, location),
    };
    json!({"kind":"force_region_merge_failure", "rule":rule, "function":function,
        "branch_pc":pc, "source_loc":location, "reason":reason,
        "rejected_function_id":rejected_function, "rejected_pc":rejected_pc,
        "rejected_source_loc":rejected_location, "force_origin":origin, "cause":error.query_failure().map(|cause|cause.diagnostic()), "error":error.to_string()})
    .to_string()
}

pub(super) fn force_failure<B: crate::bitvector::BV>(
    frame: &super::LocalFrame<B>,
    state: &super::TaskState<B>,
    shared: &crate::ir::SharedState<B>,
    location: crate::source_loc::SourceLoc,
    error: &crate::error::ExecError,
) -> ! {
    let rule = state
        .execution_limits
        .as_ref()
        .and_then(|limits| {
            limits.merge_rule(frame.function_name, location).or_else(|| {
                frame
                    .region_execution
                    .as_ref()
                    .and_then(|execution| limits.merge_rule(execution.origin.0, execution.origin.2))
            })
        })
        .map(|(index, _)| index);
    let origin = frame.region_execution.as_ref().map(|execution| {
        let (function, pc, location) = execution.origin;
        (crate::zencode::decode(shared.symtab.to_str(function)), pc, location)
    });
    // 显式 Off 在分支入口直接触发强退，尚未经过 try_region 的失败记账。
    if matches!(error, crate::error::ExecError::SpeculativeReject { reason: SpeculativeRejectReason::PolicyOff, .. }) {
        let execution = frame.region_execution.as_ref().expect("Off 冲突必须发生在 Force 推演中");
        let (function, pc, location) = execution.origin;
        let rule = state
            .execution_limits
            .as_ref()
            .and_then(|limits| limits.merge_rule(function, location))
            .map(|(index, _)| index);
        shared.execution_stats.merge_rejected(function, pc, error);
        shared.execution_stats.merge_finished(false);
        shared.execution_stats.rule_finished(rule, Some(SpeculativeRejectReason::PolicyOff));
        state.speculation_stats.record_reject(SpeculativeRejectReason::PolicyOff);
    }
    let diagnostic = force_diagnostic(
        rule,
        &crate::zencode::decode(shared.symtab.to_str(frame.function_name)),
        frame.pc,
        location,
        error,
        origin,
    );
    eprintln!("{}", diagnostic);
    shared.execution_stats.print(shared);
    std::process::exit(FORCE_MERGE_EXIT_CODE)
}
