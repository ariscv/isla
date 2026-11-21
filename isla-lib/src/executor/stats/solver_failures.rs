//! 路径丢弃与判定失败共享执行统计，验收调用不经过此入口。
use super::*;
use crate::config::PathFailureAction;
use crate::error::{ExecError, SmtError};
use crate::executor::LocalFrame;
use crate::ir::SharedState;
use crate::timeout::SmtOperation;
use serde::Deserialize;

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
pub struct SolverPathDrop {
    pub path_count: usize,
    pub function: String,
    pub pc: usize,
    pub path_signature: u64,
    pub sail_location: String,
    pub source_loc: SourceLoc,
    pub purpose: String,
    pub reason: String,
    pub seconds: f64,
    pub limit_seconds: Option<f64>,
}

#[derive(Clone, Debug, Default, Deserialize, PartialEq, Serialize)]
pub struct SolverPathDrops {
    pub count: usize,
    pub first_locations: Vec<SolverPathDrop>,
}

impl SolverPathDrops {
    const FIRST_LOCATIONS: usize = 5;

    pub fn merge(&mut self, other: &Self) {
        self.count += other.count;
        let remaining = Self::FIRST_LOCATIONS.saturating_sub(self.first_locations.len());
        self.first_locations.extend(other.first_locations.iter().take(remaining).cloned());
    }
}

impl ExecutionStats {
    pub fn solver_path_drops_since(&self, start: usize) -> SolverPathDrops {
        let drops = self.solver_path_drops.lock().unwrap();
        let drops = &drops[start..];
        SolverPathDrops {
            count: drops.len(),
            first_locations: drops.iter().take(SolverPathDrops::FIRST_LOCATIONS).cloned().collect(),
        }
    }

    pub fn solver_path_drop_count(&self) -> usize {
        self.solver_path_drops.lock().unwrap().len()
    }
}

pub fn is_solver_failure(error: &ExecError) -> bool {
    matches!(error, ExecError::Smt(SmtError::Timeout(_) | SmtError::Unknown { .. }))
}

/// 仅在失败已归属到单条探索路径时调用。返回 true 表示该路径按显式 dead 策略作废。
pub fn handle_solver_path_failure<B: BV>(
    policy: Option<PathFailureAction>,
    error: &ExecError,
    frame: &LocalFrame<'_, B>,
    shared: &SharedState<'_, B>,
) -> bool {
    let Some(policy) = policy else { return false };
    let (source, purpose, reason, wall, limit) = match error {
        ExecError::Smt(SmtError::Timeout(timeout)) => (
            timeout.source_loc,
            if timeout.operation == SmtOperation::ModelEval { "model_value" } else { timeout.query_purpose },
            "timeout",
            timeout.operation_wall,
            Some(timeout.limit),
        ),
        ExecError::Smt(SmtError::Unknown { source_loc, purpose, wall, limit }) => {
            (*source_loc, *purpose, "unknown", *wall, *limit)
        }
        _ => return false,
    };
    let failure = PathFailureDiagnostic::new(frame, shared, source, purpose, reason, wall, limit);
    if policy == PathFailureAction::Panic {
        failure.panic();
    }
    let mut drops = shared.execution_stats.solver_path_drops.lock().unwrap();
    let drop = SolverPathDrop {
        path_count: drops.len() + 1,
        function: failure.function,
        pc: frame.pc(),
        path_signature: frame.path_signature(),
        sail_location: failure.sail_location,
        source_loc: failure.source_loc,
        purpose: purpose.into(),
        reason: reason.into(),
        seconds: wall.as_secs_f64(),
        limit_seconds: limit.map(|limit| limit.as_secs_f64()),
    };
    if merge_diagnostics::enabled() {
        eprintln!("[SOLVER_PATH_DROP] {}", serde_json::to_string(&drop).unwrap());
    }
    drops.push(drop);
    true
}

pub const PATH_LIMIT_PANIC_PREFIX: &str = "[PATH_LIMIT_PANIC]";

pub(crate) struct PathFailureDiagnostic {
    function: String,
    pc: usize,
    sail_location: String,
    source_loc: SourceLoc,
    purpose: &'static str,
    reason: &'static str,
    wall: std::time::Duration,
    limit: Option<std::time::Duration>,
    path_depth: u64,
}

impl PathFailureDiagnostic {
    pub(crate) fn new<B: BV>(
        frame: &LocalFrame<'_, B>,
        shared: &SharedState<'_, B>,
        source_loc: SourceLoc,
        purpose: &'static str,
        reason: &'static str,
        wall: std::time::Duration,
        limit: Option<std::time::Duration>,
    ) -> Self {
        let source_loc = if source_loc.is_unknown() {
            frame.instrs[..frame.pc().saturating_add(1).min(frame.instrs.len())]
                .iter()
                .rev()
                .filter_map(instr_source_loc)
                .find(|loc| !loc.is_unknown())
                .unwrap_or(source_loc)
        } else {
            source_loc
        };
        Self {
            function: crate::zencode::decode(shared.symtab.to_str(frame.function_name())),
            pc: frame.pc(),
            sail_location: source_loc.file_line(shared.symtab.files()).unwrap_or_else(|| "未知 Sail 位置".into()),
            source_loc,
            purpose,
            reason,
            wall,
            limit,
            path_depth: frame.execution_limit_state.control_flow_steps(),
        }
    }

    #[cold]
    pub(crate) fn panic(&self) -> ! {
        let limit = self.limit.map_or_else(|| "unlimited".to_string(), |limit| format!("{limit:?}"));
        panic!(
            "{PATH_LIMIT_PANIC_PREFIX} reason={} function={} pc={} sail={} purpose={} elapsed={:?} limit={} path_depth={}",
            self.reason, self.function, self.pc, self.sail_location, self.purpose, self.wall, limit, self.path_depth,
        );
    }
}
