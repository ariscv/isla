//! 路径丢弃与判定失败共享执行统计，验收调用不经过此入口。
use super::*;
use crate::config::SolverOnUnknown;
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

    pub fn solver_failed(&self) -> bool {
        self.solver_failed.load(std::sync::atomic::Ordering::Relaxed)
    }
}

pub fn is_solver_failure(error: &ExecError) -> bool {
    matches!(error, ExecError::Smt(SmtError::Timeout(_) | SmtError::Unknown { .. }))
}

/// 只在探索决定丢弃时调用。返回 true 表示应走当前候选的死路径出口。
pub fn discard_solver_path<B: BV>(
    policy: Option<SolverOnUnknown>,
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
    let stats = &shared.execution_stats;
    if policy == SolverOnUnknown::Error {
        stats.solver_failed.store(true, std::sync::atomic::Ordering::Relaxed);
        return false;
    }
    let source = if source.is_unknown() {
        frame.instrs[..(frame.pc() + 1).min(frame.instrs.len())]
            .iter()
            .rev()
            .find_map(instr_source_loc)
            .unwrap_or(source)
    } else {
        source
    };
    let sail_location = source.file_line(shared.symtab.files()).unwrap_or_else(|| "未知 Sail 位置".into());
    let mut drops = stats.solver_path_drops.lock().unwrap();
    let drop = SolverPathDrop {
        path_count: drops.len() + 1,
        function: crate::zencode::decode(shared.symtab.to_str(frame.function_name())),
        pc: frame.pc(),
        path_signature: frame.path_signature(),
        sail_location,
        source_loc: source,
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
