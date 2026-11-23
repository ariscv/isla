//! 在安全指令边界固化已经认证的区域前缀。
use super::{reject, reject_query, ArmErrorSink, RegionResult};
use crate::executor::*;
use crate::smt::SolverTransaction;

#[derive(Clone)]
pub(in crate::executor) struct Cut {
    pub record_start: usize,
    pub resume_in_parent: bool,
    pub can_resume_normally: bool,
    pub saw_live_merge: bool,
    pub rejection: Option<ExecError>,
}

impl Cut {
    pub(in crate::executor) fn remember_live_merge<B>(&mut self, records: &MergeHistory<B>) {
        if !self.saw_live_merge {
            self.saw_live_merge = records.has_live_closed_tail_since(self.record_start);
        }
    }
}

pub(in crate::executor) struct Instruction<'ir, 'task, B: BV> {
    transaction: SolverTransaction,
    frame: LocalFrame<'ir, B>,
    pub errors: ArmErrorSink<'ir, 'task, B>,
}

fn reason_enabled<B>(frame: &LocalFrame<B>, reason: SpeculativeRejectReason) -> bool {
    let options = crate::config::RegionOptions::current();
    if frame
        .region_execution
        .as_ref()
        .and_then(|execution| execution.verified_prefix.as_ref())
        .is_some_and(|cut| cut.resume_in_parent && !cut.can_resume_normally)
    {
        reason.nested_verified_prefix(options)
    } else {
        reason.verified_prefix(options)
    }
}

fn has_boundary<B>(frame: &LocalFrame<B>) -> bool {
    frame.region_execution.as_ref().and_then(|execution| execution.verified_prefix.as_ref()).is_some_and(|prefix| {
        prefix.saw_live_merge
            && !matches!(frame.instrs.get(frame.pc), None | Some(Instr::Decl(..) | Instr::Goto(_)))
            && !super::super::region_engine::prefix_resume::active(frame)
    })
}

pub(in crate::executor) fn can_capture<B>(frame: &LocalFrame<B>, reason: SpeculativeRejectReason) -> bool {
    has_boundary(frame) && reason_enabled(frame, reason)
}

impl<'ir, 'task, B: BV> Instruction<'ir, 'task, B> {
    pub fn start(frame: &mut LocalFrame<'ir, B>, solver: &mut Solver<B>) -> Option<Box<Self>> {
        let prefix = frame.region_execution.as_mut()?.verified_prefix.as_mut()?;
        prefix.remember_live_merge(&frame.region_merge_records);
        if !has_boundary(frame) {
            return None;
        }
        Some(Self::save(frame, solver))
    }

    // 不让未到切点的递归解释器在栈上预留帧快照。
    #[inline(never)]
    fn save(frame: &LocalFrame<'ir, B>, solver: &mut Solver<B>) -> Box<Self> {
        Box::new(Self { transaction: solver.start_transaction(), frame: frame.clone(), errors: ArmErrorSink::new() })
    }

    #[inline(never)]
    pub fn commit(
        self: Box<Self>,
        frame: &mut LocalFrame<'ir, B>,
        solver: &mut Solver<B>,
        sink: &dyn ForkSink<'ir, 'task, B>,
    ) -> Result<(), ExecError> {
        if solver.transaction_invalid() {
            // 保存点不允许改写更早的事件。沿用区域入口回放。
            solver.rollback_transaction(self.transaction);
            *frame = self.frame;
            return Err(reject(frame, SpeculativeRejectReason::IncompatibleState));
        }
        solver.commit_transaction();
        self.errors.forward(sink);
        Ok(())
    }

    pub fn rejection(error: &ExecError, frame: &LocalFrame<B>, timeout: PathTimeout) -> Option<ExecError> {
        if timeout.timed_out_with(|| frame.path_timing.snapshot()) {
            return None;
        }
        match error {
            ExecError::SpeculativeReject { reason, .. } if reason_enabled(frame, *reason) => Some(error.clone()),
            ExecError::Unproven(cause) | ExecError::Smt(cause)
                if matches!(
                    cause,
                    crate::error::SmtError::FiniteDomain { .. } | crate::error::SmtError::DeferredQuery { .. }
                ) && reason_enabled(frame, cause.reject_reason()) =>
            {
                Some(reject_query(frame, cause.clone()))
            }
            _ => None,
        }
    }

    #[inline(never)]
    pub fn roll_back(self: Box<Self>, rejection: ExecError, frame: &mut LocalFrame<'ir, B>, solver: &mut Solver<B>) {
        solver.rollback_transaction(self.transaction);
        *frame = self.frame;
        frame.region_execution.as_mut().unwrap().verified_prefix.as_mut().unwrap().rejection = Some(rejection);
    }
}

pub(in crate::executor) fn is_cut<B>(frame: &LocalFrame<B>) -> bool {
    frame
        .region_execution
        .as_ref()
        .and_then(|execution| execution.verified_prefix.as_ref())
        .is_some_and(|prefix| prefix.rejection.is_some())
}

pub(super) fn prepare_frontiers<'ir, B: BV>(
    frame: &mut LocalFrame<'ir, B>,
    arms: [Vec<LocalFrame<'ir, B>>; 2],
) -> RegionResult {
    assert!(frame.region_arrivals.is_empty());
    let mut rejection = None;
    frame.region_arrivals = arms
        .into_iter()
        .flatten()
        .map(|mut arm| {
            let cut =
                arm.region_execution.as_mut().unwrap().verified_prefix.as_mut().and_then(|cut| cut.rejection.take());
            arm.speculation_mode = frame.speculation_mode;
            arm.region_execution = frame.region_execution.clone();
            if let Some(error) = cut {
                let reason = error.rejection_reason().unwrap();
                if arm.region_execution.is_some()
                    && !reason.nested_verified_prefix(crate::config::RegionOptions::current())
                {
                    // 该指令需要普通执行。由父组织者携带互补前沿继续向外固化。
                    let parent = arm.region_execution.as_mut().unwrap().verified_prefix.as_mut().unwrap();
                    assert!(parent.can_resume_normally, "父组织者必须能继续交付切点");
                    parent.rejection = Some(error.clone());
                } else {
                    super::super::region_engine::prefix_resume::prepare(&mut arm, &error);
                }
                assert!(rejection.replace(error).is_none(), "一次区域切点只对应一条失败指令");
            }
            arm
        })
        .collect();
    RegionResult::VerifiedPrefix(rejection.expect("前缀切点必须携带区域拒绝"))
}

/// 所有延后义务通过且每组的完整到达守卫得到判定后，调用方才能关保存点。
pub(super) fn certify_groups<B: BV>(
    frame: &mut LocalFrame<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
    timeout: PathTimeout,
) -> Result<(), ExecError> {
    let check_time = || {
        if timeout.timed_out_with(|| frame.path_timing.snapshot()) {
            Err(ExecError::Timeout)
        } else {
            Ok(())
        }
    };
    check_time()?;
    let exploration = solver.exploration_on_unknown().is_some();
    let refusal = |frame: &LocalFrame<B>, cause: crate::error::SmtError| {
        if !exploration && stats::solver_failures::is_solver_failure(&ExecError::Smt(cause.clone())) {
            ExecError::Smt(cause)
        } else {
            reject_query(frame, cause)
        }
    };
    if solver.region_queries_deferred() {
        let _scope = stats::region_progress::QueryScope::enter("prefix_obligations");
        match solver.check_deferred_assertions_since_savepoint(info).expect("前缀必须开启候选认证") {
            SmtResult::Unsat => (),
            SmtResult::Sat => return Err(reject(frame, SpeculativeRejectReason::SymbolicAssertion)),
            SmtResult::Unproven(cause) | SmtResult::Error(cause) => return Err(refusal(frame, cause)),
        }
    }
    let _scope = stats::region_progress::QueryScope::enter("prefix_group_certification");
    let mut keep = Vec::with_capacity(frame.region_arrivals.len());
    for group in &frame.region_arrivals {
        check_time()?;
        let access = group.local_state.speculative_access.as_ref().unwrap();
        let guard = access.guard.as_ref().unwrap();
        match solver.check_region_prefix_candidate(guard, info) {
            SmtResult::Sat
                if access.ordered_events && !access.global_state && !access.writes.modified_regs.is_empty() =>
            {
                // 组发布在末尾补发寄存器写。要求严格顺序的路径从原入口保留原始事件次序。
                return Err(reject(group, SpeculativeRejectReason::RegisterSequence));
            }
            SmtResult::Sat => keep.push(true),
            SmtResult::Unsat => keep.push(false),
            SmtResult::Unproven(cause) | SmtResult::Error(cause) => return Err(refusal(group, cause)),
        }
    }
    check_time()?;
    let mut keep = keep.into_iter();
    frame.region_arrivals.retain(|_| keep.next().unwrap());
    Ok(())
}

pub(super) fn record_count<B: BV>(frame: &LocalFrame<B>, record_start: usize) -> usize {
    frame.region_arrivals.iter().map(|arm| arm.region_merge_records.len() - record_start).sum()
}
