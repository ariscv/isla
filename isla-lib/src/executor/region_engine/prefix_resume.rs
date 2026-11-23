//! 已认证前缀的失败指令按普通语义继续，区域外的任务仍只由根发布。
use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(in crate::executor) struct Site {
    function: Name,
    pc: usize,
    depth: usize,
}

fn site<B>(frame: &LocalFrame<B>) -> Site {
    Site { function: frame.function_name, pc: frame.pc, depth: frame.backtrace.len() }
}

/// 只给失败前沿标记一次指令位置。同指令的候选继续继承标记。
pub(in crate::executor) fn prepare<B>(frame: &mut LocalFrame<B>, rejection: &ExecError) {
    assert!(matches!(rejection, ExecError::SpeculativeReject { .. }), "前缀恢复必须带拒绝原因");
    frame.prefix_resume = Some(site(frame));
}

pub(in crate::executor) fn active<B>(frame: &LocalFrame<B>) -> bool {
    frame.prefix_resume.is_some_and(|resume| resume == site(frame))
}

/// 指令进入下一位置后立即关闭普通查询，继续由父区域收集义务。
pub(in crate::executor) fn next_instruction<B: BV>(frame: &mut LocalFrame<B>, solver: &mut Solver<B>) {
    if frame.prefix_resume.is_some() && !active(frame) {
        frame.prefix_resume = None;
        solver.end_region_resume_queries();
    }
}

pub(in crate::executor) fn split_operand<B: BV>(
    guards: [smtlib::Exp<Sym>; 2],
    frame: &mut LocalFrame<B>,
    solver: &mut Solver<B>,
) -> Result<(), ExecError> {
    let pc = frame.pc;
    cost::make_mut(&mut frame.execution_limit_state).record_fork();
    region_merge::separate_nested_fragments(frame, solver, guards.map(|guard| (pc, guard)))?;
    for (side, part) in frame.region_arrivals.iter_mut().enumerate() {
        cost::make_mut(&mut part.execution_limit_state).advance_path_signature(side == 0);
    }
    Ok(())
}
