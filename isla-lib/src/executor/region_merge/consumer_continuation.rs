//! 不同位宽在生产指令的出口保留为分开的继续帧。临时槽位的最后
//! 一个使用点位于同一段直线代码时，尝试在那里重新汇合。
use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn try_join_after_last_use<'ir, 'task, B: BV>(
    condition: Sym,
    info: SourceLoc,
    tid: usize,
    task_id: TaskId,
    fraction: &mut Fraction,
    timeout: PathTimeout,
    stop: Option<&'task StopConditions>,
    pending_errors: &ArmErrorSink<'ir, 'task, B>,
    frame: &mut LocalFrame<'ir, B>,
    state: &'task TaskState<B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<Option<RegionResult>, ExecError> {
    let pc = frame.pc;
    let parent = frame.region_execution.as_ref();
    // 同一操作数继续枚举出的子区域须先把所有候选交给最外层生产指令。
    if parent.is_some_and(|execution| execution.region.branch_pc == pc) {
        return Ok(None);
    }
    let dest = match &frame.instrs[pc] {
        Instr::PrimopUnary(Loc::Id(dest), ..)
        | Instr::PrimopBinary(Loc::Id(dest), ..)
        | Instr::PrimopVariadic(Loc::Id(dest), ..)
        | Instr::Copy(Loc::Id(dest), ..)
            if *dest != RETURN && frame.vars().contains_key(dest) =>
        {
            *dest
        }
        _ => return Ok(None),
    };
    if frame.region_arrivals.iter().any(|part| part.pc != pc + 1) {
        return Ok(None);
    }
    let mut width = |part: &LocalFrame<'ir, B>| match part.vars().get(&dest) {
        Some(UVal::Init(value)) => crate::primop_util::merge_bit_width(value, solver, info).ok().flatten(),
        _ => None,
    };
    let Some(first) = width(&frame.region_arrivals[0]) else { return Ok(None) };
    if !frame.region_arrivals.iter().any(|part| width(part).is_some_and(|other| other != first)) {
        return Ok(None);
    }

    let global = state.execution_limits.as_ref().is_some_and(|limits| limits.region_global_state);
    let summaries = state.region_effect_summaries.get_or_init(|| function_effect_summaries(shared, global));
    let Some(join) = with_function_regions(frame, shared, summaries, true, |analysis| {
        for next in pc + 1..frame.instrs.len() {
            if parent.is_some_and(|execution| !execution.region.nodes.contains(&next)) {
                break;
            }
            if analysis.slot_unused_at(next, dest) {
                return (next > pc + 1).then_some(next);
            }
            // 只跟进同一动态调用中的直线计算。其余指令由原来的组织者处理。
            match &frame.instrs[next] {
                Instr::Decl(..)
                | Instr::Init(..)
                | Instr::Copy(..)
                | Instr::PrimopUnary(..)
                | Instr::PrimopBinary(..)
                | Instr::PrimopVariadic(..)
                    if instruction_effect(frame.function_name, next, &frame.instrs[next], shared, summaries, false)
                        .is_none() =>
                {
                    ()
                }
                _ => break,
            }
        }
        None
    }) else {
        return Ok(None);
    };
    let mode = policy(frame, state, info);
    let depth = parent.map_or(1, |execution| execution.depth + 1);
    let region = Arc::new(Region {
        branch_pc: pc,
        join: RegionPoint::Instruction(join),
        has_back_edge: false,
        nodes: ((pc + 1)..join).collect(),
        kind: crate::ir::regions::RegionKind::Reconvergent,
        local_variables: Default::default(),
    });
    let original_arrivals = std::mem::take(&mut frame.region_arrivals);
    let mut candidate = frame.clone();
    let mut arrivals = original_arrivals.clone();
    frame.region_arrivals = original_arrivals;
    let mut base = prepare_region_base(&candidate, &region, depth, mode, state, info);
    for part in &mut arrivals {
        part.region_execution = base.region_execution.clone();
        part.speculation_mode = base.speculation_mode;
    }
    let mut arm = base.clone();
    arm.region_arrivals = arrivals;
    let errors = ArmErrorSink::new();
    let tx = solver.start_transaction();
    let advance_tx = solver.start_transaction();
    let advanced = advance_region_arm(
        tid, task_id, fraction, timeout, stop, &errors, &mut arm, state, shared, solver, true, advance_tx, info,
    );
    let result = advanced.and_then(|alive| {
        let mut reached = if !alive {
            Vec::new()
        } else if arm.region_arrivals.is_empty() {
            vec![arm]
        } else {
            std::mem::take(&mut arm.region_arrivals)
        };
        // 保留各臂真实位宽直到最后一次使用完成。离开作用域后删除已证无用的临时槽。
        base.vars_mut().remove(&dest);
        for part in &mut reached {
            part.vars_mut().remove(&dest);
            promote_initials(&mut base, part, shared, solver);
        }
        finish_arrivals(
            next_region_record(),
            condition,
            &region,
            true,
            &base,
            [reached, Vec::new()],
            &mut candidate,
            state,
            shared,
            solver,
            info,
        )
    });
    match result {
        Ok(result) => {
            solver.commit_transaction();
            *frame = candidate;
            errors.forward(pending_errors);
            Ok(Some(result))
        }
        Err(error) => {
            solver.rollback_transaction(tx);
            match error {
                ExecError::SpeculativeReject { .. } => Ok(None),
                _ => Err(error),
            }
        }
    }
}
