//! 在实际捕获点汇合普通返回与异常返回，两侧独立执行相同的调用者延续。
use super::*;
use crate::ir::regions::exception_polarity;

pub(super) struct Catcher<'ir, B> {
    function: Name,
    instrs: &'ir [Instr<Name, B>],
    region: Arc<Region>,
    start: usize,
}

pub(super) fn find_catcher<'ir, B: BV>(
    frame: &LocalFrame<'ir, B>,
    callee_region: &Region,
    shared: &SharedState<'ir, B>,
) -> Option<Catcher<'ir, B>> {
    if frame.stack_call.is_none() || !callee_region.nodes.iter().any(|pc| matches!(frame.instrs[*pc], Instr::Arbitrary))
    {
        return None;
    }
    let (&(function, caller_pc), ancestry) = frame.backtrace.split_last()?;
    let caller_depth = ancestry.len();
    let &(_, _, instrs) = shared.functions.get(&function)?;
    if !matches!(instrs.get(caller_pc), Some(Instr::Call(_, _, callee, ..)) if *callee == frame.function_name) {
        return None;
    }
    let start = caller_pc + 1;
    let is_exception_check =
        |pc| matches!(instrs.get(pc), Some(Instr::Jump(exp, ..)) if exception_polarity(exp, HAVE_EXCEPTION).is_some());
    if !is_exception_check(start) {
        return None;
    }
    let mut analysis = FunctionRegions::with_options(
        instrs,
        RegionOptions {
            bounded_loops: false,
            filter_assertion_failures: true,
            recreated_slot_liveness: true,
            have_exception: None,
            terminal_calls: &[],
        },
    );
    let mut region = (*analysis.region(start).ok()?).clone();
    while let RegionPoint::Instruction(join) = region.join {
        if join <= region.branch_pc {
            return None;
        }
        if !is_exception_check(join) {
            break;
        }
        let next = analysis.region(join).ok()?;
        region.nodes.insert(join);
        region.nodes.extend(&next.nodes);
        region.local_variables.extend(&next.local_variables);
        region.join = next.join;
    }
    let RegionPoint::Instruction(join) = region.join else { return None };
    if !region.nodes.iter().any(|pc| matches!(&instrs[*pc], Instr::Copy(Loc::Id(HAVE_EXCEPTION), Exp::Bool(false), _)))
    {
        return None;
    }
    // 延续从实际返回位置进入，第一条异常检查也要执行。
    region.nodes.insert(start);
    if let Some(parent) = &frame.region_execution {
        let &(_, parent_call) = frame.backtrace.get(parent.entry_depth)?;
        if !parent.region.nodes.contains(&parent_call) || parent.region.join == RegionPoint::Instruction(parent_call) {
            return None;
        }
        if caller_depth == parent.entry_depth {
            let parent_exit = |pc| {
                parent.region.join == RegionPoint::Instruction(pc)
                    || (parent.region.join == RegionPoint::FunctionExit
                        && (matches!(instrs.get(pc), Some(Instr::End))
                            || (parent.catch_return.is_some() && matches!(instrs.get(pc), Some(Instr::Arbitrary)))))
            };
            // 捕获可以恰好到父出口。父出口上的指令仍交回父组织者执行。
            if region.nodes.iter().any(|pc| !parent.region.nodes.contains(pc) || parent_exit(*pc))
                || !(parent_exit(join) || parent.region.nodes.contains(&join))
            {
                return None;
            }
        }
    }
    Some(Catcher { function, instrs, region: Arc::new(region), start })
}

#[allow(clippy::too_many_arguments)]
pub(super) fn finish_catch<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
    catcher: Catcher<'ir, B>,
    record_id: usize,
    condition: Sym,
    mut base: LocalFrame<'ir, B>,
    arms: [Vec<LocalFrame<'ir, B>>; 2],
    tid: usize,
    task_id: TaskId,
    fraction: &mut Fraction,
    timeout: PathTimeout,
    stop: Option<&'task StopConditions>,
    sink: &S,
    frame: &mut LocalFrame<'ir, B>,
    state: &'task TaskState<B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<RegionResult, ExecError> {
    let mut execution = base.region_execution.take().unwrap();
    execution.region = Arc::clone(&catcher.region);
    execution.entry_depth -= 1;
    if frame.region_execution.is_none() {
        execution.write_depth = execution.entry_depth;
    }

    let mut reached = [Vec::new(), Vec::new()];
    for (side, arrivals) in arms.into_iter().enumerate() {
        for mut part in arrivals {
            assert!(Arc::ptr_eq(part.stack_call.as_ref().unwrap(), base.stack_call.as_ref().unwrap()));
            part.region_execution = Some(execution.clone());
            let owner = part.region_arm.unwrap();
            let guard = part.local_state.speculative_access.as_ref().unwrap().guard.clone().unwrap();
            let tx = solver.start_transaction_with_guard(Some(guard));
            let alive = solver.with_logical_arm(owner, |solver| {
                advance_region_arm(
                    tid, task_id, fraction, timeout, stop, sink, &mut part, state, shared, solver, false, tx, info,
                )
            })?;
            if alive {
                if part.region_arrivals.is_empty() {
                    reached[side].push(part);
                } else {
                    reached[side].append(&mut part.region_arrivals);
                }
            } else {
                solver.discard_logical_arm_effects(owner);
            }
        }
    }
    // 声明和返回目的槽取自本次实际调用。只有已经清除异常的同一延续可合并。
    let mut caller = base.clone();
    pop_call_stack(&mut caller);
    cost::make_mut(&mut caller.backtrace).pop().expect("捕获必须发生在调用者");
    caller.function_name = catcher.function;
    caller.instrs = catcher.instrs;
    caller.pc = catcher.start;
    if let Some(first) = reached.iter().flatten().next() {
        caller.stack_call = first.stack_call.clone();
        let scope = first.local_state.speculative_access.as_ref().unwrap().call_scope;
        cost::make_mut(&mut caller.local_state).speculative_access.as_mut().unwrap().call_scope = scope;
    }
    for part in reached.iter().flatten() {
        assert_eq!(*part.backtrace, *caller.backtrace);
        assert_eq!(part.function_name, caller.function_name);
        if !matches!(part.lets().get(&HAVE_EXCEPTION), Some(UVal::Init(Val::Bool(false)))) {
            return Err(reject(part, SpeculativeRejectReason::ExceptionCheck));
        }
        promote_initials(&mut caller, part, solver);
    }
    let limits = state.execution_limits.as_ref().unwrap();
    let summaries = state.region_effect_summaries.get().expect("被调区域必须已建立效应摘要");
    with_function_regions(&caller, shared, summaries, limits.region_loop_analysis, |_| ());
    caller.region_execution = Some(execution);
    let mut restored = caller.clone();
    restored.region_execution = frame.region_execution.clone();
    restored.speculation_mode = frame.speculation_mode;
    let result = finish_arrivals(
        record_id,
        condition,
        &catcher.region,
        false,
        restored.region_execution.is_none(),
        &caller,
        reached,
        &mut restored,
        state,
        shared,
        solver,
        info,
    )?;
    *frame = restored;
    Ok(result)
}
