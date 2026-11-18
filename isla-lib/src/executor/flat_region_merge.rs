//! 单队列区域推演。片段共享一个根事务；每段只有完整守卫作用域，不创建嵌套保存点。
use super::region_engine::{advance_arm, append_loop_exit, branch_arm, finish_arrivals, loop_exit_guard};
use super::region_merge::{self, RegionOutput, RegionResult};
use super::region_summary::function_effect_summaries;
use super::stats::merge_diagnostics as diagnostics;
use super::*;
use crate::config::MergeMode;
use crate::ir::regions::Region;
use std::collections::VecDeque;

/// 挂起到同一队列；callee 的调用实例由完整帧及 AccessLog::call_scope 保留。
pub(super) fn suspend<'ir, B: BV>(
    condition: Sym,
    target: usize,
    frame: &mut LocalFrame<'ir, B>,
    state: &TaskState<B>,
    shared: &SharedState<'ir, B>,
    info: SourceLoc,
) -> Result<RegionResult, ExecError> {
    let global = state.execution_limits.as_ref().is_some_and(|limits| limits.region_global_state);
    let summaries = state.region_effect_summaries.get_or_init(|| function_effect_summaries(shared, global));
    let candidate = region_merge::region(
        frame,
        shared,
        summaries,
        state.execution_limits.as_ref().is_some_and(|limits| limits.region_loop_analysis),
    )?;
    let execution = frame.region_execution.as_mut().unwrap();
    assert!(execution.pending_branch.is_none(), "平铺分叉必须先被队列消费");
    execution.pending_branch = Some((condition, target, candidate, info));
    Ok(RegionResult::Suspended)
}

/// 等待项保存分叉前状态和到达状态；编号只是汇合依赖，不对应事务层数。
struct Join<'ir, B> {
    original: LocalFrame<'ir, B>,
    base: LocalFrame<'ir, B>,
    region: Arc<Region>,
    condition: Sym,
    info: SourceLoc,
    record: usize,
    destination: Option<(usize, usize)>,
    arrivals: [Vec<LocalFrame<'ir, B>>; 2],
    waiting: [usize; 2],
    loop_prefix: Option<Box<LoopPrefix<'ir, B>>>,
    iteration: usize,
}

/// 循环退出前沿与最初的恢复上下文；轮次只属于同一调用实例和 PC。
struct LoopPrefix<'ir, B> {
    original: LocalFrame<'ir, B>,
    base: LocalFrame<'ir, B>,
    exits: Vec<LocalFrame<'ir, B>>,
    record: usize,
}

enum Work<'ir, B> {
    Run(LocalFrame<'ir, B>, (usize, usize)),
    Dead((usize, usize)),
}

#[allow(clippy::too_many_arguments)]
pub(super) fn execute_region<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
    condition: Sym,
    target: usize,
    region: Arc<Region>,
    depth: usize,
    mode: MergeMode,
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
) -> Result<RegionOutput<'ir, B>, ExecError> {
    assert_eq!(depth, 1, "平铺执行只能从根尝试进入");
    assert!(frame.region_execution.is_none());
    assert_eq!(solver.transaction_depth(), 1, "平铺片段共用一个根保存点");
    let mut ready = VecDeque::<Work<B>>::new();
    let mut joins = Vec::<Option<Join<B>>>::new();
    let mut branches = VecDeque::from([(frame.clone(), condition, target, region, info, None, None, 0usize)]);
    loop {
        while let Some((original, condition, target, region, info, destination, loop_prefix, iteration)) =
            branches.pop_front()
        {
            let base = if iteration == 0 {
                let region_depth = original.region_execution.as_ref().map_or(depth, |parent| parent.depth + 1);
                region_merge::prepare_region_base(&original, &region, region_depth, mode, state, info)
            } else {
                let mut base = original.clone();
                // 此处仅发布同一循环的下一轮，不再建立新的区域或重授半轮预算。
                base.region_execution.as_mut().unwrap().region = region.clone();
                base
            };
            let index = joins.len();
            for (side, pc, arm_guard) in [
                (0, target, smtlib::Exp::Var(condition)),
                (1, original.pc + 1, smtlib::Exp::Not(Box::new(smtlib::Exp::Var(condition)))),
            ] {
                let owner = solver.new_logical_arm(original.region_arm);
                let mut arm = branch_arm(&base, pc, arm_guard, owner);
                let access = cost::make_mut(&mut arm.local_state).speculative_access.as_mut().unwrap();
                // 定义共享完整守卫，嵌套 if 不复制整棵守卫树。
                access.guard = Some(smtlib::Exp::Var(solver.define_const(access.guard.take().unwrap(), info)));
                ready.push_back(Work::Run(arm, (index, side)));
            }
            let record = region_merge::NEXT_RECORD
                .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
                .expect("合并记录编号溢出");
            joins.push(Some(Join {
                original,
                base,
                region,
                condition,
                info,
                record,
                destination,
                arrivals: [Vec::new(), Vec::new()],
                waiting: [1, 1],
                loop_prefix,
                iteration,
            }));
        }
        let (destination, arrived) = match ready.pop_front().expect("未闭合的汇合必须有就绪片段") {
            Work::Dead(destination) => (destination, None),
            Work::Run(mut arm, destination) => {
                let owner = arm.region_arm.expect("片段必须有逻辑臂");
                let guard = arm.local_state.speculative_access.as_ref().unwrap().guard.clone().unwrap();
                let tx = solver.start_transaction_with_guard(Some(guard));
                let alive = solver
                    .with_logical_arm(owner, |solver| {
                        advance_arm(
                            tid, task_id, fraction, timeout, stop, sink, &mut arm, state, shared, solver, tx, info,
                        )
                    })?
                    .expect("平铺子区域只由队列产生多个片段");
                if alive {
                    (destination, Some(arm))
                } else {
                    solver.discard_logical_arm_effects(owner);
                    (destination, None)
                }
            }
        };
        let (index, side) = destination;
        if let Some(mut arm) = arrived {
            // 惰性初值沿同一调用作用域广播；任何已初始化/已写槽位都不会被覆盖。
            for pending in &mut ready {
                if let Work::Run(frame, _) = pending {
                    region_merge::promote_initials(frame, &arm, shared, solver);
                }
            }
            for join in joins.iter_mut().flatten() {
                region_merge::promote_initials(&mut join.base, &arm, shared, solver);
                if join.original.local_state.speculative_access.is_some() {
                    region_merge::promote_initials(&mut join.original, &arm, shared, solver);
                }
                for arrived in join.arrivals.iter_mut().flatten() {
                    region_merge::promote_initials(arrived, &arm, shared, solver);
                }
                if let Some(prefix) = &mut join.loop_prefix {
                    region_merge::promote_initials(&mut prefix.base, &arm, shared, solver);
                    for exit in &mut prefix.exits {
                        region_merge::promote_initials(exit, &arm, shared, solver);
                    }
                    if prefix.original.local_state.speculative_access.is_some() {
                        region_merge::promote_initials(&mut prefix.original, &arm, shared, solver);
                    }
                }
            }
            if let Some((condition, target, region, info)) =
                arm.region_execution.as_mut().unwrap().pending_branch.take()
            {
                let join = joins[index].as_ref().unwrap();
                let next_round = join.region.has_back_edge
                    && region.branch_pc == join.region.branch_pc
                    && region.join == join.region.join
                    && arm.function_name == join.base.function_name
                    && arm.backtrace.len() == join.base.backtrace.len()
                    && arm.local_state.speculative_access.as_ref().unwrap().call_scope
                        == join.base.local_state.speculative_access.as_ref().unwrap().call_scope;
                if next_round {
                    arm.region_execution.as_mut().unwrap().pending_branch = Some((condition, target, region, info));
                } else {
                    branches.push_back((arm, condition, target, region, info, Some((index, side)), None, 0));
                    continue;
                }
            }
            let join = joins[index].as_mut().expect("到达状态必须属于活动汇合");
            assert_eq!(arm.function_name, join.base.function_name, "不同函数不能汇合");
            assert_eq!(arm.backtrace.len(), join.base.backtrace.len(), "不同调用深度不能汇合");
            assert_eq!(
                arm.local_state.speculative_access.as_ref().unwrap().call_scope,
                join.base.local_state.speculative_access.as_ref().unwrap().call_scope,
                "不同调用实例不能汇合"
            );
            join.arrivals[side].push(arm);
        }
        let join = joins[index].as_mut().expect("到达状态必须属于活动汇合");
        join.waiting[side] = join.waiting[side].checked_sub(1).expect("片段只能到达一次");
        if join.waiting != [0, 0] {
            continue;
        }
        let mut join = joins[index].take().unwrap();
        let continuing: Vec<_> = join
            .arrivals
            .iter()
            .enumerate()
            .flat_map(|(side, arms)| {
                arms.iter().enumerate().filter_map(move |(i, arm)| {
                    arm.region_execution.as_ref().unwrap().pending_branch.as_ref().map(|_| (side, i))
                })
            })
            .collect();
        if !continuing.is_empty() {
            if continuing.len() > 1 {
                let iteration = join.iteration.checked_add(1).expect("循环轮次溢出");
                for (side, arrivals) in join.arrivals.iter_mut().enumerate() {
                    let mut exits = Vec::new();
                    for mut part in std::mem::take(arrivals) {
                        if let Some((condition, target, region, info)) =
                            part.region_execution.as_mut().unwrap().pending_branch.take()
                        {
                            branches.push_back((
                                part,
                                condition,
                                target,
                                region,
                                info,
                                Some((index, side)),
                                None,
                                iteration,
                            ));
                            join.waiting[side] += 1;
                        } else {
                            exits.push(part);
                        }
                    }
                    *arrivals = exits;
                }
                joins[index] = Some(join);
                continue;
            }
            let (side, piece) = continuing[0];
            let mut continued = join.arrivals[side].remove(piece);
            let mut exits = join.arrivals.into_iter().flatten();
            let mut prefix = join.loop_prefix.take();
            for exit in &mut exits {
                let prefix = prefix.get_or_insert_with(|| {
                    Box::new(LoopPrefix {
                        original: join.original.clone(),
                        base: join.base.clone(),
                        exits: Vec::new(),
                        record: join.record,
                    })
                });
                append_loop_exit(&mut prefix.exits, exit, solver, |previous, next, solver| {
                    fold_exits(previous, next, &prefix.base, &join.region, state, shared, solver, join.info)
                })?;
            }
            let (condition, target, region, info) =
                continued.region_execution.as_mut().unwrap().pending_branch.take().unwrap();
            let iteration = join.iteration.checked_add(1).expect("循环轮次溢出");
            if super::stats::region_progress::enabled() {
                eprintln!(
                    "{}",
                    serde_json::json!({"kind":"flat_loop_iteration_fold", "function":diagnostics::name_string(continued.function_name,&shared.symtab),
                    "pc":region.branch_pc,"call_instance":continued.local_state.call_instance,"iteration":iteration,"logical_frontiers":2,"savepoint_depth":solver.transaction_depth()})
                );
            }
            branches.push_back((continued, condition, target, region, info, join.destination, prefix, iteration));
            continue;
        }
        let join_pc = join.arrivals.iter().flatten().next().map(|arm| arm.pc);
        if let Some(pc) = join_pc {
            if !join.arrivals.iter().flatten().all(|arm| arm.pc == pc) {
                // 虚拟函数出口可能对应不同的 End；原平铺模式仅合并相同 PC。
                return Err(region_merge::reject(&join.original, SpeculativeRejectReason::RegionEscaped));
            }
            prepare_states(&mut [&mut join.base], pc, state, shared);
        }
        let guard =
            join.base.local_state.speculative_access.as_ref().unwrap().guard.clone().unwrap_or(smtlib::Exp::Bool(true));
        let mut restored = if join.loop_prefix.is_some() { join.base.clone() } else { join.original.clone() };
        let finish = |solver: &mut Solver<B>| {
            solver.with_transaction_condition(&guard, |solver| {
                finish_arrivals(
                    join.record,
                    join.condition,
                    &join.region,
                    &join.base,
                    join.arrivals,
                    &mut restored,
                    state,
                    shared,
                    solver,
                    join.info,
                    |arms| {
                        if let Some(pc) = join_pc {
                            let mut states: Vec<_> = arms.iter_mut().flatten().collect();
                            prepare_states(&mut states, pc, state, shared);
                        }
                    },
                )
            })
        };
        let result = match join.original.region_arm {
            Some(owner) => solver.with_logical_arm(owner, finish),
            None => finish(solver),
        }?;
        if let RegionResult::Separate(reason) = result {
            let Some(destination) = join.destination else {
                return Err(region_merge::reject(&join.original, reason));
            };
            let mut pieces = std::mem::take(&mut restored.region_arrivals);
            if let Some(prefix) = join.loop_prefix.take() {
                pieces.extend(prefix.exits);
                for piece in &mut pieces {
                    piece.region_execution = prefix.original.region_execution.clone();
                    piece.speculation_mode = prefix.original.speculation_mode;
                }
            }
            let parent = joins[destination.0].as_mut().unwrap();
            parent.waiting[destination.1] =
                parent.waiting[destination.1].checked_add(pieces.len() - 1).expect("片段数量溢出");
            for part in pieces {
                ready.push_back(Work::Run(part, destination));
            }
            continue;
        }
        let mut result = result;
        if let Some(mut prefix) = join.loop_prefix.take() {
            if !matches!(result, RegionResult::Dead) {
                cost::make_mut(&mut restored.local_state).speculative_access.as_mut().unwrap().guard = Some(guard);
                append_loop_exit(&mut prefix.exits, restored, solver, |previous, next, solver| {
                    fold_exits(previous, next, &prefix.base, &join.region, state, shared, solver, join.info)
                })?;
            }
            let exit_guard = loop_exit_guard(&prefix.exits);
            let condition = solver.define_const(exit_guard.clone(), join.info);
            let parent_guard = prefix
                .original
                .local_state
                .speculative_access
                .as_ref()
                .and_then(|access| access.guard.clone())
                .unwrap_or(smtlib::Exp::Bool(true));
            let LoopPrefix { original, base, exits, record } = *prefix;
            restored = original;
            result = solver.with_transaction_condition(&parent_guard, |solver| {
                solver.assert_region_exit(exit_guard);
                finish_arrivals(
                    record,
                    condition,
                    &join.region,
                    &base,
                    [exits, Vec::new()],
                    &mut restored,
                    state,
                    shared,
                    solver,
                    join.info,
                    |_| (),
                )
            })?;
            if let RegionResult::Separate(reason) = result {
                let Some(destination) = join.destination else {
                    return Err(region_merge::reject(&join.original, reason));
                };
                let pieces = std::mem::take(&mut restored.region_arrivals);
                let parent = joins[destination.0].as_mut().unwrap();
                parent.waiting[destination.1] =
                    parent.waiting[destination.1].checked_add(pieces.len() - 1).expect("片段数量溢出");
                for part in pieces {
                    ready.push_back(Work::Run(part, destination));
                }
                continue;
            }
        }
        join.original = restored;
        if let Some(destination) = join.destination {
            ready.push_back(if matches!(result, RegionResult::Dead) {
                Work::Dead(destination)
            } else {
                Work::Run(join.original, destination)
            });
        } else {
            assert!(ready.is_empty() && joins.iter().all(Option::is_none), "根汇合后不得遗留片段");
            *frame = join.original;
            return Ok(RegionOutput::complete(result));
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn fold_exits<'ir, B: BV>(
    previous: LocalFrame<'ir, B>,
    mut next: LocalFrame<'ir, B>,
    base: &LocalFrame<'ir, B>,
    region: &Region,
    state: &TaskState<B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<LocalFrame<'ir, B>, ExecError> {
    let cost_scope = cost::Scope::enter(cost::Category::StateMerge);
    let _ = &cost_scope;
    if previous.pc != next.pc
        || previous.function_name != next.function_name
        || previous.backtrace.len() != next.backtrace.len()
    {
        return Err(region_merge::reject(&next, SpeculativeRejectReason::FlatLoopShape));
    }
    let mut previous = previous;
    let mut base = base.clone();
    let pc = previous.pc;
    prepare_states(&mut [&mut base, &mut previous, &mut next], pc, state, shared);
    region_merge::fold_loop_exit(previous, next, &base, region, state, shared, solver, info)
}

fn prepare_states<'ir, B: BV>(
    frames: &mut [&mut LocalFrame<'ir, B>],
    pc: usize,
    state: &TaskState<B>,
    shared: &SharedState<'ir, B>,
) {
    let loop_analysis = state.execution_limits.as_ref().is_some_and(|limits| limits.region_loop_analysis);
    let live = shared
        .function_regions
        .lock()
        .unwrap()
        .get(&(frames[0].function_name, loop_analysis))
        .unwrap()
        .continuation_locals(pc);
    for candidate in frames.iter_mut() {
        candidate.vars_mut().retain(|name, _| live.contains(name));
    }
    if !state.execution_limits.as_ref().unwrap().ordered_events {
        // 足迹按集合合并，不为互斥臂寻找共同访问顺序；实际事件仍带完整守卫。
        for candidate in frames.iter_mut() {
            let access = cost::make_mut(&mut candidate.local_state).speculative_access.as_mut().unwrap();
            access.writes.register_write_order.sort_unstable();
            let mut reads: Vec<_> = access.reads.drain(..).zip(access.read_guards.drain(..)).collect();
            reads.sort_by_key(|((reg, path, _), _)| {
                (
                    *reg,
                    path.iter()
                        .map(|accessor| match accessor {
                            Accessor::Field(name) => *name,
                        })
                        .collect::<Vec<_>>(),
                )
            });
            for (read, guard) in reads {
                access.reads.push(read);
                access.read_guards.push(guard);
            }
        }
    }
}
