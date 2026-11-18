//! 单队列区域推演。片段共享一个根事务；每段只有完整守卫作用域，不创建嵌套保存点。
use super::region_engine::finish_region;
use super::region_merge::{self, AccessLog, RegionExecution, RegionOutput, RegionResult};
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
    arrivals: [Option<LocalFrame<'ir, B>>; 2],
    loop_prefix: Option<Box<LoopPrefix<'ir, B>>>,
    iteration: usize,
}

/// 循环退出前沿与最初的恢复上下文；轮次只属于同一调用实例和 PC。
struct LoopPrefix<'ir, B> {
    original: LocalFrame<'ir, B>,
    base: LocalFrame<'ir, B>,
    exit: LocalFrame<'ir, B>,
    record: usize,
}

struct Fragment<'ir, B> {
    frame: LocalFrame<'ir, B>,
    destination: (usize, usize),
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
    let remaining = state.region_step_budget().map(|budget| Arc::new(AtomicUsize::new(budget)));
    let mut ready = VecDeque::<Fragment<B>>::new();
    let mut joins = Vec::<Option<Join<B>>>::new();
    let mut branch = Some((frame.clone(), condition, target, region, info, None, None, 0usize));
    loop {
        if let Some((original, condition, target, region, info, destination, loop_prefix, iteration)) = branch.take() {
            let mut base = original.clone();
            base.region_execution = Some(RegionExecution {
                region: region.clone(),
                entry_depth: base.backtrace.len(),
                write_depth: frame.backtrace.len(),
                depth: 1,
                remaining: remaining.clone(),
                iteration_budget: None,
                mode,
                origin: (frame.function_name, frame.pc, info),
                pending_branch: None,
            });
            base.speculation_mode = SpeculationMode::On;
            if base.local_state.speculative_access.is_none() {
                cost::make_mut(&mut base.local_state).speculative_access = Some(AccessLog {
                    writes: WriteSet::default(),
                    reads: Vec::new(),
                    published_reads: Vec::new(),
                    read_guards: Vec::new(),
                    guard: None,
                    initial_registers: HashMap::new(),
                    initial_variables: HashMap::new(),
                    initial_lets: HashMap::new(),
                    call_scope: region_merge::fresh_call_scope(),
                    function: base.function_name,
                    pc: base.pc,
                    location: info,
                    writes_allowed: true,
                    global_state: state.execution_limits.as_ref().is_some_and(|limits| limits.region_global_state),
                });
            }
            let index = joins.len();
            for (side, pc, arm_guard) in [
                (0, target, smtlib::Exp::Var(condition)),
                (1, original.pc + 1, smtlib::Exp::Not(Box::new(smtlib::Exp::Var(condition)))),
            ] {
                let mut arm = base.clone();
                arm.pc = pc;
                let access = cost::make_mut(&mut arm.local_state).speculative_access.as_mut().unwrap();
                let guard = match access.guard.take() {
                    Some(parent) => smtlib::Exp::And(Box::new(parent), Box::new(arm_guard)),
                    None => arm_guard,
                };
                // 定义共享完整守卫，嵌套 if 不复制整棵守卫树。
                access.guard = Some(smtlib::Exp::Var(solver.define_const(guard, info)));
                ready.push_back(Fragment { frame: arm, destination: (index, side) });
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
                arrivals: [None, None],
                loop_prefix,
                iteration,
            }));
        }
        let Fragment { frame: mut arm, destination: (index, side) } =
            ready.pop_front().expect("未闭合的汇合必须有就绪片段");
        let guard = arm.local_state.speculative_access.as_ref().unwrap().guard.clone().unwrap();
        let outcome = solver.with_transaction_condition(&guard, |solver| {
            let result = run_loop(tid, task_id, fraction, timeout, stop, sink, &mut arm, state, shared, solver)?;
            match result {
                Run::Suspended => {
                    match solver.check_sat_for_arm(info) {
                        None | Some(SmtResult::Sat) => (),
                        Some(SmtResult::Unsat) => {
                            return Err(region_merge::reject(&arm, SpeculativeRejectReason::FlatDeadArm))
                        }
                        Some(SmtResult::Unknown) => {
                            return Err(region_merge::reject(&arm, SpeculativeRejectReason::SolverUnknown))
                        }
                        Some(SmtResult::Error(error)) => return Err(ExecError::Smt(error)),
                    }
                    Ok(())
                }
                Run::Dead => Err(region_merge::reject(&arm, SpeculativeRejectReason::FlatDeadArm)),
                _ => Err(region_merge::reject(&arm, SpeculativeRejectReason::RegionEscaped)),
            }
        });
        match outcome {
            Ok(()) => (),
            Err(ExecError::AssertionFailure(..)) => {
                return Err(region_merge::reject(&arm, SpeculativeRejectReason::FlatDeadArm))
            }
            Err(ExecError::Z3Unknown) => {
                return Err(region_merge::reject(&arm, SpeculativeRejectReason::SolverUnknown))
            }
            Err(error) => return Err(error),
        }
        // 惰性初值沿同一调用作用域广播；任何已初始化/已写槽位都不会被覆盖。
        for pending in &mut ready {
            region_merge::promote_initials(&mut pending.frame, &arm, shared, solver);
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
                region_merge::promote_initials(&mut prefix.exit, &arm, shared, solver);
                if prefix.original.local_state.speculative_access.is_some() {
                    region_merge::promote_initials(&mut prefix.original, &arm, shared, solver);
                }
            }
        }
        if let Some((condition, target, region, info)) = arm.region_execution.as_mut().unwrap().pending_branch.take() {
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
                branch = Some((arm, condition, target, region, info, Some((index, side)), None, 0));
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
        assert!(join.arrivals[side].replace(arm).is_none(), "每个分叉臂只能到达一次");
        if join.arrivals.iter().any(Option::is_none) {
            continue;
        }
        let mut join = joins[index].take().unwrap();
        let continuing: Vec<_> = join
            .arrivals
            .iter()
            .enumerate()
            .filter_map(|(side, arm)| {
                arm.as_ref().unwrap().region_execution.as_ref().unwrap().pending_branch.as_ref().map(|_| side)
            })
            .collect();
        if !continuing.is_empty() {
            if continuing.len() != 1 {
                return Err(region_merge::reject(&join.original, SpeculativeRejectReason::FlatLoopShape));
            }
            let side = continuing[0];
            let mut continued = join.arrivals[side].take().unwrap();
            let exit = join.arrivals[1 - side].take().unwrap();
            let prefix = match join.loop_prefix.take() {
                None => Box::new(LoopPrefix { original: join.original, base: join.base, exit, record: join.record }),
                Some(mut prefix) => {
                    prefix.exit =
                        fold_exits(prefix.exit, exit, &prefix.base, &join.region, state, shared, solver, join.info)?;
                    prefix
                }
            };
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
            branch = Some((continued, condition, target, region, info, join.destination, Some(prefix), iteration));
            continue;
        }
        // caller 局部值与返回 continuation 来自同一个分叉前状态，直接共享。
        let left = join.arrivals[0].as_ref().unwrap();
        let right = join.arrivals[1].as_ref().unwrap();
        // 臂中临时调用的 push/pop 可能产生内容相同但地址不同的 CoW 容器。
        assert_eq!(left.stack_vars.len(), right.stack_vars.len(), "caller 层数必须相同");
        for (a, b) in left.stack_vars.iter().zip(right.stack_vars.iter()) {
            assert_eq!(a.len(), b.len(), "caller 槽位必须相同");
            for (name, value) in a {
                assert!(
                    match (value, b.get(name)) {
                        (UVal::Init(a), Some(UVal::Init(b))) => a == b,
                        (UVal::Uninit(a), Some(UVal::Uninit(b))) => a == b,
                        _ => false,
                    },
                    "平铺汇合不能修改 caller 局部值"
                );
            }
        }
        match (&left.stack_call, &right.stack_call) {
            (Some(a), Some(b)) => assert!(Arc::ptr_eq(a, b), "返回 continuation 必须相同"),
            (None, None) => (),
            _ => panic!("返回 continuation 不匹配"),
        }
        let pc = left.pc;
        let mut states: Vec<_> = std::iter::once(&mut join.base).chain(join.arrivals.iter_mut().flatten()).collect();
        prepare_states(&mut states, pc, state, shared);

        if join.arrivals[0].as_ref().unwrap().pc != join.arrivals[1].as_ref().unwrap().pc {
            // 虚拟函数出口可对应多个 End；本原型只合并同一个实际 PC。
            return Err(region_merge::reject(&join.original, SpeculativeRejectReason::RegionEscaped));
        }
        let guard =
            join.base.local_state.speculative_access.as_ref().unwrap().guard.clone().unwrap_or(smtlib::Exp::Bool(true));
        let mut restored = if join.loop_prefix.is_some() { join.base.clone() } else { join.original.clone() };
        let result = solver.with_transaction_condition(&guard, |solver| {
            finish_region(
                join.record,
                join.condition,
                &join.region,
                &join.base,
                join.arrivals.into_iter().collect(),
                &mut restored,
                state,
                shared,
                solver,
                join.info,
            )
        })?;
        assert!(matches!(result, RegionResult::Merged), "当前平铺原型只接纳正常双臂汇合");
        if let Some(prefix) = join.loop_prefix.take() {
            cost::make_mut(&mut restored.local_state).speculative_access.as_mut().unwrap().guard = Some(guard);
            let complete =
                fold_exits(prefix.exit, restored, &prefix.base, &join.region, state, shared, solver, join.info)?;
            let exit_guard = complete.local_state.speculative_access.as_ref().unwrap().guard.clone().unwrap();
            let condition = solver.define_const(exit_guard.clone(), join.info);
            let parent_guard = prefix
                .original
                .local_state
                .speculative_access
                .as_ref()
                .and_then(|access| access.guard.clone())
                .unwrap_or(smtlib::Exp::Bool(true));
            restored = prefix.original;
            solver.with_transaction_condition(&parent_guard, |solver| {
                solver.assert_region_exit(exit_guard);
                finish_region(
                    prefix.record,
                    condition,
                    &join.region,
                    &prefix.base,
                    vec![Some(complete), None],
                    &mut restored,
                    state,
                    shared,
                    solver,
                    join.info,
                )
            })?;
        }
        join.original = restored;
        if let Some(destination) = join.destination {
            ready.push_back(Fragment { frame: join.original, destination });
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
    region_merge::fold_exit_frontiers(previous, next, &base, region, state, shared, solver, info)
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
