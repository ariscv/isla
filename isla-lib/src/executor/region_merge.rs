//! 区域推演只调用真实执行循环；此模块负责边界、事务与状态合并。
use super::region_engine::{
    advance_arm, append_loop_exit, branch_arm, finish_arrivals, finish_region, loop_exit_guard,
    publish_committed_records, LoopDependencies,
};
use super::region_summary::{function_effect_summaries, instruction_effect, CachedReject, FunctionEffect};
use super::stats::merge_diagnostics as diagnostics;
use super::*;
use crate::config::MergeMode;
use crate::executor::stats::region_cost as cost;
use crate::ir::regions::{FunctionRegions, Region, RegionOptions, RegionPoint, RegionRejection};

/// 普通区域的两臂与调用共享预算；可收敛的只读循环按完整轮核算，单轮仍受限。
/// 这只限制一次合并尝试，不截断普通符号执行的路径；配置 -1 时不创建或续配计数器。
pub const DEFAULT_REGION_STEP_BUDGET: Option<usize> = None;
pub(super) static NEXT_RECORD: AtomicUsize = AtomicUsize::new(0);
static LOGGED_ITERATION_FOLDS: AtomicUsize = AtomicUsize::new(0);
static NEXT_CALL_SCOPE: AtomicUsize = AtomicUsize::new(0);
pub(super) fn fresh_call_scope() -> usize {
    NEXT_CALL_SCOPE
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |scope| scope.checked_add(1))
        .expect("调用作用域编号溢出")
}

#[derive(Clone)]
pub(super) struct RegionExecution {
    pub region: Arc<Region>,
    pub entry_depth: usize,
    pub write_depth: usize,
    pub depth: usize,
    pub remaining: Option<Arc<AtomicUsize>>,
    pub iteration_budget: Option<usize>,
    /// 与根区域共享：局部汇合失败额外产生的片段从同一个上限扣除。
    pub additional_fragments: Option<Arc<AtomicUsize>>,
    pub mode: MergeMode,
    pub origin: (Name, usize, SourceLoc),
    pub pending_branch: Option<(Sym, usize, Arc<Region>, SourceLoc)>,
}

#[derive(Clone, Debug)]
pub(super) struct AccessLog<B> {
    pub writes: WriteSet,
    pub reads: Vec<(Name, Vec<Accessor>, Val<B>)>,
    pub published_reads: Vec<(Name, Vec<Accessor>, Val<B>)>,
    pub read_guards: Vec<smtlib::Exp<Sym>>,
    pub guard: Option<smtlib::Exp<Sym>>,
    pub initial_registers: HashMap<Name, Val<B>>,
    pub initial_variables: HashMap<(usize, Name, Name), Val<B>>,
    pub initial_lets: HashMap<Name, Val<B>>,
    pub call_scope: usize,
    pub function: Name,
    pub pc: usize,
    pub location: SourceLoc,
    pub writes_allowed: bool,
    pub global_state: bool,
}

impl<B: BV> AccessLog<B> {
    /// 发布发生在真实读取处，保证读取先于使用它的 SMT 定义；第二臂复用已发布的同序号读取。
    /// 计数属于帧快照，死臂/拒绝回滚后不会抑制存活臂的事件。
    pub fn record_read(&mut self, reg: Name, accessor: Vec<Accessor>, value: Val<B>) -> Result<bool, ExecError> {
        let cost_scope = cost::Scope::enter(cost::Category::StateMerge);
        let _ = &cost_scope;
        if self.global_state {
            // 内部读取使用当前臂的值；前态足迹按寄存器和字段路径只记录一次。
            if self.writes.modified_regs.contains(&reg) {
                return Ok(false);
            }
            if let Some(index) = self.reads.iter().position(|(name, path, _)| *name == reg && *path == accessor) {
                // 内层仅一臂读取后，汇合点之后的读取可以扩大原足迹的条件。
                self.read_guards[index] = smtlib::Exp::Or(
                    Box::new(self.read_guards[index].clone()),
                    Box::new(self.guard.clone().expect("区域读取必须有臂条件")),
                );
                return Ok(false);
            }
        } else if !self.writes.register_write_order.is_empty() {
            return Err(self.reject(SpeculativeRejectReason::RegisterReadAfterWrite));
        }
        let occurrence = self.reads.iter().filter(|(name, path, _)| *name == reg && *path == accessor).count();
        let published = self.published_reads.iter().filter(|(name, path, _)| *name == reg && *path == accessor).count();
        self.initial_registers.entry(reg).or_insert_with(|| value.clone());
        self.writes.read_regs.insert(reg);
        self.read_guards.push(self.guard.clone().expect("区域读取必须有臂条件"));
        self.reads.push((reg, accessor.clone(), value.clone()));
        if occurrence < published {
            return Ok(false);
        }
        self.published_reads.push((reg, accessor, value));
        Ok(true)
    }

    pub fn reject(&self, reason: SpeculativeRejectReason) -> ExecError {
        ExecError::SpeculativeReject { reason, function: self.function, pc: self.pc, location: self.location }
    }
}

/// 初值提升跨过一层臂条件时，同步提升类型约束。当前 symbolic 唯一的显式
/// 合法性约束来自 union 标签；复合值的每个候选载荷也由 symbolic 无条件初始化。
fn assert_initial_type<B: BV>(value: &Val<B>, solver: &mut Solver<B>) {
    use smtlib::Exp::{Bool, Eq, Or, Var};
    match value {
        Val::SymbolicCtor(tag, possibilities) => {
            let valid = possibilities.keys().fold(Bool(false), |valid, ctor| {
                Or(Box::new(valid), Box::new(Eq(Box::new(Var(*tag)), Box::new(ctor.to_smt()))))
            });
            solver.assert_region_input_fact(valid);
            for value in possibilities.values() {
                assert_initial_type(value, solver);
            }
        }
        Val::Ctor(_, value) => assert_initial_type(value, solver),
        Val::Struct(fields) => {
            for value in fields.values() {
                assert_initial_type(value, solver);
            }
        }
        Val::Vector(values) | Val::List(values) => {
            for value in values {
                assert_initial_type(value, solver);
            }
        }
        _ => (),
    }
}

pub(super) fn reject<B: BV>(frame: &LocalFrame<B>, reason: SpeculativeRejectReason) -> ExecError {
    ExecError::SpeculativeReject {
        reason,
        function: frame.function_name,
        pc: frame.pc,
        location: frame.instrs.get(frame.pc).and_then(stats::instr_source_loc).unwrap_or(SourceLoc::unknown()),
    }
}

/// 判定各侧可行性。未查询的候选保留守卫，真实失败只丢弃被查询的一侧。
pub(super) fn feasible<B: BV>(
    frame: &LocalFrame<B>,
    solver: &mut Solver<B>,
    exp: &smtlib::Exp<Sym>,
    info: SourceLoc,
    shared: &SharedState<B>,
) -> Result<bool, ExecError> {
    let speculative = frame.region_execution.is_some();
    match solver.check_sat_with_for_branch(exp, info, speculative) {
        None => Ok(true),
        Some(SmtResult::Unknown) if speculative => Err(reject(frame, SpeculativeRejectReason::SolverUnknown)),
        Some(result) => path_is_feasible(result, frame, solver, shared),
    }
}

pub(super) fn path_is_feasible<B: BV>(
    result: SmtResult,
    frame: &LocalFrame<B>,
    solver: &Solver<B>,
    shared: &SharedState<B>,
) -> Result<bool, ExecError> {
    match result.is_sat() {
        Err(error)
            if super::stats::solver_failures::discard_solver_path(solver.on_unknown(), &error, frame, shared, None) =>
        {
            Ok(false)
        }
        result => result,
    }
}

pub(super) fn record_read<B: BV>(
    state: &mut LocalState<B>,
    reg: Name,
    accessor: Vec<Accessor>,
    value: Val<B>,
) -> Result<bool, ExecError> {
    let cost_scope = cost::Scope::enter(cost::Category::StateMerge);
    let _ = &cost_scope;
    match &mut state.speculative_access {
        Some(log) => log.record_read(reg, accessor, value),
        None => Ok(true),
    }
}

pub(super) fn record_write<B: BV>(state: &mut LocalState<B>, id: Name, register: bool) -> Result<(), ExecError> {
    let cost_scope = cost::Scope::enter(cost::Category::StateMerge);
    let _ = &cost_scope;
    if let Some(log) = &mut state.speculative_access {
        if register || state.lets.contains_key(&id) {
            if !log.global_state && !log.writes_allowed {
                return Err(log.reject(SpeculativeRejectReason::CalleeStateWrite));
            }
        }
        if register {
            let first = log.writes.modified_regs.insert(id);
            if !log.global_state && !first {
                return Err(log.reject(SpeculativeRejectReason::RepeatedRegisterWrite));
            }
            if !log.global_state && log.writes.read_regs.contains(&id) {
                return Err(log.reject(SpeculativeRejectReason::RegisterReadWrite));
            }
            if first {
                log.writes.register_write_order.push(id);
            }
        } else {
            log.writes.modified_vars.insert(id);
        }
    }
    Ok(())
}

pub(super) fn policy<B: BV>(frame: &LocalFrame<B>, state: &TaskState<B>, info: SourceLoc) -> MergeMode {
    let inherited = frame.region_execution.as_ref().map(|region| region.mode);
    let mode = state
        .execution_limits
        .as_ref()
        .map_or(MergeMode::Off, |limits| limits.merge_mode(frame.function_name, info, inherited));
    if frame.region_replay.is_some() && mode == MergeMode::Adaptive {
        MergeMode::Off
    } else {
        mode
    }
}

/// 本地校验每一步的真实栈深度；调用不会重新授予入口层的写许可。
pub(super) fn step<B: BV>(frame: &mut LocalFrame<B>) -> Result<bool, ExecError> {
    if let Some((depth, join)) = frame.region_replay {
        if frame.backtrace.len() < depth
            || (frame.backtrace.len() == depth
                && (join == RegionPoint::Instruction(frame.pc)
                    || (join == RegionPoint::FunctionExit && matches!(frame.instrs.get(frame.pc), Some(Instr::End)))))
        {
            frame.region_replay = None;
        }
    }
    let Some(execution) = &frame.region_execution else { return Ok(false) };
    let depth = frame.backtrace.len();
    if depth < execution.entry_depth {
        return Err(reject(frame, SpeculativeRejectReason::StackEscaped));
    }
    if depth == execution.entry_depth {
        if execution.region.join == RegionPoint::Instruction(frame.pc) {
            return Ok(true);
        }
        if execution.region.join == RegionPoint::FunctionExit && matches!(frame.instrs.get(frame.pc), Some(Instr::End))
        {
            return Ok(true);
        }
        // 重访入口本身不授予新预算；只有完整轮次与退出前沿收敛后，
        // execute_loop_region才可为下一轮更新预算。
        if !execution.region.nodes.contains(&frame.pc)
            && !(execution.region.has_back_edge && frame.pc == execution.region.branch_pc)
        {
            return Err(reject(frame, SpeculativeRejectReason::RegionEscaped));
        }
    }
    if let Some(remaining) = &execution.remaining {
        if remaining.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |remaining| remaining.checked_sub(1)).is_err() {
            return Err(reject(frame, SpeculativeRejectReason::StepBudget));
        }
    }
    let location = frame.instrs.get(frame.pc).and_then(stats::instr_source_loc).unwrap_or(SourceLoc::unknown());
    let log = cost::make_mut(&mut frame.local_state).speculative_access.as_mut().expect("区域推演必须启用访问记录");
    log.function = frame.function_name;
    log.pc = frame.pc;
    log.location = location;
    log.writes_allowed = depth == execution.write_depth;
    // 回边这一步仍须先成功扣费；只有当前轮确已完成，才授予下一轮预算。
    // 即使后续条件已具体化、不再产生pending_branch，也不能丢掉轮次边界。
    if let Some(budget) = execution.iteration_budget {
        if depth == execution.entry_depth
            && log.writes.modified_regs.is_empty()
            && matches!(frame.instrs.get(frame.pc), Some(Instr::Goto(target)) if *target < frame.pc)
        {
            execution.remaining.as_ref().expect("逐轮续配必须有有限预算").store(budget, Ordering::Relaxed);
        }
    }
    Ok(false)
}

pub(super) fn preflight<B: BV>(
    frame: &LocalFrame<B>,
    state: &TaskState<B>,
    shared: &SharedState<B>,
) -> Result<(), ExecError> {
    if frame.region_execution.is_none() {
        return Ok(());
    }
    let global_state = state.execution_limits.as_ref().is_some_and(|limits| limits.region_global_state);
    let summaries = state.region_effect_summaries.get_or_init(|| function_effect_summaries(shared, global_state));
    if matches!(&frame.instrs[frame.pc], Instr::Call(_, _, callee, _, _) if summaries.get(callee).is_some_and(|summary| summary.non_returning))
    {
        // 此调用是静态 CFG 的异常出口，推演必须在执行其任何效应之前离开区域。
        return Err(reject(frame, SpeculativeRejectReason::RegionEscaped));
    }
    // 注意（ATTENTION）：合并路径的内存读取为并集语义；需要精确内存读序列时不可信。
    // Custom 可执行设备 IO，Constrained 是任意闭包，均不能靠 solver 回滚外部效应。
    if matches!(&frame.instrs[frame.pc], Instr::PrimopVariadic(_, f, _, _)
        if primop::variadic_effect(*f) == Some(primop::Effect::ReadsMemory))
        && frame
            .memory()
            .regions()
            .iter()
            .any(|region| matches!(region, crate::memory::Region::Custom(..) | crate::memory::Region::Constrained(..)))
    {
        return Err(reject(frame, SpeculativeRejectReason::StateEffect));
    }
    if let Some(rejection) =
        instruction_effect(frame.function_name, frame.pc, &frame.instrs[frame.pc], shared, summaries)
    {
        return Err(rejection.error());
    }
    Ok(())
}

pub(super) fn region<'ir, B: BV>(
    frame: &LocalFrame<'ir, B>,
    shared: &SharedState<'ir, B>,
    summaries: &HashMap<Name, FunctionEffect>,
    loop_analysis: bool,
) -> Result<Arc<Region>, ExecError> {
    let mut cache = shared.function_regions.lock().unwrap();
    let analysis = cache.entry((frame.function_name, loop_analysis)).or_insert_with(|| {
        FunctionRegions::with_options(
            frame.instrs,
            RegionOptions {
                bounded_loops: loop_analysis,
                filter_assertion_failures: loop_analysis,
                recreated_slot_liveness: loop_analysis,
                have_exception: Some(shared.symtab.lookup(shared.symtab.to_str(HAVE_EXCEPTION))),
                terminal_calls: &summaries
                    .iter()
                    .filter_map(|(name, summary)| summary.non_returning.then_some(*name))
                    .collect::<Vec<_>>(),
            },
        )
        .with_constant_returns(
            summaries
                .iter()
                .filter_map(|(name, summary)| summary.constant_return.map(|value| (*name, value)))
                .collect(),
        )
    });
    analysis.region(frame.pc).map_err(|reason| {
        reject(
            frame,
            match reason {
                RegionRejection::NoJoin => SpeculativeRejectReason::NoJoin,
                RegionRejection::HasBackEdge => SpeculativeRejectReason::HasBackEdge,
                RegionRejection::ExceptionCheck => SpeculativeRejectReason::ExceptionCheck,
                RegionRejection::ExitsRegion { .. } => SpeculativeRejectReason::RegionEscaped,
                RegionRejection::NotJump => panic!("区域入口必须是 Jump"),
            },
        )
    })
}

/// 只有最外层、无架构写出、无控制流采样限制的有环函数出口区域才能分段。
/// 分段本身不猜测循环是否终止；它只将同一有限展开的前缀变成两个普通前沿。
fn can_segment<B: BV>(frame: &LocalFrame<B>, state: &TaskState<B>, mode: MergeMode) -> bool {
    frame.region_execution.is_none() && can_fold_iterations(state, mode)
}

fn can_fold_iterations<B: BV>(state: &TaskState<B>, mode: MergeMode) -> bool {
    if mode != MergeMode::Adaptive || state.pc_limit.is_some() {
        return false;
    }
    state.execution_limits.as_ref().is_some_and(|limits| {
        limits.max_forks_per_branch.is_none()
            && limits.max_forks_per_path.is_none()
            && limits.max_backjumps_per_loop.is_none()
            && limits.max_path_depth.is_none()
            && limits.max_fork_pct_per_branch.is_none()
            && limits.branch_region_limits.is_empty()
            && limits.region_fork_limits.is_empty()
    })
}

pub(super) struct RegionOutput<'ir, B> {
    result: RegionResult,
    continuation: Option<(Sym, LocalFrame<'ir, B>)>,
}
impl<'ir, B> RegionOutput<'ir, B> {
    pub(super) fn complete(result: RegionResult) -> Self {
        Self { result, continuation: None }
    }
}

pub(super) enum RegionResult {
    Merged,
    Dead,
    Rejected,
    /// 当前汇合不兼容；原片段已保留在挂起帧。
    Separate(SpeculativeRejectReason),
    /// 同一有环区域的后续轮次交回本层显式工作栈。
    Suspended,
}

/// 组织区域事务。可局部化的汇合失败保留原片段；其余推演拒绝沿原错误出口处理。
#[allow(clippy::too_many_arguments)]
pub(super) fn try_region<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
    condition: Sym,
    target: usize,
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
    let mode = policy(frame, state, info);
    let global_state = state.execution_limits.as_ref().is_some_and(|limits| limits.region_global_state);
    assert_ne!(mode, MergeMode::Off, "Off 不能进入区域合并");
    let nested = frame.region_execution.is_some();
    let flat = state
        .execution_limits
        .as_ref()
        .is_some_and(|limits| limits.merge_strategy == crate::config::MergeStrategy::Flat);
    if flat && nested {
        return super::flat_region_merge::suspend(condition, target, frame, state, shared, info);
    }
    // 同一调用层、同一出口的有环分叉属于当前展开，不另开递归事务。
    // 不同出口的内层循环仍走正常嵌套；其后续轮次由内层自己的工作栈接续。
    if frame.region_execution.as_ref().is_some_and(|execution| {
        execution.region.has_back_edge && execution.entry_depth == frame.backtrace.len() && execution.mode == mode
    }) {
        let summaries = state.region_effect_summaries.get_or_init(|| function_effect_summaries(shared, global_state));
        if let Ok(candidate) = region(frame, shared, summaries, true) {
            let execution = frame.region_execution.as_mut().unwrap();
            if candidate.has_back_edge
                && candidate.join == execution.region.join
                && candidate
                    .nodes
                    .iter()
                    .all(|pc| *pc == execution.region.branch_pc || execution.region.nodes.contains(pc))
            {
                assert!(execution.pending_branch.is_none(), "循环分叉必须先被本层消费");
                execution.pending_branch = Some((condition, target, candidate, info));
                return Ok(RegionResult::Suspended);
            }
        }
    }
    let mut diagnostics_attempt = diagnostics::enabled()
        .then(|| diagnostics::AttemptGuard::start(task_id.as_usize(), frame.function_name, frame.pc, &shared.symtab));
    let depth = frame.region_execution.as_ref().map_or(1, |execution| execution.depth + 1);
    if diagnostics::enabled() {
        diagnostics::record_depth(depth, frame.backtrace.len(), solver.transaction_depth());
    }
    shared.execution_stats.merge_attempt();
    let diagnostics_active = diagnostics_attempt.is_some();
    let rule = state
        .execution_limits
        .as_ref()
        .and_then(|limits| {
            limits.merge_rule(frame.function_name, info).or_else(|| {
                frame
                    .region_execution
                    .as_ref()
                    .and_then(|execution| limits.merge_rule(execution.origin.0, execution.origin.2))
            })
        })
        .map(|(rule, _)| rule);
    shared.execution_stats.rule_attempt(rule);
    let key = (frame.function_name, frame.pc);
    let cached = state.region_negative_cache.lock().unwrap().get(&key).copied();
    let candidate = if frame.region_replay.is_some() {
        Err(reject(frame, SpeculativeRejectReason::SymbolicAssertion))
    } else if frame.execution_limit_state.has_sampled_branch() {
        Err(reject(frame, SpeculativeRejectReason::SamplingState))
    } else {
        match cached {
            Some(cached) => {
                shared.execution_stats.merge_cache_hit();
                Err(cached.error())
            }
            None => region(
                frame,
                shared,
                state.region_effect_summaries.get_or_init(|| function_effect_summaries(shared, global_state)),
                state.execution_limits.as_ref().is_some_and(|limits| limits.region_loop_analysis),
            )
            .and_then(|region| {
                for pc in &region.nodes {
                    if let Some(rejection) = instruction_effect(
                        frame.function_name,
                        *pc,
                        &frame.instrs[*pc],
                        shared,
                        state.region_effect_summaries.get_or_init(|| function_effect_summaries(shared, global_state)),
                    ) {
                        return Err(rejection.error());
                    }
                }
                Ok(region)
            }),
        }
    };
    let replay_join = candidate.as_ref().ok().map(|region| region.join);
    let mut segmented = false;
    let result = match candidate {
        Err(error) => {
            if let ExecError::SpeculativeReject { reason, function, pc, location } = error {
                if !matches!(
                    reason,
                    SpeculativeRejectReason::SamplingState | SpeculativeRejectReason::SymbolicAssertion
                ) {
                    state
                        .region_negative_cache
                        .lock()
                        .unwrap()
                        .insert(key, CachedReject { reason, function, pc, location });
                }
                Err(CachedReject { reason, function, pc, location }.error())
            } else {
                Err(error)
            }
        }
        Ok(region) => {
            if region.has_back_edge && super::stats::region_progress::enabled() {
                cost::make_mut(&mut frame.local_state).loop_attempt_seen = true;
            }
            shared.execution_stats.merge_candidate();
            if crate::config::RegionOptions::current().merge_depth_limit().is_some_and(|limit| depth > limit) {
                if diagnostics::enabled() {
                    diagnostics::emit(serde_json::json!({"stage":"region_admission",
                        "at":{"function":diagnostics::name_string(frame.function_name,&shared.symtab),
                            "pc":frame.pc,"location":info,"region_depth":depth,
                            "call_depth":frame.backtrace.len(),"transaction_depth":solver.transaction_depth()},
                        "difference":"nesting_limit","reason":"nesting_limit"}));
                }
                Err(reject(frame, SpeculativeRejectReason::NestingLimit))
            } else {
                let record_start = frame.region_merge_records.len();
                let mut candidate_frame = solver.validates_candidates().then(|| frame.clone());
                let tx = solver.start_transaction();
                let defer = solver.defer_region_checks();
                let probe_context = (!nested && crate::smt::probe_query_timings_enabled()).then(|| {
                    serde_json::json!({
                    "attempt":super::stats::region_progress::probe_attempt_id(),"task":task_id.as_usize(),
                    "call_instance":frame.local_state.call_instance,
                    "function":zencode::decode(shared.symtab.to_str(frame.function_name)), "branch_pc":key.1})
                });
                let log_phase = |phase: &str, result: Option<&SmtResult>| {
                    if let Some(context) = &probe_context {
                        crate::smt::probe_query_event(|| {
                            serde_json::json!({"type":phase,"region":context,
                            "result":result.map(|r|format!("{r:?}"))})
                        });
                    }
                };
                let execute = |solver: &mut Solver<B>| {
                    log_phase("execute_start", None);
                    let execute_region = if flat { super::flat_region_merge::execute_region } else { execute_region };
                    let output = execute_region(
                        condition,
                        target,
                        region,
                        depth,
                        mode,
                        tid,
                        task_id,
                        fraction,
                        timeout,
                        stop,
                        sink,
                        match &mut candidate_frame {
                            Some(candidate) => candidate,
                            None => &mut *frame,
                        },
                        state,
                        shared,
                        solver,
                        info,
                    );
                    log_phase("execute_end", None);
                    if defer && !nested && output.is_ok() {
                        log_phase("obligation_start", None);
                        let _scope = stats::region_progress::QueryScope::enter("exit_obligations");
                        let checked = solver.check_deferred_assertions(info);
                        log_phase("obligation_end", checked.as_ref());
                        match checked {
                            None | Some(SmtResult::Unsat) => (),
                            Some(SmtResult::Sat) => {
                                return Err(reject(frame, SpeculativeRejectReason::SymbolicAssertion))
                            }
                            Some(SmtResult::Unknown) => {
                                return Err(reject(frame, SpeculativeRejectReason::SolverUnknown))
                            }
                            Some(SmtResult::Error(crate::error::SmtError::Unknown { .. }))
                                if solver.on_unknown() == crate::config::SolverOnUnknown::Dead =>
                            {
                                return Err(reject(frame, SpeculativeRejectReason::SolverUnknown));
                            }
                            Some(SmtResult::Error(error)) => return Err(ExecError::Smt(error)),
                        }
                    }
                    output
                };
                let result = if defer { solver.with_deferred_region_queries(execute) } else { execute(solver) };
                // 只有最外层出口查询可以验证候选；嵌套结果仍带着全部守卫。
                let result = if defer
                    && !nested
                    && result.as_ref().is_ok_and(|output| !matches!(output.result, RegionResult::Dead))
                {
                    log_phase("exit_check_start", None);
                    let _scope = stats::region_progress::QueryScope::enter("region_exit");
                    let checked = solver.check_candidate_sat(info);
                    log_phase("exit_check_end", checked.as_ref());
                    match checked {
                        None | Some(SmtResult::Sat) => result,
                        // 分段可能还有继续前沿；退出前沿为空不代表整次调用为空。
                        // 保守回滚，让普通执行分别判断两个前沿。
                        Some(SmtResult::Unsat) => Err(reject(frame, SpeculativeRejectReason::SolverUnknown)),
                        Some(SmtResult::Unknown) => Err(reject(frame, SpeculativeRejectReason::SolverUnknown)),
                        Some(SmtResult::Error(crate::error::SmtError::Unknown { .. }))
                            if solver.on_unknown() == crate::config::SolverOnUnknown::Dead =>
                        {
                            Err(reject(frame, SpeculativeRejectReason::SolverUnknown))
                        }
                        Some(SmtResult::Error(error)) => Err(ExecError::Smt(error)),
                    }
                } else {
                    result
                };
                let mut continuation = None;
                let result = result.map(|output| {
                    continuation = output.continuation;
                    output.result
                });
                match &result {
                    Ok(_) => {
                        assert!(!solver.transaction_invalid(), "区域提交前保存点必须有效");
                        log_phase("commit_start", None);
                        solver.commit_transaction();
                        log_phase("commit_end", None);
                        // 出口义务或可行性验证拒绝时，调用者帧仍停留在入口。
                        if let Some(candidate_frame) = candidate_frame {
                            *frame = candidate_frame;
                        }
                        if !nested {
                            crate::smt::probe_query_event(
                                || serde_json::json!({"type":"region_commit", "function":zencode::decode(shared.symtab.to_str(frame.function_name)), "branch_pc":key.1, "call_instance":frame.local_state.call_instance,"region":probe_context}),
                            );
                            publish_committed_records(frame, record_start, task_id, shared, solver);
                            if let Some((returned, mut continued)) = continuation.take() {
                                segmented = true;
                                publish_committed_records(&mut continued, record_start, task_id, shared, solver);
                                let fork_id = cost::make_mut(&mut frame.execution_limit_state).record_fork();
                                let other = cost::make_mut(&mut continued.execution_limit_state).record_fork();
                                assert_eq!(fork_id, other, "同一分段的两前沿必须继承相同fork计数");
                                cost::make_mut(&mut frame.execution_limit_state).advance_path_signature(true);
                                cost::make_mut(&mut continued.execution_limit_state).advance_path_signature(false);
                                frame.capture_path_smt_stats();
                                continued.capture_path_smt_stats();
                                let point = checkpoint(solver);
                                let condition = smtlib::Exp::Not(Box::new(smtlib::Exp::Var(returned)));
                                let frozen = super::trace_fork_frame_with_branch_condition!(
                                    &continued,
                                    continued.pc,
                                    condition.clone()
                                );
                                fraction.halve();
                                sink.submit(Task {
                                    id: task_id,
                                    fraction: fraction.clone(),
                                    frame: frozen,
                                    checkpoint: point,
                                    fork_cond: Some((
                                        smtlib::Def::Assert(condition),
                                        Event::Fork(fork_id, returned, 1, info),
                                    )),
                                    state,
                                    stop_conditions: stop,
                                });
                                solver.add_event(Event::Fork(fork_id, returned, 0, info));
                                solver.assert(smtlib::Exp::Var(returned));
                                super::btrace_push_branch_condition!(frame, smtlib::Exp::Var(returned));
                            }
                        }
                    }
                    Err(_) => solver.rollback_transaction(tx),
                }
                result
            }
        }
    };
    match result {
        Ok(RegionResult::Separate(reason)) => {
            assert!(nested && !frame.region_arrivals.is_empty());
            if let Some(attempt) = diagnostics_attempt.as_mut() {
                attempt.finish_local_rejection(reason);
            }
            shared.execution_stats.rule_finished(rule, Some(reason));
            shared.execution_stats.merge_finished(false);
            Ok(RegionResult::Separate(reason))
        }
        Ok(result) => {
            if let Some(attempt) = diagnostics_attempt.as_mut() {
                attempt.finish(None);
                if segmented {
                    attempt.finish_segmented();
                }
            }
            shared.execution_stats.merge_finished(true);
            shared.execution_stats.rule_finished(rule, None);
            Ok(result)
        }
        Err(error) => {
            if shared.execution_stats.enabled() {
                if let ExecError::Smt(error) = &error {
                    eprintln!(
                        "[REGION_SMT_REJECT] {}",
                        serde_json::json!({
                            "function": zencode::decode(shared.symtab.to_str(frame.function_name)),
                            "branch_pc": frame.pc, "nested": nested,
                            "error": error.to_string(), "source_loc": error.source_loc(),
                        })
                    );
                }
            }
            let reason = match &error {
                ExecError::SpeculativeReject { reason, .. } => *reason,
                ExecError::Smt(_) => SpeculativeRejectReason::SmtError,
                ExecError::Timeout => SpeculativeRejectReason::Timeout,
                _ => SpeculativeRejectReason::IncompatibleState,
            };
            let site;
            let rejection = if matches!(&error, ExecError::SpeculativeReject { .. }) {
                &error
            } else {
                site = reject(frame, reason);
                &site
            };
            if diagnostics_active {
                diagnostics_attempt.as_mut().unwrap().finish(Some(reason));
                if matches!(reason, SpeculativeRejectReason::IncompatibleState | SpeculativeRejectReason::UnionPayload)
                {
                    diagnostics::unattributed_error(frame.function_name, frame.pc, &error, &shared.symtab);
                }
                diagnostics::propagated();
            }
            shared.execution_stats.merge_rejected(key.0, key.1, rejection);
            state.speculation_stats.record_reject(reason);
            shared.execution_stats.rule_finished(rule, Some(reason));
            shared.execution_stats.merge_finished(false);
            if solver.on_unknown() == crate::config::SolverOnUnknown::Error
                && stats::solver_failures::is_solver_failure(&error)
            {
                return Err(error);
            }
            if mode == MergeMode::Force {
                speculation::force_failure(frame, state, shared, info, &error);
            }
            if nested {
                Err(error)
            } else {
                let local = cost::make_mut(&mut frame.local_state);
                local.region_fallbacks = local.region_fallbacks.checked_add(1).expect("区域拒绝计数溢出");
                if reason == SpeculativeRejectReason::SymbolicAssertion {
                    // 重新合并内层返回值会再次触发悲观断言的存在性失败。
                    // 本次区域按普通分叉回放，到汇合点恢复其后的合并。
                    frame.region_replay = Some((frame.backtrace.len(), replay_join.expect("动态拒绝必须有区域")));
                }
                Ok(RegionResult::Rejected)
            }
        }
    }
}

/// 组织者共享的区域入口帧、调用范围和预算。
pub(super) fn prepare_region_base<'ir, B: BV>(
    frame: &LocalFrame<'ir, B>,
    region: &Arc<Region>,
    depth: usize,
    mode: MergeMode,
    state: &TaskState<B>,
    info: SourceLoc,
) -> LocalFrame<'ir, B> {
    let parent = frame.region_execution.clone();
    let iterative = region.has_back_edge
        && can_fold_iterations(state, mode)
        && match region.join {
            RegionPoint::FunctionExit => true,
            RegionPoint::Instruction(pc) => matches!(frame.instrs.get(pc), Some(Instr::End)),
        };
    let execution = RegionExecution {
        region: region.clone(),
        pending_branch: None,
        entry_depth: frame.backtrace.len(),
        write_depth: parent.as_ref().map_or(frame.backtrace.len(), |execution| execution.write_depth),
        // 可按轮收敛的子循环独立核算单轮预算；非循环仍共享调用者预算。
        // 总路径限时仍生效，未完成的一轮仍会正常拒绝，不据此猜测循环会终止。
        remaining: if iterative {
            state.region_step_budget().map(|budget| Arc::new(AtomicUsize::new(budget)))
        } else {
            parent.as_ref().map_or_else(
                || state.region_step_budget().map(|budget| Arc::new(AtomicUsize::new(budget))),
                |execution| execution.remaining.clone(),
            )
        },
        depth,
        iteration_budget: iterative.then(|| state.region_step_budget()).flatten(),
        additional_fragments: parent.as_ref().map_or_else(
            || {
                state
                    .execution_limits
                    .as_ref()
                    .and_then(|limits| limits.max_region_fragments)
                    .map(|limit| Arc::new(AtomicUsize::new(limit - 1)))
            },
            |execution| execution.additional_fragments.clone(),
        ),
        mode,
        origin: if mode == MergeMode::Force {
            parent
                .as_ref()
                .filter(|execution| execution.mode == MergeMode::Force)
                .map_or((frame.function_name, frame.pc, info), |execution| execution.origin)
        } else {
            (frame.function_name, frame.pc, info)
        },
    };
    let mut base = frame.clone();
    base.region_execution = Some(execution);
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
            call_scope: fresh_call_scope(),
            function: frame.function_name,
            pc: frame.pc,
            location: info,
            writes_allowed: true,
            global_state: state.execution_limits.as_ref().is_some_and(|limits| limits.region_global_state),
        });
    }
    base
}

#[allow(clippy::too_many_arguments)]
fn advance_recursive_arm<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
    tid: usize,
    task_id: TaskId,
    fraction: &mut Fraction,
    timeout: PathTimeout,
    stop: Option<&'task StopConditions>,
    sink: &S,
    arm: &mut LocalFrame<'ir, B>,
    state: &'task TaskState<B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    tx: crate::smt::SolverTransaction,
    info: SourceLoc,
) -> Result<bool, ExecError> {
    if let Some(alive) = advance_arm(tid, task_id, fraction, timeout, stop, sink, arm, state, shared, solver, tx, info)?
    {
        return Ok(alive);
    }
    // 本臂已经分成互斥片段；分别关闭，不把任何一个临时条件留在主求解器上。
    let mut pending = std::mem::take(&mut arm.region_arrivals);
    pending.reverse();
    let mut reached = Vec::new();
    while let Some(mut fragment) = pending.pop() {
        let owner = fragment.region_arm.expect("独立片段必须拥有逻辑臂");
        let guard = fragment.local_state.speculative_access.as_ref().unwrap().guard.clone().unwrap();
        let part_tx = solver.start_transaction_with_guard(Some(guard));
        let outcome = solver.with_logical_arm(owner, |solver| {
            let step = advance_arm(
                tid,
                task_id,
                fraction,
                timeout,
                stop,
                sink,
                &mut fragment,
                state,
                shared,
                solver,
                part_tx,
                info,
            )?;
            if step.is_none() {
                solver.commit_transaction();
            }
            Ok(step)
        });
        match outcome {
            Ok(Some(true)) => reached.push(fragment),
            Ok(Some(false)) => solver.discard_logical_arm_effects(owner),
            Ok(None) => pending.extend(fragment.region_arrivals.into_iter().rev()),
            Err(error) => {
                solver.rollback_transaction(tx);
                return Err(error);
            }
        }
    }
    if reached.is_empty() {
        solver.commit_dead_transaction();
        return Ok(false);
    }
    solver.commit_transaction();
    if reached.len() == 1 {
        *arm = reached.pop().unwrap();
    } else {
        arm.region_arrivals = reached;
    }
    Ok(true)
}

#[allow(clippy::too_many_arguments)]
fn execute_region<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
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
    use smtlib::Exp::{Not, Var};
    let record_id = NEXT_RECORD
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
        .expect("合并记录编号溢出");
    let mut base = prepare_region_base(frame, &region, depth, mode, state, info);
    if region.has_back_edge {
        return execute_loop_region(
            record_id, condition, target, region, base, tid, task_id, fraction, timeout, stop, sink, frame, state,
            shared, solver, info,
        );
    }
    let mut arms = [Vec::new(), Vec::new()];
    for (side, (pc, guard)) in
        [(target, Var(condition)), (frame.pc + 1, Not(Box::new(Var(condition))))].into_iter().enumerate()
    {
        let owner = solver.new_logical_arm(solver.current_logical_arm());
        let tx = solver.start_transaction_with_guard(Some(guard.clone()));
        let mut arm = branch_arm(&base, pc, guard, owner);
        if solver.with_logical_arm(owner, |solver| {
            advance_recursive_arm(
                tid, task_id, fraction, timeout, stop, sink, &mut arm, state, shared, solver, tx, info,
            )
        })? {
            if arm.region_arrivals.is_empty() {
                promote_initials(&mut base, &arm, shared, solver);
                arms[side].push(arm);
            } else {
                arms[side] = std::mem::take(&mut arm.region_arrivals);
                for fragment in &arms[side] {
                    promote_initials(&mut base, fragment, shared, solver);
                }
            }
        }
    }
    finish_arrivals(record_id, condition, &region, &base, arms, frame, state, shared, solver, info, |_| ())
        .map(RegionOutput::complete)
}

/// 执行前只校验显式 Force 命中的结构；调用方负责配置名称、源码范围和哈希校验。
pub fn validate_force_regions<B: BV>(shared: &SharedState<B>, limits: &ExecutionLimits) -> Result<(), String> {
    let summaries = std::sync::OnceLock::new();
    for (function, (_, _, body)) in &shared.functions {
        for (pc, instr) in body.iter().enumerate() {
            if let Instr::Jump(_, _, info) = instr {
                if limits.merge_mode(*function, *info, None) == MergeMode::Force {
                    let mut cache = shared.function_regions.lock().unwrap();
                    let regions = cache.entry((*function, limits.region_loop_analysis)).or_insert_with(|| {
                        let summaries =
                            summaries.get_or_init(|| function_effect_summaries(shared, limits.region_global_state));
                        FunctionRegions::with_options(
                            body,
                            RegionOptions {
                                bounded_loops: limits.region_loop_analysis,
                                filter_assertion_failures: limits.region_loop_analysis,
                                recreated_slot_liveness: limits.region_loop_analysis,
                                have_exception: Some(HAVE_EXCEPTION),
                                terminal_calls: &summaries
                                    .iter()
                                    .filter_map(|(name, summary)| summary.non_returning.then_some(*name))
                                    .collect::<Vec<_>>(),
                            },
                        )
                    });
                    match regions.region(pc) {
                        Ok(_) | Err(RegionRejection::ExceptionCheck) => (),
                        Err(reason) => {
                            let reason = match reason {
                                RegionRejection::NoJoin => SpeculativeRejectReason::NoJoin,
                                RegionRejection::HasBackEdge => SpeculativeRejectReason::HasBackEdge,
                                RegionRejection::ExitsRegion { .. } => SpeculativeRejectReason::RegionEscaped,
                                RegionRejection::NotJump | RegionRejection::ExceptionCheck => {
                                    panic!("Force 结构校验的候选必须是普通 Jump")
                                }
                            };
                            let error =
                                ExecError::SpeculativeReject { reason, function: *function, pc, location: *info };
                            shared.execution_stats.print(shared);
                            return Err(speculation::force_diagnostic(
                                limits.merge_rule(*function, *info).map(|(rule, _)| rule),
                                &zencode::decode(shared.symtab.to_str(*function)),
                                pc,
                                *info,
                                &error,
                                None,
                            ));
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

/// 循环轮次和平级臂都复用相同入口初值，防止另一臂重新创建自由变量。
pub(super) fn promote_initials<'ir, B: BV>(
    base: &mut LocalFrame<'ir, B>,
    arm: &LocalFrame<'ir, B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) {
    let cost_scope = cost::Scope::enter(cost::Category::StateMerge);
    let _ = &cost_scope;
    // 首臂惰性初始化的前置寄存器在另臂复用；无读事件的提升不扩大足迹。
    let access = arm.local_state.speculative_access.as_ref().unwrap();
    cost::make_mut(&mut base.local_state).speculative_access.as_mut().unwrap().published_reads =
        access.published_reads.clone();
    for (reg, initial) in &access.initial_registers {
        if base.regs().get_last_if_initialized(*reg).is_none() {
            assert_initial_type(initial, solver);
            base.regs_mut().assign(*reg, initial.clone(), shared);
        }
    }
    for ((scope, function, name), value) in &access.initial_variables {
        if *scope == base.local_state.speculative_access.as_ref().unwrap().call_scope
            && *function == base.function_name
            && matches!(base.vars().get(name), Some(UVal::Uninit(_)))
        {
            assert_initial_type(value, solver);
            base.vars_mut().insert(*name, UVal::Init(value.clone()));
        }
    }
    for (name, value) in &access.initial_lets {
        if matches!(base.lets().get(name), Some(UVal::Uninit(_))) {
            assert_initial_type(value, solver);
            base.lets_mut().insert(*name, UVal::Init(value.clone()));
        }
    }
}

/// 只把同一循环的轮次放在显式栈中；保存点随每段执行提交，不随轮次累积。
/// 每个汇合仍复用二臂状态合并和原记录格式，外层事务覆盖所有已提交的段。
struct LoopWork<'ir, B> {
    original: LocalFrame<'ir, B>,
    base: LocalFrame<'ir, B>,
    region: Arc<Region>,
    condition: Sym,
    target: usize,
    info: SourceLoc,
    record_id: usize,
    arms: [Vec<LocalFrame<'ir, B>>; 2],
    completed: usize,
    continuations: Vec<LocalFrame<'ir, B>>,
    parent_arm: Option<crate::smt::LogicalArm>,
    active_arm: Option<crate::smt::LogicalArm>,
}

#[allow(clippy::too_many_arguments)]
/// 两个前沿都已到函数出口，只合并返回结果；继续帧从不经过此接口。
#[allow(clippy::too_many_arguments)]
pub(super) fn fold_loop_exit<'ir, B: BV>(
    previous: LocalFrame<'ir, B>,
    next: LocalFrame<'ir, B>,
    base: &LocalFrame<'ir, B>,
    region: &Region,
    state: &TaskState<B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<LocalFrame<'ir, B>, ExecError> {
    let cost_scope = cost::Scope::enter(cost::Category::StateMerge);
    let _ = &cost_scope;
    for exit in [&previous, &next] {
        if !matches!(exit.instrs.get(exit.pc), Some(Instr::End))
            || !exit.local_state.speculative_access.as_ref().unwrap().writes.modified_regs.is_empty()
            || solver.transaction_has_memory_writes()
        {
            return Err(reject(exit, SpeculativeRejectReason::StateEffect));
        }
    }
    fold_exit_frontiers(previous, next, base, region, state, shared, solver, info)
}

/// 已到同一出口的前沿共享记录重编号和状态合并；调用方校验各策略的适用形状。
#[allow(clippy::too_many_arguments)]
pub(super) fn fold_exit_frontiers<'ir, B: BV>(
    previous: LocalFrame<'ir, B>,
    mut next: LocalFrame<'ir, B>,
    base: &LocalFrame<'ir, B>,
    region: &Region,
    state: &TaskState<B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<LocalFrame<'ir, B>, ExecError> {
    use smtlib::Exp::{Or, Var};
    // 两前沿可能共享先前轮次的记录，但在本次不同臂条件下各有一份出现。
    // 只给尚未发布的重复后缀换新ID，保留符号与父子关系；已发布前缀不动。
    let prefix = base.region_merge_records.len();
    let previous_ids: HashSet<_> = previous.region_merge_records.suffix(prefix).map(|r| r.record_id).collect();
    let mut renamed = HashMap::new();
    for record in next.region_merge_records.suffix(prefix) {
        if previous_ids.contains(&record.record_id) {
            renamed.entry(record.record_id).or_insert_with(|| {
                NEXT_RECORD
                    .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
                    .expect("合并记录编号溢出")
            });
        }
    }
    next.region_merge_records.edit_suffix(prefix, |records| {
        for record in records {
            if let Some(id) = renamed.get(&record.record_id) {
                record.record_id = *id;
            }
            if let Some(id) = record.parent_record.and_then(|id| renamed.get(&id)) {
                record.parent_record = Some(*id);
            }
        }
    });
    let a = previous.local_state.speculative_access.as_ref().unwrap().guard.clone().expect("退出前沿必须有条件");
    let b = next.local_state.speculative_access.as_ref().unwrap().guard.clone().expect("退出前沿必须有条件");
    let condition = solver.define_const(a.clone(), info);
    let union = Var(solver.define_const(Or(Box::new(a), Box::new(b)), info));
    let id = NEXT_RECORD
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
        .expect("合并记录编号溢出");
    let mut merged = base.clone();
    let result = solver.with_transaction_condition(&union, |solver| {
        finish_region(
            id,
            condition,
            region,
            base,
            vec![Some(previous), Some(next)],
            &mut merged,
            state,
            shared,
            solver,
            info,
        )
    })?;
    assert!(matches!(result, RegionResult::Merged), "两个存活退出前沿必须保留");
    cost::make_mut(&mut merged.local_state).speculative_access.as_mut().unwrap().guard = Some(union);
    Ok(merged)
}

/// 展开同一循环中尚未到达出口的独立片段，等待关系仍指向原臂槽位。
fn take_loop_continuation<'ir, B: BV>(work: &mut LoopWork<'ir, B>) -> Option<LoopWork<'ir, B>> {
    let mut arm = work.continuations.pop()?;
    let (condition, target, region, info) = arm.region_execution.as_mut().unwrap().pending_branch.take().unwrap();
    let record_id = NEXT_RECORD
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
        .expect("合并记录编号溢出");
    let parent_arm = arm.region_arm;
    Some(LoopWork {
        original: arm.clone(),
        base: arm,
        region,
        condition,
        target,
        info,
        record_id,
        arms: [Vec::new(), Vec::new()],
        completed: 0,
        continuations: Vec::new(),
        parent_arm,
        active_arm: None,
    })
}

fn execute_loop_region<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
    record_id: usize,
    condition: Sym,
    target: usize,
    region: Arc<Region>,
    base: LocalFrame<'ir, B>,
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
    use smtlib::Exp::{And, Not, Var};
    let eligible = can_segment(frame, state, base.region_execution.as_ref().unwrap().mode)
        && match region.join {
            RegionPoint::FunctionExit => true,
            RegionPoint::Instruction(pc) => matches!(frame.instrs.get(pc), Some(Instr::End)),
        };
    let iterative = can_fold_iterations(state, base.region_execution.as_ref().unwrap().mode)
        && match region.join {
            RegionPoint::FunctionExit => true,
            RegionPoint::Instruction(pc) => matches!(frame.instrs.get(pc), Some(Instr::End)),
        };
    let mut exit_prefix = Vec::new();
    let root_branch = region.branch_pc;
    let root_region = region.clone();
    let remaining = base.region_execution.as_ref().unwrap().remaining.clone();
    let original_base = base.clone();
    let original_frame = frame.clone();
    let mut last_boundary = 0;
    let mut largest_round = 0;
    let mut continuation = None;
    let mut return_guard = None;
    let (mut pending, mut frontier) = LoopDependencies::new(LoopWork {
        original: frame.clone(),
        base,
        region,
        condition,
        target,
        info,
        record_id,
        arms: [Vec::new(), Vec::new()],
        completed: 0,
        continuations: Vec::new(),
        parent_arm: solver.current_logical_arm(),
        active_arm: None,
    });
    loop {
        super::stats::memory_stats::poll(frame, solver);
        if pending.work(frontier).completed == 2 {
            let (mut work, parent) = pending.complete(frontier);
            // 子循环段已提交为完整条件保护的约束；汇合时也保留所属臂条件。
            let finish = |solver: &mut Solver<B>| {
                finish_arrivals(
                    work.record_id,
                    work.condition,
                    &work.region,
                    &work.base,
                    work.arms,
                    &mut work.original,
                    state,
                    shared,
                    solver,
                    work.info,
                    |_| (),
                )
            };
            let mut guard = work.base.local_state.speculative_access.as_ref().unwrap().guard.clone();
            if let Some(returned) = return_guard {
                guard = Some(match guard {
                    Some(parent) => And(Box::new(parent), Box::new(Var(returned))),
                    None => Var(returned),
                });
            }
            let finish_with_guard = |solver: &mut Solver<B>| match guard {
                Some(guard) => solver.with_transaction_condition(&guard, finish),
                None => finish(solver),
            };
            let result = match work.parent_arm {
                Some(owner) => solver.with_logical_arm(owner, finish_with_guard),
                None => finish_with_guard(solver),
            }?;
            if let Some((parent, side)) = parent {
                frontier = parent;
                let parent = pending.work_mut(parent);
                assert_eq!(parent.completed, side, "调用栈组织者按两臂顺序收尾");
                match result {
                    RegionResult::Merged => {
                        promote_initials(&mut parent.base, &work.original, shared, solver);
                        parent.arms[side].push(work.original);
                    }
                    RegionResult::Dead => {
                        solver.discard_logical_arm_effects(work.parent_arm.expect("挂起臂必须持有逻辑事务"));
                    }
                    RegionResult::Separate(_) => {
                        for fragment in std::mem::take(&mut work.original.region_arrivals) {
                            promote_initials(&mut parent.base, &fragment, shared, solver);
                            parent.arms[side].push(fragment);
                        }
                    }
                    RegionResult::Rejected | RegionResult::Suspended => panic!("汇合结果必须已经收尾"),
                }
                if let Some(next) = take_loop_continuation(parent) {
                    frontier = pending.attach(frontier, side, next);
                } else {
                    parent.completed += 1;
                    parent.active_arm = None;
                }
            } else {
                if let RegionResult::Separate(reason) = result {
                    let Some(outer) = original_frame.region_execution.as_ref() else {
                        return Err(reject(&original_frame, reason));
                    };
                    work.original.region_arrivals.append(&mut exit_prefix);
                    for part in &mut work.original.region_arrivals {
                        part.region_execution = Some(outer.clone());
                        part.speculation_mode = original_frame.speculation_mode;
                    }
                    *frame = work.original;
                    return Ok(RegionOutput::complete(result));
                }
                if !exit_prefix.is_empty() {
                    match result {
                        RegionResult::Merged => {
                            append_loop_exit(&mut exit_prefix, work.original, solver, |previous, next, solver| {
                                fold_loop_exit(
                                    previous,
                                    next,
                                    &original_base,
                                    &root_region,
                                    state,
                                    shared,
                                    solver,
                                    info,
                                )
                            })?
                        }
                        RegionResult::Dead => (),
                        _ => panic!("循环收尾只能汇合或全部死亡"),
                    }
                    let guard = loop_exit_guard(&exit_prefix);
                    let condition = solver.define_const(guard.clone(), info);
                    // 完整循环的存活域就是已累计的退出并集；死亡域保持原来的条件约束。
                    solver.assert_region_exit(guard);
                    let mut restored = original_frame.clone();
                    let result = finish_arrivals(
                        record_id,
                        condition,
                        &root_region,
                        &original_base,
                        [exit_prefix, Vec::new()],
                        &mut restored,
                        state,
                        shared,
                        solver,
                        info,
                        |_| (),
                    )?;
                    *frame = restored;
                    return Ok(RegionOutput::complete(result));
                }
                *frame = work.original;
                return Ok(RegionOutput { result, continuation });
            }
            continue;
        }
        let completed_exits = pending.ancestors(frontier).count();
        let single_work = completed_exits == 1;
        let exit_spine = (eligible || iterative)
            && continuation.is_none()
            && pending.ancestors(frontier).all(|work| {
                work.completed == 1
                    && work.arms[0].len() == 1
                    && work.arms[0].first().is_some_and(|arm| {
                        matches!(arm.instrs.get(arm.pc), Some(Instr::End))
                            && arm.local_state.speculative_access.as_ref().unwrap().writes.modified_regs.is_empty()
                    })
            });
        let work = pending.work_mut(frontier);
        assert!(work.active_arm.is_none(), "前一逻辑臂必须先收尾");
        let owner = solver.new_logical_arm(work.parent_arm);
        work.active_arm = Some(owner);
        let first = work.completed == 0;
        let guard = if first { Var(work.condition) } else { Not(Box::new(Var(work.condition))) };
        let mut arm = branch_arm(&work.base, if first { work.target } else { work.original.pc + 1 }, guard, owner);
        let guard = arm.local_state.speculative_access.as_ref().unwrap().guard.clone().unwrap();
        let tx = solver.start_transaction_with_guard(Some(guard));
        if solver.with_logical_arm(owner, |solver| {
            advance_recursive_arm(
                tid, task_id, fraction, timeout, stop, sink, &mut arm, state, shared, solver, tx, work.info,
            )
        })? {
            if !arm.region_arrivals.is_empty() {
                let side = work.completed;
                for part in std::mem::take(&mut arm.region_arrivals) {
                    if part.region_execution.as_ref().unwrap().pending_branch.is_some() {
                        work.continuations.push(part);
                    } else {
                        promote_initials(&mut work.base, &part, shared, solver);
                        work.arms[side].push(part);
                    }
                }
                work.continuations.reverse();
                if let Some(next) = take_loop_continuation(work) {
                    frontier = pending.attach(frontier, side, next);
                } else {
                    work.completed += 1;
                    work.active_arm = None;
                }
                continue;
            }
            let branch = arm.region_execution.as_mut().unwrap().pending_branch.take();
            if let Some((condition, target, region, info)) = branch {
                let used = state.region_step_budget().map(|budget| {
                    budget.saturating_sub(remaining.as_ref().expect("有限预算必须有计数器").load(Ordering::Relaxed))
                });
                if let Some(used) = used {
                    if region.branch_pc == root_branch {
                        largest_round = largest_round.max(used.saturating_sub(last_boundary));
                        last_boundary = used;
                    }
                }
                let no_writes = arm.local_state.speculative_access.as_ref().unwrap().writes.modified_regs.is_empty();
                if iterative
                    && single_work
                    && exit_spine
                    && region.branch_pc == root_branch
                    && no_writes
                    && !solver.transaction_has_memory_writes()
                {
                    let exit = work.arms[0].pop().expect("退出脊柱必须已有存活前沿");
                    append_loop_exit(&mut exit_prefix, exit, solver, |previous, next, solver| {
                        fold_loop_exit(previous, next, &original_base, &root_region, state, shared, solver, info)
                    })?;
                    let guard = arm
                        .local_state
                        .speculative_access
                        .as_ref()
                        .unwrap()
                        .guard
                        .clone()
                        .expect("继续前沿必须有完整条件");
                    let returned = solver.define_const(Not(Box::new(guard.clone())), info);
                    let prefix_region = Region {
                        branch_pc: root_branch,
                        has_back_edge: false,
                        join: RegionPoint::Instruction(arm.pc),
                        nodes: root_region.nodes.clone(),
                        kind: crate::ir::regions::RegionKind::Reconvergent,
                        local_variables: Default::default(),
                    };
                    let prefix_id = NEXT_RECORD
                        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
                        .expect("合并记录编号溢出");
                    let mut next = original_base.clone();
                    let result = solver.with_transaction_condition(&guard, |solver| {
                        finish_region(
                            prefix_id,
                            returned,
                            &prefix_region,
                            &original_base,
                            vec![None, Some(arm)],
                            &mut next,
                            state,
                            shared,
                            solver,
                            info,
                        )
                    })?;
                    assert!(matches!(result, RegionResult::Merged));
                    solver.compact_region_query_prefix();
                    cost::make_mut(&mut next.local_state).speculative_access.as_mut().unwrap().guard = Some(guard);
                    let id = NEXT_RECORD
                        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
                        .expect("合并记录编号溢出");
                    if super::stats::region_progress::enabled()
                        && LOGGED_ITERATION_FOLDS.fetch_add(1, Ordering::Relaxed) < 2048
                    {
                        eprintln!(
                            "{}",
                            serde_json::json!({"kind":"loop_iteration_fold",
                            "function":diagnostics::name_string(original_frame.function_name,&shared.symtab),
                            "pc":root_branch,"call_instance":original_frame.local_state.call_instance,
                            "steps_since_budget_renewal":used,"step_budget_unlimited":remaining.is_none(),"logical_frontiers":2,
                            "returned_records":exit_prefix.iter().map(|exit| exit.region_merge_records.len()).sum::<usize>(),
                            "continuation_records":next.region_merge_records.len(),
                            "savepoint_depth":solver.transaction_depth()})
                        );
                    }
                    *work = LoopWork {
                        original: next.clone(),
                        base: next,
                        region,
                        condition,
                        target,
                        info,
                        record_id: id,
                        arms: [Vec::new(), Vec::new()],
                        completed: 0,
                        continuations: Vec::new(),
                        parent_arm: work.parent_arm,
                        active_arm: None,
                    };
                    // 预算由实际回边更新；此处只收敛前沿，避免半轮重复授予预算。
                    last_boundary = 0;
                    largest_round = 0;
                    continue;
                }
                if !exit_prefix.is_empty() {
                    return Err(reject(&arm, SpeculativeRejectReason::StateEffect));
                }
                if eligible
                    && exit_spine
                    && region.branch_pc == root_branch
                    && no_writes
                    && !solver.transaction_has_memory_writes()
                    && largest_round > 0
                    && remaining
                        .as_ref()
                        .is_some_and(|remaining| remaining.load(Ordering::Relaxed) <= largest_round.saturating_mul(2))
                {
                    let continued_guard = arm
                        .local_state
                        .speculative_access
                        .as_ref()
                        .unwrap()
                        .guard
                        .clone()
                        .expect("继续臂必须有完整条件");
                    let returned = solver.define_const(Not(Box::new(continued_guard.clone())), info);
                    let continuation_region = Region {
                        branch_pc: root_branch,
                        has_back_edge: false,
                        join: RegionPoint::Instruction(arm.pc),
                        nodes: root_region.nodes.clone(),
                        kind: crate::ir::regions::RegionKind::Reconvergent,
                        local_variables: Default::default(),
                    };
                    let prefix_record = NEXT_RECORD
                        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
                        .expect("合并记录编号溢出");
                    let mut continued = original_frame.clone();
                    let result = solver.with_transaction_condition(&continued_guard, |solver| {
                        finish_region(
                            prefix_record,
                            returned,
                            &continuation_region,
                            &original_base,
                            vec![None, Some(arm)],
                            &mut continued,
                            state,
                            shared,
                            solver,
                            info,
                        )
                    })?;
                    assert!(matches!(result, RegionResult::Merged), "已证可行的继续臂必须保留");
                    if diagnostics::enabled() {
                        eprintln!(
                            "{}",
                            serde_json::json!({"kind":"loop_segment","function":diagnostics::name_string(original_frame.function_name,&shared.symtab),"pc":root_branch,"call_instance":original_frame.local_state.call_instance,"steps":used,"remaining":remaining.as_ref().map(|remaining| remaining.load(Ordering::Relaxed)),"completed_exits":completed_exits,"continuation_pc":continued.pc})
                        );
                    }
                    continuation = Some((returned, continued));
                    return_guard = Some(returned);
                    // 继续臂已单独保存；这里只折叠已完成出口，补集将在最外层提交后成为普通任务。
                    work.completed += 1;
                    work.active_arm = None;
                    continue;
                }

                let record_id = NEXT_RECORD
                    .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
                    .expect("合并记录编号溢出");
                let side = work.completed;
                frontier = pending.attach(
                    frontier,
                    side,
                    LoopWork {
                        original: arm.clone(),
                        base: arm,
                        region,
                        condition,
                        target,
                        info,
                        record_id,
                        arms: [Vec::new(), Vec::new()],
                        completed: 0,
                        continuations: Vec::new(),
                        parent_arm: Some(owner),
                        active_arm: None,
                    },
                );
            } else {
                assert!(
                    work.region.join == RegionPoint::Instruction(arm.pc)
                        || (work.region.join == RegionPoint::FunctionExit && matches!(arm.instrs[arm.pc], Instr::End)),
                    "非分叉挂起必须抵达共同出口"
                );
                promote_initials(&mut work.base, &arm, shared, solver);
                work.arms[work.completed].push(arm);
                work.completed += 1;
                work.active_arm = None;
            }
        } else {
            work.completed += 1;
            work.active_arm = None;
        }
    }
}
