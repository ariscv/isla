//! 区域推演只调用真实执行循环；此模块负责边界、事务与状态合并。
use super::region_summary::{function_effect_summaries, instruction_effect, CachedReject, FunctionEffect};
use super::stats::merge_diagnostics as diagnostics;
use super::*;
use crate::config::MergeMode;
use crate::ir::regions::{FunctionRegions, Region, RegionOptions, RegionPoint, RegionRejection};

/// 普通区域的两臂与调用共享预算；可收敛的只读循环按完整轮核算，单轮仍受限。
/// 这只限制一次合并尝试，不截断普通符号执行的路径。
pub const DEFAULT_REGION_STEP_BUDGET: usize = 8192;
/// 每层持有回滚层与当前臂两层保存点；16 层至多占 32 层，给 64 层上限留出一倍余量。
pub const MAX_REGION_MERGE_DEPTH: usize = 16;
static NEXT_RECORD: AtomicUsize = AtomicUsize::new(0);
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
    pub remaining: Arc<AtomicUsize>,
    pub iteration_budget: Option<usize>,
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

/// 各分叉口复用三值查询；Unknown 在推演中始终是拒绝，不能隐含地当作 Unsat。
pub(super) fn feasible<B: BV>(
    frame: &LocalFrame<B>,
    solver: &mut Solver<B>,
    exp: &smtlib::Exp<Sym>,
    info: SourceLoc,
) -> Result<bool, ExecError> {
    if solver.region_queries_deferred() {
        // 两臂只是候选；调用处不得把此结果登记为可满足性证明。
        return Ok(true);
    }
    match solver.check_sat_with_for_branch(exp, info, true) {
        SmtResult::Sat => Ok(true),
        SmtResult::Unsat => Ok(false),
        SmtResult::Unknown => Err(reject(frame, SpeculativeRejectReason::SolverUnknown)),
        SmtResult::Error(error) => Err(ExecError::Smt(error)),
    }
}

pub(super) fn record_read<B: BV>(
    state: &mut LocalState<B>,
    reg: Name,
    accessor: Vec<Accessor>,
    value: Val<B>,
) -> Result<bool, ExecError> {
    match &mut state.speculative_access {
        Some(log) => log.record_read(reg, accessor, value),
        None => Ok(true),
    }
}

pub(super) fn record_write<B: BV>(state: &mut LocalState<B>, id: Name, register: bool) -> Result<(), ExecError> {
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
    if execution
        .remaining
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |remaining| remaining.checked_sub(1))
        .is_err()
    {
        return Err(reject(frame, SpeculativeRejectReason::StepBudget));
    }
    let location = frame.instrs.get(frame.pc).and_then(stats::instr_source_loc).unwrap_or(SourceLoc::unknown());
    let log = Arc::make_mut(&mut frame.local_state).speculative_access.as_mut().expect("区域推演必须启用访问记录");
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
            execution.remaining.store(budget, Ordering::Relaxed);
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

fn region<'ir, B: BV>(
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

/// 提交后的返回前沿与继续前沿共用相同的条件事件后缀，分别保留自己的根记录。
fn publish_committed_records<B: BV>(
    frame: &mut LocalFrame<B>,
    start: usize,
    task: TaskId,
    shared: &SharedState<B>,
    solver: &mut Solver<B>,
) {
    let events = solver.committed_transaction_events();
    let count = events.iter().filter(|(_, event)| event.is_memory_read_or_write()).count();
    if count != 0 {
        let offset = solver
            .trace()
            .to_vec()
            .iter()
            .filter(|event| event.is_memory_read_or_write())
            .count()
            .checked_sub(count)
            .expect("提交事件必须属于主迹后缀");
        let root = frame.region_merge_records.last_mut().expect("提交必须有根记录");
        assert!(root.parent_record.is_none());
        root.memory_reads = events
            .iter()
            .filter(|(_, event)| event.is_memory_read_or_write())
            .enumerate()
            .filter_map(|(i, (guard, event))| {
                if event.is_memory_read() {
                    guard.as_ref().map(|guard| (offset + i, guard.clone(), event.clone()))
                } else {
                    None
                }
            })
            .collect();
    }
    super::merge_record::publish(
        &mut frame.region_merge_records[start..],
        &frame.local_state.pure_definitions,
        task,
        shared,
        solver,
    );
}

struct RegionOutput<'ir, B> {
    result: RegionResult,
    continuation: Option<(Sym, LocalFrame<'ir, B>)>,
}
impl<'ir, B> RegionOutput<'ir, B> {
    fn complete(result: RegionResult) -> Self {
        Self { result, continuation: None }
    }
}

pub(super) enum RegionResult {
    Merged,
    Dead,
    Rejected,
    /// 同一有环区域的后续轮次交回本层显式工作栈。
    Suspended,
}

/// 只有这里捕获推演拒绝。内层拒绝原样传播，直到最外层回滚后才恢复普通分叉。
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
                Arc::make_mut(&mut frame.local_state).loop_attempt_seen = true;
            }
            shared.execution_stats.merge_candidate();
            let depth = frame.region_execution.as_ref().map_or(1, |execution| execution.depth + 1);
            if depth > MAX_REGION_MERGE_DEPTH {
                Err(reject(frame, SpeculativeRejectReason::NestingLimit))
            } else {
                let record_start = frame.region_merge_records.len();
                let tx = solver.start_transaction();
                static DEFER_EXIT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
                let defer = solver.region_queries_deferred()
                    || *DEFER_EXIT
                        .get_or_init(|| std::env::var("ISLA_REGION_DEFER_EXIT_CHECK").is_ok_and(|value| value == "1"));
                let execute = |solver: &mut Solver<B>| {
                    let output = execute_region(
                        condition, target, region, depth, mode, tid, task_id, fraction, timeout, stop, sink, frame,
                        state, shared, solver, info,
                    );
                    if defer && !nested && output.is_ok() {
                        match solver.check_deferred_assertions(info) {
                            SmtResult::Unsat => (),
                            SmtResult::Sat => return Err(reject(frame, SpeculativeRejectReason::SymbolicAssertion)),
                            SmtResult::Unknown => return Err(reject(frame, SpeculativeRejectReason::SolverUnknown)),
                            SmtResult::Error(error) => return Err(ExecError::Smt(error)),
                        }
                    }
                    output
                };
                let result = if defer { solver.with_deferred_region_queries(execute) } else { execute(solver) };
                // 只有最外层出口查询可以验证候选；嵌套结果仍带着全部守卫。
                let result = if defer && !nested && result.is_ok() {
                    match solver.check_sat(info) {
                        SmtResult::Sat => result,
                        // 分段可能还有继续前沿；退出前沿为空不代表整次调用为空。
                        // 保守回滚，让普通执行分别判断两个前沿。
                        SmtResult::Unsat => Err(reject(frame, SpeculativeRejectReason::SolverUnknown)),
                        SmtResult::Unknown => Err(reject(frame, SpeculativeRejectReason::SolverUnknown)),
                        SmtResult::Error(error) => Err(ExecError::Smt(error)),
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
                        solver.commit_transaction();
                        if !nested {
                            crate::smt::probe_query_event(
                                || serde_json::json!({"type":"region_commit", "function":zencode::decode(shared.symtab.to_str(frame.function_name)), "branch_pc":key.1, "call_instance":frame.local_state.call_instance}),
                            );
                            publish_committed_records(frame, record_start, task_id, shared, solver);
                            if let Some((returned, mut continued)) = continuation.take() {
                                segmented = true;
                                publish_committed_records(&mut continued, record_start, task_id, shared, solver);
                                let fork_id = Arc::make_mut(&mut frame.execution_limit_state).record_fork();
                                let other = Arc::make_mut(&mut continued.execution_limit_state).record_fork();
                                assert_eq!(fork_id, other, "同一分段的两前沿必须继承相同fork计数");
                                Arc::make_mut(&mut frame.execution_limit_state).advance_path_signature(true);
                                Arc::make_mut(&mut continued.execution_limit_state).advance_path_signature(false);
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
            if mode == MergeMode::Force {
                speculation::force_failure(frame, state, shared, info, &error);
            }
            if nested {
                Err(error)
            } else {
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
            Arc::new(AtomicUsize::new(state.region_step_budget))
        } else {
            parent.as_ref().map_or_else(
                || Arc::new(AtomicUsize::new(state.region_step_budget)),
                |execution| execution.remaining.clone(),
            )
        },
        depth,
        iteration_budget: iterative.then_some(state.region_step_budget),
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
        Arc::make_mut(&mut base.local_state).speculative_access = Some(AccessLog {
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
    if region.has_back_edge {
        return execute_loop_region(
            record_id, condition, target, region, base, tid, task_id, fraction, timeout, stop, sink, frame, state,
            shared, solver, info,
        );
    }
    let mut arms = Vec::new();
    for (pc, guard) in [(target, Var(condition)), (frame.pc + 1, Not(Box::new(Var(condition))))] {
        let tx = solver.start_transaction_with_guard(Some(guard.clone()));
        let mut arm = base.clone();
        arm.pc = pc;
        let access = Arc::make_mut(&mut arm.local_state).speculative_access.as_mut().unwrap();
        access.guard = Some(match access.guard.take() {
            Some(parent) => smtlib::Exp::And(Box::new(parent), Box::new(guard.clone())),
            None => guard.clone(),
        });
        let result = run_loop(tid, task_id, fraction, timeout, stop, sink, &mut arm, state, shared, solver);
        match result {
            Ok(Run::Suspended) => {
                let close_scope = super::stats::region_progress::QueryScope::enter("arm_close");
                let close_result =
                    if solver.region_queries_deferred() { SmtResult::Sat } else { solver.check_sat_for_arm(info) };
                drop(close_scope);
                match close_result {
                    SmtResult::Unsat => {
                        solver.commit_dead_transaction();
                        arms.push(None);
                        continue;
                    }
                    SmtResult::Unknown => {
                        solver.rollback_transaction(tx);
                        return Err(reject(&arm, SpeculativeRejectReason::SolverUnknown));
                    }
                    SmtResult::Error(error) => {
                        solver.rollback_transaction(tx);
                        return Err(ExecError::Smt(error));
                    }
                    SmtResult::Sat => (),
                }
                assert!(!solver.transaction_invalid(), "臂提交前保存点必须有效");
                solver.commit_transaction();
                promote_initials(&mut base, &arm, shared, solver);
                arms.push(Some(arm));
            }
            Err(ExecError::AssertionFailure(..))
                if !match &arm.instrs[arm.pc] {
                    Instr::Exit(ExitCause::AssertionFailure, _) => true,
                    Instr::PrimopBinary(_, f, _, _, _) => {
                        std::ptr::fn_addr_eq(*f, primop::optimistic_assert::<B> as primop::Binary<B>)
                            || std::ptr::fn_addr_eq(*f, primop::pessimistic_assert::<B> as primop::Binary<B>)
                    }
                    _ => false,
                } =>
            {
                solver.rollback_transaction(tx);
                return Err(reject(&arm, SpeculativeRejectReason::SymbolicAssertion));
            }
            Ok(Run::Dead) | Err(ExecError::AssertionFailure(..)) => {
                // 具体失败与普通执行同义：仅删除完整到达守卫覆盖的臂。
                // 符号断言已在原语处记录义务，不会从这里静默丢弃。
                solver.commit_dead_transaction();
                arms.push(None);
            }
            Err(error) => {
                diagnostics::execute_arm_error(arm.function_name, arm.pc, &error, &shared.symtab);
                solver.rollback_transaction(tx);
                return Err(match error {
                    ExecError::SpeculativeReject { .. } | ExecError::Smt(_) | ExecError::Timeout => error,
                    ExecError::Z3Unknown => reject(&arm, SpeculativeRejectReason::SolverUnknown),
                    _ => reject(&arm, SpeculativeRejectReason::IncompatibleState),
                });
            }
            Ok(_) => {
                solver.rollback_transaction(tx);
                return Err(reject(&arm, SpeculativeRejectReason::RegionEscaped));
            }
        }
    }
    finish_region(record_id, condition, &region, &base, arms, frame, state, shared, solver, info)
        .map(RegionOutput::complete)
}

#[allow(clippy::too_many_arguments)]
fn finish_region<'ir, B: BV>(
    record_id: usize,
    condition: Sym,
    region: &Region,
    base: &LocalFrame<'ir, B>,
    mut arms: Vec<Option<LocalFrame<'ir, B>>>,
    frame: &mut LocalFrame<'ir, B>,
    state: &TaskState<B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<RegionResult, ExecError> {
    let depth = base.region_execution.as_ref().unwrap().depth;
    // 只修改本次推演产生的根记录。历史前缀和已连接的后代保持原上下文。
    for (index, arm) in arms.iter_mut().enumerate() {
        if let Some(arm) = arm {
            for record in &mut arm.region_merge_records[frame.region_merge_records.len()..] {
                if record.parent_record.is_none() {
                    record.parent_record = Some(record_id);
                    record.arm = if index == 0 { "then" } else { "else" };
                }
            }
        }
    }
    let right = arms.pop().unwrap();
    let left = arms.pop().unwrap();
    let mut merged = match (left, right) {
        (None, None) => {
            frame.region_merge_records.push(RegionMergeRecord {
                record_id,
                parent_record: None,
                arm: "root",
                function: frame.function_name,
                branch_pc: region.branch_pc,
                join: region.join,
                condition,
                source_loc: info,
                depth,
                dead: true,
                value_symbols: HashSet::from([condition]),
                input_symbols: HashSet::new(),
                single_arm_reads: Vec::new(),
                memory_reads: Vec::new(),
            });
            return Ok(RegionResult::Dead);
        }
        (Some(mut arm), None) | (None, Some(mut arm)) => {
            let access = arm.local_state.speculative_access.as_ref().unwrap();
            let single_arm_reads = access
                .reads
                .iter()
                .zip(&access.read_guards)
                .skip(base.local_state.speculative_access.as_ref().unwrap().reads.len())
                .map(|((register, accessor, value), guard)| GuardedRegisterRead {
                    register: *register,
                    accessor: accessor.clone(),
                    value: value.clone(),
                    guard: guard.clone(),
                })
                .collect();
            arm.region_merge_records.push(RegionMergeRecord {
                record_id,
                parent_record: None,
                arm: "root",
                function: frame.function_name,
                branch_pc: region.branch_pc,
                join: region.join,
                condition,
                source_loc: info,
                depth,
                dead: false,
                value_symbols: HashSet::new(),
                input_symbols: HashSet::new(),
                single_arm_reads,
                memory_reads: Vec::new(),
            });
            arm
        }
        (Some(left), Some(right)) => {
            merge_states(record_id, condition, &base, left, right, &region, state, shared, solver, info)?
        }
    };
    let record = merged.region_merge_records.last_mut().expect("成功合并必须有记录");
    record.value_symbols.insert(condition);
    for (bindings, original) in
        [(&merged.local_state.vars, &frame.local_state.vars), (&merged.local_state.lets, &frame.local_state.lets)]
    {
        for (name, value) in bindings {
            if let UVal::Init(value) = value {
                if !matches!(original.get(name), Some(UVal::Init(old)) if value == old) {
                    record.value_symbols.extend(value.symbolic_variables());
                }
            }
        }
    }
    let access = merged.local_state.speculative_access.as_ref().unwrap();
    for reg in &access.writes.modified_regs {
        if let Some(value) = merged.local_state.regs.get_last_if_initialized(*reg) {
            record.value_symbols.extend(value.symbolic_variables());
        }
    }
    Arc::make_mut(&mut merged.local_state).speculative_access.as_mut().unwrap().guard =
        frame.local_state.speculative_access.as_ref().and_then(|access| access.guard.clone());
    merged.region_execution = frame.region_execution.clone();
    merged.speculation_mode = frame.speculation_mode;
    if merged.region_execution.is_none() {
        // 仅前置状态/访问足迹可信，需要逐条精确读写顺序时不可信。
        // 读取在真实读取处缓冲，提交时按并集发布；此处补发以 ITE 保留原值的条件写入。
        let access = Arc::make_mut(&mut merged.local_state).speculative_access.take().unwrap();
        for reg in access.writes.register_write_order {
            if !shared.untraced_registers.contains(&reg) {
                solver.add_event(Event::WriteReg(
                    reg,
                    Vec::new(),
                    merged.regs().get_last_if_initialized(reg).unwrap().clone(),
                ));
            }
        }
    }
    solver.add_event(Event::Fork(0, condition, 0, info));
    solver.add_event(Event::Merge(0, 2, info));
    *frame = merged;
    Ok(RegionResult::Merged)
}

/// 配置注入的具体枚举可能从未经过 IR 常量读取；登记必须进入当前合并事务的事件迹。
fn register_value_enums<B: BV>(value: &Val<B>, types: &IRTypeInfo, solver: &mut Solver<B>) {
    match value {
        Val::Enum(member) => {
            let name = member.enum_id.to_name();
            solver.get_enum(name, types.enums[&name].len());
        }
        Val::Struct(fields) | Val::SymbolicCtor(_, fields) => {
            for value in fields.values() {
                register_value_enums(value, types, solver);
            }
        }
        Val::Ctor(_, value) => register_value_enums(value, types, solver),
        Val::Vector(values) | Val::List(values) => {
            for value in values {
                register_value_enums(value, types, solver);
            }
        }
        _ => (),
    }
}

#[allow(clippy::too_many_arguments)]
fn diagnose_slot<B: BV>(
    base: &LocalFrame<B>,
    region: &Region,
    space: &str,
    name: Name,
    raw_a: diagnostics::RawValue<B>,
    raw_b: diagnostics::RawValue<B>,
    a: Option<&Val<B>>,
    b: Option<&Val<B>>,
    failure: Option<diagnostics::Failure>,
    error: Option<&ExecError>,
    shared: &SharedState<B>,
    solver: &Solver<B>,
) {
    use serde_json::json;
    let original = match space {
        "vars" => base.vars().get(&name),
        "lets" => base.lets().get(&name),
        _ => None,
    };
    let ty = if space == "registers" {
        shared.registers.get(&name)
    } else {
        [diagnostics::RawValue::from_uval(original), raw_a, raw_b]
            .into_iter()
            .find_map(|value| value.ty())
            .or_else(|| {
                base.instrs.iter().find_map(|instr| match instr {
                    Instr::Decl(id, ty, _) | Instr::Init(id, ty, _, _) if *id == name => Some(ty),
                    _ => None,
                })
            })
            .or_else(|| {
                shared
                    .functions
                    .get(&base.function_name)
                    .and_then(|(args, _, _)| args.iter().find_map(|(id, ty)| (*id == name).then_some(*ty)))
            })
    };
    let left = diagnostics::describe_raw(raw_a, solver, &shared.symtab);
    let right = diagnostics::describe_raw(raw_b, solver, &shared.symtab);
    let leaf = failure.as_ref().map(|failure| failure.json(&shared.symtab));
    let difference = if raw_a.is_missing() || raw_b.is_missing() {
        "missing_arm"
    } else if left["raw"] != right["raw"] {
        "init_mismatch"
    } else {
        failure.as_ref().map_or("unsupported_value", |failure| failure.difference)
    };
    diagnostics::emit(json!({"stage":"merge_states",
        "at":{"function":diagnostics::name_string(base.function_name,&shared.symtab),"pc":base.pc},
        "slot":{"space":space,"name":diagnostics::name_string(name,&shared.symtab),
            "decl_type":ty.map(|ty|diagnostics::type_string(ty,&shared.symtab)),
            "base_present":if space=="registers" {shared.registers.contains_key(&name)} else {original.is_some()},
            "drop_eligible":space=="vars" && region.local_variables.contains(&name) && original.is_none()},
        "path":leaf.as_ref().map(|leaf|&leaf["path"]),"left":left,"right":right,
        "after_init":{"left":diagnostics::describe_value(a,solver,&shared.symtab),"right":diagnostics::describe_value(b,solver,&shared.symtab)},
        "failure":leaf,"difference":difference,
        "error":error.map(diagnostics::describe_error),
        "reason":if matches!(error,Some(ExecError::IncompatibleUnionPayload)) {"union_payload"} else {"incompatible_state"}
    }));
}

#[allow(clippy::too_many_arguments)]
fn merge_states<'ir, B: BV>(
    record_id: usize,
    condition: Sym,
    base: &LocalFrame<'ir, B>,
    left: LocalFrame<'ir, B>,
    right: LocalFrame<'ir, B>,
    region: &Region,
    state: &TaskState<B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<LocalFrame<'ir, B>, ExecError> {
    let incompatible = || reject(base, SpeculativeRejectReason::IncompatibleState);
    let mut merged = base.clone();
    let lhs = left.local_state.speculative_access.as_ref().unwrap();
    let rhs = right.local_state.speculative_access.as_ref().unwrap();
    if let Some(limits) = &state.execution_limits {
        if limits.max_path_depth.is_some()
            && left.execution_limit_state.control_flow_steps() != right.execution_limit_state.control_flow_steps()
        {
            return Err(reject(base, SpeculativeRejectReason::DepthMismatch));
        }
        if limits.max_backjumps_per_loop.is_some()
            && left.execution_limit_state.loop_counts != right.execution_limit_state.loop_counts
        {
            return Err(reject(base, SpeculativeRejectReason::LoopHistoryMismatch));
        }
    }
    if let Some((reg, _)) = state.pc_limit {
        if lhs.writes.modified_regs.contains(&reg) || rhs.writes.modified_regs.contains(&reg) {
            return Err(reject(base, SpeculativeRejectReason::SamplingState));
        }
    }
    merged.execution_limit_state =
        if left.execution_limit_state.control_flow_steps() >= right.execution_limit_state.control_flow_steps() {
            left.execution_limit_state.clone()
        } else {
            right.execution_limit_state.clone()
        };
    // 活跃的区域局部槽位必须两臂存在；静态证明离开区域不再读取的槽位直接删除。
    for lets in [false, true] {
        let a = if lets { left.lets() } else { left.vars() };
        let b = if lets { right.lets() } else { right.vars() };
        let original = if lets { base.lets() } else { base.vars() };
        let names: std::collections::BTreeSet<_> = a.keys().chain(b.keys()).copied().collect();
        for name in names {
            // End之后不再读取局部机器整数；不同具体值不能合成符号长度。
            // 可合并的基态槽位和输入仍供导出使用，不能一并删除。
            if !lets
                && name != RETURN
                && matches!(
                    (a.get(&name), b.get(&name)),
                    (Some(UVal::Init(Val::I64(_))), _) | (_, Some(UVal::Init(Val::I64(_))))
                )
                && matches!(left.instrs.get(left.pc), Some(Instr::End))
                && matches!(right.instrs.get(right.pc), Some(Instr::End))
            {
                merged.vars_mut().remove(&name);
                continue;
            }
            if !lets && region.local_variables.contains(&name) && !original.contains_key(&name) {
                merged.vars_mut().remove(&name);
                continue;
            }
            let (mut va, mut vb) = (a.get(&name).cloned(), b.get(&name).cloned());
            if matches!((&va, &vb), (Some(UVal::Init(a)), Some(UVal::Init(b))) if a == b)
                || matches!((&va, &vb), (Some(UVal::Uninit(a)), Some(UVal::Uninit(b))) if std::ptr::eq(*a, *b))
            {
                if let Some(value) = va {
                    if lets {
                        merged.lets_mut().insert(name, value);
                    } else {
                        merged.vars_mut().insert(name, value);
                    }
                }
                continue;
            }
            let ty = match (original.get(&name), &va, &vb) {
                (Some(UVal::Uninit(ty)), _, _) => Some(*ty),
                (_, Some(UVal::Uninit(ty)), _) | (_, _, Some(UVal::Uninit(ty))) => Some(*ty),
                _ => None,
            };
            if let Some(ty) = ty.filter(|_| matches!(va, Some(UVal::Uninit(_))) || matches!(vb, Some(UVal::Uninit(_))))
            {
                let initial = symbolic(ty, shared, solver, info)?;
                if matches!(va, Some(UVal::Uninit(_))) {
                    va = Some(UVal::Init(initial.clone()));
                }
                if matches!(vb, Some(UVal::Uninit(_))) {
                    vb = Some(UVal::Init(initial));
                }
            }
            let (Some(UVal::Init(a)), Some(UVal::Init(b))) = (&va, &vb) else {
                if diagnostics::enabled() {
                    diagnose_slot(
                        base,
                        region,
                        if lets { "lets" } else { "vars" },
                        name,
                        diagnostics::RawValue::from_uval(a.get(&name)),
                        diagnostics::RawValue::from_uval(b.get(&name)),
                        None,
                        None,
                        None,
                        None,
                        shared,
                        solver,
                    );
                }
                return Err(incompatible());
            };
            register_value_enums(a, &shared.type_info, solver);
            register_value_enums(b, &shared.type_info, solver);
            // 帧内普通Sail整数已固定为128位表示，可沿用通用ITE承载计数数据。
            // 机器整数、寄存器及复合载荷仍走严格合并，保持长度／位宽与载荷边界。
            let mut value_trace = diagnostics::enabled().then(diagnostics::ValueTrace::start);
            let value = match (a, b) {
                (Val::I128(_), Val::I128(_)) => crate::primop_util::build_ite(condition, a, b, solver, info),
                _ => crate::primop_util::merge_val(condition, a, b, solver, info),
            }
            .map_err(|error| {
                if diagnostics::enabled() && !matches!(error, ExecError::Smt(_) | ExecError::Timeout) {
                    diagnose_slot(
                        base,
                        region,
                        if lets { "lets" } else { "vars" },
                        name,
                        diagnostics::RawValue::from_uval(if lets { left.lets() } else { left.vars() }.get(&name)),
                        diagnostics::RawValue::from_uval(if lets { right.lets() } else { right.vars() }.get(&name)),
                        Some(a),
                        Some(b),
                        value_trace.take().and_then(diagnostics::ValueTrace::finish),
                        Some(&error),
                        shared,
                        solver,
                    );
                }
                match error {
                    ExecError::Smt(_) | ExecError::Timeout => error,
                    ExecError::IncompatibleUnionPayload => reject(base, SpeculativeRejectReason::UnionPayload),
                    _ => incompatible(),
                }
            })?;
            if lets {
                merged.lets_mut().insert(name, UVal::Init(value));
            } else {
                merged.vars_mut().insert(name, UVal::Init(value));
            }
        }
    }
    let registers: HashSet<_> = lhs.writes.modified_regs.union(&rhs.writes.modified_regs).copied().collect();
    let mut retained_initials = Vec::new();
    let read_or_written: std::collections::BTreeSet<_> =
        lhs.writes.read_regs.union(&rhs.writes.read_regs).chain(registers.iter()).collect();
    for reg in read_or_written {
        if base.regs().is_relaxed(*reg) || base.regs().has_old_writes(*reg) {
            return Err(reject(base, SpeculativeRejectReason::RelaxedRegister));
        }
        let a = left.regs().get_last_if_initialized(*reg);
        let b = right.regs().get_last_if_initialized(*reg);
        let value = if registers.contains(reg) {
            let initial = if a.is_none() || b.is_none() {
                let value = merged.regs_mut().get(*reg, shared, solver, info)?.expect("写入寄存器必须存在").clone();
                // 未写臂保留的初值也是后态依赖；发布初态元数据，不伪造架构读取。
                solver.add_event(Event::AssumeReg(*reg, Vec::new(), value.clone()));
                retained_initials.push((*reg, value.clone()));
                Some(value)
            } else {
                None
            };
            let a = a.or(initial.as_ref()).unwrap();
            let b = b.or(initial.as_ref()).unwrap();
            register_value_enums(a, &shared.type_info, solver);
            register_value_enums(b, &shared.type_info, solver);
            let mut value_trace = diagnostics::enabled().then(diagnostics::ValueTrace::start);
            crate::primop_util::merge_val(condition, a, b, solver, info).map_err(|error| {
                if diagnostics::enabled() && !matches!(error, ExecError::Smt(_) | ExecError::Timeout) {
                    let declared = shared.registers.get(reg).expect("诊断寄存器必须有声明");
                    let raw_a = left
                        .regs()
                        .get_last_if_initialized(*reg)
                        .map_or(diagnostics::RawValue::Uninit(declared), diagnostics::RawValue::Init);
                    let raw_b = right
                        .regs()
                        .get_last_if_initialized(*reg)
                        .map_or(diagnostics::RawValue::Uninit(declared), diagnostics::RawValue::Init);
                    diagnose_slot(
                        base,
                        region,
                        "registers",
                        *reg,
                        raw_a,
                        raw_b,
                        Some(a),
                        Some(b),
                        value_trace.take().and_then(diagnostics::ValueTrace::finish),
                        Some(&error),
                        shared,
                        solver,
                    );
                }
                match error {
                    ExecError::Smt(_) | ExecError::Timeout => error,
                    ExecError::IncompatibleUnionPayload => reject(base, SpeculativeRejectReason::UnionPayload),
                    _ => incompatible(),
                }
            })?
        } else {
            a.or(b).expect("已读取寄存器必须初始化").clone()
        };
        merged.regs_mut().assign(*reg, value, shared);
    }
    let shared_regs: HashSet<_> = lhs.writes.read_regs.intersection(&rhs.writes.read_regs).copied().collect();
    let common_a: Vec<_> = lhs
        .reads
        .iter()
        .filter(|(reg, _, _)| shared_regs.contains(reg))
        .map(|(reg, accessor, _)| (reg, accessor))
        .collect();
    let common_b: Vec<_> = rhs
        .reads
        .iter()
        .filter(|(reg, _, _)| shared_regs.contains(reg))
        .map(|(reg, accessor, _)| (reg, accessor))
        .collect();
    if !lhs.global_state && common_a != common_b {
        return Err(reject(base, SpeculativeRejectReason::RegisterSequence));
    }
    // 合并两臂的写入偏序，拓扑序必须同时保持每一臂的先后关系；形成环则拒绝。
    let mut graph = petgraph::graph::DiGraph::<Name, ()>::new();
    let mut nodes = HashMap::new();
    for order in [&lhs.writes.register_write_order, &rhs.writes.register_write_order] {
        for reg in order {
            nodes.entry(*reg).or_insert_with(|| graph.add_node(*reg));
        }
        for pair in order.windows(2) {
            graph.update_edge(nodes[&pair[0]], nodes[&pair[1]], ());
        }
    }
    let write_order =
        petgraph::algo::toposort(&graph, None).map_err(|_| reject(base, SpeculativeRejectReason::RegisterSequence))?;
    let mut access = lhs.clone();
    access.published_reads = rhs.published_reads.clone();
    Arc::make_mut(&mut merged.local_state).pure_definitions = left.local_state.pure_definitions.clone();
    Arc::make_mut(&mut merged.local_state)
        .pure_definitions
        .extend(right.local_state.pure_definitions[base.local_state.pure_definitions.len()..].iter().copied());
    let mut single_arm_reads = Vec::new();
    if lhs.global_state {
        // 与写入相同，前态读取按两臂首次访问的偏序合并；节点包含完整 accessor。
        let mut graph = petgraph::graph::DiGraph::new();
        let mut nodes = HashMap::new();
        let mut reads = HashMap::new();
        for source in [lhs, rhs] {
            let mut previous = None;
            for ((reg, accessor, value), guard) in source.reads.iter().zip(&source.read_guards) {
                let key = (*reg, accessor.clone());
                let node = *nodes.entry(key.clone()).or_insert_with(|| graph.add_node(key.clone()));
                if let Some(previous) = previous {
                    graph.update_edge(previous, node, ());
                }
                previous = Some(node);
                reads
                    .entry(key)
                    .and_modify(|(_, old_guard): &mut (Val<B>, smtlib::Exp<Sym>)| {
                        // 两臂包含同一读取前缀；用已有 SMT 定义共享条件，避免连续汇合把树复制成指数大小。
                        *old_guard =
                            smtlib::Exp::Var(solver.define_const(
                                smtlib::Exp::Or(Box::new(old_guard.clone()), Box::new(guard.clone())),
                                info,
                            ));
                    })
                    .or_insert_with(|| (value.clone(), guard.clone()));
            }
        }
        let order = petgraph::algo::toposort(&graph, None)
            .map_err(|_| reject(base, SpeculativeRejectReason::RegisterSequence))?;
        access.reads.clear();
        access.read_guards.clear();
        for node in order {
            let (reg, accessor) = &graph[node];
            let (value, guard) = reads.remove(&(*reg, accessor.clone())).unwrap();
            let in_arm =
                |source: &AccessLog<B>| source.reads.iter().any(|(name, path, _)| name == reg && path == accessor);
            if !in_arm(lhs) || !in_arm(rhs) {
                single_arm_reads.push(GuardedRegisterRead {
                    register: *reg,
                    accessor: accessor.clone(),
                    value: value.clone(),
                    guard: guard.clone(),
                });
            }
            access.reads.push((*reg, accessor.clone(), value));
            access.read_guards.push(guard);
        }
    } else {
        for source in [lhs, rhs] {
            for ((reg, accessor, value), guard) in source.reads.iter().zip(&source.read_guards) {
                if !shared_regs.contains(reg) {
                    single_arm_reads.push(GuardedRegisterRead {
                        register: *reg,
                        accessor: accessor.clone(),
                        value: value.clone(),
                        guard: guard.clone(),
                    });
                }
            }
        }
        let mut right_common =
            rhs.reads.iter().zip(&rhs.read_guards).filter(|((reg, _, _), _)| shared_regs.contains(reg));
        for ((reg, _, _), guard) in access.reads.iter().zip(&mut access.read_guards) {
            if shared_regs.contains(reg) {
                let (_, right_guard) = right_common.next().expect("共同读取序列必须对齐");
                *guard = smtlib::Exp::Var(
                    solver.define_const(smtlib::Exp::Or(Box::new(guard.clone()), Box::new(right_guard.clone())), info),
                );
            }
        }
        for (read, guard) in rhs.reads.iter().zip(&rhs.read_guards) {
            if !shared_regs.contains(&read.0) {
                access.reads.push(read.clone());
                access.read_guards.push(guard.clone());
            }
        }
    }
    access.initial_registers.extend(rhs.initial_registers.clone());
    // 外层另一臂必须复用同一入口初值，不能为嵌套保留状态再次创建自由变量。
    access.initial_registers.extend(retained_initials);
    access.initial_variables.extend(rhs.initial_variables.clone());
    access.initial_lets.extend(rhs.initial_lets.clone());
    access.guard = base.local_state.speculative_access.as_ref().unwrap().guard.clone();
    access.writes.modified_vars.extend(&rhs.writes.modified_vars);
    access.writes.read_regs.extend(&rhs.writes.read_regs);
    access.writes.modified_regs.extend(&rhs.writes.modified_regs);
    access.writes.register_write_order = write_order.into_iter().map(|node| graph[node]).collect();
    Arc::make_mut(&mut merged.local_state).speculative_access = Some(access);
    merged.pc = left.pc;
    let prefix = base.region_merge_records.len();
    merged.region_merge_records.extend(left.region_merge_records[prefix..].iter().cloned());
    merged.region_merge_records.extend(right.region_merge_records[prefix..].iter().cloned());
    merged.region_merge_records.push(RegionMergeRecord {
        record_id,
        parent_record: None,
        arm: "root",
        function: base.function_name,
        branch_pc: region.branch_pc,
        join: region.join,
        condition,
        source_loc: info,
        depth: base.region_execution.as_ref().unwrap().depth,
        dead: false,
        value_symbols: HashSet::new(),
        input_symbols: HashSet::new(),
        single_arm_reads,
        memory_reads: Vec::new(),
    });
    Ok(merged)
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
fn promote_initials<'ir, B: BV>(
    base: &mut LocalFrame<'ir, B>,
    arm: &LocalFrame<'ir, B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) {
    // 首臂惰性初始化的前置寄存器在另臂复用；无读事件的提升不扩大足迹。
    let access = arm.local_state.speculative_access.as_ref().unwrap();
    Arc::make_mut(&mut base.local_state).speculative_access.as_mut().unwrap().published_reads =
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
    arms: Vec<Option<LocalFrame<'ir, B>>>,
    arm_start: Option<usize>,
}

#[allow(clippy::too_many_arguments)]
/// 两个前沿都已到函数出口，只合并返回结果；继续帧从不经过此接口。
#[allow(clippy::too_many_arguments)]
fn fold_loop_exit<'ir, B: BV>(
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
    for exit in [&previous, &next] {
        if !matches!(exit.instrs.get(exit.pc), Some(Instr::End))
            || !exit.local_state.speculative_access.as_ref().unwrap().writes.modified_regs.is_empty()
            || solver.transaction_has_memory_writes()
        {
            return Err(reject(exit, SpeculativeRejectReason::StateEffect));
        }
    }
    // 两前沿可能共享先前轮次的记录，但在本次不同臂条件下各有一份出现。
    // 只给尚未发布的重复后缀换新ID，保留符号与父子关系；已发布前缀不动。
    let prefix = base.region_merge_records.len();
    let previous_ids: HashSet<_> = previous.region_merge_records[prefix..].iter().map(|r| r.record_id).collect();
    let mut renamed = HashMap::new();
    for record in &next.region_merge_records[prefix..] {
        if previous_ids.contains(&record.record_id) {
            renamed.entry(record.record_id).or_insert_with(|| {
                NEXT_RECORD
                    .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
                    .expect("合并记录编号溢出")
            });
        }
    }
    for record in &mut next.region_merge_records[prefix..] {
        if let Some(id) = renamed.get(&record.record_id) {
            record.record_id = *id;
        }
        if let Some(id) = record.parent_record.and_then(|id| renamed.get(&id)) {
            record.parent_record = Some(*id);
        }
    }
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
    Arc::make_mut(&mut merged.local_state).speculative_access.as_mut().unwrap().guard = Some(union);
    Ok(merged)
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
    let mut exit_prefix: Option<LocalFrame<'ir, B>> = None;
    let root_branch = region.branch_pc;
    let root_region = region.clone();
    let remaining = base.region_execution.as_ref().unwrap().remaining.clone();
    let original_base = base.clone();
    let original_frame = frame.clone();
    let mut last_boundary = 0;
    let mut largest_round = 0;
    let mut continuation = None;
    let mut return_guard = None;
    let mut pending = vec![LoopWork {
        original: frame.clone(),
        base,
        region,
        condition,
        target,
        info,
        record_id,
        arms: Vec::new(),
        arm_start: None,
    }];
    loop {
        super::stats::memory_stats::poll(frame, solver);
        if pending.last().unwrap().arms.len() == 2 {
            let mut work = pending.pop().unwrap();
            // 子循环段已提交为完整条件保护的约束；汇合时也保留所属臂条件。
            let finish = |solver: &mut Solver<B>| {
                finish_region(
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
                )
            };
            let mut guard = work.base.local_state.speculative_access.as_ref().unwrap().guard.clone();
            if let Some(returned) = return_guard {
                guard = Some(match guard {
                    Some(parent) => And(Box::new(parent), Box::new(Var(returned))),
                    None => Var(returned),
                });
            }
            let result = match guard {
                Some(guard) => solver.with_transaction_condition(&guard, finish),
                None => finish(solver),
            }?;
            if let Some(parent) = pending.last_mut() {
                match result {
                    RegionResult::Merged => {
                        promote_initials(&mut parent.base, &work.original, shared, solver);
                        parent.arms.push(Some(work.original));
                    }
                    RegionResult::Dead => {
                        solver.discard_transaction_effects_since(parent.arm_start.expect("挂起臂必须有事件标记"));
                        parent.arms.push(None);
                    }
                    RegionResult::Rejected | RegionResult::Suspended => panic!("汇合只能成功或两臂死亡"),
                }
                parent.arm_start = None;
            } else {
                if let Some(prefix) = exit_prefix.take() {
                    let complete = match result {
                        RegionResult::Merged => fold_loop_exit(
                            prefix,
                            work.original,
                            &original_base,
                            &root_region,
                            state,
                            shared,
                            solver,
                            info,
                        )?,
                        RegionResult::Dead => prefix,
                        _ => panic!("循环收尾只能汇合或全部死亡"),
                    };
                    let guard = complete
                        .local_state
                        .speculative_access
                        .as_ref()
                        .unwrap()
                        .guard
                        .clone()
                        .expect("完整退出前沿必须有条件");
                    let condition = solver.define_const(guard.clone(), info);
                    // 完整循环的存活域就是已累计的退出并集；死亡域保持原来的条件约束。
                    solver.assert_region_exit(guard);
                    let mut restored = original_frame.clone();
                    let result = finish_region(
                        record_id,
                        condition,
                        &root_region,
                        &original_base,
                        vec![Some(complete), None],
                        &mut restored,
                        state,
                        shared,
                        solver,
                        info,
                    )?;
                    *frame = restored;
                    return Ok(RegionOutput::complete(result));
                }
                *frame = work.original;
                return Ok(RegionOutput { result, continuation });
            }
            continue;
        }
        let single_work = pending.len() == 1;
        let exit_spine = (eligible || iterative)
            && continuation.is_none()
            && pending.iter().all(|work| {
                work.arms.len() == 1
                    && work.arms[0].as_ref().is_some_and(|arm| {
                        matches!(arm.instrs.get(arm.pc), Some(Instr::End))
                            && arm.local_state.speculative_access.as_ref().unwrap().writes.modified_regs.is_empty()
                    })
            });
        let completed_exits = pending.len();
        let work = pending.last_mut().unwrap();
        assert!(work.arm_start.is_none(), "前一逻辑臂必须先收尾");
        work.arm_start = Some(solver.transaction_effect_mark());
        let first = work.arms.is_empty();
        let guard = if first { Var(work.condition) } else { Not(Box::new(Var(work.condition))) };
        let mut arm = work.base.clone();
        arm.pc = if first { work.target } else { work.original.pc + 1 };
        let access = Arc::make_mut(&mut arm.local_state).speculative_access.as_mut().unwrap();
        let guard = match access.guard.take() {
            Some(parent) => And(Box::new(parent), Box::new(guard)),
            None => guard,
        };
        access.guard = Some(guard.clone());
        let tx = solver.start_transaction_with_guard(Some(guard));
        let result = run_loop(tid, task_id, fraction, timeout, stop, sink, &mut arm, state, shared, solver);
        match result {
            Ok(Run::Suspended) => {
                let close_scope = super::stats::region_progress::QueryScope::enter("arm_close");
                let close_result =
                    if solver.region_queries_deferred() { SmtResult::Sat } else { solver.check_sat_for_arm(work.info) };
                drop(close_scope);
                match close_result {
                    SmtResult::Sat => (),
                    SmtResult::Unsat => {
                        solver.commit_dead_transaction();
                        work.arms.push(None);
                        work.arm_start = None;
                        continue;
                    }
                    SmtResult::Unknown => {
                        solver.rollback_transaction(tx);
                        return Err(reject(&arm, SpeculativeRejectReason::SolverUnknown));
                    }
                    SmtResult::Error(error) => {
                        solver.rollback_transaction(tx);
                        return Err(ExecError::Smt(error));
                    }
                }
                assert!(!solver.transaction_invalid(), "循环段提交前保存点必须有效");
                solver.commit_transaction();
                let branch = arm.region_execution.as_mut().unwrap().pending_branch.take();
                if let Some((condition, target, region, info)) = branch {
                    let used = state.region_step_budget.saturating_sub(remaining.load(Ordering::Relaxed));
                    if region.branch_pc == root_branch {
                        largest_round = largest_round.max(used.saturating_sub(last_boundary));
                        last_boundary = used;
                    }
                    let no_writes =
                        arm.local_state.speculative_access.as_ref().unwrap().writes.modified_regs.is_empty();
                    if iterative
                        && single_work
                        && exit_spine
                        && region.branch_pc == root_branch
                        && no_writes
                        && !solver.transaction_has_memory_writes()
                    {
                        let exit = work.arms.pop().unwrap().expect("退出脊柱必须已有存活前沿");
                        exit_prefix = Some(match exit_prefix.take() {
                            Some(previous) => fold_loop_exit(
                                previous,
                                exit,
                                &original_base,
                                &root_region,
                                state,
                                shared,
                                solver,
                                info,
                            )?,
                            None => exit,
                        });
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
                        Arc::make_mut(&mut next.local_state).speculative_access.as_mut().unwrap().guard = Some(guard);
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
                                "steps_since_budget_renewal":used,"logical_frontiers":2,
                                "returned_records":exit_prefix.as_ref().unwrap().region_merge_records.len(),
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
                            arms: Vec::new(),
                            arm_start: None,
                        };
                        // 预算由实际回边更新；此处只收敛前沿，避免半轮重复授予预算。
                        last_boundary = 0;
                        largest_round = 0;
                        continue;
                    }
                    if exit_prefix.is_some() {
                        return Err(reject(&arm, SpeculativeRejectReason::StateEffect));
                    }
                    if eligible
                        && exit_spine
                        && region.branch_pc == root_branch
                        && no_writes
                        && !solver.transaction_has_memory_writes()
                        && largest_round > 0
                        && remaining.load(Ordering::Relaxed) <= largest_round.saturating_mul(2)
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
                                serde_json::json!({"kind":"loop_segment","function":diagnostics::name_string(original_frame.function_name,&shared.symtab),"pc":root_branch,"call_instance":original_frame.local_state.call_instance,"steps":used,"remaining":remaining.load(Ordering::Relaxed),"completed_exits":completed_exits,"continuation_pc":continued.pc})
                            );
                        }
                        continuation = Some((returned, continued));
                        return_guard = Some(returned);
                        // 继续臂已单独保存；这里只折叠已完成出口，补集将在最外层提交后成为普通任务。
                        work.arms.push(None);
                        work.arm_start = None;
                        continue;
                    }

                    let record_id = NEXT_RECORD
                        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
                        .expect("合并记录编号溢出");
                    pending.push(LoopWork {
                        original: arm.clone(),
                        base: arm,
                        region,
                        condition,
                        target,
                        info,
                        record_id,
                        arms: Vec::new(),
                        arm_start: None,
                    });
                } else {
                    assert!(
                        work.region.join == RegionPoint::Instruction(arm.pc)
                            || (work.region.join == RegionPoint::FunctionExit
                                && matches!(arm.instrs[arm.pc], Instr::End)),
                        "非分叉挂起必须抵达共同出口"
                    );
                    promote_initials(&mut work.base, &arm, shared, solver);
                    work.arms.push(Some(arm));
                    work.arm_start = None;
                }
            }
            Err(ExecError::AssertionFailure(..))
                if !match &arm.instrs[arm.pc] {
                    Instr::Exit(ExitCause::AssertionFailure, _) => true,
                    Instr::PrimopBinary(_, f, _, _, _) => {
                        std::ptr::fn_addr_eq(*f, primop::optimistic_assert::<B> as primop::Binary<B>)
                            || std::ptr::fn_addr_eq(*f, primop::pessimistic_assert::<B> as primop::Binary<B>)
                    }
                    _ => false,
                } =>
            {
                solver.rollback_transaction(tx);
                return Err(reject(&arm, SpeculativeRejectReason::SymbolicAssertion));
            }
            Ok(Run::Dead) | Err(ExecError::AssertionFailure(..)) => {
                // 具体失败与普通执行同义：仅删除完整到达守卫覆盖的臂。
                // 符号断言已在原语处记录义务，不会从这里静默丢弃。
                solver.commit_dead_transaction();
                work.arms.push(None);
                work.arm_start = None;
            }
            Err(error) => {
                diagnostics::execute_arm_error(arm.function_name, arm.pc, &error, &shared.symtab);
                solver.rollback_transaction(tx);
                return Err(match error {
                    ExecError::SpeculativeReject { .. } | ExecError::Smt(_) | ExecError::Timeout => error,
                    ExecError::Z3Unknown => reject(&arm, SpeculativeRejectReason::SolverUnknown),
                    _ => reject(&arm, SpeculativeRejectReason::IncompatibleState),
                });
            }
            Ok(_) => {
                solver.rollback_transaction(tx);
                return Err(reject(&arm, SpeculativeRejectReason::RegionEscaped));
            }
        }
    }
}
