//! 区域推演只调用真实执行循环；此模块负责边界、事务与状态合并。
use super::region_summary::{function_effect_summaries, instruction_effect, CachedReject, FunctionEffect};
use super::*;
use crate::config::MergeMode;
use crate::ir::regions::{FunctionRegions, Region, RegionOptions, RegionPoint, RegionRejection};

/// 共享两臂、调用与所有嵌套区域的预算，覆盖 141 条指令的谓词链并限制递归调用。
pub const DEFAULT_REGION_STEP_BUDGET: usize = 4096;
/// 每层持有回滚层与当前臂两层保存点；16 层至多占 32 层，给 64 层上限留出一倍余量。
pub const MAX_REGION_MERGE_DEPTH: usize = 16;
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
    pub mode: MergeMode,
    pub origin: (Name, usize, SourceLoc),
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
}

impl<B: BV> AccessLog<B> {
    /// 发布发生在真实读取处，保证读取先于使用它的 SMT 定义；第二臂复用已发布的同序号读取。
    /// 计数属于帧快照，死臂/拒绝回滚后不会抑制存活臂的事件。
    pub fn record_read(&mut self, reg: Name, accessor: Vec<Accessor>, value: Val<B>) -> Result<bool, ExecError> {
        if !self.writes.register_write_order.is_empty() {
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
            solver.assert(valid);
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
    match solver.check_sat_with(exp, info) {
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
            if !log.writes_allowed {
                return Err(log.reject(SpeculativeRejectReason::CalleeStateWrite));
            }
        }
        if register {
            if !log.writes.modified_regs.insert(id) {
                return Err(log.reject(SpeculativeRejectReason::RepeatedRegisterWrite));
            }
            if log.writes.read_regs.contains(&id) {
                return Err(log.reject(SpeculativeRejectReason::RegisterReadWrite));
            }
            log.writes.register_write_order.push(id);
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
        if !execution.region.nodes.contains(&frame.pc) {
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
    let summaries = state.region_effect_summaries.get_or_init(|| function_effect_summaries(shared));
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
) -> Result<Arc<Region>, ExecError> {
    let mut cache = shared.function_regions.lock().unwrap();
    let analysis = cache.entry(frame.function_name).or_insert_with(|| {
        FunctionRegions::with_options(
            frame.instrs,
            RegionOptions {
                have_exception: Some(shared.symtab.lookup(shared.symtab.to_str(HAVE_EXCEPTION))),
                terminal_calls: &summaries
                    .iter()
                    .filter_map(|(name, summary)| summary.non_returning.then_some(*name))
                    .collect::<Vec<_>>(),
            },
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

pub(super) enum RegionResult {
    Merged,
    Dead,
    Rejected,
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
    assert_ne!(mode, MergeMode::Off, "Off 不能进入区域合并");
    let nested = frame.region_execution.is_some();
    shared.execution_stats.merge_attempt();
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
            None => {
                region(frame, shared, state.region_effect_summaries.get_or_init(|| function_effect_summaries(shared)))
                    .and_then(|region| {
                        for pc in &region.nodes {
                            if let Some(rejection) = instruction_effect(
                                frame.function_name,
                                *pc,
                                &frame.instrs[*pc],
                                shared,
                                state.region_effect_summaries.get_or_init(|| function_effect_summaries(shared)),
                            ) {
                                return Err(rejection.error());
                            }
                        }
                        Ok(region)
                    })
            }
        }
    };
    let replay_join = candidate.as_ref().ok().map(|region| region.join);
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
            shared.execution_stats.merge_candidate();
            let depth = frame.region_execution.as_ref().map_or(1, |execution| execution.depth + 1);
            if depth > MAX_REGION_MERGE_DEPTH {
                Err(reject(frame, SpeculativeRejectReason::NestingLimit))
            } else {
                let record_start = frame.region_merge_records.len();
                let tx = solver.start_transaction();
                let result = execute_region(
                    condition, target, region, depth, mode, tid, task_id, fraction, timeout, stop, sink, frame, state,
                    shared, solver, info,
                );
                match &result {
                    Ok(_) => {
                        assert!(!solver.transaction_invalid(), "区域提交前保存点必须有效");
                        solver.commit_transaction();
                        if !nested {
                            // 注意（ATTENTION）：主迹保留两臂 ReadMem 的并集，不能作为精确读序列。
                            // 保存完整 guard 与主迹访存序号，供样本检查过滤另一臂的读取。
                            let events = solver.committed_transaction_events();
                            let memory_count =
                                events.iter().filter(|(_, event)| event.is_memory_read_or_write()).count();
                            if memory_count != 0 {
                                let offset = solver
                                    .trace()
                                    .to_vec()
                                    .iter()
                                    .filter(|event| event.is_memory_read_or_write())
                                    .count()
                                    .checked_sub(memory_count)
                                    .expect("提交事件必须属于主迹后缀");
                                let root = frame.region_merge_records.last_mut().expect("提交必须有根记录");
                                assert!(root.parent_record.is_none());
                                root.memory_reads = events
                                    .iter()
                                    .filter(|(_, event)| event.is_memory_read_or_write())
                                    .enumerate()
                                    .filter_map(|(index, (guard, event))| {
                                        if event.is_memory_read() {
                                            guard.as_ref().map(|guard| (offset + index, guard.clone(), event.clone()))
                                        } else {
                                            None
                                        }
                                    })
                                    .collect();
                            }
                            super::merge_record::publish(
                                &mut frame.region_merge_records[record_start..],
                                &frame.local_state.pure_definitions,
                                task_id,
                                shared,
                                solver,
                            );
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
            shared.execution_stats.merge_finished(true);
            shared.execution_stats.rule_finished(rule, None);
            Ok(result)
        }
        Err(error) => {
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
) -> Result<RegionResult, ExecError> {
    use smtlib::Exp::{Not, Var};
    static NEXT_RECORD: AtomicUsize = AtomicUsize::new(0);
    let record_id = NEXT_RECORD
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
        .expect("合并记录编号溢出");
    let parent = frame.region_execution.clone();
    let execution = RegionExecution {
        region: region.clone(),
        entry_depth: frame.backtrace.len(),
        write_depth: parent.as_ref().map_or(frame.backtrace.len(), |execution| execution.write_depth),
        remaining: parent.as_ref().map_or_else(
            || Arc::new(AtomicUsize::new(state.region_step_budget)),
            |execution| execution.remaining.clone(),
        ),
        depth,
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
        });
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
                match solver.check_sat(info) {
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
                solver.commit_dead_transaction();
                arms.push(None);
            }
            Err(error) => {
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
    merged.region_execution = parent;
    merged.speculation_mode = frame.speculation_mode;
    if merged.region_execution.is_none() {
        // 仅前置状态/访问足迹可信，需要逐条精确读写顺序时不可信。
        // 读取在真实读取处缓冲，提交时按并集发布；此处补发以 ITE 保留原值的条件写入。
        let access = Arc::make_mut(&mut merged.local_state).speculative_access.take().unwrap();
        for reg in access.writes.register_write_order {
            if zencode::decode(shared.symtab.to_str(reg)) != "_TLB" {
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
            let (Some(UVal::Init(a)), Some(UVal::Init(b))) = (va, vb) else {
                return Err(incompatible());
            };
            register_value_enums(&a, &shared.type_info, solver);
            register_value_enums(&b, &shared.type_info, solver);
            let value =
                crate::primop_util::merge_val(condition, &a, &b, solver, info).map_err(|error| match error {
                    ExecError::Smt(_) | ExecError::Timeout => error,
                    ExecError::IncompatibleUnionPayload => reject(base, SpeculativeRejectReason::UnionPayload),
                    _ => incompatible(),
                })?;
            if lets {
                merged.lets_mut().insert(name, UVal::Init(value));
            } else {
                merged.vars_mut().insert(name, UVal::Init(value));
            }
        }
    }
    let registers: HashSet<_> = lhs.writes.modified_regs.union(&rhs.writes.modified_regs).copied().collect();
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
                Some(merged.regs_mut().get(*reg, shared, solver, info)?.expect("写入寄存器必须存在").clone())
            } else {
                None
            };
            let a = a.or(initial.as_ref()).unwrap();
            let b = b.or(initial.as_ref()).unwrap();
            register_value_enums(a, &shared.type_info, solver);
            register_value_enums(b, &shared.type_info, solver);
            crate::primop_util::merge_val(condition, a, b, solver, info).map_err(|error| match error {
                ExecError::Smt(_) | ExecError::Timeout => error,
                ExecError::IncompatibleUnionPayload => reject(base, SpeculativeRejectReason::UnionPayload),
                _ => incompatible(),
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
    if common_a != common_b {
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
    let mut right_common = rhs.reads.iter().zip(&rhs.read_guards).filter(|((reg, _, _), _)| shared_regs.contains(reg));
    for ((reg, _, _), guard) in access.reads.iter().zip(&mut access.read_guards) {
        if shared_regs.contains(reg) {
            let (_, right_guard) = right_common.next().expect("共同读取序列必须对齐");
            *guard = smtlib::Exp::Or(Box::new(guard.clone()), Box::new(right_guard.clone()));
        }
    }
    for (read, guard) in rhs.reads.iter().zip(&rhs.read_guards) {
        if !shared_regs.contains(&read.0) {
            access.reads.push(read.clone());
            access.read_guards.push(guard.clone());
        }
    }
    access.initial_registers.extend(rhs.initial_registers.clone());
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
                    let regions = cache.entry(*function).or_insert_with(|| {
                        let summaries = summaries.get_or_init(|| function_effect_summaries(shared));
                        FunctionRegions::with_options(
                            body,
                            RegionOptions {
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
