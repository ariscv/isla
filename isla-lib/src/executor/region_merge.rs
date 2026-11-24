//! 区域推演只调用真实执行循环；此模块负责边界、事务与状态合并。
use super::concrete_values::ConsumerRetry;
use super::region_engine::{
    advance_arm, append_loop_exit, branch_arm, charge_fragment_growth, finish_arrivals, finish_prepared_region,
    finish_region, loop_exit_guard, publish_committed_records, publish_region_records, publish_register_writes,
    record_projected_arrival, LoopDependencies, ReadyFragments,
};
use super::region_summary::{function_effect_summaries, instruction_effect, CachedReject, FunctionEffect};
use super::stats::merge_diagnostics as diagnostics;
use super::*;
use crate::config::MergeMode;
use crate::error::{SmtError, Z3Timeout};
use crate::executor::stats::region_cost as cost;
use crate::ir::regions::{FunctionRegions, Region, RegionOptions, RegionPoint, RegionRejection};

mod consumer_continuation;
mod delivery;
mod exception_continuation;
mod loop_fold;
mod parallel_arms;
mod parallel_errors;
pub(super) mod prefix_commit;

/// 任一祖先区域拒绝时，随该次推演撤销失败任务的发布。
pub(super) struct ArmErrorSink<'ir, 'task, B: BV> {
    tasks: Mutex<Vec<Task<'ir, 'task, B>>>,
}

impl<'ir, 'task, B: BV> ArmErrorSink<'ir, 'task, B> {
    pub(super) fn new() -> Self {
        Self { tasks: Mutex::new(Vec::new()) }
    }

    pub(super) fn forward(self, sink: &(impl ForkSink<'ir, 'task, B> + ?Sized)) {
        for task in self.tasks.into_inner().unwrap() {
            sink.submit_consumer_error(task);
        }
    }

    /// 区域事务回滚后，缓冲的错误叶也必须由普通片段重新生成。
    fn discard(&self) {
        self.tasks.lock().unwrap().clear();
    }
}

impl<'ir, 'task, B: BV> ForkSink<'ir, 'task, B> for ArmErrorSink<'ir, 'task, B> {
    fn submit(&self, task: Task<'ir, 'task, B>) {
        assert!(task.frame.arm_error.is_some(), "区域内仅允许缓冲错误终态");
        self.tasks.lock().unwrap().push(task);
    }

    fn submit_consumer_error(&self, task: Task<'ir, 'task, B>) {
        self.submit(task);
    }
}

pub(super) struct ScheduledErrors<'a, 'ir, 'task, B: BV> {
    pub errors: &'a ArmErrorSink<'ir, 'task, B>,
    pub scheduler: Option<region_arm::Scheduler<'a, 'ir, B>>,
}

impl<'ir, 'task, B: BV> ForkSink<'ir, 'task, B> for ScheduledErrors<'_, 'ir, 'task, B> {
    fn submit(&self, task: Task<'ir, 'task, B>) {
        self.errors.submit(task);
    }

    fn arm_scheduler(&self) -> Option<region_arm::Scheduler<'_, 'ir, B>> {
        self.scheduler
    }
}

/// 普通区域的两臂与调用共享预算；可收敛的循环按完整轮核算，单轮仍受限。
/// 这只限制一次合并尝试，不截断普通符号执行的路径；配置 -1 时不创建或续配计数器。
pub const DEFAULT_REGION_STEP_BUDGET: Option<usize> = None;
pub(super) static NEXT_RECORD: AtomicUsize = AtomicUsize::new(0);

pub(super) fn next_region_record() -> usize {
    NEXT_RECORD.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1)).expect("合并记录编号溢出")
}
static LOGGED_ITERATION_FOLDS: AtomicUsize = AtomicUsize::new(0);
static NEXT_CALL_SCOPE: AtomicUsize = AtomicUsize::new(0);
pub(super) fn fresh_call_scope() -> usize {
    NEXT_CALL_SCOPE
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |scope| scope.checked_add(1))
        .expect("调用作用域编号溢出")
}

#[derive(Clone)]
pub(super) struct RegionExecution {
    pub remote_cancel: Option<Arc<region_arm::Cancellation>>,
    pub region: Arc<Region>,
    pub entry_depth: usize,
    pub write_depth: usize,
    pub catch_return: Option<usize>,
    pub depth: usize,
    pub remaining: Option<Arc<AtomicUsize>>,
    pub iteration_budget: Option<usize>,
    /// 与根区域共享：局部汇合失败额外产生的片段从同一个上限扣除。
    pub additional_fragments: Option<Arc<AtomicUsize>>,
    pub mode: MergeMode,
    pub origin: (Name, usize, SourceLoc),
    pub pending_branch: Option<(Sym, usize, Arc<Region>, SourceLoc)>,
    pub verified_prefix: Option<prefix_commit::Cut>,
}

impl RegionExecution {
    pub(crate) fn remap_symbols(&mut self, remap: &crate::smt::SymRemap) {
        if let Some((condition, _, _, _)) = &mut self.pending_branch {
            *condition = remap.get(*condition);
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct AccessLog<B> {
    pub writes: WriteSet,
    pub reads: Vec<(Name, Vec<Accessor>, Val<B>)>,
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
    pub ordered_events: bool,
}

impl<B: BV> AccessLog<B> {
    pub(crate) fn remap_symbols(&self, remap: &crate::smt::SymRemap) -> Self {
        Self {
            writes: self.writes.clone(),
            reads: self
                .reads
                .iter()
                .map(|(name, accessor, value)| (*name, accessor.clone(), value.remap_symbols(remap)))
                .collect(),
            read_guards: self.read_guards.iter().map(|guard| remap.exp(guard)).collect(),
            guard: self.guard.as_ref().map(|guard| remap.exp(guard)),
            initial_registers: self
                .initial_registers
                .iter()
                .map(|(name, value)| (*name, value.remap_symbols(remap)))
                .collect(),
            initial_variables: self
                .initial_variables
                .iter()
                .map(|(name, value)| (*name, value.remap_symbols(remap)))
                .collect(),
            initial_lets: self.initial_lets.iter().map(|(name, value)| (*name, value.remap_symbols(remap))).collect(),
            call_scope: self.call_scope,
            function: self.function,
            pc: self.pc,
            location: self.location,
            writes_allowed: self.writes_allowed,
            global_state: self.global_state,
            ordered_events: self.ordered_events,
        }
    }

    /// 每个臂在实际读取处缓冲事件，投影时按读取序号复用事件。
    pub fn record_read(
        &mut self,
        reg: Name,
        accessor: Vec<Accessor>,
        value: &Val<B>,
        traced: bool,
        solver: &mut Solver<B>,
    ) -> Result<(), ExecError> {
        let cost_scope = cost::Scope::enter(cost::Category::StateMerge);
        let _ = &cost_scope;
        if self.global_state || !self.ordered_events {
            // 内部读取使用当前臂的值；前态足迹按寄存器和字段路径只记录一次。
            if self.writes.modified_regs.contains(&reg) {
                return Ok(());
            }
            if let Some(index) = self.reads.iter().position(|(name, path, _)| *name == reg && *path == accessor) {
                // 内层仅一臂读取后，汇合点之后的读取可以扩大原足迹的条件。
                let guard = self.guard.as_ref().expect("区域读取必须有臂条件");
                if &self.read_guards[index] != guard {
                    self.read_guards[index] =
                        smtlib::Exp::Or(Box::new(self.read_guards[index].clone()), Box::new(guard.clone()));
                }
                return Ok(());
            }
        } else if !self.writes.register_write_order.is_empty() {
            return Err(self.reject(SpeculativeRejectReason::RegisterReadAfterWrite));
        }
        let occurrence = self.reads.iter().filter(|(name, path, _)| *name == reg && *path == accessor).count();
        self.initial_registers.entry(reg).or_insert_with(|| value.clone());
        self.writes.read_regs.insert(reg);
        self.read_guards.push(self.guard.clone().expect("区域读取必须有臂条件"));
        if traced {
            solver.add_region_register_read(Event::ReadReg(reg, accessor.clone(), value.clone()), occurrence);
        }
        self.reads.push((reg, accessor, value.clone()));
        Ok(())
    }

    pub fn reject(&self, reason: SpeculativeRejectReason) -> ExecError {
        ExecError::SpeculativeReject {
            cause: None,
            reason,
            function: self.function,
            pc: self.pc,
            location: self.location,
        }
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
        cause: None,
        reason,
        function: frame.function_name,
        pc: frame.pc,
        location: frame.instrs.get(frame.pc).and_then(stats::instr_source_loc).unwrap_or(SourceLoc::unknown()),
    }
}

pub(super) fn reject_query<B: BV>(frame: &LocalFrame<B>, cause: crate::error::SmtError) -> ExecError {
    ExecError::SpeculativeReject {
        reason: cause.reject_reason(),
        location: cause.source_loc(),
        function: frame.function_name,
        pc: frame.pc,
        cause: Some(Box::new(cause)),
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
    let speculative = frame.region_execution.is_some() && !super::region_engine::prefix_resume::active(frame);
    match solver.check_sat_with_for_branch(exp, info, speculative) {
        None => Ok(true),
        Some(SmtResult::Unproven(cause)) if speculative => Err(reject_query(frame, cause)),
        Some(SmtResult::Error(cause))
            if speculative
                && !matches!(&cause, SmtError::Z3Timeout(Z3Timeout::Interrupted(_)))
                && cause.reject_reason().partial_commit(crate::config::RegionOptions::current()) =>
        {
            Err(reject_query(frame, cause))
        }
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
            if super::stats::solver_failures::handle_solver_path_failure(
                solver.exploration_on_unknown(),
                &error,
                frame,
                shared,
            ) =>
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
    value: &Val<B>,
    solver: &mut Solver<B>,
) -> Result<(), ExecError> {
    let cost_scope = cost::Scope::enter(cost::Category::StateMerge);
    let _ = &cost_scope;
    match &mut state.speculative_access {
        Some(log) => log.record_read(reg, accessor, value, true, solver),
        None => {
            solver.add_event(Event::ReadReg(reg, accessor, value.clone()));
            Ok(())
        }
    }
}

pub(super) fn record_write<B: BV>(state: &mut LocalState<B>, id: Name, register: bool) -> Result<(), ExecError> {
    let cost_scope = cost::Scope::enter(cost::Category::StateMerge);
    let _ = &cost_scope;
    if let Some(log) = &mut state.speculative_access {
        if !register && state.lets.contains_key(&id) && !log.global_state && !log.writes_allowed {
            return Err(log.reject(SpeculativeRejectReason::CalleeStateWrite));
        }
        if register {
            let first = log.writes.modified_regs.insert(id);
            if log.ordered_events && !log.global_state && !first {
                return Err(log.reject(SpeculativeRejectReason::RepeatedRegisterWrite));
            }
            if log.ordered_events && !log.global_state && log.writes.read_regs.contains(&id) {
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

/// 本地校验每一步的真实栈深度，并跟踪全局 let 的写许可。
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
    if execution.remote_cancel.as_ref().is_some_and(|cancel| cancel.is_cancelled()) {
        return Err(reject(frame, SpeculativeRejectReason::IncompatibleState));
    }
    let depth = frame.backtrace.len();
    if depth < execution.entry_depth {
        return Err(reject(frame, SpeculativeRejectReason::StackEscaped));
    }
    if depth == execution.entry_depth {
        if execution.region.join == RegionPoint::Instruction(frame.pc) {
            return Ok(true);
        }
        if execution.region.join == RegionPoint::FunctionExit
            && (matches!(frame.instrs.get(frame.pc), Some(Instr::End))
                || (execution.catch_return.is_some() && matches!(frame.instrs.get(frame.pc), Some(Instr::Arbitrary))))
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
            && matches!(frame.instrs.get(frame.pc), Some(Instr::Goto(target)) if *target <= frame.pc)
        {
            execution.remaining.as_ref().expect("逐轮续配必须有有限预算").store(budget, Ordering::Relaxed);
        }
    }
    Ok(false)
}

pub(super) fn preflight<B: BV>(
    frame: &mut LocalFrame<B>,
    state: &TaskState<B>,
    shared: &SharedState<B>,
) -> Result<(), ExecError> {
    if frame.region_execution.is_none() {
        return Ok(());
    }
    let variadic_effect = match &frame.instrs[frame.pc] {
        Instr::PrimopVariadic(_, f, _, _) => primop::variadic_effect(*f),
        _ => None,
    };
    // 两个组织者和远程臂都在调用读原语前检查回调状态。RAM 版本只记录数组内容。
    if variadic_effect == Some(primop::Effect::ReadsMemory) {
        let memory = frame.memory();
        if !memory.is_pure_reader() {
            return Err(reject(frame, SpeculativeRejectReason::ImpureMemoryRead));
        }
        // 保留 Custom 设备原有的推演准入限制。
        if memory.regions().iter().any(|region| matches!(region, crate::memory::Region::Custom(..))) {
            return Err(reject(frame, SpeculativeRejectReason::StateEffect));
        }
    }
    if frame.region_execution.as_ref().unwrap().remote_cancel.is_some()
        && !parallel_arms::transferable_instruction(frame, shared, variadic_effect)
    {
        return Err(reject(frame, SpeculativeRejectReason::StateEffect));
    }
    let global_state = state.execution_limits.as_ref().is_some_and(|limits| limits.region_global_state);
    let summaries = state.region_effect_summaries.get_or_init(|| function_effect_summaries(shared, global_state));
    if let Instr::Call(_, _, callee, _, _) = &frame.instrs[frame.pc] {
        if summaries.get(callee).is_some_and(|summary| summary.non_returning) {
            let limits = state.execution_limits.as_ref().unwrap();
            // 只有所有终止路径都到达已配置过滤的出口，才允许推演执行这个调用。
            if (limits.filter_model_exceptions.is_empty() && !limits.filter_match_failures)
                || !state
                    .filtered_terminal_calls
                    .get_or_init(|| super::region_summary::filtered_terminal_calls(shared, summaries, limits))
                    .contains(callee)
            {
                return Err(reject(frame, SpeculativeRejectReason::RegionEscaped));
            }
        }
    }
    // 已证明直接结束的异常写入属于死臂保存点，可以在严格的被调函数作用域内记账。
    if !global_state
        && matches!(&frame.instrs[frame.pc], Instr::Copy(Loc::Id(CURRENT_EXCEPTION | HAVE_EXCEPTION), ..))
        && state.filtered_terminal_calls.get().is_some_and(|calls| calls.contains(&frame.function_name))
    {
        cost::make_mut(&mut frame.local_state).speculative_access.as_mut().unwrap().writes_allowed = true;
    }
    if variadic_effect == Some(primop::Effect::WritesMemory) && frame.memory().ram_version().is_none() {
        return Err(reject(frame, SpeculativeRejectReason::StateEffect));
    }
    let defer_call_effect_checks =
        state.execution_limits.as_ref().is_some_and(|limits| limits.defer_call_effect_checks);
    if let Some(rejection) = instruction_effect(
        frame.function_name,
        frame.pc,
        &frame.instrs[frame.pc],
        shared,
        summaries,
        defer_call_effect_checks,
    ) {
        return Err(rejection.error());
    }
    Ok(())
}

fn with_function_regions<'ir, B: BV, T>(
    frame: &LocalFrame<'ir, B>,
    shared: &SharedState<'ir, B>,
    summaries: &HashMap<Name, FunctionEffect>,
    loop_analysis: bool,
    f: impl FnOnce(&mut FunctionRegions<B>) -> T,
) -> T {
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
    f(analysis)
}

pub(super) fn region<'ir, B: BV>(
    frame: &LocalFrame<'ir, B>,
    shared: &SharedState<'ir, B>,
    summaries: &HashMap<Name, FunctionEffect>,
    loop_analysis: bool,
) -> Result<Arc<Region>, ExecError> {
    with_function_regions(frame, shared, summaries, loop_analysis, |analysis| analysis.region(frame.pc)).map_err(
        |reason| {
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
        },
    )
}

/// 折叠和分段交付同一有界展开。显式采样和控制流限制仍按原执行入口生效。
fn can_fold_iterations<B: BV>(state: &TaskState<B>, mode: MergeMode) -> bool {
    state.pc_limit.is_none() && unrestricted_adaptive(state, mode)
}

fn unrestricted_adaptive<B: BV>(state: &TaskState<B>, mode: MergeMode) -> bool {
    if mode != MergeMode::Adaptive {
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

/// 用父组织者运行普通分支时，不能绕过使用普通 fork 计数的配置。
pub(super) fn can_split_nested_branch<B: BV>(frame: &LocalFrame<B>, state: &TaskState<B>) -> bool {
    frame.region_execution.as_ref().is_some_and(|execution| can_fold_iterations(state, execution.mode))
}

pub(super) enum RegionResult {
    GuardedExits,
    Merged,
    Dead,
    Rejected,
    /// 前沿停在各自的指令边界，尚待本层认证并交付。
    VerifiedPrefix(ExecError),
    /// 当前汇合分成多个组；各组已保留在挂起帧。
    Separate {
        reason: SpeculativeRejectReason,
        merged_groups: bool,
    },
    /// 同一有环区域的后续轮次交回本层显式工作栈。
    Suspended,
}

/// 两个互补片段仍属于父臂，由当前区域的工作栈继续。
pub(super) fn separate_nested_fragments<'ir, B: BV>(
    frame: &mut LocalFrame<'ir, B>,
    solver: &mut Solver<B>,
    branches: [(usize, smtlib::Exp<Sym>); 2],
) -> Result<(), ExecError> {
    assert!(frame.region_execution.is_some(), "仅嵌套区域可保留普通分叉片段");
    assert!(frame.region_arrivals.is_empty(), "区域入口不能已有未交付片段");
    let parent = frame.region_arm.expect("嵌套区域入口必须属于祖先逻辑臂");
    charge_fragment_growth(frame, 1)?;
    frame.region_arrivals = branches
        .into_iter()
        .map(|(pc, guard)| branch_arm(frame, pc, guard, solver.new_logical_arm(Some(parent))))
        .collect();
    Ok(())
}

pub(super) fn separate_nested_branch<'ir, B: BV>(
    condition: Sym,
    target: usize,
    frame: &mut LocalFrame<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<(), ExecError> {
    use smtlib::Exp::{Not, Var};
    separate_nested_fragments(frame, solver, [(target, Var(condition)), (frame.pc + 1, Not(Box::new(Var(condition))))])
}

/// 局部拆分后保留原拒绝原因及其出错位置。
pub(super) fn record_local_rejection<B: BV>(
    frame: &LocalFrame<B>,
    state: &TaskState<B>,
    shared: &SharedState<B>,
    error: &ExecError,
) {
    let reason = error.rejection_reason().expect("局部拒绝必须有原因");
    let site;
    let rejection = if matches!(error, ExecError::SpeculativeReject { .. }) {
        error
    } else {
        site = reject(frame, reason);
        &site
    };
    shared.execution_stats.merge_rejected(frame.function_name, frame.pc, rejection);
    state.speculation_stats.record_reject(reason);
    if diagnostics::enabled() {
        diagnostics::emit(serde_json::json!({
            "stage":"local_arm_rejected",
            "difference":"local_arm_rejected",
            "reason":reason,"cause":error.query_failure().map(|cause|cause.diagnostic()),"error":error.to_string(),
            "at":{"function":diagnostics::name_string(frame.function_name, &shared.symtab),
                "pc":frame.pc,"location":error.source_loc()}
        }));
    }
}

pub(super) fn separate_nested_retry<B: BV>(
    guards: [smtlib::Exp<Sym>; 2],
    frame: &mut LocalFrame<B>,
    state: &TaskState<B>,
    shared: &SharedState<B>,
    solver: &mut Solver<B>,
) -> Result<(), ExecError> {
    let pc = frame.pc;
    separate_nested_fragments(frame, solver, guards.map(|guard| (pc, guard)))?;
    record_local_rejection(frame, state, shared, &reject(frame, SpeculativeRejectReason::RetryOperand));
    Ok(())
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
    let _scope = super::path_account::Scope::enter(super::path_account::Category::Merge);
    if !frame.region_arrivals.is_empty() {
        return Ok(RegionResult::Suspended);
    }
    let mode = policy(frame, state, info);
    let global_state = state.execution_limits.as_ref().is_some_and(|limits| limits.region_global_state);
    let defer_call_effect_checks =
        state.execution_limits.as_ref().is_some_and(|limits| limits.defer_call_effect_checks);
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
    use diagnostics::FailurePhase;
    let mut diagnostics_attempt = diagnostics::enabled().then(|| {
        diagnostics::AttemptGuard::start(
            task_id.as_usize(),
            frame.function_name,
            frame.pc,
            &shared.symtab,
            info,
            &frame.backtrace,
        )
    });
    let mut failure_phase = FailurePhase::Admission;
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
                        defer_call_effect_checks,
                    ) {
                        return Err(rejection.error());
                    }
                }
                Ok(region)
            }),
        }
    };
    let replay_join = candidate.as_ref().ok().map(|region| region.join);
    let mut pending_errors = ArmErrorSink::new();
    let mut segmented = false;
    let mut prefix_dead = false;
    // 准入拒绝没有子事务，执行拒绝必须先撤销子事务，再向父区域交付片段。
    let mut arm_execution_rolled_back = false;
    let result = match candidate {
        Err(error) => {
            if let ExecError::SpeculativeReject { reason, function, pc, location, .. } = error {
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
                        "difference":SpeculativeRejectReason::NestingLimit,"reason":SpeculativeRejectReason::NestingLimit}));
                }
                Err(reject(frame, SpeculativeRejectReason::NestingLimit))
            } else {
                let record_start = frame.region_merge_records.len();
                failure_phase = FailurePhase::ArmExecution;
                let mut candidate_frame = solver.validates_candidates().then(|| frame.clone());
                let arm_task_entry = parallel_arms::entry(sink, frame, state, &region, shared, solver);
                let tx = solver.start_transaction();
                let defer = solver.defer_region_checks();
                // 开启义务作用域的这一层认证出口；借用父作用域的层把义务留给其所有者。
                let owns_obligations = defer && !solver.region_queries_deferred();
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
                    let output = execute_region(
                        condition,
                        target,
                        frame.pc + 1,
                        arm_task_entry,
                        None,
                        region,
                        depth,
                        mode,
                        tid,
                        task_id,
                        fraction,
                        timeout,
                        stop,
                        &ScheduledErrors { errors: &pending_errors, scheduler: sink.arm_scheduler() },
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
                    if let Ok(RegionResult::VerifiedPrefix(error)) = &output {
                        let reason = error.rejection_reason().expect("切点必须记录拒绝原因");
                        state.speculation_stats.record_reject(reason);
                        shared.execution_stats.merge_rejected(key.0, key.1, error);
                        diagnostics::emit(serde_json::json!({
                            "stage":"verified_prefix_candidate", "difference":"verified_prefix_candidate",
                            "reason":reason, "cause":error.query_failure().map(|cause|cause.diagnostic()),
                            "error":error.to_string(), "location":error.source_loc(),
                        }));
                        failure_phase = FailurePhase::ExitCertification;
                        let candidate = candidate_frame.as_mut().expect("切点必须有可认证候选");
                        prefix_commit::certify_groups(candidate, solver, info, timeout)?;
                        prefix_dead = candidate.region_arrivals.is_empty();
                        return output;
                    }
                    if owns_obligations && output.is_ok() {
                        failure_phase = FailurePhase::ExitObligation;
                        log_phase("obligation_start", None);
                        let _scope = stats::region_progress::QueryScope::enter("exit_obligations");
                        let checked = solver.check_deferred_assertions(info);
                        log_phase("obligation_end", checked.as_ref());
                        match checked {
                            None | Some(SmtResult::Unsat) => (),
                            Some(SmtResult::Sat) => {
                                return Err(reject(frame, SpeculativeRejectReason::SymbolicAssertion))
                            }
                            Some(SmtResult::Unproven(cause)) => return Err(reject_query(frame, cause)),
                            Some(SmtResult::Error(cause))
                                if cause.z3_query_failure().is_some() && solver.exploration_on_unknown().is_some() =>
                            {
                                return Err(reject_query(frame, cause));
                            }
                            Some(SmtResult::Error(error)) => return Err(ExecError::Smt(error)),
                        }
                    }
                    output
                };
                let result = if defer { solver.with_deferred_region_queries(execute) } else { execute(solver) };
                // 完成义务认证后才检查本作用域的正常出口，子层交付仍带原守卫。
                let result = if owns_obligations
                    && result
                        .as_ref()
                        .is_ok_and(|output| !matches!(output, RegionResult::Dead | RegionResult::VerifiedPrefix(_)))
                {
                    failure_phase = FailurePhase::ExitCertification;
                    log_phase("exit_check_start", None);
                    let _scope = stats::region_progress::QueryScope::enter("region_exit");
                    let checked = if solver.validates_candidates() && solver.coi_query_slicing_enabled() {
                        let candidate = candidate_frame.as_ref().expect("出口认证必须有候选帧");
                        let mut symbols = Default::default();
                        candidate.collect_symbolic_variables(&mut symbols);
                        for arrival in &candidate.region_arrivals {
                            arrival.collect_symbolic_variables(&mut symbols);
                        }
                        Some(solver.check_exit_feasibility(symbols, info))
                    } else {
                        solver.check_candidate_sat(info)
                    };
                    log_phase("exit_check_end", checked.as_ref());
                    match checked {
                        None | Some(SmtResult::Sat) => result,
                        // 分段可能还有继续前沿；退出前沿为空不代表整次调用为空。
                        Some(SmtResult::Unsat)
                            if !matches!(result, Ok(RegionResult::GuardedExits))
                                && !pending_errors.tasks.get_mut().unwrap().is_empty() =>
                        {
                            Ok(RegionResult::Dead)
                        }
                        Some(SmtResult::Unsat) => Err(reject(frame, SpeculativeRejectReason::ExitUnsat)),
                        Some(SmtResult::Unproven(cause)) => Err(reject_query(frame, cause)),
                        Some(SmtResult::Error(cause))
                            if cause.z3_query_failure().is_some() && solver.exploration_on_unknown().is_some() =>
                        {
                            Err(reject_query(frame, cause))
                        }
                        Some(SmtResult::Error(error)) => Err(ExecError::Smt(error)),
                    }
                } else {
                    result
                };
                match &result {
                    Ok(_) => {
                        assert!(!solver.transaction_invalid(), "区域提交前保存点必须有效");
                        log_phase("commit_start", None);
                        segmented = matches!(result, Ok(RegionResult::GuardedExits));
                        if let Some(candidate) = candidate_frame {
                            *frame = candidate;
                        }
                        let output = result.as_ref().unwrap();
                        delivery::finish(
                            output,
                            frame,
                            record_start,
                            &mut pending_errors,
                            task_id,
                            fraction,
                            stop,
                            sink,
                            state,
                            shared,
                            solver,
                            info,
                        );
                        log_phase("commit_end", None);
                        if !nested && !matches!(output, RegionResult::VerifiedPrefix(_)) {
                            crate::smt::probe_query_event(
                                || serde_json::json!({"type":"region_commit", "function":zencode::decode(shared.symtab.to_str(frame.function_name)), "branch_pc":key.1, "call_instance":frame.local_state.call_instance,"region":probe_context}),
                            );
                        }
                    }
                    Err(_) => {
                        solver.rollback_transaction(tx);
                        arm_execution_rolled_back = true;
                    }
                }
                result
            }
        }
    };
    let result = match result {
        Err(error)
            if nested
                && error.rejection_reason().is_some_and(|reason| {
                    if !stats::solver_failures::is_solver_failure(&error) && prefix_commit::can_capture(frame, reason) {
                        return false;
                    }
                    let options = crate::config::RegionOptions::current();
                    if arm_execution_rolled_back {
                        !matches!(&error, ExecError::Smt(SmtError::Z3Timeout(Z3Timeout::Interrupted(_))))
                            && reason.partial_commit(options)
                    } else {
                        mode == MergeMode::Adaptive
                            && can_split_nested_branch(frame, state)
                            && reason.split_admission(options)
                    }
                }) =>
        {
            let reason = error.rejection_reason().unwrap();
            // 仍在父臂的分叉点，完整互补守卫和预算一起交给父组织者。
            // 回滚撤销的子事务义务、事件和错误叶由两个片段重新建立。
            match separate_nested_branch(condition, target, frame, solver) {
                Ok(()) => {
                    pending_errors.discard();
                    record_local_rejection(frame, state, shared, &error);
                    Ok(RegionResult::Separate { reason, merged_groups: false })
                }
                Err(error) => Err(error),
            }
        }
        result => result,
    };
    match result {
        Ok(RegionResult::VerifiedPrefix(error)) => {
            let reason = error.rejection_reason().unwrap();
            if let Some(attempt) = diagnostics_attempt.as_mut() {
                attempt.finish_verified_prefix(&error, &shared.symtab);
            }
            shared.execution_stats.rule_finished(rule, Some(reason));
            shared.execution_stats.merge_finished(false);
            if prefix_dead {
                Ok(RegionResult::Dead)
            } else if nested {
                Ok(RegionResult::Separate { reason, merged_groups: false })
            } else {
                Ok(RegionResult::Merged)
            }
        }
        Ok(RegionResult::Separate { reason, merged_groups }) => {
            assert_eq!(nested, !frame.region_arrivals.is_empty());
            if let Some(attempt) = diagnostics_attempt.as_mut() {
                attempt.finish_local_rejection(reason);
            }
            shared.execution_stats.rule_finished(rule, Some(reason));
            shared.execution_stats.merge_finished(!nested && merged_groups);
            if nested {
                Ok(RegionResult::Separate { reason, merged_groups })
            } else {
                Ok(RegionResult::Merged)
            }
        }
        Ok(result) => {
            if let Some(attempt) = diagnostics_attempt.as_mut() {
                attempt.finish_success(matches!(result, RegionResult::Dead));
                if segmented {
                    attempt.finish_segmented();
                }
            }
            shared.execution_stats.merge_finished(true);
            shared.execution_stats.rule_finished(rule, None);
            Ok(if segmented {
                if nested {
                    RegionResult::Suspended
                } else {
                    RegionResult::Merged
                }
            } else {
                result
            })
        }
        Err(error) => {
            if shared.execution_stats.enabled() {
                if let ExecError::Smt(error) = &error {
                    let _log = crate::executor::stats::path_account::Scope::enter(
                        crate::executor::stats::path_account::Category::Log,
                    );
                    eprintln!(
                        "[REGION_SMT_REJECT] {}",
                        serde_json::json!({
                            "function": zencode::decode(shared.symtab.to_str(frame.function_name)),
                            "branch_pc": frame.pc, "nested": nested,
                            "reason":error.reject_reason(), "error": error.to_string(), "source_loc": error.source_loc(),
                        })
                    );
                }
            }
            let reason = error.rejection_reason().unwrap_or(SpeculativeRejectReason::IncompatibleState);
            let site;
            let rejection = if matches!(&error, ExecError::SpeculativeReject { .. }) {
                &error
            } else {
                site = reject(frame, reason);
                &site
            };
            if diagnostics_active {
                diagnostics_attempt.as_mut().unwrap().finish_rejected(failure_phase, rejection, &error, &shared.symtab);
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
            if solver.exploration_on_unknown().is_none() && stats::solver_failures::is_solver_failure(&error) {
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

/// 失败叶在根保存点提交后才可交给调度器。继续组继承同一次路径拆分。
pub(super) fn publish_arm_errors<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
    frame: &mut LocalFrame<'ir, B>,
    errors: Vec<Task<'ir, 'task, B>>,
    solver: &Solver<B>,
    fraction: &mut Fraction,
    sink: &S,
    shared: &SharedState<'ir, B>,
) {
    parallel_errors::publish(errors, solver, sink.arm_scheduler(), |mut task, checked| {
        let Some((_, Event::Fork(id, ..))) = &mut task.fork_cond else {
            unreachable!("失败前沿必须有分叉元数据")
        };
        if matches!(checked, Some(SmtResult::Unsat)) {
            return;
        }
        if let Some(SmtResult::Error(error)) = &checked {
            let error = ExecError::Smt(error.clone());
            let failed = unfreeze_frame(&task.frame);
            if stats::solver_failures::handle_solver_path_failure(
                solver.exploration_on_unknown(),
                &error,
                &failed,
                shared,
            ) {
                return;
            }
        }
        task.frame.arm_error.as_mut().unwrap().1 = matches!(checked, Some(SmtResult::Sat));
        *id = cost::make_mut(&mut frame.execution_limit_state).record_fork();
        task.frame.execution_limit_state = frame.execution_limit_state.clone();
        cost::make_mut(&mut task.frame.execution_limit_state).advance_path_signature(true);
        cost::make_mut(&mut frame.execution_limit_state).advance_path_signature(false);
        for group in &mut frame.region_arrivals {
            let limits = cost::make_mut(&mut group.execution_limit_state);
            assert_eq!(limits.record_fork(), *id, "继续前沿继承同一区域的分叉计数");
            limits.advance_path_signature(false);
        }
        fraction.halve();
        task.fraction = fraction.clone();
        sink.submit(task);
    });
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
        remote_cancel: parent.as_ref().and_then(|execution| execution.remote_cancel.clone()),
        region: region.clone(),
        pending_branch: None,
        verified_prefix: None,
        entry_depth: frame.backtrace.len(),
        catch_return: None,
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
            ordered_events: state.execution_limits.as_ref().is_some_and(|limits| limits.ordered_events),
        });
    }
    base
}

#[allow(clippy::too_many_arguments)]
fn advance_region_arm<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
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
    consumer: bool,
    tx: crate::smt::SolverTransaction,
    info: SourceLoc,
) -> Result<bool, ExecError> {
    if let Some(alive) =
        advance_arm(tid, task_id, fraction, timeout, stop, sink, arm, state, shared, solver, consumer, tx, info)?
    {
        return Ok(alive);
    }
    if arm.region_arrivals.iter().any(prefix_commit::is_cut) {
        // 子层已认证需普通执行的前沿；停止推进兄弟并把完整集合交给本层认证。
        solver.commit_transaction();
        return Ok(true);
    }
    // 本臂已经分成互斥片段；分别关闭，不把任何一个临时条件留在主求解器上。
    let mut pending = ReadyFragments::new(state);
    pending.extend(
        std::mem::take(&mut arm.region_arrivals).into_iter().enumerate().map(|(index, frame)| (vec![index], frame)),
    );
    let mut reached = Vec::new();
    let live_forks = stats::merge_timing::LiveForks::start();
    while let Some((branch, mut fragment)) = pending.pop() {
        live_forks.set(pending.len() + reached.len());
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
                consumer,
                part_tx,
                info,
            )?;
            if step.is_none() {
                solver.commit_transaction();
            }
            Ok(step)
        });
        let mut cut = false;
        match outcome {
            Ok(Some(true)) => {
                cut = prefix_commit::is_cut(&fragment);
                reached.push((branch, fragment));
            }
            Ok(Some(false)) => solver.discard_logical_arm_effects(owner),
            Ok(None) => {
                cut = fragment.region_arrivals.iter().any(prefix_commit::is_cut);
                let children = fragment.region_arrivals.into_iter().enumerate().map(|(index, frame)| {
                    let mut path = branch.clone();
                    path.push(index);
                    (path, frame)
                });
                if cut {
                    reached.extend(children);
                } else {
                    pending.extend(children);
                }
            }
            Err(error) => {
                solver.rollback_transaction(tx);
                return Err(error);
            }
        }
        if cut {
            while let Some(part) = pending.pop() {
                reached.push(part);
            }
            break;
        }
    }
    if reached.is_empty() {
        solver.commit_dead_transaction();
        return Ok(false);
    }
    solver.commit_transaction();
    if reached.len() == 1 {
        *arm = reached.pop().unwrap().1;
    } else {
        // 汇合用逻辑臂顺序，不能让调度产生不同的 ITE 折叠或历史父子关系。
        reached.sort_unstable_by(|(a, _), (b, _)| a.cmp(b));
        arm.region_arrivals = reached.into_iter().map(|(_, frame)| frame).collect();
    }
    Ok(true)
}

#[allow(clippy::too_many_arguments)]
fn execute_region<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
    condition: Sym,
    target: usize,
    fallthrough: usize,
    arm_task_entry: Option<parallel_arms::Entry<'_, B>>,
    consumer: Option<ConsumerRetry>,
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
    let record_id = next_region_record();
    let mut base = prepare_region_base(frame, &region, depth, mode, state, info);
    if region.has_back_edge {
        return execute_loop_region(
            record_id, condition, target, region, base, tid, task_id, fraction, timeout, stop, sink, frame, state,
            shared, solver, info,
        );
    }
    let catcher = (consumer.is_none() && region.join == RegionPoint::FunctionExit)
        .then(|| exception_continuation::find_catcher(frame, &region, shared))
        .flatten();
    base.region_execution.as_mut().unwrap().catch_return = catcher.as_ref().map(|_| fresh_call_scope());
    if crate::config::RegionOptions::current().partial_commit_prefix
        && (frame.speculation_mode == SpeculationMode::Off || frame.region_execution.is_some())
        && unrestricted_adaptive(state, mode)
        && catcher.is_none()
        && solver.validates_candidates()
        && frame.region_execution.as_ref().is_none_or(|parent| parent.remote_cancel.is_none())
    {
        base.region_execution.as_mut().unwrap().verified_prefix = Some(prefix_commit::Cut {
            record_start: frame.region_merge_records.len(),
            resume_in_parent: frame.region_execution.is_some(),
            can_resume_normally: frame
                .region_execution
                .as_ref()
                .is_none_or(|parent| parent.verified_prefix.as_ref().is_some_and(|cut| cut.can_resume_normally)),
            saw_live_merge: false,
            rejection: None,
        });
    }
    let mut arms = [Vec::new(), Vec::new()];
    let mut ready = ReadyFragments::new(state);
    let guards = match &consumer {
        Some(ConsumerRetry::Operand { guards, .. }) => guards.clone(),
        _ => [Var(condition), Not(Box::new(Var(condition)))],
    };
    ready.extend([target, fallthrough].into_iter().zip(guards).enumerate());
    let live_forks = stats::merge_timing::LiveForks::start();
    let initial_state = arm_task_entry.as_ref().map(|_| base.local_state.clone());
    let scheduler = sink.arm_scheduler();
    let job = arm_task_entry.filter(|_| catcher.is_none()).map(|(slot, checkpoint)| {
        let mut remote_base = base.clone();
        // 切点由本地组织者认证。远端若无法完整到达，交回本地执行并使用原切点规则。
        remote_base.region_execution.as_mut().unwrap().verified_prefix = None;
        remote_base.path_timing = super::path_timing::PathTiming::from_snapshot(base.path_timing.fork_snapshot());
        let job = region_arm::ArmJob {
            checkpoint,
            options: solver.arm_context_options(),
            base: remote_base,
            pc: fallthrough,
            guard: Not(Box::new(Var(condition))),
            task: task_id,
            fraction: fraction.clone(),
            timeout,
            info,
        };
        (slot, job, reject(frame, SpeculativeRejectReason::IncompatibleState))
    });
    let mut cut = false;
    let mut local = |cell: Option<&parallel_arms::ArmCell<'ir, B>>| -> Result<(), ExecError> {
        while let Some((side, (pc, guard))) = ready.pop() {
            live_forks.set(if side == 0 { 1 } else { arms[0].len() });
            if side == 1 && !cut {
                if let Some(cell) = cell {
                    match parallel_arms::receive(
                        cell,
                        initial_state.as_ref().unwrap(),
                        &arms[0],
                        &mut base,
                        state,
                        solver,
                        sink,
                        tid,
                        stop,
                        shared,
                    )? {
                        parallel_arms::Received::Dead => continue,
                        parallel_arms::Received::Arrived(arm) => {
                            arms[1].push(arm);
                            continue;
                        }
                        parallel_arms::Received::Retry => (),
                    }
                }
            }
            if !cut && consumer.is_some() && !feasible(frame, solver, &guard, info, shared)? {
                solver.assert(Not(Box::new(guard)));
                continue;
            }
            let owner = solver.new_logical_arm(solver.current_logical_arm());
            let mut arm = branch_arm(&base, pc, guard.clone(), owner);
            if let Some(ConsumerRetry::Choice(guard)) = consumer {
                cost::make_mut(&mut arm.local_state)
                    .concrete_choices
                    .as_mut()
                    .expect("消费者拆分必须已启用")
                    .insert(guard, side == 0);
            }
            if cut {
                // 尚未开始的互补臂从自己的入口继续，其守卫由区域切点认证。
                arms[side].push(arm);
                continue;
            }
            let tx = solver.start_transaction_with_guard(Some(guard));
            if let Some(ConsumerRetry::Operand { split: Some((sym, values)), .. }) = &consumer {
                let bound = if side == 0 { &values[..1] } else { &values[1..] };
                solver.set_operand_bound(*sym, info, bound.to_vec());
            }
            if solver.with_logical_arm(owner, |solver| {
                advance_region_arm(
                    tid,
                    task_id,
                    fraction,
                    timeout,
                    stop,
                    sink,
                    &mut arm,
                    state,
                    shared,
                    solver,
                    consumer.is_some(),
                    tx,
                    info,
                )
            })? {
                if arm.region_arrivals.is_empty() {
                    promote_initials(&mut base, &arm, solver);
                    arms[side].push(arm);
                } else {
                    arms[side] = std::mem::take(&mut arm.region_arrivals);
                    for fragment in &arms[side] {
                        promote_initials(&mut base, fragment, solver);
                    }
                }
                cut = arms[side].iter().any(prefix_commit::is_cut);
            } else if consumer.is_some()
                || crate::config::RegionOptions::current().arm_error_leaf
                || state.observe_assertion_failures
            {
                solver.discard_logical_arm_effects(owner);
            }
        }
        Ok(())
    };
    if let Some((slot, work, failure)) = job {
        parallel_arms::with_worker(slot, scheduler, state, stop, shared, failure, work, local)?;
    } else {
        local(None)?;
    }
    live_forks.set(arms.iter().map(Vec::len).sum::<usize>().saturating_sub(1));
    if cut {
        return Ok(prefix_commit::prepare_frontiers(frame, arms));
    }
    if let Some(catcher) = catcher {
        if arms.iter().flatten().any(|arm| matches!(arm.instrs[arm.pc], Instr::Arbitrary)) {
            return exception_continuation::finish_catch(
                catcher, record_id, condition, base, arms, tid, task_id, fraction, timeout, stop, sink, frame, state,
                shared, solver, info,
            );
        }
    }
    if consumer.is_some() && crate::config::RegionOptions::current().width_closed_continuation {
        if let Some(result) = consumer_continuation::try_width_closed_join(
            record_id, condition, &base, &arms, tid, task_id, fraction, timeout, stop, sink, frame, state, shared,
            solver, info,
        )? {
            return Ok(result);
        }
    }
    finish_arrivals(
        record_id,
        condition,
        &region,
        consumer.is_some(),
        frame.region_execution.is_none(),
        &base,
        arms,
        frame,
        state,
        shared,
        solver,
        info,
    )
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
                            let error = ExecError::SpeculativeReject {
                                cause: None,
                                reason,
                                function: *function,
                                pc,
                                location: *info,
                            };
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
    solver: &mut Solver<B>,
) {
    let cost_scope = cost::Scope::enter(cost::Category::StateMerge);
    let _ = &cost_scope;
    // 首臂惰性初始化的前置寄存器在另臂复用；无读事件的提升不扩大足迹。
    let access = arm.local_state.speculative_access.as_ref().unwrap();
    for (reg, initial) in &access.initial_registers {
        if base.regs().get_last_if_initialized(*reg).is_none() {
            assert_initial_type(initial, solver);
            base.regs_mut().reserve_initial(*reg, initial.clone());
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
    continuations: ReadyFragments<LocalFrame<'ir, B>>,
    parent_arm: Option<crate::smt::LogicalArm>,
    active_arm: Option<crate::smt::LogicalArm>,
}

/// 两个前沿都已到函数出口，只合并返回结果；继续帧从不经过此接口。
#[allow(clippy::too_many_arguments)]
pub(super) fn fold_loop_exit<'ir, B: BV>(
    previous: LocalFrame<'ir, B>,
    next: LocalFrame<'ir, B>,
    history_ids: &mut Option<HashSet<usize>>,
    base: &LocalFrame<'ir, B>,
    region: &Region,
    loop_writes_memory: bool,
    state: &TaskState<B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<LocalFrame<'ir, B>, ExecError> {
    let cost_scope = cost::Scope::enter(cost::Category::StateMerge);
    let _ = &cost_scope;
    for exit in [&previous, &next] {
        let access = exit.local_state.speculative_access.as_ref().unwrap();
        if !matches!(exit.instrs.get(exit.pc), Some(Instr::End))
            || (access.ordered_events && !access.global_state && !access.writes.modified_regs.is_empty())
            || (loop_writes_memory
                && !(crate::config::RegionOptions::current().loop_fold_shapes && exit.memory.ram_version().is_some()))
        {
            let error = reject(exit, SpeculativeRejectReason::StateEffect);
            diagnostics::note_failure_phase(diagnostics::FailurePhase::LoopFold, &error);
            return Err(error);
        }
    }
    fold_exit_frontiers(previous, next, history_ids, base, region, state, shared, solver, info)
}

#[cfg(test)]
thread_local! {
    pub(super) static FOLD_SAMPLES: std::cell::RefCell<Option<Vec<[usize; 7]>>> = const { std::cell::RefCell::new(None) };
    pub(super) static FOLD_HISTORY_ID_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// 已到同一出口的前沿共享记录重编号和状态合并；调用方校验各策略的适用形状。
#[allow(clippy::too_many_arguments)]
pub(super) fn fold_exit_frontiers<'ir, B: BV>(
    previous: LocalFrame<'ir, B>,
    next: LocalFrame<'ir, B>,
    history_ids: &mut Option<HashSet<usize>>,
    base: &LocalFrame<'ir, B>,
    region: &Region,
    state: &TaskState<B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<LocalFrame<'ir, B>, ExecError> {
    let (planned, (start, end)) = super::region_engine::join_groups::PreparedFold::prepare_loop(
        &previous, &next, base, region, state, shared, solver, info,
    )
    .inspect_err(|error| diagnostics::note_failure_phase(diagnostics::FailurePhase::StateMerge, error))?;
    solver.reserve_join_symbols(start, end);
    fold_prepared_exit_frontiers(previous, next, history_ids, base, region, state, shared, solver, info, planned)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn fold_prepared_exit_frontiers<'ir, B: BV>(
    previous: LocalFrame<'ir, B>,
    mut next: LocalFrame<'ir, B>,
    history_ids: &mut Option<HashSet<usize>>,
    base: &LocalFrame<'ir, B>,
    region: &Region,
    state: &TaskState<B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
    planned: super::region_engine::join_groups::PreparedFold<'ir, B>,
) -> Result<LocalFrame<'ir, B>, ExecError> {
    if crate::config::RegionOptions::current().progress && diagnostics::enabled() {
        stats::merge_timing::live_sample(base.function_name, region.branch_pc, &shared.symtab, "fold_exit_frontiers");
    }
    // 两前沿可能共享先前轮次的记录，但在本次不同臂条件下各有一份出现。
    // 只给尚未发布的重复后缀换新ID，保留符号与父子关系；已发布前缀不动。
    let prefix = base.region_merge_records.len();
    let previous_ids = history_ids.get_or_insert_with(|| {
        previous
            .region_merge_records
            .suffix(prefix)
            .map(|record| {
                #[cfg(test)]
                FOLD_HISTORY_ID_VISITS.set(FOLD_HISTORY_ID_VISITS.get() + 1);
                record.record_id
            })
            .collect()
    });
    let mut renamed = HashMap::new();
    let mut incoming_ids = Vec::with_capacity(next.region_merge_records.len() - prefix);
    for record in next.region_merge_records.suffix(prefix) {
        let mut id = record.record_id;
        if previous_ids.contains(&id) {
            id = *renamed.entry(id).or_insert_with(next_region_record);
        }
        incoming_ids.push(id);
    }
    if !renamed.is_empty() {
        next.region_merge_records.edit_occurrences(prefix, |record| {
            let id = renamed.get(&record.record_id).copied();
            let parent = record.parent_record.and_then(|parent| renamed.get(&parent).copied());
            if id.is_none() && parent.is_none() {
                return None;
            }
            let mut record = record.clone();
            record.record_id = id.unwrap_or(record.record_id);
            record.parent_record = parent.or(record.parent_record);
            Some(record)
        });
    }
    let (condition, union, prepared) = planned.publish_guards(solver);
    let id = next_region_record();
    let mut merged = base.clone();
    let owner = solver.new_logical_arm(base.region_arm);
    merged.region_arm = Some(owner);
    let result = solver.with_logical_arm(owner, |solver| {
        solver.with_transaction_condition(&union, |solver| {
            finish_prepared_region(
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
                Some(prepared),
            )
        })
    })?;
    assert!(matches!(result, RegionResult::Merged), "两个存活退出前沿必须保留");
    // 双臂汇合按累计侧、新侧、新根的顺序追加。成功后才更新索引。
    previous_ids.extend(incoming_ids);
    previous_ids.insert(id);
    cost::make_mut(&mut merged.local_state).speculative_access.as_mut().unwrap().guard = Some(union);
    Ok(merged)
}

/// 展开同一循环中尚未到达出口的独立片段，等待关系仍指向原臂槽位。
fn take_loop_continuation<'ir, B: BV>(work: &mut LoopWork<'ir, B>, state: &TaskState<B>) -> Option<LoopWork<'ir, B>> {
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
        continuations: ReadyFragments::new(state),
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
) -> Result<RegionResult, ExecError> {
    use smtlib::Exp::{And, Not, Var};
    let iterative = can_fold_iterations(state, base.region_execution.as_ref().unwrap().mode)
        && match region.join {
            RegionPoint::FunctionExit => true,
            RegionPoint::Instruction(pc) => matches!(frame.instrs.get(pc), Some(Instr::End)),
        };
    let expanded = iterative && crate::config::RegionOptions::current().loop_fold_shapes;
    let back_edges = if expanded {
        let summaries = state.region_effect_summaries.get().expect("循环分析必须已具有函数摘要");
        with_function_regions(frame, shared, summaries, true, |analysis| {
            loop_fold::back_edge_predecessors(analysis.cfg(), &region)
        })
    } else {
        HashSet::new()
    };
    let mut first_pmp_fold =
        super::stats::region_progress::enabled() && shared.symtab.to_str(frame.function_name) == "zpmpCheck";
    let mut exit_prefix = Vec::new();
    let mut exit_ids = None;
    let arm_start = solver.loop_arm_count();
    let root_branch = region.branch_pc;
    let root_region = region.clone();
    let remaining = base.region_execution.as_ref().unwrap().remaining.clone();
    let original_base = base.clone();
    let original_frame = frame.clone();
    let mut last_boundary = 0;
    let mut largest_round = 0;
    let mut continuation: Option<LocalFrame<'ir, B>> = None;
    let mut return_guard = None;
    let live_forks = stats::merge_timing::LiveForks::start();
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
        continuations: ReadyFragments::new(state),
        parent_arm: solver.current_logical_arm(),
        active_arm: None,
    });
    loop {
        if crate::config::RegionOptions::current().progress && diagnostics::enabled() {
            let suspended = pending
                .ancestors(frontier)
                .map(|work| {
                    let slots = work.arms.iter().map(Vec::len).sum::<usize>();
                    (1 - work.completed.min(1)).max(slots) + work.continuations.len()
                })
                .sum::<usize>();
            live_forks.set(suspended + exit_prefix.len() + usize::from(continuation.is_some()));
        }
        super::stats::memory_stats::poll(frame, solver);
        if pending.work(frontier).completed == 2 {
            let (mut work, parent) = pending.complete(frontier);
            if back_edges.contains(&work.target) && !back_edges.contains(&(work.original.pc + 1)) {
                work.arms.swap(0, 1);
            }
            let finishing_segment = parent.is_none() && continuation.is_some();
            let mut guard = work.base.local_state.speculative_access.as_ref().unwrap().guard.clone();
            if let Some(returned) = return_guard {
                guard = Some(match guard {
                    Some(parent) => And(Box::new(parent), Box::new(Var(returned))),
                    None => Var(returned),
                });
            }
            let owner = if finishing_segment {
                // 退出组暂时保留访问记录，最后连同继续片段交给父层或普通调度器。
                let owner = solver.new_logical_arm(work.parent_arm);
                work.original.region_execution = work.base.region_execution.clone();
                work.original.region_arm = Some(owner);
                let mut access = work.base.local_state.speculative_access.as_ref().unwrap().clone();
                access.guard = guard.clone();
                cost::make_mut(&mut work.original.local_state).speculative_access = Some(access);
                Some(owner)
            } else {
                work.parent_arm
            };
            // 子循环段已提交为完整条件保护的约束；汇合时也保留所属臂条件。
            let finish = |solver: &mut Solver<B>| {
                finish_arrivals(
                    work.record_id,
                    work.condition,
                    &work.region,
                    false,
                    parent.is_none() && original_frame.region_execution.is_none(),
                    &work.base,
                    work.arms,
                    &mut work.original,
                    state,
                    shared,
                    solver,
                    work.info,
                )
            };
            let finish_with_guard = |solver: &mut Solver<B>| match guard {
                Some(guard) => solver.with_transaction_condition(&guard, finish),
                None => finish(solver),
            };
            let result = match owner {
                Some(owner) => solver.with_logical_arm(owner, finish_with_guard),
                None => finish_with_guard(solver),
            }?;
            if let Some((parent, side)) = parent {
                frontier = parent;
                let parent = pending.work_mut(parent);
                assert_eq!(parent.completed, side, "调用栈组织者按两臂顺序收尾");
                match result {
                    RegionResult::Merged => {
                        promote_initials(&mut parent.base, &work.original, solver);
                        parent.arms[side].push(work.original);
                    }
                    RegionResult::Dead => {
                        solver.discard_logical_arm_effects(work.parent_arm.expect("挂起臂必须持有逻辑事务"));
                    }
                    RegionResult::Separate { .. } => {
                        for fragment in std::mem::take(&mut work.original.region_arrivals) {
                            promote_initials(&mut parent.base, &fragment, solver);
                            parent.arms[side].push(fragment);
                        }
                    }
                    RegionResult::Rejected
                    | RegionResult::Suspended
                    | RegionResult::GuardedExits
                    | RegionResult::VerifiedPrefix(_) => {
                        panic!("子循环汇合结果必须已经收尾")
                    }
                }
                if let Some(next) = take_loop_continuation(parent, state) {
                    frontier = pending.attach(frontier, side, next);
                } else {
                    parent.completed += 1;
                    parent.active_arm = None;
                }
            } else {
                if let Some(mut continued) = continuation.take() {
                    assert!(exit_prefix.is_empty(), "预算续配时累计出口须仍在循环依赖中");
                    let mut groups = match result {
                        RegionResult::Merged => vec![work.original],
                        RegionResult::Dead => Vec::new(),
                        RegionResult::Separate { .. } => std::mem::take(&mut work.original.region_arrivals),
                        _ => panic!("分段出口必须已经收尾"),
                    };
                    if original_frame.region_execution.is_none() {
                        // 普通调度器在继续 PC 投影这组的事件；此片段尚未到达真实循环出口。
                        let continuation_region =
                            Region { join: RegionPoint::Instruction(continued.pc), ..(*root_region).clone() };
                        record_projected_arrival(&mut continued, &original_base, &continuation_region, solver, info);
                    } else if !groups.is_empty() {
                        charge_fragment_growth(&original_base, 1)?;
                    }
                    groups.push(continued);
                    for group in &mut groups {
                        group.region_execution = original_frame.region_execution.clone();
                        group.speculation_mode = original_frame.speculation_mode;
                    }
                    frame.region_arrivals = groups;
                    return Ok(RegionResult::GuardedExits);
                }
                if let RegionResult::Separate { .. } = result {
                    if original_frame.region_execution.is_none() {
                        for exit in &mut exit_prefix {
                            record_projected_arrival(exit, &original_base, &root_region, solver, info);
                        }
                    }
                    work.original.region_arrivals.append(&mut exit_prefix);
                    for part in &mut work.original.region_arrivals {
                        part.region_execution = original_frame.region_execution.clone();
                        part.speculation_mode = original_frame.speculation_mode;
                    }
                    *frame = work.original;
                    return Ok(result);
                }
                if !exit_prefix.is_empty() {
                    // 折叠另开计划保存点，须在此前读取本循环层已提交的写入。
                    let loop_writes_memory = solver.transaction_has_memory_writes();
                    match result {
                        RegionResult::Merged => append_loop_exit(
                            &mut exit_prefix,
                            &mut exit_ids,
                            work.original,
                            solver,
                            |previous, next, ids, solver| {
                                fold_loop_exit(
                                    previous,
                                    next,
                                    ids,
                                    &original_base,
                                    &root_region,
                                    loop_writes_memory,
                                    state,
                                    shared,
                                    solver,
                                    info,
                                )
                            },
                        )?,
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
                        false,
                        restored.region_execution.is_none(),
                        &original_base,
                        [exit_prefix, Vec::new()],
                        &mut restored,
                        state,
                        shared,
                        solver,
                        info,
                    )?;
                    *frame = restored;
                    return Ok(result);
                }
                *frame = work.original;
                return Ok(result);
            }
            continue;
        }
        let completed_exits = pending.ancestors(frontier).count();
        let single_work = completed_exits == 1;
        let exit_spine = iterative
            && continuation.is_none()
            && pending.ancestors(frontier).all(|work| {
                work.completed == 1
                    && work.continuations.len() == 0
                    && work.arms[1].is_empty()
                    && work.arms[0].len() == 1
                    && work.arms[0].first().is_some_and(|arm| {
                        matches!(arm.instrs.get(arm.pc), Some(Instr::End)) && {
                            let access = arm.local_state.speculative_access.as_ref().unwrap();
                            !access.ordered_events || access.global_state || access.writes.modified_regs.is_empty()
                        }
                    })
            });
        let work = pending.work_mut(frontier);
        assert!(work.active_arm.is_none(), "前一逻辑臂必须先收尾");
        let owner = solver.new_logical_arm(work.parent_arm);
        work.active_arm = Some(owner);
        let reversed = back_edges.contains(&work.target) && !back_edges.contains(&(work.original.pc + 1));
        let first = (work.completed == 0) != reversed;
        let guard = if first { Var(work.condition) } else { Not(Box::new(Var(work.condition))) };
        let mut arm = branch_arm(&work.base, if first { work.target } else { work.original.pc + 1 }, guard, owner);
        let guard = arm.local_state.speculative_access.as_ref().unwrap().guard.clone().unwrap();
        let tx = solver.start_transaction_with_guard(Some(guard));
        if solver.with_logical_arm(owner, |solver| {
            advance_region_arm(
                tid, task_id, fraction, timeout, stop, sink, &mut arm, state, shared, solver, false, tx, work.info,
            )
        })? {
            if !arm.region_arrivals.is_empty() {
                let side = work.completed;
                let mut continuing = Vec::new();
                for part in std::mem::take(&mut arm.region_arrivals) {
                    if part.region_execution.as_ref().unwrap().pending_branch.is_some() {
                        continuing.push(part);
                    } else {
                        promote_initials(&mut work.base, &part, solver);
                        work.arms[side].push(part);
                    }
                }
                work.continuations.extend(continuing.into_iter());
                if let Some(next) = take_loop_continuation(work, state) {
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
                let access = arm.local_state.speculative_access.as_ref().unwrap();
                let loop_writes_memory = exit_spine && solver.transaction_has_memory_writes();
                let fold_writes =
                    !access.ordered_events || access.global_state || access.writes.modified_regs.is_empty();
                if iterative
                    && (single_work || expanded)
                    && exit_spine
                    && region.branch_pc == root_branch
                    && fold_writes
                    && ((expanded && arm.memory.ram_version().is_some()) || !loop_writes_memory)
                {
                    let children = pending.drain_spine(&mut frontier);
                    let work = pending.work_mut(frontier);
                    let exits = std::iter::once(work.arms[0].pop().expect("根退出前沿必须存活")).chain(
                        children.into_iter().map(|mut child| child.arms[0].pop().expect("退出脊柱必须已有存活前沿")),
                    );
                    for exit in exits {
                        append_loop_exit(
                            &mut exit_prefix,
                            &mut exit_ids,
                            exit,
                            solver,
                            |previous, next, ids, solver| {
                                fold_loop_exit(
                                    previous,
                                    next,
                                    ids,
                                    &original_base,
                                    &root_region,
                                    loop_writes_memory,
                                    state,
                                    shared,
                                    solver,
                                    info,
                                )
                            },
                        )?;
                    }
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
                    let owner = solver.new_logical_arm(original_base.region_arm);
                    next.region_arm = Some(owner);
                    let result = solver.with_logical_arm(owner, |solver| {
                        solver.with_transaction_condition(&guard, |solver| {
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
                        })
                    })?;
                    assert!(matches!(result, RegionResult::Merged));
                    if crate::config::RegionOptions::current().prefix_compact {
                        loop_fold::compact_frontiers(
                            &mut exit_prefix,
                            &mut next,
                            &mut exit_ids,
                            &original_base,
                            arm_start,
                            solver,
                            info,
                        );
                    }
                    #[cfg(test)]
                    loop_fold::sample_frontiers(&exit_prefix, &next, &exit_ids, solver);
                    solver.compact_region_query_prefix();
                    // 返回选择器已保存完整到达条件。下一轮引用它的补集，避免每个事件
                    // 复制前面所有轮次的守卫树。
                    cost::make_mut(&mut next.local_state).speculative_access.as_mut().unwrap().guard =
                        Some(Not(Box::new(Var(returned))));
                    let id = NEXT_RECORD
                        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
                        .expect("合并记录编号溢出");
                    if super::stats::region_progress::enabled()
                        && (LOGGED_ITERATION_FOLDS.fetch_add(1, Ordering::Relaxed) < 2048 || first_pmp_fold)
                    {
                        first_pmp_fold = false;
                        let _log = crate::executor::stats::path_account::Scope::enter(
                            crate::executor::stats::path_account::Category::Log,
                        );
                        eprintln!(
                            "{}",
                            serde_json::json!({"kind":"loop_iteration_fold","task":task_id.as_usize(),"root_attempt":diagnostics::root_attempt(),
                            "function":diagnostics::name_string(original_frame.function_name,&shared.symtab),
                            "pc":root_branch,"call_instance":original_frame.local_state.call_instance,
                            "steps_since_budget_renewal":used,"step_budget_unlimited":remaining.is_none(),"logical_frontiers":exit_prefix.len() + 1,
                            "returned_records":exit_prefix.iter().map(|exit| exit.region_merge_records.len()).sum::<usize>(),
                            "continuation_records":next.region_merge_records.len(),
                            "savepoint_depth":solver.transaction_depth()})
                        );
                    }
                    // 写入回边本身不续配。只有本轮已交付新的退出域才允许下一轮继续。
                    if !next.local_state.speculative_access.as_ref().unwrap().writes.modified_regs.is_empty() {
                        if let (Some(remaining), Some(budget)) = (&remaining, state.region_step_budget()) {
                            remaining.store(budget, Ordering::Relaxed);
                        }
                    }
                    let parent_arm = next.region_arm;
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
                        continuations: ReadyFragments::new(state),
                        parent_arm,
                        active_arm: None,
                    };
                    // 预算由实际回边更新；此处只收敛前沿，避免半轮重复授予预算。
                    last_boundary = 0;
                    largest_round = 0;
                    continue;
                }
                if !exit_prefix.is_empty() && !(expanded && region.branch_pc != root_branch) {
                    return Err(reject(&arm, SpeculativeRejectReason::StateEffect));
                }
                if exit_prefix.is_empty()
                    && exit_spine
                    && region.branch_pc == root_branch
                    && fold_writes
                    && !loop_writes_memory
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
                    if diagnostics::enabled() {
                        let _log = crate::executor::stats::path_account::Scope::enter(
                            crate::executor::stats::path_account::Category::Log,
                        );
                        eprintln!(
                            "{}",
                            serde_json::json!({"kind":"loop_segment","function":diagnostics::name_string(original_frame.function_name,&shared.symtab),"pc":root_branch,"call_instance":original_frame.local_state.call_instance,"steps":used,"remaining":remaining.as_ref().map(|remaining| remaining.load(Ordering::Relaxed)),"completed_exits":completed_exits,"continuation_pc":arm.pc})
                        );
                    }
                    arm.pending_retry_operand = Some((arm.pc, Val::Symbolic(condition)));
                    continuation = Some(arm);
                    return_guard = Some(returned);
                    // 继续臂单独保存；当前层只折叠已完成出口，两类片段在本层边界一起交付。
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
                        continuations: ReadyFragments::new(state),
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
                promote_initials(&mut work.base, &arm, solver);
                work.arms[work.completed].push(arm);
                work.completed += 1;
                work.active_arm = None;
            }
        } else {
            if crate::config::RegionOptions::current().arm_error_leaf || state.observe_assertion_failures {
                solver.discard_logical_arm_effects(owner);
            }
            work.completed += 1;
            work.active_arm = None;
        }
    }
}

/// 候选重试从当前操作数快照开始。只有真实 Jump 使用控制流的公共后支配点。
#[allow(clippy::too_many_arguments)]
pub(super) fn concrete_consumer<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
    retry: ConsumerRetry,
    info: SourceLoc,
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
) -> Result<Option<bool>, ExecError> {
    let mode = policy(frame, state, info);
    if mode == MergeMode::Off
        || !state.execution_limits.as_ref().is_some_and(|limits| limits.merge_concrete_values)
        || frame.execution_limit_state.has_sampled_branch()
    {
        return Ok(None);
    }
    let pc = frame.pc;
    let nested = frame.region_execution.is_some();
    let depth = frame.region_execution.as_ref().map_or(1, |parent| parent.depth + 1);
    if crate::config::RegionOptions::current().merge_depth_limit().is_some_and(|limit| depth > limit) {
        if nested {
            return Err(reject(frame, SpeculativeRejectReason::NestingLimit));
        }
        return Ok(None);
    }
    let region = match &frame.instrs[pc] {
        Instr::End => return Ok(None),
        Instr::Jump(..) => {
            let global = state.execution_limits.as_ref().is_some_and(|limits| limits.region_global_state);
            let summaries = state.region_effect_summaries.get_or_init(|| function_effect_summaries(shared, global));
            let candidate = match region(frame, shared, summaries, false) {
                Ok(candidate) if !candidate.has_back_edge => candidate,
                Ok(_) if nested => return Err(reject(frame, SpeculativeRejectReason::HasBackEdge)),
                Err(error) if nested => return Err(error),
                _ => return Ok(None),
            };
            let mut candidate = (*candidate).clone();
            candidate.nodes.insert(pc);
            Arc::new(candidate)
        }
        _ => Arc::new(Region {
            branch_pc: pc,
            has_back_edge: false,
            join: RegionPoint::Instruction(pc + 1),
            nodes: [pc].into_iter().collect(),
            kind: crate::ir::regions::RegionKind::Reconvergent,
            local_variables: Default::default(),
        }),
    };
    let record_start = frame.region_merge_records.len();
    let mut pending_errors = ArmErrorSink::new();
    let tx = solver.start_transaction();
    let mut candidate = frame.clone();
    candidate.pending_retry_operand.get_or_insert((pc, Val::Unit));
    let condition = match &retry {
        ConsumerRetry::Choice(guard) => *guard,
        ConsumerRetry::Operand { guards: [selected, _], .. } => solver.define_const(selected.clone(), info),
    };
    let can_split_locally = nested
        && crate::config::RegionOptions::current().partial_commit_retry_operand
        && !matches!(&retry, ConsumerRetry::Operand { split: Some(_), .. });
    let mut result = match execute_region(
        condition,
        pc,
        pc,
        None,
        Some(retry),
        region,
        depth,
        mode,
        tid,
        task_id,
        fraction,
        timeout,
        stop,
        &pending_errors,
        &mut candidate,
        state,
        shared,
        solver,
        info,
    ) {
        Ok(output) => output,
        Err(error) => {
            solver.rollback_transaction(tx);
            if can_split_locally && error.rejection_reason() == Some(SpeculativeRejectReason::RetryOperand) {
                // 原来的具体化入口仍持有完整的互补守卫和操作数。
                return Ok(None);
            }
            if nested || !matches!(error, ExecError::SpeculativeReject { .. }) {
                return Err(error);
            }
            // 不可推演效应和控制流屏障沿用原来的执行入口。
            return Ok(None);
        }
    };
    if matches!(result, RegionResult::Separate { reason: SpeculativeRejectReason::IncompatibleState, .. }) {
        match consumer_continuation::try_join_after_last_use(
            condition,
            info,
            tid,
            task_id,
            fraction,
            timeout,
            stop,
            &pending_errors,
            &mut candidate,
            state,
            shared,
            solver,
        ) {
            Ok(Some(joined)) => result = joined,
            Ok(None) => (),
            Err(error) => {
                solver.rollback_transaction(tx);
                return Err(error);
            }
        }
    }
    if let RegionResult::VerifiedPrefix(error) = &result {
        record_local_rejection(frame, state, shared, error);
        if let Err(error) = prefix_commit::certify_groups(&mut candidate, solver, info, timeout) {
            solver.rollback_transaction(tx);
            if !nested && matches!(error, ExecError::SpeculativeReject { .. }) {
                return Ok(None);
            }
            return Err(error);
        }
    }
    let dead_prefix = matches!(result, RegionResult::VerifiedPrefix(_)) && candidate.region_arrivals.is_empty();
    *frame = candidate;
    delivery::finish(
        &result,
        frame,
        record_start,
        &mut pending_errors,
        task_id,
        fraction,
        stop,
        sink,
        state,
        shared,
        solver,
        info,
    );
    match result {
        RegionResult::Merged => {
            frame.pending_retry_operand = None;
            let local = cost::make_mut(&mut frame.local_state);
            local.expression_values.clear();
            local.expression_retry_operands = None;
            Ok(Some(true))
        }
        RegionResult::VerifiedPrefix(_) => Ok(Some(!dead_prefix)),
        RegionResult::Separate { .. } => Ok(Some(true)),
        RegionResult::Dead => Ok(Some(false)),
        _ => panic!("具体消费者区域必须完成或全死"),
    }
}
