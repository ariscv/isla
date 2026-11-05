//! 区域推演只调用真实执行循环；此模块负责边界、事务与状态合并。
use super::*;
use crate::config::MergeMode;
use crate::ir::regions::{FunctionRegions, Region, RegionOptions, RegionPoint, RegionRejection};
use crate::primop::{self as effects, Effect};

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
    pub pure_definitions: Vec<(u32, u32)>,
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

/// 主迹的寄存器读取只保证前置状态/访问足迹可信；需要逐条精确读写顺序时不可信。
/// 单臂读取保留其条件，后续记录输出可据此恢复精确路径。
#[derive(Clone, Debug)]
pub struct GuardedRegisterRead<B> {
    pub register: Name,
    pub accessor: Vec<Accessor>,
    pub value: Val<B>,
    pub guard: smtlib::Exp<Sym>,
}

#[derive(Clone, Debug)]
pub struct RegionMergeRecord<B> {
    pub function: Name,
    pub branch_pc: usize,
    pub join: RegionPoint,
    pub condition: Sym,
    pub source_loc: SourceLoc,
    pub depth: usize,
    /// 两臂都死亡时没有存活合并值，但剪枝本身仍是一次成功提交。
    pub dead: bool,
    /// 合并值中的符号；最外层提交后展开 DefineConst 依赖，得到自由输入。
    pub value_symbols: HashSet<Sym>,
    pub input_symbols: HashSet<Sym>,
    pure_definitions: Vec<(u32, u32)>,
    pub single_arm_reads: Vec<GuardedRegisterRead<B>>,
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
    state
        .execution_limits
        .as_ref()
        .map_or(MergeMode::Off, |limits| limits.merge_mode(frame.function_name, info, inherited))
}

/// 本地校验每一步的真实栈深度；调用不会重新授予入口层的写许可。
pub(super) fn step<B: BV>(frame: &mut LocalFrame<B>) -> Result<bool, ExecError> {
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
    let log = frame.local_state.speculative_access.as_mut().expect("区域推演必须启用访问记录");
    log.function = frame.function_name;
    log.pc = frame.pc;
    log.location = location;
    log.writes_allowed = depth == execution.write_depth;
    Ok(false)
}

fn constraint_unary<B: BV>(f: primop::Unary<B>) -> bool {
    std::ptr::fn_addr_eq(f, primop::assume::<B> as primop::Unary<B>)
}
fn constraint_binary<B: BV>(f: primop::Binary<B>) -> bool {
    [primop::optimistic_assert::<B> as primop::Binary<B>, primop::pessimistic_assert::<B> as primop::Binary<B>]
        .iter()
        .any(|assertion| std::ptr::fn_addr_eq(f, *assertion))
}

/// 效应等级与静态拒绝证据分别保存：寄存器读可以推演，带条件约束也可重放。
/// 因此 C4 的 WritesState（例如 assume）不必然带有静态拒绝证据。
#[derive(Clone, Copy, Debug)]
pub(super) struct FunctionEffect {
    pub effect: Effect,
    rejection: Option<CachedReject>,
}
impl FunctionEffect {
    fn join(&mut self, other: Self) -> bool {
        let changed = other.effect > self.effect || (self.rejection.is_none() && other.rejection.is_some());
        if other.rejection.is_some() && (other.effect > self.effect || self.rejection.is_none()) {
            self.rejection = other.rejection;
        }
        self.effect = self.effect.max(other.effect);
        changed
    }
}

/// 已加载的原语调用通常已改写为 Primop；特殊内建仍保留 Call 形态。
fn direct_effect<B: BV>(instr: &Instr<Name, B>, shared: &SharedState<B>) -> Effect {
    match instr {
        Instr::PrimopUnary(_, f, _, _) => effects::unary_effect(*f).expect("一元原语必须分类"),
        Instr::PrimopBinary(_, f, _, _, _) => effects::binary_effect(*f).expect("二元原语必须分类"),
        Instr::PrimopVariadic(_, f, _, _) => effects::variadic_effect(*f).expect("多元原语必须分类"),
        Instr::PrimopReset(_, _, effect, _) => *effect,
        Instr::Call(_, _, function, _, _) if !shared.functions.contains_key(function) => match *function {
            REG_DEREF | READ_REGISTER_FROM_VECTOR => Effect::ReadsState,
            WRITE_REGISTER_FROM_VECTOR => Effect::WritesState,
            INTERNAL_VECTOR_INIT | INTERNAL_VECTOR_UPDATE | ITE_PHI => Effect::Pure,
            _ => match shared.externs.get(function) {
                Some((_, _, name)) => effects::effect(name).unwrap_or(Effect::MayFork),
                None => effects::effect(&zencode::decode(shared.symtab.to_str(*function))).unwrap_or(Effect::MayFork),
            },
        },
        _ => Effect::Pure,
    }
}

/// 从格底 Pure 开始，按调用图的 SCC 逆拓扑序处理；分量内迭代到最小不动点。
/// 递归边只传播已知效应，不凭空增加效应；实际递归仍受共享推演步数预算约束。
pub(super) fn function_effect_summaries<B: BV>(shared: &SharedState<B>) -> HashMap<Name, FunctionEffect> {
    let mut graph = petgraph::graph::DiGraph::<Name, ()>::new();
    let nodes: HashMap<_, _> = shared.functions.keys().map(|function| (*function, graph.add_node(*function))).collect();
    let mut summaries = HashMap::new();
    for (function, (params, _, body)) in &shared.functions {
        let locals: HashSet<_> = params
            .iter()
            .map(|(name, _)| *name)
            .chain([RETURN])
            .chain(body.iter().filter_map(|instr| match instr {
                Instr::Decl(name, ..) | Instr::Init(name, ..) => Some(*name),
                _ => None,
            }))
            .collect();
        let mut summary = FunctionEffect { effect: Effect::Pure, rejection: None };
        for (pc, instr) in body.iter().enumerate() {
            let mut effect = direct_effect(instr, shared);
            let mut rejection = if matches!(instr, Instr::Call(_, _, callee, _, _) if shared.functions.contains_key(callee))
            {
                None
            } else {
                instruction_effect(*function, pc, instr, shared, &HashMap::new())
            };
            let mut reads = HashSet::new();
            let mut destination = None;
            match instr {
                Instr::Copy(loc, exp, _) => {
                    destination = Some(loc);
                    exp.collect_ids(&mut reads);
                }
                Instr::Init(_, _, exp, _) | Instr::Jump(exp, _, _) => exp.collect_ids(&mut reads),
                Instr::PrimopUnary(loc, _, exp, _) => {
                    destination = Some(loc);
                    exp.collect_ids(&mut reads);
                }
                Instr::PrimopBinary(loc, _, a, b, _) => {
                    destination = Some(loc);
                    a.collect_ids(&mut reads);
                    b.collect_ids(&mut reads);
                }
                Instr::PrimopVariadic(loc, _, args, _) | Instr::Call(loc, _, _, args, _) => {
                    destination = Some(loc);
                    for arg in args {
                        arg.collect_ids(&mut reads);
                    }
                }
                Instr::PrimopReset(loc, ..) => destination = Some(loc),
                Instr::Monomorphize(name, ..) => {
                    reads.insert(*name);
                }
                _ => (),
            }
            if reads.iter().any(|name| !locals.contains(name) && !shared.type_info.enum_members.contains_key(name)) {
                effect = effect.max(Effect::ReadsState);
            }
            if matches!(instr, Instr::Call(_, _, WRITE_REGISTER_FROM_VECTOR, _, _))
                || destination.map_or(false, |loc| !locals.contains(&loc.id()) || matches!(loc, Loc::Addr(_)))
            {
                effect = effect.max(Effect::WritesState);
                rejection = Some(CachedReject {
                    reason: SpeculativeRejectReason::CalleeStateWrite,
                    function: *function,
                    pc,
                    location: stats::instr_source_loc(instr).unwrap_or(SourceLoc::unknown()),
                });
            }
            summary.join(FunctionEffect { effect, rejection });
            if let Instr::Call(_, _, callee, _, _) = instr {
                if let Some(callee) = nodes.get(callee) {
                    graph.update_edge(nodes[function], *callee, ());
                }
            }
        }
        summaries.insert(*function, summary);
    }
    // kosaraju_scc 返回汇点优先的逆拓扑序，因此分量外的被调函数已收敛。
    for component in petgraph::algo::kosaraju_scc(&graph) {
        loop {
            let mut changed = false;
            for node in &component {
                let function = graph[*node];
                for callee in graph.neighbors(*node) {
                    let effect = summaries[&graph[callee]];
                    changed |= summaries.get_mut(&function).unwrap().join(effect);
                }
            }
            if !changed {
                break;
            }
        }
    }
    summaries
}

fn instruction_effect<B: BV>(
    function_name: Name,
    pc: usize,
    instr: &Instr<Name, B>,
    shared: &SharedState<B>,
    summaries: &HashMap<Name, FunctionEffect>,
) -> Option<CachedReject> {
    match instr {
        Instr::PrimopUnary(_, f, _, _) if constraint_unary(*f) => return None,
        Instr::PrimopBinary(_, f, _, _, _) if constraint_binary(*f) => return None,
        Instr::Call(_, _, function, _, _) if shared.functions.contains_key(function) => {
            return summaries.get(function).expect("IR 函数必须有收敛的效应摘要").rejection;
        }
        Instr::Call(
            _,
            _,
            REG_DEREF
            | READ_REGISTER_FROM_VECTOR
            | WRITE_REGISTER_FROM_VECTOR
            | INTERNAL_VECTOR_INIT
            | INTERNAL_VECTOR_UPDATE
            | ITE_PHI,
            _,
            _,
        ) => return None,
        _ => (),
    }
    (direct_effect(instr, shared) != Effect::Pure).then(|| CachedReject {
        reason: SpeculativeRejectReason::StateEffect,
        function: function_name,
        pc,
        location: stats::instr_source_loc(instr).unwrap_or(SourceLoc::unknown()),
    })
}

pub(super) fn preflight<B: BV>(
    frame: &LocalFrame<B>,
    state: &TaskState<B>,
    shared: &SharedState<B>,
) -> Result<(), ExecError> {
    if frame.region_execution.is_none() {
        return Ok(());
    }
    if let Some(rejection) = instruction_effect(
        frame.function_name,
        frame.pc,
        &frame.instrs[frame.pc],
        shared,
        state.region_effect_summaries.get_or_init(|| function_effect_summaries(shared)),
    ) {
        return Err(rejection.error());
    }
    Ok(())
}

#[derive(Clone, Copy, Debug)]
pub(super) struct CachedReject {
    pub reason: SpeculativeRejectReason,
    pub function: Name,
    pub pc: usize,
    pub location: SourceLoc,
}
impl CachedReject {
    fn error(self) -> ExecError {
        ExecError::SpeculativeReject {
            reason: self.reason,
            function: self.function,
            pc: self.pc,
            location: self.location,
        }
    }
}

fn region<'ir, B: BV>(frame: &LocalFrame<'ir, B>, shared: &SharedState<'ir, B>) -> Result<Arc<Region>, ExecError> {
    let mut cache = shared.function_regions.lock().unwrap();
    let analysis = cache.entry(frame.function_name).or_insert_with(|| {
        FunctionRegions::with_options(
            frame.instrs,
            RegionOptions {
                have_exception: Some(shared.symtab.lookup(shared.symtab.to_str(HAVE_EXCEPTION))),
                terminal_calls: &[],
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
    let candidate = if frame.execution_limit_state.has_sampled_branch() {
        Err(reject(frame, SpeculativeRejectReason::SamplingState))
    } else {
        match cached {
            Some(cached) => {
                shared.execution_stats.merge_cache_hit();
                Err(cached.error())
            }
            None => region(frame, shared).and_then(|region| {
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
            }),
        }
    };
    let result = match candidate {
        Err(error) => {
            if let ExecError::SpeculativeReject { reason, function, pc, location } = error {
                if reason != SpeculativeRejectReason::SamplingState {
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
                        solver.commit_transaction();
                        if !nested {
                            let mut events = solver.trace().to_vec();
                            let fresh: HashSet<_> = events
                                .iter()
                                .filter_map(|event| match event {
                                    Event::Smt(Def::DeclareConst(symbol, _), _, _) => Some(*symbol),
                                    _ => None,
                                })
                                .collect();
                            // pow_int 等纯计算用 DeclareConst + 等式共享中间结果；按 I1 协议
                            // 解开 guard 后把定义依赖交给已有 EventReferences 展开。
                            let pure_ranges: Vec<_> = frame
                                .region_merge_records
                                .iter()
                                .flat_map(|record| record.pure_definitions.iter().copied())
                                .collect();
                            let mut equations = Vec::new();
                            let mut derived = HashSet::new();
                            for event in &events {
                                if let Event::Smt(Def::Assert(exp), attributes, location) = event {
                                    let mut exp = exp;
                                    while let smtlib::Exp::Or(left, right) = exp {
                                        if matches!(left.as_ref(), smtlib::Exp::Not(_)) {
                                            exp = right;
                                        } else {
                                            break;
                                        }
                                    }
                                    if let smtlib::Exp::Eq(left, right) = exp {
                                        if let smtlib::Exp::Var(symbol) = left.as_ref() {
                                            if fresh.contains(symbol)
                                                && pure_ranges
                                                    .iter()
                                                    .any(|(start, end)| *start < symbol.id && symbol.id < *end)
                                                && !right.variables().contains(symbol)
                                            {
                                                derived.insert(*symbol);
                                                equations.push(Event::Smt(
                                                    Def::DefineConst(*symbol, right.as_ref().clone()),
                                                    *attributes,
                                                    *location,
                                                ));
                                            }
                                        }
                                    }
                                }
                            }
                            events.extend(equations.iter());
                            let references = crate::simplify::EventReferences::from_events(&events);
                            let declared: HashSet<_> = events
                                .iter()
                                .filter_map(|event| match event {
                                    Event::Smt(Def::DeclareConst(symbol, _), _, _) => Some(*symbol),
                                    _ => None,
                                })
                                .collect();
                            for record in &mut frame.region_merge_records {
                                record.input_symbols = record
                                    .value_symbols
                                    .iter()
                                    .flat_map(|symbol| references.dependencies(*symbol))
                                    .filter(|symbol| declared.contains(symbol) && !derived.contains(symbol))
                                    .collect();
                            }
                            // 只在最外层提交后发布本次新增记录，内层回滚不会留下幽灵记录。
                            emit_records(&frame.region_merge_records[record_start..], task_id, shared, solver);
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
        Err(error @ ExecError::SpeculativeReject { .. }) => {
            if let ExecError::SpeculativeReject { reason, .. } = &error {
                shared.execution_stats.merge_rejected(key.0, key.1, &error);
                state.speculation_stats.record_reject(*reason);
                shared.execution_stats.rule_finished(rule, Some(*reason));
            }
            shared.execution_stats.merge_finished(false);
            if mode == MergeMode::Force {
                speculation::force_failure(frame, state, shared, info, &error);
            }
            if nested {
                Err(error)
            } else {
                Ok(RegionResult::Rejected)
            }
        }
        Err(error) => {
            shared.execution_stats.merge_finished(false);
            shared.execution_stats.rule_finished(rule, Some(SpeculativeRejectReason::IncompatibleState));
            Err(error)
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
        base.local_state.speculative_access = Some(AccessLog {
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
            pure_definitions: Vec::new(),
        });
    }
    let mut arms = Vec::new();
    for (pc, guard) in [(target, Var(condition)), (frame.pc + 1, Not(Box::new(Var(condition))))] {
        let tx = solver.start_transaction_with_guard(Some(guard.clone()));
        let mut arm = base.clone();
        arm.pc = pc;
        let access = arm.local_state.speculative_access.as_mut().unwrap();
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
                solver.commit_transaction();
                // 首臂惰性初始化的前置寄存器在另臂复用；无读事件的提升不扩大足迹。
                let access = arm.local_state.speculative_access.as_ref().unwrap();
                base.local_state.speculative_access.as_mut().unwrap().published_reads = access.published_reads.clone();
                for (reg, initial) in &access.initial_registers {
                    if base.regs().get_last_if_initialized(*reg).is_none() {
                        base.regs_mut().assign(*reg, initial.clone(), shared);
                    }
                }
                for ((scope, function, name), value) in &access.initial_variables {
                    if *scope == base.local_state.speculative_access.as_ref().unwrap().call_scope
                        && *function == base.function_name
                        && matches!(base.vars().get(name), Some(UVal::Uninit(_)))
                    {
                        base.vars_mut().insert(*name, UVal::Init(value.clone()));
                    }
                }
                for (name, value) in &access.initial_lets {
                    if matches!(base.lets().get(name), Some(UVal::Uninit(_))) {
                        base.lets_mut().insert(*name, UVal::Init(value.clone()));
                    }
                }
                arms.push(Some(arm));
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
    let right = arms.pop().unwrap();
    let left = arms.pop().unwrap();
    let mut merged = match (left, right) {
        (None, None) => {
            frame.region_merge_records.push(RegionMergeRecord {
                function: frame.function_name,
                branch_pc: region.branch_pc,
                join: region.join,
                condition,
                source_loc: info,
                depth,
                dead: true,
                value_symbols: HashSet::from([condition]),
                input_symbols: HashSet::new(),
                pure_definitions: Vec::new(),
                single_arm_reads: Vec::new(),
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
                function: frame.function_name,
                branch_pc: region.branch_pc,
                join: region.join,
                condition,
                source_loc: info,
                depth,
                dead: false,
                value_symbols: HashSet::new(),
                input_symbols: HashSet::new(),
                pure_definitions: Vec::new(),
                single_arm_reads,
            });
            arm
        }
        (Some(left), Some(right)) => merge_states(condition, &base, left, right, &region, state, shared, solver, info)?,
    };
    let record = merged.region_merge_records.last_mut().expect("成功合并必须有记录");
    record.pure_definitions = merged.local_state.speculative_access.as_ref().unwrap().pure_definitions.clone();
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
    merged.local_state.speculative_access.as_mut().unwrap().guard =
        frame.local_state.speculative_access.as_ref().and_then(|access| access.guard.clone());
    merged.region_execution = parent;
    merged.speculation_mode = frame.speculation_mode;
    if merged.region_execution.is_none() {
        // 仅前置状态/访问足迹可信，需要逐条精确读写顺序时不可信。
        // 读取在真实读取处缓冲，提交时按并集发布；此处补发以 ITE 保留原值的条件写入。
        let access = merged.local_state.speculative_access.take().unwrap();
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

#[allow(clippy::too_many_arguments)]
fn merge_states<'ir, B: BV>(
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
        let names: HashSet<_> = a.keys().chain(b.keys()).copied().collect();
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
            let value =
                crate::primop_util::merge_val(condition, &a, &b, solver, info).map_err(|error| match error {
                    ExecError::Smt(_) | ExecError::Timeout => error,
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
    for reg in lhs.writes.read_regs.union(&rhs.writes.read_regs).chain(registers.iter()) {
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
            crate::primop_util::merge_val(
                condition,
                a.or(initial.as_ref()).unwrap(),
                b.or(initial.as_ref()).unwrap(),
                solver,
                info,
            )
            .map_err(|_| incompatible())?
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
    access.pure_definitions.extend(&rhs.pure_definitions);
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
    merged.local_state.speculative_access = Some(access);
    merged.pc = left.pc;
    let prefix = base.region_merge_records.len();
    merged.region_merge_records.extend(left.region_merge_records[prefix..].iter().cloned());
    merged.region_merge_records.extend(right.region_merge_records[prefix..].iter().cloned());
    merged.region_merge_records.push(RegionMergeRecord {
        function: base.function_name,
        branch_pc: region.branch_pc,
        join: region.join,
        condition,
        source_loc: info,
        depth: base.region_execution.as_ref().unwrap().depth,
        dead: false,
        value_symbols: HashSet::new(),
        input_symbols: HashSet::new(),
        pure_definitions: Vec::new(),
        single_arm_reads,
    });
    Ok(merged)
}

/// 执行前只校验显式 Force 命中的结构；调用方负责配置名称、源码范围和哈希校验。
pub fn validate_force_regions<B: BV>(shared: &SharedState<B>, limits: &ExecutionLimits) -> Result<(), String> {
    for (function, (_, _, body)) in &shared.functions {
        for (pc, instr) in body.iter().enumerate() {
            if let Instr::Jump(_, _, info) = instr {
                if limits.merge_mode(*function, *info, None) == MergeMode::Force {
                    let mut cache = shared.function_regions.lock().unwrap();
                    let regions = cache.entry(*function).or_insert_with(|| {
                        FunctionRegions::new(body, shared.symtab.lookup(shared.symtab.to_str(HAVE_EXCEPTION)))
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

/// 给纯原语生成的声明划定符号区间，区分定义等式和 assume 对已有输入的约束。
/// fresh 只预留编号，不声明变量；因此不会改变 SMT 状态，也无需新的求解器接口。
pub(super) fn evaluate_primop<'ir, B: BV>(
    frame: &mut LocalFrame<'ir, B>,
    solver: &mut Solver<B>,
    effect: Effect,
    evaluate: impl FnOnce(&mut Solver<B>, &mut LocalFrame<'ir, B>) -> Result<Val<B>, ExecError>,
) -> Result<Val<B>, ExecError> {
    let start = if frame.region_execution.is_some() && effect == Effect::Pure { Some(solver.fresh()) } else { None };
    let result = evaluate(solver, frame);
    if let Some(start) = start {
        let end = solver.fresh();
        frame.local_state.speculative_access.as_mut().unwrap().pure_definitions.push((start.id, end.id));
    }
    result
}

/// 进程内唯一写端：先完整序列化，再持锁追加整行；不依赖进程退出时析构刷新。
/// 两个入口共用真实执行器，因此环境变量在两处均生效。
fn emit_records<B: BV>(records: &[RegionMergeRecord<B>], task_id: TaskId, shared: &SharedState<B>, solver: &Solver<B>) {
    use serde_json::json;
    use std::io::Write;
    static OUTPUT: std::sync::OnceLock<Option<Mutex<std::fs::File>>> = std::sync::OnceLock::new();
    static NEXT_RECORD: AtomicUsize = AtomicUsize::new(0);
    let output = OUTPUT.get_or_init(|| {
        std::env::var_os("ISLA_MERGE_RECORDS").map(|path| {
            Mutex::new(
                std::fs::OpenOptions::new().create(true).append(true).open(path).expect("打开 ISLA_MERGE_RECORDS 失败"),
            )
        })
    });
    let Some(output) = output else { return };
    let types: HashMap<_, _> = solver
        .trace()
        .to_vec()
        .iter()
        .filter_map(|event| match event {
            Event::Smt(Def::DeclareConst(symbol, ty), _, _) => Some((*symbol, ty.clone())),
            _ => None,
        })
        .collect();
    fn type_json(ty: &smtlib::Ty, symtab: &Symtab) -> serde_json::Value {
        match ty {
            smtlib::Ty::Bool => json!({"kind":"bool"}),
            smtlib::Ty::BitVec(width) => json!({"kind":"bitvector", "width":width}),
            smtlib::Ty::Enum(id) => json!({"kind":"enum", "name":zencode::decode(symtab.to_str(id.to_name()))}),
            smtlib::Ty::Array(domain, range) => {
                json!({"kind":"array", "domain":type_json(domain, symtab), "range":type_json(range, symtab)})
            }
            smtlib::Ty::Float(exponent, significand) => {
                json!({"kind":"float", "exponent":exponent, "significand":significand})
            }
            smtlib::Ty::RoundingMode => json!({"kind":"rounding_mode"}),
        }
    }
    let symbol_json = |symbol: Sym, ty: &smtlib::Ty| {
        json!({
            "name":format!("v{}", symbol.id), "smt_id":symbol.id, "type":type_json(ty, &shared.symtab)
        })
    };
    for record in records {
        let mut inputs: Vec<_> = record.input_symbols.iter().copied().collect();
        inputs.sort_by_key(|symbol| symbol.id);
        let inputs: Vec<_> = inputs
            .into_iter()
            .map(|symbol| symbol_json(symbol, types.get(&symbol).expect("自由输入必须有声明类型")))
            .collect();
        let reads: Vec<_> = record
            .single_arm_reads
            .iter()
            .map(|read| {
                let mut symbols: Vec<_> = read.guard.variables().into_iter().collect();
                symbols.sort_by_key(|symbol| symbol.id);
                let symbols: Vec<_> =
                    symbols.into_iter().map(|symbol| symbol_json(symbol, &smtlib::Ty::Bool)).collect();
                let accessor: Vec<_> =
                    read.accessor.iter().map(|accessor| accessor.to_string(&shared.symtab)).collect();
                // 复用现有 SMT-LIB 输出器，变量名与记录中的 vN 一致，不能使用 Z3 的 k!N 内部名。
                let event = Event::<B>::Smt(Def::Assert(read.guard.clone()), DefAttrs::default(), record.source_loc);
                let mut expression = Vec::new();
                crate::simplify::write_events_with_opts(
                    &mut expression,
                    &[event],
                    shared,
                    &crate::simplify::WriteOpts::smtlib(),
                )
                .expect("保护条件必须可写为 SMT-LIB");
                let expression = String::from_utf8(expression).expect("SMT-LIB 必须是 UTF-8");
                let expression = expression.trim().strip_prefix("(assert ").unwrap().strip_suffix(')').unwrap();
                json!({"register":zencode::decode(shared.symtab.to_str(read.register)), "accessor":accessor,
                "value":read.value.to_string(shared), "guard":{"expression":expression, "symbols":symbols}})
            })
            .collect();
        let join = match record.join {
            RegionPoint::Instruction(pc) => json!({"instruction":pc}),
            RegionPoint::FunctionExit => json!({"function_exit":true}),
        };
        let record_id = NEXT_RECORD
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .expect("合并记录编号溢出");
        let value = json!({"schema_version":1, "record_id":record_id, "task_id":task_id.as_usize(),
            "function":zencode::decode(shared.symtab.to_str(record.function)), "branch_pc":record.branch_pc, "join":join,
            "source_loc":record.source_loc, "location":record.source_loc.location_string(shared.symtab.files()),
            "condition":symbol_json(record.condition, &smtlib::Ty::Bool), "input_symbols":inputs,
            "single_arm_reads":reads, "depth":record.depth, "outcome":if record.dead { "dead" } else { "merged" }});
        let mut line = serde_json::to_vec(&value).expect("合并记录必须可序列化");
        line.push(b'\n');
        output.lock().unwrap().write_all(&line).expect("写入 ISLA_MERGE_RECORDS 失败");
    }
}
