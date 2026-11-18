//! 区域引擎的执行、状态合并与记录边界，不决定待办的调度顺序。
use super::region_merge::{fold_exit_frontiers, reject, AccessLog, RegionResult};
use super::stats::merge_diagnostics as diagnostics;
use super::*;
use crate::executor::stats::region_cost as cost;
use crate::ir::regions::Region;

mod dependencies;
pub(super) use dependencies::LoopDependencies;

/// 构造具体臂帧并保存完整守卫；片段由调用栈或队列持有。
pub(super) fn branch_arm<'ir, B: BV>(
    base: &LocalFrame<'ir, B>,
    pc: usize,
    guard: smtlib::Exp<Sym>,
    owner: crate::smt::LogicalArm,
) -> LocalFrame<'ir, B> {
    let mut arm = base.clone();
    arm.pc = pc;
    arm.region_arm = Some(owner);
    let access = cost::make_mut(&mut arm.local_state).speculative_access.as_mut().unwrap();
    access.guard = Some(match access.guard.take() {
        Some(parent) => smtlib::Exp::And(Box::new(parent), Box::new(guard)),
        None => guard,
    });
    arm
}

/// Some 表示本次前沿已关闭；None 表示调用栈需继续分开的片段，臂保存点仍打开。
#[allow(clippy::too_many_arguments)]
pub(super) fn advance_arm<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
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
) -> Result<Option<bool>, ExecError> {
    let result = run_loop(tid, task_id, fraction, timeout, stop, sink, arm, state, shared, solver);
    if arm.region_arrivals.is_empty() {
        close_arm(result, tx, arm, shared, solver, info).map(Some)
    } else {
        assert!(matches!(result, Ok(Run::Suspended)), "只有区域挂起点可以交付未合并片段");
        Ok(None)
    }
}

/// true 表示可作为到达前沿或待展开片段保留；延迟模式的保留不代表已认证。
pub(super) fn close_arm<B: BV>(
    result: Result<Run<B>, ExecError>,
    tx: crate::smt::SolverTransaction,
    arm: &LocalFrame<B>,
    shared: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<bool, ExecError> {
    match result {
        Ok(Run::Suspended) => {
            let close_scope = super::stats::region_progress::QueryScope::enter("arm_close");
            let close_result = solver.check_sat_for_arm(info);
            drop(close_scope);
            match close_result {
                None | Some(SmtResult::Sat) => {
                    assert!(!solver.transaction_invalid(), "臂提交前保存点必须有效");
                    solver.commit_transaction();
                    Ok(true)
                }
                Some(SmtResult::Unsat) => {
                    solver.commit_dead_transaction();
                    Ok(false)
                }
                Some(SmtResult::Unknown) => {
                    solver.rollback_transaction(tx);
                    Err(reject(arm, SpeculativeRejectReason::SolverUnknown))
                }
                Some(SmtResult::Error(error)) => {
                    solver.rollback_transaction(tx);
                    Err(ExecError::Smt(error))
                }
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
            Err(reject(arm, SpeculativeRejectReason::SymbolicAssertion))
        }
        Ok(Run::Dead) | Err(ExecError::AssertionFailure(..)) => {
            // 具体失败与普通执行同义：仅删除完整到达守卫覆盖的臂。
            // 符号断言已在原语处记录义务，不会从这里静默丢弃。
            solver.commit_dead_transaction();
            Ok(false)
        }
        Err(error) => {
            diagnostics::execute_arm_error(arm.function_name, arm.pc, &error, &shared.symtab);
            solver.rollback_transaction(tx);
            Err(match error {
                ExecError::SpeculativeReject { .. } | ExecError::Smt(_) | ExecError::Timeout => error,
                ExecError::Z3Unknown => reject(arm, SpeculativeRejectReason::SolverUnknown),
                _ => reject(arm, SpeculativeRejectReason::IncompatibleState),
            })
        }
        Ok(_) => {
            solver.rollback_transaction(tx);
            Err(reject(arm, SpeculativeRejectReason::RegionEscaped))
        }
    }
}

/// 提交后的返回前沿与继续前沿共用相同的条件事件后缀，分别保留自己的根记录。
pub(super) fn publish_committed_records<B: BV>(
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
    if super::merge_record::enabled() {
        frame.region_merge_records.edit_suffix(start, |records| {
            super::merge_record::publish(records, &frame.local_state.pure_definitions, task, shared, solver)
        });
    }
}

/// 同一循环的退出前沿可能有多个兼容组。一次折叠失败只留下原两个前沿。
pub(super) fn append_loop_exit<'ir, B: BV>(
    exits: &mut Vec<LocalFrame<'ir, B>>,
    next: LocalFrame<'ir, B>,
    solver: &mut Solver<B>,
    fold: impl FnOnce(LocalFrame<'ir, B>, LocalFrame<'ir, B>, &mut Solver<B>) -> Result<LocalFrame<'ir, B>, ExecError>,
) -> Result<(), ExecError> {
    let Some(previous) = exits.pop() else {
        exits.push(next);
        return Ok(());
    };
    let tx = solver.start_transaction();
    match fold(previous.clone(), next.clone(), solver) {
        Ok(frame) => {
            solver.commit_transaction();
            exits.push(frame);
            Ok(())
        }
        Err(error) => {
            solver.rollback_transaction(tx);
            if !matches!(&error, ExecError::SpeculativeReject { reason, .. } if is_join_rejection(*reason) || matches!(reason, SpeculativeRejectReason::FlatLoopShape | SpeculativeRejectReason::StateEffect))
            {
                return Err(error);
            }
            if let ExecError::SpeculativeReject { reason, function, pc, location } = &error {
                diagnostics::emit(serde_json::json!({"stage":"loop_fold_rejected","difference":"loop_fold_rejected",
                    "reason":reason,"at":{"function_id":function.as_u32(),"pc":pc,"location":location}}));
            }
            charge_fragment_growth(&next, 1)?;
            exits.extend([previous, next]);
            Ok(())
        }
    }
}

pub(super) fn loop_exit_guard<B: BV>(exits: &[LocalFrame<B>]) -> smtlib::Exp<Sym> {
    let mut guards = exits.iter().map(|frame| {
        frame.local_state.speculative_access.as_ref().unwrap().guard.clone().expect("退出片段必须保存原守卫")
    });
    let first = guards.next().expect("退出合集不能为空");
    guards.fold(first, |left, right| smtlib::Exp::Or(Box::new(left), Box::new(right)))
}

fn is_join_rejection(reason: SpeculativeRejectReason) -> bool {
    matches!(
        reason,
        SpeculativeRejectReason::IncompatibleState
            | SpeculativeRejectReason::UnionPayload
            | SpeculativeRejectReason::RegisterSequence
            | SpeculativeRejectReason::RelaxedRegister
            | SpeculativeRejectReason::LoopHistoryMismatch
    )
}

fn charge_fragment_growth<B: BV>(frame: &LocalFrame<B>, additional: usize) -> Result<(), ExecError> {
    if let Some(remaining) =
        frame.region_execution.as_ref().and_then(|execution| execution.additional_fragments.as_ref())
    {
        if remaining.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |left| left.checked_sub(additional)).is_err() {
            return Err(reject(frame, SpeculativeRejectReason::FragmentLimit));
        }
    }
    Ok(())
}

/// 汇合动作在自己的保存点内；失败时保留已执行两臂的帧与完整守卫。
#[allow(clippy::too_many_arguments)]
pub(super) fn finish_arrivals<'ir, B: BV>(
    record_id: usize,
    condition: Sym,
    region: &Region,
    base: &LocalFrame<'ir, B>,
    mut arms: [Vec<LocalFrame<'ir, B>>; 2],
    frame: &mut LocalFrame<'ir, B>,
    state: &TaskState<B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
    prepare: impl FnOnce(&mut [Vec<LocalFrame<'ir, B>>; 2]),
) -> Result<RegionResult, ExecError> {
    let keep_separate =
        frame.region_execution.as_ref().is_some_and(|execution| execution.mode == crate::config::MergeMode::Adaptive)
            && base.region_execution.as_ref().unwrap().mode == crate::config::MergeMode::Adaptive;
    let saved = keep_separate.then(|| arms.clone());
    prepare(&mut arms);
    let tx = keep_separate.then(|| solver.start_transaction());
    let finish = |solver: &mut Solver<B>| {
        let mut sides = Vec::with_capacity(2);
        for side in arms {
            let mut combined = None;
            for fragment in side {
                combined = Some(match combined {
                    None => fragment,
                    Some(previous) => {
                        fold_exit_frontiers(previous, fragment, base, region, state, shared, solver, info)?
                    }
                });
            }
            sides.push(combined);
        }
        finish_region(record_id, condition, region, base, sides, frame, state, shared, solver, info)
    };
    match (finish(solver), tx) {
        (Ok(result), tx) => {
            if tx.is_some() {
                solver.commit_transaction();
            }
            Ok(result)
        }
        (Err(error), tx) => {
            if let Some(tx) = tx {
                solver.rollback_transaction(tx);
            }
            let ExecError::SpeculativeReject { reason, function, pc, location } = error else { return Err(error) };
            if !is_join_rejection(reason) || !keep_separate {
                return Err(error);
            }
            diagnostics::emit(
                serde_json::json!({"stage":"local_join_rejected","difference":"local_join_rejected","reason":reason,
                "at":{"function":diagnostics::name_string(function,&shared.symtab),"pc":pc,"location":location}}),
            );
            let mut separate: Vec<_> = saved.unwrap().into_iter().flatten().collect();
            assert!(separate.len() >= 2, "局部汇合拒绝必须保留两条以上片段");
            shared.execution_stats.merge_rejected(frame.function_name, region.branch_pc, &error);
            state.speculation_stats.record_reject(reason);
            charge_fragment_growth(frame, separate.len() - 1)?;
            for fragment in &mut separate {
                fragment.region_execution = frame.region_execution.clone();
                fragment.speculation_mode = frame.speculation_mode;
            }
            assert!(frame.region_arrivals.is_empty());
            frame.region_arrivals = separate;
            Ok(RegionResult::Separate(reason))
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn finish_region<'ir, B: BV>(
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
    let cost_scope = cost::Scope::enter(cost::Category::StateMerge);
    let _ = &cost_scope;
    let depth = base.region_execution.as_ref().unwrap().depth;
    // 只修改本次推演产生的根记录。历史前缀和已连接的后代保持原上下文。
    for (index, arm) in arms.iter_mut().enumerate() {
        if let Some(arm) = arm {
            arm.region_merge_records.edit_suffix(frame.region_merge_records.len(), |records| {
                for record in records {
                    if record.parent_record.is_none() {
                        record.parent_record = Some(record_id);
                        record.arm = if index == 0 { "then" } else { "else" };
                    }
                }
            });
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
                value_symbols: HashSet::from([condition]).into(),
                input_symbols: HashSet::new().into(),
                single_arm_reads: Vec::new().into(),
                memory_reads: Vec::new().into(),
            });
            return Ok(RegionResult::Dead);
        }
        (Some(mut arm), None) | (None, Some(mut arm)) => {
            let access = arm.local_state.speculative_access.as_ref().unwrap();
            let single_arm_reads: Vec<_> = access
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
                value_symbols: HashSet::new().into(),
                input_symbols: HashSet::new().into(),
                single_arm_reads: single_arm_reads.into(),
                memory_reads: Vec::new().into(),
            });
            arm
        }
        (Some(left), Some(right)) => {
            merge_states(record_id, condition, &base, left, right, &region, state, shared, solver, info)?
        }
    };
    let record = merged.region_merge_records.last_mut().expect("成功合并必须有记录");
    Arc::make_mut(&mut record.value_symbols).insert(condition);
    for (bindings, original) in
        [(&merged.local_state.vars, &frame.local_state.vars), (&merged.local_state.lets, &frame.local_state.lets)]
    {
        for (name, value) in bindings {
            if let UVal::Init(value) = value {
                if !matches!(original.get(name), Some(UVal::Init(old)) if value == old) {
                    Arc::make_mut(&mut record.value_symbols).extend(value.symbolic_variables());
                }
            }
        }
    }
    let access = merged.local_state.speculative_access.as_ref().unwrap();
    for reg in &access.writes.modified_regs {
        if let Some(value) = merged.local_state.regs.get_last_if_initialized(*reg) {
            Arc::make_mut(&mut record.value_symbols).extend(value.symbolic_variables());
        }
    }
    cost::make_mut(&mut merged.local_state).speculative_access.as_mut().unwrap().guard =
        frame.local_state.speculative_access.as_ref().and_then(|access| access.guard.clone());
    merged.region_execution = frame.region_execution.clone();
    merged.region_arm = frame.region_arm;
    merged.speculation_mode = frame.speculation_mode;
    if merged.region_execution.is_none() {
        // 仅前置状态/访问足迹可信，需要逐条精确读写顺序时不可信。
        // 读取在真实读取处缓冲，提交时按并集发布；此处补发以 ITE 保留原值的条件写入。
        let access = cost::make_mut(&mut merged.local_state).speculative_access.take().unwrap();
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
        "at":{"function":diagnostics::name_string(base.function_name,&shared.symtab),"pc":base.pc,
            "location":base.instrs.get(base.pc).and_then(stats::instr_source_loc)},
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
    let cost_scope = cost::Scope::enter(cost::Category::StateMerge);
    let _ = &cost_scope;
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
    cost::make_mut(&mut merged.local_state).pure_definitions = left.local_state.pure_definitions.clone();
    cost::make_mut(&mut merged.local_state)
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
    cost::make_mut(&mut merged.local_state).speculative_access = Some(access);
    merged.pc = left.pc;
    let prefix = base.region_merge_records.len();
    merged.region_merge_records.append_suffix(&left.region_merge_records, prefix);
    merged.region_merge_records.append_suffix(&right.region_merge_records, prefix);
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
        value_symbols: HashSet::new().into(),
        input_symbols: HashSet::new().into(),
        single_arm_reads: single_arm_reads.into(),
        memory_reads: Vec::new().into(),
    });
    Ok(merged)
}
