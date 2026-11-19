//! 守卫具体值在消费者处拆分，沿用执行器的快照、份额和限制。
use super::*;
use std::sync::atomic::{AtomicUsize, Ordering};

static CREATED: AtomicUsize = AtomicUsize::new(0);
static FORKS: AtomicUsize = AtomicUsize::new(0);
static REGIONS: AtomicUsize = AtomicUsize::new(0);
static REJECTED: AtomicUsize = AtomicUsize::new(0);

pub(crate) fn created() {
    CREATED.fetch_add(1, Ordering::Relaxed);
}
pub(super) fn snapshot() -> serde_json::Value {
    serde_json::json!({"created": CREATED.load(Ordering::Relaxed), "forks": FORKS.load(Ordering::Relaxed),
        "consumer_regions": REGIONS.load(Ordering::Relaxed), "rejected_consumers": REJECTED.load(Ordering::Relaxed)})
}

/// 在调用原语之前处理全部复合载荷；原语不会看到未选择的候选值。
pub(super) fn resolve<B: BV>(
    value: &mut Val<B>,
    choices: &Option<HashMap<Sym, bool>>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<(), ExecError> {
    if let Some(choices) = choices {
        resolve_value(value, choices, solver, info, false)?;
    }
    Ok(())
}

/// 位宽候选可以交给直接比较和终态读者。其它候选仍按原方式选择。
pub(super) fn resolve_non_bit_choices<B: BV>(
    value: &mut Val<B>,
    choices: &Option<HashMap<Sym, bool>>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<(), ExecError> {
    if let Some(choices) = choices {
        resolve_value(value, choices, solver, info, true)?;
    }
    Ok(())
}

fn resolve_value<B: BV>(
    value: &mut Val<B>,
    choices: &HashMap<Sym, bool>,
    solver: &mut Solver<B>,
    info: SourceLoc,
    preserve_widths: bool,
) -> Result<(), ExecError> {
    if preserve_widths && matches!(value, Val::Guarded(..)) && crate::primop_util::guarded_bits::is_bits(value, solver)
    {
        return Ok(());
    }
    match value {
        Val::Guarded(guard, values) => {
            let selected = choices
                .get(guard)
                .copied()
                .or_else(|| solver.structural_bool(&smtlib::Exp::Var(*guard)))
                .ok_or(ExecError::ConcreteChoice(*guard, info))?;
            *value = if selected { values.0.clone() } else { values.1.clone() };
            resolve_value(value, choices, solver, info, preserve_widths)
        }
        Val::Struct(fields) | Val::SymbolicCtor(_, fields) => {
            for value in fields.values_mut() {
                resolve_value(value, choices, solver, info, preserve_widths)?;
            }
            Ok(())
        }
        Val::Vector(values) | Val::List(values) => {
            for value in values {
                resolve_value(value, choices, solver, info, preserve_widths)?;
            }
            Ok(())
        }
        Val::Ctor(_, value) => resolve_value(value, choices, solver, info, preserve_widths),
        _ => Ok(()),
    }
}

pub(super) enum ConsumerRetry {
    Choice(Sym),
    Operand([smtlib::Exp<Sym>; 2]),
}

#[allow(clippy::too_many_arguments)]
pub(super) fn retry_region<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
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
    let result = region_merge::concrete_consumer(
        retry, info, tid, task_id, fraction, timeout, stop, sink, frame, state, shared, solver,
    );
    match &result {
        Ok(Some(_)) => {
            REGIONS.fetch_add(1, Ordering::Relaxed);
        }
        Err(_) => {
            REJECTED.fetch_add(1, Ordering::Relaxed);
        }
        Ok(None) => (),
    }
    result
}

#[allow(clippy::too_many_arguments)]
pub(super) fn retry<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
    guard: Sym,
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
) -> Result<bool, ExecError> {
    if let Some(result) = retry_region(
        ConsumerRetry::Choice(guard),
        info,
        tid,
        task_id,
        fraction,
        timeout,
        stop,
        sink,
        frame,
        state,
        shared,
        solver,
    )? {
        return Ok(result);
    }
    let positive = smtlib::Exp::Var(guard);
    let negative = smtlib::Exp::Not(Box::new(positive.clone()));
    let mut feasible =
        |condition| solver.check_sat_with_for_branch(condition, info, true).map_or(Ok(true), |result| result.is_sat());
    let yes = feasible(&positive)?;
    let no = feasible(&negative)?;
    if !yes && !no {
        return Ok(false);
    }
    if yes != no {
        cost::make_mut(&mut frame.local_state)
            .concrete_choices
            .as_mut()
            .expect("具体值拆分必须已启用")
            .insert(guard, yes);
        frame.pending_retry_operand.get_or_insert((frame.pc, Val::Unit));
        solver.assert(if yes { positive } else { negative });
        return Ok(true);
    }
    branch_decision(frame, state, SpeculativeRejectReason::RetryOperand)?;
    let decision = match state.execution_limits.as_ref() {
        Some(limits) => ExecutionLimitHandler::new(limits).on_monomorphize_fork_at(
            cost::make_mut(&mut frame.execution_limit_state),
            frame.function_name,
            frame.pc,
            &frame.backtrace,
            info,
        ),
        None => {
            ExecutionLimitDecision::Fork { fork_id: cost::make_mut(&mut frame.execution_limit_state).record_fork() }
        }
    };
    let fork_id = match decision {
        ExecutionLimitDecision::Fork { fork_id } => fork_id,
        ExecutionLimitDecision::Truncate(reason) => {
            return Err(execution_limit_error(reason, frame.function_name, frame.pc))
        }
        // 此处没有求解模型，不能把保留当前模型解释为任意选择具体候选。
        ExecutionLimitDecision::KeepCurrentModel { .. } => {
            REJECTED.fetch_add(1, Ordering::Relaxed);
            return Err(ExecError::Type("具体候选拆分不支持当前模型采样".into(), info));
        }
        _ => panic!("具体候选拆分返回无效的限制决策"),
    };
    frame.pending_retry_operand.get_or_insert((frame.pc, Val::Unit));
    let point = checkpoint(solver);
    frame.capture_path_smt_stats();
    let other = negative;
    let mut child = trace_fork_frame_with_branch_condition!(frame, frame.pc, other.clone());
    cost::make_mut(&mut child.local_state)
        .concrete_choices
        .as_mut()
        .expect("具体值拆分必须已启用")
        .insert(guard, false);
    cost::make_mut(&mut child.execution_limit_state).advance_path_signature(false);
    cost::make_mut(&mut frame.local_state).concrete_choices.as_mut().expect("具体值拆分必须已启用").insert(guard, true);
    cost::make_mut(&mut frame.execution_limit_state).advance_path_signature(true);
    sink.submit(Task {
        id: task_id,
        fraction: fraction.min_split(6),
        frame: child,
        checkpoint: point,
        fork_cond: Some((Def::Assert(other), Event::Fork(fork_id, guard, 1, info))),
        state,
        stop_conditions: stop,
    });
    solver.add_event(Event::Fork(fork_id, guard, 0, info));
    solver.assert(smtlib::Exp::Var(guard));
    FORKS.fetch_add(1, Ordering::Relaxed);
    Ok(true)
}

/// 复制仍可携带未知候选；已在本路径选择的守卫则立即还原具体叶子。
pub(super) fn select_known<B: BV>(value: &mut Val<B>, choices: &HashMap<Sym, bool>) {
    match value {
        Val::Guarded(guard, values) => {
            if let Some(selected) = choices.get(guard) {
                *value = if *selected { values.0.clone() } else { values.1.clone() };
                select_known(value, choices);
            }
        }
        Val::Struct(fields) | Val::SymbolicCtor(_, fields) => {
            for value in fields.values_mut() {
                select_known(value, choices);
            }
        }
        Val::Vector(values) | Val::List(values) => {
            for value in values {
                select_known(value, choices);
            }
        }
        Val::Ctor(_, value) => select_known(value, choices),
        _ => (),
    }
}
