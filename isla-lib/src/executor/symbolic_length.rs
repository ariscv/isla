//! 在具体长度消费者处，将合并产生的符号长度拆回具体候选路径。

use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::sync::Arc;

use super::execution_limits::{ExecutionLimitDecision, ExecutionLimitHandler};
use super::{
    branch_decision, btrace_push_branch_condition, execution_limit_error, freeze_frame, record_execution_limit,
    trace_fork_frame_with_branch_condition, ForkSink, Frame, LocalFrame, SpeculativeRejectReason, StopConditions, Task,
    TaskId, TaskState,
};
use crate::bitvector::BV;
use crate::error::ExecError;
use crate::fraction::Fraction;
use crate::ir::{Exp, Name, SharedState, Val};
use crate::primop;
use crate::smt::{checkpoint, smtlib, Event, FiniteDomain, Model, ModelVal, Solver};
use crate::source_loc::SourceLoc;

static ENUMERATION_CALLS: AtomicU64 = AtomicU64::new(0);
static ENUMERATION_CHECKS: AtomicU64 = AtomicU64::new(0);
static ENUMERATION_COMPLETED: AtomicU64 = AtomicU64::new(0);
static STRUCTURAL_CANDIDATES: AtomicU64 = AtomicU64::new(0);
static MODEL_CANDIDATES: AtomicU64 = AtomicU64::new(0);

struct EnumerationChecks(u64);

impl EnumerationChecks {
    fn start() -> Self {
        Self(crate::smt::thread_smt_check_count())
    }

    fn checks(&self) -> u64 {
        crate::smt::thread_smt_check_count() - self.0
    }
}

impl Drop for EnumerationChecks {
    fn drop(&mut self) {
        ENUMERATION_CHECKS.fetch_add(self.checks(), Relaxed);
        ENUMERATION_COMPLETED.fetch_add(1, Relaxed);
    }
}

/// 进度诊断中，仅统计具体值枚举函数内实际发出的 SMT check 与尝试的候选。
pub(super) fn finite_domain_diagnostics(trigger: &str) -> serde_json::Value {
    serde_json::json!({
        "kind": "symbolic_value_enumeration_summary",
        "trigger": trigger,
        "calls": ENUMERATION_CALLS.load(Relaxed),
        "completed": ENUMERATION_COMPLETED.load(Relaxed),
        "solver_checks": ENUMERATION_CHECKS.load(Relaxed),
        "structural_candidates": STRUCTURAL_CANDIDATES.load(Relaxed),
        "model_candidates": MODEL_CANDIDATES.load(Relaxed),
    })
}

/// 同一条 primop 重试时复用全部操作数，保持它们与已有拆分约束之间的关系。
pub(super) fn eval_operands<'exp, 'ir, B: BV>(
    operands: impl IntoIterator<Item = &'exp Exp<Name>>,
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Vec<Val<B>>, ExecError> {
    let mut values = eval_operands_before_concrete_choice(operands, frame, shared_state, solver, info)?;
    for value in &mut values {
        super::concrete_values::resolve(value, &frame.local_state.concrete_choices, solver, info)?;
    }
    Ok(values)
}

/// 仍能计算带守卫操作数的原语直接使用这一层。
pub(super) fn eval_operands_before_concrete_choice<'exp, 'ir, B: BV>(
    operands: impl IntoIterator<Item = &'exp Exp<Name>>,
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Vec<Val<B>>, ExecError> {
    if let Some((pc, operand)) = &frame.pending_retry_operand {
        assert_eq!(*pc, frame.pc, "重试操作数必须属于当前指令");
        if let Val::Vector(operands) = operand {
            return Ok(operands.clone());
        }
        assert!(matches!(operand, Val::Unit));
    }
    operands
        .into_iter()
        .map(|operand| {
            super::eval_exp(operand, Arc::make_mut(&mut frame.local_state), shared_state, solver, info)
                .map(|v| v.into_owned())
        })
        .collect()
}

/// 返回 true 时保持当前 pc 重试，false 表示当前约束不可满足。
#[allow(clippy::too_many_arguments)]
pub(super) fn retry_symbolic_length<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
    error: ExecError,
    operands: &[Val<B>],
    consumer: Option<(usize, super::PathTimeout)>,
    task_id: TaskId,
    task_fraction: &mut Fraction,
    stop_conditions: Option<&'task StopConditions>,
    fork_sink: &S,
    frame: &mut LocalFrame<'ir, B>,
    task_state: &'task TaskState<B>,
    solver: &mut Solver<B>,
    shared: &SharedState<'ir, B>,
) -> Result<bool, ExecError> {
    use smtlib::Exp::*;
    let _scope = super::stats::region_progress::QueryScope::enter("concretization");

    match &error {
        ExecError::IntegerConversion(..) => {
            if frame.region_execution.is_none() {
                branch_decision(frame, task_state, SpeculativeRejectReason::IntegerConversion)?;
            }
        }
        ExecError::RetryCondition(..) => {
            if frame.region_execution.is_none() {
                branch_decision(frame, task_state, SpeculativeRejectReason::RetryCondition)?;
            }
        }
        _ => (),
    }
    if let ExecError::IntegerConversion(in_range, info) | ExecError::RetryCondition(in_range, info) = error {
        let cond = solver.define_const(in_range, info);
        return retry_partition(
            consumer,
            None,
            cond,
            Var(cond),
            Not(Box::new(Var(cond))),
            operands,
            info,
            task_id,
            task_fraction,
            stop_conditions,
            fork_sink,
            frame,
            task_state,
            solver,
            shared,
        );
    }
    let (op, info) = match error {
        ExecError::SymbolicLength(operation, location) | ExecError::SymbolicNatural { operation, location, .. } => {
            (operation, location)
        }
        _ => return Err(error),
    };
    if consumer.is_some()
        && !solver.finite_domain_enabled()
        && task_state.execution_limits.as_ref().is_some_and(|limits| limits.merge_concrete_values)
        && super::region_merge::policy(frame, task_state, info) != crate::config::MergeMode::Off
    {
        return solver.with_finite_domain(|solver| {
            retry_symbolic_length(
                error,
                operands,
                consumer,
                task_id,
                task_fraction,
                stop_conditions,
                fork_sink,
                frame,
                task_state,
                solver,
                shared,
            )
        });
    }
    let finite_enabled = solver.finite_domain_enabled();
    if !finite_enabled && solver.no_smt() {
        return Err(ExecError::Smt(solver.no_smt_cannot_continue(op, info)));
    }
    if let ExecError::SymbolicNatural { symbol, minimum, maximum, .. } = error {
        return match fork_symbolic_value(
            symbol,
            Some(OperandBounds::RequireWithin(i128::from(minimum)..=i128::from(maximum))),
            consumer,
            operands,
            info,
            task_id,
            task_fraction,
            stop_conditions,
            fork_sink,
            frame,
            task_state,
            solver,
            shared,
        )? {
            ValueRetry::Forked => Ok(true),
            ValueRetry::Dead => Ok(false),
            ValueRetry::Unique => Err(error),
        };
    }
    // 两个端点都可继续保持符号时，按两者的差拆分即可。只有原语已经
    // 检查过联合端点范围，才会以 subrange_internal 报告长度重试。
    if op == "subrange_internal"
        && finite_enabled
        && consumer.is_some()
        && task_state.execution_limits.as_ref().is_some_and(|limits| limits.merge_concrete_values)
        && super::region_merge::policy(frame, task_state, info) != crate::config::MergeMode::Off
    {
        if let [bits, Val::Symbolic(high), Val::Symbolic(low)] = operands {
            let width = solver.define_const(primop::subrange_width(*high, *low), info);
            let source_width = crate::primop_util::length_bits(bits, solver, info)?;
            let valid = 1..=i128::from(source_width);
            let finite = match solver.finite_domain(width) {
                FiniteDomain::Known(_) | FiniteDomain::Bounded(_) => true,
                FiniteDomain::Unknown => false,
            };
            if finite {
                match fork_symbolic_value(
                    width,
                    Some(OperandBounds::Established(valid)),
                    consumer,
                    operands,
                    info,
                    task_id,
                    task_fraction,
                    stop_conditions,
                    fork_sink,
                    frame,
                    task_state,
                    solver,
                    shared,
                )? {
                    ValueRetry::Forked => return Ok(true),
                    ValueRetry::Dead => return Ok(false),
                    ValueRetry::Unique => (),
                }
            }
        }
    }

    // 只枚举消费者必须具体化的参数：长度、索引和字符串转换的输入。
    // 向量元素及其余位向量数据仍然保留符号关系。
    let indices: &[usize] = match op {
        "zeros"
        | "ones"
        | "undefined_bitvector"
        | "undefined_vector"
        | "vector_init"
        | "get_slice_int"
        | "internal_vector_init"
        | "isla_mask_from_low_bits"
        | "isla_vector_access_or_default"
        | "string_of_bits"
        | "string_of_int"
        | "dec_str"
        | "hex_str"
        | "decimal_string_of_bits"
        | "read_register_from_vector"
        | "write_register_from_vector" => &[0],
        "isla_pack_vreg" => &[0, 1],
        "isla_read_vreg" => &[0, 1, 2],
        "extension" | "replicate_bits" | "sail_truncate" | "sail_truncateLSB" | "pow_int" | "vector_access"
        | "vector_update" | "string_take" | "string_drop" => &[1],
        "slice_internal" | "read_mem_address" | "write_mem_address" => &[2],
        "read_memt_address" | "write_memt_address" => &[1],
        "subrange_internal" | "vector_subrange" => &[1, 2],
        "eq_anything" => &[0, 1],
        _ => return Err(error),
    };
    if !finite_enabled && solver.check_sat(info).is_unsat()? {
        return Ok(false);
    }

    for &index in indices {
        let mut symbols = Vec::new();
        if op == "eq_anything" {
            // 只枚举构造子标签，保留载荷中位向量数据的符号关系。
            let mut values = vec![&operands[index]];
            while let Some(value) = values.pop() {
                match value {
                    Val::SymbolicCtor(sym, constructors) => {
                        symbols.push(*sym);
                        values.extend(constructors.values());
                    }
                    Val::Ctor(_, payload) => values.push(payload),
                    Val::Struct(fields) => values.extend(fields.values()),
                    Val::Vector(elements) | Val::List(elements) => values.extend(elements),
                    _ => (),
                }
            }
        } else {
            match &operands[index] {
                Val::Symbolic(sym) => symbols.push(*sym),
                Val::MixedBits(_)
                    if matches!(
                        op,
                        "read_mem_address" | "write_mem_address" | "read_memt_address" | "write_memt_address"
                    ) =>
                {
                    // 区域边界针对完整地址；不能把某个拼接片段当作整个地址。
                    let Val::Symbolic(sym) =
                        crate::primop_util::replace_mixed_bits(operands[index].clone(), solver, info)?
                    else {
                        panic!("含符号片段的内存地址规范化后必须为符号位向量");
                    };
                    symbols.push(sym);
                }
                Val::MixedBits(segments) => {
                    for segment in segments {
                        if let crate::ir::BitsSegment::Symbolic(sym) = segment {
                            symbols.push(*sym);
                        }
                    }
                }
                _ => (),
            }
        }
        for sym in symbols {
            let partition = match op {
                "vector_access" | "vector_update" => {
                    let len = match &operands[0] {
                        Val::Vector(values) => u64::try_from(values.len()).unwrap(),
                        bits => u64::from(crate::primop_util::length_bits(bits, solver, info)?),
                    };
                    let width = solver.length(sym).expect("向量索引必须是位向量");
                    if width < 64 && (1u64 << width) <= len {
                        None
                    } else {
                        let limit = smtlib::bits64(len, width);
                        Some((
                            Bvult(Box::new(Var(sym)), Box::new(limit.clone())),
                            Bvuge(Box::new(Var(sym)), Box::new(limit)),
                        ))
                    }
                }
                "read_register_from_vector" | "write_register_from_vector" => {
                    let regs_index = if op == "read_register_from_vector" { 1 } else { 2 };
                    let Val::Vector(regs) = &operands[regs_index] else {
                        panic!("寄存器索引重试必须携带寄存器向量")
                    };
                    let width = solver.length(sym).expect("寄存器索引必须是位向量");
                    // 索引域全在合法范围内时，边界不能截断到索引位宽。
                    if width < 128 && (1u128 << width) <= regs.len() as u128 {
                        None
                    } else {
                        let limit = smtlib::bits64(regs.len() as u64, width);
                        Some((
                            Bvult(Box::new(Var(sym)), Box::new(limit.clone())),
                            Bvuge(Box::new(Var(sym)), Box::new(limit)),
                        ))
                    }
                }
                "read_mem_address" | "write_mem_address" | "read_memt_address" | "write_memt_address" => {
                    // 必须先确定完整访问长度，未固定时优先拆分长度，避免丢失跨边界的合法地址。
                    let bytes = match operands.get(index + 1) {
                        Some(Val::I128(bytes)) => u32::try_from(*bytes).expect("内存访问字节数必须能用 u32 表示"),
                        Some(Val::I64(bytes)) => u32::try_from(*bytes).expect("内存访问字节数必须能用 u32 表示"),
                        Some(Val::Bits(bytes)) => {
                            u32::try_from(bytes.unsigned()).expect("内存访问字节数必须能用 u32 表示")
                        }
                        Some(Val::Symbolic(bytes_sym)) => {
                            if let Some(bytes) = primop::proven_symbolic_i128(*bytes_sym, solver, info)? {
                                u32::try_from(bytes).expect("内存访问字节数必须能用 u32 表示")
                            } else {
                                return match fork_symbolic_value(
                                    *bytes_sym,
                                    None,
                                    consumer,
                                    operands,
                                    info,
                                    task_id,
                                    task_fraction,
                                    stop_conditions,
                                    fork_sink,
                                    frame,
                                    task_state,
                                    solver,
                                    shared,
                                )? {
                                    ValueRetry::Forked => Ok(true),
                                    ValueRetry::Dead => Ok(false),
                                    ValueRetry::Unique => panic!("无法证明的内存访问长度必须能够分叉"),
                                };
                            }
                        }
                        _ => {
                            // 无长度参数的写操作从数据位宽提取，无法确定时直接暴露内部错误。
                            let data = operands.get(index + 2).expect("内存访问重试必须提供长度或待写入数据");
                            let bits =
                                crate::primop_util::length_bits(data, solver, info).expect("待写入数据必须有确定位宽");
                            assert_eq!(bits % 8, 0, "待写入数据必须按字节对齐");
                            bits / 8
                        }
                    };
                    // 先按完整访问区间分离排除子域，再按起始地址分派区域。
                    if let Some(allowed) =
                        crate::memory::smt_excluded_constraint(frame.memory().regions(), &Var(sym), bytes, solver)
                    {
                        let excluded = Not(Box::new(allowed.clone()));
                        if solver.check_sat_with(&allowed, info).is_sat()?
                            && solver.check_sat_with(&excluded, info).is_sat()?
                        {
                            return retry_partition(
                                consumer,
                                None,
                                sym,
                                allowed,
                                excluded,
                                operands,
                                info,
                                task_id,
                                task_fraction,
                                stop_conditions,
                                fork_sink,
                                frame,
                                task_state,
                                solver,
                                shared,
                            );
                        }
                    }
                    let width = solver.length(sym).expect("内存地址必须是位向量");
                    let cmp_width = 64;
                    let addr_exp = if width > cmp_width {
                        Extract(63, 0, Box::new(Var(sym)))
                    } else if width < cmp_width {
                        ZeroExtend(cmp_width - width, Box::new(Var(sym)))
                    } else {
                        Var(sym)
                    };
                    // 逐区域拆分，保留区域内地址的符号覆盖及具体内存分派的优先级。
                    for region in frame.memory().regions() {
                        let range = region.region_range();
                        let in_region = And(
                            Box::new(Bvule(
                                Box::new(smtlib::bits64(range.start, cmp_width)),
                                Box::new(addr_exp.clone()),
                            )),
                            Box::new(Bvult(Box::new(addr_exp.clone()), Box::new(smtlib::bits64(range.end, cmp_width)))),
                        );
                        let outside_region = Not(Box::new(in_region.clone()));
                        if solver.check_sat_with(&in_region, info).is_sat()?
                            && solver.check_sat_with(&outside_region, info).is_sat()?
                        {
                            return fork_retry_operand(
                                sym,
                                in_region,
                                outside_region,
                                operands,
                                info,
                                task_id,
                                task_fraction,
                                stop_conditions,
                                fork_sink,
                                frame,
                                task_state,
                                solver,
                                shared,
                            );
                        }
                    }
                    // 同一区域中的有限合并地址沿原 ITE 条件拆分，不选择地址模型值。
                    let definitions = solver.trace().to_vec();
                    let dependencies = crate::simplify::EventReferences::from_events(&definitions).dependencies(sym);
                    let conditions: Vec<_> = definitions
                        .iter()
                        .filter_map(|event| match event {
                            Event::Smt(smtlib::Def::DefineConst(id, Ite(condition, _, _)), _, _)
                                if dependencies.contains(id) =>
                            {
                                Some(condition.as_ref().clone())
                            }
                            _ => None,
                        })
                        .collect();
                    for condition in conditions {
                        let opposite = Not(Box::new(condition.clone()));
                        if solver.check_sat_with(&condition, info).is_sat()?
                            && solver.check_sat_with(&opposite, info).is_sat()?
                        {
                            return fork_retry_operand(
                                sym,
                                condition,
                                opposite,
                                operands,
                                info,
                                task_id,
                                task_fraction,
                                stop_conditions,
                                fork_sink,
                                frame,
                                task_state,
                                solver,
                                shared,
                            );
                        }
                    }
                    // 无法继续按区域拆分时保留原错误，禁止退回地址单点枚举。
                    return Err(error);
                }
                _ => None,
            };
            if let Some((selected, remainder)) = partition {
                let is_index = matches!(
                    op,
                    "vector_access" | "vector_update" | "read_register_from_vector" | "write_register_from_vector"
                );
                let structurally_in_bounds = is_index && solver.finite_domain_predicate(&selected) == Some(true);
                if !structurally_in_bounds
                    && solver.check_sat_with(&selected, info).is_sat()?
                    && solver.check_sat_with(&remainder, info).is_sat()?
                {
                    // 先完整分离两类候选，再由消费者拒绝非法索引或处理默认符号内存。
                    let local = consumer.filter(|_| matches!(solver.finite_domain(sym), FiniteDomain::Known(_)));
                    return retry_partition(
                        local,
                        None,
                        sym,
                        selected,
                        remainder,
                        operands,
                        info,
                        task_id,
                        task_fraction,
                        stop_conditions,
                        fork_sink,
                        frame,
                        task_state,
                        solver,
                        shared,
                    );
                }
                // 不可满足的探测会使当前模型失效，单值枚举前须重新建立前缀模型。
                if !structurally_in_bounds {
                    assert!(solver.check_sat(info).is_sat()?, "边界探测不得改变路径可满足性");
                }
            }
            // 扩展及切片会按选中的具体位宽执行。整组候选都满足原语边界时，
            // 允许上界集合参与拆分，保留原守卫和其余路径约束。
            let bounds = if finite_enabled || consumer.is_some() {
                use crate::primop_util::length_bits;
                match (op, index, operands) {
                    ("zeros" | "ones", _, _) => {
                        // 延后区域的消费者按互补守卫拆分；RequireWithin 还会逐个检查
                        // 所有候选的表示范围。其余执行方式维持定义级的范围证明。
                        let width = solver.length(sym).expect("位宽参数必须为位向量");
                        let max = if width > 32 { u64::from(u32::MAX) } else { (1u64 << (width - 1)) - 1 };
                        let safe = Bvule(Box::new(Var(sym)), Box::new(smtlib::bits64(max, width)));
                        let deferred_consumer = solver.region_queries_deferred()
                            && frame.region_execution.is_some()
                            && consumer.is_some()
                            && task_state.execution_limits.as_ref().is_some_and(|limits| limits.merge_concrete_values);
                        (deferred_consumer || solver.structural_bool(&safe) == Some(true))
                            .then_some(0..=i128::from(max))
                    }
                    ("slice_internal", _, _) => Some(0..=i128::from(u32::MAX)),
                    ("vector_access" | "vector_update", 1, [Val::Vector(elements), ..]) => {
                        Some(0..=i128::try_from(elements.len()).unwrap() - 1)
                    }
                    ("extension", 1, [bits, ..]) => {
                        Some(i128::from(length_bits(bits, solver, info)?)..=i128::from(u32::MAX))
                    }
                    ("subrange_internal" | "vector_subrange", 1, [bits, _, Val::I128(low)]) if *low >= 0 => {
                        Some(*low..=i128::from(length_bits(bits, solver, info)?) - 1)
                    }
                    ("subrange_internal" | "vector_subrange", 2, [bits, Val::I128(high), _])
                        if *high < i128::from(length_bits(bits, solver, info)?) =>
                    {
                        Some(0..=*high)
                    }
                    _ => None,
                }
                .map(|range| {
                    if op == "subrange_internal" {
                        OperandBounds::Established(range)
                    } else {
                        OperandBounds::RequireWithin(range)
                    }
                })
            } else {
                None
            };
            match fork_symbolic_value(
                sym,
                bounds,
                consumer,
                operands,
                info,
                task_id,
                task_fraction,
                stop_conditions,
                fork_sink,
                frame,
                task_state,
                solver,
                shared,
            )? {
                ValueRetry::Forked => return Ok(true),
                ValueRetry::Dead => return Ok(false),
                ValueRetry::Unique => (),
            }
        }
    }
    Err(error)
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum ValueRetry {
    Forked,
    Unique,
    Dead,
}

pub(super) enum OperandBounds {
    // 原语已经在当前路径证明边界，或在无 SMT 下把边界加入了路径。
    Established(std::ops::RangeInclusive<i128>),
    RequireWithin(std::ops::RangeInclusive<i128>),
}

fn candidate_in_bounds(value: &smtlib::Exp<crate::smt::Sym>, bounds: &std::ops::RangeInclusive<i128>) -> bool {
    let length = match value {
        smtlib::Exp::Bits64(bits) => Some(i128::from(bits.signed())),
        smtlib::Exp::Bits(bits) => primop::i128_from_model_bits(bits),
        _ => unreachable!("有限域只含位向量常量"),
    };
    length.is_some_and(|length| bounds.contains(&length))
}

/// 将符号值拆为当前候选和剩余候选；唯一值不需要分叉。
#[allow(clippy::too_many_arguments)]
pub(super) fn fork_symbolic_value<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
    sym: crate::smt::Sym,
    bounds: Option<OperandBounds>,
    consumer: Option<(usize, super::PathTimeout)>,
    operands: &[Val<B>],
    info: SourceLoc,
    task_id: TaskId,
    task_fraction: &mut Fraction,
    stop_conditions: Option<&'task StopConditions>,
    fork_sink: &S,
    frame: &mut LocalFrame<'ir, B>,
    task_state: &'task TaskState<B>,
    solver: &mut Solver<B>,
    shared: &SharedState<'ir, B>,
) -> Result<ValueRetry, ExecError> {
    use smtlib::Exp::*;
    let diagnostics = crate::config::RegionOptions::current().progress;
    let _checks = diagnostics.then(|| {
        ENUMERATION_CALLS.fetch_add(1, Relaxed);
        EnumerationChecks::start()
    });
    if frame.region_execution.is_none() {
        branch_decision(frame, task_state, SpeculativeRejectReason::SymbolicValueEnumeration)?;
    };
    let width = solver.length(sym).expect("长度参数必须是位向量");
    assert!(width > 0, "待枚举的位向量必须具有正位宽");
    let inherited = solver.operand_bound(sym, info);
    let mut pass_bound = inherited.is_some();
    let domain = inherited.unwrap_or_else(|| solver.finite_domain(sym));
    let bounded = matches!(domain, FiniteDomain::Bounded(_));
    let mut restricted = false;
    let values = match (domain, bounds) {
        (FiniteDomain::Known(values), _) => Some(values),
        (FiniteDomain::Bounded(mut values), Some(OperandBounds::Established(range))) => {
            let old_len = values.len();
            // 切片的联合边界已生效，只能留下区间内的值。原前缀和选择等式继续参与重试。
            values.retain(|value| candidate_in_bounds(value, &range));
            restricted = values.len() != old_len;
            Some(values)
        }
        (FiniteDomain::Bounded(mut values), Some(OperandBounds::RequireWithin(range))) => {
            if values.iter().any(|v| !candidate_in_bounds(v, &range)) {
                let previous = values.len();
                solver.refine_guarded_values(sym, &mut values);
                restricted = values.len() != previous;
                pass_bound |= restricted;
            }
            values.iter().all(|v| candidate_in_bounds(v, &range)).then_some(values)
        }
        _ => None,
    };
    if let Some(values) = values {
        let Some(candidate) = values.first() else { return Ok(ValueRetry::Dead) };
        if values.len() == 1 {
            if !restricted {
                return Ok(ValueRetry::Unique);
            }
            let guard = Eq(Box::new(Var(sym)), Box::new(candidate.clone()));
            cache_retry_operand(frame, operands);
            solver.assert(guard.clone());
            btrace_push_branch_condition!(frame, guard);
            return Ok(ValueRetry::Forked);
        }
        let in_region = frame.region_execution.is_some();
        if !bounded
            && in_region
            && (consumer.is_none()
                || !task_state.execution_limits.as_ref().is_some_and(|limits| limits.merge_concrete_values))
        {
            // 事务只拥有当前推演臂，两边可行时交回区域外重放。
            return Err(super::region_merge::reject(frame, SpeculativeRejectReason::RetryOperand));
        }
        let equal = Eq(Box::new(Var(sym)), Box::new(candidate.clone()));
        let remainder = Neq(Box::new(Var(sym)), Box::new(candidate.clone()));
        if bounded {
            solver.note_finite_domain_use("finite_domain_bounded_width", info);
        }
        if bounded && !in_region {
            // 有限上界覆盖全部可行长度。候选仍须带上完整路径条件，用共用判定入口排除死侧。
            let selected = super::region_merge::feasible(frame, solver, &equal, info, shared)?;
            let other = super::region_merge::feasible(frame, solver, &remainder, info, shared)?;
            match (selected, other) {
                (false, false) => return Ok(ValueRetry::Dead),
                (true, true) => (),
                _ => {
                    let guard = if selected { equal } else { remainder };
                    cache_retry_operand(frame, operands);
                    solver.assert(guard.clone());
                    btrace_push_branch_condition!(frame, guard);
                    return Ok(ValueRetry::Forked);
                }
            }
        }
        if diagnostics {
            STRUCTURAL_CANDIDATES.fetch_add(1, Relaxed);
        }
        return Ok(
            if retry_partition(
                consumer,
                (pass_bound && in_region && solver.region_queries_deferred()).then_some(values),
                sym,
                equal,
                remainder,
                operands,
                info,
                task_id,
                task_fraction,
                stop_conditions,
                fork_sink,
                frame,
                task_state,
                solver,
                shared,
            )? {
                ValueRetry::Forked
            } else {
                ValueRetry::Dead
            },
        );
    }
    if solver.finite_domain_enabled() {
        let result = solver
            .check_candidate_sat(info)
            .ok_or_else(|| ExecError::Smt(solver.no_smt_cannot_continue("symbolic_value_enumeration", info)))?;
        if result == crate::smt::SmtResult::Unsat {
            return Ok(ValueRetry::Dead);
        }
        if frame.region_execution.is_some() && result.is_unknown() {
            return Err(super::region_merge::reject(frame, SpeculativeRejectReason::SolverUnknown));
        }
        if !super::region_merge::path_is_feasible(result, frame, solver, shared)? {
            return Err(ExecError::SolverDroppedPath);
        }
    }
    let candidate = {
        let mut model = Model::new(solver);
        model.set_complete_model(true);
        match model.get_var(sym)? {
            ModelVal::Exp(candidate @ (Bits(_) | Bits64(_))) => candidate,
            value => panic!("长度参数的模型不是位向量：{value:?}"),
        }
    };
    if diagnostics {
        MODEL_CANDIDATES.fetch_add(1, Relaxed);
    }
    let equal = Eq(Box::new(Var(sym)), Box::new(candidate.clone()));
    let remainder = Neq(Box::new(Var(sym)), Box::new(candidate));
    let _scope = super::stats::region_progress::QueryScope::enter("concretization");
    let selected = solver.check_sat_with(&equal, info);
    assert_ne!(selected, crate::smt::SmtResult::Unsat, "模型中的长度候选必须可满足");
    let selected = super::region_merge::path_is_feasible(selected, frame, solver, shared)?;
    let remainder_result = if frame.region_execution.is_some() {
        solver.check_sat_with_for_branch(&remainder, info, true)
    } else {
        Some(solver.check_sat_with(&remainder, info))
    };
    let remainder_failed = matches!(&remainder_result, Some(crate::smt::SmtResult::Error(_)));
    let has_remainder = match remainder_result {
        Some(result) => super::region_merge::path_is_feasible(result, frame, solver, shared)?,
        None => true,
    };
    if !selected {
        if !has_remainder {
            return Err(ExecError::SolverDroppedPath);
        }
        cache_retry_operand(frame, operands);
        solver.assert(remainder.clone());
        btrace_push_branch_condition!(frame, remainder);
        return Ok(ValueRetry::Forked);
    }
    if !has_remainder {
        if remainder_failed {
            // 唯一幸存候选必须实际约束到该值，不能继续使用原来的较宽输入域。
            cache_retry_operand(frame, operands);
            solver.assert(equal.clone());
            btrace_push_branch_condition!(frame, equal);
            return Ok(ValueRetry::Forked);
        }
        assert!(solver.check_sat(info).is_sat()?, "探测不应改变路径可满足性");
        return Ok(ValueRetry::Unique);
    }

    if !fork_retry_operand(
        sym,
        equal,
        remainder,
        operands,
        info,
        task_id,
        task_fraction,
        stop_conditions,
        fork_sink,
        frame,
        task_state,
        solver,
        shared,
    )? {
        return Err(ExecError::SolverDroppedPath);
    }
    Ok(ValueRetry::Forked)
}

fn cache_retry_operand<B: BV>(frame: &mut LocalFrame<'_, B>, operands: &[Val<B>]) {
    let cached =
        if frame.local_state.expression_retry_operands.is_some() { Val::Unit } else { Val::Vector(operands.to_vec()) };
    frame.pending_retry_operand = Some((frame.pc, cached));
}

/// 有限候选和原语给出的范围谓词共用指令级事务。没有穷尽结构域的
/// 单点模型枚举仍由普通执行调度，允许其它路径在枚举期间继续。
#[allow(clippy::too_many_arguments)]
fn retry_partition<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
    consumer: Option<(usize, super::PathTimeout)>,
    split: Option<Vec<smtlib::Exp<crate::smt::Sym>>>,
    sym: crate::smt::Sym,
    equal: smtlib::Exp<crate::smt::Sym>,
    remainder: smtlib::Exp<crate::smt::Sym>,
    operands: &[Val<B>],
    info: SourceLoc,
    task_id: TaskId,
    fraction: &mut Fraction,
    stop: Option<&'task StopConditions>,
    sink: &S,
    frame: &mut LocalFrame<'ir, B>,
    state: &'task TaskState<B>,
    solver: &mut Solver<B>,
    shared: &SharedState<'ir, B>,
) -> Result<bool, ExecError> {
    if let Some((tid, timeout)) = consumer {
        let previous = frame.pending_retry_operand.clone();
        cache_retry_operand(frame, operands);
        let retry = super::concrete_values::ConsumerRetry::Operand {
            guards: [equal.clone(), remainder.clone()],
            split: split.map(|values| (sym, values)),
        };
        match super::concrete_values::retry_region(
            retry, info, tid, task_id, fraction, timeout, stop, sink, frame, state, shared, solver,
        ) {
            Ok(Some(alive)) => return Ok(alive),
            result => {
                frame.pending_retry_operand = previous;
                result?;
            }
        }
    }
    fork_retry_operand(
        sym, equal, remainder, operands, info, task_id, fraction, stop, sink, frame, state, solver, shared,
    )
}

/// 两种重试都保存操作数，并沿用同一套执行限制和检查点语义。
/// 区域中两个守卫皆可达时拒绝本次推演，由普通执行用原前缀提交互补的两臂。
/// 两个守卫皆不可达时直接报告路径死亡。
#[allow(clippy::too_many_arguments)]
pub(super) fn fork_retry_operand<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
    sym: crate::smt::Sym,
    equal: smtlib::Exp<crate::smt::Sym>,
    remainder: smtlib::Exp<crate::smt::Sym>,
    operands: &[Val<B>],
    info: SourceLoc,
    task_id: TaskId,
    task_fraction: &mut Fraction,
    stop_conditions: Option<&'task StopConditions>,
    fork_sink: &S,
    frame: &mut LocalFrame<'ir, B>,
    task_state: &'task TaskState<B>,
    solver: &mut Solver<B>,
    shared: &SharedState<'ir, B>,
) -> Result<bool, ExecError> {
    use smtlib::Def::Assert;
    if frame.region_execution.is_some() {
        let selected = super::region_merge::feasible(frame, solver, &equal, info, shared)?;
        let other = super::region_merge::feasible(frame, solver, &remainder, info, shared)?;
        if selected && other {
            return Err(super::region_merge::reject(frame, SpeculativeRejectReason::RetryOperand));
        }
        if !selected && !other {
            return Ok(false);
        }
        cache_retry_operand(frame, operands);
        solver.assert(if selected { equal } else { remainder });
        return Ok(true);
    }
    branch_decision(frame, task_state, SpeculativeRejectReason::RetryOperand)?;
    let decision = match task_state.execution_limits.as_ref() {
        Some(limits) => ExecutionLimitHandler::new(limits).on_monomorphize_fork_at(
            Arc::make_mut(&mut frame.execution_limit_state),
            frame.function_name,
            frame.pc,
            &frame.backtrace,
            info,
        ),
        None => ExecutionLimitDecision::Fork { fork_id: Arc::make_mut(&mut frame.execution_limit_state).record_fork() },
    };
    let fork_id = match decision {
        ExecutionLimitDecision::Fork { fork_id } => Some(fork_id),
        ExecutionLimitDecision::KeepCurrentModel { reason } => {
            Arc::make_mut(&mut frame.execution_limit_state).record_kept_current_model();
            record_execution_limit(frame, reason, "keep_current_model");
            None
        }
        ExecutionLimitDecision::Truncate(reason) => {
            record_execution_limit(frame, reason, "truncate_symbolic_length");
            return Err(execution_limit_error(reason, frame.function_name, frame.pc));
        }
        ExecutionLimitDecision::Continue | ExecutionLimitDecision::ConcretizeBranch { .. } => {
            panic!("算子重试分叉返回了无效的执行限制决策")
        }
    };

    // 在冻结子帧前保存；当前路径与剩余候选路径必须使用同一次求值的操作数。
    cache_retry_operand(frame, operands);
    if let Some(fork_id) = fork_id {
        let point = checkpoint(solver);
        frame.capture_path_smt_stats();
        let mut child = trace_fork_frame_with_branch_condition!(frame, frame.pc, remainder.clone());
        Arc::make_mut(&mut child.execution_limit_state).advance_path_signature(false);
        Arc::make_mut(&mut frame.execution_limit_state).advance_path_signature(true);
        let child_fraction = task_fraction.min_split(6);
        fork_sink.submit(Task {
            id: task_id,
            fraction: child_fraction,
            frame: child,
            checkpoint: point,
            fork_cond: Some((Assert(remainder), Event::Fork(fork_id, sym, 1, info))),
            state: task_state,
            stop_conditions,
        });
        solver.add_event(Event::Fork(fork_id, sym, 0, info));
    } else {
        // 预算要求保留当前模型时，转换检查也必须按该模型选支。
        assert!(solver.check_sat(info).is_sat()?, "重试分叉的前缀必须可满足");
        let selected = {
            let mut model = Model::new(solver);
            model.set_complete_model(true);
            match model.get_exp(&equal)? {
                ModelVal::Exp(smtlib::Exp::Bool(true)) => equal,
                ModelVal::Exp(smtlib::Exp::Bool(false)) => remainder,
                value => panic!("重试分叉条件的模型必须是布尔值：{value:?}"),
            }
        };
        solver.add(Assert(selected.clone()));
        btrace_push_branch_condition!(frame, selected);
        return Ok(true);
    }
    solver.add(Assert(equal.clone()));
    btrace_push_branch_condition!(frame, equal);
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::smt::{Config, Context, SmtResult};

    #[test]
    fn enumeration_counts_checks_across_savepoint_rollback() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        crate::smt::reset_path_smt_stats();
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let choice = solver.declare_const(smtlib::Ty::Bool, info);
        let savepoint = solver.start_transaction();
        assert_eq!(solver.check_sat_with_for_range(&smtlib::Exp::Var(choice), info), SmtResult::Sat);
        assert_eq!(crate::smt::path_smt_stats().solver_checks, 1);

        let checks = std::mem::ManuallyDrop::new(EnumerationChecks::start());
        assert_eq!(
            solver.check_sat_with_for_range(&smtlib::Exp::Not(Box::new(smtlib::Exp::Var(choice))), info),
            SmtResult::Sat
        );
        assert_eq!(crate::smt::path_smt_stats().solver_checks, 2);
        solver.rollback_transaction(savepoint);
        assert_eq!(crate::smt::path_smt_stats().solver_checks, 0);
        assert_eq!(checks.checks(), 1);
    }
}
