//! 在具体长度消费者处，将合并产生的符号长度拆回具体候选路径。

use std::sync::Arc;

use super::execution_limits::{ExecutionLimitDecision, ExecutionLimitHandler};
use super::{
    execution_limit_error, freeze_frame, itrace_fork_frame_with_branch_condition, itrace_push_branch_condition,
    record_execution_limit, ForkSink, Frame, LocalFrame, StopConditions, Task, TaskId, TaskState,
};
use crate::bitvector::BV;
use crate::error::ExecError;
use crate::fraction::Fraction;
use crate::ir::{Exp, Name, SharedState, Val};
use crate::smt::{checkpoint, smtlib, Event, Model, ModelVal, Solver};
use crate::source_loc::SourceLoc;

/// 同一条 primop 重试时复用全部操作数，保持它们与已有拆分约束之间的关系。
pub(super) fn eval_operands<'exp, 'ir, B: BV>(
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
        assert!(matches!(operand, Val::Unit), "表达式重试必须使用独立的缓存");
    }
    operands
        .into_iter()
        .map(|operand| {
            super::eval_exp(operand, &mut frame.local_state, shared_state, solver, info).map(|v| v.into_owned())
        })
        .collect()
}

/// 返回 true 时保持当前 pc 重试，false 表示当前约束不可满足。
#[allow(clippy::too_many_arguments)]
pub(super) fn retry_symbolic_length<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B>>(
    error: ExecError,
    operands: &[Val<B>],
    task_id: TaskId,
    task_fraction: &mut Fraction,
    stop_conditions: Option<&'task StopConditions>,
    fork_sink: &S,
    frame: &mut LocalFrame<'ir, B>,
    task_state: &'task TaskState<B>,
    solver: &mut Solver<B>,
) -> Result<bool, ExecError> {
    use smtlib::Exp::*;

    if let ExecError::IntegerConversion(in_range, info) = error {
        let cond = solver.define_const(in_range, info);
        fork_retry_operand(
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
        )?;
        return Ok(true);
    }
    let ExecError::SymbolicLength(op, info) = error else { return Err(error) };
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
        | "decimal_string_of_bits" => &[0],
        "isla_read_vreg" | "isla_pack_vreg" => &[0, 1],
        "extension" | "replicate_bits" | "sail_truncate" | "sail_truncateLSB" | "pow_int" | "vector_access"
        | "vector_update" => &[1],
        "slice_internal" => &[2],
        "subrange_internal" => &[1, 2],
        _ => return Err(error),
    };
    if solver.check_sat(info).is_unsat()? {
        return Ok(false);
    }

    for &index in indices {
        let mut symbols = Vec::new();
        match &operands[index] {
            Val::Symbolic(sym) => symbols.push(*sym),
            Val::MixedBits(segments) => {
                for segment in segments {
                    if let crate::ir::BitsSegment::Symbolic(sym) = segment {
                        symbols.push(*sym);
                    }
                }
            }
            _ => (),
        }
        for sym in symbols {
            if fork_symbolic_value(
                sym,
                operands,
                info,
                task_id,
                task_fraction,
                stop_conditions,
                fork_sink,
                frame,
                task_state,
                solver,
            )? {
                return Ok(true);
            }
        }
    }
    Err(error)
}

/// 将符号值拆为当前候选和剩余候选；唯一值不需要分叉。
#[allow(clippy::too_many_arguments)]
pub(super) fn fork_symbolic_value<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B>>(
    sym: crate::smt::Sym,
    operands: &[Val<B>],
    info: SourceLoc,
    task_id: TaskId,
    task_fraction: &mut Fraction,
    stop_conditions: Option<&'task StopConditions>,
    fork_sink: &S,
    frame: &mut LocalFrame<'ir, B>,
    task_state: &'task TaskState<B>,
    solver: &mut Solver<B>,
) -> Result<bool, ExecError> {
    use smtlib::Exp::*;
    let width = solver.length(sym).expect("长度参数必须是位向量");
    assert!(width > 0, "待枚举的位向量必须具有正位宽");
    let candidate = {
        let mut model = Model::new(solver);
        model.set_complete_model(true);
        match model.get_var(sym)? {
            ModelVal::Exp(candidate @ (Bits(_) | Bits64(_))) => candidate,
            value => panic!("长度参数的模型不是位向量：{value:?}"),
        }
    };
    let equal = Eq(Box::new(Var(sym)), Box::new(candidate.clone()));
    let remainder = Neq(Box::new(Var(sym)), Box::new(candidate));
    assert!(solver.check_sat_with(&equal, info).is_sat()?, "模型中的长度候选必须可满足");
    if !solver.check_sat_with(&remainder, info).is_sat()? {
        assert!(solver.check_sat(info).is_sat()?, "探测不应改变路径可满足性");
        return Ok(false);
    }

    fork_retry_operand(
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
    )?;
    Ok(true)
}

/// 两种重试都必须保存操作数，并沿用同一套执行限制和检查点语义。
#[allow(clippy::too_many_arguments)]
pub(super) fn fork_retry_operand<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B>>(
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
) -> Result<(), ExecError> {
    use smtlib::Def::Assert;
    let decision = match task_state.execution_limits.as_ref() {
        Some(limits) => ExecutionLimitHandler::new(limits).on_monomorphize_fork_at(
            &mut frame.execution_limit_state,
            frame.function_name,
            frame.pc,
            &frame.backtrace,
            info,
        ),
        None => ExecutionLimitDecision::Fork { fork_id: frame.execution_limit_state.record_fork() },
    };
    let fork_id = match decision {
        ExecutionLimitDecision::Fork { fork_id } => Some(fork_id),
        ExecutionLimitDecision::KeepCurrentModel { reason } => {
            frame.execution_limit_state.record_kept_current_model();
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
    let cached =
        if frame.local_state.expression_retry_operands.is_some() { Val::Unit } else { Val::Vector(operands.to_vec()) };
    frame.pending_retry_operand = Some((frame.pc, cached));
    if let Some(fork_id) = fork_id {
        let point = checkpoint(solver);
        frame.capture_path_smt_stats();
        let mut child = itrace_fork_frame_with_branch_condition!(frame, frame.pc, remainder.clone());
        Arc::make_mut(&mut child.execution_limit_state).advance_path_signature(false);
        frame.execution_limit_state.advance_path_signature(true);
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
        itrace_push_branch_condition!(frame, selected);
        return Ok(());
    }
    solver.add(Assert(equal.clone()));
    itrace_push_branch_condition!(frame, equal);
    Ok(())
}
