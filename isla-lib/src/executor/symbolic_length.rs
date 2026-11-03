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
        let Val::Vector(operands) = operand else { panic!("重试缓存必须保存操作数列表") };
        return Ok(operands.clone());
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
    use smtlib::Def::Assert;
    use smtlib::Exp::*;

    let ExecError::SymbolicLength(op, info) = error else { return Err(error) };
    // 只枚举需要具体化的长度参数，不能把位向量数据或向量元素也逐值展开。
    let indices: &[usize] = match op {
        "zeros" | "ones" | "undefined_vector" | "vector_init" | "get_slice_int" => &[0],
        "extension" | "replicate_bits" | "sail_truncate" | "sail_truncateLSB" | "pow_int" => &[1],
        "slice_internal" => &[2],
        "subrange_internal" => &[1, 2],
        _ => return Err(error),
    };
    if solver.check_sat(info).is_unsat()? {
        return Ok(false);
    }

    for &index in indices {
        let Val::Symbolic(sym) = operands[index] else { continue };
        let width = solver.length(sym).expect("长度参数必须是位向量");
        assert!((1..=128).contains(&width), "整数长度参数不能超出 128 位");
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
            // 已唯一的操作数不是报错原因；subrange 可能还需拆分另一个边界。
            // 下一次取模型前重新 check，避免使用临时探测后的模型。
            assert!(solver.check_sat(info).is_sat()?, "探测不应改变路径可满足性");
            continue;
        }

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
                panic!("符号长度分叉返回了无效的执行限制决策")
            }
        };

        // 在冻结子帧前保存；当前路径与剩余候选路径必须使用同一次求值的操作数。
        frame.pending_retry_operand = Some((frame.pc, Val::Vector(operands.to_vec())));
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
        }
        solver.add(Assert(equal.clone()));
        itrace_push_branch_condition!(frame, equal);
        return Ok(true);
    }
    Err(error)
}
