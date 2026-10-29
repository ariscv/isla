use super::is_mapping_rejection;
use isla_lib::bitvector::BV;
use isla_lib::error::ExecError;
use isla_lib::executor::{execute_ir_function_with_checkpoint, Run};
use isla_lib::ir::{Bindings, SharedState, Val};
use isla_lib::primop_util::length_bits;
use isla_lib::register::RegisterBindings;
use isla_lib::smt::{checkpoint, Checkpoint, SmtResult};
use isla_lib::source_loc::SourceLoc;
use std::sync::Mutex;

struct MappingPaths<B> {
    encoded: Vec<(Val<B>, Checkpoint<B>)>,
    rejected: Vec<Checkpoint<B>>,
    error: Option<ExecError>,
}

/// 编码分支与原执行路径共享符号和约束，每个终态保留自己的 checkpoint。
fn mapping_paths<B: BV>(
    function_name: &str,
    instruction: &Val<B>,
    shared_state: &SharedState<B>,
    pre_regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
    execution: Checkpoint<B>,
) -> Result<MappingPaths<B>, ExecError> {
    let paths = Mutex::new(MappingPaths { encoded: Vec::new(), rejected: Vec::new(), error: None });
    execute_ir_function_with_checkpoint(
        function_name,
        &[instruction.clone()],
        shared_state,
        pre_regs,
        lets,
        &paths,
        &|_, _, result, shared_state, mut solver, paths| {
            let frame = match &result {
                Ok((_, frame)) | Err((_, frame)) => frame,
            };
            let outcome =
                if frame.has_sampled_branch() {
                    Err(ExecError::Unreachable(format!("{} 编码阶段发生符号分支采样", function_name)))
                } else {
                    match result {
                        Ok((Run::Dead, _)) => Ok(None),
                        Ok((Run::Finished(Val::Poison), _)) => {
                            Err(ExecError::Unreachable(format!("{} 返回 Poison", function_name)))
                        }
                        Ok((Run::Finished(value), _)) => length_bits(&value, &mut solver, SourceLoc::unknown())
                            .and_then(|_| match solver.check_sat(SourceLoc::unknown()) {
                                SmtResult::Sat => Ok(Some(value)),
                                SmtResult::Unsat => Ok(None),
                                SmtResult::Unknown => Err(ExecError::Z3Unknown),
                                SmtResult::Error(error) => Err(ExecError::Smt(error)),
                            }),
                        Ok((Run::Exit | Run::Suspended, _)) => {
                            Err(ExecError::Unreachable(format!("{} 未正常返回编码", function_name)))
                        }
                        Err((error, frame)) => {
                            if is_mapping_rejection(function_name, &error, &frame, shared_state) {
                                match solver.check_sat(SourceLoc::unknown()) {
                                    SmtResult::Sat => {
                                        paths.lock().expect("编码收集器锁中毒").rejected.push(checkpoint(&mut solver));
                                        Ok(None)
                                    }
                                    SmtResult::Unsat => Ok(None),
                                    SmtResult::Unknown => Err(ExecError::Z3Unknown),
                                    SmtResult::Error(error) => Err(ExecError::Smt(error)),
                                }
                            } else {
                                frame.configure_timeout_smt_dump(&error, shared_state);
                                Err(error)
                            }
                        }
                    }
                };
            let mut paths = paths.lock().expect("编码收集器锁中毒");
            match outcome {
                Ok(Some(value)) => paths.encoded.push((value, checkpoint(&mut solver))),
                Ok(None) => (),
                Err(error) if paths.error.is_none() => paths.error = Some(error),
                Err(_) => (),
            }
        },
        execution,
        None,
    );
    let mut paths = paths.into_inner().expect("编码收集器锁中毒");
    match paths.error.take() {
        Some(error) => Err(error),
        None => Ok(paths),
    }
}

pub(super) fn encoding_paths<B: BV>(
    instruction: &Val<B>,
    shared_state: &SharedState<B>,
    pre_regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
    execution: Checkpoint<B>,
) -> Result<Vec<(Val<B>, Checkpoint<B>)>, ExecError> {
    let normal = mapping_paths("zencdec_forwards", instruction, shared_state, pre_regs, lets, execution)?;
    let mut encoded = normal.encoded;
    // 普通编码成功域保持优先；只有正常拒绝域才进入压缩编码。
    for rejected in normal.rejected {
        let compressed =
            mapping_paths("zencdec_compressed_forwards", instruction, shared_state, pre_regs, lets, rejected)?;
        encoded.extend(compressed.encoded);
    }
    Ok(encoded)
}
