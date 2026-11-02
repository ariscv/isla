use super::is_mapping_rejection;
use isla_lib::bitvector::BV;
use isla_lib::error::ExecError;
use isla_lib::executor::{execute_ir_function_with_checkpoint, Run};
use isla_lib::ir::{Bindings, SharedState, Val};
use isla_lib::primop_util::length_bits;
use isla_lib::register::RegisterBindings;
use isla_lib::smt::{checkpoint, Checkpoint, Config, Context, SmtResult, Solver};
use isla_lib::source_loc::SourceLoc;
use std::sync::Mutex;

struct MappingPaths<B> {
    encoded: Vec<(Val<B>, Checkpoint<B>)>,
    rejected: Vec<Checkpoint<B>>,
    error: Option<ExecError>,
}

/// 编码分支在保留定义的辅助上下文中探索，终态先在完整执行约束下验证。
fn mapping_paths<B: BV>(
    function_name: &str,
    instruction: &Val<B>,
    shared_state: &SharedState<B>,
    pre_regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
    start: Checkpoint<B>,
    execution: &Checkpoint<B>,
    isolated: &Checkpoint<B>,
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
            if frame.has_sampled_branch() {
                let mut paths = paths.lock().expect("编码收集器锁中毒");
                if paths.error.is_none() {
                    paths.error = Some(ExecError::Unreachable(format!("{} 编码阶段发生符号分支采样", function_name)));
                }
                return;
            }
            // Dead 已在辅助域不可满足；完整执行域是它的子集。
            if matches!(&result, Ok((Run::Dead, _))) {
                return;
            }
            let candidate = checkpoint(&mut solver);
            let combined = execution.with_suffix_from(isolated, &candidate);
            let ctx = Context::new(Config::new());
            let mut verified = Solver::from_checkpoint(&ctx, combined.clone());
            let viability = match verified.check_sat(SourceLoc::unknown()) {
                SmtResult::Sat => Ok(()),
                SmtResult::Unsat => return,
                SmtResult::Unknown => Err(ExecError::Z3Unknown),
                SmtResult::Error(error) => Err(ExecError::Smt(error)),
            };
            if let Err(error) = viability {
                let mut paths = paths.lock().expect("编码收集器锁中毒");
                if paths.error.is_none() {
                    paths.error = Some(error);
                }
                return;
            }
            let outcome = match result {
                Ok((Run::Dead, _)) => unreachable!("Dead 已在辅助域提前过滤"),
                Ok((Run::Finished(Val::Poison), _)) => {
                    Err(ExecError::Unreachable(format!("{} 返回 Poison", function_name)))
                }
                Ok((Run::Finished(value), _)) => {
                    length_bits(&value, &mut solver, SourceLoc::unknown()).map(|_| Some(value))
                }
                Ok((Run::Exit | Run::Suspended, _)) => {
                    Err(ExecError::Unreachable(format!("{} 未正常返回编码", function_name)))
                }
                Err((error, frame)) => {
                    if is_mapping_rejection(function_name, &error, &frame, shared_state) {
                        paths.lock().expect("编码收集器锁中毒").rejected.push(candidate);
                        Ok(None)
                    } else {
                        frame.configure_timeout_smt_dump(&error, shared_state);
                        Err(error)
                    }
                }
            };
            let mut paths = paths.lock().expect("编码收集器锁中毒");
            match outcome {
                Ok(Some(value)) => paths.encoded.push((value, combined)),
                Ok(None) => (),
                Err(error) if paths.error.is_none() => paths.error = Some(error),
                Err(_) => (),
            }
        },
        start,
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
    let isolated = execution.with_instruction_assertions(instruction);
    let normal = mapping_paths(
        "zencdec_forwards",
        instruction,
        shared_state,
        pre_regs,
        lets,
        isolated.clone(),
        &execution,
        &isolated,
    )?;
    let mut encoded = normal.encoded;
    // 普通编码成功域保持优先；只有正常拒绝域才进入压缩编码。
    for rejected in normal.rejected {
        let compressed = mapping_paths(
            "zencdec_compressed_forwards",
            instruction,
            shared_state,
            pre_regs,
            lets,
            rejected,
            &execution,
            &isolated,
        )?;
        encoded.extend(compressed.encoded);
    }
    Ok(encoded)
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::bitvector::b64::B64;
    use isla_lib::ir::ExitCause;
    use isla_lib::ir::{Def, Exp, IRTypeInfo, Instr, Loc, Name, SharedState, Symtab, Ty, UVal, RETURN};
    use isla_lib::smt::smtlib::{self, Exp as SmtExp};
    use isla_lib::smt::Tactic;
    use std::collections::HashSet;

    #[test]
    fn isolated_candidates_keep_only_full_execution_feasible_encodings() {
        isla_lib::smt::configure_tastic(Tactic::Qfaufbv);
        let loc = SourceLoc::unknown();
        for mode in 0..3 {
            let rejected = mode == 1;
            let unreachable_error = mode == 2;
            let mut symtab = Symtab::new();
            let normal = symtab.intern("zencdec_forwards");
            let compressed = symtab.intern("zencdec_compressed_forwards");
            let arg = symtab.intern("zargument");
            let mut normal_body = vec![
                Instr::Jump(Exp::Id(arg), 3, loc),
                Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(0x13, 32)), loc),
                Instr::End,
            ];
            if rejected {
                normal_body.extend([
                    Instr::Exit(ExitCause::MatchFailure, loc),
                    Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(0, 32)), loc),
                    Instr::End,
                ]);
            } else if unreachable_error {
                normal_body.push(Instr::Exit(ExitCause::AssertionFailure, loc));
            } else {
                normal_body.extend([Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(0x93, 32)), loc), Instr::End]);
            }
            let defs: Vec<Def<Name, B64>> = vec![
                Def::Val(normal, vec![Ty::Bool], Ty::Bits(32)),
                Def::Fn(normal, vec![arg], normal_body),
                Def::Val(compressed, vec![Ty::Bool], Ty::Bits(16)),
                Def::Fn(
                    compressed,
                    vec![arg],
                    vec![Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(1, 16)), loc), Instr::End],
                ),
            ];
            let shared = SharedState::new(
                symtab,
                &defs,
                IRTypeInfo::new(&defs),
                HashSet::new(),
                HashSet::new(),
                HashSet::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            );
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let condition = solver.declare_const(smtlib::Ty::Bool, loc);
            if unreachable_error {
                solver.assert(SmtExp::Not(Box::new(SmtExp::Var(condition))));
            } else {
                solver.assert(SmtExp::Var(condition));
            }
            let execution = checkpoint(&mut solver);
            let input = Val::Symbolic(condition);
            let isolated = execution.with_instruction_assertions(&Val::Unit);
            if !unreachable_error {
                let all_normal = mapping_paths(
                    "zencdec_forwards",
                    &input,
                    &shared,
                    &RegisterBindings::new(),
                    &Bindings::default(),
                    isolated.clone(),
                    &isolated,
                    &isolated,
                )
                .unwrap();
                assert_eq!(all_normal.encoded.len(), if rejected { 1 } else { 2 });
                assert_eq!(all_normal.rejected.len(), if rejected { 1 } else { 0 });
            }

            let result =
                encoding_paths(&input, &shared, &RegisterBindings::new(), &Bindings::default(), execution).unwrap();
            assert_eq!(result.len(), 1);
            let expected = if rejected {
                B64::new(1, 16)
            } else if unreachable_error {
                B64::new(0x13, 32)
            } else {
                B64::new(0x93, 32)
            };
            assert!(matches!(&result[0].0, Val::Bits(bits) if *bits == expected));
            let mut verified = Solver::from_checkpoint(&ctx, result.into_iter().next().unwrap().1);
            assert_eq!(verified.check_sat(loc), SmtResult::Sat);
        }
    }

    #[test]
    fn instruction_guard_prunes_auxiliary_candidates_but_keeps_state_variants() {
        isla_lib::smt::configure_tastic(Tactic::Qfaufbv);
        let loc = SourceLoc::unknown();
        let mut symtab = Symtab::new();
        let normal = symtab.intern("zencdec_forwards");
        let compressed = symtab.intern("zencdec_compressed_forwards");
        let arg = symtab.intern("zargument");
        let state_reg = symtab.intern("zstate");
        let defs: Vec<Def<Name, B64>> = vec![
            Def::Register(state_reg, Ty::Bool, vec![]),
            Def::Val(normal, vec![Ty::Bool], Ty::Bits(32)),
            Def::Fn(
                normal,
                vec![arg],
                vec![
                    Instr::Jump(Exp::Id(arg), 3, loc),
                    Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(0x13, 32)), loc),
                    Instr::End,
                    Instr::Jump(Exp::Id(state_reg), 6, loc),
                    Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(0x93, 32)), loc),
                    Instr::End,
                    Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(0x113, 32)), loc),
                    Instr::End,
                ],
            ),
            Def::Val(compressed, vec![Ty::Bool], Ty::Bits(16)),
            Def::Fn(
                compressed,
                vec![arg],
                vec![Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(1, 16)), loc), Instr::End],
            ),
        ];
        let shared = SharedState::new(
            symtab,
            &defs,
            IRTypeInfo::new(&defs),
            HashSet::new(),
            HashSet::new(),
            HashSet::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let op = solver.declare_const(smtlib::Ty::Bool, loc);
        let state = solver.declare_const(smtlib::Ty::Bool, loc);
        solver.assert(SmtExp::Var(op));
        let full = checkpoint(&mut solver);
        let instruction = Val::Symbolic(op);
        let mut regs = RegisterBindings::new();
        regs.insert(state_reg, false, UVal::Init(Val::Symbolic(state)));
        let baseline = full.with_instruction_assertions(&Val::Unit);
        let all = mapping_paths(
            "zencdec_forwards",
            &instruction,
            &shared,
            &regs,
            &Bindings::default(),
            baseline.clone(),
            &baseline,
            &baseline,
        )
        .unwrap();
        assert_eq!(all.encoded.len(), 3, "旧辅助域包含与原指令guard冲突的分支");
        let isolated = full.with_instruction_assertions(&instruction);
        let candidates = mapping_paths(
            "zencdec_forwards",
            &instruction,
            &shared,
            &regs,
            &Bindings::default(),
            isolated.clone(),
            &isolated,
            &isolated,
        )
        .unwrap();
        assert_eq!(candidates.encoded.len(), 2);
        let result = encoding_paths(&instruction, &shared, &regs, &Bindings::default(), full).unwrap();
        assert_eq!(result.len(), 2);
        let values: HashSet<_> = result
            .into_iter()
            .map(|(value, _)| match value {
                Val::Bits(bits) => bits.lower_u64(),
                other => panic!("预期编码位串，得到 {other:?}"),
            })
            .collect();
        assert_eq!(values, HashSet::from([0x93, 0x113]));
    }
}
