//! RISC-V 有符号和无符号读共用访存，保留原编码域及各自的入口签名。
use isla_lib::bitvector::BV;
use isla_lib::error::ExecError;
use isla_lib::executor::LocalFrame;
use isla_lib::ir::regions::instruction_operands;
use isla_lib::ir::{ExitCause, Exp as IrExp, Instr, Loc, Name, SharedState, Val};
use isla_lib::primop_util::{length_bits, smt_value};
use isla_lib::smt::smtlib::{bits64, Exp};
use isla_lib::smt::{checkpoint, Checkpoint, Config, Context, SmtResult, Solver, Sym};
use isla_lib::source_loc::SourceLoc;

type ResumePoint = (Name, usize);

pub(super) struct EntryTwins {
    pub(super) unsigned_index: usize,
    signedness: Sym,
    resume_at: ResumePoint,
}

pub(super) struct Entry<B> {
    pub(super) index: usize,
    pub(super) encoding: Val<B>,
    pub(super) checkpoint: Checkpoint<B>,
    pub(super) twins: Option<EntryTwins>,
}

impl<B: BV> Entry<B> {
    pub(super) fn with_frame<'ir>(&self, initial: LocalFrame<'ir, B>, roots: usize) -> LocalFrame<'ir, B> {
        match &self.twins {
            Some(twins) => initial.with_shared_path_root(
                self.index,
                twins.unsigned_index,
                roots,
                twins.signedness,
                twins.resume_at,
            ),
            None => initial.with_path_root(self.index, roots),
        }
    }
}

/// 仅在 RISC-V LOAD 的真实载荷和访存返回位置可确定时选择优化。
pub(super) fn shared_load<B: BV>(instruction: &Val<B>, shared: &SharedState<B>) -> Option<(Sym, ResumePoint)> {
    let load = shared.symtab.get("zLOAD")?;
    let Val::Ctor(ctor, payload) = instruction else { return None };
    if *ctor != load {
        return None;
    }
    let Val::Struct(fields) = payload.as_ref() else { return None };
    let rs1_field = shared.symtab.get("ztuplez3z5bv12_z5bv5_z5bv5_z5bool_z5i641")?;
    let sign_field = shared.symtab.get("ztuplez3z5bv12_z5bv5_z5bv5_z5bool_z5i643")?;
    let width_field = shared.symtab.get("ztuplez3z5bv12_z5bv5_z5bv5_z5bool_z5i644")?;
    let Some(Val::Symbolic(sign)) = fields.get(&sign_field) else { return None };
    let execute = shared.symtab.get("zexecute")?;
    let read = shared.symtab.get("zvmem_read")?;
    let extend = shared.symtab.get("zextend_value")?;
    let (_, _, instructions) = shared.functions.get(&execute)?;
    let mut extensions = instructions.iter().enumerate().filter_map(|(pc, instruction)| match instruction {
        Instr::Call(_, false, name, args, _) if *name == extend => Some((pc, args.as_slice())),
        _ => None,
    });
    let (extend_pc, [IrExp::Id(sign_slot), _]) = extensions.next()? else { return None };
    if extensions.next().is_some() {
        return None;
    }
    let before_extend = &instructions[..extend_pc];
    let read_pc = before_extend
        .iter()
        .rposition(|instruction| matches!(instruction, Instr::Call(_, false, name, _, _) if *name == read))?;
    let Instr::Call(_, false, _, read_args, _) = &instructions[read_pc] else { unreachable!() };
    let [IrExp::Id(base_slot), _, IrExp::Id(width_slot), ..] = read_args.as_slice() else { return None };

    let (clause, input) =
        instructions[..read_pc].iter().enumerate().rev().find_map(|(pc, instruction)| match instruction {
            Instr::Jump(IrExp::Kind(ctor, value), target, _) if *ctor == load && *target > extend_pc => {
                match value.as_ref() {
                    IrExp::Id(input) => Some((pc, *input)),
                    _ => None,
                }
            }
            _ => None,
        })?;
    let required_fields = [(rs1_field, *base_slot), (sign_field, *sign_slot), (width_field, *width_slot)];
    let mut extracted = 0u8;
    for (pc, instruction) in instructions.iter().enumerate().take(read_pc + 1).skip(clause + 1) {
        if let Instr::Copy(Loc::Id(slot), IrExp::Field(record, field), _) = instruction {
            if matches!(record.as_ref(), IrExp::Unwrap(ctor, value)
                if *ctor == load && matches!(value.as_ref(), IrExp::Id(value) if *value == input))
            {
                // 只认这条 LOAD 的原字段，其他字段也不能写入这三个槽。
                if let Some(index) = required_fields.iter().position(|(required, _)| required == field) {
                    let (_, expected) = required_fields[index];
                    if *slot != expected || extracted & (1 << index) != 0 {
                        return None;
                    }
                    extracted |= 1 << index;
                } else if required_fields.iter().any(|(_, required)| required == slot) {
                    return None;
                }
                continue;
            }
        }
        if let Instr::Goto(handler) = instruction {
            // solve-state 默认把 Sail 断言移到四条指令的尾部处理块。
            let [Instr::Jump(condition, pass, _), Instr::Exit(ExitCause::AssertionFailure, _), Instr::Copy(Loc::Id(result), IrExp::Unit, _), Instr::Goto(resume)] =
                instructions.get(*handler..handler.checked_add(4)?)?
            else {
                return None;
            };
            if *handler <= extend_pc
                || *pass != *handler + 2
                || *resume != pc + 1
                || *result == input
                || required_fields.iter().any(|(_, slot)| result == slot)
                || expression_uses_entry(condition, input, *sign_slot)
            {
                return None;
            }
            continue;
        }
        if matches!(instruction, Instr::Jump(..) | Instr::Goto(..) | Instr::Exit(..) | Instr::Arbitrary | Instr::End) {
            return None;
        }
        let (arguments, destination, implicit) = instruction_operands(instruction);
        let reads_instruction_or_sign = |name: Name| name == input || name == *sign_slot;
        if arguments.into_iter().any(|argument| expression_uses_entry(argument, input, *sign_slot))
            || implicit.is_some_and(reads_instruction_or_sign)
            || destination.is_some_and(|location| {
                let name = location.id();
                reads_instruction_or_sign(name)
                    || (extracted & 1 != 0 && name == *base_slot)
                    || (extracted & 4 != 0 && name == *width_slot)
            })
        {
            return None;
        }
    }
    if extracted != 0b111 {
        return None;
    }
    Some((*sign, (execute, read_pc + 1)))
}

fn expression_uses_entry(expression: &IrExp<Name>, input: Name, sign: Name) -> bool {
    match expression {
        IrExp::Id(name) | IrExp::Ref(name) => *name == input || *name == sign,
        IrExp::Kind(_, expression) | IrExp::Unwrap(_, expression) | IrExp::Field(expression, _) => {
            expression_uses_entry(expression, input, sign)
        }
        IrExp::Call(_, args) => args.iter().any(|arg| expression_uses_entry(arg, input, sign)),
        IrExp::Struct(_, fields) => fields.iter().any(|(_, value)| expression_uses_entry(value, input, sign)),
        _ => false,
    }
}

struct LoadEncoding {
    code: u64,
    guard: Exp<Sym>,
    word: Exp<Sym>,
}

fn proven<B: BV>(solver: &mut Solver<B>, counterexample: Exp<Sym>) -> bool {
    // 入口合并是可选优化。没有证明时，两份编码检查点继续各自执行。
    solver.check_sat_with(&counterexample, SourceLoc::unknown()) == SmtResult::Unsat
}

fn specialize(exp: &Exp<Sym>, sign: Sym, unsigned: bool) -> Exp<Sym> {
    exp.map_var(&mut |symbol| Ok::<_, ()>(if *symbol == sign { Exp::Bool(unsigned) } else { Exp::Var(*symbol) }))
        .unwrap()
        .eval()
}

fn load_encoding<B: BV>(
    entry: &Entry<B>,
    base: &Checkpoint<B>,
    ctx: &Context,
    solver: &mut Solver<B>,
    sign: Sym,
) -> Result<Option<LoadEncoding>, ExecError> {
    let loc = SourceLoc::unknown();
    let mut encoded = Solver::from_checkpoint(ctx, entry.checkpoint.clone());
    if length_bits(&entry.encoding, &mut encoded, loc)? != 32 {
        return Ok(None);
    }
    let Some((guard, word)) = entry.checkpoint.project_smt_suffix(base, smt_value(&entry.encoding, loc)?) else {
        return Ok(None);
    };
    let opcode_and_funct3 = Exp::Bvand(Box::new(word.clone()), Box::new(bits64(0x707f, 32)));
    for code in [1, 5, 2, 6] {
        let word_matches = Exp::Eq(Box::new(opcode_and_funct3.clone()), Box::new(bits64((code << 12) | 3, 32)));
        let unsigned = code & 4 != 0;
        let sign_matches = Exp::Eq(Box::new(Exp::Var(sign)), Box::new(Exp::Bool(unsigned)));
        let bad = Exp::Not(Box::new(Exp::And(Box::new(word_matches), Box::new(sign_matches))));
        if proven(solver, Exp::And(Box::new(guard.clone()), Box::new(bad))) {
            return Ok(Some(LoadEncoding {
                code,
                guard: specialize(&guard, sign, unsigned),
                word: specialize(&word, sign, unsigned),
            }));
        }
    }
    Ok(None)
}

pub(super) fn plan<B: BV>(
    encodings: Vec<(Val<B>, Checkpoint<B>)>,
    base: &Checkpoint<B>,
    share: Option<(Sym, ResumePoint)>,
) -> Result<Vec<Entry<B>>, ExecError> {
    let mut entries = encodings
        .into_iter()
        .enumerate()
        .map(|(index, (encoding, checkpoint))| Some(Entry { index, encoding, checkpoint, twins: None }))
        .collect::<Vec<_>>();
    if let Some((sign, resume_at)) = share.filter(|_| entries.len() > 1) {
        let ctx = Context::new(Config::new());
        let mut proof = Solver::from_checkpoint(&ctx, base.clone());
        let candidates = entries
            .iter()
            .map(|entry| load_encoding(entry.as_ref().unwrap(), base, &ctx, &mut proof, sign))
            .collect::<Result<Vec<_>, _>>()?;
        for code in [1, 2] {
            let matching = |code| {
                candidates.iter().enumerate().filter_map(move |(index, entry)| {
                    entry.as_ref().filter(|entry| entry.code == code).map(|entry| (index, entry))
                })
            };
            let signed = matching(code).collect::<Vec<_>>();
            let unsigned = matching(code | 4).collect::<Vec<_>>();
            let ([(signed_index, signed)], [(unsigned_index, unsigned)]) = (signed.as_slice(), unsigned.as_slice())
            else {
                continue;
            };
            let different_domains = Exp::Neq(Box::new(signed.guard.clone()), Box::new(unsigned.guard.clone()));
            let code_difference = Exp::Bvxor(Box::new(signed.word.clone()), Box::new(unsigned.word.clone()));
            let different_operands = Exp::And(
                Box::new(signed.guard.clone()),
                Box::new(Exp::Neq(Box::new(code_difference), Box::new(bits64(1 << 14, 32)))),
            );
            if !proven(&mut proof, Exp::Or(Box::new(different_domains), Box::new(different_operands))) {
                continue;
            }

            // 两支的原编码约束恰好等于公共守卫与各自符号位的合取。
            let loc = SourceLoc::unknown();
            let mut merged = Solver::from_checkpoint(&ctx, base.with_assertion(signed.guard.clone(), loc));
            let word =
                Exp::Ite(Box::new(Exp::Var(sign)), Box::new(unsigned.word.clone()), Box::new(signed.word.clone()));
            let entry = entries[*signed_index].as_mut().unwrap();
            entry.encoding = Val::Symbolic(merged.define_bitvector(word, loc));
            entry.checkpoint = checkpoint(&mut merged);
            entry.twins = Some(EntryTwins { unsigned_index: *unsigned_index, signedness: sign, resume_at });
            entries[*unsigned_index] = None;
        }
    }
    Ok(entries.into_iter().flatten().collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::bitvector::b64::B64;
    use isla_lib::smt::smtlib::{bits64, Exp};
    use isla_lib::smt::{checkpoint, Checkpoint, Config, Context, SmtResult, Solver, Tactic};
    use isla_lib::source_loc::SourceLoc;

    fn eq(lhs: Exp<Sym>, rhs: Exp<Sym>) -> Exp<Sym> {
        Exp::Eq(Box::new(lhs), Box::new(rhs))
    }

    #[test]
    fn paired_load_entries_keep_the_exact_encoder_domain() {
        isla_lib::smt::configure_tastic(Tactic::Qfaufbv);
        let loc = SourceLoc::unknown();
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let signedness = solver.declare_const(isla_lib::smt::smtlib::Ty::Bool, loc);
        let width = solver.declare_const(isla_lib::smt::smtlib::Ty::BitVec(64), loc);
        let admitted = solver.declare_const(isla_lib::smt::smtlib::Ty::Bool, loc);
        let base = checkpoint(&mut solver);
        let encoding = |word, sign, bytes, extra: bool| {
            let mut solver = Solver::from_checkpoint(&ctx, base.clone());
            // 各编码检查点的局部符号编号相同，定义各自独立。
            let guard = solver.define_const(eq(Exp::Var(signedness), Exp::Bool(sign)), loc);
            solver.assert(Exp::Var(guard));
            solver.assert(eq(Exp::Var(width), bits64(bytes, 64)));
            if extra {
                solver.assert(Exp::Var(admitted));
            }
            (Val::Bits(B64::new(word, 32)), checkpoint(&mut solver))
        };
        let unsigned = Name::from_u32(0);
        let entries = plan(
            vec![
                encoding(0x0003_1383, false, 2, true),
                encoding(0x0003_2383, false, 4, false),
                encoding(0x0003_5383, true, 2, true),
                encoding(0x0003_6383, true, 4, true),
                encoding(0x0003_0383, false, 1, false),
                encoding(0x0003_4383, true, 1, false),
            ],
            &base,
            Some((signedness, (unsigned, 0))),
        )
        .expect("编码域证明可完成");
        assert_eq!(entries.iter().map(|entry| entry.index).collect::<Vec<_>>(), vec![0, 1, 3, 4, 5]);
        let mut paired = Solver::from_checkpoint(&ctx, entries[0].checkpoint.clone());
        for sign in [false, true] {
            assert_eq!(paired.check_sat_with(&eq(Exp::Var(signedness), Exp::Bool(sign)), loc), SmtResult::Sat);
        }
        assert_eq!(
            paired.check_sat_with(&Exp::Not(Box::new(eq(Exp::Var(width), bits64(2, 64)))), loc),
            SmtResult::Unsat
        );
        assert_eq!(paired.check_sat_with(&Exp::Not(Box::new(Exp::Var(admitted))), loc), SmtResult::Unsat);
    }

    #[test]
    fn one_fixed_instruction_keeps_its_entry() {
        let point = Checkpoint::new();
        let entries = plan(vec![(Val::Bits(B64::new(0x0003_5383, 32)), point.clone())], &point, None)
            .expect("固定指令无需做编码域证明");
        assert_eq!(entries.len(), 1);
        assert!(entries[0].twins.is_none());
    }
}
