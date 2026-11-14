//! 在完整函数CFG上计算布尔常量；未知调用与间接写入不保留旧知识。
use super::*;

fn boolean(exp: &Exp<Name>, facts: &HashMap<Name, bool>) -> Option<bool> {
    match exp {
        Exp::Bool(value) => Some(*value),
        Exp::Id(name) => facts.get(name).copied(),
        Exp::Call(Op::Not, args) => match args.as_slice() {
            [value] => boolean(value, facts).map(|value| !value),
            _ => None,
        },
        Exp::Call(op, args) => match (op, args.as_slice()) {
            (Op::And, [left, right]) => match (boolean(left, facts), boolean(right, facts)) {
                (Some(false), _) | (_, Some(false)) => Some(false),
                (Some(true), Some(true)) => Some(true),
                _ => None,
            },
            (Op::Or, [left, right]) => match (boolean(left, facts), boolean(right, facts)) {
                (Some(true), _) | (_, Some(true)) => Some(true),
                (Some(false), Some(false)) => Some(false),
                _ => None,
            },
            (Op::Eq, [left, right]) => Some(boolean(left, facts)? == boolean(right, facts)?),
            (Op::Neq, [left, right]) => Some(boolean(left, facts)? != boolean(right, facts)?),
            _ => None,
        },
        _ => None,
    }
}

impl RegionCfg {
    /// 不可达是None；可达状态只保存确定的局部布尔值，缺项表示未知。
    /// 合流取共同常量，循环用工作队列迭代到不动点，不设次数或时间限制。
    pub(crate) fn constant_branches<B: BV>(
        &self,
        instrs: &[Instr<Name, B>],
        constant_returns: &HashMap<Name, bool>,
    ) -> HashMap<usize, bool> {
        assert_eq!(instrs.len(), self.pcs.len());
        assert!(self.exception_pcs.is_empty(), "常量证明必须保留完整异常边");
        if instrs.is_empty() {
            return HashMap::new();
        }
        let locals: HashSet<_> = instrs
            .iter()
            .filter_map(|instr| match instr {
                Instr::Decl(name, ..) | Instr::Init(name, ..) => Some(*name),
                _ => None,
            })
            .chain([RETURN])
            .collect();
        let mut states: Vec<Option<HashMap<Name, bool>>> = vec![None; instrs.len()];
        states[0] = Some(HashMap::new());
        let mut pending = VecDeque::from([0]);
        let mut queued = vec![false; instrs.len()];
        queued[0] = true;
        while let Some(pc) = pending.pop_front() {
            queued[pc] = false;
            let input = states[pc].as_ref().unwrap();
            let condition = match &instrs[pc] {
                Instr::Jump(exp, ..) => boolean(exp, input),
                _ => None,
            };
            let mut output = input.clone();
            let assignment = match &instrs[pc] {
                Instr::Decl(name, ..) | Instr::Monomorphize(name, ..) => Some((Loc::Id(*name), None)),
                Instr::Init(name, _, exp, _) => Some((Loc::Id(*name), boolean(exp, input))),
                Instr::Copy(loc, exp, _) => Some((loc.clone(), boolean(exp, input))),
                Instr::Call(loc, _, callee, _, _) => {
                    let value = constant_returns.get(callee).copied();
                    if value.is_none() {
                        output.clear();
                    }
                    Some((loc.clone(), value))
                }
                Instr::PrimopUnary(loc, f, exp, _)
                    if std::ptr::fn_addr_eq(*f, primop::not_bool::<B> as primop::Unary<B>) =>
                {
                    Some((loc.clone(), boolean(exp, input).map(|value| !value)))
                }
                Instr::PrimopUnary(loc, ..)
                | Instr::PrimopBinary(loc, ..)
                | Instr::PrimopVariadic(loc, ..)
                | Instr::PrimopReset(loc, ..) => {
                    // 不透明原语与Reset闭包不在静态阶段执行，也不猜其返回值。
                    output.clear();
                    Some((loc.clone(), None))
                }
                _ => None,
            };
            if let Some((loc, value)) = assignment {
                let mut root = &loc;
                while let Loc::Field(inner, _) = root {
                    root = inner;
                }
                if matches!(root, Loc::Addr(_)) {
                    output.clear();
                } else if let (Loc::Id(name), Some(value)) = (&loc, value) {
                    if locals.contains(name) {
                        output.insert(*name, value);
                    }
                } else {
                    output.remove(&loc.id());
                }
            }
            for (target, edge) in self.successors(pc) {
                if matches!((condition, edge), (Some(value), EdgeKind::Jump(polarity)) if value != polarity) {
                    continue;
                }
                let RegionPoint::Instruction(target) = target else { continue };
                let changed = match &mut states[target] {
                    None => {
                        states[target] = Some(output.clone());
                        true
                    }
                    Some(old) => {
                        let before = old.len();
                        old.retain(|name, value| output.get(name) == Some(value));
                        old.len() != before
                    }
                };
                if changed && !queued[target] {
                    pending.push_back(target);
                    queued[target] = true;
                }
            }
        }
        instrs
            .iter()
            .enumerate()
            .filter_map(|(pc, instr)| match instr {
                Instr::Jump(exp, ..) => boolean(exp, states[pc].as_ref()?).map(|value| (pc, value)),
                _ => None,
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::ir::{Reset, Ty, Val};
    use crate::source_loc::SourceLoc;

    fn name(value: u32) -> Name {
        Name::from_u32(value + 100)
    }
    fn copy(value: bool) -> Instr<Name, B64> {
        Instr::Copy(Loc::Id(name(1)), Exp::Bool(value), SourceLoc::unknown())
    }
    fn jump(condition: Name, target: usize) -> Instr<Name, B64> {
        Instr::Jump(Exp::Id(condition), target, SourceLoc::unknown())
    }
    fn branches(body: &[Instr<Name, B64>]) -> HashMap<usize, bool> {
        RegionCfg::new(body, RegionOptions::default()).constant_branches(body, &HashMap::new())
    }

    #[test]
    fn constant_merge_keeps_only_agreement_and_loop_backedges_weaken_facts() {
        for right in [false, true] {
            let body = vec![
                Instr::Decl(name(1), Ty::Bool, SourceLoc::unknown()),
                jump(name(0), 4),
                copy(false),
                Instr::Goto(5),
                copy(right),
                jump(name(1), 7),
                Instr::End,
                Instr::End,
            ];
            assert_eq!(branches(&body).get(&5), if right { None } else { Some(&false) });
        }
        let body = vec![
            Instr::Init(name(1), Ty::Bool, Exp::Bool(false), SourceLoc::unknown()),
            jump(name(1), 4),
            copy(true),
            Instr::Goto(1),
            Instr::End,
        ];
        assert!(!branches(&body).contains_key(&1), "回边携带相反值时必须保留两条边");
    }

    #[test]
    fn constant_knowledge_does_not_survive_opaque_calls_resets_or_indirect_writes() {
        let source = SourceLoc::unknown();
        let reset: Reset<B64> = Arc::new(|_, _, _| Ok(Val::Bool(false)));
        for effect in [
            Instr::Call(Loc::Id(name(2)), false, name(9), vec![Exp::Ref(name(1))], source),
            Instr::Copy(Loc::Addr(Box::new(Loc::Id(name(2)))), Exp::Bool(true), source),
            Instr::Copy(Loc::Field(Box::new(Loc::Addr(Box::new(Loc::Id(name(2))))), name(3)), Exp::Bool(true), source),
            Instr::PrimopReset(Loc::Id(name(2)), reset, primop::Effect::Pure, source),
        ] {
            let body = vec![
                Instr::Init(name(1), Ty::Bool, Exp::Bool(false), source),
                effect,
                jump(name(1), 4),
                Instr::End,
                Instr::End,
            ];
            assert!(!branches(&body).contains_key(&2));
        }
        let body = vec![copy(false), jump(name(1), 3), Instr::End, Instr::End];
        assert!(branches(&body).is_empty(), "未声明的全局槽不能获得局部常量知识");
    }
}
