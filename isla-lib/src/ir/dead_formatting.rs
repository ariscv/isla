//! 删除断言转跳转后不再被读取的、在合法输入类型上全定义的字符串格式化。
//! 不删除其他纯运算：它们可能有除零、越界或外部状态等可观察行为。

use super::{label_instrs, unlabel_instrs, Def, Exp, Instr, Loc, Name, Ty, RETURN};
use crate::bitvector::BV;
use std::collections::{HashMap, HashSet};

fn reads(exp: &Exp<Name>, names: &mut HashSet<Name>) {
    match exp {
        // 地址可能传给其他消费者，必须与普通读取一样保留对应的赋值。
        Exp::Id(name) | Exp::Ref(name) => {
            names.insert(*name);
        }
        Exp::Kind(_, exp) | Exp::Unwrap(_, exp) | Exp::Field(exp, _) => reads(exp, names),
        Exp::Call(_, args) => args.iter().for_each(|arg| reads(arg, names)),
        Exp::Struct(_, fields) => fields.iter().for_each(|(_, exp)| reads(exp, names)),
        _ => (),
    }
}

pub(super) fn remove_dead_formatting<B: BV>(defs: &mut [Def<Name, B>]) {
    let implemented: HashSet<_> = defs
        .iter()
        .filter_map(|def| match def {
            Def::Fn(name, ..) => Some(*name),
            _ => None,
        })
        .collect();
    let formatters: HashMap<_, _> = defs
        .iter()
        .filter_map(|def| match def {
            Def::Extern(name, false, op, args, Ty::String) if !implemented.contains(name) => {
                let total = match op.as_str() {
                    "concat_str" => args == &[Ty::String, Ty::String],
                    "dec_str" | "hex_str" | "string_of_int" => matches!(args.as_slice(), [Ty::I64 | Ty::I128]),
                    "string_of_bits" | "decimal_string_of_bits" => {
                        matches!(args.as_slice(), [Ty::Bits(_) | Ty::AnyBits])
                    }
                    _ => false,
                };
                if total {
                    assert_eq!(crate::primop::effect(op), Some(crate::primop::Effect::Pure));
                    Some((*name, args.len()))
                } else {
                    None
                }
            }
            _ => None,
        })
        .collect();
    if formatters.is_empty() {
        return;
    }
    for def in defs {
        let Def::Fn(_, _, body) = def else { continue };
        let targets: HashSet<_> = body
            .iter()
            .filter_map(|instr| match instr {
                Instr::Jump(_, target, _) | Instr::Goto(target) => Some(*target),
                _ => None,
            })
            .collect();
        let mut strings = HashSet::new();
        let mut candidates = HashMap::new();
        let mut dependencies = vec![HashSet::new(); body.len()];
        let mut live = HashSet::from([RETURN]);
        for (pc, instr) in body.iter().enumerate() {
            // 只删除同一基本块内已有字符串槽位的赋值，不能误删全局写入，
            // 也不能假定跳转绕过的声明已执行。
            if targets.contains(&pc) {
                strings.clear();
            }
            match instr {
                Instr::Decl(name, ty, _) | Instr::Init(name, ty, _, _) => {
                    strings.remove(name);
                    if *ty == Ty::String {
                        strings.insert(*name);
                    }
                }
                Instr::Call(Loc::Id(name), false, function, args, _)
                    if strings.contains(name) && formatters.get(function) == Some(&args.len()) =>
                {
                    candidates.insert(pc, *name);
                }
                _ => (),
            }
            let used = &mut dependencies[pc];
            let destination = match instr {
                Instr::Init(_, _, exp, _) | Instr::Jump(exp, _, _) => {
                    reads(exp, used);
                    None
                }
                Instr::Copy(loc, exp, _) | Instr::PrimopUnary(loc, _, exp, _) => {
                    reads(exp, used);
                    Some(loc)
                }
                Instr::Call(loc, _, _, args, _) | Instr::PrimopVariadic(loc, _, args, _) => {
                    args.iter().for_each(|arg| reads(arg, used));
                    Some(loc)
                }
                Instr::PrimopBinary(loc, _, lhs, rhs, _) => {
                    reads(lhs, used);
                    reads(rhs, used);
                    Some(loc)
                }
                Instr::PrimopReset(loc, ..) => Some(loc),
                Instr::Monomorphize(name, ..) => {
                    used.insert(*name);
                    None
                }
                _ => None,
            };
            if let Some(Loc::Field(..) | Loc::Addr(_)) = destination {
                used.insert(destination.unwrap().id());
            }
            if !candidates.contains_key(&pc) {
                live.extend(used.iter().copied());
            }
            if matches!(instr, Instr::Jump(..) | Instr::Goto(_) | Instr::Exit(..) | Instr::End | Instr::Arbitrary) {
                strings.clear();
            }
        }
        loop {
            let before = live.len();
            for (pc, name) in &candidates {
                if live.contains(name) {
                    live.extend(dependencies[*pc].iter().copied());
                }
            }
            if live.len() == before {
                break;
            }
        }
        let dead: HashSet<_> =
            candidates.into_iter().filter_map(|(pc, name)| (!live.contains(&name)).then_some(pc)).collect();
        if dead.is_empty() {
            continue;
        }
        assert!(dead.is_disjoint(&targets), "不能删除跳转目标");
        // 沿用现有标签转换重定位所有跳转，不引入额外的空跳转或改变循环结构。
        *body = unlabel_instrs(
            label_instrs(std::mem::take(body))
                .into_iter()
                .enumerate()
                .filter_map(|(pc, instr)| (!dead.contains(&pc)).then_some(instr))
                .collect(),
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::source_loc::SourceLoc;

    fn fixture(body: Vec<Instr<Name, B64>>, op: &str) -> Vec<Def<Name, B64>> {
        vec![
            Def::Extern(Name::from_u32(10), false, op.into(), vec![Ty::I128], Ty::String),
            Def::Fn(Name::from_u32(11), vec![], body),
        ]
    }

    fn format() -> Instr<Name, B64> {
        Instr::Call(Loc::Id(Name::from_u32(12)), false, Name::from_u32(10), vec![Exp::I128(7)], SourceLoc::unknown())
    }

    fn call_count(defs: &[Def<Name, B64>]) -> usize {
        defs.iter()
            .map(|def| match def {
                Def::Fn(_, _, body) => body.iter().filter(|instr| matches!(instr, Instr::Call(..))).count(),
                _ => 0,
            })
            .sum()
    }

    #[test]
    fn dead_formatting_keeps_references_global_writes_and_jump_entries() {
        let message = Name::from_u32(12);
        let source = SourceLoc::unknown();
        let decl = || Instr::Decl(message, Ty::String, source);
        for body in [
            vec![
                decl(),
                format(),
                Instr::Call(Loc::Id(RETURN), false, Name::from_u32(99), vec![Exp::Ref(message)], source),
                Instr::End,
            ],
            vec![format(), Instr::End],
            vec![decl(), Instr::Jump(Exp::Bool(true), 2, source), format(), Instr::End],
            vec![
                decl(),
                format(),
                Instr::Copy(Loc::Addr(Box::new(Loc::Id(message))), Exp::String("changed".into()), source),
                Instr::End,
            ],
        ] {
            let mut defs = fixture(body, "dec_str");
            let before = call_count(&defs);
            remove_dead_formatting(&mut defs);
            assert_eq!(call_count(&defs), before, "逃逸地址、全局写入和绕过声明的入口均不得误删");
        }
    }

    #[test]
    fn dead_formatting_keeps_unknown_abstract_and_implemented_externs() {
        let message = Name::from_u32(12);
        let body = || vec![Instr::Decl(message, Ty::String, SourceLoc::unknown()), format(), Instr::End];
        for op in ["string_subrange", "model_specific_formatter"] {
            let mut defs = fixture(body(), op);
            remove_dead_formatting(&mut defs);
            assert_eq!(call_count(&defs), 1, "不能以纯函数名义删除可能报错或不透明的运算");
        }
        let mut abstract_defs = fixture(body(), "dec_str");
        let Def::Extern(_, flag, ..) = &mut abstract_defs[0] else { panic!("必须是extern") };
        *flag = true;
        remove_dead_formatting(&mut abstract_defs);
        assert_eq!(call_count(&abstract_defs), 1);
        let mut implemented = fixture(body(), "dec_str");
        implemented.push(Def::Fn(Name::from_u32(10), vec![], vec![Instr::End]));
        remove_dead_formatting(&mut implemented);
        assert_eq!(call_count(&implemented), 1, "模型自己实现的函数不按原语语义消除");
    }
}
