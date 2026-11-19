//! 声明式线性化策略：在改写前检查封闭纯标量资格和成本。
use super::ssa::{Terminator, CFG};
use super::*;
use crate::config::allowed_table_keys;
use crate::primop::{binary_primops, unary_primops, variadic_primops};
use toml::Value;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinearizeStrategy {
    None,
    Full,
    Bounded { max_branches: usize, max_instructions: usize },
}

/// 参数名、参数类型和函数体；参数类型来自对应的 Val 定义。
pub type FunctionDefinition<B> = (Vec<Name>, Vec<Ty<Name>>, Vec<Instr<Name, B>>);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LinearizeCost {
    pub branches: usize,
    pub instructions: usize,
}

pub fn evaluate_cost<B: BV>(body: &[Instr<Name, B>]) -> LinearizeCost {
    let cfg = CFG::new(&prune_labels(label_instrs(body.to_vec())));
    LinearizeCost {
        branches: cfg
            .graph
            .node_indices()
            .map(|ix| &cfg.graph[ix])
            .filter(|block| matches!(block.terminator, Terminator::Jump(..)))
            .count(),
        instructions: cfg
            .graph
            .node_indices()
            .map(|ix| &cfg.graph[ix])
            .map(|block| block.instrs.len() + usize::from(!matches!(block.terminator, Terminator::Continue)))
            .sum(),
    }
}

pub fn verify_closed_scalar_safety<B: BV>(
    fn_def: &FunctionDefinition<B>,
    ret_ty: &Ty<Name>,
    symtab: &Symtab,
) -> Result<(), String> {
    let (args, arg_tys, body) = fn_def;
    assert_eq!(args.len(), arg_tys.len(), "函数参数与类型数量不一致");
    let scalar = |ty: &Ty<Name>| matches!(ty, Ty::Bool | Ty::Bits(_));
    if !scalar(ret_ty) || arg_tys.iter().any(|ty| !scalar(ty)) {
        return Err("入参和返回值必须仅为 Bool 或 Bits".into());
    }
    let cfg = CFG::new(&prune_labels(label_instrs(body.to_vec())));
    if petgraph::algo::toposort(&cfg.graph, None).is_err() {
        return Err("控制流图包含循环".into());
    }
    let mut types = cfg.all_vars_typed(ret_ty);
    types.extend(args.iter().copied().zip(arg_tys.iter().cloned()));
    if types.values().any(|ty| !scalar(ty)) {
        return Err("CFG 变量必须仅为 Bool 或 Bits".into());
    }
    // 仅接受已审核的纯标量 primop；不能将整个 primop 注册表当成纯函数表。
    let unary = unary_primops::<B>();
    let binary = binary_primops::<B>();
    let variadic = variadic_primops::<B>();
    let pure_unary = ["not", "not_bits", "length", "zeros", "ones", "bit_to_bool"];
    let pure_binary = [
        "and_bool",
        "strict_and_bool",
        "or_bool",
        "strict_or_bool",
        "eq_bool",
        "eq_bits",
        "neq_bits",
        "xor_bits",
        "or_bits",
        "and_bits",
        "add_bits",
        "sub_bits",
        "zero_extend",
        "sign_extend",
        "sail_truncate",
        "sail_truncateLSB",
        "replicate_bits",
        "shiftr",
        "shiftl",
        "arith_shiftr",
        "shift_bits_right",
        "shift_bits_left",
        "append",
        "append_64",
        "eq_anything",
    ];
    let pure_variadic = ["slice", "bitvector_update", "set_slice", "ite"];
    for instr in body {
        let mut destination = None;
        let mut expressions = Vec::new();
        match instr {
            Instr::Monomorphize(..) => return Err("封闭纯标量安全门拒绝包含 Monomorphize 的函数".into()),
            Instr::Decl(_, ty, _) => {
                if !scalar(ty) {
                    return Err("局部变量必须仅为 Bool 或 Bits".into());
                }
            }
            Instr::Init(_, ty, exp, _) => {
                if !scalar(ty) {
                    return Err("局部变量必须仅为 Bool 或 Bits".into());
                }
                expressions.push(exp);
            }
            Instr::Copy(loc, exp, _) => {
                destination = Some(loc);
                expressions.push(exp);
            }
            Instr::Jump(exp, _, _) => expressions.push(exp),
            Instr::PrimopUnary(loc, op, exp, _) => {
                if !pure_unary.iter().any(|name| unary.get(*name).map(|f| *f as usize) == Some(*op as usize)) {
                    return Err("未获准的 unary primop（可能含副作用或断言）".into());
                }
                destination = Some(loc);
                expressions.push(exp);
            }
            Instr::PrimopBinary(loc, op, lhs, rhs, _) => {
                if !pure_binary.iter().any(|name| binary.get(*name).map(|f| *f as usize) == Some(*op as usize)) {
                    return Err("未获准的 binary primop（可能含副作用或断言）".into());
                }
                destination = Some(loc);
                expressions.extend([lhs, rhs]);
            }
            Instr::PrimopVariadic(loc, op, exps, _) => {
                if !pure_variadic.iter().any(|name| variadic.get(*name).map(|f| *f as usize) == Some(*op as usize)) {
                    return Err("未获准的 variadic primop（可能访问内存）".into());
                }
                destination = Some(loc);
                expressions.extend(exps);
            }
            Instr::Call(_, _, name, _, _) => {
                return Err(format!(
                    "不接受未解析的调用或活动断言：{}；纯 primop 须先解析为 Primop 指令",
                    symtab.to_str(*name)
                ))
            }
            Instr::PrimopReset(..) | Instr::Exit(..) | Instr::Arbitrary => {
                return Err("不接受重置、退出或任意返回".into())
            }
            Instr::Goto(_) | Instr::End => (),
        }
        if let Some(loc) = destination {
            match loc {
                Loc::Id(id) if args.contains(id) => return Err("函数形参不可重新赋值".into()),
                Loc::Id(id) if types.contains_key(id) => (),
                _ => return Err("不接受全局寄存器、内存或复合位置写入".into()),
            }
        }
        while let Some(exp) = expressions.pop() {
            match exp {
                Exp::Id(id) if types.contains_key(id) => (),
                Exp::Bool(_) | Exp::Bits(_) | Exp::I64(_) | Exp::I128(_) => (),
                Exp::Call(Op::Head | Op::Tail | Op::IsEmpty, _) => return Err("不接受复合类型运算".into()),
                Exp::Call(_, exps) => expressions.extend(exps),
                _ => return Err("表达式不是封闭纯标量表达式".into()),
            }
        }
    }
    Ok(())
}

pub fn should_linearize<B: BV>(
    fn_def: &FunctionDefinition<B>,
    ret_ty: &Ty<Name>,
    strategy: LinearizeStrategy,
    symtab: &Symtab,
) -> Result<bool, String> {
    if strategy == LinearizeStrategy::None {
        return Ok(false);
    }
    if let Err(reason) = verify_closed_scalar_safety(fn_def, ret_ty, symtab) {
        if strategy == LinearizeStrategy::Full {
            return Err(reason);
        }
        eprintln!("线性化 bounded 保留原 IR：安全资格检查失败：{}", reason);
        return Ok(false);
    }
    if let LinearizeStrategy::Bounded { max_branches, max_instructions } = strategy {
        let cost = evaluate_cost(&fn_def.2);
        if cost.branches > max_branches || cost.instructions > max_instructions {
            eprintln!(
                "线性化 bounded 保留原 IR：分支 {}/{}，指令 {}/{}",
                cost.branches, max_branches, cost.instructions, max_instructions
            );
            return Ok(false);
        }
    }
    Ok(true)
}

/// 通用函数线性化配置，目标名在加载时编码一次。
#[derive(Debug, Clone)]
struct LinearizeConfig {
    verify: bool,
    targets: HashMap<Name, crate::ir::linearize_policy::LinearizeStrategy>,
}

impl Default for LinearizeConfig {
    fn default() -> Self {
        Self { verify: true, targets: HashMap::new() }
    }
}

impl LinearizeConfig {
    fn parse(config: &Value, symtab: &Symtab) -> Result<Self, String> {
        let mut parsed = Self::default();
        let value = match config.get("linearize") {
            None => return Ok(parsed),
            Some(value) => value,
        };
        let table = value.as_table().ok_or("linearize 必须是表")?;
        allowed_table_keys(table, "linearize", &["verify", "targets"])?;
        if let Some(value) = table.get("verify") {
            parsed.verify = value.as_bool().ok_or("linearize.verify 必须是布尔值")?;
        }
        if let Some(value) = table.get("targets") {
            for target in value.as_array().ok_or("linearize.targets 必须是表数组")? {
                let target = target.as_table().ok_or("linearize.targets 元素必须是表")?;
                allowed_table_keys(
                    target,
                    "linearize.targets",
                    &["function", "strategy", "max_branches", "max_instructions"],
                )?;
                let function =
                    target.get("function").and_then(Value::as_str).ok_or("linearize 目标缺少字符串 function")?;
                let name = symtab
                    .get(&zencode::encode(function))
                    .ok_or_else(|| format!("linearize 目标函数不存在：{}", function))?;
                let strategy =
                    target.get("strategy").and_then(Value::as_str).ok_or("linearize 目标缺少字符串 strategy")?;
                let limit = |key: &str| -> Result<usize, String> {
                    let n = target
                        .get(key)
                        .and_then(Value::as_integer)
                        .ok_or_else(|| format!("linearize.{} 必须是非负整数", key))?;
                    usize::try_from(n).map_err(|_| format!("linearize.{} 为负数或溢出", key))
                };
                let strategy = match strategy {
                    "bounded" => LinearizeStrategy::Bounded {
                        max_branches: limit("max_branches")?,
                        max_instructions: limit("max_instructions")?,
                    },
                    "none" | "full" => {
                        if target.contains_key("max_branches") || target.contains_key("max_instructions") {
                            return Err("只有 bounded 策略允许成本阈值".into());
                        }
                        if strategy == "full" {
                            LinearizeStrategy::Full
                        } else {
                            LinearizeStrategy::None
                        }
                    }
                    other => return Err(format!("未知线性化策略：{}", other)),
                };
                if parsed.targets.insert(name, strategy).is_some() {
                    return Err(format!("重复 linearize 目标：{}", function));
                }
            }
        }
        Ok(parsed)
    }
}

/// 应用 TOML 目标。已有命令行目标由各自的改写入口处理。
pub fn rewrite_configured<B: BV>(
    arch: &mut [Def<Name, B>],
    symtab: &mut Symtab,
    type_info: &IRTypeInfo,
    isa_config: &ISAConfig<B>,
    merged_config: &Value,
    cli_targets: &[Name],
    verify_all: bool,
    num_threads: usize,
) -> Result<(), String> {
    let config = LinearizeConfig::parse(merged_config, symtab)?;
    let mut targets: Vec<_> = config.targets.into_iter().collect();
    targets.sort_by_key(|(name, _)| *name);
    let mut resolved: Vec<_> = arch
        .iter()
        .filter(|definition| match definition {
            Def::Extern(..) => !targets.is_empty(),
            Def::Fn(name, ..) => targets.iter().any(|(target, strategy)| {
                name == target && *strategy != LinearizeStrategy::None && !cli_targets.contains(name)
            }),
            _ => false,
        })
        .cloned()
        .collect();
    if !resolved.is_empty() {
        insert_primops(&mut resolved, symtab, AssertionMode::Pessimistic, isa_config);
    }
    for (target, strategy) in targets {
        if cli_targets.contains(&target) {
            continue;
        }
        let name = zencode::decode(symtab.to_str(target));
        let (arg_tys, ret_ty) = arch
            .iter()
            .find_map(|def| match def {
                Def::Val(f, args, ret) if *f == target => Some((args.clone(), ret.clone())),
                _ => None,
            })
            .ok_or_else(|| format!("线性化目标缺少函数类型：{name}"))?;
        let slot = arch
            .iter()
            .position(|def| matches!(def, Def::Fn(f, ..) if *f == target))
            .ok_or_else(|| format!("线性化目标缺少函数体：{name}"))?;
        if strategy == LinearizeStrategy::None {
            continue;
        }
        let (args, body) = resolved
            .iter()
            .find_map(|def| match def {
                Def::Fn(f, args, body) if *f == target => Some((args.clone(), body.clone())),
                _ => None,
            })
            .expect("待改写目标必须已解析原语");
        let definition = (args, arg_tys, body);
        if !should_linearize(&definition, &ret_ty, strategy, symtab)
            .map_err(|reason| format!("函数 {name} 线性化安全资格检查失败：{reason}"))?
        {
            continue;
        }
        let Def::Fn(_, _, original) = &arch[slot] else { unreachable!() };
        let rewritten = partial_linearize::partial_linearize(original.clone(), &ret_ty, symtab);
        if (config.verify || verify_all)
            && !linearize::self_test(
                num_threads,
                arch.to_vec(),
                symtab.clone(),
                type_info.clone(),
                isa_config,
                &definition.0,
                &definition.1,
                &ret_ty,
                original.clone(),
                rewritten.clone(),
            )
        {
            return Err(format!("函数 {name} 线性化等价验证失败"));
        }
        let Def::Fn(_, _, body) = &mut arch[slot] else { unreachable!() };
        *body = rewritten;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::source_loc::SourceLoc;

    fn body() -> Vec<Instr<Name, B64>> {
        vec![Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), SourceLoc::unknown()), Instr::End]
    }

    #[test]
    fn scalar_cost_and_strategies() {
        let symtab = Symtab::new();
        let f = (Vec::new(), Vec::new(), body());
        assert_eq!(should_linearize(&f, &Ty::Bool, LinearizeStrategy::Full, &symtab), Ok(true));
        assert_eq!(
            should_linearize(
                &f,
                &Ty::Bool,
                LinearizeStrategy::Bounded { max_branches: 0, max_instructions: 2 },
                &symtab
            ),
            Ok(true)
        );
        assert_eq!(
            should_linearize(
                &f,
                &Ty::Bool,
                LinearizeStrategy::Bounded { max_branches: 0, max_instructions: 1 },
                &symtab
            ),
            Ok(false)
        );
        assert_eq!(should_linearize(&f, &Ty::Bool, LinearizeStrategy::None, &symtab), Ok(false));
    }

    #[test]
    fn branch_limit_and_direct_memory_primop() {
        let mut symtab = Symtab::new();
        let arg = symtab.intern("zarg");
        let s = SourceLoc::unknown();
        let f: FunctionDefinition<B64> = (
            vec![arg],
            vec![Ty::Bool],
            vec![
                Instr::Jump(Exp::Id(arg), 3, s),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), s),
                Instr::Goto(4),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), s),
                Instr::End,
            ],
        );
        assert_eq!(evaluate_cost(&f.2), LinearizeCost { branches: 1, instructions: 5 });
        assert_eq!(
            should_linearize(
                &f,
                &Ty::Bool,
                LinearizeStrategy::Bounded { max_branches: 1, max_instructions: 5 },
                &symtab
            ),
            Ok(true)
        );
        assert_eq!(
            should_linearize(
                &f,
                &Ty::Bool,
                LinearizeStrategy::Bounded { max_branches: 0, max_instructions: 5 },
                &symtab
            ),
            Ok(false)
        );
        let primops = variadic_primops::<B64>();
        let write = (
            vec![],
            vec![],
            vec![Instr::PrimopVariadic(Loc::Id(RETURN), primops["platform_write_mem"], vec![], s), Instr::End],
        );
        assert!(verify_closed_scalar_safety(&write, &Ty::Bool, &symtab).is_err());
        let reads_global = (vec![], vec![], vec![Instr::Copy(Loc::Id(RETURN), Exp::Id(arg), s), Instr::End]);
        assert!(verify_closed_scalar_safety::<B64>(&reads_global, &Ty::Bool, &symtab).is_err());
    }

    #[test]
    fn rejects_composites_cycles_and_effects() {
        let mut symtab = Symtab::new();
        let x = symtab.intern("zx");
        let s = SourceLoc::unknown();
        for ty in [Ty::Union(x), Ty::Struct(x), Ty::Ref(Box::new(Ty::Bool))] {
            let f = (vec![x], vec![ty.clone()], body());
            assert!(verify_closed_scalar_safety(&f, &Ty::Bool, &symtab).is_err());
            let f: FunctionDefinition<B64> = (vec![], vec![], vec![Instr::Decl(x, ty, s), Instr::End]);
            assert!(verify_closed_scalar_safety(&f, &Ty::Bool, &symtab).is_err());
        }
        let write_mem = symtab.intern("zplatform_write_mem");
        for instructions in [
            vec![Instr::Goto(0)],
            vec![Instr::Call(Loc::Id(RETURN), true, write_mem, vec![], s), Instr::End],
            vec![Instr::Copy(Loc::Id(x), Exp::Bool(true), s), Instr::End],
            vec![Instr::Call(Loc::Id(RETURN), true, SAIL_ASSERT, vec![Exp::Bool(true)], s), Instr::End],
        ] {
            let f: FunctionDefinition<B64> = (vec![], vec![], instructions);
            assert!(should_linearize(&f, &Ty::Bool, LinearizeStrategy::Full, &symtab).is_err());
            assert_eq!(
                should_linearize(
                    &f,
                    &Ty::Bool,
                    LinearizeStrategy::Bounded { max_branches: 100, max_instructions: 100 },
                    &symtab
                ),
                Ok(false)
            );
        }
    }
}
