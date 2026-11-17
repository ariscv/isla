//! 默认执行路径不调用的纯函数摘要准入分析。
use super::*;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AssertionCondition {
    Concrete(bool),
    Symbolic,
    Pessimistic,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PureFunction {
    pub registers: BTreeSet<Name>,
    pub lets: BTreeSet<Name>,
    pub writes: BTreeSet<Name>,
    pub calls: BTreeSet<Name>,
    pub assertions: BTreeMap<(Name, usize), AssertionCondition>,
    pub externals: BTreeSet<String>,
    pub rejections: BTreeSet<String>,
    pub has_back_edge: bool,
    pub terminates: bool,
}
impl PureFunction {
    pub fn accepted(&self) -> bool {
        self.rejections.is_empty()
    }
}

// 只传播已知的布尔／整数值；其余表达式保持未知，不执行宿主原语。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Constant {
    Bool(bool),
    I64(i64),
    I128(i128),
}

fn constant(exp: &Exp<Name>, facts: &HashMap<Name, Constant>) -> Option<Constant> {
    use Constant::*;
    match exp {
        Exp::Bool(v) => Some(Bool(*v)),
        Exp::I64(v) => Some(I64(*v)),
        Exp::I128(v) => Some(I128(*v)),
        Exp::Id(id) => facts.get(id).copied(),
        Exp::Call(Op::Not, args) => match args.as_slice() {
            [a] => match constant(a, facts)? {
                Bool(v) => Some(Bool(!v)),
                _ => None,
            },
            _ => None,
        },
        Exp::Call(op, args) if args.len() == 2 => {
            let a = constant(&args[0], facts)?;
            let b = constant(&args[1], facts)?;
            match (op, a, b) {
                (Op::Eq, a, b) => Some(Bool(a == b)),
                (Op::Neq, a, b) => Some(Bool(a != b)),
                (Op::And, Bool(a), Bool(b)) => Some(Bool(a && b)),
                (Op::Or, Bool(a), Bool(b)) => Some(Bool(a || b)),
                (Op::Lt, I64(a), I64(b)) => Some(Bool(a < b)),
                (Op::Gt, I64(a), I64(b)) => Some(Bool(a > b)),
                (Op::Lteq, I64(a), I64(b)) => Some(Bool(a <= b)),
                (Op::Gteq, I64(a), I64(b)) => Some(Bool(a >= b)),
                (Op::Add, I64(a), I64(b)) => a.checked_add(b).map(I64),
                (Op::Sub, I64(a), I64(b)) => a.checked_sub(b).map(I64),
                _ => None,
            }
        }
        _ => None,
    }
}

fn unary<B: BV>(f: crate::primop::Unary<B>, arg: Option<Constant>) -> Option<Constant> {
    let registry = crate::primop::unary_primops::<B>();
    let is = |name: &str| std::ptr::fn_addr_eq(f, registry[name]);
    match arg? {
        Constant::I64(v) if is("%i64->%i") => Some(Constant::I128(v as i128)),
        Constant::I128(v) if is("%i->%i64") => i64::try_from(v).ok().map(Constant::I64),
        Constant::Bool(v) if is("not") => Some(Constant::Bool(!v)),
        _ => None,
    }
}
fn binary<B: BV>(f: crate::primop::Binary<B>, a: Option<Constant>, b: Option<Constant>) -> Option<Constant> {
    let registry = crate::primop::binary_primops::<B>();
    let is = |name: &str| std::ptr::fn_addr_eq(f, registry[name]);
    match (a?, b?) {
        (Constant::I128(a), Constant::I128(b)) => {
            let v = if is("lt") {
                a < b
            } else if is("gt") {
                a > b
            } else if is("lteq") {
                a <= b
            } else if is("gteq") {
                a >= b
            } else if is("eq_int") {
                a == b
            } else {
                return None;
            };
            Some(Constant::Bool(v))
        }
        _ => None,
    }
}

fn expressions<B>(instr: &Instr<Name, B>) -> Vec<&Exp<Name>> {
    match instr {
        Instr::Init(_, _, a, _) | Instr::Copy(_, a, _) | Instr::Jump(a, _, _) | Instr::PrimopUnary(_, _, a, _) => {
            vec![a]
        }
        Instr::PrimopBinary(_, _, a, b, _) => vec![a, b],
        Instr::Call(_, _, _, args, _) | Instr::PrimopVariadic(_, _, args, _) => args.iter().collect(),
        _ => vec![],
    }
}
fn destination<B>(instr: &Instr<Name, B>) -> Option<&Loc<Name>> {
    match instr {
        Instr::Copy(loc, ..)
        | Instr::Call(loc, ..)
        | Instr::PrimopUnary(loc, ..)
        | Instr::PrimopBinary(loc, ..)
        | Instr::PrimopVariadic(loc, ..)
        | Instr::PrimopReset(loc, ..) => Some(loc),
        _ => None,
    }
}
fn has_reference(exp: &Exp<Name>) -> bool {
    match exp {
        Exp::Ref(_) | Exp::Undefined(_) => true,
        Exp::Struct(_, fields) => fields.iter().any(|(_, e)| has_reference(e)),
        Exp::Kind(_, e) | Exp::Unwrap(_, e) | Exp::Field(e, _) => has_reference(e),
        Exp::Call(_, args) => args.iter().any(has_reference),
        _ => false,
    }
}
fn indirect(loc: &Loc<Name>) -> bool {
    match loc {
        Loc::Id(_) => false,
        Loc::Field(loc, _) => indirect(loc),
        Loc::Addr(_) => true,
    }
}
fn reference_type(ty: &Ty<Name>, types: &IRTypeInfo, seen: &mut HashSet<Name>) -> bool {
    match ty {
        Ty::Ref(_) => true,
        Ty::Vector(t) | Ty::FixedVector(_, t) | Ty::List(t) => reference_type(t, types, seen),
        Ty::Struct(n) if seen.insert(*n) => types.structs[n].values().any(|t| reference_type(t, types, seen)),
        Ty::Union(n) if seen.insert(*n) => types.unions[n].iter().any(|(_, t)| reference_type(t, types, seen)),
        _ => false,
    }
}

/// 所有已加载函数的传递摘要。配置事实只能来自不可变 let，不能传入调用点条件。
/// 纯度准入与终止证明分开：有界执行仍须自行证明正常域和处理预算失败。
pub fn analyze<B: BV>(
    shared: &SharedState<B>,
    lets: &Bindings<B>,
    relaxed: &HashSet<Name>,
) -> HashMap<Name, PureFunction> {
    analyze_from(shared, lets, relaxed, &shared.functions.keys().copied().collect())
}

/// 仅分析给定入口的完整传递调用闭包，供大型 IR 的定向诊断使用。
pub fn analyze_from<B: BV>(
    shared: &SharedState<B>,
    lets: &Bindings<B>,
    relaxed: &HashSet<Name>,
    roots: &BTreeSet<Name>,
) -> HashMap<Name, PureFunction> {
    let mut selected = BTreeSet::new();
    let mut pending: Vec<_> = roots.iter().copied().collect();
    while let Some(name) = pending.pop() {
        if selected.insert(name) {
            for instr in shared.functions[&name].2 {
                if let Instr::Call(_, _, callee, _, _) = instr {
                    if shared.functions.contains_key(callee) {
                        pending.push(*callee);
                    }
                }
            }
        }
    }
    use crate::ir::regions::{RegionCfg, RegionOptions, RegionPoint};
    use crate::primop::{self, Effect};
    let constants: HashMap<_, _> = lets
        .iter()
        .filter_map(|(n, v)| match v {
            UVal::Init(Val::Bool(v)) => Some((*n, Constant::Bool(*v))),
            UVal::Init(Val::I64(v)) => Some((*n, Constant::I64(*v))),
            UVal::Init(Val::I128(v)) => Some((*n, Constant::I128(*v))),
            _ => None,
        })
        .collect();
    let assumed: HashSet<_> = shared.function_assumptions.iter().filter_map(|(n, _, _)| shared.symtab.get(n)).collect();
    let mut primop_names: HashMap<usize, BTreeSet<String>> = HashMap::new();
    for (n, f) in primop::unary_primops::<B>() {
        primop_names.entry(f as usize).or_default().insert(n);
    }
    for (n, f) in primop::binary_primops::<B>() {
        primop_names.entry(f as usize).or_default().insert(n);
    }
    for (n, f) in primop::variadic_primops::<B>() {
        primop_names.entry(f as usize).or_default().insert(n);
    }
    let mut summaries = HashMap::new();
    let mut cfgs = HashMap::new();
    for function in &selected {
        let (params, ret, body) = &shared.functions[function];
        let cfg = RegionCfg::new(body, RegionOptions::default());
        let reachable = cfg.reachable_instructions();
        let locals: HashSet<_> = params
            .iter()
            .map(|(n, _)| *n)
            .chain([RETURN])
            .chain(body.iter().filter_map(|i| match i {
                Instr::Decl(n, ..) | Instr::Init(n, ..) => Some(*n),
                _ => None,
            }))
            .collect();
        // CFG 上的交集不动点，不沿调用点的前态裁剪任何臂。
        let mut states = vec![None::<HashMap<Name, Constant>>; body.len()];
        if !body.is_empty() {
            let mut used = HashSet::new();
            for instr in *body {
                for exp in expressions(instr) {
                    exp.collect_ids(&mut used);
                }
            }
            states[0] = Some(
                constants
                    .iter()
                    .filter(|(n, _)| used.contains(n) && !locals.contains(n))
                    .map(|(n, v)| (*n, *v))
                    .collect(),
            );
        }
        let mut pending = std::collections::VecDeque::from_iter((!body.is_empty()).then_some(0));
        while let Some(pc) = pending.pop_front() {
            let mut facts = states[pc].clone().unwrap();
            let instr = &body[pc];
            let value = match instr {
                Instr::Init(_, _, exp, _) | Instr::Copy(_, exp, _) => constant(exp, &facts),
                Instr::PrimopUnary(_, f, exp, _) => unary(*f, constant(exp, &facts)),
                Instr::PrimopBinary(_, f, a, b, _) => binary(*f, constant(a, &facts), constant(b, &facts)),
                _ => None,
            };
            let assignment = destination(instr).map(Loc::id).or_else(|| match instr {
                Instr::Decl(n, ..) | Instr::Init(n, ..) | Instr::Monomorphize(n, ..) => Some(*n),
                _ => None,
            });
            if let Some(n) = assignment {
                facts.remove(&n);
                if let Some(v) = value {
                    if destination(instr).map_or(true, |loc| matches!(loc, Loc::Id(_))) {
                        facts.insert(n, v);
                    }
                }
            }
            for (next, _) in cfg.successors(pc) {
                if let RegionPoint::Instruction(next) = next {
                    let changed = match &mut states[next] {
                        None => {
                            states[next] = Some(facts.clone());
                            true
                        }
                        Some(old) => {
                            let len = old.len();
                            old.retain(|n, v| facts.get(n) == Some(v));
                            old.len() != len
                        }
                    };
                    if changed {
                        pending.push_back(next);
                    }
                }
            }
        }
        let mut result = PureFunction::default();
        if assumed.contains(function) {
            result.rejections.insert("函数假设替代了函数体".into());
        }
        if params
            .iter()
            .map(|(_, t)| *t)
            .chain([*ret])
            .any(|t| reference_type(t, &shared.type_info, &mut HashSet::new()))
        {
            result.rejections.insert(format!("{:?}: 引用类型", function));
        }
        for pc in reachable {
            let instr = &body[pc];
            let reject = |reason: &str| {
                format!("{}@{}: {}", crate::zencode::decode(shared.symtab.to_str(*function)), pc, reason)
            };
            result.has_back_edge |=
                cfg.successors(pc).any(|(n, _)| matches!(n, RegionPoint::Instruction(n) if n <= pc));
            for exp in expressions(instr) {
                if has_reference(exp) {
                    result.rejections.insert(reject("引用逃逸或不确定值"));
                }
                let mut ids = HashSet::new();
                exp.collect_ids(&mut ids);
                for id in ids.difference(&locals) {
                    if shared.registers.contains_key(id) {
                        result.registers.insert(*id);
                        if relaxed.contains(id) {
                            result.rejections.insert(reject("relaxed 寄存器"));
                        }
                    } else if lets.contains_key(id) {
                        result.lets.insert(*id);
                    } else if !shared.type_info.enum_members.contains_key(id) {
                        result.rejections.insert(reject("未知全局读取"));
                    }
                }
            }
            if let Instr::Monomorphize(id, ..) = instr {
                if !locals.contains(id) {
                    result.rejections.insert(reject("全局具体化"));
                }
            }
            if let Some(loc) = destination(instr) {
                if indirect(loc) {
                    result.rejections.insert(reject("间接写或未知别名"));
                }
                if !locals.contains(&loc.id()) {
                    result.writes.insert(loc.id());
                    result.rejections.insert(reject("全局写"));
                }
            }
            // 断言单独分类，不以 WritesState 一律拒绝具体 false 死臂。
            let assertion = match instr {
                Instr::Call(_, _, name, args, _) if *name == SAIL_ASSERT => Some((&args[0], false)),
                Instr::PrimopBinary(_, f, arg, _, _)
                    if std::ptr::fn_addr_eq(*f, primop::optimistic_assert::<B> as primop::Binary<B>) =>
                {
                    Some((arg, false))
                }
                Instr::PrimopBinary(_, f, arg, _, _)
                    if std::ptr::fn_addr_eq(*f, primop::pessimistic_assert::<B> as primop::Binary<B>) =>
                {
                    Some((arg, true))
                }
                _ => None,
            };
            if let Some((arg, pessimistic)) = assertion {
                let kind = if pessimistic {
                    AssertionCondition::Pessimistic
                } else {
                    match states[pc].as_ref().and_then(|facts| constant(arg, facts)) {
                        Some(Constant::Bool(v)) => AssertionCondition::Concrete(v),
                        _ => AssertionCondition::Symbolic,
                    }
                };
                result.assertions.insert((*function, pc), kind);
                if !matches!(kind, AssertionCondition::Concrete(_)) {
                    result.rejections.insert(reject("符号或悲观断言"));
                }
            } else {
                let effect = crate::executor::region_summary::direct_effect(instr, shared);
                if !matches!(effect, Effect::Pure) {
                    result.rejections.insert(reject(&format!("原语效应 {:?}", effect)));
                }
            }
            match instr {
                Instr::Call(_, _, callee, _, _) if shared.functions.contains_key(callee) => {
                    result.calls.insert(*callee);
                }
                Instr::Call(_, _, callee, _, _) => {
                    result.externals.insert(
                        shared
                            .externs
                            .get(callee)
                            .map(|(_, _, name)| name.to_string())
                            .unwrap_or_else(|| crate::zencode::decode(shared.symtab.to_str(*callee))),
                    );
                }
                Instr::PrimopUnary(..)
                | Instr::PrimopBinary(..)
                | Instr::PrimopVariadic(..)
                | Instr::PrimopReset(..) => {
                    let pointer = match instr {
                        Instr::PrimopUnary(_, f, ..) => Some(*f as usize),
                        Instr::PrimopBinary(_, f, ..) => Some(*f as usize),
                        Instr::PrimopVariadic(_, f, ..) => Some(*f as usize),
                        _ => None,
                    };
                    result.externals.insert(format!(
                        "{}@{} {:?}",
                        crate::zencode::decode(shared.symtab.to_str(*function)),
                        pc,
                        pointer.and_then(|p| primop_names.get(&p))
                    ));
                }
                Instr::Exit(..) | Instr::Arbitrary => {
                    result.rejections.insert(reject("未支持的终止"));
                }
                _ => (),
            }
        }
        cfgs.insert(*function, cfg);
        summaries.insert(*function, result);
    }
    let mut graph = petgraph::graph::DiGraph::<Name, ()>::new();
    let nodes: HashMap<_, _> = selected.iter().map(|n| (*n, graph.add_node(*n))).collect();
    for (n, s) in &summaries {
        for c in &s.calls {
            graph.add_edge(nodes[n], nodes[c], ());
        }
    }
    for component in petgraph::algo::kosaraju_scc(&graph) {
        if component.len() > 1 || component.iter().any(|n| graph.contains_edge(*n, *n)) {
            for n in component {
                summaries.get_mut(&graph[n]).unwrap().rejections.insert("递归调用".into());
            }
        }
    }
    loop {
        let mut changed = false;
        for function in &selected {
            let before = summaries[function].clone();
            let mut result = before.clone();
            for callee in &before.calls {
                let other = &summaries[callee];
                result.registers.extend(&other.registers);
                result.lets.extend(&other.lets);
                result.writes.extend(&other.writes);
                result.assertions.extend(&other.assertions);
                result.externals.extend(other.externals.iter().cloned());
                result.rejections.extend(other.rejections.iter().cloned());
                result.has_back_edge |= other.has_back_edge;
            }
            if !result.terminates {
                let terminating = summaries.iter().map(|(n, s)| (*n, s.terminates)).collect();
                result.terminates = cfgs[function].always_terminates(
                    shared.functions[function].2,
                    HAVE_EXCEPTION,
                    &HashSet::new(),
                    &terminating,
                    true,
                );
            }
            changed |= before != result;
            summaries.insert(*function, result);
        }
        if !changed {
            break;
        }
    }
    summaries
}

#[cfg(test)]
mod tests;
