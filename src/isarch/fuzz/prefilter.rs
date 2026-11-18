//! 原路径断言的保守预筛：只排除在给定前态下直接求值为 false 的路径。
//! 不使用样本记录的路径、守卫、期望后态；未知值继续交给完整 judge。
use crate::isarch::resident::ResidentPath;
use isla_lib::{
    bitvector::{b64::B64, BV},
    executor::samples::Sample,
    ir::{SharedState, Val},
    smt::{
        smtlib::{Def, Exp, Ty},
        EnumId, EnumMember, Event, Sym,
    },
    zencode,
};
use std::collections::{HashMap, HashSet};

pub(super) struct Prefilter {
    bindings: Vec<(Sym, Vec<String>)>,
    conditions: Vec<Exp<Sym>>,
    enums: HashMap<String, EnumMember>,
}

fn bounded(exp: &Exp<Sym>) -> bool {
    let mut nodes = 0;
    exp.clone().modify(&mut |_| nodes += 1);
    nodes <= 64
}

impl Prefilter {
    pub(super) fn new<B: BV>(path: &ResidentPath<B>, shared: &SharedState<B>) -> Self {
        let mut filter = Self { bindings: Vec::new(), conditions: Vec::new(), enums: HashMap::new() };
        fn inputs<B: BV>(value: &Val<B>, at: Vec<String>, shared: &SharedState<B>, out: &mut Vec<(Sym, Vec<String>)>) {
            match value {
                Val::Symbolic(symbol) => out.push((*symbol, at)),
                Val::Struct(fields) => {
                    for (name, value) in fields {
                        let mut at = at.clone();
                        at.extend(["struct".into(), zencode::decode(shared.symtab.to_str(*name))]);
                        inputs(value, at, shared, out);
                    }
                }
                Val::Ctor(_, value) => {
                    let mut at = at;
                    at.push("value".into());
                    inputs(value, at, shared, out);
                }
                // 未支持的输入形状不作为预筛事实。
                _ => (),
            }
        }
        for (name, value) in &path.path.pre {
            inputs(value, vec![name.clone()], shared, &mut filter.bindings);
        }
        let Some(trace) = path.checkpoint.trace() else { return filter };
        let events = trace.to_vec();
        let mut declared = HashSet::new();
        let mut enum_types = HashMap::new();
        let input_symbols: HashSet<_> = filter.bindings.iter().map(|(symbol, _)| *symbol).collect();
        // 输入引用最终符号版本。若迹内重绑，早期断言可能属于另一版本，整条路径不预筛。
        for event in events.iter().rev() {
            if let Event::Smt(def, ..) = event {
                if let Def::DeclareConst(symbol, Ty::Enum(id)) = def {
                    enum_types.insert(*symbol, *id);
                }
                let symbol = match def {
                    Def::DeclareConst(symbol, _) | Def::DeclareFun(symbol, ..) => Some(*symbol),
                    Def::DefineConst(symbol, _) => {
                        if input_symbols.contains(symbol) {
                            return Self { bindings: vec![], conditions: vec![], enums: HashMap::new() };
                        }
                        Some(*symbol)
                    }
                    _ => None,
                };
                if symbol.is_some_and(|symbol| !declared.insert(symbol)) {
                    return Self { bindings: vec![], conditions: vec![], enums: HashMap::new() };
                }
            }
        }
        let mut definitions: HashMap<_, _> = input_symbols.iter().map(|symbol| (*symbol, Exp::Var(*symbol))).collect();
        fn condition(exp: &Exp<Sym>, definitions: &HashMap<Sym, Exp<Sym>>, out: &mut Vec<Exp<Sym>>) {
            if out.len() >= 128 {
                return;
            }
            if let Exp::And(left, right) = exp {
                condition(left, definitions, out);
                condition(right, definitions, out);
                return;
            }
            if !bounded(exp) {
                return;
            }
            if let Ok(exp) = exp.map_var(&mut |symbol| definitions.get(symbol).cloned().ok_or(())) {
                if bounded(&exp) {
                    out.push(exp);
                }
            }
        }
        // 固定资源上限只会减少拒绝机会，不能造成漏接纳。
        for event in events.into_iter().rev().take(4096) {
            if let Event::Smt(def, ..) = event {
                match def {
                    Def::DefineConst(symbol, exp) if bounded(exp) => {
                        if let Ok(exp) = exp.map_var(&mut |symbol| definitions.get(symbol).cloned().ok_or(())) {
                            if bounded(&exp) {
                                definitions.insert(*symbol, exp);
                            }
                        }
                    }
                    Def::Assert(exp) => condition(exp, &definitions, &mut filter.conditions),
                    _ => (),
                }
            }
        }
        let used: HashSet<_> = filter.conditions.iter().flat_map(|exp| exp.variables()).collect();
        filter.bindings.retain(|(symbol, _)| used.contains(symbol));
        let needed_enums: Vec<_> = filter.bindings.iter().filter_map(|(symbol, _)| enum_types.get(symbol)).collect();
        for (name, (member, _, id)) in &shared.type_info.enum_members {
            if !needed_enums.contains(&&EnumId::from_name(*id)) {
                continue;
            }
            filter.enums.insert(
                zencode::decode(shared.symtab.to_str(*name)),
                EnumMember { enum_id: EnumId::from_name(*id), member: *member },
            );
        }
        filter
    }

    pub(super) fn rejects(&self, input: &Sample) -> bool {
        let mut known: HashMap<Sym, Exp<Sym>> = HashMap::new();
        for (symbol, at) in &self.bindings {
            let Some(mut value) = input.pre_registers.get(&at[0]) else { continue };
            for field in &at[1..] {
                value = &value[field];
            }
            let constant = if let Some(bits) = value["bits"].as_str() {
                if bits.is_empty() || bits.len() > 64 || !bits.bytes().all(|b| b == b'0' || b == b'1') {
                    continue;
                }
                Exp::Bits64(B64::new(u64::from_str_radix(bits, 2).unwrap(), bits.len() as u32))
            } else if let Some(value) = value["bool"].as_bool() {
                Exp::Bool(value)
            } else if let Some(value) = value["enum"].as_str().and_then(|name| self.enums.get(name)) {
                Exp::Enum(*value)
            } else {
                continue;
            };
            known.insert(*symbol, constant);
        }
        self.conditions.iter().any(|condition| {
            let Ok(mut exp) = condition.map_var(&mut |symbol| known.get(symbol).cloned().ok_or(())) else {
                return false;
            };
            exp.modify(&mut |part| {
                *part = match part {
                    Exp::Bits(bits) if !bits.is_empty() && bits.len() <= 64 => Exp::Bits64(B64::new(
                        bits.iter().rev().fold(0, |value, bit| (value << 1) | u64::from(*bit)),
                        bits.len() as u32,
                    )),
                    Exp::Eq(left, right) => match (&**left, &**right) {
                        (Exp::Enum(a), Exp::Enum(b)) if a.enum_id == b.enum_id => Exp::Bool(a == b),
                        (Exp::Bits64(a), Exp::Bits64(b)) if a.len() == b.len() => Exp::Bool(a == b),
                        (Exp::Bool(a), Exp::Bool(b)) => Exp::Bool(a == b),
                        _ => part.clone().eval(),
                    },
                    Exp::Neq(left, right) => match (&**left, &**right) {
                        (Exp::Enum(a), Exp::Enum(b)) if a.enum_id == b.enum_id => Exp::Bool(a != b),
                        (Exp::Bits64(a), Exp::Bits64(b)) if a.len() == b.len() => Exp::Bool(a != b),
                        (Exp::Bool(a), Exp::Bool(b)) => Exp::Bool(a != b),
                        _ => part.clone().eval(),
                    },
                    _ => part.clone().eval(),
                };
            });
            exp == Exp::Bool(false)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::{
        bitvector::b64::B64,
        executor::samples::SamplePath,
        ir::{Symtab, Val},
        smt::{
            smtlib::{Exp, Ty},
            Config, Context, Solver, Sym,
        },
        source_loc::SourceLoc,
    };
    use serde_json::json;
    use std::collections::BTreeMap;

    fn fixture(solver: &mut Solver<B64>, x: Sym) -> ResidentPath<B64> {
        ResidentPath {
            checkpoint: isla_lib::smt::checkpoint(solver),
            path: SamplePath {
                terminal: Default::default(),
                pre: BTreeMap::from([("input".into(), Val::Symbolic(x))]),
                post: BTreeMap::new(),
                result: Val::Unit,
                memory: vec![],
                memory_guards: BTreeMap::new(),
            },
            records: vec![],
            signature: 7,
            pure_definitions: vec![],
        }
    }
    fn sample(value: u64) -> Sample {
        let mut sample = super::super::tests::example_sample();
        sample.pre_registers = BTreeMap::from([("input".into(), json!({"bits":format!("{value:08b}")}))]);
        sample.path_signature = 999;
        sample
    }
    #[test]
    fn prefilter_rejects_only_proven_conflict_and_ignores_source_path() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let x = solver.declare_const(Ty::BitVec(8), SourceLoc::unknown());
        let masked = solver.define_const(
            Exp::Bvand(Box::new(Exp::Var(x)), Box::new(Exp::Bits64(B64::new(3, 8)))),
            SourceLoc::unknown(),
        );
        solver.assert(Exp::Eq(Box::new(Exp::Var(masked)), Box::new(Exp::Bits64(B64::new(2, 8)))));
        let shared = SharedState::empty(Symtab::new());
        let filter = Prefilter::new(&fixture(&mut solver, x), &shared);
        assert!(filter.rejects(&sample(1)));
        assert!(!filter.rejects(&sample(2)));
        let mut missing = sample(1);
        missing.pre_registers.clear();
        assert!(!filter.rejects(&missing));
    }
    #[test]
    fn prefilter_exhaustive_membership_matches_full_judge() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let x = solver.declare_const(Ty::BitVec(8), SourceLoc::unknown());
        let free = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        let low = Exp::Extract(3, 0, Box::new(Exp::Var(x)));
        let condition = Exp::Eq(Box::new(low), Box::new(Exp::Bits64(B64::new(6, 4))));
        solver.assert(Exp::And(Box::new(condition), Box::new(Exp::Var(free))));
        let path = fixture(&mut solver, x);
        let shared = SharedState::empty(Symtab::new());
        let filter = Prefilter::new(&path, &shared);
        let mut rejected = 0;
        for value in 0..256 {
            let input = sample(value);
            let full = path.path.judge(&mut solver, &shared, &input, &[], 7, |_, _| Ok(())).unwrap();
            if filter.rejects(&input) {
                rejected += 1;
                assert!(full.is_none());
            } else {
                assert_eq!(full.is_some(), value % 16 == 6);
            }
        }
        assert!(rejected > 0);
    }
    #[test]
    fn prefilter_unknown_symbols_are_retained() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let x = solver.declare_const(Ty::BitVec(8), SourceLoc::unknown());
        let free = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        solver.assert(Exp::Var(free));
        let shared = SharedState::empty(Symtab::new());
        let path = fixture(&mut solver, x);
        assert!(!Prefilter::new(&path, &shared).rejects(&sample(1)));
    }
    #[test]
    fn prefilter_rebinding_cannot_reuse_an_early_assertion() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let x = solver.declare_const(Ty::BitVec(8), SourceLoc::unknown());
        solver.assert(Exp::Eq(Box::new(Exp::Var(x)), Box::new(Exp::Bits64(B64::new(1, 8)))));
        solver.add(isla_lib::smt::smtlib::Def::DeclareConst(x, Ty::BitVec(8)));
        let shared = SharedState::empty(Symtab::new());
        let path = fixture(&mut solver, x);
        assert!(!Prefilter::new(&path, &shared).rejects(&sample(2)));
    }
}
