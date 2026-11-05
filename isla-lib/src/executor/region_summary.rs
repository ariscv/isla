//! 函数调用图的静态效应与终止摘要；不参与运行事务或记录输出。
use super::*;
use crate::ir::regions::{RegionCfg, RegionOptions};
use crate::primop::{self as effects, Effect};

fn constraint_unary<B: BV>(f: primop::Unary<B>) -> bool {
    std::ptr::fn_addr_eq(f, primop::assume::<B> as primop::Unary<B>)
}
fn constraint_binary<B: BV>(f: primop::Binary<B>) -> bool {
    [primop::optimistic_assert::<B> as primop::Binary<B>, primop::pessimistic_assert::<B> as primop::Binary<B>]
        .iter()
        .any(|assertion| std::ptr::fn_addr_eq(f, *assertion))
}

/// 效应等级与静态拒绝证据分别保存：寄存器读可以推演，带条件约束也可重放。
/// 因此 C4 的 WritesState（例如 assume）不必然带有静态拒绝证据。
#[derive(Clone, Copy, Debug)]
pub(super) struct FunctionEffect {
    pub effect: Effect,
    pub non_returning: bool,
    pub(super) rejection: Option<CachedReject>,
}
impl FunctionEffect {
    fn join(&mut self, other: Self) -> bool {
        let changed = other.effect > self.effect || (self.rejection.is_none() && other.rejection.is_some());
        if other.rejection.is_some() && (other.effect > self.effect || self.rejection.is_none()) {
            self.rejection = other.rejection;
        }
        self.effect = self.effect.max(other.effect);
        changed
    }
}

/// 已加载的原语调用通常已改写为 Primop；特殊内建仍保留 Call 形态。
fn direct_effect<B: BV>(instr: &Instr<Name, B>, shared: &SharedState<B>) -> Effect {
    match instr {
        Instr::PrimopUnary(_, f, _, _) => effects::unary_effect(*f).expect("一元原语必须分类"),
        Instr::PrimopBinary(_, f, _, _, _) => effects::binary_effect(*f).expect("二元原语必须分类"),
        Instr::PrimopVariadic(_, f, _, _) => effects::variadic_effect(*f).expect("多元原语必须分类"),
        Instr::PrimopReset(_, _, effect, _) => *effect,
        Instr::Call(_, _, function, _, _) if !shared.functions.contains_key(function) => match *function {
            REG_DEREF | READ_REGISTER_FROM_VECTOR => Effect::ReadsState,
            WRITE_REGISTER_FROM_VECTOR
            | RESET_REGISTERS
            | INTERRUPT_PENDING
            | INSTR_ANNOUNCE
            | ABSTRACT_CALL
            | ABSTRACT_PRIMOP => Effect::WritesState,
            INTERNAL_VECTOR_INIT | INTERNAL_VECTOR_UPDATE | ITE_PHI => Effect::Pure,
            // 与执行器 special_primop 的构造子路径一致：只构造载荷值，不调用不透明实现。
            _ if shared.type_info.union_ctors.contains(function) => Effect::Pure,
            _ => match shared.externs.get(function) {
                Some((_, _, name)) => effects::effect(name).unwrap_or(Effect::Unknown),
                None => effects::effect(&zencode::decode(shared.symtab.to_str(*function))).unwrap_or(Effect::Unknown),
            },
        },
        _ => Effect::Pure,
    }
}

/// 从格底 Pure 开始，按调用图的 SCC 逆拓扑序处理；分量内迭代到最小不动点。
/// 递归边只传播已知效应，不凭空增加效应；实际递归仍受共享推演步数预算约束。
pub(super) fn function_effect_summaries<B: BV>(shared: &SharedState<B>) -> HashMap<Name, FunctionEffect> {
    let mut graph = petgraph::graph::DiGraph::<Name, ()>::new();
    let nodes: HashMap<_, _> = shared.functions.keys().map(|function| (*function, graph.add_node(*function))).collect();
    for (function, (_, _, body)) in &shared.functions {
        for instr in *body {
            if let Instr::Call(_, _, callee, _, _) = instr {
                if let Some(callee) = nodes.get(callee) {
                    graph.update_edge(nodes[function], *callee, ());
                }
            }
        }
    }
    let components = petgraph::algo::kosaraju_scc(&graph);
    let mut non_returning = HashSet::new();
    let mut terminating: HashMap<_, _> = shared.functions.keys().map(|function| (*function, false)).collect();
    for component in &components {
        let cfgs: Vec<_> = component
            .iter()
            .map(|node| {
                let function = graph[*node];
                (
                    function,
                    RegionCfg::new(
                        shared.functions[&function].2,
                        RegionOptions { have_exception: None, terminal_calls: &[] },
                    ),
                )
            })
            .collect();
        loop {
            let mut changed = false;
            for (function, cfg) in &cfgs {
                if !terminating[function]
                    && cfg.always_terminates(
                        shared.functions[function].2,
                        HAVE_EXCEPTION,
                        &non_returning,
                        &terminating,
                        true,
                    )
                {
                    *terminating.get_mut(function).unwrap() = true;
                    changed = true;
                }
                if !non_returning.contains(function)
                    && cfg.always_terminates(
                        shared.functions[function].2,
                        HAVE_EXCEPTION,
                        &non_returning,
                        &terminating,
                        false,
                    )
                {
                    changed |= non_returning.insert(*function);
                }
            }
            if !changed {
                break;
            }
        }
    }
    let terminal_calls: Vec<_> = non_returning.iter().copied().collect();
    // 效应只沿能继续执行的调用边传播；终止调用与其后的不可达指令不贡献效应。
    graph.clear_edges();
    let mut summaries = HashMap::new();
    for (function, (params, _, body)) in &shared.functions {
        let locals: HashSet<_> = params
            .iter()
            .map(|(name, _)| *name)
            .chain([RETURN])
            .chain(body.iter().filter_map(|instr| match instr {
                Instr::Decl(name, ..) | Instr::Init(name, ..) => Some(*name),
                _ => None,
            }))
            .collect();
        let mut summary =
            FunctionEffect { effect: Effect::Pure, non_returning: non_returning.contains(function), rejection: None };
        let cfg = RegionCfg::new(body, RegionOptions { have_exception: None, terminal_calls: &terminal_calls });
        for pc in cfg.reachable_instructions() {
            let instr = &body[pc];
            if matches!(instr, Instr::Call(_, _, callee, _, _) if non_returning.contains(callee)) {
                continue;
            }
            let mut effect = direct_effect(instr, shared);
            let mut rejection = if matches!(instr, Instr::Call(_, _, callee, _, _) if shared.functions.contains_key(callee))
            {
                None
            } else {
                instruction_effect(*function, pc, instr, shared, &HashMap::new())
            };
            let mut reads = HashSet::new();
            let mut destination = None;
            match instr {
                Instr::Copy(loc, exp, _) => {
                    destination = Some(loc);
                    exp.collect_ids(&mut reads);
                }
                Instr::Init(_, _, exp, _) | Instr::Jump(exp, _, _) => exp.collect_ids(&mut reads),
                Instr::PrimopUnary(loc, _, exp, _) => {
                    destination = Some(loc);
                    exp.collect_ids(&mut reads);
                }
                Instr::PrimopBinary(loc, _, a, b, _) => {
                    destination = Some(loc);
                    a.collect_ids(&mut reads);
                    b.collect_ids(&mut reads);
                }
                Instr::PrimopVariadic(loc, _, args, _) | Instr::Call(loc, _, _, args, _) => {
                    destination = Some(loc);
                    for arg in args {
                        arg.collect_ids(&mut reads);
                    }
                }
                Instr::PrimopReset(loc, ..) => destination = Some(loc),
                Instr::Monomorphize(name, ..) => {
                    reads.insert(*name);
                }
                _ => (),
            }
            if reads.iter().any(|name| !locals.contains(name) && !shared.type_info.enum_members.contains_key(name)) {
                effect = effect.max(Effect::ReadsState);
            }
            if matches!(instr, Instr::Call(_, _, WRITE_REGISTER_FROM_VECTOR, _, _))
                || destination.map_or(false, |loc| !locals.contains(&loc.id()) || matches!(loc, Loc::Addr(_)))
            {
                effect = effect.max(Effect::WritesState);
                rejection = Some(CachedReject {
                    reason: SpeculativeRejectReason::CalleeStateWrite,
                    function: *function,
                    pc,
                    location: stats::instr_source_loc(instr).unwrap_or(SourceLoc::unknown()),
                });
            }
            summary.join(FunctionEffect { effect, non_returning: false, rejection });
            if let Instr::Call(_, _, callee, _, _) = instr {
                if let Some(callee) = nodes.get(callee) {
                    graph.update_edge(nodes[function], *callee, ());
                }
            }
        }
        summaries.insert(*function, summary);
    }
    // kosaraju_scc 返回汇点优先的逆拓扑序，因此分量外的被调函数已收敛。
    for component in components {
        loop {
            let mut changed = false;
            for node in &component {
                let function = graph[*node];
                for callee in graph.neighbors(*node) {
                    let effect = summaries[&graph[callee]];
                    changed |= summaries.get_mut(&function).unwrap().join(effect);
                }
            }
            if !changed {
                break;
            }
        }
    }
    summaries
}

pub(super) fn instruction_effect<B: BV>(
    function_name: Name,
    pc: usize,
    instr: &Instr<Name, B>,
    shared: &SharedState<B>,
    summaries: &HashMap<Name, FunctionEffect>,
) -> Option<CachedReject> {
    match instr {
        Instr::PrimopUnary(_, f, _, _) if constraint_unary(*f) => return None,
        Instr::PrimopBinary(_, f, _, _, _) if constraint_binary(*f) => return None,
        Instr::Call(_, _, function, _, _) if shared.functions.contains_key(function) => {
            let summary = summaries.get(function).expect("IR 函数必须有收敛的效应摘要");
            return if summary.non_returning { None } else { summary.rejection };
        }
        Instr::Call(
            _,
            _,
            REG_DEREF
            | READ_REGISTER_FROM_VECTOR
            | WRITE_REGISTER_FROM_VECTOR
            | INTERNAL_VECTOR_INIT
            | INTERNAL_VECTOR_UPDATE
            | ITE_PHI,
            _,
            _,
        ) => return None,
        _ => (),
    }
    // Unknown 没有可执行实现；保留摘要等级，只有实际到达时才拒绝推演。
    (!matches!(direct_effect(instr, shared), Effect::Pure | Effect::Unknown | Effect::ReadsMemory)).then(|| {
        CachedReject {
            reason: SpeculativeRejectReason::StateEffect,
            function: function_name,
            pc,
            location: stats::instr_source_loc(instr).unwrap_or(SourceLoc::unknown()),
        }
    })
}

#[derive(Clone, Copy, Debug)]
pub(super) struct CachedReject {
    pub reason: SpeculativeRejectReason,
    pub function: Name,
    pub pc: usize,
    pub location: SourceLoc,
}
impl CachedReject {
    pub(super) fn error(self) -> ExecError {
        ExecError::SpeculativeReject {
            reason: self.reason,
            function: self.function,
            pc: self.pc,
            location: self.location,
        }
    }
}
