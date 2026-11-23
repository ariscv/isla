use super::scalar::{ArmFacts, ScalarLayout};
use super::*;
use std::cell::OnceCell;

pub(in crate::smt) const BUFFERED: usize = usize::MAX;

// 已发布的段号在建检查点后保持不变；缓冲区使用单独的段号。
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Position(usize, usize);

type GuardBounds = HashMap<Sym, Option<Arc<Vec<Exp<Sym>>>>>;

pub(in crate::smt) struct PrefixIndex<'ctx> {
    pub(super) arm_facts: RefCell<ArmFacts>,
    pub(super) layouts: HashMap<Sym, ScalarLayout>,
    symbols: ahash::AHashMap<Sym, Position>,
    rebindings: usize,
    bounds: RefCell<HashMap<Sym, (usize, Bound)>>,
    guard_bounds: RefCell<Vec<GuardBounds>>,
    assertions: Vec<Position>,
    bool_symbols: Vec<(Position, Sym)>,
    pub(super) projection: RefCell<ProjectionCache>,
    pub(super) rewrites: rewrites::Rewrites<'ctx>,
    pub(super) domains: RefCell<HashMap<(Sym, bool, bool), FiniteDomain>>,
    pub(super) asts: ProjectionAsts<'ctx>,
    pub(super) branch: RefCell<Option<BranchCandidates>>,
}

#[derive(Default)]
pub(super) struct ProjectionCache {
    pub(super) assertions: Vec<Z3_ast>,
    pub(super) guards: Vec<Z3_ast>,
    pub(super) simplified: HashMap<Z3_ast, (Option<bool>, Z3_ast)>,
    pub(super) anchors: HashMap<Z3_ast, AnchorFacts>,
}

#[derive(Default)]
pub(super) struct AnchorFacts {
    pub(super) projection: AnchorProjection,
    // 普通追加只检查新后缀。条件替换、前缀缩短和改绑随整个投影缓存失效。
    indexed_assertions: usize,
    indexed_guards: usize,
    related: Vec<Z3_ast>,
    candidates: HashMap<Z3_ast, BranchCheck>,
}

#[derive(Clone, Copy)]
enum BranchCheck {
    Excluded,
    Checked(usize),
}

// 与 ConstBinding 相同，接管 Ast 的引用，由原 Context 释放。
// 可变容器只存原生句柄，故 Solver 仍可借给生命周期较短的 Model。
pub(super) struct ProjectionAsts<'ctx> {
    pub(super) ctx: &'ctx Context,
    refs: RefCell<HashSet<Z3_ast>>,
    ordinary: RefCell<HashSet<Z3_ast>>,
}

impl<'ctx> ProjectionAsts<'ctx> {
    pub(super) fn new(ctx: &'ctx Context) -> Self {
        Self { ctx, refs: Default::default(), ordinary: Default::default() }
    }

    pub(super) fn retain(&self, key: Z3_ast) {
        if self.refs.borrow_mut().insert(key) {
            unsafe { Z3_inc_ref(self.ctx.z3_ctx, key) };
        }
    }

    pub(super) fn heap_bytes(&self) -> usize {
        crate::executor::stats::memory_stats::map_bytes::<Z3_ast, ()>(self.refs.borrow().capacity())
    }

    pub(super) fn keep(&self, ast: Ast<'_>) -> Z3_ast {
        assert!(std::ptr::eq(self.ctx, ast.ctx));
        let key = ast.z3_ast;
        if self.refs.borrow_mut().insert(key) {
            std::mem::forget(ast);
        }
        key
    }

    pub(super) fn get(&self, key: Z3_ast) -> Ast<'ctx> {
        assert!(self.refs.borrow().contains(&key) || self.ordinary.borrow().contains(&key));
        unsafe { Z3_inc_ref(self.ctx.z3_ctx, key) };
        Ast { ctx: self.ctx, z3_ast: key }
    }

    fn clear(&mut self) {
        for key in self.refs.get_mut().drain() {
            unsafe { Z3_dec_ref(self.ctx.z3_ctx, key) };
        }
    }
}

impl Drop for ProjectionAsts<'_> {
    fn drop(&mut self) {
        self.clear();
        for key in self.ordinary.get_mut().drain() {
            unsafe { Z3_dec_ref(self.ctx.z3_ctx, key) };
        }
    }
}

pub(super) struct BranchCandidates {
    pub(super) predicate: Exp<Sym>,
    pub(super) subjects: Vec<Option<Vec<Candidate>>>,
}

pub(super) struct Candidate {
    pub(super) value: Exp<Sym>,
    pub(super) excluded: Option<bool>,
}

fn binding<B>(event: &Event<B>) -> Option<(Sym, bool)> {
    match event {
        Event::Smt(Def::DeclareConst(sym, ty), ..) => Some((*sym, matches!(ty, Ty::Bool))),
        Event::Smt(Def::DefineConst(sym, _) | Def::DeclareFun(sym, ..), ..) => Some((*sym, false)),
        _ => None,
    }
}

impl<'ctx> PrefixIndex<'ctx> {
    pub(super) fn has_binding(&self, sym: Sym) -> bool {
        self.symbols.contains_key(&sym)
    }

    pub(in crate::smt) fn new(ctx: &'ctx Context) -> Self {
        Self {
            arm_facts: Default::default(),
            layouts: Default::default(),
            symbols: Default::default(),
            rebindings: 0,
            bounds: Default::default(),
            guard_bounds: RefCell::default(),
            assertions: Vec::new(),
            bool_symbols: Vec::new(),
            projection: RefCell::default(),
            asts: ProjectionAsts::new(ctx),
            domains: Default::default(),
            rewrites: rewrites::Rewrites::new(ctx),
            branch: RefCell::default(),
        }
    }

    pub(in crate::smt) fn push<B>(&mut self, segment: usize, offset: usize, event: &Event<B>) {
        #[cfg(test)]
        PREFIX_EVENT_VISITS.set(PREFIX_EVENT_VISITS.get() + 1);
        let position = Position(segment, offset);
        if let Some((sym, boolean)) = binding(event) {
            if let std::collections::hash_map::Entry::Vacant(entry) = self.symbols.entry(sym) {
                entry.insert(position);
                if super::scalar::enabled() {
                    let layout = match event {
                        Event::Smt(Def::DeclareConst(_, Ty::BitVec(width)), ..) => Some(ScalarLayout::full(*width)),
                        Event::Smt(Def::DefineConst(_, exp), ..) => ScalarLayout::definition(exp, &self.layouts),
                        _ => None,
                    };
                    if let Some(layout) = layout {
                        self.layouts.insert(sym, layout);
                    }
                }
            } else {
                self.rebindings += 1;
                self.invalidate_candidates();
            }
            if boolean {
                self.domains.get_mut().clear();
                self.bool_symbols.push((position, sym));
            }
        } else if matches!(event, Event::Smt(Def::Assert(_), ..)) {
            self.domains.get_mut().clear();
            self.assertions.push(position);
        } else {
            return;
        }
        *self.branch.get_mut() = None;
    }

    pub(in crate::smt) fn remove_suffix<B>(&mut self, segment: usize, events: &[Event<B>], start: usize) {
        let first = Position(segment, start);
        self.assertions.truncate(self.assertions.partition_point(|position| *position < first));
        self.bool_symbols.truncate(self.bool_symbols.partition_point(|(position, _)| *position < first));
        for (index, event) in events.iter().enumerate().skip(start).rev() {
            if let Some((sym, _)) = binding(event) {
                let first = self.symbols[&sym];
                if first == Position(segment, index) {
                    self.symbols.remove(&sym);
                    self.layouts.remove(&sym);
                    for layer in self.guard_bounds.get_mut() {
                        layer.remove(&sym);
                    }
                } else {
                    self.rebindings -= 1;
                }
            }
        }
        if start < events.len() {
            self.arm_facts.get_mut().truncate_assertions(self.assertions.len());
            self.clear_candidate_caches();
        }
    }

    pub(in crate::smt) fn invalidate_candidates(&mut self) {
        *self.arm_facts.get_mut() = ArmFacts::default();
        self.guard_bounds.get_mut().clear();
        self.clear_candidate_caches();
    }

    pub(in crate::smt) fn guarded_suffix(&mut self, offset: usize, guard_depth: usize) {
        let retained = self.assertions.partition_point(|p| *p < Position(BUFFERED, offset));
        self.arm_facts.get_mut().truncate_assertions(retained);
        self.truncate_guards(guard_depth);
        self.clear_candidate_caches();
    }

    fn clear_candidate_caches(&mut self) {
        self.bounds.get_mut().clear();
        self.projection.get_mut().assertions.clear();
        for key in self.asts.ordinary.get_mut().drain() {
            unsafe { Z3_dec_ref(self.asts.ctx.z3_ctx, key) };
        }
        self.clear_guard_caches();
    }

    fn truncate_guards(&mut self, depth: usize) {
        self.arm_facts.get_mut().truncate_guards(depth);
        self.guard_bounds.get_mut().truncate(depth);
    }

    pub(in crate::smt) fn guards_changed(&mut self, depth: usize) {
        self.truncate_guards(depth);
        self.clear_guard_caches();
    }

    fn clear_guard_caches(&mut self) {
        let cache = self.projection.get_mut();
        let assertions = if super::scalar::enabled() { std::mem::take(&mut cache.assertions) } else { Vec::new() };
        *cache = ProjectionCache { assertions, ..Default::default() };
        self.asts.clear();
        self.domains.get_mut().clear();
        self.rewrites.advance();
        *self.branch.get_mut() = None;
    }

    pub(in crate::smt) fn heap_bytes(&self) -> usize {
        use crate::executor::stats::memory_stats::{exp_heap_bytes, map_bytes};
        use std::mem::size_of;

        let cache = self.projection.borrow();
        let layers = self.guard_bounds.borrow();
        let mut unique = HashSet::new();
        let guarded_bytes = layers
            .iter()
            .map(|layer| {
                map_bytes::<Sym, Option<Arc<Vec<Exp<Sym>>>>>(layer.capacity())
                    + layer
                        .values()
                        .flatten()
                        .filter(|v| unique.insert(Arc::as_ptr(v)))
                        .map(|v| v.capacity() * size_of::<Exp<Sym>>() + v.iter().map(exp_heap_bytes).sum::<usize>())
                        .sum::<usize>()
            })
            .sum::<usize>();
        self.arm_facts.borrow().heap_bytes()
            + map_bytes::<Sym, ScalarLayout>(self.layouts.capacity())
            + map_bytes::<Z3_ast, ()>(self.asts.ordinary.borrow().capacity())
            + layers.capacity() * size_of::<GuardBounds>()
            + guarded_bytes
            + (cache.assertions.capacity() + cache.guards.capacity()) * size_of::<Z3_ast>()
            + map_bytes::<Z3_ast, (Option<bool>, Z3_ast)>(cache.simplified.capacity())
            + map_bytes::<Z3_ast, ()>(self.asts.refs.borrow().capacity())
            + map_bytes::<Z3_ast, AnchorFacts>(cache.anchors.capacity())
            + cache
                .anchors
                .values()
                .map(|facts| {
                    facts.projection.heap_bytes()
                        + facts.related.capacity() * size_of::<Z3_ast>()
                        + map_bytes::<Z3_ast, BranchCheck>(facts.candidates.capacity())
                })
                .sum::<usize>()
            + map_bytes::<Sym, (usize, Bound)>(self.bounds.borrow().capacity())
            + self
                .bounds
                .borrow()
                .values()
                .filter_map(|(_, v)| v.as_ref())
                .map(|v| v.capacity() * size_of::<Exp<Sym>>() + v.iter().map(exp_heap_bytes).sum::<usize>())
                .sum::<usize>()
            + self.rewrites.heap_bytes()
            + map_bytes::<(Sym, bool, bool), FiniteDomain>(self.domains.borrow().capacity())
            + self
                .domains
                .borrow()
                .values()
                .map(|domain| match domain {
                    FiniteDomain::Known(v) | FiniteDomain::Bounded(v) => {
                        v.capacity() * size_of::<Exp<Sym>>() + v.iter().map(exp_heap_bytes).sum::<usize>()
                    }
                    FiniteDomain::Unknown => 0,
                })
                .sum::<usize>()
            + map_bytes::<Sym, Position>(self.symbols.capacity())
            + self.assertions.capacity() * size_of::<Position>()
            + self.bool_symbols.capacity() * size_of::<(Position, Sym)>()
            + self.branch.borrow().as_ref().map_or(0, |branch| {
                exp_heap_bytes(&branch.predicate)
                    + branch.subjects.capacity() * size_of::<Option<Vec<Candidate>>>()
                    + branch
                        .subjects
                        .iter()
                        .flatten()
                        .map(|candidates| {
                            candidates.capacity() * size_of::<Candidate>()
                                + candidates.iter().map(|candidate| exp_heap_bytes(&candidate.value)).sum::<usize>()
                        })
                        .sum::<usize>()
            })
    }
}

pub(super) struct PathConditions<'a, B> {
    pub(super) index: &'a PrefixIndex<'a>,
    trace: &'a Trace<B>,
    buffered: &'a [Event<B>],
    guards: &'a [Exp<Sym>],
    published: OnceCell<Vec<&'a Trace<B>>>,
}

impl<'a, B: BV> PathConditions<'a, B> {
    pub(super) fn new(solver: &'a Solver<'_, B>) -> Option<Self> {
        let index = solver.finite_prefix.as_ref()?;
        // 已发布断言保留发布时的绑定，不能用重绑后的符号表解释。
        (index.rebindings == 0).then(|| Self {
            index,
            trace: &solver.trace,
            buffered: &solver.transaction_events,
            guards: &solver.transaction_conditions,
            published: OnceCell::new(),
        })
    }

    fn event(&self, position: Position) -> &'a Event<B> {
        let Position(segment, offset) = position;
        if segment == BUFFERED {
            &self.buffered[offset]
        } else if segment == self.trace.checkpoints {
            self.trace.head_event(offset)
        } else {
            self.published.get_or_init(|| {
                let mut segments: Vec<_> =
                    std::iter::successors(self.trace.tail.as_ref().as_ref(), |trace| trace.tail.as_ref().as_ref())
                        .collect();
                segments.reverse();
                segments
            })[segment]
                .head_event(offset)
        }
    }

    pub(super) fn definition(&self, sym: Sym) -> Option<&'a Exp<Sym>> {
        match self.event(*self.index.symbols.get(&sym)?) {
            Event::Smt(Def::DefineConst(_, exp), ..) => Some(exp),
            _ => None,
        }
    }

    pub(super) fn assertions(&self) -> impl Iterator<Item = &'a Exp<Sym>> + '_ {
        self.index.assertions.iter().rev().map(|position| self.assertion(*position)).chain(self.guards)
    }

    // 原顺序是最新断言在前、活动臂守卫在后。追加后用新后缀作交集的左操作数，
    // 保留第一个给出有限集合的断言所规定的候选顺序。守卫与普通断言分别索引。
    pub(super) fn assertion_bound(&self, input: &Exp<Sym>, subject: &Exp<Sym>) -> Bound {
        let symbol = match input {
            Exp::Var(s) if self.index.symbols.contains_key(s) => Some(*s),
            _ => None,
        };
        let count = self.index.assertions.len();
        let (start, previous) = symbol.and_then(|s| self.index.bounds.borrow().get(&s).cloned()).unwrap_or_default();
        let mut memo = HashMap::new();
        let mut total = previous;
        if start < count {
            let mut suffix = None;
            for &position in self.index.assertions[start..].iter().rev() {
                suffix = intersect(suffix, bound(self.assertion(position), subject, self, false, &mut memo));
            }
            total = intersect(suffix, total);
            if let Some(s) = symbol {
                self.index.bounds.borrow_mut().insert(s, (count, total.clone()));
            }
        }
        if let Some(sym) = symbol.filter(|_| super::scalar::enabled() && !self.guards.is_empty()) {
            let mut layers = self.index.guard_bounds.borrow_mut();
            layers.resize_with(self.guards.len(), HashMap::new);
            let start = layers.iter().rposition(|layer| layer.contains_key(&sym)).map_or(0, |i| i + 1);
            let mut inherited = start.checked_sub(1).and_then(|i| layers[i][&sym].clone());
            for (guard, layer) in self.guards[start..].iter().zip(&mut layers[start..]) {
                if let Some(values) = bound(guard, subject, self, false, &mut memo) {
                    let common = intersect(inherited.as_deref().cloned(), Some(values));
                    inherited = common.map(Arc::new);
                }
                layer.insert(sym, inherited.clone());
            }
            return intersect(total, inherited.as_deref().cloned());
        }
        for guard in self.guards {
            total = intersect(total, bound(guard, subject, self, false, &mut memo));
        }
        total
    }

    pub(super) fn ordinary_suffix(&self, start: usize) -> impl Iterator<Item = &'a Exp<Sym>> + '_ {
        self.index.assertions[start..].iter().map(|position| self.assertion(*position))
    }

    pub(super) fn translate_projection_suffix(&self, solver: &Solver<'_, B>, cache: &mut ProjectionCache) {
        for &position in &self.index.assertions[cache.assertions.len()..] {
            let ast = solver.translate_projection_assertion(self.assertion(position));
            let key = if super::scalar::enabled() {
                let key = ast.z3_ast;
                if self.index.asts.ordinary.borrow_mut().insert(key) {
                    std::mem::forget(ast);
                }
                key
            } else {
                self.index.asts.keep(ast)
            };
            cache.assertions.push(key);
        }
        for guard in &self.guards[cache.guards.len()..] {
            cache.guards.push(self.index.asts.keep(solver.translate_projection_assertion(guard)));
        }
    }

    pub(super) fn excludes_branch_candidate(&self, solver: &Solver<'_, B>, anchor: &Ast, value: &Ast) -> bool {
        if value.z3_ast == anchor.z3_ast {
            return false;
        }
        let asts = &self.index.asts;
        let mut cache = self.index.projection.borrow_mut();
        self.translate_projection_suffix(solver, &mut cache);
        let ProjectionCache { assertions, guards, anchors, .. } = &mut *cache;
        let facts = anchors.entry(asts.keep(anchor.clone())).or_default();
        let checked = match facts.candidates.get(&value.z3_ast) {
            Some(BranchCheck::Excluded) => return true,
            Some(BranchCheck::Checked(count)) => *count,
            None => 0,
        };

        // 同一批新断言常共享很大的子式。每个 DAG 节点只查一次是否含锚点。
        let mut independent = HashSet::new();
        for &key in assertions[facts.indexed_assertions..].iter().chain(&guards[facts.indexed_guards..]) {
            if facts.projection.contains_anchor(key, anchor, value, &mut independent) {
                facts.related.push(key);
            }
        }
        facts.indexed_assertions = assertions.len();
        facts.indexed_guards = guards.len();
        let excluded = facts.related[checked..].iter().any(|&key| {
            let mut residual = asts.get(key).substitute(anchor, value);
            residual.z3_ast != key && residual.structural_bool() == Some(false)
        });
        let result = if excluded { BranchCheck::Excluded } else { BranchCheck::Checked(facts.related.len()) };
        facts.candidates.insert(asts.keep(value.clone()), result);
        excluded
    }

    fn assertion(&self, position: Position) -> &'a Exp<Sym> {
        match self.event(position) {
            Event::Smt(Def::Assert(exp), ..) => exp,
            _ => unreachable!("断言索引必须指向断言"),
        }
    }

    /// 活动臂条件及已发布的路径断言。缓冲内可能包含尚待认证的出口约束。
    pub(super) fn path_guards(&self) -> impl Iterator<Item = &'a Exp<Sym>> + '_ {
        self.guards.iter().rev().chain(
            self.index
                .assertions
                .iter()
                .rev()
                .skip_while(|position| position.0 == BUFFERED)
                .map(|position| self.assertion(*position)),
        )
    }

    pub(super) fn bool_symbols(&self) -> impl Iterator<Item = Sym> + '_ {
        self.index.bool_symbols.iter().rev().map(|(_, sym)| *sym)
    }
}
