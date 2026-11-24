use super::scalar::{ArmFacts, ScalarLayout};
use super::*;
use std::cell::OnceCell;

pub(in crate::smt) const BUFFERED: usize = usize::MAX;

// 已发布的段号在建检查点后保持不变；缓冲区使用单独的段号。
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Position(usize, usize);

type GuardBounds = HashMap<Sym, Option<Arc<Vec<Exp<Sym>>>>>;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct Slice {
    source: Sym,
    high: u32,
    low: u32,
}

// 允许别名与嵌套切片。复杂定义以所属符号为起点，保留绑定身份。
pub(super) fn narrow_slice<'a>(exp: &'a Exp<Sym>, definition: impl Fn(Sym) -> Option<&'a Exp<Sym>>) -> Option<Slice> {
    let Exp::Extract(high, low, source) = exp else { return None };
    let (mut high, mut low) = (*high, *low);
    if high.checked_sub(low)? >= 4 {
        return None;
    }
    let mut source = &**source;
    for _ in 0..16 {
        match source {
            Exp::Var(sym) => match definition(*sym) {
                Some(alias @ (Exp::Var(_) | Exp::Extract(..))) => source = alias,
                _ => return Some(Slice { source: *sym, high, low }),
            },
            Exp::Extract(parent_high, parent_low, parent) if high <= parent_high.checked_sub(*parent_low)? => {
                high += parent_low;
                low += parent_low;
                source = parent;
            }
            _ => return None,
        }
    }
    None
}

pub(super) fn slice_comparison<'a>(
    mut exp: &'a Exp<Sym>,
    resolve: impl Fn(&'a Exp<Sym>) -> &'a Exp<Sym>,
    definition: impl Fn(Sym) -> Option<&'a Exp<Sym>>,
) -> Option<(Slice, B64, bool)> {
    let mut equal = true;
    let (lhs, rhs) = loop {
        match resolve(exp) {
            Exp::Not(inner) => {
                equal = !equal;
                exp = inner;
            }
            Exp::Eq(lhs, rhs) => break (lhs, rhs),
            Exp::Neq(lhs, rhs) => {
                equal = !equal;
                break (lhs, rhs);
            }
            _ => return None,
        }
    };
    [(lhs, rhs), (rhs, lhs)].into_iter().find_map(|(field, value)| {
        let slice = narrow_slice(resolve(field), &definition)?;
        let Exp::Bits64(value) = constant(resolve(value))? else { return None };
        (value.len() == slice.high - slice.low + 1).then_some((slice, value, equal))
    })
}

fn slice_exclusion(exp: &Exp<Sym>) -> Option<(Slice, B64)> {
    let excluded = |exp| match slice_comparison(exp, |exp| exp, |_| None) {
        Some((slice, value, false)) => Some((slice, value)),
        _ => None,
    };
    if let Exp::Or(lhs, rhs) = exp {
        // 前态的常量配置条件仍保留在原公式里。仅在另一侧恒假时登记排除。
        [(lhs, rhs), (rhs, lhs)].into_iter().find_map(|(candidate, condition)| {
            let fact = excluded(candidate)?;
            (ground::eval_assertion(condition, |_| None, |_| None) == Some(false)).then_some(fact)
        })
    } else {
        excluded(exp)
    }
}

struct ScalarUpperBound {
    definition: Position,
    proof_assertions: usize,
    candidates: Vec<Exp<Sym>>,
}

pub(in crate::smt) struct PrefixIndex<'ctx> {
    choice_epoch: u64,
    choice_assertions: Vec<u64>,
    choice_guards: Vec<u64>,
    choice_binding_revision: u64,
    incremental_choices: bool,
    pub(super) joined_choices: HashMap<Sym, super::arithmetic::JoinedChoices>,
    pub(super) arm_facts: RefCell<ArmFacts>,
    pub(super) layouts: HashMap<Sym, ScalarLayout>,
    symbols: ahash::AHashMap<Sym, Position>,
    symbol_upper_bounds: RefCell<HashMap<Sym, ScalarUpperBound>>,
    rebindings: usize,
    bounds: RefCell<HashMap<Sym, (usize, Bound)>>,
    guard_bounds: RefCell<Vec<GuardBounds>>,
    assertions: Vec<Position>,
    slice_exclusions: HashMap<Slice, Vec<(Position, B64)>>,
    bool_symbols: Vec<(Position, Sym)>,
    pub(super) projection: RefCell<ProjectionCache>,
    pub(super) rewrites: rewrites::ScopedRewriteCache<'ctx>,
    pub(super) domains: RefCell<HashMap<(Sym, bool, bool), FiniteDomain>>,
    pub(super) asts: ProjectionAsts<'ctx>,
    pub(super) ordinary_asts: ProjectionAsts<'ctx>,
    pub(super) branch: RefCell<Option<BranchCandidates>>,
}

#[derive(Default)]
pub(super) struct ProjectionCache {
    pub(super) assertions: Vec<Z3_ast>,
    pub(super) guards: Vec<Z3_ast>,
    pub(super) ordinary: ProjectionLayer,
    pub(super) active: ProjectionLayer,
}

#[derive(Default)]
pub(super) struct ProjectionLayer {
    pub(super) anchors: HashMap<Z3_ast, AnchorFacts>,
}

#[derive(Default)]
pub(super) struct AnchorFacts {
    pub(super) projection: AnchorProjection,
    indexed: usize,
    related: Vec<(usize, Z3_ast)>,
    candidates: HashMap<Z3_ast, BranchCheck>,
}

#[derive(Clone, Copy)]
enum BranchCheck {
    ExcludedAt(usize),
    Checked(usize),
}

// 与 ConstBinding 相同，接管 Ast 的引用，由原 Context 释放。
// 可变容器只存原生句柄，故 Solver 仍可借给生命周期较短的 Model。
pub(super) struct ProjectionAsts<'ctx> {
    pub(super) ctx: &'ctx Context,
    refs: RefCell<HashSet<Z3_ast>>,
    stable: RefCell<HashMap<Z3_ast, usize>>,
}

impl<'ctx> ProjectionAsts<'ctx> {
    pub(super) fn new(ctx: &'ctx Context) -> Self {
        Self { ctx, refs: Default::default(), stable: Default::default() }
    }

    pub(super) fn retain(&self, key: Z3_ast) {
        if self.refs.borrow_mut().insert(key) {
            unsafe { Z3_inc_ref(self.ctx.z3_ctx, key) };
        }
    }

    pub(super) fn retained_count(&self) -> usize {
        self.refs.borrow().len()
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
        assert!(self.refs.borrow().contains(&key) || self.stable.borrow().contains_key(&key));
        unsafe { Z3_inc_ref(self.ctx.z3_ctx, key) };
        Ast { ctx: self.ctx, z3_ast: key }
    }

    fn keep_stable(&self, ast: Ast<'_>) -> Z3_ast {
        assert!(std::ptr::eq(self.ctx, ast.ctx));
        let key = ast.z3_ast;
        let mut roots = self.stable.borrow_mut();
        let count = roots.entry(key).or_default();
        if *count == 0 {
            std::mem::forget(ast);
        }
        *count += 1;
        key
    }

    fn release_stable(&mut self, key: Z3_ast) {
        let roots = self.stable.get_mut();
        let count = roots.get_mut(&key).expect("断言翻译必须持有 AST 引用");
        *count -= 1;
        if *count == 0 {
            roots.remove(&key);
            unsafe { Z3_dec_ref(self.ctx.z3_ctx, key) };
        }
    }

    pub(super) fn release_all(&self) {
        for key in self.refs.borrow_mut().drain() {
            unsafe { Z3_dec_ref(self.ctx.z3_ctx, key) };
        }
    }
}

impl Drop for ProjectionAsts<'_> {
    fn drop(&mut self) {
        self.release_all();
        for (key, _) in self.stable.get_mut().drain() {
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
            choice_epoch: 0,
            choice_assertions: Vec::new(),
            choice_guards: Vec::new(),
            choice_binding_revision: 0,
            incremental_choices: ctx.solver_options.incremental_choice_dag,
            joined_choices: HashMap::new(),
            arm_facts: Default::default(),
            layouts: Default::default(),
            symbols: Default::default(),
            symbol_upper_bounds: Default::default(),
            rebindings: 0,
            bounds: Default::default(),
            guard_bounds: RefCell::default(),
            assertions: Vec::new(),
            slice_exclusions: Default::default(),
            bool_symbols: Vec::new(),
            projection: RefCell::default(),
            asts: ProjectionAsts::new(ctx),
            ordinary_asts: ProjectionAsts::new(ctx),
            domains: Default::default(),
            rewrites: rewrites::ScopedRewriteCache::new(ctx),
            branch: RefCell::default(),
        }
    }

    fn next_choice_epoch(&mut self) -> u64 {
        self.choice_epoch = self.choice_epoch.checked_add(1).expect("选择图版本溢出");
        self.choice_epoch
    }

    pub(super) fn choice_revision(&self) -> (&[u64], (u64, u64)) {
        let assertions = self.choice_assertions.last().copied().unwrap_or(0);
        (&self.choice_guards, (assertions, self.choice_binding_revision))
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
        } else if let Event::Smt(Def::Assert(exp), ..) = event {
            // 缓冲断言可能在提交时套上臂守卫。只登记已发布的公式。
            if segment != BUFFERED {
                if let Some((slice, value)) = slice_exclusion(exp) {
                    self.slice_exclusions.entry(slice).or_default().push((position, value));
                }
            }
            self.domains.get_mut().clear();
            self.assertions.push(position);
            if self.incremental_choices {
                let epoch = self.next_choice_epoch();
                self.choice_assertions.push(epoch);
            }
        } else {
            return;
        }
        *self.branch.get_mut() = None;
    }

    pub(in crate::smt) fn remove_suffix<B>(
        &mut self,
        segment: usize,
        events: &[Event<B>],
        start: usize,
        publishing: bool,
    ) {
        self.rewind(
            segment,
            start,
            publishing,
            events.iter().enumerate().skip(start).rev().map(|(offset, event)| (segment, offset, event)),
        );
    }

    pub(in crate::smt) fn rewind<'a, B: 'a>(
        &mut self,
        segment: usize,
        start: usize,
        publishing: bool,
        reversed: impl Iterator<Item = (usize, usize, &'a Event<B>)>,
    ) {
        let first = Position(segment, start);
        self.assertions.truncate(self.assertions.partition_point(|position| *position < first));
        if segment != BUFFERED {
            self.slice_exclusions.retain(|_, facts| {
                facts.truncate(facts.partition_point(|(position, _)| *position < first));
                !facts.is_empty()
            });
        }
        if self.incremental_choices {
            self.choice_assertions.truncate(self.assertions.len());
        }
        self.bool_symbols.truncate(self.bool_symbols.partition_point(|(position, _)| *position < first));
        let mut reversed = reversed.peekable();
        let has_suffix = reversed.peek().is_some();
        for (segment, index, event) in reversed {
            if let Some((sym, _)) = binding(event) {
                if self.incremental_choices {
                    self.choice_binding_revision = self.next_choice_epoch();
                }
                let first = self.symbols[&sym];
                if first == Position(segment, index) {
                    self.symbols.remove(&sym);
                    if !publishing {
                        self.joined_choices.remove(&sym);
                    }
                    self.layouts.remove(&sym);
                    for layer in self.guard_bounds.get_mut() {
                        layer.remove(&sym);
                    }
                } else {
                    self.rebindings -= 1;
                }
            }
        }
        if has_suffix {
            let retained = self.assertions.len();
            self.symbol_upper_bounds
                .get_mut()
                .retain(|_, bound| bound.definition < first && bound.proof_assertions <= retained);
            self.arm_facts.get_mut().truncate_assertions(self.assertions.len());
            let preserve = if self.incremental_choices || self.retain_ordinary() { self.assertions.len() } else { 0 };
            self.clear_candidate_caches(preserve);
        }
    }

    pub(in crate::smt) fn invalidate_candidates(&mut self) {
        if self.incremental_choices {
            self.choice_binding_revision = self.next_choice_epoch();
        }
        self.joined_choices.clear();
        self.symbol_upper_bounds.get_mut().clear();
        *self.arm_facts.get_mut() = ArmFacts::default();
        self.guard_bounds.get_mut().clear();
        if self.incremental_choices {
            for key in self.projection.get_mut().guards.drain(..) {
                self.asts.release_stable(key);
            }
        }
        self.projection.get_mut().ordinary = ProjectionLayer::default();
        self.ordinary_asts.release_all();
        self.clear_candidate_caches(0);
    }

    fn retain_ordinary(&self) -> bool {
        self.asts.ctx.solver_options.retain_ordinary_prefix_cache
    }

    fn stable_assertions(&self) -> bool {
        self.retain_ordinary() || super::scalar::enabled() || self.incremental_choices
    }

    pub(in crate::smt) fn guarded_suffix(&mut self, offset: usize, guard_depth: usize) {
        let retained = self.assertions.partition_point(|p| *p < Position(BUFFERED, offset));
        if self.incremental_choices && retained < self.choice_assertions.len() {
            let epoch = self.next_choice_epoch();
            self.choice_assertions[retained..].fill(epoch);
        }
        self.symbol_upper_bounds.get_mut().retain(|_, bound| bound.proof_assertions <= retained);
        self.arm_facts.get_mut().truncate_assertions(retained);
        self.truncate_guards(guard_depth);
        self.clear_candidate_caches(if self.incremental_choices || self.retain_ordinary() { retained } else { 0 });
    }

    fn clear_candidate_caches(&mut self, preserve: usize) {
        self.bounds.get_mut().clear();
        let stable = self.stable_assertions();
        let cache = self.projection.get_mut();
        let preserve = preserve.min(cache.assertions.len());
        if preserve < cache.assertions.len() {
            for facts in cache.ordinary.anchors.values_mut() {
                // 依赖索引含有被删根的子节点，先丢掉裸指针再释放根引用。
                facts.projection = AnchorProjection::default();
                let retained_related = facts.related.partition_point(|&(index, _)| index < preserve);
                facts.candidates.retain(|_, check| match check {
                    BranchCheck::ExcludedAt(index) => *index < preserve,
                    BranchCheck::Checked(count) => {
                        *count = (*count).min(retained_related);
                        true
                    }
                });
                facts.indexed = 0;
                facts.related.clear();
            }
            for key in cache.assertions.drain(preserve..) {
                if stable {
                    self.asts.release_stable(key);
                }
            }
        }
        self.clear_guard_caches();
    }

    fn truncate_guards(&mut self, depth: usize) {
        if self.incremental_choices {
            let guards = &mut self.projection.get_mut().guards;
            let keep = depth.min(guards.len());
            for key in guards.drain(keep..) {
                self.asts.release_stable(key);
            }
            self.choice_guards.truncate(depth);
            while self.choice_guards.len() < depth {
                let epoch = self.next_choice_epoch();
                self.choice_guards.push(epoch);
            }
        }
        self.arm_facts.get_mut().truncate_guards(depth);
        self.guard_bounds.get_mut().truncate(depth);
    }

    pub(in crate::smt) fn guards_changed(&mut self, depth: usize) {
        self.truncate_guards(depth);
        self.clear_guard_caches();
    }

    fn clear_guard_caches(&mut self) {
        let stable_assertions = self.stable_assertions();
        let retain_ordinary = self.retain_ordinary();
        let cache = self.projection.get_mut();
        cache.active = ProjectionLayer::default();
        if !retain_ordinary || self.ordinary_asts.retained_count() > 32_768 {
            cache.ordinary = ProjectionLayer::default();
            self.ordinary_asts.release_all();
        }
        if !stable_assertions {
            cache.assertions.clear();
        }
        if !self.incremental_choices {
            cache.guards.clear();
        }
        self.asts.release_all();
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
            + map_bytes::<Z3_ast, usize>(self.asts.stable.borrow().capacity())
            + layers.capacity() * size_of::<GuardBounds>()
            + guarded_bytes
            + (cache.assertions.capacity() + cache.guards.capacity()) * size_of::<Z3_ast>()
            + self.asts.heap_bytes()
            + self.ordinary_asts.heap_bytes()
            + [&cache.ordinary, &cache.active]
                .into_iter()
                .map(|layer| {
                    map_bytes::<Z3_ast, AnchorFacts>(layer.anchors.capacity())
                        + layer
                            .anchors
                            .values()
                            .map(|facts| {
                                facts.projection.heap_bytes()
                                    + facts.related.capacity() * size_of::<(usize, Z3_ast)>()
                                    + map_bytes::<Z3_ast, BranchCheck>(facts.candidates.capacity())
                            })
                            .sum::<usize>()
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
            + map_bytes::<Sym, ScalarUpperBound>(self.symbol_upper_bounds.borrow().capacity())
            + self
                .symbol_upper_bounds
                .borrow()
                .values()
                .map(|bound| {
                    bound.candidates.capacity() * size_of::<Exp<Sym>>()
                        + bound.candidates.iter().map(exp_heap_bytes).sum::<usize>()
                })
                .sum::<usize>()
            + map_bytes::<Slice, Vec<(Position, B64)>>(self.slice_exclusions.capacity())
            + self.slice_exclusions.values().map(|facts| facts.capacity() * size_of::<(Position, B64)>()).sum::<usize>()
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

    pub(super) fn known_choice(&self, solver: &Solver<'_, B>, guard: &Exp<Sym>) -> Option<bool> {
        let mut facts = self.index.arm_facts.borrow_mut();
        facts.choice(guard, solver, self)
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

    pub(super) fn excluded_slice_comparison(&self, exp: &Exp<Sym>) -> Option<bool> {
        if self.index.slice_exclusions.is_empty() {
            return None;
        }
        let (slice, compared, equal) = slice_comparison(exp, |exp| resolve(exp, self), |sym| self.definition(sym))?;
        self.index.slice_exclusions.get(&slice)?.iter().any(|&(_, value)| value == compared).then_some(!equal)
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

    pub(super) fn ordinary_assertion_count(&self) -> usize {
        self.index.assertions.len()
    }

    pub(super) fn ordinary_suffix(&self, start: usize) -> impl Iterator<Item = &'a Exp<Sym>> + '_ {
        self.index.assertions[start..].iter().map(|position| self.assertion(*position))
    }

    pub(super) fn translate_projection_suffix(&self, solver: &Solver<'_, B>, cache: &mut ProjectionCache) {
        for &position in &self.index.assertions[cache.assertions.len()..] {
            let ast = solver.translate_projection_assertion(self.assertion(position));
            let key = if self.index.stable_assertions() {
                self.index.asts.keep_stable(ast)
            } else {
                self.index.asts.keep(ast)
            };
            cache.assertions.push(key);
        }
        for guard in &self.guards[cache.guards.len()..] {
            let ast = solver.translate_projection_assertion(guard);
            let key = if self.index.incremental_choices {
                self.index.asts.keep_stable(ast)
            } else {
                self.index.asts.keep(ast)
            };
            cache.guards.push(key);
        }
    }

    pub(super) fn scalar_proof_prefix(&self, sym: Sym, savepoint: usize) -> Option<usize> {
        let position = *self.index.symbols.get(&sym)?;
        (position < Position(BUFFERED, savepoint)).then(|| self.index.assertions.partition_point(|p| *p < position))
    }

    pub(super) fn remember_scalar_upper(&self, sym: Sym, count: usize, values: Vec<Exp<Sym>>) {
        let mut bounds = self.index.symbol_upper_bounds.borrow_mut();
        // 只限制缓存开销。容量满时仍按原入口完整推导。
        if bounds.len() < 64 {
            bounds.insert(
                sym,
                ScalarUpperBound { definition: self.index.symbols[&sym], proof_assertions: count, candidates: values },
            );
        }
    }

    pub(super) fn scalar_upper(&self, solver: &Solver<'_, B>, sym: Sym) -> Option<Vec<Exp<Sym>>> {
        let bounds = self.index.symbol_upper_bounds.borrow();
        let upper = bounds.get(&sym)?;
        let anchor = solver.translate_exp(&Exp::Var(sym));
        Some(
            upper
                .candidates
                .iter()
                .filter(|value| {
                    let candidate = solver.translate_exp(value);
                    !self.excludes_branch_candidate(solver, &anchor, &candidate)
                })
                .cloned()
                .collect(),
        )
    }

    pub(super) fn excludes_branch_candidate(&self, solver: &Solver<'_, B>, anchor: &Ast, value: &Ast) -> bool {
        if value.z3_ast == anchor.z3_ast {
            return false;
        }
        let asts = &self.index.asts;
        let mut cache = self.index.projection.borrow_mut();
        self.translate_projection_suffix(solver, &mut cache);
        let ProjectionCache { assertions, guards, ordinary, active } = &mut *cache;
        let evaluator = ground::AstEvaluator::new(asts.ctx);
        let replacement = [(anchor.z3_ast, value.z3_ast)];
        let mut rebuilt = HashMap::new();
        for (is_guard, layer, roots, owners) in
            [(false, ordinary, assertions, &self.index.ordinary_asts), (true, active, guards, asts)]
        {
            let facts = layer.anchors.entry(owners.keep(anchor.clone())).or_default();
            let checked = match facts.candidates.get(&value.z3_ast) {
                Some(BranchCheck::ExcludedAt(_)) => return true,
                Some(BranchCheck::Checked(count)) => *count,
                None => 0,
            };
            let mut independent = HashSet::new();
            for (index, &key) in roots.iter().enumerate().skip(facts.indexed) {
                if facts.projection.contains_anchor(key, anchor, value, &mut independent) {
                    facts.related.push((index, key));
                }
            }
            facts.indexed = roots.len();
            let result = facts.related[checked..].iter().find_map(|&(index, key)| {
                let excluded = if asts.ctx.solver_options.branch_candidate_sparse_rewrite {
                    let fact =
                        self.index.rewrites.for_assertion(is_guard).single(anchor.z3_ast, value.z3_ast, key, || {
                            facts.projection.project_assertion(asts, key, anchor, value, &mut rebuilt)
                        });
                    !fact.unchanged && fact.truth == Some(false)
                } else {
                    evaluator.evaluate(key, &replacement).map_or_else(
                        || {
                            let mut residual = asts.get(key).substitute(anchor, value);
                            residual.z3_ast != key && residual.structural_bool() == Some(false)
                        },
                        |(truth, changed)| changed && !truth,
                    )
                };
                excluded.then_some(index)
            });
            let progress = result.map_or(BranchCheck::Checked(facts.related.len()), BranchCheck::ExcludedAt);
            facts.candidates.insert(owners.keep(value.clone()), progress);
            if result.is_some() {
                return true;
            }
        }
        false
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
