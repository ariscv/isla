use super::*;
use std::cell::OnceCell;

pub(in crate::smt) const BUFFERED: usize = usize::MAX;

// 已发布的段号在建检查点后保持不变；缓冲区使用单独的段号。
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Position(usize, usize);

pub(in crate::smt) struct PrefixIndex<'ctx> {
    symbols: ahash::AHashMap<Sym, Position>,
    rebindings: usize,
    assertions: Vec<Position>,
    bool_symbols: Vec<(Position, Sym)>,
    pub(super) projection: RefCell<ProjectionCache>,
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
    pub(super) dependencies: HashMap<Z3_ast, bool>,
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
    ctx: &'ctx Context,
    refs: RefCell<HashSet<Z3_ast>>,
}

impl<'ctx> ProjectionAsts<'ctx> {
    pub(super) fn keep(&self, ast: Ast<'_>) -> Z3_ast {
        assert!(std::ptr::eq(self.ctx, ast.ctx));
        let key = ast.z3_ast;
        if self.refs.borrow_mut().insert(key) {
            std::mem::forget(ast);
        }
        key
    }

    pub(super) fn get(&self, key: Z3_ast) -> Ast<'ctx> {
        assert!(self.refs.borrow().contains(&key));
        unsafe { Z3_inc_ref(self.ctx.z3_ctx, key) };
        Ast { ctx: self.ctx, z3_ast: key }
    }

    // 子节点由当前前缀持有的根保活。显式后序遍历不占 Rust 递归栈。
    fn contains_anchor(&self, root: Z3_ast, anchor: &Ast, probe: &Ast, nodes: &mut HashMap<Z3_ast, bool>) -> bool {
        let ctx = self.ctx.z3_ctx;
        let mut pending = vec![(root, false)];
        while let Some((node, expanded)) = pending.pop() {
            if nodes.contains_key(&node) {
                continue;
            }
            let found = if node == anchor.z3_ast {
                true
            } else {
                unsafe {
                    match Z3_get_ast_kind(ctx, node) {
                        AstKind::Numeral | AstKind::Var => false,
                        AstKind::App => {
                            let app = Z3_to_app(ctx, node);
                            let mut children = (0..Z3_get_app_num_args(ctx, app)).map(|i| Z3_get_app_arg(ctx, app, i));
                            if !expanded {
                                pending.push((node, true));
                                pending.extend(children.map(|child| (child, false)));
                                continue;
                            }
                            children.any(|child| nodes[&child])
                        }
                        // 对带绑定器等未遍历的形式，保留原生非恒等代入的判定。
                        _ => return self.get(root).substitute(anchor, probe).z3_ast != root,
                    }
                }
            };
            nodes.insert(node, found);
        }
        nodes[&root]
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
    pub(in crate::smt) fn new(ctx: &'ctx Context) -> Self {
        Self {
            symbols: Default::default(),
            rebindings: 0,
            assertions: Vec::new(),
            bool_symbols: Vec::new(),
            projection: RefCell::default(),
            asts: ProjectionAsts { ctx, refs: RefCell::default() },
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
            } else {
                self.rebindings += 1;
                self.invalidate_candidates();
            }
            if boolean {
                self.bool_symbols.push((position, sym));
            }
        } else if matches!(event, Event::Smt(Def::Assert(_), ..)) {
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
                } else {
                    self.rebindings -= 1;
                }
            }
        }
        if start < events.len() {
            self.invalidate_candidates();
        }
    }

    pub(in crate::smt) fn invalidate_candidates(&mut self) {
        *self.projection.get_mut() = ProjectionCache::default();
        self.asts.clear();
        *self.branch.get_mut() = None;
    }

    pub(in crate::smt) fn heap_bytes(&self) -> usize {
        use crate::executor::stats::memory_stats::{exp_heap_bytes, map_bytes};
        use std::mem::size_of;

        let cache = self.projection.borrow();
        (cache.assertions.capacity() + cache.guards.capacity()) * size_of::<Z3_ast>()
            + map_bytes::<Z3_ast, (Option<bool>, Z3_ast)>(cache.simplified.capacity())
            + map_bytes::<Z3_ast, ()>(self.asts.refs.borrow().capacity())
            + map_bytes::<Z3_ast, AnchorFacts>(cache.anchors.capacity())
            + cache
                .anchors
                .values()
                .map(|facts| {
                    map_bytes::<Z3_ast, bool>(facts.dependencies.capacity())
                        + facts.related.capacity() * size_of::<Z3_ast>()
                        + map_bytes::<Z3_ast, BranchCheck>(facts.candidates.capacity())
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

    pub(super) fn translate_projection_suffix(&self, solver: &Solver<'_, B>, cache: &mut ProjectionCache) {
        for &position in &self.index.assertions[cache.assertions.len()..] {
            cache
                .assertions
                .push(self.index.asts.keep(solver.translate_projection_assertion(self.assertion(position))));
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
        let mut nodes = HashMap::new();
        for &key in assertions[facts.indexed_assertions..].iter().chain(&guards[facts.indexed_guards..]) {
            if *facts.dependencies.entry(key).or_insert_with(|| asts.contains_anchor(key, anchor, value, &mut nodes)) {
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
