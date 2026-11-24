//! 这些表只存 Z3 表达式的纯改写。每个键、残余和字面量都由本代的 Context 引用保活。
use super::*;
use crate::executor::stats::memory_stats::map_bytes;
use prefix_index::ProjectionAsts;
use std::mem::size_of;

type Replacement = (Z3_ast, Z3_ast);
type ByNode = HashMap<Z3_ast, Z3_ast>;
type ByAssertion = HashMap<Z3_ast, Narrowed>;

#[derive(Clone, Copy)]
struct Narrowed {
    unchanged: bool,
    truth: Option<bool>,
    residual: Z3_ast,
}

struct Generation<'ctx, K, V> {
    asts: ProjectionAsts<'ctx>,
    entries: RefCell<HashMap<K, V>>,
}

impl<'ctx, K, V> Generation<'ctx, K, V> {
    fn new(ctx: &'ctx Context) -> Self {
        Self { asts: ProjectionAsts::new(ctx), entries: Default::default() }
    }

    fn heap_bytes(&self) -> usize {
        self.asts.heap_bytes() + map_bytes::<K, V>(self.entries.borrow().capacity())
    }
}

// 单锚点和联合边界可以相隔多个臂。每张表只在自身被查询后换代。
struct Recent<'ctx, K, V> {
    current: Generation<'ctx, K, V>,
    previous: Generation<'ctx, K, V>,
}

impl<'ctx, K, V> Recent<'ctx, K, V> {
    fn new(ctx: &'ctx Context) -> Self {
        Self { current: Generation::new(ctx), previous: Generation::new(ctx) }
    }

    fn advance(&mut self) {
        if !self.current.entries.get_mut().is_empty() {
            self.previous = std::mem::replace(&mut self.current, Generation::new(self.previous.asts.ctx));
        }
    }

    fn heap_bytes(&self) -> usize {
        self.current.heap_bytes() + self.previous.heap_bytes()
    }
}

/// 普通断言的改写按 AST 和实际代入项共享。守卫及临时绑定随活跃臂换代。
pub(super) struct ScopedRewriteCache<'ctx> {
    base_rewrites: Option<Rewrites<'ctx>>,
    guard_rewrites: Rewrites<'ctx>,
}

impl<'ctx> ScopedRewriteCache<'ctx> {
    pub(super) fn new(ctx: &'ctx Context) -> Self {
        Self {
            base_rewrites: (ctx.solver_options.retain_ordinary_prefix_cache
                || ctx.solver_options.incremental_choice_dag)
                .then(|| Rewrites::new(ctx)),
            guard_rewrites: Rewrites::new(ctx),
        }
    }

    pub(super) fn for_assertion(&self, is_guard: bool) -> &Rewrites<'ctx> {
        if is_guard {
            &self.guard_rewrites
        } else {
            self.base_rewrites.as_ref().unwrap_or(&self.guard_rewrites)
        }
    }

    pub(super) fn advance(&mut self) {
        self.guard_rewrites.advance();
        // 释放缓存页的软水位。约束与可枚举候选的数量不受此值限制。
        if let Some(base) = &mut self.base_rewrites {
            if base.single.current.asts.ctx.solver_options.retain_ordinary_prefix_cache {
                if base.retained_ast_count() > 32_768 {
                    base.advance();
                }
            } else if base.retained_ast_count() > 32_768 {
                *base = Rewrites::new(base.single.current.asts.ctx);
            }
        }
    }

    pub(super) fn heap_bytes(&self) -> usize {
        self.guard_rewrites.heap_bytes() + self.base_rewrites.as_ref().map_or(0, Rewrites::heap_bytes)
    }
}

pub(super) struct Rewrites<'ctx> {
    single: Recent<'ctx, (Z3_ast, Z3_ast, Z3_ast), ProjectedFact>,
    joint: Recent<'ctx, Vec<Replacement>, ByAssertion>,
    subgraphs: Generation<'ctx, Vec<Replacement>, ByNode>,
    subgraph_count: Cell<usize>,
    simplified: Recent<'ctx, Z3_ast, (Option<bool>, Z3_ast)>,
}

impl<'ctx> Rewrites<'ctx> {
    pub(super) fn new(ctx: &'ctx Context) -> Self {
        Self {
            single: Recent::new(ctx),
            joint: Recent::new(ctx),
            subgraphs: Generation::new(ctx),
            subgraph_count: Cell::new(0),
            simplified: Recent::new(ctx),
        }
    }

    pub(super) fn advance(&mut self) {
        self.single.advance();
        self.joint.advance();
        self.simplified.advance();
    }

    fn retained_ast_count(&self) -> usize {
        self.single.current.asts.retained_count()
            + self.joint.current.asts.retained_count()
            + self.simplified.current.asts.retained_count()
    }

    pub(super) fn heap_bytes(&self) -> usize {
        self.single.heap_bytes()
            + self.joint.heap_bytes()
            + self.simplified.heap_bytes()
            + self.subgraphs.heap_bytes()
            + self
                .subgraphs
                .entries
                .borrow()
                .iter()
                .map(|(key, values)| {
                    key.capacity() * size_of::<Replacement>() + map_bytes::<Z3_ast, Z3_ast>(values.capacity())
                })
                .sum::<usize>()
            + [&self.joint.current, &self.joint.previous]
                .into_iter()
                .map(|g| {
                    g.entries
                        .borrow()
                        .iter()
                        .map(|(key, values)| {
                            key.capacity() * size_of::<Replacement>() + map_bytes::<Z3_ast, Narrowed>(values.capacity())
                        })
                        .sum::<usize>()
                })
                .sum::<usize>()
    }

    pub(super) fn single(
        &self,
        anchor: Z3_ast,
        value: Z3_ast,
        root: Z3_ast,
        compute: impl FnOnce() -> ProjectedFact,
    ) -> ProjectedFact {
        let key = (anchor, value, root);
        if let Some(&fact) = self.single.current.entries.borrow().get(&key) {
            return fact;
        }
        let fact = self.single.previous.entries.borrow().get(&key).copied().unwrap_or_else(compute);
        for key in [anchor, value, root].into_iter().chain(fact.literal) {
            self.single.current.asts.retain(key);
        }
        self.single.current.entries.borrow_mut().insert(key, fact);
        fact
    }

    pub(super) fn narrow(
        &self,
        replacements: &[Replacement],
        original: &Ast<'ctx>,
        dependencies: &mut InputDependencies,
    ) -> (bool, Option<bool>, Ast<'ctx>) {
        if replacements.is_empty() {
            let (truth, residual) = self.simplified(original.clone());
            return (true, truth, residual);
        }
        let find = |g: &Generation<Vec<Replacement>, ByAssertion>| {
            g.entries.borrow().get(replacements).and_then(|m| m.get(&original.z3_ast)).copied()
        };
        let present = find(&self.joint.current);
        let fact = present.or_else(|| find(&self.joint.previous)).unwrap_or_else(|| {
            if let Some((truth, changed)) =
                ground::AstEvaluator::new(original.ctx).evaluate(original.z3_ast, replacements)
            {
                return Narrowed {
                    unchanged: !changed,
                    truth: Some(truth),
                    residual: self.joint.current.asts.keep(Ast::mk_bool(original.ctx, truth)),
                };
            }
            let mut residual = if original.ctx.solver_options.joint_candidate_sparse_rewrite {
                self.substitute_subgraphs(original, replacements, dependencies)
            } else {
                let (from, to): (Vec<_>, Vec<_>) = replacements.iter().copied().unzip();
                original.substitute_many(&from, &to)
            };
            Narrowed {
                unchanged: residual.z3_ast == original.z3_ast,
                truth: residual.structural_bool(),
                residual: self.joint.current.asts.keep(residual),
            }
        });
        if present.is_none() {
            let mut tables = self.joint.current.entries.borrow_mut();
            if !tables.contains_key(replacements) {
                for &(a, v) in replacements {
                    self.joint.current.asts.retain(a);
                    self.joint.current.asts.retain(v);
                }
                tables.insert(replacements.to_vec(), HashMap::new());
            }
            self.joint.current.asts.retain(original.z3_ast);
            self.joint.current.asts.retain(fact.residual);
            tables.get_mut(replacements).unwrap().insert(original.z3_ast, fact);
        }
        (fact.unchanged, fact.truth, self.joint.current.asts.get(fact.residual))
    }

    pub(super) fn after_narrow(&self, truth: Option<bool>, residual: Ast<'ctx>) -> (Option<bool>, Ast<'ctx>) {
        if residual.ctx.solver_options.reuse_narrow_truth
            && residual.ctx.has_unbounded_rewriting()
            && (truth.is_some() || projection::is_literal_shape(&residual))
        {
            return (truth, residual);
        }
        // 未知的复杂残余仍需走原入口，不能用前一次 Z3 输出推定不动点。
        #[cfg(test)]
        AFTER_NARROW.set(AFTER_NARROW.get() + 1);
        self.simplified(residual)
    }

    pub(super) fn simplified(&self, original: Ast<'ctx>) -> (Option<bool>, Ast<'ctx>) {
        let key = original.z3_ast;
        if let Some(&(truth, raw)) = self.simplified.current.entries.borrow().get(&key) {
            return (truth, self.simplified.current.asts.get(raw));
        }
        self.simplified.current.asts.retain(key);
        let (truth, raw) = self.simplified.previous.entries.borrow().get(&key).copied().unwrap_or_else(|| {
            if let Some((truth, _)) = ground::AstEvaluator::new(original.ctx).evaluate(key, &[]) {
                return (Some(truth), self.simplified.current.asts.keep(Ast::mk_bool(original.ctx, truth)));
            }
            let mut value = original;
            (value.structural_bool(), self.simplified.current.asts.keep(value))
        });
        self.simplified.current.asts.retain(raw);
        self.simplified.current.entries.borrow_mut().insert(key, (truth, raw));
        (truth, self.simplified.current.asts.get(raw))
    }
}

// 根由本次联合查询持有。取模碰撞只多标记依赖，不漏掉实际的替换。
pub(super) struct InputDependencies {
    anchors: HashMap<Z3_ast, u128>,
    nodes: ahash::AHashMap<Z3_ast, u128>,
}

impl InputDependencies {
    pub(super) fn new(inputs: impl Iterator<Item = (usize, Z3_ast)>) -> Self {
        let mut anchors = HashMap::new();
        for (index, anchor) in inputs {
            *anchors.entry(anchor).or_insert(0) |= arithmetic::input_bit(index);
        }
        Self { anchors, nodes: Default::default() }
    }

    pub(super) fn mask(&mut self, root: Z3_ast, z3: Z3_context) -> u128 {
        if let Some(&mask) = self.nodes.get(&root) {
            return mask;
        }
        let mut pending = vec![(root, false)];
        while let Some((node, expanded)) = pending.pop() {
            if self.nodes.contains_key(&node) {
                continue;
            }
            let mut mask = self.anchors.get(&node).copied().unwrap_or(0);
            unsafe {
                match Z3_get_ast_kind(z3, node) {
                    AstKind::App => {
                        let app = Z3_to_app(z3, node);
                        let children = (0..Z3_get_app_num_args(z3, app)).map(|i| Z3_get_app_arg(z3, app, i));
                        if !expanded {
                            pending.push((node, true));
                            pending.extend(
                                children.filter(|child| !self.nodes.contains_key(child)).map(|child| (child, false)),
                            );
                            continue;
                        }
                        for child in children {
                            mask |= self.nodes[&child];
                        }
                    }
                    AstKind::Numeral | AstKind::Var => (),
                    // Z3 按完整替换表处理量词的绑定深度和模式。
                    _ => mask = u128::MAX,
                }
            }
            self.nodes.insert(node, mask);
        }
        self.nodes[&root]
    }
}

impl<'ctx> Rewrites<'ctx> {
    fn substitute_subgraphs(
        &self,
        original: &Ast<'ctx>,
        replacements: &[Replacement],
        dependencies: &mut InputDependencies,
    ) -> Ast<'ctx> {
        // 一个长式约有 18,000 个节点。保留约三个长式的改写条目，
        // 在整次重建完成后统一释放，工作表仍可覆盖单个更大的输入。
        const SUBGRAPH_LIMIT: usize = 65_536;
        let z3 = original.ctx.z3_ctx;
        let root = original.z3_ast;
        let active = replacements.iter().fold(0, |mask, (from, _)| mask | dependencies.anchors[from]);
        if dependencies.mask(root, z3) & active == 0 {
            return original.clone();
        }
        let mut tables = self.subgraphs.entries.borrow_mut();
        let asts = &self.subgraphs.asts;
        let mut vectors = ahash::AHashMap::new();
        let mut done = ahash::AHashMap::new();
        let mut pending = vec![(root, false)];
        while let Some((node, expanded)) = pending.pop() {
            if done.contains_key(&node) {
                continue;
            }
            let mask = dependencies.nodes[&node] & active;
            if mask == 0 {
                continue;
            }
            // 命中父节点即结束，恒等替换也遮住其后代。新值不再参与本次代入。
            if let Some(&(_, to)) = replacements.iter().find(|&&(from, _)| from == node) {
                done.insert(node, to);
                continue;
            }
            let local = vectors.entry(mask).or_insert_with(|| {
                replacements
                    .iter()
                    .copied()
                    .filter(|(from, _)| dependencies.anchors[from] & mask != 0)
                    .collect::<Vec<_>>()
            });
            if let Some(&cached) = tables.get(local.as_slice()).and_then(|table| table.get(&node)) {
                done.insert(node, cached);
                continue;
            }
            let result = unsafe {
                if Z3_get_ast_kind(z3, node) == AstKind::App {
                    let app = Z3_to_app(z3, node);
                    let count = Z3_get_app_num_args(z3, app);
                    let children = (0..count).map(|i| Z3_get_app_arg(z3, app, i));
                    if !expanded {
                        pending.push((node, true));
                        pending.extend(
                            children
                                .filter(|child| dependencies.nodes[child] & active != 0)
                                .map(|child| (child, false)),
                        );
                        continue;
                    }
                    let mut changed = false;
                    let args: Vec<_> = children
                        .map(|child| {
                            let value = done.get(&child).copied().unwrap_or(child);
                            changed |= value != child;
                            value
                        })
                        .collect();
                    if changed {
                        Z3_update_term(z3, node, count, args.as_ptr())
                    } else {
                        node
                    }
                } else if Z3_get_ast_kind(z3, node) == AstKind::Quantifier {
                    let (from, to): (Vec<_>, Vec<_>) = replacements.iter().copied().unzip();
                    asts.retain(node);
                    asts.keep(asts.get(node).substitute_many(&from, &to))
                } else {
                    node
                }
            };
            if !tables.contains_key(local.as_slice()) {
                for &(from, to) in local.iter() {
                    asts.retain(from);
                    asts.retain(to);
                }
                tables.insert(local.clone(), HashMap::new());
            }
            asts.retain(node);
            asts.retain(result);
            self.subgraph_count.set(self.subgraph_count.get() + 1);
            tables.get_mut(local.as_slice()).unwrap().insert(node, result);
            done.insert(node, result);
        }
        let result = done[&root];
        asts.retain(result);
        let result = asts.get(result);
        if self.subgraph_count.get() >= SUBGRAPH_LIMIT {
            tables.clear();
            asts.release_all();
            self.subgraph_count.set(0);
        }
        result
    }
}
