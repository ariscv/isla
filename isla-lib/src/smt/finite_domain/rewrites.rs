//! 这些表只存 Z3 表达式的纯改写。每个键、残余和字面量都由本代的 Context 引用保活。
use super::*;
use crate::executor::stats::memory_stats::map_bytes;
use prefix_index::ProjectionAsts;
use std::mem::size_of;

type Replacement = (Z3_ast, Z3_ast);
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

pub(super) struct Rewrites<'ctx> {
    single: Recent<'ctx, (Z3_ast, Z3_ast, Z3_ast), ProjectedFact>,
    joint: Recent<'ctx, Vec<Replacement>, ByAssertion>,
    simplified: Recent<'ctx, Z3_ast, (Option<bool>, Z3_ast)>,
}

impl<'ctx> Rewrites<'ctx> {
    pub(super) fn new(ctx: &'ctx Context) -> Self {
        Self { single: Recent::new(ctx), joint: Recent::new(ctx), simplified: Recent::new(ctx) }
    }

    pub(super) fn advance(&mut self) {
        self.single.advance();
        self.joint.advance();
        self.simplified.advance();
    }

    pub(super) fn heap_bytes(&self) -> usize {
        self.single.heap_bytes()
            + self.joint.heap_bytes()
            + self.simplified.heap_bytes()
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
        original: &Ast,
        from: &[Z3_ast],
        to: &[Z3_ast],
    ) -> (bool, Option<bool>, Ast<'ctx>) {
        let find = |g: &Generation<Vec<Replacement>, ByAssertion>| {
            g.entries.borrow().get(replacements).and_then(|m| m.get(&original.z3_ast)).copied()
        };
        let present = find(&self.joint.current);
        let fact = present.or_else(|| find(&self.joint.previous)).unwrap_or_else(|| {
            let mut residual = original.substitute_many(from, to);
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

    pub(super) fn simplified(&self, original: Ast<'ctx>) -> (Option<bool>, Ast<'ctx>) {
        let key = original.z3_ast;
        if let Some(&(truth, raw)) = self.simplified.current.entries.borrow().get(&key) {
            return (truth, self.simplified.current.asts.get(raw));
        }
        self.simplified.current.asts.retain(key);
        let (truth, raw) = self.simplified.previous.entries.borrow().get(&key).copied().unwrap_or_else(|| {
            let mut value = original;
            (value.structural_bool(), self.simplified.current.asts.keep(value))
        });
        self.simplified.current.asts.retain(raw);
        self.simplified.current.entries.borrow_mut().insert(key, (truth, raw));
        (truth, self.simplified.current.asts.get(raw))
    }
}
