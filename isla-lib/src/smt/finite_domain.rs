//! 从当前路径提取位向量的有限值域。只化简表达式，不做 SMT 查询。
use super::*;

mod arithmetic;
mod prefix_index;
use prefix_index::{BranchCandidates, Candidate, PathConditions, ProjectionCache};
pub(super) use prefix_index::{PrefixIndex, BUFFERED};

#[cfg_attr(test, derive(Debug, PartialEq))]
pub(crate) enum FiniteDomain {
    Known(Vec<Exp<Sym>>),
    /// 包含全部可行取值，个别候选还可能被残余约束排除。
    Bounded(Vec<Exp<Sym>>),
    Unknown,
}

type Bound = Option<Vec<Exp<Sym>>>;

fn intersect(lhs: Bound, rhs: Bound) -> Bound {
    match (lhs, rhs) {
        (Some(mut lhs), Some(rhs)) => {
            lhs.retain(|value| rhs.contains(value));
            Some(lhs)
        }
        (lhs, rhs) => lhs.or(rhs),
    }
}

fn union(lhs: Bound, rhs: Bound) -> Bound {
    let (mut lhs, rhs) = (lhs?, rhs?);
    for value in rhs {
        if !lhs.contains(&value) {
            lhs.push(value);
        }
    }
    Some(lhs)
}

fn resolve<'a, B: BV>(mut exp: &'a Exp<Sym>, prefix: &'a PathConditions<'_, B>) -> &'a Exp<Sym> {
    while let Exp::Var(sym) = exp {
        let Some(definition) = prefix.definition(*sym) else { break };
        exp = definition;
    }
    exp
}

fn implies_equality<B: BV>(
    guard: &Exp<Sym>,
    lhs: &Exp<Sym>,
    rhs: &Exp<Sym>,
    prefix: &PathConditions<'_, B>,
    mut negated: bool,
    visited: &mut HashSet<(*const Exp<Sym>, bool)>,
) -> bool {
    let mut guard = resolve(guard, prefix);
    while let Exp::Not(inner) = guard {
        negated = !negated;
        guard = resolve(inner, prefix);
    }
    match guard {
        Exp::Eq(a, b) | Exp::Neq(a, b) if matches!(guard, Exp::Neq(..)) == negated => {
            (&**a == lhs && &**b == rhs) || (&**b == lhs && &**a == rhs)
        }
        Exp::And(a, b) | Exp::Or(a, b) if matches!(guard, Exp::Or(..)) == negated => {
            visited.insert((guard, negated))
                && (implies_equality(a, lhs, rhs, prefix, negated, visited)
                    || implies_equality(b, lhs, rhs, prefix, negated, visited))
        }
        _ => false,
    }
}

fn constant(exp: &Exp<Sym>) -> Option<Exp<Sym>> {
    match exp {
        Exp::Bits(bits) if bits.len() <= 64 => {
            let value = bits.iter().rev().fold(0, |word, bit| (word << 1) | u64::from(*bit));
            Some(bits64(value, bits.len() as u32))
        }
        Exp::Bits(_) | Exp::Bits64(_) => Some(exp.clone()),
        _ => None,
    }
}

// 掩码覆盖目标切片的每一位时，等式给出切片的唯一候选。
fn masked_slice<B: BV>(
    target: &Exp<Sym>,
    masked: &Exp<Sym>,
    result: &Exp<Sym>,
    prefix: &PathConditions<'_, B>,
) -> Option<Exp<Sym>> {
    let Exp::Extract(high, low, source) = target else { return None };
    let Exp::Bvand(lhs, rhs) = masked else { return None };
    let (lhs, rhs, source) = (resolve(lhs, prefix), resolve(rhs, prefix), resolve(source, prefix));
    let mask = if lhs == source {
        rhs
    } else if rhs == source {
        lhs
    } else {
        return None;
    };
    match mask {
        Exp::Bits64(bits) if bits.extract(*high, *low).is_some_and(|slice| slice == B64::ones(slice.len())) => (),
        Exp::Bits(bits) if bits.get(*low as usize..=*high as usize)?.iter().all(|bit| *bit) => (),
        _ => return None,
    }
    match result {
        Exp::Bits64(bits) => bits.extract(*high, *low).map(Exp::Bits64),
        Exp::Bits(bits) => constant(&Exp::Bits(bits.get(*low as usize..=*high as usize)?.to_vec())),
        _ => None,
    }
}

// 只识别能产生有限上界的布尔形式。排除项与其他谓词在代入候选后检查。
fn bound<B: BV>(exp: &Exp<Sym>, target: &Exp<Sym>, prefix: &PathConditions<'_, B>, negated: bool) -> Bound {
    use Exp::*;
    let visit = |child, negated| bound(child, target, prefix, negated);
    let exp = resolve(exp, prefix);
    match exp {
        Eq(lhs, rhs) | Neq(lhs, rhs) if matches!(exp, Eq(..)) != negated => {
            let (lhs, rhs) = (resolve(lhs, prefix), resolve(rhs, prefix));
            let value = if lhs == target {
                constant(rhs)
            } else if rhs == target {
                constant(lhs)
            } else {
                masked_slice(target, lhs, rhs, prefix).or_else(|| masked_slice(target, rhs, lhs, prefix))
            };
            value.map(|value| vec![value])
        }
        Not(inner) => visit(inner, !negated),
        And(lhs, rhs) | Or(lhs, rhs) => {
            let combine = if matches!(exp, And(..)) != negated { intersect } else { union };
            combine(visit(lhs, negated), visit(rhs, negated))
        }
        Ite(condition, yes, no) => union(
            intersect(visit(condition, false), visit(yes, negated)),
            intersect(visit(condition, true), visit(no, negated)),
        ),
        Bool(value) if *value == negated => Some(Vec::new()),
        _ => None,
    }
}

// 定义为 ITE 的位向量即使没有显式等式断言，两个值臂也可给出上界。
fn value_bound<B: BV>(exp: &Exp<Sym>, prefix: &PathConditions<'_, B>) -> Bound {
    let exp = resolve(exp, prefix);
    if let Exp::Ite(_, yes, no) = exp {
        union(value_bound(yes, prefix), value_bound(no, prefix))
    } else {
        constant(exp).map(|value| vec![value])
    }
}

impl<B: BV> PathConditions<'_, B> {
    // 只从公式显式给出的有限集合取值。自由位向量的位宽不能作为枚举依据。
    fn bounds(&self, subject: &Exp<Sym>) -> Bound {
        #[cfg(test)]
        BOUND_SEARCHES.set(BOUND_SEARCHES.get() + 1);
        let subject = resolve(subject, self);
        let mut candidates = value_bound(subject, self);
        for assertion in self.assertions() {
            candidates = intersect(candidates, bound(assertion, subject, self, false));
        }
        candidates.or_else(|| match subject {
            Exp::Ite(_, yes, no) => union(self.bounds(yes), self.bounds(no)),
            _ => None,
        })
    }

    fn comparison_subjects<'a>(&'a self, exp: &'a Exp<Sym>, subjects: &mut Vec<&'a Exp<Sym>>) {
        use Exp::*;
        match resolve(exp, self) {
            Eq(lhs, rhs) | Neq(lhs, rhs) => {
                for (symbolic, concrete) in [(lhs, rhs), (rhs, lhs)] {
                    if constant(resolve(concrete, self)).is_some() && constant(resolve(symbolic, self)).is_none() {
                        subjects.push(symbolic);
                    }
                }
            }
            Not(inner) => self.comparison_subjects(inner, subjects),
            And(lhs, rhs) | Or(lhs, rhs) => {
                self.comparison_subjects(lhs, subjects);
                self.comparison_subjects(rhs, subjects);
            }
            _ => (),
        }
    }
}

// structural_bool 可能替换 AST。字面量必须用化简后的残余式识别。
struct ProjectionLiterals {
    values: HashMap<Sym, bool>,
    only_literals: bool,
}

impl ProjectionLiterals {
    fn new() -> Self {
        Self { values: HashMap::new(), only_literals: true }
    }

    fn record(&mut self, literal: Option<(Sym, bool)>, common: &HashMap<Sym, bool>) -> bool {
        if let Some((sym, positive)) = literal {
            if let Some(previous) = common.get(&sym) {
                return *previous == positive;
            }
            return self.values.insert(sym, positive).is_none_or(|previous| previous == positive);
        }
        self.only_literals = false;
        true
    }
}

impl<'ctx> Ast<'ctx> {
    fn substitute(&self, old: &Self, new: &Self) -> Self {
        self.substitute_many(&[old.z3_ast], &[new.z3_ast])
    }

    fn substitute_many(&self, old: &[Z3_ast], new: &[Z3_ast]) -> Self {
        if old.is_empty() {
            return self.clone();
        }
        #[cfg(test)]
        PROJECT_SUBSTITUTIONS.set(PROJECT_SUBSTITUTIONS.get() + 1);
        assert_eq!(old.len(), new.len());
        unsafe {
            let z3_ast =
                Z3_substitute(self.ctx.z3_ctx, self.z3_ast, old.len().try_into().unwrap(), old.as_ptr(), new.as_ptr());
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Self { z3_ast, ctx: self.ctx }
        }
    }

    fn finite_bits(&mut self) -> Option<Exp<Sym>> {
        self.simplify();
        let width = unsafe {
            let ctx = self.ctx.z3_ctx;
            let sort = Z3_get_sort(ctx, self.z3_ast);
            if Z3_get_sort_kind(ctx, sort) != SortKind::BV || !Z3_is_numeral_ast(ctx, self.z3_ast) {
                return None;
            }
            Z3_get_bv_sort_size(ctx, sort)
        };
        if width <= 64 {
            return Some(bits64(self.get_numeral_u64().expect("位向量常量必须能读取"), width));
        }
        let mut bits = Vec::with_capacity(width as usize);
        for low in (0..width).step_by(64) {
            let size = (width - low).min(64);
            let mut part = self.extract(low + size - 1, low);
            part.simplify();
            let word = part.get_numeral_u64().expect("常量的位向量切片必须能读取");
            bits.extend((0..size).map(|index| word >> index & 1 != 0));
        }
        Some(Exp::Bits(bits))
    }
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    pub(crate) fn finite_domain_enabled(&self) -> bool {
        self.finite_prefix.is_some()
    }

    /// 一条路径可以复用其自身的标签约束。仅证明蕴含，路径可满足性另行判定。
    pub(crate) fn path_implies_tag(&self, tag: Sym, ctor: Name) -> bool {
        if self.transaction_invalid() {
            return false;
        }
        let Some(prefix) = PathConditions::new(self) else { return false };
        let lhs = Exp::Var(tag);
        let rhs = ctor.to_smt();
        let mut visited = HashSet::new();
        let implied =
            prefix.path_guards().any(|guard| implies_equality(guard, &lhs, &rhs, &prefix, false, &mut visited));
        implied
    }

    /// 指令级重试也能利用已有的穷尽约束。默认不维护全路径索引时，
    /// 只在这次重试的作用域内建立索引，后续的保存点操作走同一入口。
    pub(crate) fn with_finite_domain<T>(&mut self, use_domain: impl FnOnce(&mut Self) -> T) -> T {
        assert!(self.finite_prefix.is_none(), "有限域索引必须只安装一次");
        let mut segments: Vec<_> =
            std::iter::successors(Some(&self.trace), |trace| trace.tail.as_ref().as_ref()).collect();
        let mut index = PrefixIndex::new(self.ctx);
        for trace in segments.drain(..).rev() {
            for (offset, event) in trace.head_events().enumerate() {
                index.push(trace.checkpoints, offset, event);
            }
        }
        for (offset, event) in self.transaction_events.iter().enumerate() {
            index.push(BUFFERED, offset, event);
        }
        self.finite_prefix = Some(index);
        let result = use_domain(self);
        self.finite_prefix = None;
        result
    }

    /// 条件在所有剩余候选中同值时才折叠。只证明蕴含，完整前缀仍由原入口认证。
    pub(crate) fn finite_domain_bool(&self, exp: &Exp<Sym>) -> Option<bool> {
        let prefix = PathConditions::new(self)?;
        let mut subjects = Vec::new();
        prefix.comparison_subjects(exp, &mut subjects);
        let predicate = self.translate_exp(exp);
        if subjects.is_empty() {
            return None;
        }

        // 两侧仍分别化简各自的谓词。共享候选及排除结果，空域时两侧均可判死。
        let mut branch_exp = exp;
        while let Exp::Not(inner) = branch_exp {
            branch_exp = inner;
        }
        let mut cache = prefix.index.branch.borrow_mut();
        if cache.as_ref().is_none_or(|entry| &entry.predicate != branch_exp) {
            *cache = Some(BranchCandidates { predicate: branch_exp.clone(), subjects: Vec::new() });
        }
        let prepared = &mut cache.as_mut().unwrap().subjects;
        for (index, subject) in subjects.into_iter().enumerate() {
            if index == prepared.len() {
                prepared.push(prefix.bounds(subject).map(|candidates| {
                    candidates.into_iter().map(|value| Candidate { value, excluded: None }).collect()
                }));
            }
            let Some(candidates) = &mut prepared[index] else { continue };
            let anchor = self.translate_exp(subject);
            let mut result = None;
            let mut undecided = false;
            for candidate in candidates {
                let value = self.translate_exp(&candidate.value);
                if *candidate.excluded.get_or_insert_with(|| {
                    prefix.assertions().any(|fact| {
                        let original = self.translate_exp(fact);
                        let mut narrowed = original.substitute(&anchor, &value);
                        narrowed.z3_ast != original.z3_ast && narrowed.structural_bool() == Some(false)
                    })
                }) {
                    continue;
                }
                match predicate.substitute(&anchor, &value).structural_bool() {
                    Some(current) if result.is_none() || result == Some(current) => result = Some(current),
                    _ => {
                        undecided = true;
                        break;
                    }
                }
            }
            if !undecided {
                return result.or(Some(false));
            }
        }
        None
    }

    /// 在需要证明原语联合边界时，按同一组输入检查整个谓词。
    pub(crate) fn finite_domain_predicate(&self, exp: &Exp<Sym>) -> Option<bool> {
        let prefix = PathConditions::new(self)?;
        let mut answer = None;
        self.combined_values(&prefix, exp, |mut value, _| {
            let current = value.structural_bool().expect("有限域谓词必须为布尔常量");
            if answer.is_some_and(|previous| previous != current) {
                answer = None;
                false
            } else {
                answer = Some(current);
                true
            }
        })?;
        answer
    }

    pub(crate) fn note_finite_domain_use(&self, category: &'static str, info: SourceLoc) {
        if self.no_smt() && crate::config::RegionOptions::current().progress {
            no_smt::record(category, info);
        }
    }

    pub(crate) fn finite_domain(&self, sym: Sym) -> FiniteDomain {
        let Some(prefix) = PathConditions::new(self) else { return FiniteDomain::Unknown };
        let mut pending = vec![sym];
        let mut seen = HashSet::new();
        let mut best = FiniteDomain::Unknown;
        while let Some(subject) = pending.pop() {
            if !seen.insert(subject) {
                continue;
            }
            let source = Exp::Var(subject);
            if let Some(definition) = prefix.definition(subject) {
                let mut dependencies: Vec<_> = definition.variables().into_iter().collect();
                dependencies.sort_by_key(|dep| dep.as_u32());
                pending.extend(dependencies);
            }
            let Some(candidates) = prefix.bounds(&source) else { continue };
            match self.project_finite_values(&prefix, sym, subject, candidates) {
                known @ FiniteDomain::Known(_) => return known,
                bounded @ FiniteDomain::Bounded(_) if matches!(best, FiniteDomain::Unknown) => best = bounded,
                FiniteDomain::Bounded(values) => {
                    if matches!(&best, FiniteDomain::Bounded(previous) if values.len() < previous.len()) {
                        best = FiniteDomain::Bounded(values);
                    }
                }
                FiniteDomain::Unknown => (),
            }
        }
        if !matches!(best, FiniteDomain::Unknown) {
            return best;
        }
        let mut exact = true;
        let mut values = Vec::new();
        let mut seen = HashMap::new();
        if self
            .combined_values(&prefix, &Exp::Var(sym), |mut value, certified| {
                exact &= certified;
                let constant = value.finite_bits().expect("有限域表达式必须为位向量常量");
                if seen.insert(value.z3_ast, value).is_none() {
                    values.push(constant);
                }
                true
            })
            .is_none()
        {
            return FiniteDomain::Unknown;
        }
        if exact {
            FiniteDomain::Known(values)
        } else {
            FiniteDomain::Bounded(values)
        }
    }

    /// 原生化简可能把锚点改写到不再是目标的子表达式。沿原定义逐层代入已知值。
    fn project_finite_definition(
        &self,
        sym: Sym,
        prefix: &PathConditions<'_, B>,
        projected: &mut HashMap<Sym, Option<Exp<Sym>>>,
    ) -> Option<Exp<Sym>> {
        if let Some(value) = projected.get(&sym) {
            return value.clone();
        }
        let value = prefix.definition(sym).and_then(|definition| {
            let mut changed = false;
            let expression = definition
                .map_var(&mut |input| {
                    Ok::<_, std::convert::Infallible>(match self.project_finite_definition(*input, prefix, projected) {
                        Some(value) => {
                            changed = true;
                            value
                        }
                        None => Exp::Var(*input),
                    })
                })
                .unwrap();
            if !changed {
                return None;
            }
            let mut ast = self.translate_exp(&expression);
            ast.finite_bits().or_else(|| ast.structural_bool().map(Exp::Bool))
        });
        projected.insert(sym, value.clone());
        value
    }

    fn translate_projection_assertion(&self, exp: &Exp<Sym>) -> Ast<'ctx> {
        #[cfg(test)]
        PROJECT_TRANSLATIONS.set(PROJECT_TRANSLATIONS.get() + 1);
        self.translate_exp(exp)
    }

    fn project_finite_values(
        &self,
        prefix: &PathConditions<'_, B>,
        target: Sym,
        source: Sym,
        candidates: Vec<Exp<Sym>>,
    ) -> FiniteDomain {
        // 对派生锚点代入时保留原等式，防止把它错误地当成独立自由变量。
        let source_var = Exp::Var(source);
        let free = matches!(resolve(&source_var, prefix), Exp::Var(_));
        let anchor = self.translate_exp(&source_var);
        let target_ast = self.translate_exp(&Exp::Var(target));
        if candidates.is_empty() {
            return FiniteDomain::Known(Vec::new());
        }
        // 已化简的锚点可能等于第一个候选。选第一个非恒等代入来判依赖，
        // 全部相等时只复用本次的公共结果，不向依赖缓存登记“无关”。
        let probe =
            candidates.iter().map(|c| self.translate_exp(c)).enumerate().find(|(_, c)| c.z3_ast != anchor.z3_ast);
        let mut bool_atoms = Vec::new();
        let mut bool_literals = HashMap::new();
        for sym in prefix.bool_symbols() {
            let atom = self.decls[&sym].ast();
            let negative = Ast::mk_not(&atom);
            bool_literals.insert(atom.z3_ast, (sym, true));
            bool_literals.insert(negative.z3_ast, (sym, false));
            bool_atoms.push(negative);
        }
        let mut cache = prefix.index.projection.borrow_mut();
        prefix.translate_projection_suffix(self, &mut cache);
        let ProjectionCache { assertions, guards, anchors, simplified } = &mut *cache;
        let asts = &prefix.index.asts;
        let dependencies = anchors.entry(asts.keep(anchor.clone())).or_default();
        let mut common = ProjectionLiterals::new();
        let empty = HashMap::new();
        let mut dependent = Vec::new();
        for &key in assertions.iter().rev().chain(guards.iter()) {
            if let Some((_, probe_value)) = &probe {
                let mut prepared = None;
                if *dependencies.entry(key).or_insert_with(|| {
                    let residual = asts.get(key).substitute(&anchor, probe_value);
                    if residual.z3_ast == key {
                        false
                    } else {
                        prepared = Some(residual);
                        true
                    }
                }) {
                    dependent.push((asts.get(key), prepared));
                    continue;
                }
            }
            let (truth, residual) = simplified.entry(key).or_insert_with(|| {
                let mut residual = asts.get(key);
                (residual.structural_bool(), asts.keep(residual))
            });
            match truth {
                Some(false) => return FiniteDomain::Known(Vec::new()),
                Some(true) => (),
                None if common.record(bool_literals.get(residual).copied(), &empty) => (),
                None => return FiniteDomain::Known(Vec::new()),
            }
        }

        let mut admissible = Vec::new();
        let mut exact = true;
        'candidate: for (index, candidate) in candidates.into_iter().enumerate() {
            let value = self.translate_exp(&candidate);
            let binding = (!free).then(|| Ast::mk_eq(&anchor, &value));
            let path_facts = dependent.iter().map(|(original, prepared)| {
                let residual = match prepared {
                    Some(first) if Some(index) == probe.as_ref().map(|(index, _)| *index) => first.clone(),
                    _ => original.substitute(&anchor, &value),
                };
                let unchanged = original.z3_ast == residual.z3_ast;
                (residual, unchanged)
            });
            let mut literals = ProjectionLiterals::new();
            let mut can_reuse_witness = self.has_stashed_model();
            for (mut residual, unchanged) in path_facts.chain(binding.map(|eq| (eq, false))) {
                match residual.structural_bool() {
                    Some(false) => continue 'candidate,
                    Some(true) => (),
                    None => {
                        can_reuse_witness &= unchanged;
                        if !literals.record(bool_literals.get(&residual.z3_ast).copied(), &common.values) {
                            continue 'candidate;
                        }
                    }
                }
            }
            let value = match target_ast.substitute(&anchor, &value).finite_bits() {
                Some(value) => value,
                None if !free => {
                    let mut projected = HashMap::from([(source, Some(candidate))]);
                    let Some(value) = self.project_finite_definition(target, prefix, &mut projected) else {
                        return FiniteDomain::Unknown;
                    };
                    // 重试的排除式可能引用遭化简的目标。先在原表达式中代入，再判是否必假。
                    for assertion in prefix.assertions() {
                        let mut changed = false;
                        let substituted = assertion
                            .map_var(&mut |sym| {
                                Ok::<_, std::convert::Infallible>(match projected.get(sym) {
                                    Some(Some(value)) => {
                                        changed = true;
                                        value.clone()
                                    }
                                    _ => Exp::Var(*sym),
                                })
                            })
                            .unwrap();
                        if changed && self.translate_exp(&substituted).structural_bool() == Some(false) {
                            continue 'candidate;
                        }
                    }
                    value
                }
                None => return FiniteDomain::Unknown,
            };
            exact &= (common.only_literals && literals.only_literals) || can_reuse_witness;
            if !admissible.contains(&value) {
                admissible.push(value);
            }
        }
        if exact {
            FiniteDomain::Known(admissible)
        } else {
            FiniteDomain::Bounded(admissible)
        }
    }
}

#[cfg(test)]
thread_local! {
    static PREFIX_EVENT_VISITS: Cell<usize> = const { Cell::new(0) };
    static PROJECT_TRANSLATIONS: Cell<usize> = const { Cell::new(0) };
    static PROJECT_SUBSTITUTIONS: Cell<usize> = const { Cell::new(0) };
    pub(super) static STRUCTURAL_BOOLS: Cell<usize> = const { Cell::new(0) };
    static BOUND_SEARCHES: Cell<usize> = const { Cell::new(0) };
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod arithmetic_tests;
