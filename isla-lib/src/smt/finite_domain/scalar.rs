//! 具体整数消费者共用的结构证明和随臂事实。所有域都是当前前缀下的结论。
use super::*;
use std::ops::RangeInclusive;

pub(super) fn enabled() -> bool {
    crate::config::RegionOptions::current().symbolic_scalar_resolver
}

enum PriorFact {
    Constant(Sym, Option<Exp<Sym>>),
    Range(Sym, Option<RangeInclusive<i128>>),
}

#[derive(Default)]
struct Facts {
    marks: Vec<usize>,
    undo: Vec<PriorFact>,
    constants: HashMap<Sym, Exp<Sym>>,
    ranges: HashMap<Sym, RangeInclusive<i128>>,
}

fn signed(value: &Exp<Sym>) -> Option<i128> {
    match value {
        Exp::Bits64(bits) => Some(bits.signed()),
        Exp::Bits(bits) => crate::primop::i128_from_model_bits(bits),
        _ => None,
    }
}

#[cfg(test)]
thread_local! { pub(super) static PREDICATE_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) }; }

impl Facts {
    fn heap_bytes(&self) -> usize {
        use crate::executor::stats::memory_stats::{exp_heap_bytes, map_bytes};
        use std::mem::size_of;
        self.marks.capacity() * size_of::<usize>()
            + self.undo.capacity() * size_of::<PriorFact>()
            + self
                .undo
                .iter()
                .filter_map(|prior| match prior {
                    PriorFact::Constant(_, Some(value)) => Some(exp_heap_bytes(value)),
                    _ => None,
                })
                .sum::<usize>()
            + map_bytes::<Sym, Exp<Sym>>(self.constants.capacity())
            + self.constants.values().map(exp_heap_bytes).sum::<usize>()
            + map_bytes::<Sym, RangeInclusive<i128>>(self.ranges.capacity())
    }

    fn constant(&mut self, sym: Sym, value: Exp<Sym>) {
        self.undo.push(PriorFact::Constant(sym, self.constants.insert(sym, value)));
    }

    fn intersect(&mut self, sym: Sym, lo: i128, hi: i128) {
        let range = self.ranges.get(&sym).map_or(lo..=hi, |r| lo.max(*r.start())..=hi.min(*r.end()));
        self.undo.push(PriorFact::Range(sym, self.ranges.insert(sym, range)));
    }

    fn truncate(&mut self, depth: usize) {
        if let Some(&start) = self.marks.get(depth) {
            self.marks.truncate(depth);
            for prior in self.undo.drain(start..).rev() {
                match prior {
                    PriorFact::Constant(sym, Some(v)) => {
                        self.constants.insert(sym, v);
                    }
                    PriorFact::Constant(sym, None) => {
                        self.constants.remove(&sym);
                    }
                    PriorFact::Range(sym, Some(r)) => {
                        self.ranges.insert(sym, r);
                    }
                    PriorFact::Range(sym, None) => {
                        self.ranges.remove(&sym);
                    }
                }
            }
        }
    }

    fn record<B: BV>(&mut self, predicate: &Exp<Sym>, prefix: &PathConditions<'_, B>) {
        #[cfg(test)]
        PREDICATE_VISITS.set(PREDICATE_VISITS.get() + 1);
        self.marks.push(self.undo.len());
        use Exp::*;
        let mut pending = vec![(predicate, true)];
        let mut seen = HashSet::new();
        while let Some((exp, truth)) = pending.pop() {
            match exp {
                Var(sym) => {
                    if seen.insert((*sym, truth)) {
                        self.constant(*sym, Bool(truth));
                        pending.extend(prefix.definition(*sym).map(|exp| (exp, truth)));
                    }
                }
                Not(inner) => pending.push((inner, !truth)),
                And(a, b) if truth => pending.extend([(a.as_ref(), truth), (b.as_ref(), truth)]),
                Or(a, b) if !truth => pending.extend([(a.as_ref(), truth), (b.as_ref(), truth)]),
                Eq(a, b) | Neq(a, b) if matches!(exp, Eq(..)) == truth => {
                    for (symbol, value) in [(a, b), (b, a)] {
                        if let Var(sym) = **symbol {
                            let value = resolve(value, prefix);
                            if let Bool(value) = value {
                                pending.push((symbol, *value));
                            } else if let Some(v) = constant(value) {
                                self.constant(sym, v);
                            }
                        }
                    }
                }
                Bvsle(a, b) | Bvslt(a, b) | Bvsge(a, b) | Bvsgt(a, b) => {
                    let (lo, hi) = if matches!(exp, Bvsle(..) | Bvslt(..)) { (a, b) } else { (b, a) };
                    let (lo, hi) = if truth { (lo, hi) } else { (hi, lo) };
                    let strict = matches!(exp, Bvslt(..) | Bvsgt(..)) == truth;
                    if let (Var(sym), Some(v)) = (&**lo, signed(resolve(hi, prefix))) {
                        if let Some(v) = v.checked_sub(i128::from(strict)) {
                            self.intersect(*sym, i128::MIN, v);
                        }
                    }
                    if let (Some(v), Var(sym)) = (signed(resolve(lo, prefix)), &**hi) {
                        if let Some(v) = v.checked_add(i128::from(strict)) {
                            self.intersect(*sym, v, i128::MAX);
                        }
                    }
                }
                _ => (),
            }
        }
    }
}

#[derive(Default)]
pub(super) struct ArmFacts {
    ordinary: Facts,
    guards: Facts,
    derived: HashMap<Sym, Option<Exp<Sym>>>,
}

impl ArmFacts {
    pub(super) fn heap_bytes(&self) -> usize {
        use crate::executor::stats::memory_stats::{exp_heap_bytes, map_bytes};
        self.ordinary.heap_bytes()
            + self.guards.heap_bytes()
            + map_bytes::<Sym, Option<Exp<Sym>>>(self.derived.capacity())
            + self.derived.values().flatten().map(exp_heap_bytes).sum::<usize>()
    }

    pub(super) fn truncate_guards(&mut self, depth: usize) {
        self.guards.truncate(depth);
        self.derived.clear();
    }

    pub(super) fn truncate_assertions(&mut self, depth: usize) {
        self.ordinary.truncate(depth);
        self.derived.clear();
    }

    pub(super) fn choice<B: BV>(
        &mut self,
        exp: &Exp<Sym>,
        solver: &Solver<'_, B>,
        prefix: &PathConditions<'_, B>,
    ) -> Option<bool> {
        self.update(solver, prefix);
        let mut result = self.evaluate(exp, solver);
        while let Err(Some(sym)) = result {
            self.value(sym, solver, prefix);
            result = self.evaluate(exp, solver);
        }
        match result {
            Ok(Exp::Bool(truth)) => Some(truth),
            _ => None,
        }
    }

    fn update<B: BV>(&mut self, solver: &Solver<B>, prefix: &PathConditions<'_, B>) {
        for assertion in prefix.ordinary_suffix(self.ordinary.marks.len()) {
            self.ordinary.record(assertion, prefix);
            self.derived.clear();
        }
        for guard in &solver.transaction_conditions[self.guards.marks.len()..] {
            self.guards.record(guard, prefix);
            self.derived.clear();
        }
    }

    // 左值尚待计算时把它放到显式栈顶。未知值也记忆，避免同一输入经共享定义反复展开。
    fn value<B: BV>(&mut self, sym: Sym, solver: &Solver<B>, prefix: &PathConditions<'_, B>) -> Option<Exp<Sym>> {
        let mut pending = vec![sym];
        while let Some(&next) = pending.last() {
            if !self.derived.contains_key(&next) {
                let facts = self.guards.constants.get(&next).or_else(|| self.ordinary.constants.get(&next));
                let answer = if let Some(value) = facts {
                    Some(value.clone())
                } else if let Some(def) = prefix.definition(next) {
                    match self.evaluate(def, solver) {
                        Ok(value) => Some(value),
                        Err(Some(input)) => {
                            pending.push(input);
                            continue;
                        }
                        Err(None) => None,
                    }
                } else {
                    None
                };
                self.derived.insert(next, answer);
            }
            pending.pop();
        }
        self.derived[&sym].clone()
    }

    fn evaluate<B: BV>(&self, exp: &Exp<Sym>, solver: &Solver<B>) -> Result<Exp<Sym>, Option<Sym>> {
        use Exp::*;
        let known = |s: &Sym| self.derived.get(s).ok_or(Some(*s))?.clone().ok_or(None);
        match exp {
            Bool(_) | Bits(_) | Bits64(_) | Enum(_) => Ok(exp.clone()),
            Var(sym) => known(sym),
            Ite(g, a, b) => match self.evaluate(g, solver)? {
                Bool(g) => self.evaluate(if g { a } else { b }, solver),
                _ => Err(None),
            },
            Eq(..) | Neq(..) | And(..) | Or(..) | Not(..) | Bvadd(..) | Bvsub(..) | Bvmul(..) | Bvshl(..)
            | Bvand(..) | Bvor(..) | Bvlshr(..) | Bvashr(..) | Bvxor(..) | Bvneg(..) | Bvnot(..) | SignExtend(..)
            | ZeroExtend(..) | Extract(..) | Concat(..) | Bvult(..) | Bvule(..) | Bvugt(..) | Bvuge(..) | Bvslt(..)
            | Bvsle(..) | Bvsgt(..) | Bvsge(..) => {
                let value = exp.map_var(&mut |s| known(s))?;
                let mut ast = solver.translate_exp(&value);
                ast.finite_bits().or_else(|| ast.structural_bool().map(Bool)).ok_or(None)
            }
            _ => Err(None),
        }
    }
}

pub(crate) enum OperandBounds {
    Established(RangeInclusive<i128>),
    RequireWithin(RangeInclusive<i128>),
}

pub(crate) struct ScalarChoice {
    pub(crate) values: Vec<Exp<Sym>>,
    pub(crate) bounded: bool,
    pub(crate) restricted: bool,
    pub(crate) pass_bound: bool,
    pub(crate) requires_checked_replay: bool,
}

impl<B: BV> Solver<'_, B> {
    /// 只移交导入后仍成立的定义级范围；带守卫的事实经已重命名的断言后缀进入接收端。
    pub(crate) fn export_scalar_layouts(&self, start: u32) -> Vec<(Sym, ScalarLayout)> {
        if !enabled() {
            return Vec::new();
        }
        PathConditions::new(self).map_or_else(Vec::new, |p| {
            p.index.layouts.iter().filter(|(sym, _)| sym.as_u32() >= start).map(|(&sym, &r)| (sym, r)).collect()
        })
    }

    pub(crate) fn import_scalar_layouts(&mut self, layouts: Vec<(Sym, ScalarLayout)>) {
        if layouts.is_empty() || PathConditions::new(self).is_none() {
            return;
        }
        let index = self.finite_prefix.as_mut().unwrap();
        for (sym, layout) in layouts {
            // 未导入的局部定义（例如已经撤销的片段）不得变成接收端事实。
            if index.has_binding(sym) {
                index.layouts.insert(sym, layout);
            }
        }
    }

    /// 某个 ITE 值臂可能直接来自带有限类型断言的输入。这些值只用来提出
    /// 待验证的完整域，不能据此排除另一个值臂或发布任何结果。
    fn declared_arm_values(&self, sym: Sym) -> Vec<Exp<Sym>> {
        #[derive(Clone, Copy, Hash, PartialEq, Eq)]
        enum Cast {
            Extract(u32, u32),
            Signed(u32),
            Unsigned(u32),
        }
        let Some(prefix) = PathConditions::new(self) else { return Vec::new() };
        let root = Exp::Var(sym);
        let mut pending = vec![(&root, false, Vec::new())];
        let mut seen = HashSet::new();
        let mut values = Vec::new();
        while let Some((exp, in_choice, mut casts)) = pending.pop() {
            match exp {
                Exp::Var(s) => {
                    if !seen.insert((*s, in_choice, casts.clone())) {
                        continue;
                    }
                    if let Some(def) = prefix.definition(*s) {
                        pending.push((def, in_choice, casts));
                    } else if in_choice && self.length(*s).is_some() {
                        for value in prefix.assertion_bound(exp, exp).unwrap_or_default() {
                            let mut ast = self.translate_exp(&value);
                            for cast in casts.iter().rev() {
                                ast = match *cast {
                                    Cast::Extract(hi, lo) => ast.extract(hi, lo),
                                    Cast::Signed(n) => ast.sign_extend(n),
                                    Cast::Unsigned(n) => ast.zero_extend(n),
                                };
                            }
                            let value = ast.finite_bits().expect("有限输入的位宽转换应得到常量");
                            if !values.contains(&value) {
                                values.push(value);
                            }
                        }
                    }
                }
                Exp::Ite(_, a, b) => {
                    pending.push((b, true, casts.clone()));
                    pending.push((a, true, casts));
                }
                Exp::Extract(hi, lo, x) => {
                    casts.push(Cast::Extract(*hi, *lo));
                    pending.push((x, in_choice, casts));
                }
                Exp::SignExtend(n, x) | Exp::ZeroExtend(n, x) => {
                    casts.push(if matches!(exp, Exp::SignExtend(..)) { Cast::Signed(*n) } else { Cast::Unsigned(*n) });
                    pending.push((x, in_choice, casts));
                }
                _ => (),
            }
        }
        values
    }

    pub(crate) fn resolve_scalar_choice(
        &mut self,
        sym: Sym,
        bounds: Option<OperandBounds>,
        consumer: bool,
        site: SourceLoc,
    ) -> Result<ScalarChoice, SmtError> {
        let missing = |candidates: Option<Vec<Exp<Sym>>>, width| SmtError::FiniteDomain {
            source_loc: site,
            symbol: sym,
            width,
            candidates: candidates.map(|v| {
                v.into_iter()
                    .map(|v| match v {
                        Exp::Bits64(b) => b.to_string(),
                        Exp::Bits(bits) => {
                            let mut text = Vec::new();
                            crate::simplify::write_bits(&mut text, &bits).unwrap();
                            String::from_utf8(text).unwrap()
                        }
                        _ => unreachable!("有限域只能包含位向量常量"),
                    })
                    .collect()
            }),
        };
        let width = self.length(sym).expect("具体化输入必须是位向量");
        let mut pass_bound = enabled() || self.operand_bound(sym, site).is_some();
        let persist = consumer && matches!(&bounds, Some(OperandBounds::RequireWithin(_)));
        let domain = self.resolve_scalar_in_scope(sym, site, persist);
        let bounded = matches!(domain, FiniteDomain::Bounded(_));
        let mut restricted = false;
        let mut requires_checked_replay = false;
        let values = match domain {
            FiniteDomain::Unknown => return Err(missing(None, width)),
            FiniteDomain::Known(values) => values,
            FiniteDomain::Bounded(mut values) => {
                let Some(bounds) = bounds else {
                    return Err(missing(Some(values), width));
                };
                let established = matches!(bounds, OperandBounds::Established(_));
                let range = match bounds {
                    OperandBounds::Established(r) | OperandBounds::RequireWithin(r) => r,
                };
                let fits = |v: &Exp<Sym>| signed(v).is_some_and(|v| range.contains(&v));
                let original = values.len();
                if established {
                    values.retain(fits);
                } else if !values.iter().all(fits) {
                    let can_defer = enabled()
                        && consumer
                        && !self.no_smt()
                        && self.region_queries_deferred()
                        && crate::config::RegionOptions::current().defer_range_proofs
                        && (1..=128).contains(&width)
                        && values.iter().any(fits);
                    let diagnostics = can_defer && crate::executor::stats::merge_diagnostics::enabled();
                    if diagnostics {
                        eprintln!(
                            "{}",
                            serde_json::json!({
                                "kind":"scalar_range_check", "location":site, "symbol":sym.as_u32(),
                                "candidates":original, "outside":values.iter().filter(|v| !fits(v)).count(),
                                "attempt":crate::executor::stats::merge_diagnostics::root_attempt(),
                            })
                        );
                    }
                    let input_values = if can_defer { self.declared_arm_values(sym) } else { Vec::new() };
                    let proposed: Vec<_> =
                        values.iter().filter(|v| fits(v) && input_values.contains(v)).cloned().collect();
                    let use_input = !proposed.is_empty() && values.iter().any(|v| fits(v) && !input_values.contains(v));
                    // 当前域已经过全栈推导。若能把剩余问题表为值臂有限集的补集，
                    // 直接在原前缀登记该反例，避免为同一义务再展开比较操作数的联合枚举。
                    if !use_input {
                        self.refine_guarded_values(sym, &mut values, fits, !can_defer);
                    }
                    pass_bound |= original != values.len();
                    if !values.iter().all(fits) {
                        if !can_defer || !values.iter().any(fits) {
                            return Err(missing(Some(values), width));
                        }
                        let allowed: Vec<_> = values.iter().filter(|v| fits(v)).cloned().collect();
                        // 在加入任何假设前冻结反例。若用值臂提出了更小的候选集，
                        // 出口验证也必须排除合法范围内遗漏的候选，否则撤销整个推演。
                        let membership = use_input.then_some(proposed.as_slice());
                        if !self.defer_scalar_range(sym, &range, membership, site) {
                            return Err(missing(Some(values), width));
                        }
                        requires_checked_replay = !use_input && allowed.len() > 1;
                        values = if use_input { proposed } else { allowed };
                        if diagnostics {
                            eprintln!(
                                "{}",
                                serde_json::json!({
                                    "kind":"scalar_range_obligation", "location":site, "symbol":sym.as_u32(),
                                    "retained":values.len(), "input_domain_obligation":use_input, "requires_checked_replay":requires_checked_replay, "attempt":crate::executor::stats::merge_diagnostics::root_attempt(),
                                })
                            );
                        }
                    }
                }
                restricted = original != values.len();
                values
            }
        };
        Ok(ScalarChoice { values, bounded, restricted, pass_bound, requires_checked_replay })
    }

    pub(crate) fn defer_scalar_range(
        &mut self,
        sym: Sym,
        range: &RangeInclusive<i128>,
        membership: Option<&[Exp<Sym>]>,
        site: SourceLoc,
    ) -> bool {
        use Exp::*;
        let width = self.length(sym).expect("范围参数必须有位宽");
        if !(1..=128).contains(&width) || !self.region_queries_deferred() {
            return false;
        }
        let max = i128::MAX >> (128 - width);
        let lo = (*range.start()).max(!max);
        let hi = (*range.end()).min(max);
        if lo > hi {
            return false;
        }
        let bits = |n: i128| {
            if width <= 64 {
                bits64(n as u64, width)
            } else {
                Bits((0..width).map(|i| (n >> i) & 1 == 1).collect())
            }
        };
        let condition = And(
            Box::new(Bvsle(Box::new(bits(lo)), Box::new(Var(sym)))),
            Box::new(Bvsle(Box::new(Var(sym)), Box::new(bits(hi)))),
        );
        let condition = if let Some(values) = membership {
            // 平衡析取树对任意大小的显式类型域都适用。
            fn member(sym: Sym, values: &[Exp<Sym>]) -> Exp<Sym> {
                if let [value] = values {
                    return Eq(Box::new(Var(sym)), Box::new(value.clone()));
                }
                let (first, second) = values.split_at(values.len() / 2);
                Or(Box::new(member(sym, first)), Box::new(member(sym, second)))
            }
            assert!(!values.is_empty());
            And(Box::new(condition), Box::new(member(sym, values)))
        } else {
            condition
        };
        if let Some(directory) = &crate::config::RegionOptions::current().obligation_dump_dir {
            // 必须在登记义务前捕获原始前缀，否则范围假设会排除自己的反例。
            static NEXT_DUMP: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
            let ordinal = NEXT_DUMP.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let attempt = crate::executor::stats::merge_diagnostics::root_attempt().unwrap_or(0);
            let pid = std::process::id();
            let path = directory.join(format!("scalar-range-{pid}-{attempt}-{}-{ordinal}.smt2", sym.as_u32()));
            let goal = SmtDumpRequest::CheckSatWith(Not(Box::new(condition.clone())));
            let replay = timeout_dump_from_checkpoint(self.checkpoint_snapshot(), goal);
            let text = replay.materialize().expect("生成标量范围反例回放失败");
            std::fs::create_dir_all(directory).expect("创建义务目录失败");
            let temporary = path.with_extension("tmp");
            std::fs::write(&temporary, text.as_bytes()).expect("写出标量范围反例失败");
            std::fs::rename(temporary, path).expect("发布标量范围反例失败");
        }
        self.defer_safety_check(
            &condition,
            crate::config::RegionOptions::current().defer_range_proofs,
            "range_obligation",
            site,
        )
    }

    pub(crate) fn scalar_fits_i64(&self, sym: Sym) -> bool {
        if enabled() {
            if PathConditions::new(self)
                .and_then(|p| p.index.layouts.get(&sym).copied())
                .is_some_and(|r| r.signed_bits <= 64)
            {
                return true;
            }
            self.structural_fits_i64(sym)
        } else {
            self.is_widened_i64(sym)
        }
    }

    pub(crate) fn scalar_domain_within_i64(&self, sym: Sym, site: SourceLoc) -> bool {
        match self.resolve_scalar(sym, site) {
            FiniteDomain::Known(values) => values.iter().all(|v| signed(v).is_some_and(|v| i64::try_from(v).is_ok())),
            FiniteDomain::Bounded(values) if enabled() => {
                values.iter().all(|v| signed(v).is_some_and(|v| i64::try_from(v).is_ok()))
            }
            _ => false,
        }
    }

    pub(crate) fn resolve_scalar(&self, sym: Sym, site: SourceLoc) -> FiniteDomain {
        self.resolve_scalar_in_scope(sym, site, false)
    }

    pub(crate) fn resolve_scalar_in_scope(&self, sym: Sym, site: SourceLoc, persist: bool) -> FiniteDomain {
        if !enabled() {
            return self.operand_bound(sym, site).unwrap_or_else(|| self.finite_domain(sym));
        }
        let Some(prefix) = PathConditions::new(self) else { return FiniteDomain::Unknown };
        let mut facts = prefix.index.arm_facts.borrow_mut();
        facts.update(self, &prefix);
        let value = facts.value(sym, self, &prefix).and_then(|v| constant(&v));
        if let Some(v) = value {
            // 结构常量只证明取值，前缀可行性仍由调用方按执行模式认证。
            return FiniteDomain::Bounded(vec![v]);
        }
        let range = {
            let mut min = i128::MIN;
            let mut max = i128::MAX;
            for range in [facts.ordinary.ranges.get(&sym), facts.guards.ranges.get(&sym)].into_iter().flatten() {
                min = min.max(*range.start());
                max = max.min(*range.end());
            }
            min..=max
        };
        drop(facts);
        let inherited = self.operand_bound(sym, site);
        // 同条重试的子域由互补守卫保证穷尽；其它位置还需与当前前缀取交。
        let own = self
            .savepoints
            .last()
            .and_then(|arm| arm.operand_bound.as_ref())
            .is_some_and(|b| b.sym == sym && b.site == site);
        let domain = match inherited {
            Some(domain) if own => domain,
            Some(FiniteDomain::Bounded(mut values)) => match self.finite_domain(sym) {
                FiniteDomain::Known(mut exact) => {
                    exact.retain(|v| values.contains(v));
                    FiniteDomain::Known(exact)
                }
                FiniteDomain::Bounded(upper) => {
                    values.retain(|v| upper.contains(v));
                    FiniteDomain::Bounded(values)
                }
                FiniteDomain::Unknown => FiniteDomain::Bounded(values),
            },
            _ if persist
                && self.region_queries_deferred()
                && crate::config::RegionOptions::current().scalar_domain_persist =>
            {
                let key = (sym, self.has_stashed_model(), self.region_queries_deferred());
                let current = prefix.index.domains.borrow().get(&key).cloned();
                if let Some(domain) = current {
                    domain
                } else if let Some(values) = prefix.scalar_upper(self, sym) {
                    FiniteDomain::Bounded(values)
                } else {
                    let domain = self.finite_domain(sym);
                    if matches!(domain, FiniteDomain::Bounded(_)) {
                        if let Some(count) = self
                            .savepoints
                            .last()
                            .and_then(|savepoint| prefix.scalar_proof_prefix(sym, savepoint.events_len))
                        {
                            if let Some(values) = self.scalar_definition_upper(&prefix, sym, count) {
                                prefix.remember_scalar_upper(sym, count, values);
                            }
                        }
                    }
                    domain
                }
            }
            _ => self.finite_domain(sym),
        };
        match domain {
            FiniteDomain::Bounded(mut values) => {
                values.retain(|v| signed(v).is_none_or(|v| range.contains(&v)));
                FiniteDomain::Bounded(values)
            }
            other => other,
        }
    }
}

// 第二项是有符号表示所需位数的上界。每个定义只合并直接操作数的摘要。
#[derive(Clone, Copy)]
pub(crate) struct ScalarLayout {
    width: u32,
    signed_bits: u32,
}

impl ScalarLayout {
    pub(super) fn full(width: u32) -> Self {
        Self { width, signed_bits: width }
    }

    pub(super) fn definition(exp: &Exp<Sym>, known: &HashMap<Sym, Self>) -> Option<Self> {
        use Exp::*;
        let child = |e| Self::definition(e, known);
        match exp {
            Var(sym) => known.get(sym).copied(),
            Bits(_) | Bits64(_) => {
                let width = match exp {
                    Bits(bits) => u32::try_from(bits.len()).ok()?,
                    Bits64(bits) => bits.len(),
                    _ => unreachable!(),
                };
                let signed_bits =
                    signed(exp).map_or(width, |n| 129 - if n < 0 { n.leading_ones() } else { n.leading_zeros() });
                Some(Self { width, signed_bits })
            }
            SignExtend(n, x) | ZeroExtend(n, x) => {
                let x = child(x)?;
                let width = x.width.checked_add(*n)?;
                let signed_bits =
                    if matches!(exp, SignExtend(..)) { x.signed_bits } else { x.width.saturating_add(1).min(width) };
                Some(Self { width, signed_bits })
            }
            Extract(hi, lo, _) => Some(Self::full(hi - lo + 1)),
            Ite(_, a, b) | Bvmul(a, b) | Bvadd(a, b) | Bvsub(a, b) => {
                let a = child(a)?;
                let b = child(b)?;
                let max = a.signed_bits.max(b.signed_bits);
                let signed_bits = match exp {
                    Ite(..) => max,
                    Bvmul(..) => a.signed_bits.saturating_add(b.signed_bits),
                    _ => max.saturating_add(1),
                };
                Some(Self { width: a.width, signed_bits: signed_bits.min(a.width) })
            }
            _ => None,
        }
    }
}
