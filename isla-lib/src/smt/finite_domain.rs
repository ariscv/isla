//! 从当前路径提取位向量的有限值域。只化简表达式，不做 SMT 查询。
use super::*;

pub(crate) enum FiniteDomain {
    Known(Vec<Exp<Sym>>),
    /// 包含全部可行取值，个别候选还可能被残余约束排除。
    Bounded(Vec<Exp<Sym>>),
    Unknown,
}

type Bound = Option<Vec<Exp<Sym>>>;
type Definitions<'a> = HashMap<Sym, &'a Exp<Sym>>;

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

fn resolve<'a>(mut exp: &'a Exp<Sym>, definitions: &Definitions<'a>) -> &'a Exp<Sym> {
    while let Exp::Var(sym) = exp {
        let Some(definition) = definitions.get(sym) else { break };
        exp = definition;
    }
    exp
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

// 只识别能产生有限上界的布尔形式。排除项与其他谓词在代入候选后检查。
fn bound(exp: &Exp<Sym>, target: &Exp<Sym>, definitions: &Definitions<'_>, negated: bool) -> Bound {
    use Exp::*;
    let visit = |child, negated| bound(child, target, definitions, negated);
    let exp = resolve(exp, definitions);
    match exp {
        Eq(lhs, rhs) | Neq(lhs, rhs) if matches!(exp, Eq(..)) != negated => {
            let (lhs, rhs) = (resolve(lhs, definitions), resolve(rhs, definitions));
            let value = if lhs == target {
                rhs
            } else if rhs == target {
                lhs
            } else {
                return None;
            };
            constant(value).map(|value| vec![value])
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
fn value_bound(exp: &Exp<Sym>, definitions: &Definitions<'_>) -> Bound {
    let exp = resolve(exp, definitions);
    if let Exp::Ite(_, yes, no) = exp {
        union(value_bound(yes, definitions), value_bound(no, definitions))
    } else {
        constant(exp).map(|value| vec![value])
    }
}

struct PathConditions<'a> {
    definitions: Definitions<'a>,
    assertions: Vec<&'a Exp<Sym>>,
    bool_symbols: Vec<Sym>,
}

impl<'a> PathConditions<'a> {
    // 只从公式显式给出的有限集合取值。自由位向量的位宽不能作为枚举依据。
    fn bounds(&self, subject: &Exp<Sym>) -> Bound {
        let subject = resolve(subject, &self.definitions);
        let mut candidates = value_bound(subject, &self.definitions);
        for assertion in &self.assertions {
            candidates = intersect(candidates, bound(assertion, subject, &self.definitions, false));
        }
        candidates
    }

    fn comparison_subjects(&self, exp: &'a Exp<Sym>, subjects: &mut Vec<&'a Exp<Sym>>) {
        use Exp::*;
        match resolve(exp, &self.definitions) {
            Eq(lhs, rhs) | Neq(lhs, rhs) => {
                for (symbolic, concrete) in [(lhs, rhs), (rhs, lhs)] {
                    if constant(resolve(concrete, &self.definitions)).is_some()
                        && constant(resolve(symbolic, &self.definitions)).is_none()
                    {
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

impl<'ctx> Ast<'ctx> {
    fn substitute(&self, old: &Self, new: &Self) -> Self {
        unsafe {
            let z3_ast = Z3_substitute(self.ctx.z3_ctx, self.z3_ast, 1, &old.z3_ast, &new.z3_ast);
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

impl<B: BV> Solver<'_, B> {
    pub(crate) fn finite_domain_enabled(&self) -> bool {
        self.ctx.solver_options.finite_domain_enumeration
    }

    fn finite_domain_prefix(&self) -> Option<PathConditions<'_>> {
        if !self.finite_domain_enabled() {
            return None;
        }
        // 提交的带守卫断言已改写为蕴含，活动守卫单独加入。回滚不留下缓存。
        let mut symbols = HashSet::new();
        let mut conditions =
            PathConditions { definitions: HashMap::new(), bool_symbols: Vec::new(), assertions: Vec::new() };
        for event in self.transaction_events.iter().rev().chain(self.trace.events_rev()) {
            let defined = match event {
                Event::Smt(Def::DefineConst(sym, exp), ..) => {
                    conditions.definitions.insert(*sym, exp);
                    *sym
                }
                Event::Smt(Def::DeclareConst(sym, ty), ..) => {
                    if matches!(ty, Ty::Bool) {
                        conditions.bool_symbols.push(*sym);
                    }
                    *sym
                }
                Event::Smt(Def::DeclareFun(sym, ..), ..) => *sym,
                Event::Smt(Def::Assert(exp), ..) => {
                    conditions.assertions.push(exp);
                    continue;
                }
                _ => continue,
            };
            // 已发布断言保留发布时的绑定，不能用重绑后的符号表解释。
            if !symbols.insert(defined) {
                return None;
            }
        }
        conditions.assertions.extend(&self.transaction_conditions);
        Some(conditions)
    }

    /// 条件在所有剩余候选中同值时才折叠。只证明蕴含，完整前缀仍由原入口认证。
    pub(crate) fn finite_domain_bool(&self, exp: &Exp<Sym>) -> Option<bool> {
        let prefix = self.finite_domain_prefix()?;
        let mut subjects = Vec::new();
        prefix.comparison_subjects(exp, &mut subjects);
        let predicate = self.translate_exp(exp);
        for subject in subjects {
            let Some(candidates) = prefix.bounds(subject) else { continue };
            let anchor = self.translate_exp(subject);
            let mut result = None;
            let mut undecided = false;
            for candidate in candidates {
                let value = self.translate_exp(&candidate);
                if prefix.assertions.iter().any(|fact| {
                    let original = self.translate_exp(fact);
                    let mut narrowed = original.substitute(&anchor, &value);
                    narrowed.z3_ast != original.z3_ast && narrowed.structural_bool() == Some(false)
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

    pub(crate) fn note_finite_domain_use(&self, category: &'static str, info: SourceLoc) {
        if self.no_smt() && crate::config::RegionOptions::current().progress {
            no_smt::record(category, info);
        }
    }

    pub(crate) fn finite_domain(&self, sym: Sym) -> FiniteDomain {
        let Some(prefix) = self.finite_domain_prefix() else { return FiniteDomain::Unknown };
        let mut pending = vec![sym];
        let mut seen = HashSet::new();
        let mut best = FiniteDomain::Unknown;
        while let Some(subject) = pending.pop() {
            if !seen.insert(subject) {
                continue;
            }
            let source = Exp::Var(subject);
            if let Some(definition) = prefix.definitions.get(&subject) {
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
        best
    }

    /// 原生化简可能把锚点改写到不再是目标的子表达式。沿原定义逐层代入已知值。
    fn project_finite_definition(
        &self,
        sym: Sym,
        definitions: &Definitions<'_>,
        projected: &mut HashMap<Sym, Option<Exp<Sym>>>,
    ) -> Option<Exp<Sym>> {
        if let Some(value) = projected.get(&sym) {
            return value.clone();
        }
        let value = definitions.get(&sym).and_then(|definition| {
            let mut changed = false;
            let expression = definition
                .map_var(&mut |input| {
                    Ok::<_, std::convert::Infallible>(
                        match self.project_finite_definition(*input, definitions, projected) {
                            Some(value) => {
                                changed = true;
                                value
                            }
                            None => Exp::Var(*input),
                        },
                    )
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

    fn project_finite_values(
        &self,
        prefix: &PathConditions<'_>,
        target: Sym,
        source: Sym,
        candidates: Vec<Exp<Sym>>,
    ) -> FiniteDomain {
        // 对派生锚点代入时保留原等式，防止把它错误地当成独立自由变量。
        let source_var = Exp::Var(source);
        let free = matches!(resolve(&source_var, &prefix.definitions), Exp::Var(_));
        let anchor = self.translate_exp(&source_var);
        let target_ast = self.translate_exp(&Exp::Var(target));
        let assertions: Vec<_> = prefix.assertions.iter().map(|exp| self.translate_exp(exp)).collect();
        let mut bool_atoms = Vec::new();
        let mut bool_literals = HashMap::new();
        for sym in &prefix.bool_symbols {
            let atom = &self.decls[sym];
            let negative = Ast::mk_not(atom);
            bool_literals.insert(atom.z3_ast, (*sym, true));
            bool_literals.insert(negative.z3_ast, (*sym, false));
            bool_atoms.push(negative);
        }
        let mut admissible = Vec::new();
        let mut exact = true;
        'candidate: for candidate in candidates {
            let value = self.translate_exp(&candidate);
            let binding = (!free).then(|| Ast::mk_eq(&anchor, &value));
            let mut literals = HashMap::new();
            let mut satisfiable_by_literals = true;
            let mut can_reuse_witness = self.has_stashed_model();
            for (index, original) in assertions.iter().chain(&binding).enumerate() {
                let is_path_fact = index < assertions.len();
                let mut residual = if is_path_fact { original.substitute(&anchor, &value) } else { original.clone() };
                let unchanged = residual.z3_ast == original.z3_ast && is_path_fact;
                match residual.structural_bool() {
                    Some(false) => continue 'candidate,
                    Some(true) => (),
                    None => {
                        can_reuse_witness &= unchanged;
                        if let Some(&(literal, positive)) = bool_literals.get(&residual.z3_ast) {
                            if literals.insert(literal, positive).is_some_and(|previous| previous != positive) {
                                continue 'candidate;
                            }
                        } else {
                            satisfiable_by_literals = false;
                        }
                    }
                }
            }
            let value = match target_ast.substitute(&anchor, &value).finite_bits() {
                Some(value) => value,
                None if !free => {
                    let mut projected = HashMap::from([(source, Some(candidate))]);
                    let Some(value) = self.project_finite_definition(target, &prefix.definitions, &mut projected)
                    else {
                        return FiniteDomain::Unknown;
                    };
                    // 重试的排除式可能引用遭化简的目标。先在原表达式中代入，再判是否必假。
                    for assertion in &prefix.assertions {
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
            exact &= satisfiable_by_literals || can_reuse_witness;
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
