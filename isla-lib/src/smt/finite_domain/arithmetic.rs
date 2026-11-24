//! 对原始定义建立共享表达式图。沿一组输入赋值遍历，只展开当前 ITE 值臂。
use super::*;
use std::rc::Rc;

type Formula = Exp<Sym>;

#[cfg(test)]
thread_local! {
    pub(super) static COMBINED_VALUES_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
#[derive(Default)]
struct Evaluated<'ctx> {
    values: HashMap<*const Expression, Ast<'ctx>>,
    fixed: Vec<Rc<FixedChoice>>,
}
type Node = Rc<Expression>;

enum Expression {
    Constant(ChoiceAst),
    Input(usize),
    Select(Node, Node, Node),
    FixedSelect(Rc<FixedChoice>, Node),
    Unary(Unary, Node),
    Binary(Binary, Node, Node),
}

enum Unary {
    ZeroExtend(u32),
    SignExtend(u32),
    Extract(u32, u32),
    Not,
    Bvneg,
}

enum Binary {
    Bvadd,
    Bvsub,
    Bvmul,
    Bvshl,
    Eq,
    Neq,
    Bvult,
    Bvule,
    Bvugt,
    Bvuge,
    Bvslt,
    Bvsle,
    Bvsgt,
    Bvsge,
    And,
    Or,
}

struct FixedChoice {
    sym: Sym,
    truth: bool,
    anchor: ChoiceAst,
}

struct Input {
    symbol: Option<Sym>,
    guard_symbol: Option<Sym>,
    anchor: ChoiceAst,
    choices: Vec<Formula>,
    free: bool,
}

#[derive(Default)]
struct ChoiceGraph {
    symbols: HashMap<Sym, Option<Node>>,
    guards: HashMap<Z3_ast, usize>,
    bounds: HashMap<Sym, Bound>,
    inputs: Vec<Input>,
    // 每个节点的去重结果只在完整遍历后发布。中途停止则保留可复用的图。
    outputs: Vec<(Formula, bool, Vec<(ChoiceAst, bool)>)>,
}

// 选择图只在当前 Solver 内共享。原生引用由节点持有，借用时验证所属 Context。
struct ChoiceAst {
    context: Z3_context,
    z3_ast: Z3_ast,
}

impl ChoiceAst {
    fn keep(ast: Ast<'_>) -> Self {
        let value = Self { context: ast.ctx.z3_ctx, z3_ast: ast.z3_ast };
        std::mem::forget(ast);
        value
    }

    fn get<'ctx>(&self, ctx: &'ctx Context) -> Ast<'ctx> {
        assert_eq!(self.context, ctx.z3_ctx);
        unsafe { Z3_inc_ref(self.context, self.z3_ast) };
        Ast { ctx, z3_ast: self.z3_ast }
    }
}

impl Drop for ChoiceAst {
    fn drop(&mut self) {
        unsafe { Z3_dec_ref(self.context, self.z3_ast) };
    }
}

/// 到达时的保守候选上界，以当前臂和全部祖先条件为生效前提。
#[derive(Clone)]
pub(crate) struct ArrivalFactSummary {
    guards: Vec<Formula>,
    slots: HashMap<Sym, Vec<Formula>>,
}

impl ArrivalFactSummary {
    pub(crate) fn remap_symbols(&mut self, remap: &SymRemap) {
        self.guards = self.guards.iter().map(|guard| remap.exp(guard)).collect();
        self.slots = self.slots.drain().map(|(sym, values)| (remap.get(sym), values)).collect();
    }
}

#[derive(Clone)]
pub(super) struct JoinedChoices {
    pub(super) ancestors: Vec<Formula>,
    pub(super) operands: [Option<Arc<Vec<Formula>>>; 2],
}

type ChoiceRevision = (u64, u64);

pub(in crate::smt) struct IncrementalChoiceDag<'ctx> {
    context: &'ctx Context,
    scopes: RefCell<Vec<(u64, Option<ChoiceRevision>, ChoiceGraph)>>,
}

impl<'ctx> IncrementalChoiceDag<'ctx> {
    pub(in crate::smt) fn new(context: &'ctx Context) -> Self {
        Self { context, scopes: RefCell::default() }
    }

    pub(super) fn clear(&mut self) {
        self.scopes.get_mut().clear();
    }

    fn current<'a>(
        scopes: &'a mut Vec<(u64, Option<ChoiceRevision>, ChoiceGraph)>,
        guards: &[u64],
        revision: ChoiceRevision,
    ) -> &'a mut ChoiceGraph {
        let ids = std::iter::once(0).chain(guards.iter().copied());
        let shared = ids.clone().zip(scopes.iter()).take_while(|(id, scope)| *id == scope.0).count();
        scopes.truncate(shared);
        scopes.extend(ids.skip(shared).map(|id| (id, None, ChoiceGraph::default())));
        let (_, cached, graph) = scopes.last_mut().unwrap();
        if *cached != Some(revision) {
            *graph = ChoiceGraph::default();
            *cached = Some(revision);
        }
        graph
    }
}

struct Graph<'a, 'prefix, 'ctx, B> {
    solver: &'a Solver<'ctx, B>,
    prefix: &'a PathConditions<'prefix, B>,
    state: &'a mut ChoiceGraph,
    incremental: bool,
    // 上界证明只读取定义前的普通断言，不借用活动臂事实。
    scalar_proof_assertions: Option<usize>,
}

impl<'a, 'ctx, B: BV> Graph<'a, '_, 'ctx, B> {
    fn build_join_arm(&mut self, output: Option<Sym>, exp: &Formula, side: usize) -> Option<Node> {
        if let (None, Some(output), Exp::Var(symbol)) = (self.scalar_proof_assertions, output, exp) {
            if let Some(joined) = self.prefix.index.joined_choices.get(&output) {
                if let Some(values) = &joined.operands[side] {
                    if joined.ancestors.iter().all(|guard| self.prefix.known_choice(self.solver, guard) == Some(true)) {
                        let index = self.state.inputs.len();
                        self.state.inputs.push(Input {
                            // 这是对该次 ITE 值臂的限制，不能无条件改写其它使用点。
                            symbol: Some(*symbol),
                            guard_symbol: None,
                            anchor: ChoiceAst::keep(self.solver.translate_exp(exp)),
                            choices: values.as_ref().clone(),
                            free: false,
                        });
                        return Some(Rc::new(Expression::Input(index)));
                    }
                }
            }
        }
        self.build(exp)
    }

    fn build(&mut self, exp: &Formula) -> Option<Node> {
        self.build_definition(exp, None)
    }

    fn build_definition(&mut self, exp: &Formula, output: Option<Sym>) -> Option<Node> {
        use Exp::*;
        if let Var(sym) = exp {
            if let Some(cached) = self.state.symbols.get(sym) {
                return cached.clone();
            }
            let definition = self.prefix.definition(*sym);
            let node = definition.and_then(|exp| self.build_definition(exp, Some(*sym))).or_else(|| {
                let choices = if let Some(count) = self.scalar_proof_assertions {
                    let subject = resolve(exp, self.prefix);
                    let mut memo = HashMap::new();
                    self.prefix.ordinary_suffix(0).take(count).fold(
                        value_bound(subject, self.prefix),
                        |previous, assertion| {
                            intersect(previous, bound(assertion, subject, self.prefix, false, &mut memo))
                        },
                    )
                } else if self.incremental {
                    self.state.bounds.entry(*sym).or_insert_with(|| self.prefix.bounds(exp)).clone()
                } else {
                    self.prefix.bounds(exp)
                }?;
                let index = self.state.inputs.len();
                self.state.inputs.push(Input {
                    symbol: Some(*sym),
                    guard_symbol: None,
                    anchor: ChoiceAst::keep(self.solver.translate_exp(exp)),
                    choices,
                    free: matches!(resolve(exp, self.prefix), Var(_)),
                });
                Some(Rc::new(Expression::Input(index)))
            });
            self.state.symbols.insert(*sym, node.clone());
            return node;
        }
        let node = match exp {
            Bits(_) | Bits64(_) | Bool(_) | Enum(_) => {
                Expression::Constant(ChoiceAst::keep(self.solver.translate_exp(exp)))
            }
            Ite(guard, yes, no) => {
                if let Var(sym) = **guard {
                    // 自由布尔选择已有当前臂事实时，保留认证所需字面量，不再枚举守卫。
                    if self.incremental && self.prefix.definition(sym).is_none() {
                        if let Some(truth) = self.prefix.known_choice(self.solver, guard) {
                            let selected =
                                self.build_join_arm(output, if truth { yes } else { no }, usize::from(!truth))?;
                            let anchor = ChoiceAst::keep(self.solver.translate_exp(guard));
                            let fixed = Rc::new(FixedChoice { sym, truth, anchor });
                            return Some(Rc::new(Expression::FixedSelect(fixed, selected)));
                        }
                    }
                }
                let yes = self.build_join_arm(output, yes, 0)?;
                let no = self.build_join_arm(output, no, 1)?;
                let guard = self.build(guard).unwrap_or_else(|| {
                    let mut anchor = self.solver.translate_exp(guard);
                    if let Some(value) = anchor.structural_bool() {
                        return Rc::new(Expression::Constant(ChoiceAst::keep(Ast::mk_bool(self.solver.ctx, value))));
                    }
                    let index = *self.state.guards.entry(anchor.z3_ast).or_insert_with(|| {
                        let free =
                            self.prefix.bool_symbols().any(|sym| self.solver.decls[&sym].ast().z3_ast == anchor.z3_ast);
                        let index = self.state.inputs.len();
                        let guard_symbol = if let Var(sym) = guard.as_ref() { Some(*sym) } else { None };
                        self.state.inputs.push(Input {
                            symbol: None,
                            guard_symbol,
                            anchor: ChoiceAst::keep(anchor),
                            choices: vec![Bool(true), Bool(false)],
                            free,
                        });
                        index
                    });
                    Rc::new(Expression::Input(index))
                });
                Expression::Select(guard, yes, no)
            }
            Bvadd(lhs, rhs) => Expression::Binary(Binary::Bvadd, self.build(lhs)?, self.build(rhs)?),
            Bvsub(lhs, rhs) => Expression::Binary(Binary::Bvsub, self.build(lhs)?, self.build(rhs)?),
            Bvmul(lhs, rhs) => Expression::Binary(Binary::Bvmul, self.build(lhs)?, self.build(rhs)?),
            Bvshl(lhs, rhs) => Expression::Binary(Binary::Bvshl, self.build(lhs)?, self.build(rhs)?),
            Eq(lhs, rhs) => Expression::Binary(Binary::Eq, self.build(lhs)?, self.build(rhs)?),
            Neq(lhs, rhs) => Expression::Binary(Binary::Neq, self.build(lhs)?, self.build(rhs)?),
            Bvult(lhs, rhs) => Expression::Binary(Binary::Bvult, self.build(lhs)?, self.build(rhs)?),
            Bvule(lhs, rhs) => Expression::Binary(Binary::Bvule, self.build(lhs)?, self.build(rhs)?),
            Bvugt(lhs, rhs) => Expression::Binary(Binary::Bvugt, self.build(lhs)?, self.build(rhs)?),
            Bvuge(lhs, rhs) => Expression::Binary(Binary::Bvuge, self.build(lhs)?, self.build(rhs)?),
            Bvslt(lhs, rhs) => Expression::Binary(Binary::Bvslt, self.build(lhs)?, self.build(rhs)?),
            Bvsle(lhs, rhs) => Expression::Binary(Binary::Bvsle, self.build(lhs)?, self.build(rhs)?),
            Bvsgt(lhs, rhs) => Expression::Binary(Binary::Bvsgt, self.build(lhs)?, self.build(rhs)?),
            Bvsge(lhs, rhs) => Expression::Binary(Binary::Bvsge, self.build(lhs)?, self.build(rhs)?),
            And(lhs, rhs) => Expression::Binary(Binary::And, self.build(lhs)?, self.build(rhs)?),
            Or(lhs, rhs) => Expression::Binary(Binary::Or, self.build(lhs)?, self.build(rhs)?),
            ZeroExtend(width, value) => Expression::Unary(Unary::ZeroExtend(*width), self.build(value)?),
            SignExtend(width, value) => Expression::Unary(Unary::SignExtend(*width), self.build(value)?),
            Extract(hi, lo, value) => Expression::Unary(Unary::Extract(*hi, *lo), self.build(value)?),
            Not(value) => Expression::Unary(Unary::Not, self.build(value)?),
            Bvneg(value) => Expression::Unary(Unary::Bvneg, self.build(value)?),
            _ => return None,
        };
        Some(Rc::new(node))
    }

    // 两种投影共用同一棵按需展开的选择树。返回 false 表示调用方已提前结束遍历。
    fn visit(
        &self,
        root: &Expression,
        compared: Option<&Expression>,
        mut accept: impl FnMut(Ast<'ctx>, &[(usize, usize)], &[Option<Ast<'ctx>>], &Evaluated<'ctx>) -> bool,
    ) -> bool {
        let mut assignments = vec![None; self.state.inputs.len()];
        let mut stack: Vec<(usize, usize)> = Vec::new();
        loop {
            let mut evaluated = Evaluated::default();
            let result = root.evaluate(self.solver.ctx, &assignments, &mut evaluated).and_then(|value| {
                if let Some(compared) = compared {
                    compared.evaluate(self.solver.ctx, &assignments, &mut evaluated)?;
                }
                Ok(value)
            });
            match result {
                Err(index) => stack.push((index, 0)),
                Ok(value) => {
                    if !accept(value, &stack, &assignments, &evaluated) {
                        return false;
                    }
                }
            }
            while let Some((index, next)) = stack.last_mut() {
                if let Some(choice) = self.state.inputs[*index].choices.get(*next) {
                    assignments[*index] = Some(self.solver.translate_exp(choice));
                    *next += 1;
                    break;
                }
                assignments[*index] = None;
                stack.pop();
            }
            if stack.is_empty() {
                return true;
            }
        }
    }

    fn retain_guarded(
        &self,
        target: Sym,
        root: &Expression,
        compared: Option<(Sym, &Expression)>,
        values: &mut Vec<Formula>,
    ) {
        let mut possible = vec![false; values.len()];
        // 选择条件可以先由枚举值或算术表达式算出。保留本组合已求值的布尔符号，
        // 返回标签使用同一条件时可直接复用，无需从枚举构造子再次推导。
        let predicates: Vec<_> = self
            .state
            .symbols
            .iter()
            .filter_map(|(&sym, node)| {
                let node = node.as_ref()?;
                self.solver.is_bool(sym).then_some((sym, Rc::as_ptr(node)))
            })
            .collect();
        self.visit(root, compared.map(|(_, expr)| expr), |mut ast, stack, _, evaluated| {
            let value = ast.finite_bits().expect("长度候选必须为位向量常量");
            let Some(index) = values.iter().position(|v| v == &value) else {
                return true;
            };
            if possible[index] {
                return true;
            }
            let mut projected = HashMap::from([(target, Some(value))]);
            if let Some((sym, expr)) = compared {
                let mut ast = evaluated.values[&std::ptr::from_ref(expr)].clone();
                projected.insert(sym, Some(ast.finite_bits().expect("比较操作数必须为位向量常量")));
            }
            for &(input, next) in stack {
                let input = &self.state.inputs[input];
                if let Some(sym) = input.symbol.or(input.guard_symbol) {
                    projected.insert(sym, Some(input.choices[next - 1].clone()));
                }
            }
            for fixed in &evaluated.fixed {
                projected.insert(fixed.sym, Some(Exp::Bool(fixed.truth)));
            }
            for &(sym, node) in &predicates {
                if let Some(value) = evaluated.values.get(&node) {
                    let truth = value.clone().structural_bool().expect("已求值的布尔节点必须为常量");
                    projected.insert(sym, Some(Exp::Bool(truth)));
                }
            }
            possible[index] = !self.solver.transaction_conditions.iter().rev().any(|guard| {
                let reduced = guard
                    .map_var(&mut |sym| {
                        Ok::<_, std::convert::Infallible>(
                            self.solver
                                .project_finite_definition(*sym, self.prefix, &mut projected)
                                .unwrap_or(Exp::Var(*sym)),
                        )
                    })
                    .unwrap();
                self.solver.translate_exp(&reduced).structural_bool() == Some(false)
            });
            !possible.iter().all(|&v| v)
        });
        let mut possible = possible.into_iter();
        values.retain(|_| possible.next().unwrap());
    }
}

impl Expression {
    fn reachable_inputs(&self) -> (HashSet<usize>, Vec<Z3_ast>) {
        let mut inputs = HashSet::new();
        let mut fixed = Vec::new();
        let mut seen = HashSet::new();
        let mut pending = vec![self];
        while let Some(node) = pending.pop() {
            if !seen.insert(std::ptr::from_ref(node)) {
                continue;
            }
            match node {
                Self::Input(index) => {
                    inputs.insert(*index);
                }
                Self::Constant(_) => (),
                Self::Unary(_, value) => pending.push(value),
                Self::FixedSelect(fact, value) => {
                    fixed.push(fact.anchor.z3_ast);
                    pending.push(value);
                }
                Self::Binary(_, left, right) => pending.extend([left.as_ref(), right]),
                Self::Select(guard, yes, no) => pending.extend([guard.as_ref(), yes, no]),
            }
        }
        (inputs, fixed)
    }

    // 返回本次求值所需的下一个输入。多个操作数引用同一输入时复用其赋值。
    fn evaluate<'ctx>(
        &self,
        ctx: &'ctx Context,
        assignments: &[Option<Ast<'ctx>>],
        cache: &mut Evaluated<'ctx>,
    ) -> Result<Ast<'ctx>, usize> {
        if let Some(value) = cache.values.get(&(self as *const Self)) {
            return Ok(value.clone());
        }
        let value = match self {
            Self::Constant(value) => value.get(ctx),
            Self::Input(index) => assignments[*index].clone().ok_or(*index)?,
            Self::Select(guard, yes, no) => {
                let guard = guard.evaluate(ctx, assignments, cache)?.structural_bool().expect("有限域守卫必须为常量");
                (if guard { yes } else { no }).evaluate(ctx, assignments, cache)?
            }
            Self::FixedSelect(fixed, selected) => {
                cache.fixed.push(Rc::clone(fixed));
                selected.evaluate(ctx, assignments, cache)?
            }
            Self::Unary(op, value) => {
                let value = value.evaluate(ctx, assignments, cache)?;
                match op {
                    Unary::ZeroExtend(width) => value.zero_extend(*width),
                    Unary::SignExtend(width) => value.sign_extend(*width),
                    Unary::Extract(hi, lo) => value.extract(*hi, *lo),
                    Unary::Not => value.mk_not(),
                    Unary::Bvneg => value.mk_bvneg(),
                }
            }
            Self::Binary(op, lhs, rhs) => {
                let lhs = lhs.evaluate(ctx, assignments, cache)?;
                let rhs = rhs.evaluate(ctx, assignments, cache)?;
                match op {
                    Binary::Bvadd => lhs.mk_bvadd(&rhs),
                    Binary::Bvsub => lhs.mk_bvsub(&rhs),
                    Binary::Bvmul => lhs.mk_bvmul(&rhs),
                    Binary::Bvshl => lhs.mk_bvshl(&rhs),
                    Binary::Eq => lhs.mk_eq(&rhs),
                    Binary::Neq => lhs.mk_eq(&rhs).mk_not(),
                    Binary::Bvult => lhs.mk_bvult(&rhs),
                    Binary::Bvule => lhs.mk_bvule(&rhs),
                    Binary::Bvugt => lhs.mk_bvugt(&rhs),
                    Binary::Bvuge => lhs.mk_bvuge(&rhs),
                    Binary::Bvslt => lhs.mk_bvslt(&rhs),
                    Binary::Bvsle => lhs.mk_bvsle(&rhs),
                    Binary::Bvsgt => lhs.mk_bvsgt(&rhs),
                    Binary::Bvsge => lhs.mk_bvsge(&rhs),
                    Binary::And => lhs.mk_and(&rhs),
                    Binary::Or => lhs.mk_or(&rhs),
                }
            }
        };
        cache.values.insert(self, value.clone());
        Ok(value)
    }
}

// 每位代表一类输入。超过 128 个输入时碰撞只会多保留代入项。
pub(super) fn input_bit(index: usize) -> u128 {
    1 << (index % u128::BITS as usize)
}

fn source_uses_input<B: BV>(exp: &Formula, prefix: &PathConditions<'_, B>, memo: &mut HashMap<Sym, bool>) -> bool {
    let roots = exp.variables();
    let mut pending: Vec<_> = roots.iter().copied().map(|sym| (sym, false)).collect();
    while let Some((sym, expanded)) = pending.pop() {
        if memo.contains_key(&sym) {
            continue;
        }
        let Some(def) = prefix.definition(sym) else {
            memo.insert(sym, false);
            continue;
        };
        let children = def.variables();
        if expanded {
            memo.insert(sym, children.iter().any(|c| memo[c]));
        } else {
            pending.push((sym, true));
            pending.extend(children.into_iter().filter(|c| !memo.contains_key(c)).map(|c| (c, false)));
        }
    }
    roots.iter().any(|sym| memo[sym])
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    pub(crate) fn arrival_fact_summary(
        &self,
        symbols: impl IntoIterator<Item = Sym>,
    ) -> Option<Arc<ArrivalFactSummary>> {
        self.choice_dag.as_ref()?;
        self.transaction_conditions.last()?;
        let prefix = PathConditions::new(self)?;
        let domains = prefix.index.domains.borrow();
        let model = self.has_stashed_model();
        let deferred = self.region_queries_deferred();
        let slots: HashMap<_, _> = symbols
            .into_iter()
            .filter_map(|sym| {
                let (FiniteDomain::Known(values) | FiniteDomain::Bounded(values)) =
                    domains.get(&(sym, model, deferred))?
                else {
                    return None;
                };
                Some((sym, values.clone()))
            })
            .collect();
        (!slots.is_empty()).then(|| Arc::new(ArrivalFactSummary { guards: self.transaction_conditions.clone(), slots }))
    }

    /// 只在实际发布的 ITE 上接续到达事实。复杂分组中无法确认的选择关系继续按定义推导。
    pub(crate) fn install_arrival_choices(
        &mut self,
        start: u32,
        left: Option<&ArrivalFactSummary>,
        right: Option<&ArrivalFactSummary>,
    ) {
        if left.is_none() && right.is_none() {
            return;
        }
        let Some(prefix) = PathConditions::new(self) else { return };
        let mut updates = Vec::new();
        for raw in start..self.next_join_symbol() {
            let output = Sym::from_u32(raw);
            let Some(Exp::Ite(selector, first, second)) = prefix.definition(output) else {
                continue;
            };
            for (side, (summary, operand)) in [(left, first), (right, second)].into_iter().enumerate() {
                let (Some(summary), Exp::Var(symbol)) = (summary, operand.as_ref()) else {
                    continue;
                };
                let Some(values) = summary.slots.get(symbol) else { continue };
                let (arrival, ancestors) = summary.guards.split_last().unwrap();
                let selected =
                    if side == 0 { self.translate_exp(selector) } else { self.translate_exp(selector).mk_not() };
                if self.translate_exp(arrival).z3_ast == selected.z3_ast {
                    updates.push((output, side, ancestors.to_vec(), Arc::new(values.clone())));
                }
            }
        }
        let index = self.finite_prefix.as_mut().unwrap();
        for (output, side, ancestors, values) in updates {
            let choice = index
                .joined_choices
                .entry(output)
                .or_insert_with(|| JoinedChoices { ancestors: ancestors.clone(), operands: [None, None] });
            if choice.ancestors == ancestors {
                choice.operands[side] = Some(values);
            }
        }
    }

    fn with_choice_graph<T>(
        &self,
        prefix: &PathConditions<'_, B>,
        f: impl FnOnce(&mut Graph<'_, '_, 'ctx, B>) -> T,
    ) -> T {
        if let Some(dag) = &self.choice_dag {
            assert!(std::ptr::eq(dag.context, self.ctx));
            let mut scopes = dag.scopes.borrow_mut();
            let (guards, revision) = prefix.index.choice_revision();
            let state = IncrementalChoiceDag::current(&mut scopes, guards, revision);
            f(&mut Graph { solver: self, prefix, state, incremental: true, scalar_proof_assertions: None })
        } else {
            let mut state = ChoiceGraph::default();
            f(&mut Graph { solver: self, prefix, state: &mut state, incremental: false, scalar_proof_assertions: None })
        }
    }

    pub(super) fn scalar_definition_upper(&self, prefix: &PathConditions<'_, B>, sym: Sym, count: usize) -> Bound {
        let mut state = ChoiceGraph::default();
        let mut graph =
            Graph { solver: self, prefix, state: &mut state, incremental: false, scalar_proof_assertions: Some(count) };
        let root = graph.build(&Exp::Var(sym))?;
        let mut seen = HashMap::new();
        let mut output = Vec::new();
        // 上界缓存只做有限的预计算。达到缓存预算时，继续用原入口完整推导。
        let mut remaining = 512;
        let complete = graph.visit(&root, None, |mut value, _, _, _| {
            let constant = value.finite_bits().expect("标量上界必须为位向量常量");
            if seen.insert(value.z3_ast, value).is_none() {
                output.push(constant);
            }
            remaining -= 1;
            remaining > 0
        });
        complete.then_some(output)
    }

    pub(super) fn choice_bounds(&self, prefix: &PathConditions<'_, B>, subject: &Formula) -> Bound {
        let (Some(dag), Exp::Var(sym)) = (&self.choice_dag, subject) else {
            return prefix.bounds(subject);
        };
        let mut scopes = dag.scopes.borrow_mut();
        let (guards, revision) = prefix.index.choice_revision();
        let state = IncrementalChoiceDag::current(&mut scopes, guards, revision);
        state.bounds.entry(*sym).or_insert_with(|| prefix.bounds(subject)).clone()
    }

    /// 按产生目标值的输入重算活动守卫。只要一组赋值尚未被排除，就保留该值。
    pub(crate) fn refine_guarded_values(
        &self,
        target: Sym,
        values: &mut Vec<Formula>,
        in_bounds: impl Fn(&Formula) -> bool,
        expand_outer_operands: bool,
    ) {
        let Some(last_guard) = self.transaction_conditions.last() else { return };
        let Some(prefix) = PathConditions::new(self) else {
            return;
        };
        self.with_choice_graph(&prefix, |graph| {
            let exp = Exp::Var(target);
            let Some(root) = graph.build(&exp) else {
                return;
            };
            graph.retain_guarded(target, &root, None, values);
            if values.iter().all(&in_bounds) {
                return;
            }
            // 最近的选择守卫可能比较另一个有限操作数。两者共用输入赋值，
            // 逐个补算比较操作数，避免把多个独立守卫展开为笛卡尔积。
            let mut subjects = Vec::new();
            // retain_guarded 已检查全部活动守卫。若剩余越界值可交给出口证明，
            // 保留原重试臂的比较剪枝，避免为外层其它操作数展开第二组联合枚举。
            if expand_outer_operands && super::scalar::enabled() {
                for guard in self.transaction_conditions.iter().rev() {
                    prefix.comparison_subjects(guard, &mut subjects);
                }
            } else {
                prefix.comparison_subjects(last_guard, &mut subjects);
            }
            let mut visited = HashSet::new();
            for subject in subjects {
                let Exp::Var(sym) = subject else { continue };
                if *sym == target || !visited.insert(*sym) {
                    continue;
                }
                let Some(node) = graph.build(subject) else { continue };
                graph.retain_guarded(target, &root, Some((*sym, &node)), values);
                if values.iter().all(&in_bounds) {
                    break;
                }
            }
        });
    }

    pub(super) fn combined_values(
        &self,
        prefix: &PathConditions<'_, B>,
        exp: &Formula,
        mut accept: impl FnMut(Ast<'ctx>, bool) -> bool,
    ) -> Option<()> {
        #[cfg(test)]
        COMBINED_VALUES_CALLS.set(COMBINED_VALUES_CALLS.get() + 1);
        self.with_choice_graph(prefix, |graph| {
            let witness = self.has_stashed_model();
            if graph.incremental {
                if let Some((_, _, values)) =
                    graph.state.outputs.iter().find(|(key, certified, _)| key == exp && *certified == witness)
                {
                    values.iter().all(|(value, exact)| accept(value.get(self.ctx), *exact));
                    return Some(());
                }
            }
            let root = graph.build(exp)?;
            let (reachable, fixed) = root.reachable_inputs();
            if reachable.is_empty() && fixed.is_empty() && (graph.incremental || graph.state.inputs.is_empty()) {
                return None;
            }
            let mut outputs = Vec::new();
            let stage1 = super::scalar::enabled() || graph.incremental;
            let facts: Vec<_> = if stage1 {
                let mut cache = prefix.index.projection.borrow_mut();
                prefix.translate_projection_suffix(self, &mut cache);
                prefix
                    .assertions()
                    .zip(cache.assertions.iter().rev().chain(&cache.guards))
                    .map(|(exp, key)| (exp, prefix.index.asts.get(*key)))
                    .collect()
            } else {
                prefix.assertions().map(|exp| (exp, self.translate_exp(exp))).collect()
            };
            // 固定守卫同样要进入断言的依赖掩码，但在枚举栈中没有候选位置。
            let fixed_base = graph.state.inputs.len();
            let fixed_indices: HashMap<_, _> =
                fixed.into_iter().enumerate().map(|(i, a)| (a, fixed_base + i)).collect();
            let mut dependencies = rewrites::InputDependencies::new(
                reachable
                    .iter()
                    .map(|&i| (i, graph.state.inputs[i].anchor.z3_ast))
                    .chain(fixed_indices.iter().map(|(&anchor, &i)| (i, anchor))),
            );
            // 原始定义也可能含有被 Z3 化简消去的锚点，须同时检查两个表达式图。
            let mut source_dependencies = HashMap::new();
            for &index in &reachable {
                if let Some(sym) = graph.state.inputs[index].symbol {
                    source_dependencies.insert(sym, true);
                }
            }
            let mut relevant_facts = Vec::new();
            for (index, (exp, ast)) in facts.iter().enumerate() {
                let mask = dependencies.mask(ast.z3_ast, ast.ctx.z3_ctx);
                let is_guard = index >= prefix.ordinary_assertion_count();
                let depends = !stage1 || mask != 0 || source_uses_input(exp, prefix, &mut source_dependencies);
                if !depends {
                    match prefix.index.rewrites.for_assertion(is_guard).simplified(ast.clone()).0 {
                        Some(true) => continue,
                        Some(false) => return Some(()),
                        None => (),
                    }
                }
                relevant_facts.push((*exp, ast, mask, depends, is_guard));
            }
            let mut negative_atoms = Vec::new();
            let mut literals = HashMap::new();
            for sym in prefix.bool_symbols() {
                let atom = self.decls[&sym].ast();
                let negative = atom.mk_not();
                literals.insert(atom.z3_ast, (sym, true));
                literals.insert(negative.z3_ast, (sym, false));
                negative_atoms.push(negative);
            }
            let completed = graph.visit(&root, None, |value, stack, assignments, evaluated| {
                let mut projected = HashMap::new();
                let mut anchors = Vec::new();
                let mut values = Vec::new();
                let mut free_replacements = Vec::new();
                let mut bindings = Vec::new();
                for &(index, next) in stack {
                    let input = &graph.state.inputs[index];
                    let assigned = assignments[index].as_ref().expect("活跃的有限域分支必须已有赋值");
                    if let Some(sym) = input.symbol {
                        projected.insert(sym, Some(input.choices[next - 1].clone()));
                    }
                    if let Some(previous) = anchors.iter().position(|&a| a == input.anchor.z3_ast) {
                        if graph.incremental && values[previous] != assigned.z3_ast {
                            return true;
                        }
                    }
                    anchors.push(input.anchor.z3_ast);
                    values.push(assigned.z3_ast);
                    if input.free {
                        free_replacements.push((input.anchor.z3_ast, assigned.z3_ast));
                    } else {
                        bindings.push(input.anchor.get(self.ctx).mk_eq(assigned));
                    }
                }
                let mut indices: Vec<_> = stack.iter().map(|&(index, _)| index).collect();
                let mut fixed_values = Vec::new();
                for fixed in &evaluated.fixed {
                    let anchor = fixed.anchor.z3_ast;
                    let assigned = Ast::mk_bool(self.ctx, fixed.truth);
                    if let Some(index) = anchors.iter().position(|&a| a == anchor) {
                        if values[index] != assigned.z3_ast {
                            return true;
                        }
                        continue;
                    }
                    indices.push(fixed_indices[&anchor]);
                    anchors.push(anchor);
                    values.push(assigned.z3_ast);
                    free_replacements.push((anchor, assigned.z3_ast));
                    projected.insert(fixed.sym, Some(Exp::Bool(fixed.truth)));
                    fixed_values.push(assigned);
                }
                let replacements: Vec<_> = anchors.iter().copied().zip(values.iter().copied()).collect();
                let mut local_replacements = HashMap::new();
                let rewrites = prefix.index.rewrites.for_assertion(true);
                let mut binding_dependencies =
                    rewrites::InputDependencies::new(free_replacements.iter().map(|&(from, _)| from).enumerate());
                // 派生输入必须满足其定义。先用同组自由输入检查绑定，矛盾组无需访问路径断言。
                // 幸存组仍按原顺序合取残余，绑定的化简结果已在重写表内。
                if !free_replacements.is_empty()
                    && bindings.iter().any(|binding| {
                        let (_, truth, fact) = rewrites.narrow(&free_replacements, binding, &mut binding_dependencies);
                        rewrites.after_narrow(truth, fact).0 == Some(false)
                    })
                {
                    return true;
                }
                let mut residual = Ast::mk_bool(self.ctx, true);
                let mut assignments_by_literal = HashMap::new();
                let mut exact = true;
                let mut reuse_witness = self.has_stashed_model() && bindings.is_empty();
                let mut possible = true;
                let assertions = relevant_facts
                    .iter()
                    .map(|(exp, ast, mask, depends, is_guard)| (Some((*exp, *mask, *depends)), *ast, *is_guard));
                for (source, original, is_guard) in assertions.chain(bindings.iter().map(|ast| (None, ast, true))) {
                    let rewrites = prefix.index.rewrites.for_assertion(is_guard);
                    let relevant = if let Some((_, mask, _)) = source {
                        local_replacements
                            .entry(mask)
                            .or_insert_with(|| {
                                indices
                                    .iter()
                                    .zip(&replacements)
                                    .filter(|(index, _)| mask & input_bit(**index) != 0)
                                    .map(|(_, pair)| *pair)
                                    .collect::<Vec<_>>()
                            })
                            .as_slice()
                    } else {
                        &free_replacements
                    };
                    let inputs = if source.is_some() { &mut dependencies } else { &mut binding_dependencies };
                    let (unchanged, mut truth, mut fact) = rewrites.narrow(relevant, original, inputs);
                    reuse_witness &= unchanged;
                    if truth.is_none() {
                        if let Some((source, _, _)) = source.filter(|(_, _, depends)| *depends && !projected.is_empty())
                        {
                            let mut changed = false;
                            let substituted = source
                                .map_var(&mut |sym| {
                                    Ok::<_, std::convert::Infallible>(
                                        self.project_finite_definition(*sym, prefix, &mut projected)
                                            .inspect(|_| changed = true)
                                            .unwrap_or(Exp::Var(*sym)),
                                    )
                                })
                                .unwrap();
                            if changed {
                                let mut other = self.translate_exp(&substituted).substitute_many(&anchors, &values);
                                if let Some(current) = other.structural_bool() {
                                    truth = Some(current);
                                    fact = other;
                                    reuse_witness = false;
                                }
                            }
                        }
                    }
                    let (truth, fact) = rewrites.after_narrow(truth, fact);
                    match truth {
                        Some(true) => (),
                        Some(false) => {
                            possible = false;
                            break;
                        }
                        None => {
                            if let Some(&(sym, positive)) = literals.get(&fact.z3_ast) {
                                if assignments_by_literal.insert(sym, positive).is_some_and(|prev| prev != positive) {
                                    possible = false;
                                    break;
                                }
                            } else {
                                exact = false;
                            }
                            residual = residual.mk_and(&fact);
                        }
                    }
                }
                if possible && residual.structural_bool() != Some(false) {
                    let exact = exact || reuse_witness;
                    if graph.incremental
                        && !outputs
                            .iter()
                            .any(|(ast, cached): &(ChoiceAst, bool)| ast.z3_ast == value.z3_ast && *cached == exact)
                    {
                        outputs.push((ChoiceAst::keep(value.clone()), exact));
                    }
                    return accept(value, exact);
                }
                true
            });
            if graph.incremental && completed {
                // 缓存容量只影响复用；全部可行候选仍交给调用方。
                if graph.state.outputs.len() == 64 {
                    graph.state.outputs.remove(0);
                }
                graph.state.outputs.push((exp.clone(), witness, outputs));
            }
            Some(())
        })
    }
}

#[cfg(test)]
#[path = "arithmetic_reference.rs"]
mod reference;
