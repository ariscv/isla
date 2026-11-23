//! 对原始定义建立共享表达式图。沿一组输入赋值遍历，只展开当前 ITE 值臂。
use super::*;
use std::rc::Rc;

type Formula = Exp<Sym>;
type Evaluated<'a, 'ctx> = HashMap<*const Expression<'a, 'ctx>, Ast<'ctx>>;
type Node<'a, 'ctx> = Rc<Expression<'a, 'ctx>>;

enum Expression<'a, 'ctx> {
    Constant(Ast<'ctx>),
    Input(usize),
    Select(Node<'a, 'ctx>, Node<'a, 'ctx>, Node<'a, 'ctx>),
    Apply(&'a Formula, Vec<Node<'a, 'ctx>>),
}

struct Input<'ctx> {
    symbol: Option<Sym>,
    guard_symbol: Option<Sym>,
    anchor: Ast<'ctx>,
    choices: Vec<Formula>,
    free: bool,
}

struct Graph<'a, 'prefix, 'ctx, B> {
    solver: &'a Solver<'ctx, B>,
    prefix: &'a PathConditions<'prefix, B>,
    symbols: HashMap<Sym, Option<Node<'a, 'ctx>>>,
    guards: HashMap<Z3_ast, usize>,
    inputs: Vec<Input<'ctx>>,
}

impl<'a, 'ctx, B: BV> Graph<'a, '_, 'ctx, B> {
    fn build(&mut self, exp: &'a Formula) -> Option<Node<'a, 'ctx>> {
        use Exp::*;
        if let Var(sym) = exp {
            if let Some(cached) = self.symbols.get(sym) {
                return cached.clone();
            }
            let definition = self.prefix.definition(*sym);
            let node = definition.and_then(|exp| self.build(exp)).or_else(|| {
                let choices = self.prefix.bounds(exp)?;
                let index = self.inputs.len();
                self.inputs.push(Input {
                    symbol: Some(*sym),
                    guard_symbol: None,
                    anchor: self.solver.translate_exp(exp),
                    choices,
                    free: matches!(resolve(exp, self.prefix), Var(_)),
                });
                Some(Rc::new(Expression::Input(index)))
            });
            self.symbols.insert(*sym, node.clone());
            return node;
        }
        let node = match exp {
            Bits(_) | Bits64(_) | Bool(_) | Enum(_) => Expression::Constant(self.solver.translate_exp(exp)),
            Ite(guard, yes, no) => {
                let yes = self.build(yes)?;
                let no = self.build(no)?;
                let guard = self.build(guard).unwrap_or_else(|| {
                    let mut anchor = self.solver.translate_exp(guard);
                    if let Some(value) = anchor.structural_bool() {
                        return Rc::new(Expression::Constant(Ast::mk_bool(self.solver.ctx, value)));
                    }
                    let index = *self.guards.entry(anchor.z3_ast).or_insert_with(|| {
                        let free =
                            self.prefix.bool_symbols().any(|sym| self.solver.decls[&sym].ast().z3_ast == anchor.z3_ast);
                        let index = self.inputs.len();
                        let guard_symbol = if let Var(sym) = guard.as_ref() { Some(*sym) } else { None };
                        self.inputs.push(Input {
                            symbol: None,
                            guard_symbol,
                            anchor,
                            choices: vec![Bool(true), Bool(false)],
                            free,
                        });
                        index
                    });
                    Rc::new(Expression::Input(index))
                });
                Expression::Select(guard, yes, no)
            }
            Bvadd(lhs, rhs)
            | Bvsub(lhs, rhs)
            | Bvmul(lhs, rhs)
            | Bvshl(lhs, rhs)
            | Eq(lhs, rhs)
            | Neq(lhs, rhs)
            | Bvult(lhs, rhs)
            | Bvule(lhs, rhs)
            | Bvugt(lhs, rhs)
            | Bvuge(lhs, rhs)
            | Bvslt(lhs, rhs)
            | Bvsle(lhs, rhs)
            | Bvsgt(lhs, rhs)
            | Bvsge(lhs, rhs)
            | And(lhs, rhs)
            | Or(lhs, rhs) => Expression::Apply(exp, vec![self.build(lhs)?, self.build(rhs)?]),
            ZeroExtend(_, value) | SignExtend(_, value) | Extract(_, _, value) | Not(value) | Bvneg(value) => {
                Expression::Apply(exp, vec![self.build(value)?])
            }
            _ => return None,
        };
        Some(Rc::new(node))
    }

    // 两种投影共用同一棵按需展开的选择树。返回 false 表示调用方已提前结束遍历。
    fn visit(
        &self,
        root: &Expression<'a, 'ctx>,
        compared: Option<&Expression<'a, 'ctx>>,
        mut accept: impl FnMut(Ast<'ctx>, &[(usize, usize)], &[Option<Ast<'ctx>>], &Evaluated<'a, 'ctx>) -> bool,
    ) -> bool {
        let mut assignments = vec![None; self.inputs.len()];
        let mut stack: Vec<(usize, usize)> = Vec::new();
        loop {
            let mut evaluated = HashMap::new();
            let result = root.evaluate(&assignments, &mut evaluated).and_then(|value| {
                if let Some(compared) = compared {
                    compared.evaluate(&assignments, &mut evaluated)?;
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
                if let Some(choice) = self.inputs[*index].choices.get(*next) {
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
        root: &Expression<'a, 'ctx>,
        compared: Option<(Sym, &Expression<'a, 'ctx>)>,
        values: &mut Vec<Formula>,
    ) {
        let mut possible = vec![false; values.len()];
        // 选择条件可以先由枚举值或算术表达式算出。保留本组合已求值的布尔符号，
        // 返回标签使用同一条件时可直接复用，无需从枚举构造子再次推导。
        let predicates: Vec<_> = self
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
                let mut ast = evaluated[&std::ptr::from_ref(expr)].clone();
                projected.insert(sym, Some(ast.finite_bits().expect("比较操作数必须为位向量常量")));
            }
            for &(input, next) in stack {
                let input = &self.inputs[input];
                if let Some(sym) = input.symbol.or(input.guard_symbol) {
                    projected.insert(sym, Some(input.choices[next - 1].clone()));
                }
            }
            for &(sym, node) in &predicates {
                if let Some(value) = evaluated.get(&node) {
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

impl<'ctx> Expression<'_, 'ctx> {
    // 返回本次求值所需的下一个输入。多个操作数引用同一输入时复用其赋值。
    fn evaluate(
        &self,
        assignments: &[Option<Ast<'ctx>>],
        cache: &mut HashMap<*const Self, Ast<'ctx>>,
    ) -> Result<Ast<'ctx>, usize> {
        use Exp::*;
        if let Some(value) = cache.get(&(self as *const Self)) {
            return Ok(value.clone());
        }
        let value = match self {
            Self::Constant(value) => value.clone(),
            Self::Input(index) => assignments[*index].clone().ok_or(*index)?,
            Self::Select(guard, yes, no) => {
                let guard = guard.evaluate(assignments, cache)?.structural_bool().expect("有限域守卫必须为常量");
                (if guard { yes } else { no }).evaluate(assignments, cache)?
            }
            Self::Apply(exp, args) => {
                let lhs = args[0].evaluate(assignments, cache)?;
                if let [_, rhs] = args.as_slice() {
                    let rhs = rhs.evaluate(assignments, cache)?;
                    match exp {
                        Bvadd(..) => lhs.mk_bvadd(&rhs),
                        Bvsub(..) => lhs.mk_bvsub(&rhs),
                        Bvmul(..) => lhs.mk_bvmul(&rhs),
                        Bvshl(..) => lhs.mk_bvshl(&rhs),
                        Eq(..) => lhs.mk_eq(&rhs),
                        Neq(..) => lhs.mk_eq(&rhs).mk_not(),
                        Bvult(..) => lhs.mk_bvult(&rhs),
                        Bvule(..) => lhs.mk_bvule(&rhs),
                        Bvugt(..) => lhs.mk_bvugt(&rhs),
                        Bvuge(..) => lhs.mk_bvuge(&rhs),
                        Bvslt(..) => lhs.mk_bvslt(&rhs),
                        Bvsle(..) => lhs.mk_bvsle(&rhs),
                        Bvsgt(..) => lhs.mk_bvsgt(&rhs),
                        Bvsge(..) => lhs.mk_bvsge(&rhs),
                        And(..) => lhs.mk_and(&rhs),
                        Or(..) => lhs.mk_or(&rhs),
                        _ => unreachable!("有限域表达式图只登记可组合的二元操作"),
                    }
                } else {
                    match exp {
                        ZeroExtend(width, _) => lhs.zero_extend(*width),
                        SignExtend(width, _) => lhs.sign_extend(*width),
                        Extract(hi, lo, _) => lhs.extract(*hi, *lo),
                        Not(_) => lhs.mk_not(),
                        Bvneg(_) => lhs.mk_bvneg(),
                        _ => unreachable!("有限域表达式图只登记可组合的一元操作"),
                    }
                }
            }
        };
        cache.insert(self, value.clone());
        Ok(value)
    }
}

// 每位代表一类输入。超过 128 个输入时碰撞只会多保留代入项。
fn input_bit(index: usize) -> u128 {
    1 << (index % u128::BITS as usize)
}

// 断言根、输入和各自的子节点在此次遍历中均由调用方持有。
// 即使节点本身是锚点也要统计子树：某组赋值可能只选中了内层锚点。
fn assertion_inputs(inputs: &[Input], facts: &[(&Formula, Ast)]) -> Vec<u128> {
    let mut anchors = HashMap::new();
    for (i, input) in inputs.iter().enumerate() {
        *anchors.entry(input.anchor.z3_ast).or_insert(0) |= input_bit(i);
    }
    let mut dependencies = HashMap::new();
    facts
        .iter()
        .map(|(_, fact)| {
            let z3 = fact.ctx.z3_ctx;
            let mut pending = vec![(fact.z3_ast, false)];
            while let Some((node, expanded)) = pending.pop() {
                if dependencies.contains_key(&node) {
                    continue;
                }
                let mut mask = anchors.get(&node).copied().unwrap_or(0);
                unsafe {
                    match Z3_get_ast_kind(z3, node) {
                        AstKind::App => {
                            let app = Z3_to_app(z3, node);
                            let children = (0..Z3_get_app_num_args(z3, app)).map(|i| Z3_get_app_arg(z3, app, i));
                            if !expanded {
                                pending.push((node, true));
                                pending.extend(children.map(|child| (child, false)));
                                continue;
                            }
                            for child in children {
                                mask |= dependencies[&child];
                            }
                        }
                        AstKind::Numeral | AstKind::Var => (),
                        // 带绑定器的子式交给 Z3 按原有作用域执行全部代入。
                        _ => mask = u128::MAX,
                    }
                }
                dependencies.insert(node, mask);
            }
            dependencies[&fact.z3_ast]
        })
        .collect()
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    /// 按产生目标值的输入重算活动守卫。只要一组赋值尚未被排除，就保留该值。
    pub(crate) fn refine_guarded_values(
        &self,
        target: Sym,
        values: &mut Vec<Formula>,
        in_bounds: impl Fn(&Formula) -> bool,
    ) {
        let Some(last_guard) = self.transaction_conditions.last() else { return };
        let Some(prefix) = PathConditions::new(self) else {
            return;
        };
        let mut graph = Graph {
            solver: self,
            prefix: &prefix,
            symbols: HashMap::new(),
            guards: HashMap::new(),
            inputs: Vec::new(),
        };
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
        prefix.comparison_subjects(last_guard, &mut subjects);
        for subject in subjects {
            let Exp::Var(sym) = subject else { continue };
            if *sym == target {
                continue;
            }
            let Some(node) = graph.build(subject) else { continue };
            graph.retain_guarded(target, &root, Some((*sym, &node)), values);
            if values.iter().all(&in_bounds) {
                break;
            }
        }
    }

    pub(super) fn combined_values(
        &self,
        prefix: &PathConditions<'_, B>,
        exp: &Formula,
        mut accept: impl FnMut(Ast<'ctx>, bool) -> bool,
    ) -> Option<()> {
        let mut graph =
            Graph { solver: self, prefix, symbols: HashMap::new(), guards: HashMap::new(), inputs: Vec::new() };
        let root = graph.build(exp)?;
        if graph.inputs.is_empty() {
            return None;
        }
        let facts: Vec<_> = prefix.assertions().map(|exp| (exp, self.translate_exp(exp))).collect();
        let dependencies = assertion_inputs(&graph.inputs, &facts);
        let mut negative_atoms = Vec::new();
        let mut literals = HashMap::new();
        for sym in prefix.bool_symbols() {
            let atom = self.decls[&sym].ast();
            let negative = atom.mk_not();
            literals.insert(atom.z3_ast, (sym, true));
            literals.insert(negative.z3_ast, (sym, false));
            negative_atoms.push(negative);
        }
        graph.visit(&root, None, |value, stack, assignments, _| {
            let mut projected = HashMap::new();
            let mut anchors = Vec::new();
            let mut values = Vec::new();
            let mut free_replacements = Vec::new();
            let mut bindings = Vec::new();
            for &(index, next) in stack {
                let input = &graph.inputs[index];
                let assigned = assignments[index].as_ref().expect("活跃的有限域分支必须已有赋值");
                if let Some(sym) = input.symbol {
                    projected.insert(sym, Some(input.choices[next - 1].clone()));
                }
                anchors.push(input.anchor.z3_ast);
                values.push(assigned.z3_ast);
                if input.free {
                    free_replacements.push((input.anchor.z3_ast, assigned.z3_ast));
                } else {
                    bindings.push(input.anchor.mk_eq(assigned));
                }
            }
            let replacements: Vec<_> = anchors.iter().copied().zip(values.iter().copied()).collect();
            let mut local_replacements = HashMap::new();
            let rewrites = &prefix.index.rewrites;
            // 派生输入必须满足其定义。先用同组自由输入检查绑定，矛盾组无需访问路径断言。
            // 幸存组仍按原顺序合取残余，绑定的化简结果已在重写表内。
            if !free_replacements.is_empty()
                && bindings.iter().any(|binding| {
                    let (_, _, fact) = rewrites.narrow(&free_replacements, binding);
                    rewrites.simplified(fact).0 == Some(false)
                })
            {
                return true;
            }
            let mut residual = Ast::mk_bool(self.ctx, true);
            let mut assignments_by_literal = HashMap::new();
            let mut exact = true;
            let mut reuse_witness = self.has_stashed_model() && bindings.is_empty();
            let mut possible = true;
            let assertions = facts.iter().zip(&dependencies).map(|((exp, ast), mask)| (Some((*exp, *mask)), ast));
            for (source, original) in assertions.chain(bindings.iter().map(|ast| (None, ast))) {
                let relevant = if let Some((_, mask)) = source {
                    local_replacements
                        .entry(mask)
                        .or_insert_with(|| {
                            stack
                                .iter()
                                .zip(&replacements)
                                .filter(|((index, _), _)| mask & input_bit(*index) != 0)
                                .map(|(_, pair)| *pair)
                                .collect::<Vec<_>>()
                        })
                        .as_slice()
                } else {
                    &free_replacements
                };
                let (unchanged, truth, mut fact) = rewrites.narrow(relevant, original);
                reuse_witness &= unchanged;
                if truth.is_none() {
                    if let Some((source, _)) = source.filter(|_| !projected.is_empty()) {
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
                            if other.structural_bool().is_some() {
                                fact = other;
                                reuse_witness = false;
                            }
                        }
                    }
                }
                let (truth, fact) = rewrites.simplified(fact);
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
            if possible && residual.structural_bool() != Some(false) && !accept(value, exact || reuse_witness) {
                return false;
            }
            true
        });
        Some(())
    }
}

#[cfg(test)]
#[path = "arithmetic_reference.rs"]
mod reference;
