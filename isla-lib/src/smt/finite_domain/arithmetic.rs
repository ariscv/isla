//! 对原始定义建立共享表达式图。沿一组输入赋值遍历，只展开当前 ITE 值臂。
use super::*;
use std::rc::Rc;

type Formula = Exp<Sym>;
type Node<'a, 'ctx> = Rc<Expression<'a, 'ctx>>;

enum Expression<'a, 'ctx> {
    Constant(Ast<'ctx>),
    Input(usize),
    Select(Node<'a, 'ctx>, Node<'a, 'ctx>, Node<'a, 'ctx>),
    Apply(&'a Formula, Vec<Node<'a, 'ctx>>),
}

struct Input<'ctx> {
    symbol: Option<Sym>,
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
                        self.inputs.push(Input { symbol: None, anchor, choices: vec![Bool(true), Bool(false)], free });
                        index
                    });
                    Rc::new(Expression::Input(index))
                });
                Expression::Select(guard, yes, no)
            }
            Bvadd(lhs, rhs)
            | Bvsub(lhs, rhs)
            | Bvmul(lhs, rhs)
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

impl<'ctx, B: BV> Solver<'ctx, B> {
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
        let mut negative_atoms = Vec::new();
        let mut literals = HashMap::new();
        for sym in prefix.bool_symbols() {
            let atom = self.decls[&sym].ast();
            let negative = atom.mk_not();
            literals.insert(atom.z3_ast, (sym, true));
            literals.insert(negative.z3_ast, (sym, false));
            negative_atoms.push(negative);
        }
        let mut assignments = vec![None; graph.inputs.len()];
        let mut stack: Vec<(usize, usize)> = Vec::new();
        loop {
            match root.evaluate(&assignments, &mut HashMap::new()) {
                Err(index) => stack.push((index, 0)),
                Ok(value) => {
                    let mut projected = HashMap::new();
                    let mut anchors = Vec::new();
                    let mut values = Vec::new();
                    let mut free_anchors = Vec::new();
                    let mut free_values = Vec::new();
                    let mut bindings = Vec::new();
                    for &(index, next) in &stack {
                        let input = &graph.inputs[index];
                        let assigned = assignments[index].as_ref().expect("活跃的有限域分支必须已有赋值");
                        if let Some(sym) = input.symbol {
                            projected.insert(sym, Some(input.choices[next - 1].clone()));
                        }
                        anchors.push(input.anchor.z3_ast);
                        values.push(assigned.z3_ast);
                        if input.free {
                            free_anchors.push(input.anchor.z3_ast);
                            free_values.push(assigned.z3_ast);
                        } else {
                            bindings.push(input.anchor.mk_eq(assigned));
                        }
                    }
                    let mut residual = Ast::mk_bool(self.ctx, true);
                    let mut assignments_by_literal = HashMap::new();
                    let mut exact = true;
                    let mut reuse_witness = self.has_stashed_model() && bindings.is_empty();
                    let mut possible = true;
                    for (source, original) in
                        facts.iter().map(|(exp, ast)| (Some(*exp), ast)).chain(bindings.iter().map(|ast| (None, ast)))
                    {
                        let mut fact = if source.is_some() {
                            original.substitute_many(&anchors, &values)
                        } else {
                            original.substitute_many(&free_anchors, &free_values)
                        };
                        reuse_witness &= fact.z3_ast == original.z3_ast;
                        if fact.structural_bool().is_none() {
                            if let Some(source) = source.filter(|_| !projected.is_empty()) {
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
                        match fact.structural_bool() {
                            Some(true) => (),
                            Some(false) => {
                                possible = false;
                                break;
                            }
                            None => {
                                if let Some(&(sym, positive)) = literals.get(&fact.z3_ast) {
                                    if assignments_by_literal.insert(sym, positive).is_some_and(|prev| prev != positive)
                                    {
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
                        return Some(());
                    }
                }
            }
            while let Some((index, next)) = stack.last_mut() {
                if let Some(choice) = graph.inputs[*index].choices.get(*next) {
                    assignments[*index] = Some(self.translate_exp(choice));
                    *next += 1;
                    break;
                }
                assignments[*index] = None;
                stack.pop();
            }
            if stack.is_empty() {
                return Some(());
            }
        }
    }
}
