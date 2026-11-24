// ec45fa52 的逐组合实现，用来核对输出顺序、见证和候选排除。
use super::*;
impl<'ctx, B: BV> Solver<'ctx, B> {
    pub(in crate::smt::finite_domain) fn reference_combined_values(
        &self,
        prefix: &PathConditions<'_, B>,
        exp: &Formula,
        mut accept: impl FnMut(Ast<'ctx>, bool) -> bool,
    ) -> Option<()> {
        let mut state = ChoiceGraph::default();
        let mut graph = Graph { solver: self, prefix, state: &mut state, incremental: false };
        let root = graph.build(exp)?;
        if graph.state.inputs.is_empty() {
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
        let mut assignments = vec![None; graph.state.inputs.len()];
        let mut stack: Vec<(usize, usize)> = Vec::new();
        loop {
            match root.evaluate(self.ctx, &assignments, &mut Evaluated::default()) {
                Err(index) => stack.push((index, 0)),
                Ok(value) => {
                    let mut projected = HashMap::new();
                    let mut anchors = Vec::new();
                    let mut values = Vec::new();
                    let mut free_anchors = Vec::new();
                    let mut free_values = Vec::new();
                    let mut bindings = Vec::new();
                    for &(index, next) in &stack {
                        let input = &graph.state.inputs[index];
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
                            bindings.push(input.anchor.get(self.ctx).mk_eq(assigned));
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
                if let Some(choice) = graph.state.inputs[*index].choices.get(*next) {
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
