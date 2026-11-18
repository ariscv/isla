//! 辅助求解只重建可访问输入和断言的传递依赖；原执行保存点不变。
use super::*;

impl<B: BV> Checkpoint<B> {
    /// 生成不读取历史事件的辅助SMT上下文。调用者须给出所有可访问初始值的符号。
    /// 所有断言和类型/声明保留，只移除无关定义与非SMT历史事件；保留原符号编号空间。
    pub fn smt_for_inputs(&self, inputs: &HashSet<Sym, ahash::RandomState>) -> Self {
        let mut needed = inputs.clone();
        let mut events = Vec::new();
        if let Some(trace) = self.trace.as_ref().as_ref() {
            // to_vec按逆时间排序，先标活使用者，再保留其传递依赖。
            for event in trace.to_vec() {
                let keep = match event {
                    Event::Smt(Def::Assert(exp), _, _) => {
                        exp.collect_variables(&mut needed);
                        true
                    }
                    Event::Smt(Def::DefineConst(sym, exp), _, _) => {
                        if needed.remove(sym) {
                            exp.collect_variables(&mut needed);
                            true
                        } else {
                            false
                        }
                    }
                    Event::Smt(..) => true,
                    _ => false,
                };
                if keep {
                    events.push(event.clone());
                }
            }
        }
        events.reverse();
        Checkpoint {
            num: 1,
            next_var: self.next_var,
            trace: Arc::new(Some(Trace { checkpoints: 0, head: events, tail: Arc::new(None) })),
            cycles: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;

    #[test]
    fn dependency_slice_keeps_input_aliases_and_every_assertion() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut source = Solver::<B64>::new(&ctx);
        let loc = SourceLoc::unknown();
        let x = source.declare_bitvector(8, loc);
        let checked =
            source.define_bitvector(Exp::Bvadd(Box::new(Exp::Var(x)), Box::new(Exp::Bits64(B64::new(1, 8)))), loc);
        let alias =
            source.define_bitvector(Exp::Bvadd(Box::new(Exp::Var(x)), Box::new(Exp::Bits64(B64::new(3, 8)))), loc);
        let unused = source.define_bitvector(Exp::Bvmul(Box::new(Exp::Var(x)), Box::new(Exp::Var(alias))), loc);
        source.assert_eq(Exp::Var(checked), Exp::Bits64(B64::new(7, 8)));
        source.add_event(Event::WriteReg(Name::from_u32(91), vec![], Val::Symbolic(unused)));
        let full = checkpoint(&mut source);
        let isolated = full.smt_for_inputs(&Val::<B64>::Symbolic(alias).symbolic_variables());
        let events = isolated.trace().as_ref().unwrap().to_vec();
        assert!(!events
            .iter()
            .any(|event| matches!(event, Event::Smt(Def::DefineConst(sym, _), _, _) if *sym==unused)));
        assert!(events.iter().all(|event| matches!(event, Event::Smt(..))));
        let helper_ctx = Context::new(Config::new());
        let mut helper = Solver::from_checkpoint(&helper_ctx, isolated.clone());
        assert!(helper.is_sail_bitvector(alias));
        assert_eq!(helper.check_sat(loc), SmtResult::Sat);
        assert_eq!(
            helper.check_sat_with(&Exp::Neq(Box::new(Exp::Var(alias)), Box::new(Exp::Bits64(B64::new(9, 8)))), loc),
            SmtResult::Unsat
        );
        helper.assert_eq(Exp::Var(alias), Exp::Bits64(B64::new(10, 8)));
        let combined = full.with_suffix_from(&isolated, &checkpoint(&mut helper));
        assert!(combined.trace().as_ref().unwrap().to_vec().iter().any(|event| matches!(event, Event::WriteReg(..))));
        let final_ctx = Context::new(Config::new());
        let mut final_solver = Solver::from_checkpoint(&final_ctx, combined);
        assert_eq!(final_solver.check_sat(loc), SmtResult::Unsat);
    }

    #[test]
    fn dependency_slice_keeps_definitions_used_only_by_constraints() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut source = Solver::<B64>::new(&ctx);
        let loc = SourceLoc::unknown();
        let x = source.declare_const(Ty::Bool, loc);
        let required = source.define_const(Exp::Not(Box::new(Exp::Var(x))), loc);
        let unused = source.define_const(Exp::Var(x), loc);
        source.assert(Exp::Var(required));
        let slice = checkpoint(&mut source).smt_for_inputs(&Default::default());
        assert!(!slice
            .trace()
            .as_ref()
            .unwrap()
            .to_vec()
            .iter()
            .any(|event| matches!(event, Event::Smt(Def::DefineConst(sym, _), _, _) if *sym==unused)));
        let other = Context::new(Config::new());
        let mut replay = Solver::from_checkpoint(&other, slice);
        assert_eq!(replay.check_sat_with(&Exp::Var(x), loc), SmtResult::Unsat);
    }
}

#[test]
fn shared_context_replay_preserves_independent_constraints_and_values() {
    use crate::bitvector::b64::B64;
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut original = Solver::<B64>::new(&ctx);
    let loc = SourceLoc::unknown();
    let input = original.declare_bitvector(8, loc);
    let value =
        original.define_bitvector(Exp::Bvxor(Box::new(Exp::Var(input)), Box::new(Exp::Bits64(B64::new(0xA5, 8)))), loc);
    original.assert_eq(Exp::Var(input), Exp::Bits64(B64::new(0x42, 8)));
    let cp = checkpoint(&mut original);
    let mut replay = Solver::from_checkpoint(original.context(), cp);
    assert_eq!(original.decls.get(&value).unwrap().z3_ast, replay.decls.get(&value).unwrap().z3_ast);
    replay.assert_eq(Exp::Var(input), Exp::Bits64(B64::new(0x43, 8)));
    assert_eq!(replay.check_sat(loc), SmtResult::Unsat);
    assert_eq!(original.check_sat(loc), SmtResult::Sat);
    assert_eq!(Model::new(&original).get_var(value).unwrap().unwrap_exp(), Exp::Bits64(B64::new(0xE7, 8)));
}
