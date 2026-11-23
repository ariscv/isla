//! 按原发布顺序认证失败叶。相邻检查点只共享顺序和对象身份都相同的 SMT 前缀。
use super::*;

struct ReplayStep<B> {
    event: *const Event<B>,
    declarations: usize,
    assertions: usize,
    next_var: u32,
}

pub(super) struct ArmErrorReplay<'ctx, B> {
    verifier: Solver<'ctx, B>,
    steps: Vec<ReplayStep<B>>,
    // 回放 DefineEnum 时分配的成员编号，与失败点已经发布的 next_var 分开。
    replay_next_var: u32,
}

impl<'ctx, B: BV> ArmErrorReplay<'ctx, B> {
    pub(super) fn new(ctx: &'ctx Context) -> Self {
        let mut verifier = Solver::new(ctx);
        verifier.replay_assertions = Some(Vec::new());
        Self { verifier, steps: Vec::new(), replay_next_var: 0 }
    }

    pub(super) fn restore(&mut self, point: &Checkpoint<B>) -> &Solver<'ctx, B> {
        let verifier = &mut self.verifier;
        // verifier.trace.tail 持有上一叶直到比较结束，两侧地址都来自仍存活的不可变事件。
        let traces: Vec<_> = std::iter::successors(point.trace().as_ref(), |t| t.tail.as_ref().as_ref()).collect();
        assert_eq!(traces.len(), point.num);
        let mut events =
            traces.into_iter().rev().flat_map(Trace::head_events).filter(|e| matches!(e, Event::Smt(..))).peekable();
        let mut common = 0;
        while let Some(old) = self.steps.get(common) {
            if events.next_if(|e| std::ptr::eq(old.event, *e)).is_none() {
                break;
            }
            common += 1;
        }
        if let Some(old) = self.steps.get(common) {
            verifier.rewind_declarations(old.declarations);
            verifier.replay_assertions.as_mut().unwrap().truncate(old.assertions);
            verifier.asserts_since_check = old.assertions;
            self.replay_next_var = old.next_var;
            self.steps.truncate(common);
        }
        verifier.next_var = self.replay_next_var;
        for event in events {
            self.steps.push(ReplayStep {
                event,
                declarations: verifier.declaration_undo.len(),
                assertions: verifier.replay_assertions.as_ref().unwrap().len(),
                next_var: verifier.next_var,
            });
            verifier.add_event_internal(event);
        }
        self.replay_next_var = verifier.next_var;
        // 查询诊断与超时转储须能从当前叶的完整失败点单独恢复。
        verifier.trace.tail = point.trace.clone();
        verifier.trace.checkpoints = point.num;
        verifier.next_var = point.next_var;
        verifier.cycles = point.cycles;
        verifier
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use smtlib::Def::*;
    use smtlib::Exp::*;

    #[test]
    fn arm_error_replay_restores_rebindings_and_each_failure_formula() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let loc = SourceLoc::unknown();
        let mut parent = Solver::<B64>::new(&ctx);
        let guard = parent.declare_const(Ty::Bool, loc);
        let fun = parent.fresh();
        parent.add(DeclareFun(fun, vec![Ty::Bool], Ty::Bool));
        parent.assert(Bool(true));
        parent.assert(Var(guard));
        parent.assert(Var(guard));
        let entry = checkpoint(&mut parent);

        let mut left = Solver::from_checkpoint(&ctx, entry.clone());
        left.add(DefineConst(guard, Bool(false)));
        left.add(DeclareFun(fun, vec![Ty::Bool], Ty::BitVec(8)));
        let tagged = left.define_bitvector(App(fun, vec![Bool(true)]), loc);
        let enumeration = left.get_enum(Name::from_u32(923), 2);
        let value = left.declare_const(Ty::Enum(enumeration), loc);
        left.assert_eq(Var(value), Enum(enumeration.first_member()));
        let left = checkpoint(&mut left);

        let tx = parent.start_transaction();
        let arm = parent.new_logical_arm(None);
        let right = parent.with_logical_arm(arm, |p| {
            p.add_event(Event::Instr(Val::Unit));
            p.assert(App(fun, vec![Var(guard)]));
            p.with_transaction_condition(&Var(guard), |p| p.arm_error_snapshot(arm).0)
        });
        parent.rollback_transaction(tx);

        let mut replay = ArmErrorReplay::new(&ctx);
        for (point, live) in [(&left, false), (&right, true), (&right, true), (&entry, true), (&left, false)] {
            let cached = replay.restore(point);
            let mut old = Solver::from_checkpoint(&ctx, point.clone());
            assert_eq!(cached.translate_exp(&Var(guard)).z3_ast, old.translate_exp(&Var(guard)).z3_ast);
            assert_eq!(cached.func_decls[&fun].z3_func_decl, old.func_decls[&fun].z3_func_decl);
            assert_eq!(cached.is_sail_bitvector(tagged), old.is_sail_bitvector(tagged));
            assert_eq!(cached.enums.enums.len(), old.enums.enums.len());
            assert_eq!(cached.next_var, point.next_var);
            assert!(Arc::ptr_eq(&cached.trace.tail, &point.trace));
            unsafe {
                let assertions = Z3_solver_get_assertions(ctx.z3_ctx, old.z3_solver);
                Z3_ast_vector_inc_ref(ctx.z3_ctx, assertions);
                let expected: Vec<_> = (0..Z3_ast_vector_size(ctx.z3_ctx, assertions))
                    .map(|i| Z3_ast_vector_get(ctx.z3_ctx, assertions, i))
                    .collect();
                let actual: Vec<_> = cached.replay_assertions.as_ref().unwrap().iter().map(|a| a.z3_ast).collect();
                assert_eq!(actual, expected);
                Z3_ast_vector_dec_ref(ctx.z3_ctx, assertions);
            }
            assert_eq!(old.check_sat_with(&Var(guard), loc), if live { Sat } else { Unsat });
        }
    }
}
