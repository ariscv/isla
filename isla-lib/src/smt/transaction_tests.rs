//! 保存点的提交、回滚与事件出口契约。
use super::*;
use crate::bitvector::b64::B64;
use smtlib::Def::*;
use smtlib::Exp::*;

#[test]
fn smt_savepoint_commit_rollback_combinations() {
    let ctx = Context::new(Config::new());
    for outer_commit in [false, true] {
        for inner_commit in [false, true] {
            let mut solver = Solver::<B64>::new(&ctx);
            let outer = solver.start_transaction();
            let a = solver.declare_bitvector(8, SourceLoc::unknown());
            solver.add_event(Event::Cycle);
            let inner = solver.start_transaction();
            let b = solver.declare_bitvector(16, SourceLoc::unknown());
            solver.add_event(Event::Cycle);
            assert_eq!(solver.transaction_depth(), 2);
            if inner_commit {
                solver.commit_transaction();
            } else {
                solver.rollback_transaction(inner);
            }
            assert_eq!(solver.transaction_depth(), 1);
            assert!(solver.trace.head.is_empty());
            assert_eq!(solver.decls.contains_key(&b), inner_commit);
            assert_eq!(solver.is_sail_bitvector(b), inner_commit);
            if outer_commit {
                solver.commit_transaction();
            } else {
                solver.rollback_transaction(outer);
            }
            assert_eq!(solver.transaction_depth(), 0);
            assert_eq!(solver.decls.contains_key(&a), outer_commit);
            assert_eq!(solver.decls.contains_key(&b), outer_commit && inner_commit);
            assert_eq!(
                solver.trace.head.len(),
                if outer_commit {
                    if inner_commit {
                        4
                    } else {
                        2
                    }
                } else {
                    0
                }
            );
            assert!(solver.fresh().id > b.id, "回滚不能复用已经交给调用方的符号编号");
            let point = checkpoint(&mut solver);
            let replayed = Solver::from_checkpoint(&ctx, point);
            assert_eq!(replayed.is_sail_bitvector(a), outer_commit);
            assert_eq!(replayed.is_sail_bitvector(b), outer_commit && inner_commit);
        }
    }
}

#[test]
fn smt_savepoint_three_levels_publish_events_in_order() {
    let ctx = Context::new(Config::new());
    for middle_commit in [false, true] {
        for deepest_commit in [false, true] {
            let mut solver = Solver::<B64>::new(&ctx);
            solver.start_transaction();
            solver.trace_call(Name::from_u32(1));
            let middle = solver.start_transaction();
            solver.cycle_count();
            let deepest = solver.start_transaction();
            solver.trace_call(Name::from_u32(2));
            assert_eq!(solver.transaction_depth(), 3);
            if deepest_commit {
                solver.commit_transaction();
            } else {
                solver.rollback_transaction(deepest);
            }
            solver.trace_return(Name::from_u32(2));
            if middle_commit {
                solver.commit_transaction();
            } else {
                solver.rollback_transaction(middle);
            }
            solver.trace_return(Name::from_u32(1));
            assert!(solver.trace.head.is_empty());
            solver.commit_transaction();
            let mut expected: Vec<Event<B64>> = vec![Event::Function { name: Name::from_u32(1), call: true }];
            if middle_commit {
                expected.push(Event::Cycle);
                if deepest_commit {
                    expected.push(Event::Function { name: Name::from_u32(2), call: true });
                }
                expected.push(Event::Function { name: Name::from_u32(2), call: false });
            }
            expected.push(Event::Function { name: Name::from_u32(1), call: false });
            assert_eq!(format!("{:?}", solver.trace.head), format!("{:?}", expected));
            assert_eq!(solver.get_cycle_count(), if middle_commit { 1 } else { 0 });
        }
    }
}

#[test]
fn smt_savepoint_restores_overwritten_symbols_and_attributes() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let sym = solver.declare_bitvector(8, SourceLoc::unknown());
    let function = solver.fresh();
    solver.add(DeclareFun(function, vec![Ty::Bool], Ty::Bool));
    let plain = solver.declare_const(Ty::BitVec(8), SourceLoc::unknown());
    let ast = solver.decls[&sym].z3_ast;
    let fd = solver.func_decls[&function].z3_func_decl;
    let tx = solver.start_transaction();
    solver.add(DeclareConst(sym, Ty::Bool));
    solver.add(DeclareFun(function, vec![], Ty::BitVec(8)));
    solver.set_def_attrs(DefAttrs::default().sail_bitvector());
    solver.add(DeclareConst(plain, Ty::BitVec(8)));
    assert!(solver.is_sail_bitvector(plain));
    solver.cycle_count();
    solver.rollback_transaction(tx);
    assert_eq!(solver.decls[&sym].z3_ast, ast);
    assert_eq!(solver.func_decls[&function].z3_func_decl, fd);
    assert!(solver.is_sail_bitvector(sym));
    assert!(!solver.is_sail_bitvector(plain));
    assert_eq!(solver.def_attrs.attrs, 0);
    assert_eq!(solver.get_cycle_count(), 0);
}

#[test]
fn smt_savepoint_invalid_is_inherited_and_rollback_is_local() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let existing = solver.declare_const(Ty::BitVec(8), SourceLoc::unknown());
    let outer = solver.start_transaction();
    let inner = solver.start_transaction();
    // 修改当前层之外的定义属性仍不受支持；断言本身不再导致 invalid。
    solver.mark_bitvector(existing);
    assert!(solver.transaction_invalid());
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| solver.commit_transaction())).is_err());
    solver.rollback_transaction(inner);
    assert!(!solver.transaction_invalid());
    solver.mark_bitvector(existing);
    let inner = solver.start_transaction();
    assert!(solver.transaction_invalid(), "新层不能清除父层的拒绝状态");
    solver.rollback_transaction(inner);
    assert!(solver.transaction_invalid());
    solver.rollback_transaction(outer);
    assert!(!solver.transaction_invalid());
    assert_eq!(solver.check_sat(SourceLoc::unknown()), Sat);
}

#[test]
fn smt_savepoint_assert_after_inner_commit_is_buffered_in_parent() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let outer = solver.start_transaction();
    solver.start_transaction();
    let sym = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    solver.commit_transaction();
    // 既有执行器在内层提交后补断言，仍属于父层并能随父层回滚。
    solver.assert(Var(sym));
    assert!(!solver.transaction_invalid());
    assert_eq!(solver.check_sat_with(&Var(sym), SourceLoc::unknown()), Sat);
    assert_eq!(solver.check_sat_with(&Not(Box::new(Var(sym))), SourceLoc::unknown()), Unsat);
    solver.rollback_transaction(outer);
    assert!(!solver.decls.contains_key(&sym));
}

#[test]
fn smt_savepoint_restores_model_and_check_state() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let sym = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    assert_eq!(solver.check_sat_with(&Var(sym), SourceLoc::unknown()), Sat);
    let other = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let original = solver.stashed_model;
    let outer = solver.start_transaction();
    solver.with_transaction_condition(&Not(Box::new(Var(sym))), |solver| {
        assert_eq!(solver.check_sat_with(&Var(other), SourceLoc::unknown()), Sat);
        let inner_model = solver.stashed_model;
        let inner = solver.start_transaction();
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(other))), SourceLoc::unknown()), Sat);
        assert_ne!(solver.stashed_model, inner_model);
        assert_eq!(solver.check_sat_with(&Bool(false), SourceLoc::unknown()), Unsat);
        assert!(!solver.last_check_sat);
        solver.rollback_transaction(inner);
        assert_eq!(solver.stashed_model, inner_model);
        assert!(solver.last_check_sat);
        let mut model = solver.take_stashed_model().unwrap();
        assert_eq!(model.get_var(other).unwrap().unwrap_exp(), Bool(true));
    });
    assert!(!solver.has_stashed_model());
    solver.rollback_transaction(outer);
    assert_eq!(solver.stashed_model, original);
    assert!(solver.last_check_sat);
    {
        let mut model = solver.take_stashed_model().unwrap();
        assert_eq!(model.get_var(sym).unwrap().unwrap_exp(), Bool(true));
    }
    solver.assert(Bool(true));
    let tx = solver.start_transaction();
    assert_eq!(solver.asserts_since_check, 1);
    solver.check_sat(SourceLoc::unknown());
    solver.rollback_transaction(tx);
    assert_eq!(solver.asserts_since_check, 1);
    assert!(!solver.has_stashed_model());
}

#[test]
fn smt_savepoint_condition_scopes_are_balanced_even_on_unwind() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let flag = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let scopes = || unsafe { Z3_solver_get_num_scopes(ctx.z3_ctx, solver.z3_solver) };
    let baseline = scopes();
    let outer = solver.start_transaction();
    solver.with_transaction_condition(&Var(flag), |solver| {
        let inner = solver.start_transaction();
        solver.with_transaction_condition(&Not(Box::new(Var(flag))), |solver| {
            assert_eq!(solver.check_sat(SourceLoc::unknown()), Unsat);
        });
        assert_eq!(solver.check_sat(SourceLoc::unknown()), Sat);
        solver.rollback_transaction(inner);
    });
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solver.with_transaction_condition(&Bool(false), |solver| {
            assert_eq!(solver.check_sat(SourceLoc::unknown()), Unsat);
            panic!("测试臂提前退出");
        });
    }));
    assert!(panic.is_err());
    assert_eq!(unsafe { Z3_solver_get_num_scopes(ctx.z3_ctx, solver.z3_solver) }, baseline);
    assert_eq!(solver.check_sat_with(&Not(Box::new(Var(flag))), SourceLoc::unknown()), Sat);
    solver.rollback_transaction(outer);
}

#[test]
fn smt_savepoint_register_reads_support_outer_precommit_and_legacy_postcommit() {
    let ctx = Context::new(Config::new());
    for before_commit in [false, true] {
        let mut solver = Solver::<B64>::new(&ctx);
        let tx = solver.start_transaction();
        let sym = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        solver.define_const(Not(Box::new(Var(sym))), SourceLoc::unknown());
        if !before_commit {
            solver.commit_transaction();
        }
        solver.add_event(Event::ReadReg(Name::from_u32(0), vec![], Val::Symbolic(sym)));
        solver.order_transaction_register_reads(tx);
        if before_commit {
            assert!(solver.trace.head.is_empty());
            solver.commit_transaction();
        }
        assert!(matches!(solver.trace.head[1], Event::ReadReg(..)));
        assert!(matches!(solver.trace.head[2], Event::Smt(DefineConst(..), ..)));
    }
}

#[test]
fn smt_savepoint_nested_register_read_ordering_has_no_effect() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    solver.start_transaction();
    let inner = solver.start_transaction();
    solver.add_event(Event::Cycle);
    solver.order_transaction_register_reads(inner);
    assert_eq!(solver.transaction_depth(), 2);
    solver.commit_transaction();
    solver.order_transaction_register_reads(inner);
    assert_eq!(solver.transaction_depth(), 1);
    solver.commit_transaction();
    assert_eq!(solver.transaction_depth(), 0);
    assert!(matches!(solver.trace.head.as_slice(), [Event::Cycle]));
}

#[test]
fn smt_savepoint_enum_registration_survives_nested_rollback_for_replay() {
    let ctx = Context::new(Config::new());
    for inner_commit in [false, true] {
        for outer_commit in [false, true] {
            let mut solver = Solver::<B64>::new(&ctx);
            let outer = solver.start_transaction();
            let inner = solver.start_transaction();
            let enumeration = solver.get_enum(Name::from_u32(5), 2);
            if inner_commit {
                solver.commit_transaction();
            } else {
                solver.rollback_transaction(inner);
            }
            assert!(solver.trace.head.is_empty(), "全局枚举定义也必须等外层结束才发布");
            let speculative = solver.declare_const(Ty::Enum(enumeration), SourceLoc::unknown());
            if outer_commit {
                solver.commit_transaction();
            } else {
                solver.rollback_transaction(outer);
            }
            assert_eq!(solver.decls.contains_key(&speculative), outer_commit);
            assert_eq!(solver.trace.head.iter().filter(|e| matches!(e, Event::Smt(DefineEnum(..), ..))).count(), 1);
            let sym = solver.declare_const(Ty::Enum(enumeration), SourceLoc::unknown());
            solver.assert_eq(Var(sym), Enum(enumeration.first_member()));
            let mut replayed = Solver::from_checkpoint(&ctx, checkpoint(&mut solver));
            assert_eq!(replayed.check_sat(SourceLoc::unknown()), Sat);
        }
    }
}

#[test]
fn smt_savepoint_rejects_out_of_order_rollback() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let outer = solver.start_transaction();
    solver.start_transaction();
    solver.add_event(Event::Cycle);
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| solver.rollback_transaction(outer))).is_err());
    assert_eq!(solver.transaction_depth(), 2);
    solver.commit_transaction();
    solver.commit_transaction();
    assert!(matches!(solver.trace.head.as_slice(), [Event::Cycle]));
}

#[cfg(feature = "smtperf")]
#[test]
fn smt_savepoint_restores_performance_graph_and_attributed_time() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let sym = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let nodes = solver.performance_info.var_nodes.clone();
    let times = solver.performance_info.time_per_location.clone();
    let start = solver.performance_info.start;
    let stats = path_smt_stats();
    let outer = solver.start_transaction();
    solver.start_transaction();
    solver.define_const(Not(Box::new(Var(sym))), SourceLoc::unknown());
    assert_eq!(solver.check_sat_with(&Var(sym), SourceLoc::unknown()), Sat);
    solver.commit_transaction();
    solver.rollback_transaction(outer);
    assert_eq!(solver.performance_info.var_nodes, nodes);
    assert_eq!(solver.performance_info.vars.edge_count(), 0);
    assert_eq!(solver.performance_info.time_per_location, times);
    assert_eq!(solver.performance_info.start, start);
    assert_eq!(path_smt_stats(), stats);
}

#[test]
fn smt_savepoint_legacy_merge_replaces_speculative_register_events() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let reg = Name::from_u32(10);
    let tx = solver.start_transaction();
    solver.trace_call(Name::from_u32(11));
    solver.add_event(Event::ReadReg(reg, vec![], Val::I64(1)));
    solver.add_event(Event::WriteReg(reg, vec![], Val::I64(2)));
    solver.add_event(Event::ReadReg(reg, vec![], Val::I64(1)));
    solver.add_event(Event::Cycle);
    solver.commit_transaction();
    assert_eq!(solver.trace.head.len(), 5, "提交出口保留每一个缓冲事件");
    // 旧执行器在提交后补发两臂合并的读取，整理后再补发合并写入。
    solver.add_event(Event::ReadReg(reg, vec![], Val::I64(1)));
    solver.order_transaction_register_reads(tx);
    solver.add_event(Event::WriteReg(reg, vec![], Val::I64(3)));
    assert_eq!(solver.trace.head.iter().filter(|e| matches!(e, Event::ReadReg(..))).count(), 1);
    assert_eq!(solver.trace.head.iter().filter(|e| matches!(e, Event::WriteReg(..))).count(), 1);
    assert!(matches!(solver.trace.head[0], Event::Function { .. }));
    assert!(matches!(solver.trace.head[1], Event::Cycle));
}

#[test]
fn smt_savepoint_precommit_order_preserves_non_smt_barriers() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let tx = solver.start_transaction();
    let sym = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    solver.add_event(Event::WriteReg(Name::from_u32(0), vec![], Val::Bool(false)));
    solver.define_const(Not(Box::new(Var(sym))), SourceLoc::unknown());
    solver.add_event(Event::ReadReg(Name::from_u32(0), vec![], Val::Symbolic(sym)));
    solver.order_transaction_register_reads(tx);
    solver.commit_transaction();
    assert!(matches!(solver.trace.head[1], Event::WriteReg(..)));
    assert!(matches!(solver.trace.head[2], Event::ReadReg(..)));
    assert!(matches!(solver.trace.head[3], Event::Smt(DefineConst(..), ..)));
}

#[test]
fn smt_savepoint_legacy_merge_retains_repeated_merged_reads() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let tx = solver.start_transaction();
    let reg = Name::from_u32(0);
    solver.add_event(Event::ReadReg(reg, vec![], Val::I64(1)));
    solver.commit_transaction();
    solver.add_event(Event::ReadReg(reg, vec![], Val::I64(1)));
    solver.add_event(Event::ReadReg(reg, vec![], Val::I64(1)));
    solver.order_transaction_register_reads(tx);
    assert_eq!(solver.trace.head.len(), 2);
    assert!(solver.trace.head.iter().all(|event| matches!(event, Event::ReadReg(..))));
}

#[test]
fn smt_savepoint_unwind_rolls_back_unfinished_inner_savepoint() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let outer = solver.start_transaction();
    let scopes = unsafe { Z3_solver_get_num_scopes(ctx.z3_ctx, solver.z3_solver) };
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solver.with_transaction_condition(&Bool(false), |solver| {
            solver.start_transaction();
            solver.cycle_count();
            solver.check_sat(SourceLoc::unknown());
            panic!("内层保存点尚未结束");
        });
    }));
    assert!(panic.is_err());
    assert_eq!(solver.transaction_depth(), 1);
    assert_eq!(solver.get_cycle_count(), 0);
    assert_eq!(unsafe { Z3_solver_get_num_scopes(ctx.z3_ctx, solver.z3_solver) }, scopes);
    assert!(!solver.has_stashed_model());
    solver.rollback_transaction(outer);
}

#[test]
fn smt_savepoint_checkpoint_invalidates_legacy_order_token_without_mutation() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let tx = solver.start_transaction();
    solver.add_event(Event::ReadReg(Name::from_u32(0), vec![], Val::I64(1)));
    solver.commit_transaction();
    checkpoint(&mut solver);
    solver.add_event(Event::ReadReg(Name::from_u32(1), vec![], Val::I64(2)));
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| solver.order_transaction_register_reads(tx))).is_err()
    );
    assert!(matches!(solver.trace.head.as_slice(), [Event::ReadReg(reg, ..)] if *reg == Name::from_u32(1)));
}

#[test]
fn smt_savepoint_legacy_token_remains_send_and_sync() {
    fn require_send_and_sync<T: Send + Sync>() {}
    require_send_and_sync::<SolverTransaction>();
}

#[test]
fn smt_rollback_direct_model_single_and_nested() {
    for nested in [false, true] {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let sym = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        assert_eq!(solver.check_sat_with(&Var(sym), SourceLoc::unknown()), Sat);
        let outer = solver.start_transaction();
        if nested {
            assert_eq!(solver.check_sat_with(&Not(Box::new(Var(sym))), SourceLoc::unknown()), Sat);
            let inner = solver.start_transaction();
            assert_eq!(solver.check_sat_with(&Bool(false), SourceLoc::unknown()), Unsat);
            solver.rollback_transaction(inner);
            assert_eq!(Model::new(&solver).get_var(sym).unwrap().unwrap_exp(), Bool(false));
        }
        assert_eq!(solver.check_sat_with(&Bool(false), SourceLoc::unknown()), Unsat);
        solver.rollback_transaction(outer);
        assert_eq!(Model::new(&solver).get_var(sym).unwrap().unwrap_exp(), Bool(true));
    }
}

#[test]
#[should_panic(expected = "保存点嵌套深度超过上限")]
fn smt_savepoint_depth_limit_panics() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    for depth in 0..=transaction::MAX_TRANSACTION_DEPTH {
        assert_eq!(solver.transaction_depth(), depth);
        solver.start_transaction();
    }
}

// 条件查询使用真实 Z3，同时检查发布后的检查点重放，避免仅验证日志形状。
fn guarded_query(solver: &mut Solver<B64>, g1: Sym, g2: Sym, c: Sym) {
    let all = And(Box::new(Var(g1)), Box::new(Var(g2)));
    assert_eq!(solver.check_sat_with(&And(Box::new(all.clone()), Box::new(Var(c))), SourceLoc::unknown()), Sat);
    assert_eq!(
        solver.check_sat_with(&And(Box::new(all), Box::new(Not(Box::new(Var(c))))), SourceLoc::unknown()),
        Unsat
    );
    for condition in [Not(Box::new(Var(g1))), Not(Box::new(Var(g2)))] {
        assert_eq!(
            solver.check_sat_with(&And(Box::new(condition), Box::new(Not(Box::new(Var(c))))), SourceLoc::unknown()),
            Sat
        );
    }
}

#[test]
fn smt_guarded_nested_assertions_and_event_annotations() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let g1 = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let g2 = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let c = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let scopes = unsafe { Z3_solver_get_num_scopes(ctx.z3_ctx, solver.z3_solver) };
    solver.start_transaction_with_guard(Some(Var(g1)));
    solver.start_transaction_with_guard(Some(Var(g2)));
    solver.assert(Var(c));
    solver.add_event(Event::ReadReg(Name::from_u32(8), vec![], Val::Symbolic(c)));
    assert!(!solver.transaction_invalid());
    assert_eq!(solver.check_sat_with(&Not(Box::new(Var(c))), SourceLoc::unknown()), Unsat);
    assert_eq!(solver.check_sat_deadline(SourceLoc::unknown(), Duration::from_secs(10)), Sat);
    solver.commit_transaction();
    assert_eq!(solver.check_sat_with(&Not(Box::new(Var(g2))), SourceLoc::unknown()), Sat);
    assert_eq!(solver.trace.head.len(), 3);
    solver.commit_transaction();
    assert_eq!(unsafe { Z3_solver_get_num_scopes(ctx.z3_ctx, solver.z3_solver) }, scopes);
    guarded_query(&mut solver, g1, g2, c);
    let expected =
        Or(Box::new(Not(Box::new(Var(g1)))), Box::new(Or(Box::new(Not(Box::new(Var(g2)))), Box::new(Var(c)))));
    assert!(matches!(&solver.trace.head[3], Event::Smt(Assert(exp), ..) if *exp == expected));
    let events = solver.committed_transaction_events();
    assert!(matches!(&events[1], (Some(And(a, b)), Event::ReadReg(..)) if **a == Var(g1) && **b == Var(g2)));
    let mut replayed = Solver::from_checkpoint(&ctx, checkpoint(&mut solver));
    guarded_query(&mut replayed, g1, g2, c);
}

#[test]
fn smt_guarded_assertions_commit_rollback_combinations() {
    let ctx = Context::new(Config::new());
    for outer_commit in [false, true] {
        for inner_commit in [false, true] {
            let mut solver = Solver::<B64>::new(&ctx);
            let g = solver.declare_const(Ty::Bool, SourceLoc::unknown());
            let c = solver.declare_const(Ty::Bool, SourceLoc::unknown());
            let outer = solver.start_transaction_with_guard(Some(Var(g)));
            let inner = solver.start_transaction_with_guard(None);
            solver.assert(Var(c));
            if inner_commit {
                solver.commit_transaction();
            } else {
                solver.rollback_transaction(inner);
            }
            if outer_commit {
                solver.commit_transaction();
            } else {
                solver.rollback_transaction(outer);
            }
            let contrary = And(Box::new(Var(g)), Box::new(Not(Box::new(Var(c)))));
            let expected = if inner_commit && outer_commit { Unsat } else { Sat };
            assert_eq!(solver.check_sat_with(&contrary, SourceLoc::unknown()), expected);
            assert_eq!(solver.check_sat_with(&Not(Box::new(Var(c))), SourceLoc::unknown()), Sat);
            let mut replayed = Solver::from_checkpoint(&ctx, checkpoint(&mut solver));
            assert_eq!(replayed.check_sat_with(&contrary, SourceLoc::unknown()), expected);
        }
    }
}

#[test]
fn smt_guarded_dead_arm_discards_buffer_and_restores_state() {
    let ctx = Context::new(Config::new());
    for nested in [false, true] {
        let mut solver = Solver::<B64>::new(&ctx);
        let g = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        if nested {
            solver.start_transaction();
        }
        solver.start_transaction_with_guard(Some(Var(g)));
        let discarded = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        solver.cycle_count();
        solver.assert(Bool(false));
        assert_eq!(solver.check_sat(SourceLoc::unknown()), Unsat);
        assert_eq!(solver.check_sat_deadline(SourceLoc::unknown(), Duration::from_secs(10)), Unsat);
        solver.commit_dead_transaction();
        assert!(!solver.decls.contains_key(&discarded));
        assert_eq!(solver.get_cycle_count(), 0);
        assert_eq!(solver.check_sat_with(&Var(g), SourceLoc::unknown()), Unsat);
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(g))), SourceLoc::unknown()), Sat);
        if nested {
            assert_eq!(solver.trace.head.len(), 1);
            solver.commit_transaction();
        }
        assert!(solver.committed_transaction_events().iter().all(|(_, event)| !matches!(event, Event::Cycle)));
        assert_eq!(solver.trace.head.len(), 2);
        let mut replayed = Solver::from_checkpoint(&ctx, checkpoint(&mut solver));
        assert_eq!(replayed.check_sat_with(&Var(g), SourceLoc::unknown()), Unsat);
    }
}

#[test]
fn smt_guarded_fresh_product_remains_evaluable_in_merged_value() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let g = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let x = solver.declare_bitvector(8, SourceLoc::unknown());
    solver.assert_eq(Var(x), smtlib::bits64(3, 8));
    solver.start_transaction_with_guard(Some(Var(g)));
    let v = solver.declare_bitvector(8, SourceLoc::unknown());
    solver.assert_eq(Var(v), Bvmul(Box::new(Var(x)), Box::new(Var(x))));
    assert!(!solver.transaction_invalid());
    solver.commit_transaction();
    let merged =
        solver.define_bitvector(Ite(Box::new(Var(g)), Box::new(Var(v)), Box::new(Var(x))), SourceLoc::unknown());
    for replay in [false, true] {
        if replay {
            solver = Solver::from_checkpoint(&ctx, checkpoint(&mut solver));
        }
        for (condition, value) in [(Var(g), 9), (Not(Box::new(Var(g))), 3)] {
            assert_eq!(solver.check_sat_with(&condition, SourceLoc::unknown()), Sat);
            let actual = solver.take_stashed_model().unwrap().get_var(merged).unwrap().unwrap_exp();
            assert_eq!(actual, smtlib::bits64::<Sym>(value, 8));
        }
    }
}

#[test]
fn smt_guarded_legacy_condition_scopes_replay_assertions_under_each_arm() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let g = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let c = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    solver.start_transaction();
    for (condition, value) in [(Var(g), true), (Not(Box::new(Var(g))), false)] {
        solver.with_transaction_condition(&condition, |solver| {
            solver.assert_eq(Var(c), Bool(value));
            assert!(!solver.transaction_invalid());
        });
    }
    solver.commit_transaction();
    assert_eq!(solver.check_sat_with(&Neq(Box::new(Var(c)), Box::new(Var(g))), SourceLoc::unknown()), Unsat);
}

#[test]
fn smt_guarded_read_order_is_deferred_until_outer_publication() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let g = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let outer = solver.start_transaction();
    let inner = solver.start_transaction_with_guard(Some(Var(g)));
    let sym = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    solver.define_const(Not(Box::new(Var(sym))), SourceLoc::unknown());
    solver.add_event(Event::ReadReg(Name::from_u32(0), vec![], Val::Symbolic(sym)));
    solver.order_transaction_register_reads(inner);
    assert!(matches!(solver.transaction_events[1], Event::Smt(DefineConst(..), ..)));
    solver.commit_transaction();
    solver.order_transaction_register_reads(inner);
    solver.order_transaction_register_reads(outer);
    assert!(matches!(solver.transaction_events[1], Event::Smt(DefineConst(..), ..)));
    solver.commit_transaction();
    assert!(matches!(solver.trace.head[2], Event::ReadReg(..)));
    let events = solver.committed_transaction_events();
    assert!(matches!(&events[1], (Some(condition), Event::ReadReg(..)) if *condition == Var(g)));
}

#[test]
fn smt_guarded_query_snapshot_includes_buffer_and_active_conditions() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let g = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    solver.start_transaction_with_guard(Some(Var(g)));
    let c = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    solver.with_transaction_condition(&Var(c), |solver| {
        let v = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        solver.assert(Var(v));
        let mut replayed = Solver::from_checkpoint(&ctx, solver.checkpoint_snapshot());
        for sym in [g, c, v] {
            assert_eq!(replayed.check_sat_with(&Not(Box::new(Var(sym))), SourceLoc::unknown()), Unsat);
        }
    });
    solver.commit_transaction();
}

#[test]
fn smt_guarded_dead_arm_is_conditional_on_parent_and_can_be_rolled_back() {
    let ctx = Context::new(Config::new());
    for commit in [false, true] {
        let mut solver = Solver::<B64>::new(&ctx);
        let outer_guard = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        let inner_guard = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        let outer = solver.start_transaction_with_guard(Some(Var(outer_guard)));
        solver.start_transaction_with_guard(Some(Var(inner_guard)));
        // 也覆盖调用方判死而非当前查询返回 Unsat 的入口。
        solver.commit_dead_transaction();
        if commit {
            solver.commit_transaction();
        } else {
            solver.rollback_transaction(outer);
        }
        assert_eq!(
            solver.check_sat_with(&And(Box::new(Var(outer_guard)), Box::new(Var(inner_guard))), SourceLoc::unknown()),
            if commit { Unsat } else { Sat }
        );
        assert_eq!(
            solver.check_sat_with(
                &And(Box::new(Not(Box::new(Var(outer_guard)))), Box::new(Var(inner_guard))),
                SourceLoc::unknown()
            ),
            Sat
        );
    }
}

#[test]
fn smt_guarded_supported_assert_and_definitions_do_not_invalidate() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let tx = solver.start_transaction();
    let flag = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let alias = solver.define_const(Not(Box::new(Var(flag))), SourceLoc::unknown());
    let fun = solver.fresh();
    solver.add(DeclareFun(fun, vec![Ty::Bool], Ty::Bool));
    solver.add_event(Event::Smt(Assert(Var(alias)), DefAttrs::default(), SourceLoc::unknown()));
    assert!(!solver.transaction_invalid());
    assert_eq!(solver.check_sat_with(&Var(flag), SourceLoc::unknown()), Unsat);
    solver.rollback_transaction(tx);
    assert_eq!(solver.check_sat(SourceLoc::unknown()), Sat);
}

#[test]
fn smt_guarded_unconditional_commit_preserves_cached_model_without_new_constraints() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let flag = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    assert_eq!(solver.check_sat_with(&Var(flag), SourceLoc::unknown()), Sat);
    let original = solver.stashed_model;
    solver.start_transaction();
    solver.commit_transaction();
    assert_eq!(solver.stashed_model, original);
    assert!(solver.last_check_sat);
}

#[test]
fn smt_guarded_commit_preserves_assertion_check_accounting() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    solver.assert(Bool(true));
    solver.start_transaction();
    assert_eq!(solver.check_sat(SourceLoc::unknown()), Sat);
    solver.commit_transaction();
    assert_eq!(solver.asserts_since_check(), 0, "空提交不能恢复已经查询过的旧断言计数");
    solver.start_transaction();
    solver.assert(Bool(true));
    solver.commit_transaction();
    assert_eq!(solver.asserts_since_check(), 1, "重放同一断言不能重复计数");
}

#[test]
fn smt_guarded_read_order_respects_guard_symbol_definition() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let value = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let outer = solver.start_transaction();
    let guard = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    solver.start_transaction_with_guard(Some(Var(guard)));
    solver.add_event(Event::ReadReg(Name::from_u32(0), vec![], Val::Symbolic(value)));
    solver.commit_transaction();
    solver.order_transaction_register_reads(outer);
    solver.commit_transaction();
    assert!(matches!(&solver.trace.head[1], Event::Smt(DeclareConst(sym, ..), ..) if *sym == guard));
    assert!(matches!(&solver.trace.head[2], Event::ReadReg(..)));
}
