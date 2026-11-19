//! 新模式先验证完整前提、回滚及模型缓存，默认测试不更改进程模式。
use super::*;
use crate::bitvector::b64::B64;

fn solver(ctx: &Context) -> Solver<'_, B64> {
    configure_tastic(Tactic::Qfaufbv);
    Solver::new_in_mode(ctx, on_demand::SolverMode::OnDemand)
}

#[test]
fn branch_query_and_model_without_resident_solver() {
    let ctx = Context::new(Config::new());
    let mut s = solver(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_const(Ty::Bool, info);
    s.assert(Exp::Var(x));
    assert!(s.z3_solver.is_null());
    assert!(s.check_sat_with(&Exp::Not(Box::new(Exp::Var(x))), info).is_unsat().unwrap());
    assert!(s.check_sat_with(&Exp::Var(x), info).is_sat().unwrap());
    assert_eq!(Model::new(&s).get_exp(&Exp::Var(x)).unwrap().unwrap_exp(), Exp::Bool(true));
    assert!(s.z3_solver.is_null());
}

#[test]
fn nested_rollback_does_not_leak_guards_or_definitions() {
    let ctx = Context::new(Config::new());
    let mut s = solver(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_const(Ty::Bool, info);
    let tx = s.start_transaction_with_guard(Some(Exp::Var(x)));
    let nested = s.start_transaction();
    s.assert(Exp::Not(Box::new(Exp::Var(x))));
    assert!(s.check_sat(info).is_unsat().unwrap());
    s.rollback_transaction(nested);
    assert!(s.check_sat(info).is_sat().unwrap());
    s.rollback_transaction(tx);
    assert!(s.check_sat_with(&Exp::Not(Box::new(Exp::Var(x))), info).is_sat().unwrap());
    assert!(s.z3_solver.is_null());
}

#[test]
fn cache_hits_and_symbol_rebinding_changes_full_key() {
    let ctx = Context::new(Config::new());
    let mut s = solver(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_const(Ty::Bool, info);
    s.assert(Exp::Var(x));
    let goal = Exp::Not(Box::new(Exp::Var(x)));
    assert!(s.check_sat_with(&goal, info).is_unsat().unwrap());
    let checks = test_query_count();
    assert!(s.check_sat_with(&goal, info).is_unsat().unwrap());
    assert_eq!(test_query_count(), checks);
    s.add(Def::DefineConst(x, Exp::Bool(false)));
    // 已发布断言仍绑定原AST；新目标true不能沿用旧目标的UNSAT。
    assert!(s.check_sat_with(&Exp::Not(Box::new(Exp::Var(x))), info).is_sat().unwrap());
}

#[test]
fn guarded_commit_and_checkpoint_replay_keep_full_constraints() {
    let ctx = Context::new(Config::new());
    let mut s = solver(&ctx);
    let info = SourceLoc::unknown();
    let g = s.declare_const(Ty::Bool, info);
    let x = s.declare_const(Ty::Bool, info);
    s.start_transaction_with_guard(Some(Exp::Var(g)));
    s.assert(Exp::Var(x));
    s.commit_transaction();
    let cp = s.checkpoint_snapshot();
    let mut restored = solver(&ctx);
    restored.replay(cp.num, cp.trace);
    restored.next_var = cp.next_var;
    let bad = Exp::And(Box::new(Exp::Var(g)), Box::new(Exp::Not(Box::new(Exp::Var(x)))));
    assert!(restored.check_sat_with(&bad, info).is_unsat().unwrap());
    assert!(restored.check_sat_with(&Exp::Not(Box::new(Exp::Var(g))), info).is_sat().unwrap());
    assert!(restored.z3_solver.is_null());
}

#[test]
fn public_restore_and_obligation_verifier_use_selected_mode() {
    let name = "smt::on_demand_tests::public_restore_and_obligation_verifier_use_selected_mode";
    if SolverMode::current() != SolverMode::OnDemand {
        let status = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", name, "--skip=isla_solver_mode_on_demand", "--nocapture", "--test-threads=1"])
            .status()
            .unwrap();
        assert!(status.success());
        return;
    }
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let info = SourceLoc::unknown();
    for safe in [false, true] {
        let mut s = Solver::<B64>::new(&ctx);
        let x = s.declare_const(Ty::Bool, info);
        let root = s.start_transaction();
        s.with_deferred_region_queries(|s| {
            s.start_transaction_with_guard(Some(Exp::Var(x)));
            s.defer_assertion(if safe { Exp::Var(x) } else { Exp::Bool(false) }, info);
            s.commit_transaction();
            s.assert(Exp::Bool(false));
            assert_eq!(s.check_deferred_assertions(info), Some(if safe { Unsat } else { Sat }));
        });
        s.rollback_transaction(root);
        let point = s.checkpoint_snapshot();
        let mut restored = Solver::<B64>::from_checkpoint(&ctx, point);
        assert!(restored.on_demand.is_some());
        assert!(restored.z3_solver.is_null());
        assert_eq!(restored.check_sat(info), Sat);
        assert!(restored.z3_solver.is_null());
    }
}

#[test]
fn deferred_and_unknown_queries_keep_common_policy() {
    let ctx = Context::new(Config::new());
    let mut s = solver(&ctx);
    let info = SourceLoc::unknown();
    let flag = s.declare_const(Ty::Bool, info);
    let tx = s.start_transaction();
    let checks = test_query_count();
    s.with_deferred_region_queries(|s| {
        assert_eq!(s.check_sat_with(&Exp::Var(flag), info), Unknown);
        assert_eq!(test_query_count(), checks);
    });
    s.rollback_transaction(tx);
    test_queries::with_results([Some(Z3_L_UNDEF)], || {
        assert!(matches!(s.check_sat_with(&Exp::Var(flag), info), Error(_)));
    });
    assert_eq!(s.check_sat_with(&Exp::Var(flag), info), Sat);
}
