//! 查询去重的红绿回归；普通check_sat继续生成模型。
use super::*;
use crate::bitvector::b64::B64;
use smtlib::Exp::*;

fn both(s: &mut Solver<B64>, x: Sym) {
    let info = SourceLoc::unknown();
    assert_eq!(s.check_sat_with(&Var(x), info), Sat);
    assert_eq!(s.check_sat_with(&Not(Box::new(Var(x))), info), Sat);
    s.note_bool_proof(x, true);
}
#[test]
fn dedup_both_sat_branch_has_no_query_or_model_eval() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_const(Ty::Bool, info);
    both(&mut s, x);
    s.define_const(Bool(true), info);
    reset_path_smt_stats();
    assert_eq!(s.check_sat_with_for_branch(&Var(x), info, true), Sat);
    assert_eq!(s.check_sat_with_for_branch(&Not(Box::new(Var(x))), info, true), Sat);
    assert_eq!(path_smt_stats().calls, 0, "双侧已证明，同断言版本不应重新查或取模型");
}
#[test]
fn dedup_assertion_prunes_dead_branch_before_poison() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_const(Ty::Bool, info);
    both(&mut s, x);
    s.assert(Var(x));
    if s.check_sat_with_for_branch(&Not(Box::new(Var(x))), info, true).is_sat().unwrap() {
        panic!("死臂不应执行原语不变量检查");
    }
    assert_eq!(s.check_sat_with_for_branch(&Var(x), info, true), Sat);
}
#[test]
fn dedup_definition_arm_close_does_not_require_model() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_const(Ty::Bool, info);
    both(&mut s, x);
    let tx = s.start_transaction_with_guard(Some(Var(x)));
    s.define_const(Bool(true), info);
    assert!(!s.has_stashed_model());
    reset_path_smt_stats();
    assert_eq!(s.check_sat_for_arm(info), Sat);
    assert_eq!(path_smt_stats().calls, 0);
    assert!(!s.has_stashed_model(), "已知SAT不等于持有模型");
    assert_eq!(s.check_sat(info), Sat);
    assert!(s.has_stashed_model(), "普通调用仍需生成模型");
    s.rollback_transaction(tx);
}
#[test]
fn dedup_nested_definition_commit_preserves_sat() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_const(Ty::Bool, info);
    let y = s.declare_const(Ty::Bool, info);
    both(&mut s, x);
    let tx = s.start_transaction_with_guard(Some(Var(x)));
    both(&mut s, y);
    s.start_transaction_with_guard(Some(Var(y)));
    s.define_const(Bool(false), info);
    s.commit_transaction();
    assert!(!s.has_stashed_model());
    reset_path_smt_stats();
    assert_eq!(s.check_sat_for_arm(info), Sat);
    assert_eq!(path_smt_stats().calls, 0);
    s.rollback_transaction(tx);
}
#[test]
fn dedup_nested_assertion_commit_clears_sat_and_prunes() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_const(Ty::Bool, info);
    both(&mut s, x);
    let tx = s.start_transaction_with_guard(Some(Var(x)));
    s.start_transaction_with_guard(None);
    s.assert(Bool(false));
    s.commit_transaction();
    assert!(!s.knowledge.sat);
    assert_eq!(s.check_sat_for_arm(info), Unsat);
    s.rollback_transaction(tx);
    assert_eq!(s.check_sat_with_for_branch(&Not(Box::new(Var(x))), info, true), Sat);
}
#[test]
fn dedup_unknown_proof_and_rebinding_never_reuse_both() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_const(Ty::Bool, info);
    s.note_bool_proof(x, false);
    assert!(s.knowledge.both.is_none());
    both(&mut s, x);
    s.add(Def::DefineConst(x, Bool(false)));
    assert_eq!(s.check_sat_with_for_branch(&Var(x), info, true), Unsat);
}
#[test]
fn dedup_temporary_condition_constraint_clears_parent_sat() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_const(Ty::Bool, info);
    both(&mut s, x);
    let tx = s.start_transaction();
    s.with_transaction_condition(&Bool(true), |s| s.assert(Bool(false)));
    assert!(!s.knowledge.sat);
    assert_eq!(s.check_sat_for_arm(info), Unsat);
    s.rollback_transaction(tx);
}

#[test]
fn dedup_continuation_cannot_reuse_sat_across_guarded_constraints() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let continuing = s.declare_const(Ty::Bool, info);
    let choice = s.declare_const(Ty::Bool, info);
    let data = s.declare_const(Ty::BitVec(8), info);
    both(&mut s, continuing);
    s.start_transaction_with_guard(Some(Var(continuing)));
    s.assert(Eq(Box::new(Var(data)), Box::new(Bits64(B64::new(0, 8)))));
    assert_eq!(s.check_sat_for_arm(info), Sat);
    s.commit_transaction();
    assert!(!s.knowledge.sat, "带约束提交不能沿用旧SAT标记");
    // 后续片段选择继续路径，必须保留前段已提交的条件约束。
    s.assert(Var(continuing));
    both(&mut s, choice);
    let tx = s.start_transaction_with_guard(Some(Var(choice)));
    s.assert(Eq(Box::new(Var(data)), Box::new(Bits64(B64::new(1, 8)))));
    assert_eq!(s.check_sat_for_arm(info), Unsat, "跨段矛盾约束必须剪掉死臂");
    s.rollback_transaction(tx);
    assert_eq!(s.check_sat_with_for_branch(&Not(Box::new(Var(choice))), info, true), Sat);
    assert_eq!(s.check_sat(info), Sat);
    assert!(s.has_stashed_model(), "继续执行后普通取值仍能获得模型");
}

#[test]
fn deferred_exit_queries_never_publish_sat_and_restore_after_error() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_const(Ty::Bool, info);
    s.assert(Var(x));
    reset_path_smt_stats();
    s.with_deferred_region_queries(|s| {
        assert!(s.region_queries_deferred());
        assert_eq!(s.check_sat_with_for_bool(&Var(x), info), Unknown);
        assert_eq!(s.check_sat_with_for_range(&Var(x), info), Unknown);
        assert_eq!(s.check_sat(info), Unknown);
        s.note_jump_results(x, true, true);
        assert!(s.knowledge.both.is_none());
        assert!(!s.knowledge.sat);
    });
    assert_eq!(path_smt_stats().calls, 0);
    assert!(!s.region_queries_deferred());
    assert_eq!(s.check_sat_with(&Not(Box::new(Var(x))), info), Unsat);
    let error = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        s.with_deferred_region_queries(|_| panic!("检查作用域恢复"));
    }));
    assert!(error.is_err());
    assert!(!s.region_queries_deferred());
    assert_eq!(s.check_sat(info), Sat);
}

#[test]
fn deferred_assert_obligation_uses_entry_domain_not_assumed_success() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let info = SourceLoc::unknown();
    for safe in [false, true] {
        let mut s = Solver::<B64>::new(&ctx);
        let x = s.declare_const(Ty::Bool, info);
        let root = s.start_transaction();
        s.with_deferred_region_queries(|s| {
            let arm = s.start_transaction_with_guard(Some(Var(x)));
            let c = if safe { Var(x) } else { Bool(false) };
            s.defer_assertion(c, info);
            s.commit_transaction();
            // 后续正常域为空，也不能掩盖入口域下可行的错误。
            s.assert(Bool(false));
            let result = s.check_deferred_assertions(info);
            assert_eq!(result, if safe { Unsat } else { Sat });
            let _ = arm;
        });
        s.rollback_transaction(root);
        assert_eq!(s.check_sat(info), Sat);
    }
}

#[test]
fn deferred_assert_obligation_respects_entry_constraints_and_nested_rollback() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let info = SourceLoc::unknown();
    let mut s = Solver::<B64>::new(&ctx);
    let x = s.declare_const(Ty::Bool, info);
    s.assert(Var(x));
    let root = s.start_transaction();
    s.with_deferred_region_queries(|s| {
        s.defer_assertion(Var(x), info);
        let tx = s.start_transaction_with_guard(Some(Var(x)));
        // 故意引用本层新符号；回滚后不得留下悬空义务。
        let y = s.declare_const(Ty::Bool, info);
        s.defer_assertion(Var(y), info);
        s.rollback_transaction(tx);
        assert_eq!(s.check_deferred_assertions(info), Unsat);
    });
    s.rollback_transaction(root);
}

#[test]
fn obligation_domain_predecessor_proves_later_but_keeps_first_error() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_const(Ty::Bool, info);
    let root = s.start_transaction();
    s.with_deferred_region_queries(|s| {
        s.defer_assertion(Var(x), info);
        s.defer_assertion(Var(x), info);
        let all = s.deferred_assertions.as_ref().unwrap().obligations.clone();
        s.deferred_assertions.as_mut().unwrap().obligations = vec![all[1].clone()];
        assert_eq!(s.check_deferred_assertions(info), Unsat, "前序断言成立后同一断言不可失败");
        s.deferred_assertions.as_mut().unwrap().obligations = all;
        assert_eq!(s.check_deferred_assertions(info), Sat, "第一条可行错误不能被后序假设抹掉");
        s.assert(Bool(false));
        assert_eq!(s.check_deferred_assertions(info), Sat, "后续约束/退出域不能裁掉前面的错误");
    });
    s.rollback_transaction(root);
}

#[test]
fn obligation_domain_initial_type_fact_and_outer_guard_are_retained() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_const(Ty::Bool, info);
    let root = s.start_transaction();
    s.with_deferred_region_queries(|s| {
        s.assert_region_input_fact(Var(x));
        s.defer_assertion(Var(x), info);
        assert_eq!(s.check_deferred_assertions(info), Unsat);
    });
    s.rollback_transaction(root);
}

#[test]
fn obligation_domain_excludes_even_earlier_normal_exit_and_keeps_outer_guard() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_const(Ty::Bool, info);
    let root = s.start_transaction();
    s.with_deferred_region_queries(|s| {
        let outer = s.start_transaction_with_guard(Some(Var(x)));
        let inner = s.start_transaction_with_guard(Some(Not(Box::new(Var(x)))));
        s.defer_assertion(Bool(false), info);
        assert_eq!(s.check_deferred_assertions(info), Unsat);
        s.rollback_transaction(inner);
        s.rollback_transaction(outer);
        s.assert_region_exit(Var(x));
        s.defer_assertion(Var(x), info);
        assert_eq!(s.check_deferred_assertions(info), Sat, "正常退出域即便在前面也不能掩盖错误");
    });
    s.rollback_transaction(root);
}
