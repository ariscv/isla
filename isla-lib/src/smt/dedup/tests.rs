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
    assert_eq!(s.check_sat_with_for_branch(&Var(x), info, true), Some(Sat));
    assert_eq!(s.check_sat_with_for_branch(&Not(Box::new(Var(x))), info, true), Some(Sat));
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
    if s.check_sat_with_for_branch(&Not(Box::new(Var(x))), info, true).unwrap().is_sat().unwrap() {
        panic!("死臂不应执行原语不变量检查");
    }
    assert_eq!(s.check_sat_with_for_branch(&Var(x), info, true), Some(Sat));
}
#[test]
fn dedup_deferred_branch_discards_structurally_false_condition() {
    configure_tastic(Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    for no_smt in [false, true] {
        let mut config = Config::new();
        config.solver_options.no_smt = no_smt;
        config.solver_options.finite_domain_enumeration = true;
        let context = Context::new(config);
        let mut solver = Solver::<B64>::new(&context);
        let address_matches = solver.declare_const(Ty::Bool, info);
        // 地址是符号值，当前调用的访问宽度为 4 字节。8 字节分支的两臂都为假。
        let wrong_width = solver
            .define_const(Ite(Box::new(Var(address_matches)), Box::new(Bool(false)), Box::new(Bool(false))), info);
        reset_path_smt_stats();
        solver.with_deferred_region_queries(|solver| {
            assert_eq!(solver.check_sat_with_for_branch(&Var(wrong_width), info, true), Some(Unsat));
            assert_eq!(solver.check_sat_with_for_branch(&Not(Box::new(Var(wrong_width))), info, true), None);
            assert_eq!(solver.check_sat_with_for_branch(&Var(address_matches), info, true), None);
        });
        assert_eq!(path_smt_stats().solver_checks, 0, "结构不可能的分支不用求解，其他分支仍待认证");
    }
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
    assert_eq!(s.check_sat_for_arm(info), Some(Sat));
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
    assert_eq!(s.check_sat_for_arm(info), Some(Sat));
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
    assert_eq!(s.check_sat_for_arm(info), Some(Unsat));
    s.rollback_transaction(tx);
    assert_eq!(s.check_sat_with_for_branch(&Not(Box::new(Var(x))), info, true), Some(Sat));
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
    assert_eq!(s.check_sat_with_for_branch(&Var(x), info, true), Some(Unsat));
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
    assert_eq!(s.check_sat_for_arm(info), Some(Unsat));
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
    assert_eq!(s.check_sat_for_arm(info), Some(Sat));
    s.commit_transaction();
    assert!(!s.knowledge.sat, "带约束提交不能沿用旧SAT标记");
    // 后续片段选择继续路径，必须保留前段已提交的条件约束。
    s.assert(Var(continuing));
    both(&mut s, choice);
    let tx = s.start_transaction_with_guard(Some(Var(choice)));
    s.assert(Eq(Box::new(Var(data)), Box::new(Bits64(B64::new(1, 8)))));
    assert_eq!(s.check_sat_for_arm(info), Some(Unsat), "跨段矛盾约束必须剪掉死臂");
    s.rollback_transaction(tx);
    assert_eq!(s.check_sat_with_for_branch(&Not(Box::new(Var(choice))), info, true), Some(Sat));
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
        assert_eq!(
            s.check_sat_with_for_bool(&Var(x), info),
            Unproven(SmtError::DeferredQuery { source_loc: info, purpose: "boolean_proof" })
        );
        assert_eq!(
            s.check_sat_with_for_range(&Var(x), info),
            Unproven(SmtError::DeferredQuery { source_loc: info, purpose: "range_proof" })
        );
        assert_eq!(
            s.check_sat(info),
            Unproven(SmtError::DeferredQuery { source_loc: info, purpose: "model_or_general" })
        );
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
            assert_eq!(result, Some(if safe { Unsat } else { Sat }));
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
        assert_eq!(s.check_deferred_assertions(info), Some(Unsat));
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
        let all = s.deferred_assertions.as_ref().unwrap().arm.obligations.clone();
        s.deferred_assertions.as_mut().unwrap().arm.obligations = vec![all[1].clone()];
        assert_eq!(s.check_deferred_assertions(info), Some(Unsat), "前序断言成立后同一断言不可失败");
        s.deferred_assertions.as_mut().unwrap().arm.obligations = all;
        assert_eq!(s.check_deferred_assertions(info), Some(Sat), "第一条可行错误不能被后序假设抹掉");
        s.assert(Bool(false));
        assert_eq!(s.check_deferred_assertions(info), Some(Sat), "后续约束/退出域不能裁掉前面的错误");
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
        assert_eq!(s.check_deferred_assertions(info), Some(Unsat));
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
        assert_eq!(s.check_deferred_assertions(info), Some(Unsat));
        s.rollback_transaction(inner);
        s.rollback_transaction(outer);
        s.assert_region_exit(Var(x));
        s.defer_assertion(Var(x), info);
        assert_eq!(s.check_deferred_assertions(info), Some(Sat), "正常退出域即便在前面也不能掩盖错误");
    });
    s.rollback_transaction(root);
}

#[test]
fn structural_integer_narrowing_needs_no_query_or_obligation() {
    configure_tastic(Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    for no_smt in [false, true] {
        let mut cfg = Config::new();
        cfg.solver_options.no_smt = no_smt;
        let ctx = Context::new(cfg);
        let mut s = Solver::<B64>::new(&ctx);
        let raw = s.declare_const(Ty::BitVec(128), info);
        let bits = s.declare_const(Ty::BitVec(5), info);
        let widened = s.define_const(ZeroExtend(123, Box::new(Var(bits))), info);
        let signed = s.define_const(SignExtend(123, Box::new(Var(bits))), info);
        let extracted = s.define_const(Extract(63, 0, Box::new(Var(raw))), info);
        let sign_extended = s.define_const(SignExtend(64, Box::new(Var(extracted))), info);
        let sub = s.define_const(Bvsub(Box::new(Var(widened)), Box::new(bits64(1, 128))), info);
        let add = s.define_const(Bvadd(Box::new(Var(sub)), Box::new(Var(signed))), info);
        let sub_pair = s.define_const(Bvsub(Box::new(Var(signed)), Box::new(Var(sub))), info);
        let root = s.start_transaction();
        s.with_deferred_region_queries(|s| {
            let narrow = crate::primop::unary_primops()["%i->%i64"];
            reset_path_smt_stats();
            for (index, value) in [sub, add, sub_pair, sign_extended].into_iter().enumerate() {
                let ast = s.translate_exp(&Var(value));
                assert!(
                    s.structural_fits_i64(value),
                    "第 {index} 项应可结构证明，表达式 {}",
                    unsafe { CStr::from_ptr(Z3_ast_to_string(ctx.z3_ctx, ast.z3_ast)) }.to_string_lossy()
                );
                assert!(matches!(narrow(Val::Symbolic(value), s, info), Ok(Val::Symbolic(_))));
            }
            assert_eq!(path_smt_stats().calls, 0);
            assert!(s.deferred_assertions.as_ref().unwrap().arm.obligations.is_empty());
        });
        s.rollback_transaction(root);
    }
}

#[test]
fn region_util_defer_range_obligation_preserves_error_domain() {
    const CHILD: &str = "REGION_UTIL_RANGE_TEST_CHILD";
    let Ok(mode) = std::env::var(CHILD) else {
        for mode in ["disabled", "smt", "no_smt"] {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "smt::dedup::tests::region_util_defer_range_obligation_preserves_error_domain",
                    "--nocapture",
                ])
                .env(CHILD, mode)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }
        return;
    };
    let enabled = mode != "disabled";
    let no_smt = mode == "no_smt";
    if !enabled {
        crate::config::RegionOptions { defer_range_proofs: false, ..Default::default() }.configure();
    }
    configure_tastic(Tactic::Qfaufbv);
    let mut config = Config::new();
    config.solver_options.no_smt = no_smt;
    let ctx = Context::new(config);
    let info = SourceLoc::unknown();
    for safe in [false, true] {
        let mut s = Solver::<B64>::new(&ctx);
        let wide = s.declare_const(Ty::BitVec(128), info);
        let value = if safe { 5 } else { 1 << 63 };
        s.assert(Eq(Box::new(Var(wide)), Box::new(bits64(value, 128))));
        let root = s.start_transaction();
        let narrow = crate::primop::unary_primops()["%i->%i64"];
        s.with_deferred_region_queries(|s| {
            reset_path_smt_stats();
            let result = narrow(Val::Symbolic(wide), s, info);
            if enabled || safe {
                assert!(matches!(result, Ok(Val::Symbolic(_))));
            } else {
                assert!(matches!(result, Err(ExecError::Unproven(SmtError::DeferredQuery { .. }))));
            }
            assert_eq!(s.deferred_assertions.as_ref().unwrap().arm.obligations.len(), usize::from(enabled && !safe));
            assert_eq!(path_smt_stats().calls, 0, "出口前不查 SMT");
            s.assert_region_exit(Bool(false));
            assert_eq!(
                s.check_deferred_assertions(info),
                if no_smt { None } else { Some(if enabled && !safe { Sat } else { Unsat }) },
                "正常退出域不得掩盖越界输入"
            );
        });
        s.rollback_transaction(root);
        if !no_smt {
            assert_eq!(s.check_sat(info), Sat, "回滚应恢复原到达域");
            let result = narrow(Val::Symbolic(wide), &mut s, info);
            if safe {
                assert!(result.is_ok());
            } else {
                assert!(matches!(result, Err(ExecError::Overflow)));
            }
        }
    }
}

#[test]
fn no_smt_stage1_switches_are_independent_and_never_certify_branches() {
    configure_tastic(Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    for branches in [false, true] {
        for booleans in [false, true] {
            let mut cfg = Config::new();
            cfg.solver_options =
                SolverOptions { skip_branch_checks: branches, skip_bool_proofs: booleans, ..Default::default() };
            let ctx = Context::new(cfg);
            let mut s = Solver::<B64>::new(&ctx);
            let x = s.declare_const(Ty::Bool, info);
            s.assert(Var(x));
            reset_path_smt_stats();
            assert_eq!(
                s.check_sat_with_for_branch(&Not(Box::new(Var(x))), info, false),
                if branches { None } else { Some(Unsat) }
            );
            if branches {
                assert_eq!(path_smt_stats().calls, 0);
                s.note_jump_results(x, true, true);
                assert!(s.knowledge.both.is_none());
                assert!(!s.knowledge.sat);
            }
            reset_path_smt_stats();
            assert_eq!(
                s.check_sat_with_for_bool(&Not(Box::new(Var(x))), info),
                if booleans {
                    Unproven(SmtError::DeferredQuery { source_loc: info, purpose: "boolean_proof" })
                } else {
                    Unsat
                }
            );
            if booleans {
                assert_eq!(path_smt_stats().calls, 0);
            }
            assert_eq!(s.check_sat_with_for_range(&Not(Box::new(Var(x))), info), Unsat);
            assert_eq!(s.check_sat_with(&Not(Box::new(Var(x))), info), Unsat);
            s.with_deferred_region_queries(|s| {
                assert_eq!(
                    s.check_sat_with_for_range(&Var(x), info),
                    Unproven(SmtError::DeferredQuery { source_loc: info, purpose: "range_proof" })
                );
            });
        }
    }
}

#[test]
fn no_smt_global_zero_checks_and_explicit_safety_assumptions() {
    configure_tastic(Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    let mut cfg = Config::new();
    cfg.solver_options.no_smt = true;
    let ctx = Context::new(cfg);
    let mut s = Solver::<B64>::new(&ctx);
    let x = s.declare_const(Ty::BitVec(5), info);
    let index = s.define_const(ZeroExtend(123, Box::new(Var(x))), info);
    reset_path_smt_stats();
    assert!(s.no_smt_safety(&Bvult(Box::new(Var(index)), Box::new(bits64(32, 128))), info));
    let unknown = s.declare_const(Ty::Bool, info);
    assert!(s.no_smt_safety(&Var(unknown), info));
    assert_eq!(
        s.check_sat_with_for_bool(&Var(unknown), info),
        Unproven(SmtError::DeferredQuery { source_loc: info, purpose: "boolean_proof" })
    );
    assert!(matches!(s.check_sat(info), Error(SmtError::NoSmt { .. })));
    assert_eq!(path_smt_stats().calls, 0);
    assert!(!s.knowledge.sat);
    assert!(!s.has_stashed_model());
}

#[test]
fn no_smt_third_mode_only_permits_boolean_proofs_even_in_defer() {
    configure_tastic(Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    let mut cfg = Config::new();
    cfg.solver_options.no_smt = true;
    cfg.solver_options.keep_bool_proofs = true;
    let ctx = Context::new(cfg);
    let mut s = Solver::<B64>::new(&ctx);
    let x = s.declare_const(Ty::Bool, info);
    s.assert(Var(x));
    s.with_deferred_region_queries(|s| {
        reset_path_smt_stats();
        assert_eq!(s.check_sat_with_for_bool(&Not(Box::new(Var(x))), info), Unsat);
        assert!(path_smt_stats().calls > 0);
        reset_path_smt_stats();
        assert_eq!(s.check_sat_with_for_branch(&Var(x), info, true), None);
        assert!(matches!(s.check_sat(info), Error(SmtError::NoSmt { .. })));
        assert!(matches!(s.check_sat_with_for_range(&Var(x), info), Error(SmtError::NoSmt { .. })));
        assert_eq!(path_smt_stats().calls, 0);
    });
}

#[test]
fn no_smt_structural_ranges_respect_wraparound() {
    configure_tastic(Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let b = s.declare_const(Ty::Bool, info);
    let x = s.define_const(Ite(Box::new(Var(b)), Box::new(bits64(3, 8)), Box::new(bits64(7, 8))), info);
    assert_eq!(s.structural_bool(&Bvult(Box::new(Var(x)), Box::new(bits64(8, 8)))), Some(true));
    let wrapped = s.define_const(Bvadd(Box::new(Var(x)), Box::new(bits64(250, 8))), info);
    assert_ne!(s.structural_bool(&Bvult(Box::new(Var(wrapped)), Box::new(bits64(8, 8)))), Some(true));
}

// 两种断言策略在未知符号条件上都保留成功条件；无SMT还必须留下未验义务。
#[test]
fn unify_characterization_assertions_and_mandatory_queries() {
    configure_tastic(Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    for no_smt in [false, true] {
        for optimistic in [false, true] {
            let mut cfg = Config::new();
            cfg.solver_options.no_smt = no_smt;
            let ctx = Context::new(cfg);
            let mut s = Solver::<B64>::new(&ctx);
            let x = s.declare_const(Ty::Bool, info);
            let root = s.start_transaction();
            reset_path_smt_stats();
            s.with_deferred_region_queries(|s| {
                let value = Val::Symbolic(x);
                let result = if optimistic {
                    crate::primop::optimistic_assert(value, Val::Unit, s, info)
                } else {
                    crate::primop::pessimistic_assert(value, Val::Unit, s, info)
                };
                assert!(matches!(result, Ok(Val::Unit)));
                assert_eq!(s.deferred_assertions.as_ref().unwrap().arm.obligations.len(), 1);
                assert_eq!(s.check_sat_with_for_branch(&Var(x), info, true), None);
                assert_eq!(
                    s.check_sat_with_for_bool(&Var(x), info),
                    Unproven(SmtError::DeferredQuery { source_loc: info, purpose: "boolean_proof" })
                );
                if no_smt {
                    assert!(matches!(s.check_sat(info), Error(SmtError::NoSmt { .. })));
                    assert!(matches!(s.check_sat_with_for_range(&Var(x), info), Error(SmtError::NoSmt { .. })));
                } else {
                    assert_eq!(
                        s.check_sat(info),
                        Unproven(SmtError::DeferredQuery { source_loc: info, purpose: "model_or_general" })
                    );
                    assert_eq!(
                        s.check_sat_with_for_range(&Var(x), info),
                        Unproven(SmtError::DeferredQuery { source_loc: info, purpose: "range_proof" })
                    );
                }
                assert_eq!(path_smt_stats().calls, 0);
                assert!(!s.knowledge.sat);
                assert!(!s.has_stashed_model());
            });
            s.rollback_transaction(root);
        }
    }
}

#[test]
fn unify_characterization_unknown_branch_is_a_guarded_candidate() {
    configure_tastic(Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    for no_smt in [false, true] {
        let mut cfg = Config::new();
        cfg.solver_options.no_smt = no_smt;
        let ctx = Context::new(cfg);
        let mut s = Solver::<B64>::new(&ctx);
        let x = s.declare_const(Ty::Bool, info);
        // 这里依赖路径断言，单看分支表达式无法证明为假。
        s.assert(Not(Box::new(Var(x))));
        reset_path_smt_stats();
        assert_eq!(s.check_sat_with_for_branch(&Var(x), info, false), if no_smt { None } else { Some(Unsat) });
        if no_smt {
            assert_eq!(path_smt_stats().calls, 0);
            s.note_jump_results(x, true, true);
            assert!(s.knowledge.both.is_none());
        }
    }
}

// 未查询的候选与实际Unknown必须可区分，实际Unknown不能被认证或当作死臂。
#[test]
fn unify_optional_candidate_checks_keep_real_unknown_and_obligations() {
    configure_tastic(Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    for no_smt in [false, true] {
        let mut cfg = Config::new();
        cfg.solver_options.no_smt = no_smt;
        let ctx = Context::new(cfg);
        let mut s = Solver::<B64>::new(&ctx);
        let x = s.declare_const(Ty::Bool, info);
        s.assert(Var(x));
        reset_path_smt_stats();
        assert_eq!(s.check_candidate_sat_with(&Not(Box::new(Var(x))), info), if no_smt { None } else { Some(Unsat) });
        if no_smt {
            assert_eq!(path_smt_stats().calls, 0);
            assert!(!s.has_stashed_model());
        }
        let root = s.start_transaction();
        s.with_deferred_region_queries(|s| {
            s.defer_assertion(Var(x), info);
            reset_path_smt_stats();
            assert_eq!(
                s.check_candidate_sat(info),
                if no_smt {
                    None
                } else {
                    Some(Unproven(SmtError::DeferredQuery { source_loc: info, purpose: "model_or_general" }))
                }
            );
            assert_eq!(
                s.check_candidate_sat_with(&Var(x), info),
                if no_smt {
                    None
                } else {
                    Some(Unproven(SmtError::DeferredQuery { source_loc: info, purpose: "general" }))
                }
            );
            assert_eq!(s.check_sat_for_arm(info), None);
            assert_eq!(path_smt_stats().calls, 0);
            assert_eq!(s.check_deferred_assertions(info), if no_smt { None } else { Some(Unsat) });
            assert_eq!(s.deferred_assertions.as_ref().unwrap().arm.obligations.len(), 1, "未验证义务不能丢失");
        });
        s.rollback_transaction(root);
    }
}

#[test]
fn entry_branch_retained_models_check_both_polarities_and_new_assertions() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_const(Ty::Bool, info);
    let y = s.declare_const(Ty::Bool, info);
    let pos = Var(x);
    let neg = Not(Box::new(Var(x)));
    for side in [&pos, &neg] {
        assert_eq!(s.check_sat_with(&And(Box::new(side.clone()), Box::new(Var(y))), info), Sat);
    }
    s.add(Def::Assert(Var(y)));
    reset_path_smt_stats();
    for (side, expected) in [(&pos, true), (&neg, false)] {
        assert_eq!(s.check_sat_with_for_branch(side, info, false), Some(Sat));
        assert!(matches!(Model::new(&s).get_exp(&pos), Ok(ModelVal::Exp(Bool(v))) if v == expected));
        assert!(matches!(Model::new(&s).get_exp(&Var(y)), Ok(ModelVal::Exp(Bool(true)))));
    }
    assert_eq!(path_smt_stats().solver_checks, 0, "旧见证满足完整前提时入口不再重复原生求解");
    s.add(Def::Assert(neg.clone()));
    assert_eq!(s.check_sat_with_for_branch(&pos, info, false), Some(Unsat), "旧真侧模型已经违反新断言");
    assert_eq!(s.check_sat_with_for_branch(&neg, info, false), Some(Sat));
}
