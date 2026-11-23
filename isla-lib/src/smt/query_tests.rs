//! 单次查询的调用边界、事务条件、模型及显式增量范围。
use super::*;
use smtlib::Exp::*;

fn in_default_process(name: &str, test: impl FnOnce()) {
    const CHILD: &str = "ISLA_SINGLE_QUERY_TEST_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", &format!("smt::query_tests::{name}"), "--nocapture"])
            .env(CHILD, "1")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        return;
    }
    configure_tastic(Tactic::Default);
    test();
}

fn floating_prefix(solver: &mut Solver<B64>) {
    let value = solver.declare_bitvector(32, SourceLoc::unknown());
    let float = FPUnary(smtlib::FPUnary::FromIEEE(8, 24), Box::new(Var(value)));
    solver.assert(Not(Box::new(FPUnary(smtlib::FPUnary::IsNaN, Box::new(float)))));
}

#[test]
fn default_bitvector_queries_keep_original_backend() {
    in_default_process("default_bitvector_queries_keep_original_backend", || {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let byte = solver.declare_bitvector(8, info);
        let original = solver.z3_solver as usize;
        assert_eq!(solver.check_sat_with(&Eq(Box::new(Var(byte)), Box::new(smtlib::bits64(3, 8))), info), Sat);
        assert_eq!(z3_timeout::last_solver_query(), (original, 1));
        let tx = solver.start_transaction();
        floating_prefix(&mut solver);
        assert_eq!(solver.check_sat(info), Sat);
        assert_ne!(z3_timeout::last_solver_query().0, original);
        solver.rollback_transaction(tx);
        let calls = z3_timeout::test_query_count();
        assert_eq!(solver.check_sat(info), Sat);
        assert_eq!(z3_timeout::test_query_count(), calls, "回滚恢复的有效模型不应重新求解");
        floating_prefix(&mut solver);
        assert_eq!(solver.check_sat(info), Sat);
        assert_ne!(z3_timeout::last_solver_query().0, original);
    });
}

#[test]
fn default_queries_use_fresh_plain_check() {
    in_default_process("default_queries_use_fresh_plain_check", || {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        floating_prefix(&mut solver);
        let info = SourceLoc::unknown();
        let bit = solver.declare_const(smtlib::Ty::Bool, info);
        let original = solver.z3_solver as usize;
        let before = solver.trace().to_vec().len();
        assert_eq!(solver.check_sat_with(&Var(bit), info), Sat);
        let (queried, assumptions) = z3_timeout::last_solver_query();
        assert_ne!(queried, original, "普通default应查询独立solver");
        assert_eq!(assumptions, 0, "临时条件应断言到新solver，不触发增量假设查询");
        assert_eq!(solver.trace().to_vec().len(), before);
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(bit))), info), Sat);
        assert_eq!(solver.check_sat(info), Sat);
        assert_ne!(z3_timeout::last_solver_query().0, original);
        assert_eq!(solver.check_sat_deadline(info, Duration::from_secs(5)), Sat);
        assert_ne!(z3_timeout::last_solver_query().0, original);
    });
}

#[test]
fn default_snapshot_preserves_nested_conditions_and_cached_model() {
    in_default_process("default_snapshot_preserves_nested_conditions_and_cached_model", || {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        floating_prefix(&mut solver);
        let info = SourceLoc::unknown();
        let fixed = solver.declare_const(smtlib::Ty::Bool, info);
        let guard = solver.declare_const(smtlib::Ty::Bool, info);
        let nested = solver.declare_const(smtlib::Ty::Bool, info);
        let buffered = solver.declare_const(smtlib::Ty::Bool, info);
        solver.assert(Var(fixed));
        let outer = solver.start_transaction_with_guard(Some(Var(guard)));
        solver.assert(Var(buffered));
        let inner = solver.start_transaction_with_guard(Some(Var(nested)));
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(buffered))), info), Unsat);
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(fixed))), info), Unsat);
        assert_eq!(solver.check_sat(info), Sat);
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(guard))), info), Unsat);
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(nested))), info), Unsat);
        let mut model = Model::new(&solver);
        for symbol in [fixed, guard, nested, buffered] {
            assert_eq!(model.get_var(symbol).unwrap().unwrap_exp(), Bool(true));
        }
        drop(model);
        solver.rollback_transaction(inner);
        solver.rollback_transaction(outer);
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(buffered))), info), Sat);
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(guard))), info), Sat);
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(nested))), info), Sat);
    });
}

#[test]
fn default_count_scope_keeps_incremental_backend_and_restores_it() {
    in_default_process("default_count_scope_keeps_incremental_backend_and_restores_it", || {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        floating_prefix(&mut solver);
        let info = SourceLoc::unknown();
        let bit = solver.declare_const(smtlib::Ty::Bool, info);
        let original = solver.z3_solver;
        let tx = solver.start_transaction();
        solver.with_incremental_checks(|solver| {
            let incremental = solver.z3_solver as usize;
            for condition in [Var(bit), Not(Box::new(Var(bit)))] {
                assert_eq!(solver.check_sat_with(&condition, info), Sat);
                assert_eq!(z3_timeout::last_solver_query(), (incremental, 1));
            }
        });
        assert_eq!(solver.z3_solver, original);
        let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            solver.with_incremental_checks(|solver| {
                assert_eq!(solver.check_sat_with(&Var(bit), info), Sat);
                panic!("验证查询范围展开后的恢复");
            });
        }));
        assert!(unwind.is_err());
        assert_eq!(solver.z3_solver, original);
        solver.rollback_transaction(tx);
        assert_eq!(solver.check_sat_with(&Var(bit), info), Sat);
        assert_ne!(z3_timeout::last_solver_query().0, original as usize);
        assert_eq!(z3_timeout::last_solver_query().1, 0);
    });
}

#[test]
fn default_snapshot_keeps_context_configuration_and_explicit_seed() {
    in_default_process("default_snapshot_keeps_context_configuration_and_explicit_seed", || {
        let context = Context::new(Config::new());
        let info = SourceLoc::unknown();
        let mut seeded = Solver::<B64>::new_seeded(&context, 117);
        floating_prefix(&mut seeded);
        assert_eq!(seeded.seed, Some(117));
        let byte = seeded.declare_bitvector(8, info);
        seeded.assert(Neq(Box::new(Var(byte)), Box::new(smtlib::bits64(0, 8))));
        let mut values = Vec::new();
        for _ in 0..3 {
            let query = seeded.query_solver(&[], false);
            drop(query);
            assert_eq!(seeded.check_sat(info), Sat);
            values.push(Model::new(&seeded).get_var(byte).unwrap().unwrap_exp());
        }
        assert_eq!(values[0], values[1]);
        assert_eq!(values[1], values[2]);
        let mut config = Config::new();
        config.set_param_value("rlimit", "1");
        let limited = Context::new(config);
        let mut solver = Solver::<B64>::new(&limited);
        let value = solver.declare_bitvector(64, info);
        let Error(error) = solver.check_sat_with(&Eq(Box::new(Var(value)), Box::new(smtlib::bits64(12, 64))), info)
        else {
            panic!("极小 rlimit 应耗尽")
        };
        assert_eq!(error.diagnostic()["reason_unknown"], "canceled");
        assert_eq!(error.reject_reason().to_string(), "z3_resource_exhausted");
        assert!(!solver.has_stashed_model());
    });
}

#[cfg(feature = "smt-thread-interrupt")]
#[test]
fn default_snapshot_interrupt_keeps_dump_and_restores_queries() {
    in_default_process("default_snapshot_interrupt_keeps_dump_and_restores_queries", || {
        let context = Context::new(Config::new());
        let info = SourceLoc::unknown();
        let mut solver = Solver::<B64>::new(&context);
        let left = solver.declare_bitvector(256, info);
        let right = solver.declare_bitvector(256, info);
        solver.assert(Eq(Box::new(Bvmul(Box::new(Var(left)), Box::new(Var(right)))), Box::new(Bits(vec![true; 256]))));
        let tx = solver.start_transaction();
        let error = match solver.check_sat_deadline(info, Duration::from_nanos(1)) {
            Error(error) => error,
            other => panic!("应中断真实求解，得到{other:?}"),
        };
        assert_eq!(error.reject_reason().to_string(), "z3_timeout");
        // 实际中断错误携带的转储来自原执行保存点，仍保留全部乘法断言。
        let SmtError::Z3Timeout(Z3Timeout::Interrupted(timeout)) = error else { panic!("应为超时错误") };
        assert!(timeout.dump.materialize().unwrap().contains("bvmul"));
        solver.rollback_transaction(tx);
        assert!(solver.check_sat_with(&Bool(false), info).is_unsat().unwrap());
    });
}

#[test]
fn default_integer_range_proof_uses_fresh_complete_snapshot() {
    in_default_process("default_integer_range_proof_uses_fresh_complete_snapshot", || {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let byte = solver.declare_bitvector(8, info);
        let wide = solver.declare_bitvector(128, info);
        // 通过断言给出范围，避免ZeroExtend本身已被化简、无需调用求解器。
        solver.assert(Eq(Box::new(Var(wide)), Box::new(ZeroExtend(120, Box::new(Var(byte))))));
        let original = solver.z3_solver as usize;
        let narrow = crate::primop::unary_primops::<B64>()["%i->%i64"];
        narrow(Val::Symbolic(wide), &mut solver, info).unwrap();
        let (queried, assumptions) = z3_timeout::last_solver_query();
        assert_ne!(queried, original, "default范围证明使用全部前提的新solver，避免增量历史");
        assert_eq!(assumptions, 0, "反例条件作为普通断言，保持首次普通check");
        // 普通BV查询仍复用原solver，范围证明不能改变其调用策略。
        assert_eq!(solver.check_sat_with(&Eq(Box::new(Var(byte)), Box::new(smtlib::bits64(7, 8))), info), Sat);
        assert_eq!(z3_timeout::last_solver_query(), (original, 1));
    });
}

#[test]
fn default_integer_range_proof_keeps_overflow_and_nested_guards() {
    in_default_process("default_integer_range_proof_keeps_overflow_and_nested_guards", || {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let guard = solver.declare_const(smtlib::Ty::Bool, info);
        let wide = solver.define_const(
            Ite(
                Box::new(Var(guard)),
                Box::new(crate::primop_util::smt_i128(1i128 << 70)),
                Box::new(crate::primop_util::smt_i128(7)),
            ),
            info,
        );
        let narrow = crate::primop::unary_primops::<B64>()["%i->%i64"];
        assert!(matches!(
            narrow(Val::Symbolic(wide), &mut solver, info),
            Err(crate::error::ExecError::IntegerConversion(..))
        ));
        let tx = solver.start_transaction();
        solver.assert(Not(Box::new(Var(guard))));
        let inner = solver.start_transaction_with_guard(Some(Not(Box::new(Var(guard)))));
        let result = narrow(Val::Symbolic(wide), &mut solver, info).unwrap();
        assert!(matches!(result, Val::Symbolic(_)));
        solver.rollback_transaction(inner);
        solver.rollback_transaction(tx);
        let tx = solver.start_transaction_with_guard(Some(Var(guard)));
        assert!(matches!(narrow(Val::Symbolic(wide), &mut solver, info), Err(crate::error::ExecError::Overflow)));
        // 新solver的Sat模型仍被正常缓存，回滚也恢复原查询上下文。
        assert!(solver.has_stashed_model());
        solver.rollback_transaction(tx);
        assert!(matches!(
            narrow(Val::Symbolic(wide), &mut solver, info),
            Err(crate::error::ExecError::IntegerConversion(..))
        ));
        assert_eq!(solver.transaction_depth(), 0);
    });
}

#[test]
fn default_integer_range_proof_preserves_incremental_scope_and_limits() {
    in_default_process("default_integer_range_proof_preserves_incremental_scope_and_limits", || {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new_seeded(&context, 117);
        let info = SourceLoc::unknown();
        let narrow = crate::primop::unary_primops::<B64>()["%i->%i64"];
        let overflow = solver.define_const(crate::primop_util::smt_i128(1i128 << 70), info);
        let tx = solver.start_transaction();
        solver.with_incremental_checks(|solver| {
            let original = solver.z3_solver as usize;
            assert!(matches!(narrow(Val::Symbolic(overflow), solver, info), Err(crate::error::ExecError::Overflow)));
            assert_eq!(z3_timeout::last_solver_query().0, original, "显式增量范围保持学习状态");
        });
        solver.rollback_transaction(tx);
        assert_eq!(solver.seed, Some(117));
        let mut config = Config::new();
        config.set_param_value("rlimit", "1");
        let limited = Context::new(config);
        let mut solver = Solver::<B64>::new(&limited);
        let wide = solver.declare_bitvector(128, info);
        assert!(
            matches!(
                narrow(Val::Symbolic(wide), &mut solver, info),
                Err(ExecError::Smt(SmtError::Z3ResourceExhausted(_)))
            ),
            "显式资源限制返回Unknown，不能被当作无溢出"
        );
    });
}

#[test]
fn default_range_snapshot_keeps_all_conditions_and_sat_model() {
    in_default_process("default_range_snapshot_keeps_all_conditions_and_sat_model", || {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new_seeded(&context, 117);
        let info = SourceLoc::unknown();
        let fixed = solver.declare_const(smtlib::Ty::Bool, info);
        let guard = solver.declare_const(smtlib::Ty::Bool, info);
        let nested = solver.declare_const(smtlib::Ty::Bool, info);
        let buffered = solver.declare_const(smtlib::Ty::Bool, info);
        let temporary = solver.declare_const(smtlib::Ty::Bool, info);
        solver.assert(Var(fixed));
        let outer = solver.start_transaction_with_guard(Some(Var(guard)));
        solver.assert(Var(buffered));
        let inner = solver.start_transaction_with_guard(Some(Var(nested)));
        solver.with_transaction_condition(&Var(temporary), |solver| {
            for symbol in [fixed, guard, nested, buffered, temporary] {
                assert_eq!(solver.check_sat_with_for_range(&Not(Box::new(Var(symbol))), info), Unsat);
            }
            assert_eq!(solver.check_sat_with_for_range(&Bool(true), info), Sat);
            // 查询对象已销毁，缓存模型仍须包含所有上下文条件。
            let mut model = Model::new(solver);
            for symbol in [fixed, guard, nested, buffered, temporary] {
                assert_eq!(model.get_var(symbol).unwrap().unwrap_exp(), Bool(true));
            }
        });
        solver.rollback_transaction(inner);
        solver.rollback_transaction(outer);
        for symbol in [guard, nested, buffered, temporary] {
            assert_eq!(solver.check_sat_with_for_range(&Not(Box::new(Var(symbol))), info), Sat);
            assert_eq!(Model::new(&solver).get_var(symbol).unwrap().unwrap_exp(), Bool(false));
        }
        assert_eq!(solver.check_sat_with_for_range(&Not(Box::new(Var(fixed))), info), Unsat);
        assert_eq!(solver.seed, Some(117));
        assert_eq!(solver.transaction_depth(), 0);
    });
}

#[cfg(feature = "smt-thread-interrupt")]
#[test]
fn default_range_interrupt_keeps_complete_dump_and_rollback_model() {
    in_default_process("default_range_interrupt_keeps_complete_dump_and_rollback_model", || {
        z3_timeout::configure_z3_timeout(Some(Duration::from_millis(10)));
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let fixed = solver.declare_const(smtlib::Ty::Bool, info);
        solver.assert(Var(fixed));
        assert_eq!(solver.check_sat(info), Sat);
        let guard = solver.declare_const(smtlib::Ty::Bool, info);
        let temporary = solver.declare_const(smtlib::Ty::Bool, info);
        let outer = solver.start_transaction_with_guard(Some(Var(guard)));
        let buffered = solver.declare_const(smtlib::Ty::Bool, info);
        solver.assert(Var(buffered));
        let left = solver.declare_bitvector(512, info);
        let right = solver.declare_bitvector(512, info);
        // 两个因数最多128位，积为188位；排除1乘整个目标及512位回绕的平凡解。
        for factor in [left, right] {
            solver.assert(Eq(Box::new(Extract(511, 128, Box::new(Var(factor)))), Box::new(Bits(vec![false; 384]))));
        }
        let target = Bvmul(
            Box::new(ZeroExtend(384, Box::new(crate::primop_util::smt_i128(i128::MAX)))),
            Box::new(ZeroExtend(384, Box::new(crate::primop_util::smt_i128((1i128 << 61) - 1)))),
        );
        solver.assert(Eq(Box::new(Bvmul(Box::new(Var(left)), Box::new(Var(right)))), Box::new(target)));
        let wide = solver.declare_bitvector(128, info);
        solver.with_transaction_condition(&Var(temporary), |solver| {
            let narrow = crate::primop::unary_primops::<B64>()["%i->%i64"];
            let error = narrow(Val::Symbolic(wide), solver, info).unwrap_err();
            let crate::error::ExecError::Smt(SmtError::Z3Timeout(Z3Timeout::Interrupted(timeout))) = error else {
                panic!("范围查询必须传播真实中断错误，得到{error:?}");
            };
            assert_eq!(timeout.operation, SmtOperation::CheckSatAssuming);
            assert_eq!(timeout.limit, Duration::from_millis(10));
            assert!(!solver.has_stashed_model());
            let dump = timeout.dump.materialize().unwrap();
            for text in ["bvmul", "sign_extend", "check-sat"] {
                assert!(dump.contains(text), "范围查询转储缺少{text}: {dump}");
            }
            for symbol in [fixed, guard, temporary, buffered, wide] {
                assert!(dump.contains(&format!("isla_s{}", symbol.id)), "转储缺少{symbol:?}: {dump}");
            }
        });
        solver.rollback_transaction(outer);
        assert!(solver.has_stashed_model(), "回滚恢复进入事务前的模型");
        assert_eq!(Model::new(&solver).get_var(fixed).unwrap().unwrap_exp(), Bool(true));
        assert_eq!(solver.check_sat_with_for_range(&Bool(false), info), Unsat);
        assert_eq!(solver.transaction_depth(), 0);
    });
}

#[test]
fn default_vector_bounds_use_fresh_snapshot_and_preserve_values() {
    in_default_process("default_vector_bounds_use_fresh_snapshot_and_preserve_values", || {
        let context = Context::new(Config::new());
        let info = SourceLoc::unknown();
        for width in [64, 128] {
            for bits in [false, true] {
                let mut solver = Solver::<B64>::new_seeded(&context, 117);
                let index = solver.declare_bitvector(width, info);
                let guard = solver.declare_const(smtlib::Ty::Bool, info);
                let before = solver.trace().to_vec().len();
                let tx = solver.start_transaction_with_guard(Some(Var(guard)));
                // 下标约束留在事务缓冲；新solver必须保留它才能证明边界。
                solver.assert(Eq(
                    Box::new(Var(index)),
                    Box::new(if width == 64 {
                        crate::primop_util::smt_i64(1)
                    } else {
                        crate::primop_util::smt_i128(1)
                    }),
                ));
                let values = if bits {
                    Val::Bits(B64::new(2, 3))
                } else {
                    Val::Vector(vec![Val::I128(10), Val::I128(20), Val::I128(30)])
                };
                let original = solver.z3_solver as usize;
                let read =
                    crate::primop::vector_access(values.clone(), Val::Symbolic(index), &mut solver, info).unwrap();
                assert_ne!(z3_timeout::last_solver_query().0, original, "向量读取边界应使用完整新solver");
                assert_eq!(z3_timeout::last_solver_query().1, 0);
                let expected =
                    if bits { crate::primop_util::smt_sbits(B64::BIT_ONE) } else { crate::primop_util::smt_i128(20) };
                assert_eq!(
                    solver.check_sat_with(
                        &Neq(Box::new(crate::primop_util::smt_value(&read, info).unwrap()), Box::new(expected)),
                        info
                    ),
                    Unsat
                );
                let mut frame = crate::executor::LocalFrame::new(
                    crate::ir::Name::from_u32(0),
                    &[],
                    &crate::ir::Ty::Unit,
                    None,
                    &[],
                );
                let update = if bits { Val::Bits(B64::BIT_ZERO) } else { Val::I128(99) };
                let updated = crate::primop::vector_update(
                    vec![values, Val::Symbolic(index), update],
                    &mut solver,
                    &mut frame,
                    info,
                )
                .unwrap();
                assert_ne!(z3_timeout::last_solver_query().0, original, "向量更新边界应使用完整新solver");
                assert_eq!(z3_timeout::last_solver_query().1, 0);
                let read = crate::primop::vector_access(updated, Val::I128(1), &mut solver, info).unwrap();
                let expected =
                    if bits { crate::primop_util::smt_sbits(B64::BIT_ZERO) } else { crate::primop_util::smt_i128(99) };
                assert_eq!(
                    solver.check_sat_with(
                        &Neq(Box::new(crate::primop_util::smt_value(&read, info).unwrap()), Box::new(expected)),
                        info
                    ),
                    Unsat
                );
                solver.rollback_transaction(tx);
                assert_eq!(solver.trace().to_vec().len(), before);
                assert_eq!(solver.seed, Some(117));
                assert_eq!(
                    solver.check_sat_with(
                        &Eq(
                            Box::new(Var(index)),
                            Box::new(if width == 64 {
                                crate::primop_util::smt_i64(7)
                            } else {
                                crate::primop_util::smt_i128(7)
                            })
                        ),
                        info
                    ),
                    Sat
                );
            }
        }
    });
}

#[test]
fn default_vector_bounds_keep_errors_limits_and_incremental_scope() {
    in_default_process("default_vector_bounds_keep_errors_limits_and_incremental_scope", || {
        use crate::error::ExecError;
        let context = Context::new(Config::new());
        let info = SourceLoc::unknown();
        let mut solver = Solver::<B64>::new(&context);
        let index = solver.declare_bitvector(128, info);
        let values = Val::Vector(vec![Val::I128(10), Val::I128(20)]);
        assert!(matches!(
            crate::primop::vector_access(values.clone(), Val::Symbolic(index), &mut solver, info),
            Err(ExecError::SymbolicLength("vector_access", _))
        ));
        let tx = solver.start_transaction();
        solver.assert(Eq(Box::new(Var(index)), Box::new(crate::primop_util::smt_i128(-1))));
        solver.with_incremental_checks(|solver| {
            let original = solver.z3_solver as usize;
            assert!(matches!(
                crate::primop::vector_access(values.clone(), Val::Symbolic(index), solver, info),
                Err(ExecError::OutOfBounds("vector_access"))
            ));
            assert_eq!(z3_timeout::last_solver_query().0, original);
        });
        solver.rollback_transaction(tx);
        assert!(matches!(
            crate::primop::vector_access(Val::Vector(vec![]), Val::Symbolic(index), &mut solver, info),
            Err(ExecError::OutOfBounds("vector_access"))
        ));
        let mut config = Config::new();
        config.set_param_value("rlimit", "1");
        let limited = Context::new(config);
        let mut solver = Solver::<B64>::new(&limited);
        let index = solver.declare_bitvector(128, info);
        assert!(matches!(
            crate::primop::vector_access(values, Val::Symbolic(index), &mut solver, info),
            Err(ExecError::Smt(SmtError::Z3ResourceExhausted(_)))
        ));
    });
}

#[test]
fn default_slice_bounds_keep_partial_range_and_rollback_model() {
    in_default_process("default_slice_bounds_keep_partial_range_and_rollback_model", || {
        use crate::error::ExecError;
        let context = Context::new(Config::new());
        let info = SourceLoc::unknown();
        for width in [64, 128] {
            let mut solver = Solver::<B64>::new_seeded(&context, 117);
            let index = solver.declare_bitvector(width, info);
            let integer = |value: i128| {
                if width == 64 {
                    crate::primop_util::smt_i64(value as i64)
                } else {
                    crate::primop_util::smt_i128(value)
                }
            };
            let update = |solver: &mut Solver<B64>| {
                let bits = Val::Bits(B64::new(0, 8));
                let replacement = Val::Bits(B64::new(3, 2));
                if width == 64 {
                    crate::primop::op_set_slice(bits, Val::Symbolic(index), replacement, solver, info)
                } else {
                    crate::primop::set_slice_internal(bits, Val::Symbolic(index), replacement, solver, info)
                }
            };
            // 保存一个确定为7的模型；事务内的范围查询会改成6，回滚必须恢复7。
            assert_eq!(solver.check_sat_with(&Eq(Box::new(Var(index)), Box::new(integer(7))), info), Sat);
            let before = solver.trace().to_vec().len();
            let outer = solver.start_transaction();
            solver.assert(Bvuge(Box::new(Var(index)), Box::new(integer(6))));
            solver.assert(Bvule(Box::new(Var(index)), Box::new(integer(7))));
            let original = solver.z3_solver as usize;
            let condition = match update(&mut solver) {
                Err(ExecError::RetryCondition(condition, _)) => condition,
                other => panic!("两位更新只有下标6合法，下标7必须请求重试，得到{other:?}"),
            };
            assert_ne!(z3_timeout::last_solver_query().0, original);
            assert_eq!(z3_timeout::last_solver_query().1, 0);
            assert_eq!(Model::new(&solver).get_var(index).unwrap().unwrap_exp(), integer(6));
            let inner = solver.start_transaction_with_guard(Some(condition));
            let updated = update(&mut solver).unwrap();
            assert_eq!(
                solver.check_sat_with(
                    &Neq(
                        Box::new(crate::primop_util::smt_value(&updated, info).unwrap()),
                        Box::new(smtlib::bits64(0xc0, 8)),
                    ),
                    info
                ),
                Unsat
            );
            solver.rollback_transaction(inner);
            assert_eq!(Model::new(&solver).get_var(index).unwrap().unwrap_exp(), integer(6));
            solver.rollback_transaction(outer);
            assert_eq!(solver.trace().to_vec().len(), before);
            assert!(solver.has_stashed_model());
            assert_eq!(Model::new(&solver).get_var(index).unwrap().unwrap_exp(), integer(7));
            // 保留整个更新范围与原始索引位宽，不能截低位后接受越界输入。
            for invalid in [7, -1, 1i128 << 32] {
                let tx = solver.start_transaction();
                solver.assert(Eq(Box::new(Var(index)), Box::new(integer(invalid))));
                assert!(matches!(update(&mut solver), Err(ExecError::OutOfBounds("vector_update"))));
                solver.rollback_transaction(tx);
            }
            assert_eq!(solver.seed, Some(117));
            assert_eq!(solver.transaction_depth(), 0);
        }
    });
}

// 多个独立选择构成大DAG，但所有结果仍在0..=128；不依赖具体模型。
fn boolean_proof_counter(solver: &mut Solver<B64>) -> Sym {
    let info = SourceLoc::unknown();
    let mut value = crate::primop_util::smt_i128(0);
    for i in 1..=128 {
        let bit = solver.declare_const(smtlib::Ty::Bool, info);
        value = Ite(Box::new(Var(bit)), Box::new(crate::primop_util::smt_i128(i)), Box::new(value));
    }
    solver.define_const(value, info)
}

#[test]
fn default_complex_boolean_proofs_keep_truth_and_complete_state() {
    in_default_process("default_complex_boolean_proofs_keep_truth_and_complete_state", || {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new_seeded(&context, 117);
        let info = SourceLoc::unknown();
        let value = boolean_proof_counter(&mut solver);
        let lt = crate::primop::binary_primops::<B64>()["lt"];
        let eq = crate::primop::binary_primops::<B64>()["eq_int"];
        let original = solver.z3_solver as usize;
        for (bound, expected) in [(129, Some(true)), (0, Some(false)), (64, None)] {
            let result = lt(Val::Symbolic(value), Val::I128(bound), &mut solver, info).unwrap();
            match expected {
                Some(expected) => assert_eq!(result, Val::Bool(expected)),
                None => assert!(matches!(result, Val::Symbolic(_))),
            }
            assert_ne!(z3_timeout::last_solver_query().0, original, "大布尔证明应复用完整快照普通check");
            assert_eq!(z3_timeout::last_solver_query().1, 0);
        }
        let pending_value = boolean_proof_counter(&mut solver);
        let cached = solver.declare_bitvector(128, info);
        solver.assert(Eq(Box::new(Var(cached)), Box::new(crate::primop_util::smt_i128(7))));
        let outer_guard = solver.declare_const(smtlib::Ty::Bool, info);
        let inner_guard = solver.declare_const(smtlib::Ty::Bool, info);
        let premise = Eq(Box::new(Var(value)), Box::new(crate::primop_util::smt_i128(17)));
        solver.assert(Or(Box::new(Not(Box::new(Var(outer_guard)))), Box::new(premise)));
        assert_eq!(solver.check_sat(info), Sat);
        let outer = solver.start_transaction_with_guard(Some(Var(outer_guard)));
        let inner = solver.start_transaction_with_guard(Some(Var(inner_guard)));
        solver.assert(Or(Box::new(Not(Box::new(Var(inner_guard)))), Box::new(Var(outer_guard))));
        assert_eq!(eq(Val::Symbolic(value), Val::I128(17), &mut solver, info).unwrap(), Val::Bool(true));
        // 这条约束只留在事务缓冲；另一大表达式的恒值必须依赖它。
        solver.assert(Eq(Box::new(Var(pending_value)), Box::new(crate::primop_util::smt_i128(23))));
        assert_eq!(eq(Val::Symbolic(pending_value), Val::I128(23), &mut solver, info).unwrap(), Val::Bool(true));
        solver.rollback_transaction(inner);
        solver.rollback_transaction(outer);
        let mut model = Model::new(&solver);
        assert_eq!(model.get_var(cached).unwrap().unwrap_exp(), crate::primop_util::smt_i128(7));
        drop(model);
        assert!(matches!(eq(Val::Symbolic(value), Val::I128(17), &mut solver, info).unwrap(), Val::Symbolic(_)));
        assert!(matches!(
            eq(Val::Symbolic(pending_value), Val::I128(23), &mut solver, info).unwrap(),
            Val::Symbolic(_)
        ));
        assert_eq!(solver.seed, Some(117));
    });
}

#[test]
fn default_boolean_proofs_keep_small_incremental_and_unknown_behavior() {
    in_default_process("default_boolean_proofs_keep_small_incremental_and_unknown_behavior", || {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let lt = crate::primop::binary_primops::<B64>()["lt"];
        let simple = solver.declare_bitvector(128, info);
        let original = solver.z3_solver as usize;
        assert!(matches!(lt(Val::Symbolic(simple), Val::I128(64), &mut solver, info).unwrap(), Val::Symbolic(_)));
        assert_eq!(z3_timeout::last_solver_query().0, original, "小比较保留增量学习");
        let complex = boolean_proof_counter(&mut solver);
        let tx = solver.start_transaction();
        solver.with_incremental_checks(|solver| {
            let original = solver.z3_solver as usize;
            assert_eq!(lt(Val::Symbolic(complex), Val::I128(129), solver, info).unwrap(), Val::Bool(true));
            assert_eq!(z3_timeout::last_solver_query().0, original, "显式增量范围优先");
        });
        solver.rollback_transaction(tx);
        let mut config = Config::new();
        config.set_param_value("rlimit", "1");
        let limited = Context::new(config);
        let mut solver = Solver::<B64>::new(&limited);
        let complex = boolean_proof_counter(&mut solver);
        assert!(
            matches!(
                lt(Val::Symbolic(complex), Val::I128(64), &mut solver, info),
                Err(ExecError::Smt(SmtError::Z3ResourceExhausted(Z3QueryFailure { purpose: "boolean_proof", .. })))
            ),
            "真实查询未判定必须作为带来源的求解错误返回"
        );
    });
}

#[test]
fn default_region_queries_reuse_complete_prefix_without_leaking_assumptions() {
    in_default_process("default_region_queries_reuse_complete_prefix_without_leaking_assumptions", || {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new_seeded(&context, 117);
        let info = SourceLoc::unknown();
        let fixed = solver.declare_const(smtlib::Ty::Bool, info);
        let guard = solver.declare_const(smtlib::Ty::Bool, info);
        let buffered = solver.declare_const(smtlib::Ty::Bool, info);
        let choice = solver.declare_const(smtlib::Ty::Bool, info);
        solver.assert(Var(fixed));
        let outer = solver.start_transaction_with_guard(Some(Var(guard)));
        solver.assert(Var(buffered));
        let positive = solver.translate_exp(&Var(choice));
        let negative = solver.translate_exp(&Not(Box::new(Var(choice))));
        let pending = solver.transaction_assertions();
        let mut assumptions = pending.iter().map(|ast| ast.z3_ast).collect::<Vec<_>>();
        assumptions.push(positive.z3_ast);
        let first = solver.query_solver(&assumptions, true);
        assert_eq!(unsafe { Z3_solver_check(context.z3_ctx, first.z3_solver) }, Z3_L_TRUE);
        *assumptions.last_mut().unwrap() = negative.z3_ast;
        let second = solver.query_solver(&assumptions, true);
        assert_eq!(first.z3_solver, second.z3_solver, "同一完整前缀的区域查询必须复用solver");
        assert_eq!(
            unsafe { Z3_solver_check(context.z3_ctx, second.z3_solver) },
            Z3_L_TRUE,
            "切换目标必须pop上次正条件，不能把两个目标同时保留"
        );
        drop(second);
        drop(first);
        assert_eq!(solver.check_sat_with_for_bool(&Not(Box::new(Var(fixed))), info), Unsat, "原路径前提必须保留");
        assert_eq!(
            solver.check_sat_with_for_bool(&Not(Box::new(Var(buffered))), info),
            Unsat,
            "尚未发布的事务断言必须保留"
        );
        assert_eq!(solver.check_sat_with_for_bool(&Not(Box::new(Var(guard))), info), Unsat, "活动臂条件必须保留");
        let inner = solver.start_transaction_with_guard(Some(Not(Box::new(Var(choice)))));
        assert_eq!(solver.check_sat_with_for_bool(&Var(choice), info), Unsat);
        solver.rollback_transaction(inner);
        assert_eq!(solver.check_sat_with_for_bool(&Var(choice), info), Sat);
        assert_eq!(solver.check_sat_with_for_bool(&Not(Box::new(Var(choice))), info), Sat);
        solver.rollback_transaction(outer);
        let next = solver.start_transaction();
        assert_eq!(
            solver.check_sat_with_for_bool(&Not(Box::new(Var(buffered))), info),
            Sat,
            "共同前缀变化后不能保留已回滚的缓冲断言"
        );
        assert_eq!(solver.check_sat_with_for_bool(&Not(Box::new(Var(guard))), info), Sat);
        solver.rollback_transaction(next);
        solver.assert(Not(Box::new(Var(fixed))));
        assert_eq!(solver.check_sat(info), Unsat);
        assert_eq!(solver.seed, Some(117));
    });
}

#[test]
fn smt_witness_commit_keeps_witness_for_weaker_guarded_formula() {
    in_default_process("smt_witness_commit_keeps_witness_for_weaker_guarded_formula", || {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let guard = solver.declare_const(Ty::Bool, info);
        let value = solver.declare_const(Ty::Bool, info);
        solver.start_transaction_with_guard(Some(Var(guard)));
        solver.assert(Var(value));
        assert_eq!(solver.check_sat(info), Sat);
        let witness = solver.stashed_model;
        let calls = path_smt_stats().calls;
        solver.commit_transaction();
        // g ∧ c 的同一个见证满足 g→c；提交不应丢弃已经证明有效的模型。
        assert_eq!(solver.stashed_model, witness);
        assert_eq!(solver.check_sat(info), Sat);
        assert_eq!(path_smt_stats().calls, calls, "提交后的完整查询应复用见证");
        // 原臂条件已经撤掉，另一臂仍可取相反值，不能把模型取值当成恒真条件。
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(value))), info), Sat);
        assert_eq!(solver.cached_bool_value(&Var(guard)).unwrap(), Some(false));
        solver.assert(Var(guard));
        assert!(!solver.has_stashed_model(), "新增断言必须使旧见证失效");
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(value))), info), Unsat);
    });
}

#[test]
fn smt_witness_commit_two_arms_preserves_both_values_and_rollback() {
    in_default_process("smt_witness_commit_two_arms_preserves_both_values_and_rollback", || {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let guard = solver.declare_const(Ty::Bool, info);
        let value = solver.declare_const(Ty::Bool, info);
        assert_eq!(solver.check_sat_with(&Var(guard), info), Sat);
        let prefix_witness = solver.stashed_model;
        let outer = solver.start_transaction();
        for (condition, result) in [(Var(guard), Var(value)), (Not(Box::new(Var(guard))), Not(Box::new(Var(value))))] {
            solver.start_transaction_with_guard(Some(condition));
            solver.assert(result);
            assert_eq!(solver.check_sat(info), Sat);
            let witness = solver.stashed_model;
            solver.commit_transaction();
            assert_eq!(solver.stashed_model, witness);
            assert_eq!(solver.check_sat(info), Sat);
        }
        assert_eq!(solver.check_sat_with(&Var(value), info), Sat);
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(value))), info), Sat);
        assert_eq!(solver.check_sat_with(&And(Box::new(Var(guard)), Box::new(Not(Box::new(Var(value))))), info), Unsat);
        solver.rollback_transaction(outer);
        assert_eq!(solver.stashed_model, prefix_witness);
        // 回滚移除了两臂约束，交叉赋值重新可行。
        assert_eq!(solver.check_sat_with(&And(Box::new(Var(guard)), Box::new(Not(Box::new(Var(value))))), info), Sat);
    });
}

#[test]
fn smt_witness_commit_unconditional_assertions_keeps_current_witness() {
    in_default_process("smt_witness_commit_unconditional_assertions_keeps_current_witness", || {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let value = solver.declare_const(Ty::Bool, info);
        solver.start_transaction();
        solver.assert(Var(value));
        assert_eq!(solver.check_sat(info), Sat);
        let witness = solver.stashed_model;
        solver.commit_transaction();
        assert_eq!(solver.stashed_model, witness);
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(value))), info), Unsat);
        // 未查询的新断言不能在提交时重新获得一个旧模型。
        solver.start_transaction();
        solver.assert(Not(Box::new(Var(value))));
        solver.commit_transaction();
        assert!(!solver.has_stashed_model());
        assert_eq!(solver.check_sat(info), Unsat);
    });
}

#[test]
fn default_rebinding_invalidates_witness_for_buffered_assertions() {
    in_default_process("default_rebinding_invalidates_witness_for_buffered_assertions", || {
        for redeclare in [false, true] {
            let context = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&context);
            let info = SourceLoc::unknown();
            let guard = solver.declare_const(smtlib::Ty::Bool, info);
            solver.start_transaction_with_guard(Some(Var(guard)));
            let value = solver.define_const(Bool(true), info);
            solver.assert(Var(value));
            assert_eq!(solver.check_sat(info), Sat);
            solver.define_const(Not(Box::new(Var(guard))), info);
            assert!(solver.has_stashed_model(), "新符号的纯定义不改变既有约束");
            if redeclare {
                solver.add(smtlib::Def::DeclareConst(value, smtlib::Ty::Bool));
            } else {
                solver.add(smtlib::Def::DefineConst(value, Bool(false)));
            }
            assert!(!solver.has_stashed_model(), "已有符号改绑后，缓冲断言的含义可能改变");
            solver.commit_transaction();
            let impossible =
                if redeclare { And(Box::new(Var(guard)), Box::new(Not(Box::new(Var(value))))) } else { Var(guard) };
            assert_eq!(solver.check_sat_with(&impossible, info), Unsat);
            assert_eq!(solver.check_sat_with(&Not(Box::new(Var(guard))), info), Sat);
        }
    });
}
