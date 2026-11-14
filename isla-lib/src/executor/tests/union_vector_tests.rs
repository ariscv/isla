//! 联合值向量的通用下标选择；具体下标旧路径作为语义对照。
use super::*;
use crate::primop_util::{build_vector_ite, smt_i128, smt_i64};
use crate::smt::smtlib::Exp as S;

fn record(value: Val<B64>) -> Val<B64> {
    Val::Struct(HashMap::from_iter([(test_name(1502), value), (test_name(1503), Val::Bool(true))]))
}

fn item(value: Val<B64>) -> Val<B64> {
    Val::Ctor(test_name(1501), Box::new(record(value)))
}

fn empty() -> Val<B64> {
    Val::Ctor(test_name(1500), Box::new(Val::Unit))
}

// 预期构造子已由枚举下标确定；比较标签及该标签的全部可观察载荷。
fn differences(actual: &Val<B64>, expected: &Val<B64>) -> Vec<S<Sym>> {
    match (actual, expected) {
        (Val::SymbolicCtor(tag, cases), Val::Ctor(name, payload)) => {
            let mut result = vec![S::Neq(Box::new(S::Var(*tag)), Box::new(name.to_smt()))];
            result.extend(differences(&cases[name], payload));
            result
        }
        (Val::Ctor(a, x), Val::Ctor(b, y)) => {
            assert_eq!(a, b);
            differences(x, y)
        }
        (Val::Struct(a), Val::Struct(b)) => {
            assert_eq!(a.len(), b.len());
            b.iter().flat_map(|(name, value)| differences(&a[name], value)).collect()
        }
        _ if actual == expected => vec![],
        _ => vec![S::Neq(Box::new(smt_value(actual, info()).unwrap()), Box::new(smt_value(expected, info()).unwrap()))],
    }
}

#[test]
fn union_vector_repeated_updates_match_enumerated_indices() {
    for width in [64, 128] {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let i = solver.declare_const(smtlib::Ty::BitVec(width), info());
        let k = solver.declare_const(smtlib::Ty::BitVec(width), info());
        let j = solver.declare_const(smtlib::Ty::BitVec(2), info());
        for index in [i, k] {
            solver.assert(S::Bvult(
                Box::new(S::Var(index)),
                Box::new(if width == 64 { smt_i64(3) } else { smt_i128(3) }),
            ));
        }
        solver.assert(S::Bvult(Box::new(S::Var(j)), Box::new(smtlib::bits64(3, 2))));
        let flag = solver.declare_const(smtlib::Ty::Bool, info());
        let data = Val::Symbolic(solver.declare_bitvector(8, info()));
        let other = Val::Symbolic(solver.declare_bitvector(8, info()));
        let choice = symbolic_ctor_choice(
            flag,
            (test_name(1500), Val::Unit),
            (test_name(1501), record(data.clone())),
            &mut solver,
        );
        let initial = Val::Vector(vec![empty(), item(data.clone()), choice]);
        let mut frame = make_frame(vec![Instr::End]);
        let once = primop::vector_update(
            vec![initial, Val::Symbolic(i), item(other.clone())],
            &mut solver,
            &mut frame,
            info(),
        )
        .unwrap();
        let twice =
            primop::vector_update(vec![once, Val::Symbolic(k), empty()], &mut solver, &mut frame, info()).unwrap();
        let selected = primop::vector_access(twice.clone(), Val::Symbolic(j), &mut solver, info()).unwrap();
        for a in 0..3 {
            for b in 0..3 {
                for c in 0..3 {
                    for is_empty in [false, true] {
                        let tx = solver.start_transaction_with_guard(Some(S::Bool(true)));
                        solver.assert_eq(S::Var(i), if width == 64 { smt_i64(a) } else { smt_i128(i128::from(a)) });
                        solver.assert_eq(S::Var(k), if width == 64 { smt_i64(b) } else { smt_i128(i128::from(b)) });
                        solver.assert_eq(S::Var(j), smtlib::bits64(c, 2));
                        solver.assert_eq(S::Var(flag), S::Bool(is_empty));
                        let mut oracle =
                            vec![empty(), item(data.clone()), if is_empty { empty() } else { item(data.clone()) }];
                        oracle[a as usize] = item(other.clone());
                        oracle[b as usize] = empty();
                        let expected = &oracle[c as usize];
                        let concrete_read =
                            primop::vector_access(twice.clone(), Val::I128(i128::from(c)), &mut solver, info())
                                .unwrap();
                        for actual in [&selected, &concrete_read] {
                            for difference in differences(actual, expected) {
                                assert!(
                                    solver.check_sat_with(&difference, info()).is_unsat().unwrap(),
                                    "任意载荷下均须与枚举路径等价"
                                );
                            }
                        }
                        assert!(solver.check_sat(info()).is_sat().unwrap(), "不得排除任何合法下标组合");
                        let mut model = Model::new(&solver);
                        assert_eq!(model.get_val(&selected).unwrap(), model.get_val(expected).unwrap());
                        drop(model);
                        solver.rollback_transaction(tx);
                    }
                }
            }
        }
    }
}

#[test]
fn union_vector_preflight_rejects_unrepresentable_payload_without_definitions() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let cond = solver.declare_const(smtlib::Ty::Bool, info());
    let tag = test_name(1501);
    let small = record(Val::Bits(B64::new(1, 8)));
    let mut extra = match small.clone() {
        Val::Struct(fields) => fields,
        _ => unreachable!(),
    };
    extra.insert(test_name(1504), Val::Unit);
    for (left, right) in [
        (small.clone(), Val::Struct(extra)),
        (small, record(Val::Bits(B64::new(1, 16)))),
        (Val::Vector(vec![Val::Bool(false)]), Val::Vector(vec![])),
        (Val::Unit, Val::Bool(false)),
        (Val::String("a".into()), Val::String("b".into())),
    ] {
        let left = Val::Ctor(tag, Box::new(left));
        let right = Val::Ctor(tag, Box::new(right));
        for (left, right) in [(&left, &right), (&right, &left)] {
            let before = format!("{:?}", solver.trace().to_vec());
            assert!(matches!(
                build_vector_ite(cond, left, right, &mut solver, info()),
                Err(ExecError::IncompatibleMerge | ExecError::NoSymbolicType)
            ));
            assert_eq!(format!("{:?}", solver.trace().to_vec()), before, "纯结构检查不得留下部分定义");
        }
    }
}

#[test]
fn union_vector_unsupported_payload_uses_original_index_retry() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let index = solver.declare_const(smtlib::Ty::BitVec(128), info());
    solver.assert(S::Bvult(Box::new(S::Var(index)), Box::new(smt_i128(2))));
    let initial = Val::Vector(vec![item(Val::Bits(B64::new(0, 8))), item(Val::Bits(B64::new(0, 16)))]);
    let mut frame = make_frame(vec![Instr::End]);
    assert!(matches!(
        primop::vector_access(initial.clone(), Val::Symbolic(index), &mut solver, info()),
        Err(ExecError::SymbolicLength("vector_access", _))
    ));
    assert!(matches!(
        primop::vector_update(
            vec![initial.clone(), Val::Symbolic(index), item(Val::Bits(B64::new(1, 8)))],
            &mut solver,
            &mut frame,
            info()
        ),
        Err(ExecError::SymbolicLength("vector_update", _))
    ));
    solver.assert_eq(S::Var(index), smt_i128(1));
    assert_eq!(
        primop::vector_access(initial.clone(), Val::Symbolic(index), &mut solver, info()).unwrap(),
        item(Val::Bits(B64::new(0, 16)))
    );
    let updated = primop::vector_update(
        vec![initial, Val::Symbolic(index), item(Val::Bits(B64::new(1, 8)))],
        &mut solver,
        &mut frame,
        info(),
    )
    .unwrap();
    assert_eq!(
        primop::vector_access(updated, Val::I128(1), &mut solver, info()).unwrap(),
        item(Val::Bits(B64::new(1, 8)))
    );
}

#[test]
fn union_vector_wrong_tag_keeps_success_and_error_input_domains() {
    for merging in [false, true] {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let index = solver.declare_const(smtlib::Ty::BitVec(128), info());
        solver.assert(S::Bvult(Box::new(S::Var(index)), Box::new(smt_i128(2))));
        let vector = test_name(1505);
        let n = test_name(1506);
        let selected = test_name(1507);
        let mut frame = make_frame(vec![
            Instr::PrimopVariadic(
                Loc::Id(vector),
                primop::variadic_primops()["vector_update"],
                vec![Exp::Id(vector), Exp::Id(n), Exp::Id(selected)],
                info(),
            ),
            Instr::PrimopBinary(
                Loc::Id(selected),
                primop::binary_primops()["vector_access"],
                Exp::Id(vector),
                Exp::I128(0),
                info(),
            ),
            Instr::Copy(Loc::Id(RETURN), Exp::Unwrap(test_name(1500), Box::new(Exp::Id(selected))), info()),
            Instr::End,
        ]);
        frame.vars_mut().insert(vector, UVal::Init(Val::Vector(vec![empty(), empty()])));
        frame.vars_mut().insert(n, UVal::Init(Val::Symbolic(index)));
        frame.vars_mut().insert(selected, UVal::Init(item(Val::Bits(B64::new(9, 8)))));
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(merging));
        let observed = Mutex::new(Vec::new());
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            &empty_shared_state(),
            &observed,
            &|_, _, result, _, mut solver, observed| {
                let error = match result {
                    Ok((Run::Finished(_), _)) => false,
                    Err((ExecError::Type(..), _)) => true,
                    _ => panic!("只能完成或报告标签错误"),
                };
                for value in 0..2 {
                    if solver
                        .check_sat_with(&S::Eq(Box::new(S::Var(index)), Box::new(smt_i128(value))), info())
                        .is_sat()
                        .unwrap()
                    {
                        observed.lock().unwrap().push((value, error));
                    }
                }
            },
        );
        let mut actual = observed.into_inner().unwrap();
        actual.sort();
        assert_eq!(actual, vec![(0, true), (1, false)], "错误域不能被标签合并吞掉");
    }
}

#[test]
fn union_vector_rejected_region_restores_frame_trace_and_solver() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let condition = solver.declare_const(smtlib::Ty::Bool, info());
    let index = solver.declare_const(smtlib::Ty::BitVec(128), info());
    solver.assert(S::Bvult(Box::new(S::Var(index)), Box::new(smt_i128(2))));
    let vector = test_name(1510);
    let n = test_name(1511);
    let value = test_name(1512);
    let mut frame = make_frame(vec![
        Instr::Jump(Exp::Id(test_name(1513)), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(6),
        Instr::PrimopVariadic(
            Loc::Id(vector),
            primop::variadic_primops()["vector_update"],
            vec![Exp::Id(vector), Exp::Id(n), Exp::Id(value)],
            info(),
        ),
        Instr::Copy(Loc::Id(RETURN), Exp::String("different".into()), info()),
        Instr::Goto(6),
        Instr::End,
    ]);
    let initial = Val::Vector(vec![empty(), empty()]);
    frame.vars_mut().insert(vector, UVal::Init(initial.clone()));
    frame.vars_mut().insert(n, UVal::Init(Val::Symbolic(index)));
    frame.vars_mut().insert(value, UVal::Init(item(Val::Bits(B64::new(7, 8)))));
    frame.vars_mut().insert(test_name(1513), UVal::Init(Val::Symbolic(condition)));
    // 先检查新标签和载荷定义确实由同一求解器事务管理。
    let before = format!("{:?}", solver.trace().to_vec());
    let tx = solver.start_transaction_with_guard(Some(S::Bool(true)));
    let updated = primop::vector_update(
        vec![initial.clone(), Val::Symbolic(index), item(Val::Bits(B64::new(7, 8)))],
        &mut solver,
        &mut frame,
        info(),
    )
    .unwrap();
    let mut symbols = HashSet::default();
    updated.collect_symbolic_variables(&mut symbols);
    assert!(!symbols.is_empty());
    solver.rollback_transaction(tx);
    assert!(symbols.iter().all(|sym| solver.scalar_sort(*sym).is_none()));
    assert_eq!(format!("{:?}", solver.trace().to_vec()), before);
    let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(true));
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let queue = Worker::new_lifo();
    let mut fraction = Fraction::one();
    let outcome = region_merge::try_region(
        condition,
        3,
        0,
        TaskId::fresh(),
        &mut fraction,
        PathTimeout::unlimited(),
        None,
        &SingleForkSink { queue: &queue },
        &mut frame,
        &state,
        &shared,
        &mut solver,
        info(),
    )
    .unwrap();
    assert!(matches!(outcome, region_merge::RegionResult::Rejected));
    assert_eq!(shared.execution_stats.merge_json()["candidate_attempts"], 1);
    assert_eq!(solver.transaction_depth(), 0);
    assert_eq!(format!("{:?}", solver.trace().to_vec()), before);
    assert_eq!(frame.pc, 0);
    let UVal::Init(actual) = &frame.vars()[&vector] else { panic!("向量必须初始化") };
    assert_eq!(actual, &initial);
    assert!(frame.region_merge_records().is_empty());
    assert!(frame.local_state.speculative_access.is_none());
    for selected in 0..2 {
        for flag in [false, true] {
            let tx = solver.start_transaction_with_guard(Some(S::Bool(true)));
            solver.assert_eq(S::Var(index), smt_i128(selected));
            solver.assert_eq(S::Var(condition), S::Bool(flag));
            assert!(solver.check_sat(info()).is_sat().unwrap(), "失败推演不得缩小输入域");
            solver.rollback_transaction(tx);
        }
    }
}

#[test]
fn union_vector_bounds_keep_old_errors_for_all_index_widths() {
    for width in [64, 128] {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let n = solver.declare_const(smtlib::Ty::BitVec(width), info());
        let mut frame = make_frame(vec![Instr::End]);
        let initial = Val::Vector(vec![empty(), item(Val::Bits(B64::new(1, 8)))]);
        for value in [-1, 2, 1_i128 << 64] {
            assert!(matches!(
                primop::vector_access(initial.clone(), Val::I128(value), &mut solver, info()),
                Err(ExecError::OutOfBounds(_))
            ));
            assert!(matches!(
                primop::vector_update(
                    vec![initial.clone(), Val::I128(value), empty()],
                    &mut solver,
                    &mut frame,
                    info()
                ),
                Err(ExecError::OutOfBounds(_))
            ));
        }
        for values in [Val::Vector(vec![]), initial.clone()] {
            let tx = solver.start_transaction_with_guard(Some(S::Bool(true)));
            solver.assert_eq(S::Var(n), if width == 64 { smt_i64(2) } else { smt_i128(2) });
            assert!(matches!(
                primop::vector_access(values.clone(), Val::Symbolic(n), &mut solver, info()),
                Err(ExecError::OutOfBounds(_))
            ));
            assert!(matches!(
                primop::vector_update(vec![values, Val::Symbolic(n), empty()], &mut solver, &mut frame, info()),
                Err(ExecError::OutOfBounds(_))
            ));
            solver.rollback_transaction(tx);
        }
        solver.assert(S::Bvule(Box::new(S::Var(n)), Box::new(if width == 64 { smt_i64(2) } else { smt_i128(2) })));
        assert!(matches!(
            primop::vector_access(initial.clone(), Val::Symbolic(n), &mut solver, info()),
            Err(ExecError::SymbolicLength("vector_access", _))
        ));
        assert!(matches!(
            primop::vector_update(vec![initial, Val::Symbolic(n), empty()], &mut solver, &mut frame, info()),
            Err(ExecError::SymbolicLength("vector_update", _))
        ));
        for value in 0..3 {
            assert!(solver
                .check_sat_with(
                    &S::Eq(
                        Box::new(S::Var(n)),
                        Box::new(if width == 64 { smt_i64(value) } else { smt_i128(i128::from(value)) })
                    ),
                    info()
                )
                .is_sat()
                .unwrap());
        }
    }
}

#[test]
fn union_vector_nested_union_and_enum_payload_keep_sorts_and_kind() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let cond = solver.declare_const(smtlib::Ty::Bool, info());
    let enumeration = solver.get_enum(test_name(1520), 2);
    let scalar = Val::Symbolic(solver.declare_const(smtlib::Ty::Enum(enumeration), info()));
    let concrete = Val::Enum(enumeration.first_member());
    let left = item(Val::Vector(vec![empty(), item(scalar)]));
    let right = item(Val::Vector(vec![item(concrete.clone()), item(concrete)]));
    let actual = build_vector_ite(cond, &left, &right, &mut solver, info()).unwrap();
    for flag in [false, true] {
        let tx = solver.start_transaction_with_guard(Some(S::Bool(true)));
        solver.assert_eq(S::Var(cond), S::Bool(flag));
        assert!(solver.check_sat(info()).is_sat().unwrap());
        let mut model = Model::new(&solver);
        assert_eq!(model.get_val(&actual).unwrap(), model.get_val(if flag { &left } else { &right }).unwrap());
        drop(model);
        let value = test_name(1521);
        let Val::Ctor(_, payload) = &actual else { panic!("外层标签必须保留") };
        let Val::Struct(fields) = payload.as_ref() else { panic!("记录必须保留") };
        let Val::Vector(elements) = &fields[&test_name(1502)] else { panic!("嵌套向量必须保留") };
        let mut frame = make_frame(vec![Instr::End]);
        frame.vars_mut().insert(value, UVal::Init(elements[0].clone()));
        let kind = eval_exp(
            &Exp::Kind(test_name(1500), Box::new(Exp::Id(value))),
            Arc::make_mut(&mut frame.local_state),
            &empty_shared_state(),
            &mut solver,
            info(),
        )
        .unwrap()
        .into_owned();
        assert!(solver.check_sat(info()).is_sat().unwrap());
        assert_eq!(Model::new(&solver).get_val(&kind).unwrap(), Val::Bool(!flag), "Kind 为标签不匹配");
        solver.rollback_transaction(tx);
    }
}
