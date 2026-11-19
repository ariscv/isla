//! 两臂具体值的区域合并及消费者差分。
use super::*;

fn candidate(program: Vec<Instr<Name, B64>>, shared: &SharedState<'static, B64>) -> Vec<Path> {
    let limits = ExecutionLimits::default().with_path_merging(true);
    paths_with_state(program, shared, 1, limits, crate::memory::Memory::new(), |_| ())
}

fn program(left: Exp<Name>, right: Exp<Name>, consumer: Instr<Name, B64>) -> Vec<Instr<Name, B64>> {
    let slot = test_name(1400);
    let ty = if matches!(&left, Exp::I64(_)) { Ty::I64 } else { Ty::String };
    vec![
        Instr::Decl(slot, ty, info()),
        Instr::Jump(input(0), 4, info()),
        Instr::Copy(Loc::Id(slot), right, info()),
        Instr::Goto(5),
        Instr::Copy(Loc::Id(slot), left, info()),
        consumer,
        Instr::End,
    ]
}

#[test]
fn region_concrete_values_string_return_retains_both_guards() {
    let shared = empty_shared_state();
    let code = program(
        Exp::String("左".into()),
        Exp::String("右".into()),
        Instr::Copy(Loc::Id(RETURN), Exp::Id(test_name(1400)), info()),
    );
    let forked = paths(code.clone(), &shared, 1, false);
    let merged = candidate(code, &shared);
    equivalent_values(&forked, &merged);
    assert_eq!(merged.len(), 2);
    assert!(merged.iter().all(|path| !path.records.is_empty()), "必须先合并，再在根返回处拆分");
    assert!(merged.iter().any(|path| path.value == Val::String("左".into())));
    assert!(merged.iter().any(|path| path.value == Val::String("右".into())));
}

#[test]
fn region_concrete_values_i64_arithmetic_differential() {
    let shared = empty_shared_state();
    let code = program(
        Exp::I64(3),
        Exp::I64(7),
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Add, vec![Exp::Id(test_name(1400)), Exp::I64(1)]), info()),
    );
    let forked = paths(code.clone(), &shared, 1, false);
    let merged = candidate(code, &shared);
    assert!(merged.iter().all(|path| !path.records.is_empty()), "消费者拆分不能作废先前合并");
    equivalent_values(&forked, &merged);
}

#[test]
fn region_concrete_values_string_comparison_differential() {
    let shared = empty_shared_state();
    let code = program(
        Exp::String("左".into()),
        Exp::String("右".into()),
        Instr::PrimopBinary(
            Loc::Id(RETURN),
            primop::binary_primops()["eq_string"],
            Exp::Id(test_name(1400)),
            Exp::String("左".into()),
            info(),
        ),
    );
    let forked = paths(code.clone(), &shared, 1, false);
    let merged = candidate(code, &shared);
    assert!(merged.iter().all(|path| !path.records.is_empty()));
    assert_eq!(merged.len(), 1, "字符串比较直接生成带守卫的布尔结果");
    equivalent_paths(&forked, &merged, 1, true);
}

fn equivalent_values(forked: &[Path], merged: &[Path]) {
    use smtlib::Exp::*;
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let inputs = [solver.declare_const(smtlib::Ty::Bool, info())];
    let guards = |paths: &[Path], solver: &mut Solver<B64>| {
        paths.iter().map(|path| (import_values(path, &inputs, solver, &[]).0, path.value.clone())).collect::<Vec<_>>()
    };
    let left = guards(forked, &mut solver);
    let right = guards(merged, &mut solver);
    for (a, va) in &left {
        for (b, vb) in &right {
            if va != vb {
                assert!(solver
                    .check_sat_with(&And(Box::new(a.clone()), Box::new(b.clone())), info())
                    .is_unsat()
                    .unwrap());
            }
        }
    }
    let covered = |paths: &[(Formula, Val<B64>)]| {
        paths.iter().fold(Bool(false), |p, (g, _)| Or(Box::new(p), Box::new(g.clone())))
    };
    assert!(solver
        .check_sat_with(&Neq(Box::new(covered(&left)), Box::new(covered(&right))), info())
        .is_unsat()
        .unwrap());
    assert!(solver.check_sat_with(&Not(Box::new(covered(&right))), info()).is_unsat().unwrap());
}

#[test]
fn region_concrete_values_print_does_not_change_return() {
    let shared = empty_shared_state();
    let mut code = program(
        Exp::String("左".into()),
        Exp::String("右".into()),
        Instr::PrimopUnary(Loc::Id(RETURN), primop::unary_primops()["print"], Exp::Id(test_name(1400)), info()),
    );
    code.insert(6, Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()));
    let forked = paths(code.clone(), &shared, 1, false);
    let merged = candidate(code, &shared);
    assert!(merged.iter().all(|path| !path.records.is_empty()));
    equivalent_paths(&forked, &merged, 1, true);
}

#[test]
fn region_concrete_values_nested_consumer_differential() {
    let shared = empty_shared_state();
    let slot = test_name(1400);
    let code = vec![
        Instr::Decl(slot, Ty::String, info()),
        Instr::Jump(input(0), 4, info()),
        Instr::Copy(Loc::Id(slot), Exp::String("右".into()), info()),
        Instr::Goto(5),
        Instr::Copy(Loc::Id(slot), Exp::String("左".into()), info()),
        Instr::Jump(input(1), 8, info()),
        Instr::PrimopBinary(
            Loc::Id(RETURN),
            primop::binary_primops()["eq_string"],
            Exp::Id(slot),
            Exp::String("左".into()),
            info(),
        ),
        Instr::Goto(9),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::End,
    ];
    let forked = paths(code.clone(), &shared, 2, false);
    let limits = ExecutionLimits::default().with_path_merging(true);
    let merged = paths_with_state(code, &shared, 2, limits, crate::memory::Memory::new(), |_| ());
    assert_eq!(merged.len(), 1, "嵌套消费者应在区域内拆分再汇合");
    equivalent_paths(&forked, &merged, 2, true);
}

#[test]
fn region_concrete_values_model_and_frozen_guard() {
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let guard = solver.declare_const(smtlib::Ty::Bool, info());
    let left = Val::I64(3);
    let right = Val::I64(9);
    let value = crate::primop_util::merge_concrete_val(guard, &left, &right, &mut solver, info()).unwrap();
    assert!(
        crate::primop_util::merge_val(guard, &left, &right, &mut solver, info()).is_err(),
        "严格值合并仍拒绝不同具体值"
    );
    solver.assert(smtlib::Exp::Var(guard));
    assert!(solver.check_sat(info()).is_sat().unwrap());
    let mut model = Model::new(&solver);
    assert_eq!(model.get_val(&value).unwrap(), left);
    drop(model);
    // 改写原符号的解释不应改变已创建候选的守卫AST。
    solver.add(smtlib::Def::DefineConst(guard, smtlib::Exp::Bool(false)));
    let Val::Guarded(frozen, _) = value else {
        panic!("必须保存候选");
    };
    assert_ne!(frozen, guard);
    assert_ne!(solver.structural_bool(&smtlib::Exp::Var(frozen)), Some(false));
}

#[test]
fn region_concrete_values_comparison_branch_inside_region() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let slot = test_name(1400);
    let code = vec![
        Instr::Decl(slot, Ty::I64, info()),
        Instr::Jump(input(0), 4, info()),
        Instr::Copy(Loc::Id(slot), Exp::I64(3), info()),
        Instr::Goto(5),
        Instr::Copy(Loc::Id(slot), Exp::I64(7), info()),
        Instr::Jump(input(1), 11, info()),
        Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(slot), Exp::I64(3)]), 9, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
        Instr::Goto(12),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(12),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
        Instr::End,
    ];
    let forked = paths(code.clone(), &shared, 2, false);
    let limits = ExecutionLimits::default().with_path_merging(true);
    let merged = paths_with_state(code, &shared, 2, limits, crate::memory::Memory::new(), |_| ());
    assert_eq!(merged.len(), 1);
    equivalent_paths(&forked, &merged, 2, true);
}
