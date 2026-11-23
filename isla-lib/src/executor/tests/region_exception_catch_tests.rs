use super::*;

fn throwing_callee(shared: &mut SharedState<'static, B64>) -> Name {
    let callee = shared.symtab.intern("zmaybe");
    let ctor = shared.symtab.intern("zThrown");
    shared.type_info.union_ctors.insert(ctor);
    shared.type_info.unions.insert(SAIL_EXCEPTION, vec![(ctor, Ty::Unit)]);
    let parameter = test_name(980);
    let exception = test_name(981);
    let copy = |id, value| Instr::Copy(Loc::Id(id), value, info());
    let body = vec![
        Instr::Jump(Exp::Id(parameter), 3, info()),
        copy(RETURN, Exp::Bool(false)),
        Instr::End,
        Instr::Decl(exception, Ty::Union(SAIL_EXCEPTION), info()),
        Instr::Call(Loc::Id(exception), false, ctor, vec![Exp::Unit], info()),
        copy(CURRENT_EXCEPTION, Exp::Id(exception)),
        copy(HAVE_EXCEPTION, Exp::Bool(true)),
        copy(THROW_LOCATION, Exp::String("fixture.sail:17".into())),
        Instr::Arbitrary,
    ];
    shared.functions.insert(callee, (vec![(parameter, &Ty::Bool)], &Ty::Bool, Box::leak(body.into_boxed_slice())));
    callee
}

#[test]
fn region_exception_catch_resumes_each_call_with_its_own_return_slot() {
    let mut shared = empty_shared_state();
    let callee = throwing_callee(&mut shared);
    let copy = |id, value| Instr::Copy(Loc::Id(id), value, info());
    let call = |id, function, args| Instr::Call(Loc::Id(id), false, function, args, info());

    let a = test_name(982);
    let b = test_name(983);
    let program = vec![
        Instr::Decl(a, Ty::Bool, info()),
        Instr::Decl(b, Ty::Bool, info()),
        call(a, callee, vec![input(0)]),
        Instr::Jump(Exp::Call(Op::Not, vec![Exp::Id(HAVE_EXCEPTION)]), 6, info()),
        copy(HAVE_EXCEPTION, Exp::Bool(false)),
        copy(a, Exp::Bool(true)),
        call(b, callee, vec![Exp::Call(Op::Not, vec![input(0)])]),
        Instr::Jump(Exp::Call(Op::Not, vec![Exp::Id(HAVE_EXCEPTION)]), 10, info()),
        copy(HAVE_EXCEPTION, Exp::Bool(false)),
        copy(b, Exp::Bool(true)),
        copy(RETURN, Exp::Call(Op::And, vec![Exp::Id(a), Exp::Call(Op::Not, vec![Exp::Id(b)])])),
        Instr::End,
    ];
    shared.functions.insert(TOP_LEVEL_LET, (Vec::new(), &Ty::Bool, Box::leak(program.clone().into_boxed_slice())));
    let off = paths(program.clone(), &shared, 1, false);
    for strategy in [crate::config::MergeStrategy::Recursive, crate::config::MergeStrategy::Flat] {
        let mut limits = ExecutionLimits::default().with_path_merging(true);
        limits.merge_strategy = strategy;
        let on = paths_with_state(program.clone(), &shared, 1, limits, crate::memory::Memory::new(), |_| ());
        assert_eq!((off.len(), on.len()), (2, 1));
        assert!(on[0].exception.is_none());
        // 直接从执行检查点重放。这里有两次定义借用同一输入，
        // 需保留 Z3 中的所有原始定义及断言。
        let context = Context::new(Config::new());
        let mut solver = Solver::from_checkpoint(&context, on[0].checkpoint.clone());
        let returned = smt_value(&on[0].value, info()).unwrap();
        let input = smtlib::Exp::Var(Sym { id: 0 });
        assert!(
            solver.check_sat_with(&smtlib::Exp::Neq(Box::new(returned), Box::new(input)), info()).is_unsat().unwrap(),
            "两次调用分别向自己的目的槽写入，最终结果应等于输入"
        );
    }
}

fn initialized_exception_globals(shared: &SharedState<'static, B64>) -> [Instr<Name, B64>; 2] {
    // 捕获只清除 have_exception。固定未激活的异常载荷和位置，令差分只比较捕获控制与返回值。
    [
        Instr::Call(Loc::Id(CURRENT_EXCEPTION), false, shared.symtab.lookup("zThrown"), vec![Exp::Unit], info()),
        Instr::Copy(Loc::Id(THROW_LOCATION), Exp::String("fixture.sail:17".into()), info()),
    ]
}

#[test]
fn region_exception_catch_in_descendant_call_returns_to_the_parent_region() {
    let mut shared = empty_shared_state();
    let throwing = throwing_callee(&mut shared);
    let catching = shared.symtab.intern("zcatching_in_parent_arm");
    let parameter = test_name(984);
    let copy = |id, value| Instr::Copy(Loc::Id(id), value, info());
    let call = |id, function, args| Instr::Call(Loc::Id(id), false, function, args, info());
    let no_exception = || Exp::Call(Op::Not, vec![Exp::Id(HAVE_EXCEPTION)]);
    let body = vec![
        call(RETURN, throwing, vec![Exp::Id(parameter)]),
        Instr::Jump(no_exception(), 4, info()),
        copy(HAVE_EXCEPTION, Exp::Bool(false)),
        copy(RETURN, Exp::Bool(true)),
        Instr::End,
    ];
    shared.functions.insert(catching, (vec![(parameter, &Ty::Bool)], &Ty::Bool, Box::leak(body.into_boxed_slice())));
    let mut program = initialized_exception_globals(&shared).to_vec();
    program.extend([
        Instr::Jump(input(0), 5, info()),
        call(RETURN, catching, vec![input(1)]),
        Instr::Goto(6),
        copy(RETURN, Exp::Bool(true)),
        Instr::End,
    ]);
    shared.functions.insert(TOP_LEVEL_LET, (Vec::new(), &Ty::Bool, Box::leak(program.clone().into_boxed_slice())));

    let plain = paths(program.clone(), &shared, 2, false);
    assert_eq!(plain.len(), 3);
    for strategy in [crate::config::MergeStrategy::Recursive, crate::config::MergeStrategy::Flat] {
        let mut limits = ExecutionLimits::default().with_path_merging(true).with_region_global_state(true);
        limits.merge_strategy = strategy;
        let merged = paths_with_state(program.clone(), &shared, 2, limits, crate::memory::Memory::new(), |_| ());
        assert_eq!(equivalent_paths(&plain, &merged, 2, true), (3, 1));
        assert!(merged[0].exception.is_none());
        assert!(merged[0]
            .records
            .iter()
            .any(|record| { record.function == catching && record.branch_pc == 1 && record.parent_record.is_some() }));
    }
}

#[test]
fn region_exception_catch_does_not_execute_nodes_outside_the_parent_region() {
    let mut shared = empty_shared_state();
    let throwing = throwing_callee(&mut shared);
    let copy = |id, value| Instr::Copy(Loc::Id(id), value, info());
    let mut program = initialized_exception_globals(&shared).to_vec();
    program.extend([
        Instr::Jump(input(0), 8, info()),
        Instr::Call(Loc::Id(RETURN), false, throwing, vec![input(1)], info()),
        Instr::Jump(Exp::Call(Op::Not, vec![Exp::Id(HAVE_EXCEPTION)]), 7, info()),
        copy(HAVE_EXCEPTION, Exp::Bool(false)),
        copy(RETURN, Exp::Bool(true)),
        Instr::Goto(9),
        copy(RETURN, Exp::Bool(true)),
        Instr::End,
    ]);
    shared.functions.insert(TOP_LEVEL_LET, (Vec::new(), &Ty::Bool, Box::leak(program.clone().into_boxed_slice())));

    let plain = paths(program.clone(), &shared, 2, false);
    assert_eq!(plain.len(), 3);
    for strategy in [crate::config::MergeStrategy::Recursive, crate::config::MergeStrategy::Flat] {
        let mut limits = ExecutionLimits::default().with_path_merging(true).with_region_global_state(true);
        limits.merge_strategy = strategy;
        let merged = paths_with_state(program.clone(), &shared, 2, limits, crate::memory::Memory::new(), |_| ());
        equivalent_paths(&plain, &merged, 2, true);
        assert!(merged.iter().all(|path| path.exception.is_none()));
        assert!(merged.iter().flat_map(|path| path.records.iter()).all(|record| {
            record.function != TOP_LEVEL_LET || record.branch_pc != 4 || record.parent_record.is_none()
        }));
    }
}
