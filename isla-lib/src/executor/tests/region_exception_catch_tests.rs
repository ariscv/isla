use super::*;

#[test]
fn region_exception_catch_resumes_each_call_with_its_own_return_slot() {
    let mut shared = empty_shared_state();
    let callee = shared.symtab.intern("zmaybe");
    let ctor = shared.symtab.intern("zThrown");
    shared.type_info.union_ctors.insert(ctor);
    shared.type_info.unions.insert(SAIL_EXCEPTION, vec![(ctor, Ty::Unit)]);
    let parameter = test_name(980);
    let exception = test_name(981);
    let copy = |id, value| Instr::Copy(Loc::Id(id), value, info());
    let call = |id, function, args| Instr::Call(Loc::Id(id), false, function, args, info());
    let body = vec![
        Instr::Jump(Exp::Id(parameter), 3, info()),
        copy(RETURN, Exp::Bool(false)),
        Instr::End,
        Instr::Decl(exception, Ty::Union(SAIL_EXCEPTION), info()),
        call(exception, ctor, vec![Exp::Unit]),
        copy(CURRENT_EXCEPTION, Exp::Id(exception)),
        copy(HAVE_EXCEPTION, Exp::Bool(true)),
        copy(THROW_LOCATION, Exp::String("fixture.sail:17".into())),
        Instr::Arbitrary,
    ];
    shared.functions.insert(callee, (vec![(parameter, &Ty::Bool)], &Ty::Bool, Box::leak(body.into_boxed_slice())));

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
        assert_eq!(equivalent_paths(&off, &on, 1, true), (2, 1));
        assert!(on[0].exception.is_none());
    }
}
