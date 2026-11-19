use super::*;

#[test]
fn region_callee_register_write_uses_the_arm_guard() {
    let mut shared = empty_shared_state();
    let register = shared.symtab.intern("zcallee_state");
    let callee = shared.symtab.intern("zset_state");
    shared.registers.insert(register, Ty::Bool);
    let body = vec![
        Instr::Copy(Loc::Id(register), Exp::Bool(true), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
        Instr::End,
    ];
    shared.functions.insert(callee, (Vec::new(), &Ty::Unit, Box::leak(body.into_boxed_slice())));
    let program = vec![
        Instr::Decl(test_name(800), Ty::Unit, info()),
        Instr::Jump(input(0), 3, info()),
        Instr::Goto(4),
        Instr::Call(Loc::Id(test_name(800)), false, callee, Vec::new(), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Id(register), info()),
        Instr::End,
    ];
    let run = |merge| {
        paths_with_state(
            program.clone(),
            &shared,
            1,
            ExecutionLimits::default().with_path_merging(merge),
            crate::memory::Memory::new(),
            |frame| frame.regs_mut().assign(register, Val::Bool(false), &shared),
        )
    };
    let forked = run(false);
    let merged = run(true);
    assert_eq!(equivalent_paths(&forked, &merged, 1, true), (2, 1));
    equivalent_register_paths(&forked, &merged, 1);
    let path = &merged[0];
    let writes = path
        .events
        .iter()
        .filter_map(|event| match event {
            Event::WriteReg(name, _, value) if *name == register => Some(value),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(writes, [path.registers.get_last_if_initialized(register).unwrap()]);
}
