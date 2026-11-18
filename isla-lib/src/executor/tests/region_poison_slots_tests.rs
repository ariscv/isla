//! 联合载荷与局部槽的汇合验证，涵盖返回关系、覆盖和活跃 Poison 错误。
use super::*;

#[test]
fn region_merge_poison_slots_local_overwrite_and_default() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let slot = shared.symtab.intern("zpoison_local");
    let overwrite = Instr::Copy(Loc::Id(slot), Exp::String("after".into()), info());
    let program = vec![
        Instr::Decl(slot, Ty::String, info()),
        Instr::Jump(input(0), 4, info()),
        Instr::Copy(Loc::Id(slot), Exp::String("before".into()), info()),
        Instr::Goto(5),
        Instr::Goto(5),
        overwrite,
        Instr::Copy(Loc::Id(RETURN), input(0), info()),
        Instr::End,
    ];
    let reference = paths(program.clone(), &shared, 1, false);
    let default = paths(program.clone(), &shared, 1, true);
    assert_eq!(equivalent_paths(&reference, &default, 1, true), (2, 2));
    assert!(default.iter().all(|path| path.records.is_empty()));

    let mut limits = ExecutionLimits::default().with_path_merging(true);
    limits.merge_poison_slots = true;
    let enabled = paths_with_state(program, &shared, 1, limits, crate::memory::Memory::new(), |_| ());
    assert_eq!(equivalent_paths(&reference, &enabled, 1, true), (2, 1));
    assert!(enabled[0].records.iter().any(|record| record.join == crate::ir::regions::RegionPoint::Instruction(5)));
}

#[test]
fn region_merge_poison_slots_live_local_rejects() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let slot = shared.symtab.intern("zpoison_live");
    let program = vec![
        Instr::Decl(slot, Ty::String, info()),
        Instr::Jump(input(0), 4, info()),
        Instr::Copy(Loc::Id(slot), Exp::String("before".into()), info()),
        Instr::Goto(5),
        Instr::Goto(5),
        Instr::Copy(Loc::Id(RETURN), Exp::Id(slot), info()),
        Instr::End,
    ];
    let mut limits = ExecutionLimits::default().with_path_merging(true);
    limits.merge_poison_slots = true;
    let results = paths_with_state(program, &shared, 1, limits, crate::memory::Memory::new(), |_| ());
    assert_eq!(results.len(), 2);
    assert!(results.iter().all(|path| path.records.is_empty()));
    assert_eq!(shared.execution_stats.merge_json()["failure_reasons"]["incompatible_state"], 1);
    assert!(results.iter().any(|path| path.value == Val::Poison));
}

fn union_case(nested: bool, checked: bool, enabled: bool) -> (Vec<Path>, Vec<Path>, usize, usize, u64) {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let selected = shared.symtab.intern("zpoison_selected");
    let left = shared.symtab.intern("zpoison_left");
    let right = shared.symtab.intern("zpoison_right");
    let ok = shared.symtab.intern("zpoison_ok");
    let err = shared.symtab.intern("zpoison_err");
    let wrapper = shared.symtab.intern("zpoison_wrapper");
    let unwrap = |ctor, value| Exp::Unwrap(ctor, Box::new(value));
    let union = if nested { unwrap(wrapper, Exp::Id(selected)) } else { Exp::Id(selected) };
    let mut program = vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(selected), Exp::Id(left), info()),
        Instr::Goto(4),
        Instr::Copy(Loc::Id(selected), Exp::Id(right), info()),
    ];
    if nested {
        // 待构造完整匹配后，补上外层标签不匹配时的目标。
        program.push(Instr::Jump(Exp::Kind(wrapper, Box::new(Exp::Id(selected))), 0, info()));
    }
    if checked {
        let pc = program.len();
        program.push(Instr::Jump(Exp::Kind(ok, Box::new(union.clone())), pc + 3, info()));
        program.push(Instr::Copy(Loc::Id(RETURN), unwrap(ok, union.clone()), info()));
        program.push(Instr::Goto(pc + 7));
        program.push(Instr::Jump(Exp::Kind(err, Box::new(union.clone())), pc + 6, info()));
        program.push(Instr::Copy(Loc::Id(RETURN), unwrap(err, union), info()));
        program.push(Instr::Goto(pc + 7));
        program.push(Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()));
        if nested {
            let Instr::Jump(_, target, _) = &mut program[4] else { unreachable!() };
            *target = pc + 6;
        }
    } else {
        program.push(Instr::Copy(Loc::Id(RETURN), unwrap(ok, union), info()));
    }
    program.push(Instr::End);

    let run = |merge| {
        let mut limits = ExecutionLimits::default().with_path_merging(merge);
        limits.merge_poison_slots = enabled;
        paths_with_solver_state(
            program.clone(),
            &shared,
            1,
            limits,
            crate::memory::Memory::new(),
            |frame, solver| {
                let wrap = |value| if nested { Val::Ctor(wrapper, Box::new(value)) } else { value };
                let ok_tag = solver.define_const(ok.to_smt(), info());
                let err_tag = solver.define_const(err.to_smt(), info());
                let a = Val::SymbolicCtor(ok_tag, [(ok, Val::Bool(true)), (err, Val::Poison)].into_iter().collect());
                let b = Val::SymbolicCtor(err_tag, [(ok, Val::Poison), (err, Val::Bool(false))].into_iter().collect());
                for (name, value) in [(left, wrap(a)), (right, wrap(b)), (selected, Val::Unit)] {
                    frame.vars_mut().insert(name, UVal::Init(value));
                }
            },
            true,
        )
    };
    let (reference, reference_errors) = run(false);
    let (merged, merged_errors) = run(true);
    (
        reference,
        merged,
        reference_errors,
        merged_errors,
        shared.execution_stats.merge_json()["failure_reasons"]["union_payload"].as_u64().unwrap_or(0),
    )
}

#[test]
fn region_merge_poison_slots_guarded_union_and_nested_union() {
    for nested in [false, true] {
        let (reference, merged, errors_before, errors_after, rejections) = union_case(nested, true, true);
        assert_eq!((errors_before, errors_after, rejections), (0, 0, 0), "nested={nested}");
        assert_eq!(equivalent_paths(&reference, &merged, 1, true), (2, 1));
        assert!(merged[0].records.iter().any(|record| record.join == crate::ir::regions::RegionPoint::Instruction(4)));
    }
}

#[test]
fn region_merge_poison_slots_unguarded_unwrap_and_default_reject() {
    for (checked, enabled, errors) in [(false, true, 1), (true, false, 0)] {
        let (reference, merged, before, after, rejections) = union_case(false, checked, enabled);
        assert_eq!((before, after, rejections), (errors, errors, 1));
        assert!(merged.iter().all(|path| path.records.is_empty()));
        assert_eq!(equivalent_paths(&reference, &merged, 1, checked), (2 - errors, 2 - errors));
    }
}
