//! 联合载荷与局部槽的汇合验证，涵盖返回关系、覆盖和活跃 Poison 错误。
use super::super::nested_merge_failure_tests::{strategies, Strategy};
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
    let defaults = crate::config::ExecutionLimitsConfig::default();
    assert!(defaults.path_merge.merge_poison_slots);
    let explicit_off = toml::from_str("[path_merge]\nmerge_poison_slots=false").unwrap();
    for (config, enabled) in [(None, true), (Some(&defaults), true), (Some(&explicit_off), false)] {
        let limits = ExecutionLimits::for_symbolic_dag(config, &shared.symtab);
        assert!(limits.path_merging);
        assert_eq!(limits.merge_poison_slots, enabled);
    }

    for strategy in strategies() {
        let run = |limits| paths_with_state(program.clone(), &shared, 1, limits, crate::memory::Memory::new(), |_| ());
        let mut limits = strategy.limits();
        let default = run(limits.clone());
        assert_eq!(equivalent_paths(&reference, &default, 1, true), (2, 1), "{strategy:?}");
        assert!(default[0].records.iter().any(|record| record.branch_pc == 1), "{strategy:?}");

        limits.merge_poison_slots = false;
        let disabled = run(limits);
        assert_eq!(equivalent_paths(&reference, &disabled, 1, true), (2, 2), "{strategy:?}");
        assert!(disabled.iter().all(|path| path.records.is_empty()), "{strategy:?}");
    }
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
    for strategy in strategies() {
        shared.execution_stats.reset();
        let mut limits = strategy.limits();
        limits.merge_poison_slots = true;
        let results = paths_with_state(program.clone(), &shared, 1, limits, crate::memory::Memory::new(), |_| ());
        assert_eq!(results.len(), 2, "{strategy:?}");
        assert!(results.iter().all(|path| path.records.is_empty()), "{strategy:?}");
        assert_eq!(
            shared.execution_stats.merge_json()["failure_reasons"]["SpeculativeRejectReason::IncompatibleState"],
            1,
            "{strategy:?}"
        );
        assert!(results.iter().any(|path| path.value == Val::Poison), "{strategy:?}");
    }
}

fn union_case(
    strategy: Strategy,
    nested: bool,
    checked: bool,
    enabled: bool,
) -> (Vec<Path>, Vec<Path>, usize, usize, u64) {
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

    let run = |limits| {
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
    let (reference, reference_errors, _) = run(ExecutionLimits::default().with_path_merging(false));
    let mut limits = strategy.limits();
    limits.merge_poison_slots = enabled;
    let (merged, merged_errors, _) = run(limits);
    (
        reference,
        merged,
        reference_errors,
        merged_errors,
        shared.execution_stats.merge_json()["failure_reasons"]["SpeculativeRejectReason::UnionPayload"]
            .as_u64()
            .unwrap_or(0),
    )
}

#[test]
fn region_merge_poison_slots_guarded_union_and_nested_union() {
    for strategy in strategies() {
        for nested in [false, true] {
            let (reference, merged, errors_before, errors_after, rejections) = union_case(strategy, nested, true, true);
            assert_eq!((errors_before, errors_after, rejections), (0, 0, 0), "{strategy:?}, nested={nested}");
            assert_eq!(equivalent_paths(&reference, &merged, 1, true), (2, 1), "{strategy:?}, nested={nested}");
            assert!(merged[0].records.iter().any(|record| record.branch_pc == 0), "{strategy:?}, nested={nested}");
        }
    }
}

#[test]
fn region_merge_poison_slots_unguarded_unwrap_and_default_reject() {
    for strategy in strategies() {
        for (checked, enabled, errors) in [(false, true, 1), (true, false, 0)] {
            let (reference, merged, before, after, rejections) = union_case(strategy, false, checked, enabled);
            assert_eq!((before, after, rejections), (errors, errors, 1), "{strategy:?}, checked={checked}");
            assert!(merged.iter().all(|path| path.records.is_empty()), "{strategy:?}, checked={checked}");
            assert_eq!(equivalent_paths(&reference, &merged, 1, checked), (2 - errors, 2 - errors), "{strategy:?}");
        }
    }
}
