//! 联合载荷与局部槽的汇合验证，涵盖返回关系、覆盖和活跃 Poison 错误。
use super::super::nested_merge_failure_tests::{strategies, Strategy};
use super::*;

fn assert_projected_fragments(paths: &[Path], branch_pc: usize) {
    use smtlib::Exp::{Not, Var};

    let context = Context::new(Config::new());
    let mut recorded = HashSet::new();
    for path in paths {
        let root = path
            .records
            .iter()
            .find(|record| record.branch_pc == branch_pc && record.parent_record.is_none() && !record.dead)
            .expect("未合并的出口片段应保留自己的根投影记录");
        assert!(recorded.insert(root.record_id), "不同出口片段不得共用根投影记录");
        let mut solver = Solver::from_checkpoint(&context, path.checkpoint.clone());
        assert!(
            solver.check_sat_with(&Not(Box::new(Var(root.condition))), info()).is_unsat().unwrap(),
            "片段守卫必须蕴含它自己的根投影条件"
        );
    }
}

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
        let reason = SpeculativeRejectReason::IncompatibleState.to_string();
        let rejections = || shared.execution_stats.merge_json()["failure_reasons"][&reason].as_u64().unwrap_or(0);
        let run = |limits| paths_with_state(program.clone(), &shared, 1, limits, crate::memory::Memory::new(), |_| ());
        let mut limits = strategy.limits();
        shared.execution_stats.reset();
        let default = run(limits.clone());
        assert_eq!(equivalent_paths(&reference, &default, 1, true), (2, 1), "{strategy:?}");
        assert_eq!(rejections(), 0, "{strategy:?}");
        assert!(default[0].records.iter().any(|record| record.branch_pc == 1), "{strategy:?}");

        limits.merge_poison_slots = false;
        shared.execution_stats.reset();
        let disabled = run(limits);
        assert_eq!(equivalent_paths(&reference, &disabled, 1, true), (2, 2), "{strategy:?}");
        assert_eq!(rejections(), 1, "{strategy:?}");
        assert_projected_fragments(&disabled, 1);
    }
}

#[test]
fn region_merge_poison_slots_live_local_rejects() {
    use smtlib::Exp::{Not, Var};

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
        assert_projected_fragments(&results, 1);
        let reason = SpeculativeRejectReason::IncompatibleState.to_string();
        assert_eq!(shared.execution_stats.merge_json()["failure_reasons"][reason], 1, "{strategy:?}");
        let context = Context::new(Config::new());
        let mut poison_paths = 0;
        for path in results {
            let input = Var(Sym::from_u32(0));
            let wrong_input = if path.value == Val::Poison {
                poison_paths += 1;
                Not(Box::new(input))
            } else {
                assert_eq!(path.value, Val::String("before".into()), "{strategy:?}");
                input
            };
            let mut solver = Solver::from_checkpoint(&context, path.checkpoint);
            assert!(solver.check_sat_with(&wrong_input, info()).is_unsat().unwrap(), "{strategy:?}");
        }
        assert_eq!(poison_paths, 1, "{strategy:?}");
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
        shared.execution_stats.merge_json()["failure_reasons"][SpeculativeRejectReason::UnionPayload.to_string()]
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
            assert_eq!(equivalent_paths(&reference, &merged, 1, checked), (2 - errors, 2 - errors), "{strategy:?}");
            assert_projected_fragments(&merged, 0);
        }
    }
}

#[test]
fn region_merge_poison_slots_ptwalk_nested_ppn() {
    use crate::smt::Model;

    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let union = shared.symtab.intern("zptw_result");
    let ok = shared.symtab.intern("zptw_ok");
    let err = shared.symtab.intern("zptw_err");
    let tuple = shared.symtab.intern("zptw_tuple");
    let output = shared.symtab.intern("zptw_output");
    let field = shared.symtab.intern("zptw_output_field");
    let ppn = shared.symtab.intern("zptw_ppn");
    let slot = shared.symtab.intern("zptw_result_slot");
    let ready = shared.symtab.intern("zptw_result_ready");
    let reg = shared.symtab.intern("zptw_register");
    let wrote = shared.symtab.intern("zptw_wrote");
    let loaded = shared.symtab.intern("zptw_loaded");
    shared.type_info.structs.insert(output, BTreeMap::from([(ppn, Ty::AnyBits)]));
    shared.type_info.structs.insert(tuple, BTreeMap::from([(field, Ty::Struct(output))]));
    shared.type_info.unions.insert(union, vec![(ok, Ty::Struct(tuple)), (err, Ty::Unit)]);
    shared.registers.insert(reg, Ty::Bool);

    let bits = |value, width| Exp::Bits(B64::new(value, width));
    let copy = |dst, value| Instr::Copy(Loc::Id(dst), value, info());
    let mem = || vec![Exp::Unit, Exp::I128(64), bits(0x1000, 64), Exp::I128(1)];
    let store = |value| {
        let mut args = mem();
        args.push(bits(value, 8));
        Instr::PrimopVariadic(Loc::Id(wrote), primop::variadic_primops()["platform_write_mem"], args, info())
    };
    let prefix = vec![
        Instr::Decl(slot, Ty::Union(union), info()),
        Instr::Jump(input(0), 5, info()),
        copy(reg, Exp::Bool(false)),
        store(0x11),
        Instr::Goto(8),
        copy(slot, Exp::Id(ready)),
        copy(reg, Exp::Bool(true)),
        store(0x22),
    ];
    let mut dead = prefix.clone();
    dead.extend([
        copy(slot, Exp::Id(ready)),
        Instr::PrimopVariadic(Loc::Id(loaded), primop::variadic_primops()["platform_read_mem"], mem(), info()),
        copy(RETURN, Exp::Call(Op::Eq, vec![Exp::Id(loaded), bits(0x22, 8)])),
        Instr::End,
    ]);
    let mut live = prefix;
    let selected = Exp::Unwrap(ok, Box::new(Exp::Id(slot)));
    let read_ppn = Exp::Field(Box::new(Exp::Field(Box::new(selected), field)), ppn);
    live.extend([
        Instr::Jump(Exp::Kind(ok, Box::new(Exp::Id(slot))), 11, info()),
        Instr::PrimopBinary(Loc::Id(RETURN), primop::binary_primops()["eq_bits"], read_ppn, bits(0, 44), info()),
        Instr::Goto(12),
        copy(RETURN, Exp::Bool(false)),
        Instr::End,
    ]);
    let run = |program: &[Instr<Name, B64>], limits| {
        shared.function_regions.lock().unwrap().clear();
        shared.execution_stats.reset();
        let (paths, errors, _) = paths_with_solver_state(
            program.to_vec(),
            &shared,
            1,
            limits,
            crate::memory::Memory::new(),
            |frame, solver| {
                let tag = solver.define_const(ok.to_smt(), info());
                let ppn_value = Val::Symbolic(solver.define_bitvector(smtlib::bits64(0, 44), info()));
                let output_value = Val::Struct([(ppn, ppn_value)].into_iter().collect());
                let payload = Val::Struct([(field, output_value)].into_iter().collect());
                let value = Val::SymbolicCtor(tag, [(ok, payload), (err, Val::Unit)].into_iter().collect());
                frame.vars_mut().insert(ready, UVal::Init(value));
                frame.vars_mut().insert(wrote, UVal::Uninit(&Ty::Bool));
                frame.vars_mut().insert(loaded, UVal::Uninit(&Ty::Bits(8)));
                frame.memory_mut().add_symbolic_region(0x1000..0x1001);
                crate::memory::install_seq_memory(frame.memory_mut(), 64, solver, false);
            },
            true,
        );
        let reason = SpeculativeRejectReason::UnionPayload.to_string();
        let rejections = shared.execution_stats.merge_json()["failure_reasons"][reason].as_u64().unwrap_or(0);
        (paths, errors, rejections)
    };

    let plain = ExecutionLimits::default().with_path_merging(false);
    let (reference, 0, 0) = run(&dead, plain.clone()) else { panic!("未合并的覆盖夹具必须完整执行") };
    let (_, 1, 0) = run(&live, plain) else { panic!("可观察的未初始化 ppn 必须保留错误路径") };
    for strategy in strategies() {
        let limits = strategy.limits().with_region_global_state(true);
        let (merged, errors, rejections) = run(&dead, limits.clone());
        assert_eq!((errors, rejections), (0, 0), "{strategy:?}");
        assert_eq!(equivalent_paths(&reference, &merged, 1, true), (2, 1), "{strategy:?}");
        assert!(merged[0].records.iter().any(|record| record.branch_pc == 1), "{strategy:?}");
        equivalent_register_paths(&reference, &merged, 1);

        for paths in [&reference, &merged] {
            let context = Context::new(Config::new());
            let mut checked = 0;
            for path in paths {
                for direction in [false, true] {
                    let mut solver = Solver::from_checkpoint(&context, path.checkpoint.clone());
                    let branch = smtlib::Exp::Var(Sym::from_u32(0));
                    solver.assert(if direction { branch } else { smtlib::Exp::Not(Box::new(branch)) });
                    if solver.check_sat(info()).is_unsat().unwrap() {
                        continue;
                    }
                    checked += 1;
                    let trace: Vec<_> = solver
                        .trace()
                        .events_with_guards_rev()
                        .map(|(ev, guard)| (ev.clone(), guard.cloned()))
                        .collect();
                    let mut model = Model::new(&mut solver);
                    model.set_complete_model(true);
                    let mut access = Vec::new();
                    for (event, guard) in trace.into_iter().rev() {
                        if guard.is_some_and(|guard| {
                            model.get_exp(&guard).unwrap().unwrap_exp() == smtlib::Exp::Bool(false)
                        }) {
                            continue;
                        }
                        match event {
                            Event::ReadMem { address, value, bytes, .. } => {
                                access.push((
                                    false,
                                    model.get_val(&address).unwrap(),
                                    bytes,
                                    model.get_val(&value).unwrap(),
                                ));
                            }
                            Event::WriteMem { address, data, bytes, .. } => {
                                access.push((
                                    true,
                                    model.get_val(&address).unwrap(),
                                    bytes,
                                    model.get_val(&data).unwrap(),
                                ));
                            }
                            _ => (),
                        }
                    }
                    let address = Val::Bits(B64::new(0x1000, 64));
                    let byte = Val::Bits(B64::new(if direction { 0x22 } else { 0x11 }, 8));
                    assert_eq!(access, [(true, address.clone(), 1, byte.clone()), (false, address, 1, byte)]);
                }
            }
            assert_eq!(checked, 2);
        }

        let (_, errors, rejections) = run(&live, limits);
        assert_eq!((errors, rejections), (1, 1), "{strategy:?}");
    }
}
