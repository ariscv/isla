//! 用首次命中的扫描循环检验折叠触发、终态与有序写入。
use super::*;

#[derive(Clone, Copy, Debug, PartialEq)]
enum Shape {
    Reverse,
    Nested,
    Register,
    Ram,
    Read,
}

fn compare(shape: Shape, compact: bool, expanded: bool) {
    crate::config::RegionOptions { prefix_compact: compact, loop_fold_shapes: expanded, ..Default::default() }
        .configure();
    for n in [4, 16] {
        let mut shared = empty_shared_state();
        let reg = shared.symtab.intern("zround");
        shared.registers.insert(reg, Ty::I128);
        let counter = test_name(1800);
        let choices = test_name(1801);
        let choice = test_name(1802);
        let data = test_name(1803);
        let bytes = test_name(1804);
        let stored = test_name(1805);
        let ram = test_name(1806);
        let nested_choices = test_name(1807);
        let mut program = scan_program(counter, choices, choice, n, None);
        program[7] = Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(counter), Exp::I128(1)]), info());
        program[9] = Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info());
        match shape {
            Shape::Reverse => {
                program[3] = Instr::Jump(Exp::Id(choice).bool_not(), 7, info());
                program.swap(4, 7);
                program.swap(5, 8);
            }
            Shape::Nested => {
                program[4] = Instr::Jump(Exp::Id(choice), 10, info());
                program[5] = Instr::PrimopBinary(
                    Loc::Id(counter),
                    primop::binary_primops()["add_int"],
                    Exp::Id(counter),
                    Exp::I128(1),
                    info(),
                );
                program[6] = Instr::Goto(1);
                program[1] = Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(counter), Exp::I128(n as i128)]), 10, info());
                program[3] = Instr::Jump(Exp::Id(choice), 8, info());
                program[8] = Instr::Goto(12);
                program[10] = Instr::Goto(12);
                program.insert(
                    4,
                    Instr::PrimopBinary(
                        Loc::Id(choice),
                        primop::binary_primops()["vector_access"],
                        Exp::Id(nested_choices),
                        Exp::Id(counter),
                        info(),
                    ),
                );
            }
            Shape::Read => {
                // 继续臂读取同一入口值。后续轮次继承该访问及其守卫。
                program[5] = Instr::Copy(Loc::Id(choice), Exp::Call(Op::Eq, vec![Exp::Id(reg), Exp::I128(-1)]), info());
                program[6] = Instr::Goto(1);
            }
            Shape::Register | Shape::Ram => {
                let ops = if shape == Shape::Register {
                    vec![Instr::Copy(Loc::Id(reg), Exp::Id(counter), info())]
                } else {
                    vec![
                        Instr::PrimopBinary(
                            Loc::Id(data),
                            primop::binary_primops()["vector_access"],
                            Exp::Id(bytes),
                            Exp::Id(counter),
                            info(),
                        ),
                        Instr::PrimopVariadic(
                            Loc::Id(stored),
                            primop::variadic_primops()["platform_write_mem"],
                            vec![
                                Exp::Unit,
                                Exp::I128(64),
                                Exp::Bits(B64::new(0x1000, 64)),
                                Exp::I128(1),
                                Exp::Id(data),
                            ],
                            info(),
                        ),
                    ]
                };
                for item in &mut program {
                    match item {
                        Instr::Jump(_, pc, _) | Instr::Goto(pc) if *pc >= 2 => *pc += ops.len(),
                        _ => (),
                    }
                }
                program.splice(2..2, ops);
            }
        }
        let inputs = if shape == Shape::Nested { 2 * n } else { n };
        let prefix: MergeHistory<_> =
            vec![super::super::super::merge_history_tests::record(region_merge::next_region_record())].into();
        let run = |merge| {
            segment_paths_with_solver(
                program.clone(),
                &shared,
                inputs,
                ExecutionLimits::default()
                    .with_path_merging(merge)
                    .with_region_loop_analysis(true)
                    .with_region_global_state(true),
                512,
                crate::memory::Memory::new(),
                |frame, solver| {
                    let values = (0..n)
                        .map(|i| {
                            let UVal::Init(value) = &frame.vars()[&test_name(900 + i as u32)] else { unreachable!() };
                            value.clone()
                        })
                        .collect();
                    frame.vars_mut().insert(choices, UVal::Init(Val::Vector(values)));
                    frame.vars_mut().insert(choice, UVal::Uninit(&Ty::Bool));
                    if shape == Shape::Nested {
                        let extra = (n..inputs)
                            .map(|i| {
                                let UVal::Init(v) = &frame.vars()[&test_name(900 + i as u32)] else { unreachable!() };
                                v.clone()
                            })
                            .collect();
                        frame.vars_mut().insert(nested_choices, UVal::Init(Val::Vector(extra)));
                    }
                    frame.regs_mut().assign(reg, Val::I128(-1), &shared);
                    frame.region_merge_records = prefix.clone();
                    if shape == Shape::Ram {
                        frame.vars_mut().insert(data, UVal::Init(Val::Bits(B64::new(0, 8))));
                        frame.vars_mut().insert(
                            bytes,
                            UVal::Init(Val::Vector((1..=n).map(|i| Val::Bits(B64::new(i as u64, 8))).collect())),
                        );
                        frame.vars_mut().insert(stored, UVal::Init(Val::Bool(false)));
                        frame.memory_mut().add_concrete_region(0x1000..0x1001, HashMap::new());
                        crate::memory::install_seq_memory(frame.memory_mut(), 64, solver, false);
                    }
                },
                move |frame, path| {
                    if let Some(version) = frame.memory.ram_version() {
                        path.variables.insert(ram, UVal::Init(Val::Symbolic(version)));
                    }
                },
            )
        };
        let plain = run(false);
        region_merge::FOLD_SAMPLES.replace(Some(Vec::new()));
        let merged = run(true);
        equivalent_paths(&plain, &merged, inputs, true);
        equivalent_register_paths(&plain, &merged, inputs);
        if shape == Shape::Ram {
            for paths in [&plain, &merged] {
                check_ram(paths, n, ram);
            }
        }
        let samples = region_merge::FOLD_SAMPLES.take().unwrap();
        for (round, values) in samples.iter().enumerate() {
            eprintln!("pf_round {shape:?} {n} {compact} {expanded} {} {values:?}", round + 1);
        }
        let rounds = samples.len();
        eprintln!("{shape:?} n={n} compact={compact} expanded={expanded} rounds={rounds}");
        if expanded || shape == Shape::Register {
            assert_eq!(rounds, n - 1, "每次再次遇到循环入口都应折叠");
            assert_eq!(merged.len(), 1);
            if shape == Shape::Read {
                check_read_guard(&merged[0], n, reg);
                assert!(samples.iter().any(|s| s[2] > 0), "读载荷夹具必须实际产生受守卫保护的读取");
            }
            if compact && n == 16 {
                // 比较稳定轮次，不用固定容量作为执行器准入条件。
                for index in [0, 1, 2, 3, 4, 5] {
                    assert_eq!(samples[3][index], samples.last().unwrap()[index], "指标 {index} 随轮数增长");
                }
            }
        }
    }
}

fn check_read_guard(path: &Path, n: usize, reg: Name) {
    use smtlib::Exp::*;
    let ctx = Context::new(Config::new());
    let mut verify = Solver::new(&ctx);
    let inputs: Vec<_> = (0..n).map(|_| verify.declare_const(smtlib::Ty::Bool, info())).collect();
    let guard = path
        .records
        .iter()
        .flat_map(|r| r.single_arm_reads.iter())
        .filter(|read| read.register == reg)
        .fold(Bool(false), |a, r| Or(Box::new(a), Box::new(r.guard.clone())));
    let (_, values) = import_values(path, &inputs, &mut verify, &[guard]);
    let expected = Not(Box::new(Var(inputs[0])));
    assert!(verify.check_sat_with(&Neq(Box::new(values[0].clone()), Box::new(expected)), info()).is_unsat().unwrap());
}

fn check_ram(paths: &[Path], n: usize, ram: Name) {
    use crate::smt::smtlib::{bits64, Exp::*};
    let ctx = Context::new(Config::new());
    for hit in 0..=n {
        let mut matches = 0;
        for path in paths {
            let mut solver = Solver::from_checkpoint(&ctx, path.checkpoint.clone());
            let count = (hit + 1).min(n);
            for i in 0..count {
                solver.assert(Eq(Box::new(Var(Sym::from_u32(i as u32))), Box::new(Bool(i == hit))));
            }
            if solver.check_sat(info()).is_unsat().unwrap() {
                continue;
            }
            matches += 1;
            let UVal::Init(Val::Symbolic(mem)) = path.variables[&ram] else { unreachable!() };
            let byte = Select(Box::new(Var(mem)), Box::new(bits64(0x1000, 64)));
            assert!(solver
                .check_sat_with(&Neq(Box::new(byte), Box::new(bits64(count as u64, 8))), info())
                .is_unsat()
                .unwrap());
            let mut writes = Vec::new();
            for (event, guard) in path.checkpoint.trace().as_ref().unwrap().events_with_guards_rev() {
                if let Event::WriteMem { data, address, bytes, .. } = event {
                    if let Some(guard) = guard {
                        if solver.check_sat_with(guard, info()).is_unsat().unwrap() {
                            continue;
                        }
                        assert!(solver.check_sat_with(&Not(Box::new(guard.clone())), info()).is_unsat().unwrap());
                    }
                    assert_eq!(address, &Val::Bits(B64::new(0x1000, 64)));
                    assert_eq!(*bytes, 1);
                    writes.push(data.clone());
                }
            }
            writes.reverse();
            assert_eq!(writes, (1..=count).map(|i| Val::Bits(B64::new(i as u64, 8))).collect::<Vec<_>>());
        }
        assert_eq!(matches, 1);
    }
}

macro_rules! case {
    ($name:ident,$shape:ident,$compact:literal,$expanded:literal) => {
        #[test]
        fn $name() {
            if run_in_diagnostics_process(concat!(module_path!(), "::", stringify!($name))) {
                run_deep_region_test(|| compare(Shape::$shape, $compact, $expanded));
            }
        }
    };
}
case!(reverse, Reverse, true, true);
case!(nested, Nested, true, true);
case!(register, Register, true, true);
case!(ram, Ram, true, true);
case!(reverse_full, Reverse, false, true);
case!(nested_full, Nested, false, true);
case!(register_full, Register, false, true);
case!(ram_full, Ram, false, true);
case!(baseline_ram, Ram, false, false);
case!(register_independent, Register, true, false);

#[test]
fn incompatible_exits_preserve_disjoint_groups() {
    if run_in_diagnostics_process(concat!(module_path!(), "::incompatible_exits_preserve_disjoint_groups")) {
        crate::config::RegionOptions { prefix_compact: true, loop_fold_shapes: true, ..Default::default() }.configure();
        run_deep_region_test(super::loop_segment_failed_exit_merge_does_not_submit_a_continuation);
    }
}

case!(read, Read, true, true);
case!(read_full, Read, false, true);

#[test]
fn compact_single_root_and_verify_parent_metadata() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let record = super::super::super::merge_history_tests::record;
    let ctx = Context::new(Config::new());
    let mut solver = Solver::new(&ctx);
    let mut base = make_frame(vec![Instr::End]);
    let mut prefix = record(0);
    prefix.parent_record = Some(10);
    prefix.arm = "then";
    base.region_merge_records = vec![prefix, record(10)].into();
    let mut hidden: Vec<_> = (20..84).map(record).collect();
    hidden.extend(base.region_merge_records.iter().cloned());
    hidden.push(record(90));
    let mut current = base.clone();
    current.region_merge_records.clear();
    current.region_merge_records.append_suffix(&hidden.into(), 64);
    current.region_merge_records.compact_loop_suffix(&base.region_merge_records, true, &mut solver, info());
    assert!(current.region_merge_records.retained_record_slots() < 64);
    assert!(std::ptr::eq(&base.region_merge_records[0], current.region_merge_records.iter().next().unwrap()));

    current.region_merge_records.edit_occurrences(0, |r| {
        (r.record_id == 0).then(|| {
            let mut changed = r.clone();
            changed.arm = "else";
            changed
        })
    });
    current.region_merge_records.push(record(91));
    current.region_merge_records.compact_loop_suffix(&base.region_merge_records, true, &mut solver, info());
    assert_eq!(current.region_merge_records.iter().next().unwrap().arm, "else");
    assert_eq!(current.region_merge_records.len(), 4);
}
