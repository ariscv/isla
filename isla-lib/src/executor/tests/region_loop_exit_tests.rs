use super::loop_segment_tests::{equivalent_scalar_paths, scan_paths_with_limits};
use super::*;

#[test]
fn region_loop_exit_keeps_register_writes_across_rounds_with_small_budget() {
    let mut shared = empty_shared_state();
    let register = shared.symtab.intern("zloop_exit_state");
    shared.registers.insert(register, Ty::I128);
    let limits = ExecutionLimits::default();
    let off = scan_paths_with_limits(&shared, 8, 40, Some(register), limits.clone());
    assert_eq!(off.len(), 9);
    for strategy in [crate::config::MergeStrategy::Recursive, crate::config::MergeStrategy::Flat] {
        let mut on_limits = limits.clone().with_path_merging(true);
        on_limits.merge_strategy = strategy;
        let on = scan_paths_with_limits(&shared, 8, 40, Some(register), on_limits);
        assert_eq!(on.len(), 1, "同一循环的各轮返回必须到达同一出口");
        equivalent_scalar_paths(&off, &on, 8);
        equivalent_register_paths(&off, &on, 8);
    }
}

#[test]
fn region_loop_exit_budget_publishes_one_task_per_guarded_continuation() {
    use super::loop_segment_tests::segment_paths;
    use smtlib::Exp::{And, Var};

    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let [a, b, pick_a, pick_b] = [1881, 1882, 1883, 1884].map(test_name);
    let program = budget_segment_program(a, b, pick_a, pick_b);
    let memory = budget_segment_memory();
    let run = |merge, strategy| {
        let mut limits = ExecutionLimits::default().with_path_merging(merge).with_region_loop_analysis(true);
        limits.merge_strategy = strategy;
        segment_paths(program.clone(), &shared, 4, limits, 32, memory.clone(), |frame| {
            let input_value = |index: u32| match frame.vars()[&test_name(900 + index)] {
                UVal::Init(ref value) => value.clone(),
                _ => panic!("输入须初始化"),
            };
            let left = vec![input_value(0), input_value(2)];
            let right = vec![input_value(1), input_value(3)];
            frame.vars_mut().insert(a, UVal::Init(Val::Vector(left)));
            frame.vars_mut().insert(b, UVal::Init(Val::Vector(right)));
            for slot in [pick_a, pick_b] {
                frame.vars_mut().insert(slot, UVal::Uninit(&Ty::Bool));
            }
        })
    };
    let off = run(false, crate::config::MergeStrategy::Recursive);
    assert_eq!(off.len(), 5);
    for strategy in [crate::config::MergeStrategy::Recursive, crate::config::MergeStrategy::Flat] {
        shared.execution_stats.reset();
        let on = run(true, strategy);
        assert_eq!(on.len(), 2);
        equivalent_scalar_paths(&off, &on, 4);
        assert!(on.iter().any(|path| path.records.iter().any(|record| {
            record.join == crate::ir::regions::RegionPoint::Instruction(15) && !record.memory_reads.is_empty()
        })));
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let inputs: Vec<_> = (0..4).map(|_| solver.declare_const(smtlib::Ty::Bool, info())).collect();
        let (left, _) = import(&on[0], &inputs, &mut solver);
        let (right, _) = import(&on[1], &inputs, &mut solver);
        let overlap = solver.define_const(And(Box::new(left), Box::new(right)), info());
        assert!(solver.check_sat_with(&Var(overlap), info()).is_unsat().unwrap());
    }
}

// 同轮两个仍能提前退出的分支，使循环不得在第一次回边直接折叠。
fn budget_segment_program(a: Name, b: Name, pick_a: Name, pick_b: Name) -> Vec<Instr<Name, B64>> {
    let counter = test_name(1880);
    let var = |name| Exp::Id(name);
    let copy = |id, value| Instr::Copy(Loc::Id(id), value, info());
    let at = |dest, choices| {
        Instr::PrimopBinary(
            Loc::Id(dest),
            primop::binary_primops()["vector_access"],
            var(choices),
            var(counter),
            info(),
        )
    };
    let mut program = vec![
        Instr::Init(counter, Ty::I128, Exp::I128(0), info()),
        Instr::Jump(Exp::Call(Op::Eq, vec![var(counter), Exp::I128(2)]), 22, info()),
    ];
    program.extend([Instr::Decl(pick_a, Ty::Bool, info()), Instr::Decl(pick_b, Ty::Bool, info())]);
    let read = test_name(1886);
    program.push(copy(pick_a, Exp::Bool(false)));
    program.push(Instr::Decl(read, Ty::Bits(8), info()));
    program.push(Instr::PrimopVariadic(
        Loc::Id(read),
        primop::variadic_primops()["platform_read_mem"],
        vec![Exp::Unit, Exp::I128(64), Exp::Bits(B64::new(0x1000, 64)), Exp::I128(1)],
        info(),
    ));
    program.extend((0..7).map(|_| copy(pick_a, Exp::Bool(false))));
    program.extend([
        at(pick_a, a), // 14
        Instr::Jump(var(pick_a), 24, info()),
        at(pick_b, b),
        Instr::Jump(var(pick_b), 26, info()),
        Instr::PrimopBinary(Loc::Id(counter), primop::binary_primops()["add_int"], var(counter), Exp::I128(1), info()),
        Instr::Goto(1),
        Instr::Arbitrary,
        Instr::Arbitrary,
        copy(RETURN, Exp::I128(2)), // 22
        Instr::Goto(28),
        copy(RETURN, Exp::I128(0)),
        Instr::Goto(28),
        copy(RETURN, Exp::I128(1)),
        Instr::Goto(28),
        Instr::End,
    ]);
    program
}

fn budget_segment_memory() -> crate::memory::Memory<B64> {
    let mut memory = crate::memory::Memory::new();
    memory.add_concrete_region(0x1000..0x1002, HashMap::from([(0x1000, 7), (0x1001, 0)]));
    memory
}

#[test]
fn region_loop_exit_nested_budget_returns_both_frontiers_to_parent() {
    if !run_in_diagnostics_process(concat!(
        module_path!(),
        "::region_loop_exit_nested_budget_returns_both_frontiers_to_parent"
    )) {
        return;
    }
    use super::loop_segment_tests::{equivalent_scalar_paths_for_inputs, segment_paths_with_solver};
    let [a, b, pick_a, pick_b, ignored, wrote] = [1881, 1882, 1883, 1884, 1885, 1887].map(test_name);
    for depth in [3, 4] {
        let mut shared = empty_shared_state();
        let loop_code = budget_segment_program(a, b, pick_a, pick_b);
        let memory = crate::memory::Memory::new();
        let loop_fn = shared.symtab.intern("znested_budget_segment_loop");
        let vector_ty: &'static Ty<Name> = Box::leak(Box::new(Ty::FixedVector(2, Box::new(Ty::Bool))));
        let inputs = (0..depth - 1).map(|index| test_name(1890 + index as u32)).collect::<Vec<_>>();
        let args = [a, b].into_iter().map(Exp::Id).chain(inputs.iter().copied().map(Exp::Id)).collect::<Vec<_>>();
        let params = [(a, &*vector_ty), (b, &*vector_ty)]
            .into_iter()
            .chain(inputs.iter().map(|&name| (name, &Ty::Bool)))
            .collect::<Vec<_>>();
        shared.functions.insert(loop_fn, (params.clone(), &Ty::I128, Box::leak(loop_code.into_boxed_slice())));
        let wrapper = |callee, condition, index, fail| {
            let mut code = vec![
                Instr::Jump(condition, 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::I128(-1 - index as i128), info()),
                Instr::Goto(0),
            ];
            if index == 0 {
                // 父层已做 RAM 写入，本循环层只有读取，仍然可以分段。
                code.extend([
                    Instr::Decl(wrote, Ty::Bool, info()),
                    Instr::PrimopVariadic(
                        Loc::Id(wrote),
                        primop::variadic_primops()["platform_write_mem"],
                        vec![
                            Exp::Unit,
                            Exp::I128(64),
                            Exp::Bits(B64::new(0x1001, 64)),
                            Exp::I128(1),
                            Exp::Bits(B64::new(9, 8)),
                        ],
                        info(),
                    ),
                ]);
            }
            code.push(Instr::Call(Loc::Id(RETURN), false, callee, args.clone(), info()));
            if fail {
                code.extend([
                    Instr::Decl(ignored, Ty::Unit, info()),
                    Instr::PrimopReset(
                        Loc::Id(ignored),
                        Arc::new(|_, _, solver| {
                            if solver.transaction_depth() > 0 {
                                Err(ExecError::Unimplemented)
                            } else {
                                Ok(Val::Unit)
                            }
                        }),
                        primop::Effect::Pure,
                        info(),
                    ),
                ]);
            }
            code[2] = Instr::Goto(code.len());
            code.push(Instr::End);
            code
        };
        let mut inner = loop_fn;
        for (index, &input) in inputs.iter().enumerate().skip(1).rev() {
            let name = shared.symtab.intern(
                ["znested_budget_segment_root", "znested_budget_segment_first", "znested_budget_segment_second"][index],
            );
            let code = wrapper(inner, Exp::Id(input), index, false);
            shared.functions.insert(name, (params.clone(), &Ty::I128, Box::leak(code.into_boxed_slice())));
            inner = name;
        }
        let run = |merge, strategy, fail| {
            let mut limits = ExecutionLimits::default().with_path_merging(merge).with_region_loop_analysis(true);
            limits.merge_strategy = strategy;
            let program = wrapper(inner, Exp::Id(inputs[0]), 0, fail);
            segment_paths_with_solver(
                program,
                &shared,
                4 + inputs.len(),
                limits,
                44,
                memory.clone(),
                |frame, solver| {
                    crate::memory::install_seq_memory(frame.memory_mut(), 64, solver, false);
                    let input = |i| {
                        let UVal::Init(value) = &frame.vars()[&test_name(900 + i)] else { unreachable!() };
                        value.clone()
                    };
                    let left = Val::Vector(vec![input(0), input(2)]);
                    let right = Val::Vector(vec![input(1), input(3)]);
                    let guards = inputs
                        .iter()
                        .enumerate()
                        .map(|(index, &name)| (name, input(4 + index as u32)))
                        .collect::<Vec<_>>();
                    for (name, value) in [(a, left), (b, right)].into_iter().chain(guards) {
                        frame.vars_mut().insert(name, UVal::Init(value));
                    }
                },
                |_, _| {},
            )
        };
        use crate::config::MergeStrategy::{Flat, Recursive};
        let plain = run(false, Recursive, false);
        assert_eq!(plain.len(), 5 + inputs.len());
        let check_returns = |paths: &[Path]| {
            // 初始 RAM 数组和布尔选择位同属所有路径共享的输入。
            use smtlib::Ty::{Array, BitVec, Bool};
            let ram = Array(Box::new(BitVec(64)), Box::new(BitVec(8)));
            equivalent_scalar_paths_for_inputs(&plain, paths, std::iter::repeat_n(Bool, 4 + inputs.len()).chain([ram]));
        };
        for strategy in [Recursive, Flat] {
            stats::merge_diagnostics::configure("summary").unwrap();
            let merged = run(true, strategy, false);
            check_returns(&merged);
            let count_segments = || {
                let timing = stats::merge_timing::summary_for_test();
                timing["outcomes"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|row| row["outcome"] == "segmented")
                    .map_or((0, 0), |row| {
                        (row["root"]["count"].as_u64().unwrap(), row["inclusive"]["count"].as_u64().unwrap())
                    })
            };
            let (root, all) = count_segments();
            assert!(root == 0 && all > 0, "{depth} 层 {strategy:?}：必须发生父事务内的分段，实际为 {root}/{all}");
            assert_eq!(
                merged.len(),
                1,
                "{depth} 层 {strategy:?}：父层必须继续汇合退出与继续片段，实际 {}",
                stats::merge_timing::summary_for_test()["outcomes"],
            );
            assert!(merged[0]
                .records
                .iter()
                .any(|record| record.function == TOP_LEVEL_LET && record.outcome == RegionRecordOutcome::Merged));
            stats::merge_diagnostics::configure("summary").unwrap();
            let replayed = run(true, strategy, true);
            check_returns(&replayed);
            assert!(replayed.iter().flat_map(|path| &path.records).all(|record| record.function != TOP_LEVEL_LET));
            let (root, all) = count_segments();
            assert!(all > root, "外层拒绝发生前必须完整经历一次内层分段");

            let ancestor_guards = ((1u32 << inputs.len()) - 1) << 4;
            for (mask, expected) in
                [(ancestor_guards | 1, [1, 1]), (ancestor_guards | 4, [2, 1]), (ancestor_guards, [2, 1]), (0, [0, 0])]
            {
                for paths in [&plain, &merged, &replayed] {
                    assert_eq!(
                        guarded_memory_accesses(paths, 4 + inputs.len(), mask),
                        expected,
                        "每轮的读取事件和父层写入只能生成一次",
                    );
                }
            }
        }
    }
}

fn guarded_memory_accesses(paths: &[Path], inputs: usize, mask: u32) -> [usize; 2] {
    use smtlib::Exp::{Bool, Not, Var};
    let context = Context::new(Config::new());
    let mut reached = Vec::new();
    for path in paths {
        let mut solver = Solver::from_checkpoint(&context, path.checkpoint.clone());
        for index in 0..u32::try_from(inputs).unwrap() {
            solver.assert_eq(Var(Sym::from_u32(index)), Bool(mask & (1 << index) != 0));
        }
        if solver.check_sat(info()).is_unsat().unwrap() {
            continue;
        }
        let mut counts = [0; 2];
        for (event, guard) in path.checkpoint.trace().as_ref().unwrap().events_with_guards_rev() {
            let kind = match event {
                Event::ReadMem { .. } => 0,
                Event::WriteMem { .. } => 1,
                _ => continue,
            };
            if let Some(guard) = guard {
                if solver.check_sat_with(guard, info()).is_unsat().unwrap() {
                    continue;
                }
                assert!(solver.check_sat_with(&Not(Box::new(guard.clone())), info()).is_unsat().unwrap());
            }
            counts[kind] += 1;
        }
        reached.push(counts);
    }
    assert_eq!(reached.len(), 1, "同一输入只能落入一个完成路径");
    reached[0]
}
