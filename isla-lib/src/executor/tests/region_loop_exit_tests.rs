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
    let counter = test_name(1880);
    let a = test_name(1881);
    let b = test_name(1882);
    let pick_a = test_name(1883);
    let pick_b = test_name(1884);
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
    program.extend((0..12).map(|_| copy(pick_a, Exp::Bool(false))));
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
    let run = |merge, strategy| {
        let mut limits = ExecutionLimits::default().with_path_merging(merge).with_region_loop_analysis(true);
        limits.merge_strategy = strategy;
        segment_paths(program.clone(), &shared, 4, limits, 32, crate::memory::Memory::new(), |frame| {
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
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let inputs: Vec<_> = (0..4).map(|_| solver.declare_const(smtlib::Ty::Bool, info())).collect();
        let (left, _) = import(&on[0], &inputs, &mut solver);
        let (right, _) = import(&on[1], &inputs, &mut solver);
        let overlap = solver.define_const(And(Box::new(left), Box::new(right)), info());
        assert!(solver.check_sat_with(&Var(overlap), info()).is_unsat().unwrap());
    }
}
