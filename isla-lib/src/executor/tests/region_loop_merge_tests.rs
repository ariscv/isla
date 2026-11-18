//! 循环内分叉的差分、槽位和寄存器回归；沿用父模块的真实执行与 SMT 等价判据。
use super::*;

fn paths(instrs: Vec<Instr<Name, B64>>, shared: &SharedState<'static, B64>, inputs: usize, merge: bool) -> Vec<Path> {
    paths_with_state(
        instrs,
        shared,
        inputs,
        ExecutionLimits::default().with_path_merging(merge).with_region_loop_analysis(true),
        crate::memory::Memory::new(),
        |_| (),
    )
}

fn differential(
    instrs: Vec<Instr<Name, B64>>,
    shared: &SharedState<'static, B64>,
    inputs: usize,
    complete: bool,
) -> (usize, usize) {
    let forked = paths(instrs.clone(), shared, inputs, false);
    let merged = paths(instrs, shared, inputs, true);
    if merged.len() == 1 {
        assert!(!merged[0].records.is_empty());
    }
    equivalent_paths(&forked, &merged, inputs, complete)
}

fn loop_program(assertion: Exp<Name>, other: Exp<Name>, jumps: bool, pessimistic: bool) -> Vec<Instr<Name, B64>> {
    let counter = test_name(1100);
    let temporary = test_name(1101);
    let unit = test_name(1102);
    let assertion_instr = |condition| {
        if jumps {
            Instr::Call(Loc::Id(unit), false, SAIL_ASSERT, vec![condition, Exp::String("循环断言".into())], info())
        } else {
            Instr::PrimopBinary(
                Loc::Id(unit),
                primop::binary_primops()[if pessimistic { "pessimistic_assert" } else { "optimistic_assert" }],
                condition,
                Exp::String("循环断言".into()),
                info(),
            )
        }
    };
    let mut definitions = vec![crate::ir::Def::Fn(
        TOP_LEVEL_LET,
        vec![],
        vec![
            Instr::Init(counter, Ty::I64, Exp::I64(0), info()),
            Instr::Decl(unit, Ty::Unit, info()),
            Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(counter), Exp::I64(3)]), 14, info()),
            Instr::Jump(input(0), 9, info()),
            Instr::Decl(temporary, Ty::Bool, info()),
            Instr::Copy(Loc::Id(temporary), input(1), info()),
            assertion_instr(assertion),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(temporary), info()),
            Instr::Goto(11),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            assertion_instr(other),
            Instr::Copy(Loc::Id(counter), Exp::Call(Op::Add, vec![Exp::Id(counter), Exp::I64(1)]), info()),
            Instr::Goto(2),
            Instr::Arbitrary,
            Instr::End,
        ],
    )];
    if jumps {
        crate::ir::assertions_to_jumps(&mut definitions);
    }
    let crate::ir::Def::Fn(_, _, program) = definitions.pop().unwrap() else { unreachable!() };
    program
}

#[test]
fn region_merge_loop_assertion_forms_and_dead_arms_differential() {
    for jumps in [false, true] {
        for (condition, other) in [
            (Exp::Bool(true), Exp::Bool(true)),
            (Exp::Bool(false), Exp::Bool(true)),
            (input(2), Exp::Bool(true)),
            (Exp::Bool(false), Exp::Bool(false)),
            (input(2), input(2).bool_not()),
        ] {
            let mut shared = empty_shared_state();
            shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
            let complete = matches!((&condition, &other), (Exp::Bool(true), Exp::Bool(true)));
            let program = loop_program(condition, other, jumps, false);
            differential(program.clone(), &shared, 3, complete);
            for path in paths(program, &shared, 3, true) {
                assert!(matches!(path.variables.get(&test_name(1100)), Some(UVal::Init(Val::I64(3)))));
                assert!(!path.variables.contains_key(&test_name(1101)), "下一轮声明前可删除临时槽位");
                assert!(
                    path.events.iter().all(|event| !matches!(event, Event::ReadReg(..) | Event::WriteReg(..))),
                    "局部槽位不得转为寄存器访问"
                );
            }
        }
    }
}

#[test]
fn region_merge_loop_pessimistic_symbolic_assertion_is_rejected() {
    for condition in [Exp::Bool(true), Exp::Bool(false), input(2)] {
        let mut shared = empty_shared_state();
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let symbolic = matches!(condition, Exp::Id(_));
        let program = loop_program(condition, Exp::Bool(true), false, true);
        if symbolic {
            let forked = paths(program.clone(), &shared, 3, false);
            let merged = paths(program, &shared, 3, true);
            assert_eq!(equivalent_paths(&forked, &merged, 3, false), (1, 1));
            assert!(merged[0].records.is_empty(), "符号悲观断言必须拒绝整个区域推演");
        } else {
            differential(program, &shared, 3, false);
        }
        if symbolic {
            assert!(shared.execution_stats.merge_json()["failure_reasons"]["symbolic_assertion"].as_u64().unwrap() > 0);
        }
    }
}

#[test]
fn region_merge_loop_base_slot_and_late_entry_preserve_state() {
    for initialized in [false, true] {
        let mut shared = empty_shared_state();
        let register = shared.symtab.intern("zloop_register");
        shared.registers.insert(register, Ty::Bool);
        let temporary = test_name(1101);
        let mut program = loop_program(Exp::Bool(true), Exp::Bool(true), false, false);
        // 前两轮仅执行声明臂，第三轮才以符号条件进入合并。
        let counter = test_name(1100);
        program[3] = Instr::Jump(
            Exp::Call(Op::And, vec![Exp::Call(Op::Eq, vec![Exp::Id(counter), Exp::I64(2)]), input(0)]),
            9,
            info(),
        );
        program[10] = Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info());
        // 两臂给基态已有的同一槽位赋不同布尔值，随后删除不会被允许。
        program[9] = Instr::Copy(Loc::Id(temporary), Exp::Bool(false), info());
        program[14] = Instr::Copy(Loc::Id(register), Exp::Id(temporary), info());
        program.extend([Instr::Copy(Loc::Id(RETURN), Exp::Id(temporary), info()), Instr::End]);
        program.insert(
            0,
            if initialized {
                Instr::Init(temporary, Ty::Bool, Exp::Bool(true), info())
            } else {
                Instr::Decl(temporary, Ty::Bool, info())
            },
        );
        // 插入入口声明后复用指令的标签偏移规则。
        for instr in &mut program[1..] {
            match instr {
                Instr::Jump(_, target, _) | Instr::Goto(target) => *target += 1,
                _ => (),
            }
        }
        assert_eq!(differential(program.clone(), &shared, 3, true), (2, 1));
        let merged = paths(program, &shared, 3, true);
        let path = &merged[0];
        assert!(path.variables.contains_key(&temporary), "基态已有槽位必须保留");
        assert_eq!(path.registers.get_last_if_initialized(register).unwrap(), &path.value);
        assert_eq!(
            path.events
                .iter()
                .filter(|event| matches!(event, Event::WriteReg(name, _, _) if *name == register))
                .count(),
            1
        );
        assert!(!path.events.iter().any(|event| matches!(event, Event::ReadReg(..))), "局部读取不得成为寄存器读取");
    }
}

#[test]
fn region_merge_base_slot_survives_even_when_statically_dead() {
    let shared = empty_shared_state();
    let temporary = test_name(1101);
    let program = vec![
        Instr::Jump(input(0), 4, info()),
        Instr::Decl(temporary, Ty::Bool, info()),
        Instr::Copy(Loc::Id(temporary), Exp::Bool(true), info()),
        Instr::Goto(5),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::End,
    ];
    assert!(crate::ir::regions::FunctionRegions::new(&program, HAVE_EXCEPTION)
        .region(0)
        .unwrap()
        .local_variables
        .contains(&temporary));
    for initialized in [false, true] {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::new(&context);
        let condition = solver.declare_const(smtlib::Ty::Bool, info());
        let mut frame = make_frame(program.clone());
        frame.vars_mut().insert(test_name(900), UVal::Init(Val::Symbolic(condition)));
        frame.vars_mut().insert(RETURN, UVal::Init(Val::Bool(false)));
        frame
            .vars_mut()
            .insert(temporary, if initialized { UVal::Init(Val::Bool(false)) } else { UVal::Uninit(&Ty::Bool) });
        assert!(merge_region_for_test(condition, 4, &mut frame, &shared, &mut solver, info(), None, None)
            .unwrap()
            .is_some());
        let Some(UVal::Init(value)) = frame.vars().get(&temporary) else {
            panic!("基态槽位必须保留并初始化")
        };
        let value = smt_value(value, info()).unwrap();
        use smtlib::Exp::{And, Not, Var};
        assert!(solver
            .check_sat_with(
                &And(Box::new(Not(Box::new(Var(condition)))), Box::new(Not(Box::new(value.clone())))),
                info()
            )
            .is_unsat()
            .unwrap());
        assert!(
            solver.check_sat_with(&And(Box::new(Var(condition)), Box::new(value)), info()).is_sat().unwrap()
                != initialized
        );
        assert!(solver.trace().to_vec().iter().all(|event| !matches!(event, Event::ReadReg(..) | Event::WriteReg(..))));
        assert_eq!(solver.transaction_depth(), 0);
    }
}

#[test]
fn region_merge_assignment_keeps_local_slot_and_register_events() {
    let mut shared = empty_shared_state();
    let slot = shared.symtab.intern("zloop_slot");
    shared.registers.insert(slot, Ty::Bool);
    let program = vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Decl(slot, Ty::Bool, info()),
        Instr::Goto(4),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Copy(Loc::Id(slot), Exp::Bool(false), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
        Instr::End,
    ];
    assert_eq!(differential(program.clone(), &shared, 1, true), (2, 2));
    for merge in [false, true] {
        for path in paths(program.clone(), &shared, 1, merge) {
            let local = path.variables.contains_key(&slot);
            assert_eq!(
                path.events
                    .iter()
                    .filter(|event| matches!(event, Event::WriteReg(name, _, _) if *name == slot))
                    .count(),
                usize::from(!local)
            );
            assert_eq!(
                path.registers.get_last_if_initialized(slot),
                if local { None } else { Some(&Val::Bool(false)) }
            );
        }
    }
}

#[test]
fn region_premerge_review_loop_options_keep_shared_cache_separate() {
    for order in [[false, true, false], [true, false, true]] {
        let shared = empty_shared_state();
        let program = vec![
            Instr::Jump(input(0), 3, info()),
            Instr::Exit(crate::ir::ExitCause::AssertionFailure, info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::End,
        ];
        for enabled in order {
            let result = paths_with_state(
                program.clone(),
                &shared,
                1,
                ExecutionLimits::default().with_path_merging(true).with_region_loop_analysis(enabled),
                crate::memory::Memory::new(),
                |_| (),
            );
            assert_eq!(result.len(), 1);
            assert_eq!(!result[0].records.is_empty(), enabled, "默认旧模式与新模式不能复用对方的区域边界");
        }
        let cache = shared.function_regions.lock().unwrap();
        assert!(cache.contains_key(&(TOP_LEVEL_LET, false)));
        assert!(cache.contains_key(&(TOP_LEVEL_LET, true)));
    }
}

/// 出口可在不同轮次到达，循环头再次分叉，循环体内还有独立分叉。
fn crossing_loop_program(dead: bool) -> Vec<Instr<Name, B64>> {
    let counter = test_name(1150);
    let eq = |n| Exp::Call(Op::Eq, vec![Exp::Id(counter), Exp::I128(n)]);
    vec![
        Instr::Init(counter, Ty::I128, Exp::I128(0), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Jump(
            Exp::Call(
                Op::Or,
                vec![
                    eq(3),
                    Exp::Call(
                        Op::Or,
                        vec![Exp::Call(Op::And, vec![input(0), eq(0)]), Exp::Call(Op::And, vec![input(1), eq(1)])],
                    ),
                ],
            ),
            10,
            info(),
        ),
        Instr::Jump(input(2), 6, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(7),
        if dead {
            Instr::Exit(crate::ir::ExitCause::AssertionFailure, info())
        } else {
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info())
        },
        Instr::PrimopBinary(
            Loc::Id(counter),
            primop::binary_primops()["add_int"],
            Exp::Id(counter),
            Exp::I128(1),
            info(),
        ),
        Instr::Goto(2),
        Instr::Arbitrary,
        Instr::End,
    ]
}

#[test]
fn region_crossing_loop_finite_nested_head_and_dead_arm() {
    for dead in [false, true] {
        let shared = empty_shared_state();
        let program = crossing_loop_program(dead);
        let forked = paths(program.clone(), &shared, 3, false);
        let merged = paths(program, &shared, 3, true);
        equivalent_paths(&forked, &merged, 3, !dead);
        assert_eq!(merged.len(), 1, "不同轮次的出口必须实际合并");
        assert!(merged[0].records.iter().filter(|r| r.branch_pc == 2).count() >= 2, "循环头再次分叉必须产生嵌套记录");
    }
}

#[test]
fn region_crossing_loop_nontermination_rolls_back_inner_commits() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let reg = shared.symtab.intern("zbounded_loop_register");
    shared.registers.insert(reg, Ty::Bool);
    let program = vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(10),
        Instr::Jump(input(1), 6, info()),
        Instr::Copy(Loc::Id(reg), Exp::Bool(false), info()),
        Instr::Goto(7),
        Instr::Copy(Loc::Id(reg), Exp::Bool(true), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
        Instr::Jump(input(2), 10, info()),
        Instr::Goto(3),
        Instr::End,
    ];
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let mut frame = make_frame(program);
    for index in 0..3 {
        let sym = solver.declare_const(smtlib::Ty::Bool, info());
        frame.vars_mut().insert(test_name(900 + index), UVal::Init(Val::Symbolic(sym)));
    }
    solver.assert(smtlib::Exp::Not(Box::new(smtlib::Exp::Var(Sym { id: 2 }))));
    frame.regs_mut().insert(reg, false, UVal::Init(Val::Bool(false)));
    let before_vars = format!("{:?}", frame.vars());
    let before_events = solver.trace().to_vec().len();
    let state = TaskState::new().with_region_step_budget(80).with_execution_limits(
        ExecutionLimits::default()
            .with_path_merging(true)
            .with_region_loop_analysis(true)
            .with_region_global_state(true),
    );
    let queue = Worker::new_lifo();
    let mut fraction = Fraction::one();
    let result = region_merge::try_region(
        Sym { id: 0 },
        3,
        0,
        TaskId::fresh(),
        &mut fraction,
        PathTimeout::unlimited(),
        None,
        &SingleForkSink { queue: &queue },
        &mut frame,
        &state,
        &shared,
        &mut solver,
        info(),
    )
    .unwrap();
    assert!(matches!(result, region_merge::RegionResult::Rejected));
    assert!(shared.execution_stats.merge_json()["failure_reasons"]["step_budget"].as_u64().unwrap() > 0);
    assert!(shared.execution_stats.merge_json()["successes"].as_u64().unwrap() > 0);
    assert_eq!(frame.pc, 0);
    assert_eq!(format!("{:?}", frame.vars()), before_vars);
    assert_eq!(frame.regs().get_last_if_initialized(reg), Some(&Val::Bool(false)));
    assert!(frame.region_merge_records().is_empty());
    assert!(frame.region_execution.is_none());
    assert!(frame.local_state.speculative_access.is_none());
    assert_eq!(solver.transaction_depth(), 0);
    assert_eq!(solver.trace().to_vec().len(), before_events);
    assert!(queue.is_empty());
    assert!(fraction.is_one());
    assert!(solver.check_sat_with(&smtlib::Exp::Var(Sym { id: 0 }), info()).is_sat().unwrap());
    assert!(solver
        .check_sat_with(&smtlib::Exp::Not(Box::new(smtlib::Exp::Var(Sym { id: 0 }))), info())
        .is_sat()
        .unwrap());
}

#[test]
fn region_crossing_loop_budget_rejection_preserves_complete_execution() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let program = crossing_loop_program(false);
    let forked = paths(program.clone(), &shared, 3, false);
    for budget in [0, 12] {
        let successes_before = shared.execution_stats.merge_json()["successes"].as_u64().unwrap();
        let rejected_before =
            shared.execution_stats.merge_json()["failure_reasons"]["step_budget"].as_u64().unwrap_or(0);
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::new(&context);
        let mut frame = make_frame(program.clone());
        frame.function_name = TOP_LEVEL_LET;
        for index in 0..3 {
            let symbol = solver.declare_const(smtlib::Ty::Bool, info());
            frame.vars_mut().insert(test_name(900 + index), UVal::Init(Val::Symbolic(symbol)));
        }
        let state = TaskState::new()
            .with_region_step_budget(budget)
            .with_execution_limits(ExecutionLimits::default().with_path_merging(true).with_region_loop_analysis(true));
        let output = Mutex::new(Vec::new());
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            &shared,
            &output,
            &|_, _, result, _, mut solver, output| {
                let Ok((Run::Finished(value), frame)) = result else {
                    panic!("合并预算耗尽后普通执行必须完整完成");
                };
                assert_eq!(solver.transaction_depth(), 0);
                assert!(frame.region_execution.is_none());
                if solver.check_sat(info()).is_sat().unwrap() {
                    output.lock().unwrap().push(Path {
                        exception: frame.get_exception().map(|(value, _)| value.clone()),
                        records: frame.region_merge_records().to_vec(),
                        value,
                        events: solver.trace().to_vec().into_iter().rev().cloned().collect(),
                        variables: frame.vars().clone(),
                        registers: frame.regs().clone(),
                        lets: frame.lets().clone(),
                        checkpoint: checkpoint(&mut solver),
                    });
                }
            },
        );
        equivalent_paths(&forked, &output.into_inner().unwrap(), 3, true);
        if budget == 0 {
            assert!(
                shared.execution_stats.merge_json()["failure_reasons"]["step_budget"].as_u64().unwrap()
                    > rejected_before
            );
        } else {
            // 预算按完整轮续配；12足以容纳本夹具一轮，不能再要求累计预算失败。
            assert_eq!(
                shared.execution_stats.merge_json()["failure_reasons"]["step_budget"].as_u64().unwrap(),
                rejected_before
            );
            assert!(shared.execution_stats.merge_json()["successes"].as_u64().unwrap() > successes_before);
        }
    }
}

#[test]
fn region_crossing_loop_no_join_and_mode_cache_isolation() {
    use crate::ir::regions::{FunctionRegions, RegionOptions, RegionRejection};
    for body in [
        vec![Instr::Jump(input(0), 0, info()), Instr::Goto(0)],
        vec![Instr::Jump(input(0), 2, info()), Instr::Goto(1), Instr::End],
        vec![
            Instr::Jump(input(0), 2, info()),
            Instr::Exit(crate::ir::ExitCause::AssertionFailure, info()),
            Instr::Exit(crate::ir::ExitCause::AssertionFailure, info()),
        ],
    ] {
        let options = RegionOptions { bounded_loops: true, filter_assertion_failures: true, ..Default::default() };
        assert_eq!(FunctionRegions::<B64>::with_options(&body, options).region(0), Err(RegionRejection::NoJoin));
    }
    for order in [[false, true, false], [true, false, true]] {
        let shared = empty_shared_state();
        let program = crossing_loop_program(false);
        assert_eq!(FunctionRegions::new(&program, HAVE_EXCEPTION).region(2), Err(RegionRejection::HasBackEdge));
        for enabled in order {
            let result = paths_with_state(
                program.clone(),
                &shared,
                3,
                ExecutionLimits::default().with_path_merging(true).with_region_loop_analysis(enabled),
                crate::memory::Memory::new(),
                |_| (),
            );
            assert_eq!(result.iter().any(|path| path.records.iter().any(|record| record.branch_pc == 2)), enabled);
        }
        let mut cache = shared.function_regions.lock().unwrap();
        assert_eq!(cache.get_mut(&(TOP_LEVEL_LET, false)).unwrap().region(2), Err(RegionRejection::HasBackEdge));
        assert!(cache.get_mut(&(TOP_LEVEL_LET, true)).unwrap().region(2).unwrap().has_back_edge);
    }
}

/// 布尔输入定义有限但符号的循环上界，差分时仍共享完全相同的外部输入。
fn bounded_iteration_paths(program: Vec<Instr<Name, B64>>, groups: &[usize], expected_value: usize) -> Vec<Path> {
    use smtlib::Exp::{And, Bits, Bool, Bvadd, Ite, Neq, Not, Var};
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let mut frame = make_frame(program);
    frame.function_name = TOP_LEVEL_LET;
    let mut index = 0;
    let constant = |n: u128| Bits((0..128).map(|bit| n & (1u128 << bit) != 0).collect());
    for (group, bits) in groups.iter().enumerate() {
        let mut bound = constant(0);
        for bit in 0..*bits {
            let input = solver.declare_const(smtlib::Ty::Bool, info());
            frame.vars_mut().insert(test_name(900 + index), UVal::Init(Val::Symbolic(input)));
            index += 1;
            bound = Bvadd(
                Box::new(bound),
                Box::new(Ite(Box::new(Var(input)), Box::new(constant(1 << bit)), Box::new(constant(0)))),
            );
        }
        let bound = solver.define_const(bound, info());
        frame.vars_mut().insert(test_name(1200 + group as u32), UVal::Init(Val::Symbolic(bound)));
    }
    let state = TaskState::new()
        .with_execution_limits(ExecutionLimits::default().with_path_merging(true).with_region_loop_analysis(true));
    frame.pc = 1;
    frame.vars_mut().insert(test_name(1210), UVal::Init(Val::I128(0)));
    frame.vars_mut().insert(RETURN, UVal::Init(Val::Bool(false)));
    let UVal::Init(Val::Symbolic(bound)) = frame.vars()[&test_name(1200)].clone() else { unreachable!() };
    let condition = solver.define_const(smtlib::Exp::Eq(Box::new(Var(bound)), Box::new(constant(0))), info());
    let Instr::Jump(_, target, _) = frame.instrs[1] else { unreachable!() };
    let shared = empty_shared_state();
    let queue = Worker::new_lifo();
    let sink = SingleForkSink { queue: &queue };
    let mut fraction = Fraction::one();
    let result = region_merge::try_region(
        condition,
        target,
        0,
        TaskId::fresh(),
        &mut fraction,
        PathTimeout::unlimited(),
        None,
        &sink,
        &mut frame,
        &state,
        &shared,
        &mut solver,
        info(),
    )
    .unwrap();
    assert!(matches!(result, region_merge::RegionResult::Merged), "整个有限循环必须一次合并，不能靠普通执行掩盖拒绝");
    let Run::Finished(value) = run_loop(
        0,
        TaskId::fresh(),
        &mut fraction,
        PathTimeout::unlimited(),
        None,
        &sink,
        &mut frame,
        &state,
        &shared,
        &mut solver,
    )
    .unwrap() else {
        panic!("合并之后必须返回")
    };
    assert!(queue.is_empty());
    // 直接使用原求解器保留共享表达式；不把深层定义DAG递归展开成树。
    let inputs: Vec<_> = (0..index)
        .map(|index| {
            let UVal::Init(Val::Symbolic(symbol)) = frame.vars()[&test_name(900 + index)] else { unreachable!() };
            symbol
        })
        .collect();
    let ideal = inputs[..groups[0]].iter().enumerate().fold(Bool(true), |formula, (bit, symbol)| {
        And(
            Box::new(formula),
            Box::new(if expected_value & (1 << bit) != 0 { Var(*symbol) } else { Not(Box::new(Var(*symbol))) }),
        )
    });
    assert!(solver
        .check_sat_with(&Neq(Box::new(smt_value(&value, info()).unwrap()), Box::new(ideal)), info())
        .is_unsat()
        .unwrap());
    // 输入域仅由这些布尔量组成；逐个组合可满足即证明没有丢弃任意输入。
    for assignment in 0..(1usize << inputs.len()) {
        let guard = inputs.iter().enumerate().fold(Bool(true), |formula, (bit, symbol)| {
            And(
                Box::new(formula),
                Box::new(if assignment & (1 << bit) != 0 { Var(*symbol) } else { Not(Box::new(Var(*symbol))) }),
            )
        });
        assert!(solver.check_sat_with(&guard, info()).is_sat().unwrap(), "有限输入组合不得被合并过滤");
    }

    vec![Path {
        exception: None,
        records: frame.region_merge_records().to_vec(),
        value,
        events: solver.trace().to_vec().into_iter().rev().cloned().collect(),
        variables: frame.vars().clone(),
        registers: frame.regs().clone(),
        lets: frame.lets().clone(),
        checkpoint: checkpoint(&mut solver),
    }]
}

#[test]
fn region_loop_rounds_many_iterations_use_one_level() {
    let counter = test_name(1210);
    let bound = test_name(1200);
    let program = vec![
        Instr::Init(counter, Ty::I128, Exp::I128(0), info()),
        Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(counter), Exp::Id(bound)]), 4, info()),
        Instr::PrimopBinary(
            Loc::Id(counter),
            primop::binary_primops()["add_int"],
            Exp::Id(counter),
            Exp::I128(1),
            info(),
        ),
        Instr::Goto(1),
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(counter), Exp::I128(42)]), info()),
        Instr::End,
    ];
    let merged = bounded_iteration_paths(program, &[6], 42);
    assert!(merged[0].records.iter().filter(|record| record.branch_pc == 1).count() > 32);
    assert!(merged[0].records.iter().all(|record| record.depth == 1), "后续轮次复用本循环层数");
}

#[test]
fn region_loop_rounds_nested_loops_keep_distinct_levels() {
    let outer = test_name(1210);
    let inner = test_name(1211);
    let program = vec![
        Instr::Init(outer, Ty::I128, Exp::I128(0), info()),
        Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(outer), Exp::Id(test_name(1200))]), 9, info()),
        Instr::Init(inner, Ty::I128, Exp::I128(0), info()),
        Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(inner), Exp::Id(test_name(1201))]), 6, info()),
        Instr::PrimopBinary(Loc::Id(inner), primop::binary_primops()["add_int"], Exp::Id(inner), Exp::I128(1), info()),
        Instr::Goto(3),
        Instr::PrimopBinary(Loc::Id(outer), primop::binary_primops()["add_int"], Exp::Id(outer), Exp::I128(1), info()),
        Instr::Goto(1),
        Instr::Arbitrary,
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(outer), Exp::I128(2)]), info()),
        Instr::End,
    ];
    let merged = bounded_iteration_paths(program, &[2, 5], 2);
    assert_eq!(merged.len(), 1);
    assert!(merged[0].records.iter().filter(|record| record.branch_pc == 1).all(|record| record.depth == 1));
    assert!(merged[0].records.iter().filter(|record| record.branch_pc == 3).all(|record| record.depth == 2));
    assert!(merged[0].records.iter().any(|record| record.branch_pc == 3));
}

#[test]
fn region_merge_unlimited_budget_applies_to_independent_loop_rounds() {
    let mut code = crossing_loop_program(false);
    let extra = 10_000;
    for instr in &mut code {
        match instr {
            Instr::Jump(_, target, _) | Instr::Goto(target) if *target >= 8 => *target += extra,
            _ => (),
        }
    }
    code.splice(8..8, (0..extra).map(|_| Instr::Copy(Loc::Id(RETURN), input(0), info())));
    let forked = paths(code.clone(), &empty_shared_state(), 3, false);
    for budget in [None, Some(8192), Some(-1)] {
        let mut shared = empty_shared_state();
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let config = crate::config::ExecutionLimitsConfig {
            path_merge: crate::config::PathMergeConfig {
                enabled: Some(true),
                step_budget: budget,
                ..Default::default()
            },
            ..Default::default()
        };
        let limits = ExecutionLimits::default()
            .with_config(&config, &shared.symtab)
            .with_region_loop_analysis(true)
            .with_region_global_state(true);
        let merged = paths_with_state(code.clone(), &shared, 3, limits, crate::memory::Memory::new(), |_| ());
        equivalent_paths(&forked, &merged, 3, true);
        let failures = shared.execution_stats.merge_json()["failure_reasons"]["step_budget"].as_u64().unwrap_or(0);
        if budget == Some(8192) {
            assert!(failures > 0, "{:?}", shared.execution_stats.merge_json());
        } else {
            assert_eq!(failures, 0);
            assert_eq!(merged.len(), 1);
            assert!(!merged[0].records.is_empty());
        }
    }
}
