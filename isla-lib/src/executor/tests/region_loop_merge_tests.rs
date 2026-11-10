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
