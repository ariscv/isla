//! M2 的全局状态差分与事件检查；寄存器名称和结构均不依赖具体架构。
use super::*;

fn diamond(
    then_arm: Vec<Instr<Name, B64>>,
    else_arm: Vec<Instr<Name, B64>>,
    tail: Vec<Instr<Name, B64>>,
) -> Vec<Instr<Name, B64>> {
    let target = else_arm.len() + 2;
    let join = target + then_arm.len();
    let mut program = vec![Instr::Jump(input(0), target, info())];
    program.extend(else_arm);
    program.push(Instr::Goto(join));
    program.extend(then_arm);
    program.extend(tail);
    program
}

fn run(
    program: Vec<Instr<Name, B64>>,
    shared: &SharedState<'static, B64>,
    inputs: usize,
    merge: bool,
    configure: impl FnOnce(&mut LocalFrame<'static, B64>),
) -> Vec<Path> {
    paths_with_state(
        program,
        shared,
        inputs,
        ExecutionLimits::default().with_path_merging(merge).with_region_global_state(true),
        crate::memory::Memory::new(),
        |frame| {
            frame.vars_mut().insert(RETURN, UVal::Init(Val::Bool(false)));
            // 差分两侧使用同一个具体前态；符号前态由程序中的输入赋值覆盖。
            for (name, ty) in &shared.registers {
                if matches!(ty, Ty::Bool) {
                    frame.regs_mut().assign(*name, Val::Bool(false), shared);
                }
            }
            configure(frame);
        },
    )
}

fn check(program: Vec<Instr<Name, B64>>, shared: &SharedState<'static, B64>, inputs: usize) -> Vec<Path> {
    let forked = run(program.clone(), shared, inputs, false, |_| ());
    let merged = run(program, shared, inputs, true, |_| ());
    assert_eq!(equivalent_paths(&forked, &merged, inputs, true), (2, 1));
    assert!(!merged[0].records.is_empty());
    equivalent_register_paths(&forked, &merged, inputs);
    merged
}

fn finish() -> Vec<Instr<Name, B64>> {
    vec![Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()), Instr::End]
}

#[test]
fn region_m2_nested_unread_preservation_shares_one_initial() {
    let mut shared = empty_shared_state();
    let reg = shared.symtab.intern("zstate");
    let function = shared.symtab.intern("zconditional_write");
    let parameter = test_name(993);
    shared.registers.insert(reg, Ty::Bool);
    let body = vec![
        Instr::Jump(Exp::Id(parameter), 2, info()),
        Instr::Goto(3),
        Instr::Copy(Loc::Id(reg), Exp::Bool(false), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
        Instr::End,
    ];
    shared.functions.insert(function, (vec![(parameter, &Ty::Bool)], &Ty::Unit, Box::leak(body.into_boxed_slice())));
    let arm = vec![Instr::Call(Loc::Id(RETURN), false, function, vec![input(1)], info())];
    let merged = paths_with_state(
        diamond(arm.clone(), arm, finish()),
        &shared,
        2,
        ExecutionLimits::default().with_path_merging(true).with_region_global_state(true),
        crate::memory::Memory::new(),
        |_| (),
    );
    assert_eq!(merged.len(), 1);
    let initials: Vec<_> = merged[0]
        .events
        .iter()
        .filter_map(|event| match event {
            Event::AssumeReg(name, _, value) if *name == reg => Some(value),
            _ => None,
        })
        .collect();
    assert!(!initials.is_empty());
    assert!(
        initials.iter().all(|value| *value == initials[0]),
        "两外臂内的保留状态必须引用同一个入口初值：{initials:?}"
    );
}

#[test]
fn region_m2_retained_unread_initial_is_published_without_read_event() {
    let mut shared = empty_shared_state();
    let reg = shared.symtab.intern("zstate");
    shared.registers.insert(reg, Ty::Bool);
    let program = diamond(vec![Instr::Copy(Loc::Id(reg), Exp::Bool(false), info())], vec![], finish());
    let merged = paths_with_state(
        program,
        &shared,
        1,
        ExecutionLimits::default().with_path_merging(true).with_region_global_state(true),
        crate::memory::Memory::new(),
        |_| (),
    );
    assert_eq!(merged.len(), 1);
    assert!(!merged[0].events.iter().any(|event| matches!(event, Event::ReadReg(..))));
    assert!(
        merged[0].events.iter().any(
            |event| matches!(event, Event::AssumeReg(name, path, Val::Symbolic(_)) if *name == reg && path.is_empty())
        ),
        "未活动臂保留的初值必须成为显式输入，不能伪造架构读取"
    );
}

#[test]
fn region_m2_long_finite_callee_preserves_masked_state_in_one_path() {
    for (steps, expected_paths) in [(4200, 1), (9000, 2)] {
        let mut shared = empty_shared_state();
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let reg = shared.symtab.intern("zstate");
        let function = shared.symtab.intern("zlong_finite_body");
        let temporary = test_name(992);
        shared.registers.insert(reg, Ty::Bool);
        // 真实长臂可跨多层算术与回调；有限直线调用不能在尾部反复退回掩码分叉。
        let mut body = vec![Instr::Decl(temporary, Ty::Bool, info())];
        body.extend((0..steps).map(|_| Instr::Copy(Loc::Id(temporary), Exp::Bool(true), info())));
        body.extend([
            Instr::Copy(Loc::Id(reg), Exp::Bool(true), info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Unit, info()),
            Instr::End,
        ]);
        shared.functions.insert(function, (vec![], &Ty::Unit, Box::leak(body.into_boxed_slice())));
        let program = diamond(
            vec![Instr::Call(Loc::Id(RETURN), false, function, vec![], info())],
            vec![Instr::Copy(Loc::Id(RETURN), Exp::Unit, info())],
            vec![Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()), Instr::End],
        );
        let forked = run(program.clone(), &shared, 1, false, |_| ());
        let merged = run(program, &shared, 1, true, |_| ());
        assert_eq!(
            equivalent_paths(&forked, &merged, 1, true),
            (2, expected_paths),
            "{}",
            shared.execution_stats.merge_json()
        );
        equivalent_register_paths(&forked, &merged, 1);
        assert_eq!(merged[0].records.len(), usize::from(expected_paths == 1));
    }
}

#[test]
fn region_m2_vector_update_preflight_and_merge() {
    let shared = empty_shared_state();
    let vector = test_name(990);
    let updated = test_name(991);
    let update = |index| {
        vec![
            // 沿用区域局部槽位规则：向量在臂内消费，汇合点保留布尔返回值。
            Instr::Decl(updated, Ty::Vector(Box::new(Ty::Bool)), info()),
            Instr::PrimopVariadic(
                Loc::Id(updated),
                primop::variadic_primops()["vector_update"],
                vec![Exp::Id(vector), Exp::I128(index), Exp::Bool(true)],
                info(),
            ),
            Instr::PrimopBinary(
                Loc::Id(RETURN),
                primop::binary_primops()["vector_access"],
                Exp::Id(updated),
                Exp::I128(0),
                info(),
            ),
        ]
    };
    let program = diamond(update(0), update(1), vec![Instr::End]);
    let summaries = region_summary::function_effect_summaries(&shared, true);
    for (pc, instruction) in program.iter().enumerate() {
        assert!(region_summary::instruction_effect(TOP_LEVEL_LET, pc, instruction, &shared, &summaries).is_none());
    }
    let initial = Val::Vector(vec![Val::Bool(false), Val::Bool(false)]);
    let configure = |frame: &mut LocalFrame<'static, B64>| {
        frame.vars_mut().insert(vector, UVal::Init(initial.clone()));
    };
    let forked = run(program.clone(), &shared, 1, false, configure);
    let merged = run(program, &shared, 1, true, configure);
    assert_eq!(equivalent_paths(&forked, &merged, 1, true), (2, 1));
    assert_eq!(merged[0].records.len(), 1, "必须实际提交区域合并");
    assert!(!merged[0].variables.contains_key(&updated));
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let condition = solver.declare_const(smtlib::Ty::Bool, info());
    let (_, actual) = import(&merged[0], &[condition], &mut solver);
    assert!(
        solver
            .check_sat_with(&smtlib::Exp::Neq(Box::new(actual), Box::new(smtlib::Exp::Var(condition))), info())
            .is_unsat()
            .unwrap(),
        "索引 0 的最终值必须等于分支条件"
    );
}

#[test]
fn region_m2_vector_update_live_after_join() {
    let shared = empty_shared_state();
    let vector = test_name(990);
    let update = |index| {
        vec![Instr::PrimopVariadic(
            Loc::Id(vector),
            primop::variadic_primops()["vector_update"],
            vec![Exp::Id(vector), Exp::I128(index), Exp::Bool(true)],
            info(),
        )]
    };
    let program = diamond(
        update(0),
        update(1),
        vec![
            Instr::PrimopBinary(
                Loc::Id(RETURN),
                primop::binary_primops()["vector_access"],
                Exp::Id(vector),
                Exp::I128(0),
                info(),
            ),
            Instr::End,
        ],
    );
    let configure = |frame: &mut LocalFrame<'static, B64>| {
        frame.vars_mut().insert(vector, UVal::Init(Val::Vector(vec![Val::Bool(false), Val::Bool(false)])));
    };
    let forked = run(program.clone(), &shared, 1, false, configure);
    let merged = run(program, &shared, 1, true, configure);
    assert_eq!(equivalent_paths(&forked, &merged, 1, true), (2, 1));
    assert_eq!(merged[0].records.len(), 1, "汇合后读取的向量必须逐元素保留分支选择");
}

fn check_vector_update_error_rollback(symbolic_index: bool) {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let reg = shared.symtab.intern("zstate");
    shared.registers.insert(reg, Ty::Bool);
    let vector = test_name(990);
    let index_name = test_name(991);
    let temporary = test_name(992);
    let program = diamond(
        vec![
            Instr::Copy(Loc::Id(reg), Exp::Bool(true), info()),
            Instr::Decl(temporary, Ty::Bool, info()),
            Instr::PrimopUnary(Loc::Id(temporary), primop::unary_primops()["not"], input(0), info()),
            Instr::PrimopVariadic(
                Loc::Id(vector),
                primop::variadic_primops()["vector_update"],
                vec![Exp::Id(vector), Exp::Id(index_name), Exp::Bool(true)],
                info(),
            ),
        ],
        vec![],
        finish(),
    );
    let mut frame = make_frame(program);
    frame.regs_mut().insert(reg, false, UVal::Init(Val::Bool(false)));
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let condition = solver.declare_const(smtlib::Ty::Bool, info());
    let index = solver.declare_const(smtlib::Ty::BitVec(128), info());
    let initial = Val::Vector(vec![Val::Bool(false), Val::Bool(false)]);
    let index_value = if symbolic_index { Val::Symbolic(index) } else { Val::I128(2) };
    frame.vars_mut().insert(test_name(900), UVal::Init(Val::Symbolic(condition)));
    frame.vars_mut().insert(vector, UVal::Init(initial.clone()));
    frame.vars_mut().insert(index_name, UVal::Init(index_value.clone()));
    // 先证实输入确实触发目标错误，再检查完整区域事务的拒绝和回滚。
    let error = primop::vector_update(
        vec![initial.clone(), index_value.clone(), Val::Bool(true)],
        &mut solver,
        &mut frame,
        info(),
    )
    .unwrap_err();
    if symbolic_index {
        assert!(matches!(error, ExecError::SymbolicLength("vector_update", _)));
    } else {
        assert!(matches!(error, ExecError::OutOfBounds("vector_update")));
    }
    let before = solver.trace().to_vec().len();
    let state = TaskState::new()
        .with_execution_limits(ExecutionLimits::default().with_path_merging(true).with_region_global_state(true));
    let queue = Worker::new_lifo();
    let mut fraction = Fraction::one();
    let outcome = region_merge::try_region(
        condition,
        2,
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
    assert!(matches!(outcome, region_merge::RegionResult::Rejected));
    let report = shared.execution_stats.merge_json();
    assert_eq!(report["candidate_attempts"], 1, "必须通过静态预检并在运行时拒绝");
    let reason = if symbolic_index { "retry_operand" } else { "incompatible_state" };
    assert_eq!(report["failure_reasons"][reason], 1);
    assert_eq!(solver.transaction_depth(), 0);
    assert_eq!(solver.trace().to_vec().len(), before, "回滚不得泄漏定义和寄存器事件");
    assert_eq!(frame.pc, 0);
    assert_eq!(frame.regs().get_last_if_initialized(reg), Some(&Val::Bool(false)));
    let UVal::Init(actual_vector) = &frame.vars()[&vector] else { panic!("向量必须保持初始化") };
    let UVal::Init(actual_index) = &frame.vars()[&index_name] else { panic!("索引必须保持初始化") };
    assert_eq!(*actual_vector, initial);
    assert_eq!(*actual_index, index_value);
    assert!(!frame.vars().contains_key(&temporary));
    assert!(frame.region_merge_records().is_empty());
    assert!(frame.region_execution.is_none());
    assert!(frame.local_state.speculative_access.is_none());
    assert!(frame.pending_retry_operand.is_none());
    assert!(queue.is_empty());
    assert!(fraction.is_one());
    // 两侧分支与合法、越界索引仍能任意组合，证明回滚没有缩小输入域。
    for branch in [false, true] {
        for concrete_index in [0, 2] {
            let constraint = smtlib::Exp::And(
                Box::new(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(condition)), Box::new(smtlib::Exp::Bool(branch)))),
                Box::new(smtlib::Exp::Eq(
                    Box::new(smtlib::Exp::Var(index)),
                    Box::new(crate::primop_util::smt_i128(concrete_index)),
                )),
            );
            assert!(solver.check_sat_with(&constraint, info()).is_sat().unwrap());
        }
    }
}

#[test]
fn region_m2_vector_update_symbolic_length_rollback() {
    check_vector_update_error_rollback(true);
}

#[test]
fn region_m2_vector_update_out_of_bounds_rollback() {
    check_vector_update_error_rollback(false);
}

#[test]
fn region_m2_vector_update_invalid_index_retains_arguments() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let mut frame = make_frame(vec![Instr::End]);
    let args = vec![Val::Vector(vec![Val::Bool(false)]), Val::Bool(true), Val::Bool(false)];
    let error = primop::vector_update(args.clone(), &mut solver, &mut frame, info()).unwrap_err();
    let ExecError::Type(message, location) = error else { panic!("非法索引类型必须返回类型错误") };
    assert_eq!(location, info());
    assert!(message.contains(&format!("{args:?}")), "类型错误必须保留全部实参：{message}");
}

#[test]
fn region_m2_callee_register_and_global_let_writes() {
    let mut shared = empty_shared_state();
    let reg = shared.symtab.intern("zstate");
    let global = shared.symtab.intern("zglobal");
    shared.registers.insert(reg, Ty::Bool);
    let callee = helper(&mut shared);
    let argument = shared.functions[&callee].0[0].0;
    shared.functions.get_mut(&callee).unwrap().2 = Box::leak(
        vec![
            Instr::Copy(Loc::Id(reg), Exp::Id(argument), info()),
            Instr::Copy(Loc::Id(global), Exp::Id(argument), info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(global), info()),
            Instr::End,
        ]
        .into_boxed_slice(),
    );
    let program = diamond(
        vec![Instr::Call(Loc::Id(RETURN), false, callee, vec![input(1)], info())],
        vec![Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info())],
        vec![Instr::End],
    );
    let configure = |frame: &mut LocalFrame<'static, B64>| {
        frame.lets_mut().insert(global, UVal::Init(Val::Bool(false)));
    };
    let forked = run(program.clone(), &shared, 2, false, configure);
    let merged = run(program, &shared, 2, true, configure);
    assert_eq!(equivalent_paths(&forked, &merged, 2, true), (2, 1));
    equivalent_register_paths(&forked, &merged, 2);
    let path = &merged[0];
    assert!(matches!(path.value, Val::Symbolic(_)), "返回值必须保留臂条件");
    let UVal::Init(global_value) = &path.lets[&global] else { panic!("全局 let 必须初始化") };
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let inputs: Vec<_> = (0..2).map(|_| solver.declare_const(smtlib::Ty::Bool, info())).collect();
    let (_, values) = import_values(
        path,
        &inputs,
        &mut solver,
        &[
            smt_value(&path.value, info()).unwrap(),
            smt_value(path.registers.get_last_if_initialized(reg).unwrap(), info()).unwrap(),
            smt_value(global_value, info()).unwrap(),
        ],
    );
    for value in &values[1..] {
        assert!(solver
            .check_sat_with(&smtlib::Exp::Neq(Box::new(values[0].clone()), Box::new(value.clone())), info())
            .is_unsat()
            .unwrap());
    }
    assert!(!path.events.iter().any(|event| matches!(event, Event::ReadReg(..))));
    assert_eq!(path.events.iter().filter(|event| matches!(event, Event::WriteReg(..))).count(), 1);
}

#[test]
fn region_m2_repeated_write_and_internal_read() {
    let mut shared = empty_shared_state();
    let reg = shared.symtab.intern("zstate");
    shared.registers.insert(reg, Ty::Bool);
    let program = diamond(
        vec![
            Instr::Copy(Loc::Id(reg), Exp::Bool(false), info()),
            Instr::Copy(Loc::Id(reg), input(1), info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
        ],
        vec![Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info())],
        vec![Instr::End],
    );
    let paths = check(program, &shared, 2);
    assert!(!paths[0].events.iter().any(|event| matches!(event, Event::ReadReg(..))));
    assert_eq!(paths[0].events.iter().filter(|event| matches!(event, Event::WriteReg(..))).count(), 1);
}

#[test]
fn region_m2_unrelated_read_after_write_and_first_write_order() {
    let mut shared = empty_shared_state();
    let a = shared.symtab.intern("za");
    let b = shared.symtab.intern("zb");
    let c = shared.symtab.intern("zc");
    for reg in [a, b, c] {
        shared.registers.insert(reg, Ty::Bool);
    }
    let read = Instr::Copy(Loc::Id(RETURN), Exp::Id(c), info());
    let write = |reg, value| Instr::Copy(Loc::Id(reg), Exp::Bool(value), info());
    let paths = check(
        diamond(
            vec![write(a, false), read.clone(), write(b, true), write(a, true), read.clone()],
            vec![read.clone(), read],
            finish(),
        ),
        &shared,
        1,
    );
    assert_eq!(
        paths[0].events.iter().filter(|event| matches!(event, Event::ReadReg(reg, _, _) if *reg == c)).count(),
        1
    );
    let writes: Vec<_> = paths[0]
        .events
        .iter()
        .filter_map(|event| match event {
            Event::WriteReg(reg, _, _) => Some(*reg),
            _ => None,
        })
        .collect();
    assert_eq!(writes, vec![a, b]);
}

#[test]
fn region_m2_callee_address_and_other_write_effects_stay_in_summary() {
    let mut shared = empty_shared_state();
    let callee = helper(&mut shared);
    let argument = shared.functions[&callee].0[0].0;
    for (instruction, reason) in [
        (
            Instr::Copy(Loc::Addr(Box::new(Loc::Id(argument))), Exp::Bool(true), info()),
            SpeculativeRejectReason::CalleeStateWrite,
        ),
        (
            Instr::PrimopVariadic(Loc::Id(RETURN), primop::variadic_primops()["platform_write_mem"], vec![], info()),
            SpeculativeRejectReason::StateEffect,
        ),
    ] {
        shared.functions.get_mut(&callee).unwrap().2 = Box::leak(vec![instruction, Instr::End].into_boxed_slice());
        let summaries = region_summary::function_effect_summaries(&shared, true);
        assert_eq!(summaries[&callee].rejection.unwrap().reason, reason);
    }
}

#[test]
fn region_m2_read_write_read_and_repeated_pre_state_read() {
    let mut shared = empty_shared_state();
    let reg = shared.symtab.intern("zstate");
    shared.registers.insert(reg, Ty::Bool);
    let read = Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info());
    let mut program = diamond(
        vec![read.clone(), Instr::Copy(Loc::Id(reg), input(1), info()), read.clone()],
        vec![read.clone(), read],
        vec![Instr::End],
    );
    // 符号前态也必须在每条路径的最终寄存器映射中保持等价。
    program.insert(0, Instr::Copy(Loc::Id(reg), input(2), info()));
    for instr in &mut program[1..] {
        match instr {
            Instr::Jump(_, target, _) | Instr::Goto(target) => *target += 1,
            _ => (),
        }
    }
    let paths = check(program, &shared, 3);
    assert_eq!(paths[0].events.iter().filter(|event| matches!(event, Event::ReadReg(..))).count(), 1);
}

#[test]
fn region_m2_read_footprint_topology_and_write_cycle() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let regs: Vec<_> = ["za", "zb", "zc"].iter().map(|name| shared.symtab.intern(name)).collect();
    for reg in &regs {
        shared.registers.insert(*reg, Ty::Bool);
    }
    let read = |reg| Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info());
    // 共同读取只有 b；单臂读取分别位于共同读取的前后，不能按寄存器名排序。
    let paths =
        check(diamond(vec![read(regs[0]), read(regs[1])], vec![read(regs[1]), read(regs[2])], finish()), &shared, 1);
    assert_eq!(paths[0].records.last().unwrap().single_arm_reads.len(), 2);
    assert_eq!(paths[0].events.iter().filter(|event| matches!(event, Event::ReadReg(..))).count(), 3);
    // 相反的共同读取和相反的写入偏序分别形成环，都必须拒绝。
    for write in [false, true] {
        let access = |reg| if write { Instr::Copy(Loc::Id(reg), Exp::Bool(true), info()) } else { read(reg) };
        let program = diamond(vec![access(regs[0]), access(regs[1])], vec![access(regs[1]), access(regs[0])], finish());
        let forked = run(program.clone(), &shared, 1, false, |_| ());
        let merged = run(program, &shared, 1, true, |_| ());
        assert_eq!(equivalent_paths(&forked, &merged, 1, true), (2, 2));
        equivalent_register_paths(&forked, &merged, 1);
    }
    assert!(shared.execution_stats.merge_json()["failure_reasons"]["register_sequence"].as_u64().unwrap() >= 2);
}

#[test]
fn region_m2_nested_conditional_write_then_outer_read() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let reg = shared.symtab.intern("zstate");
    shared.registers.insert(reg, Ty::Bool);
    let program = vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(8),
        Instr::Jump(input(1), 6, info()),
        Instr::Copy(Loc::Id(reg), Exp::Bool(true), info()),
        Instr::Goto(7),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
        Instr::End,
    ];
    let forked = run(program.clone(), &shared, 2, false, |_| ());
    let merged = run(program, &shared, 2, true, |_| ());
    assert_eq!(equivalent_paths(&forked, &merged, 2, true), (3, 1), "{}", shared.execution_stats.merge_json());
    equivalent_register_paths(&forked, &merged, 2);
    assert_eq!(merged[0].records.len(), 2);
    assert!(!merged[0].events.iter().any(|event| matches!(event, Event::ReadReg(..))));
    assert_eq!(merged[0].events.iter().filter(|event| matches!(event, Event::WriteReg(..))).count(), 1);
    // 缺少内部读取足迹时，缓存和导出仍必须直接保留最终帧里的条件值。
    use crate::executor::path_cache::{CachedPath, TraceReader, TraceWriter};
    use crate::executor::samples::{fast::FastFacts, SamplePath};
    let path = &merged[0];
    let context = Context::new(Config::new());
    let mut solver = Solver::from_checkpoint(&context, path.checkpoint.clone());
    let sample_path = SamplePath {
        pre: (0..2)
            .map(|i| {
                let UVal::Init(value) = &path.variables[&test_name(900 + i)] else { panic!("输入必须初始化") };
                (format!("input{i}"), value.clone())
            })
            .chain([("state".into(), Val::Bool(false))])
            .collect(),
        post: BTreeMap::from([("state".into(), path.registers.get_last_if_initialized(reg).unwrap().clone())]),
        result: path.value.clone(),
        memory: vec![],
        memory_guards: BTreeMap::new(),
    };
    let facts = FastFacts::analyze(&sample_path, &mut solver, &path.records).unwrap();
    assert!(facts.is_complete(), "内部读的条件值只依赖初始输入");
    let dag = sample_path.export_dag(&solver, &shared, &path.records, 7);
    assert_eq!(dag["guards"].as_array().unwrap().len(), 2);
    assert!(matches!(path.registers.get_last_if_initialized(reg), Some(Val::Symbolic(_))));
    assert!(solver
        .check_sat_with(
            &smtlib::Exp::Neq(
                Box::new(smt_value(path.registers.get_last_if_initialized(reg).unwrap(), info()).unwrap()),
                Box::new(smt_value(&path.value, info()).unwrap()),
            ),
            info()
        )
        .is_unsat()
        .unwrap());
    assert!(dag["state"]["post"]["state"]["symbol"].is_string());
    assert!(dag["state"]["result"]["symbol"].is_string());
    assert!(dag["definitions"].as_array().unwrap().iter().any(|row| row["smtlib"].as_str().unwrap().contains("ite")));
    let mut writer = TraceWriter::default();
    let cached = CachedPath {
        signature: 7,
        checkpoint: writer.capture(&path.checkpoint),
        path: sample_path.into(),
        records: path.records.iter().cloned().map(Into::into).collect(),
        facts: facts.into(),
    };
    let json = serde_json::to_vec(&cached).unwrap();
    let decoded: CachedPath<B64> = serde_json::from_slice(&json).unwrap();
    assert_eq!(decoded, cached);
    let decoded: CachedPath<B64> = bincode::deserialize(&bincode::serialize(&cached).unwrap()).unwrap();
    assert_eq!(decoded, cached);
    let replay = TraceReader::new(&writer.segments).restore(&decoded.checkpoint);
    let mut replay = Solver::from_checkpoint(&context, replay);
    let restored: SamplePath<B64> = decoded.path.into();
    let records: Vec<_> = decoded.records.into_iter().map(Into::into).collect();
    assert!(FastFacts::analyze(&restored, &mut replay, &records).unwrap().is_complete());
    assert_eq!(restored.export_dag(&replay, &shared, &records, 7), dag);
}

#[test]
fn region_m2_relaxed_and_address_writes_remain_rejected() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let reg = shared.symtab.intern("zstate");
    let reference = shared.symtab.intern("zreference");
    shared.registers.insert(reg, Ty::Bool);
    for address in [false, true] {
        let program = diamond(
            vec![Instr::Copy(
                if address { Loc::Addr(Box::new(Loc::Id(reference))) } else { Loc::Id(reg) },
                Exp::Bool(true),
                info(),
            )],
            vec![],
            finish(),
        );
        let configure = |frame: &mut LocalFrame<'static, B64>| {
            frame.vars_mut().insert(reference, UVal::Init(Val::Ref(reg)));
            if !address {
                frame.regs_mut().insert(reg, true, UVal::Init(Val::Bool(false)));
            }
        };
        let forked = run(program.clone(), &shared, 1, false, configure);
        let merged = run(program, &shared, 1, true, configure);
        assert_eq!(equivalent_paths(&forked, &merged, 1, true), (2, 2));
        equivalent_register_paths(&forked, &merged, 1);
        assert!(merged.iter().all(|path| path.records.is_empty()));
    }
    assert!(shared.execution_stats.merge_json()["failure_reasons"]["relaxed_register"].as_u64().unwrap() > 0);
}

#[test]
fn region_m2_opposite_register_order_with_distinct_accessors() {
    let mut shared = empty_shared_state();
    let a = shared.symtab.intern("za");
    let b = shared.symtab.intern("zb");
    let pair = shared.symtab.intern("zpair");
    let x = shared.symtab.intern("zx");
    let y = shared.symtab.intern("zy");
    shared.type_info.structs.insert(pair, BTreeMap::from([(x, Ty::Bool), (y, Ty::Bool)]));
    for reg in [a, b] {
        shared.registers.insert(reg, Ty::Struct(pair));
    }
    let read = |reg, field| Instr::Copy(Loc::Id(RETURN), Exp::Field(Box::new(Exp::Id(reg)), field), info());
    let program = diamond(vec![read(a, x), read(b, x)], vec![read(b, y), read(a, y)], vec![Instr::End]);
    let configure = |frame: &mut LocalFrame<'static, B64>| {
        for reg in [a, b] {
            frame.regs_mut().assign(
                reg,
                Val::Struct([(x, Val::Bool(true)), (y, Val::Bool(false))].into_iter().collect()),
                &shared,
            );
        }
    };
    let forked = run(program.clone(), &shared, 1, false, configure);
    let merged = run(program, &shared, 1, true, configure);
    assert_eq!(equivalent_paths(&forked, &merged, 1, true), (2, 1));
    equivalent_register_paths(&forked, &merged, 1);
    assert_eq!(merged[0].records.last().unwrap().single_arm_reads.len(), 4);
    assert_eq!(merged[0].events.iter().filter(|event| matches!(event, Event::ReadReg(..))).count(), 4);
}

#[test]
fn region_m2_callee_vector_write_uses_register_merge() {
    let mut shared = empty_shared_state();
    let a = shared.symtab.intern("za");
    let b = shared.symtab.intern("zb");
    let refs = shared.symtab.intern("zrefs");
    for reg in [a, b] {
        shared.registers.insert(reg, Ty::Bool);
    }
    let callee = helper(&mut shared);
    shared.functions.get_mut(&callee).unwrap().2 = Box::leak(
        vec![
            Instr::Call(
                Loc::Id(RETURN),
                false,
                WRITE_REGISTER_FROM_VECTOR,
                vec![Exp::I128(0), Exp::Bool(true), Exp::Id(refs)],
                info(),
            ),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::End,
        ]
        .into_boxed_slice(),
    );
    let program = diamond(
        vec![Instr::Call(Loc::Id(RETURN), false, callee, vec![input(0)], info())],
        vec![Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info())],
        vec![Instr::End],
    );
    let configure = |frame: &mut LocalFrame<'static, B64>| {
        frame.lets_mut().insert(refs, UVal::Init(Val::Vector(vec![Val::Ref(a), Val::Ref(b)])));
    };
    let forked = run(program.clone(), &shared, 1, false, configure);
    let merged = run(program, &shared, 1, true, configure);
    assert_eq!(equivalent_paths(&forked, &merged, 1, true), (2, 1));
    equivalent_register_paths(&forked, &merged, 1);
    let writes: Vec<_> = merged[0]
        .events
        .iter()
        .filter_map(|event| match event {
            Event::WriteReg(reg, _, _) => Some(*reg),
            _ => None,
        })
        .collect();
    assert_eq!(writes, vec![a]);
}

#[test]
fn region_m2_status_callback_with_conditional_and_repeated_struct_writes() {
    let mut shared = empty_shared_state();
    let status = shared.symtab.intern("zstatus");
    let context_reg = shared.symtab.intern("zcontext");
    let structure = shared.symtab.intern("zpair");
    let x = shared.symtab.intern("zx");
    let y = shared.symtab.intern("zy");
    shared.type_info.structs.insert(structure, BTreeMap::from([(x, Ty::Bool), (y, Ty::Bool)]));
    for reg in [status, context_reg] {
        shared.registers.insert(reg, Ty::Struct(structure));
    }
    let callback = helper(&mut shared);
    let callback_arg = shared.functions[&callback].0[0].0;
    let local = shared.symtab.intern("zcallback_local");
    shared.functions.get_mut(&callback).unwrap().2 = Box::leak(
        vec![
            Instr::Init(local, Ty::Bool, Exp::Id(callback_arg), info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(local), info()),
            Instr::End,
        ]
        .into_boxed_slice(),
    );
    let accrue = shared.symtab.intern("zupdate_status");
    let flags = shared.symtab.intern("zflags");
    let old = shared.symtab.intern("zold");
    let field = |reg, name| Exp::Field(Box::new(Exp::Id(reg)), name);
    shared.functions.insert(
        accrue,
        (
            vec![(flags, &Ty::Bool)],
            &Ty::Bool,
            Box::leak(
                vec![
                    Instr::Init(old, Ty::Bool, field(status, x), info()),
                    Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(old), Exp::Id(flags)]), 5, info()),
                    Instr::Copy(Loc::Field(Box::new(Loc::Id(status)), x), Exp::Id(flags), info()),
                    Instr::Copy(Loc::Field(Box::new(Loc::Id(context_reg)), x), Exp::Bool(true), info()),
                    Instr::Copy(Loc::Field(Box::new(Loc::Id(context_reg)), y), Exp::Bool(true), info()),
                    Instr::Call(Loc::Id(RETURN), false, callback, vec![field(status, x)], info()),
                    Instr::End,
                ]
                .into_boxed_slice(),
            ),
        ),
    );
    let program = diamond(
        vec![Instr::Call(Loc::Id(RETURN), false, accrue, vec![input(1)], info())],
        vec![Instr::Copy(Loc::Id(RETURN), field(status, x), info())],
        vec![Instr::End],
    );
    let configure = |frame: &mut LocalFrame<'static, B64>| {
        for reg in [status, context_reg] {
            frame.regs_mut().assign(
                reg,
                Val::Struct([(x, Val::Bool(false)), (y, Val::Bool(false))].into_iter().collect()),
                &shared,
            );
        }
    };
    let forked = run(program.clone(), &shared, 2, false, configure);
    let merged = run(program, &shared, 2, true, configure);
    assert_eq!(equivalent_paths(&forked, &merged, 2, true), (3, 1), "{}", shared.execution_stats.merge_json());
    equivalent_register_paths(&forked, &merged, 2);
    assert_eq!(merged[0].records.len(), 2);
    assert_eq!(merged[0].events.iter().filter(|event| matches!(event, Event::ReadReg(..))).count(), 1);
    let writes: Vec<_> = merged[0]
        .events
        .iter()
        .filter_map(|event| match event {
            Event::WriteReg(reg, accessor, _) => {
                assert!(accessor.is_empty());
                Some(*reg)
            }
            _ => None,
        })
        .collect();
    assert_eq!(writes, vec![status, context_reg]);
}

#[test]
fn region_m2_pre_state_read_after_nested_join_widens_footprint_guard() {
    let mut shared = empty_shared_state();
    let reg = shared.symtab.intern("zstate");
    shared.registers.insert(reg, Ty::Bool);
    let read = Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info());
    let program = vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(8),
        Instr::Jump(input(1), 6, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(7),
        read.clone(),
        read,
        Instr::End,
    ];
    let forked = run(program.clone(), &shared, 2, false, |_| ());
    let merged = run(program, &shared, 2, true, |_| ());
    assert_eq!(equivalent_paths(&forked, &merged, 2, true), (3, 1));
    equivalent_register_paths(&forked, &merged, 2);
    let root = merged[0].records.iter().find(|record| record.parent_record.is_none()).unwrap();
    let read = root.single_arm_reads.iter().find(|read| read.register == reg).unwrap();
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let inputs: Vec<_> = (0..2).map(|_| solver.declare_const(smtlib::Ty::Bool, info())).collect();
    let (_, guards) = import_values(&merged[0], &inputs, &mut solver, &[read.guard.clone()]);
    assert!(
        solver
            .check_sat_with(
                &smtlib::Exp::Neq(Box::new(guards[0].clone()), Box::new(smtlib::Exp::Var(inputs[0]))),
                info(),
            )
            .is_unsat()
            .unwrap(),
        "内层汇合后的前态读必须覆盖外层臂的全部输入"
    );
}

#[test]
fn region_m2_second_arm_pre_state_read_after_first_arm_internal_read() {
    let mut shared = empty_shared_state();
    let reg = shared.symtab.intern("zstate");
    shared.registers.insert(reg, Ty::Bool);
    let read = Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info());
    let program =
        diamond(vec![Instr::Copy(Loc::Id(reg), Exp::Bool(true), info()), read.clone()], vec![read], vec![Instr::End]);
    let paths = check(program, &shared, 1);
    let reads: Vec<_> = paths[0]
        .events
        .iter()
        .filter_map(|event| match event {
            Event::ReadReg(name, _, value) if *name == reg => Some(value),
            _ => None,
        })
        .collect();
    assert_eq!(reads, vec![&Val::Bool(false)], "第二臂必须发布自己的前态，不能复用第一臂内部读");
    let reads = &paths[0].records.last().unwrap().single_arm_reads;
    assert_eq!(reads.len(), 1);
    assert_eq!(reads[0].value, Val::Bool(false));
}

#[test]
fn region_m2_scalar_integer_counter_drives_symbolic_vector_update() {
    let shared = empty_shared_state();
    let index = test_name(994);
    let vector = test_name(995);
    let program = diamond(
        vec![Instr::Copy(Loc::Id(index), Exp::I128(1), info())],
        vec![Instr::Copy(Loc::Id(index), Exp::I128(0), info())],
        vec![
            Instr::PrimopVariadic(
                Loc::Id(vector),
                primop::variadic_primops()["vector_update"],
                vec![Exp::Id(vector), Exp::Id(index), Exp::Bool(true)],
                info(),
            ),
            Instr::PrimopBinary(
                Loc::Id(RETURN),
                primop::binary_primops()["vector_access"],
                Exp::Id(vector),
                Exp::I128(0),
                info(),
            ),
            Instr::End,
        ],
    );
    let configure = |frame: &mut LocalFrame<'static, B64>| {
        frame.vars_mut().insert(index, UVal::Init(Val::I128(0)));
        frame.vars_mut().insert(vector, UVal::Init(Val::Vector(vec![Val::Bool(false); 2])));
    };
    let forked = run(program.clone(), &shared, 1, false, configure);
    let merged = run(program, &shared, 1, true, configure);
    assert_eq!(equivalent_paths(&forked, &merged, 1, true), (2, 1));
    assert_eq!(merged[0].records.len(), 1, "普通整数计数必须实际合并，后续动态向量索引保持原语义");
}
