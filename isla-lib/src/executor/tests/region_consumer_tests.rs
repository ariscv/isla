//! 指令级候选汇合、操作数快照及独立出口。
use super::*;
use crate::config::MergeStrategy;
use crate::ir::Op;

fn strategies() -> [MergeStrategy; 2] {
    [MergeStrategy::Recursive, MergeStrategy::Flat]
}

fn limits(strategy: MergeStrategy) -> ExecutionLimits {
    let mut limits = ExecutionLimits::default().with_path_merging(true);
    limits.merge_strategy = strategy;
    limits
}

fn width_candidates(frame: &mut LocalFrame<'static, B64>) {
    set_width_candidates(frame, Val::I64);
}

fn set_width_candidates(frame: &mut LocalFrame<'static, B64>, mut value: impl FnMut(i64) -> Val<B64>) {
    let guard = |frame: &LocalFrame<B64>, i: u32| match &frame.vars()[&test_name(900 + i)] {
        UVal::Init(Val::Symbolic(symbol)) => *symbol,
        _ => unreachable!(),
    };
    let mut low = |a, b| Val::Guarded(guard(frame, 1), Box::new((value(a), value(b))));
    let width = Val::Guarded(guard(frame, 0), Box::new((low(32, 39), low(48, 57))));
    frame.vars_mut().insert(test_name(1800), UVal::Init(width));
}

fn compare(op: Op, rhs: Exp<Name>) -> Exp<Name> {
    Exp::Call(op, vec![Exp::Id(test_name(1800)), rhs])
}

#[test]
fn region_consumer_four_widths_check_and_continue_once() {
    let shared = empty_shared_state();
    for strategy in strategies() {
        let code = vec![
            Instr::Decl(test_name(1802), Ty::Unit, info()),
            Instr::PrimopUnary(Loc::Id(test_name(1802)), primop::assume, compare(Op::Lteq, Exp::I64(57)), info()),
            Instr::Copy(Loc::Id(RETURN), compare(Op::Eq, Exp::I64(32)), info()),
            Instr::End,
        ];
        let (result, _, _) = paths_with_solver_state(
            code,
            &shared,
            2,
            limits(strategy),
            crate::memory::Memory::new(),
            |frame, _| width_candidates(frame),
            false,
        );
        let expected = paths(
            vec![Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::And, vec![input(0), input(1)]), info()), Instr::End],
            &shared,
            2,
            false,
        );
        assert_eq!(result.len(), 1, "{strategy:?}");
        assert!(result[0].records.iter().any(|record| record.branch_pc == 1));
        equivalent_paths(&expected, &result, 2, true);
    }
}

#[test]
fn region_consumer_mixed_integer_and_strict_operand_read() {
    let mut shared = empty_shared_state();
    shared.registers.insert(test_name(1801), Ty::I64);
    for strategy in strategies() {
        let mut settings = limits(strategy);
        settings.ordered_events = true;
        let code = vec![Instr::Copy(Loc::Id(RETURN), compare(Op::Lteq, Exp::Id(test_name(1801))), info()), Instr::End];
        let (result, _, _) = paths_with_solver_state(
            code,
            &shared,
            2,
            settings,
            crate::memory::Memory::new(),
            |frame, solver| {
                width_candidates(frame);
                let threshold = solver.declare_bitvector(64, info());
                frame.regs_mut().assign(test_name(1801), Val::Symbolic(threshold), &shared);
                solver.assert(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(threshold)), Box::new(smtlib::bits64(40, 64))));
            },
            false,
        );
        assert_eq!(result.len(), 1, "{strategy:?}");
        assert_eq!(
            result[0]
                .events
                .iter()
                .filter(|event| matches!(event, Event::ReadReg(reg, ..) if *reg == test_name(1801)))
                .count(),
            1
        );
        let expected = paths(vec![Instr::Copy(Loc::Id(RETURN), input(0), info()), Instr::End], &shared, 2, false);
        equivalent_paths(&expected, &result, 2, true);
    }
}

#[test]
fn region_consumer_known_domain_joins_native_widths() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    for strategy in strategies() {
        for no_smt in [false, true] {
            let width = Exp::Id(test_name(1800));
            let consumers = [
                (
                    Instr::PrimopBinary(
                        Loc::Id(RETURN),
                        primop::binary_primops()["pow_int"],
                        Exp::I128(-1),
                        width.clone(),
                        info(),
                    ),
                    1,
                ),
                (Instr::PrimopUnary(Loc::Id(RETURN), primop::unary_primops()["zeros"], width, info()), 1),
            ];
            for (consumer, expected) in consumers {
                let mut config = Config::new();
                config.solver_options.no_smt = no_smt;
                config.solver_options.finite_domain_enumeration = true;
                let context = Context::new(config);
                let mut solver = Solver::new(&context);
                let sym = solver.declare_bitvector(64, info());
                use smtlib::Exp::*;
                solver.assert(
                    [32, 39, 48, 57]
                        .into_iter()
                        .map(|width| Eq(Box::new(Var(sym)), Box::new(smtlib::bits64(width, 64))))
                        .reduce(|a, b| Or(Box::new(a), Box::new(b)))
                        .unwrap(),
                );
                assert!(
                    matches!(solver.finite_domain(sym), crate::smt::FiniteDomain::Known(values) if values.len() == 4)
                );
                let mut frame = make_frame(vec![consumer, Instr::End]);
                frame.vars_mut().insert(test_name(1800), UVal::Init(Val::Symbolic(sym)));
                let state = TaskState::new().with_execution_limits(limits(strategy));
                let shared = empty_shared_state();
                let queue = Worker::new_lifo();
                let sink = SingleForkSink { queue: &queue };
                sink.queue.push(frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)));
                let mut outputs = Vec::new();
                let query_start = crate::smt::test_query_count();
                while let Some(mut task) = sink.queue.pop() {
                    let mut solver = Solver::from_checkpoint(&context, task.checkpoint);
                    if let Some((def, event)) = task.fork_cond {
                        solver.add_event(event);
                        solver.add(def);
                    }
                    let mut frame = unfreeze_frame(&task.frame);
                    let result = run_loop(
                        0,
                        task.id,
                        &mut task.fraction,
                        PathTimeout::unlimited(),
                        None,
                        &sink,
                        &mut frame,
                        &state,
                        &shared,
                        &mut solver,
                    )
                    .unwrap();
                    let Run::Finished(value) = result else { panic!("应正常完成") };
                    assert!(
                        frame.region_merge_records().iter().any(|record| record.branch_pc == 0),
                        "{strategy:?}, no_smt={no_smt}, expected={expected}, value={value:?}",
                    );
                    outputs.push(value);
                }
                assert_eq!(outputs.len(), expected, "{strategy:?}, no_smt={no_smt}");
                if no_smt {
                    assert_eq!(crate::smt::test_query_count() - query_start, 0);
                }
            }
        }
    }
}

#[test]
fn region_consumer_preserves_candidate_assertion_failure() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    for strategy in strategies() {
        let context = Context::new(Config::new());
        let mut solver = Solver::new(&context);
        let mut frame = make_frame(vec![
            Instr::Decl(test_name(1802), Ty::Unit, info()),
            Instr::PrimopBinary(
                Loc::Id(test_name(1802)),
                primop::optimistic_assert,
                compare(Op::Neq, Exp::I64(32)),
                Exp::String("32".into()),
                info(),
            ),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::End,
        ]);
        for i in 0..2 {
            let sym = solver.declare_const(smtlib::Ty::Bool, info());
            frame.vars_mut().insert(test_name(900 + i), UVal::Init(Val::Symbolic(sym)));
        }
        width_candidates(&mut frame);
        let state = TaskState::new().with_execution_limits(limits(strategy));
        let outcomes = Mutex::new(Vec::new());
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            &empty_shared_state(),
            &outcomes,
            &|_, _, result, _, mut solver, outcomes| {
                assert!(solver.check_sat(info()).is_sat().unwrap());
                outcomes.lock().unwrap().push(match result {
                    Ok((Run::Finished(Val::Bool(true)), _)) => true,
                    Err((ExecError::AssertionFailure(Some(message), _), _)) if message == "32" => false,
                    _ => panic!("意外的候选出口"),
                });
            },
        );
        let mut outcomes = outcomes.into_inner().unwrap();
        outcomes.sort_unstable();
        assert_eq!(outcomes, [false, true], "{strategy:?}");
    }
}

#[test]
fn region_consumer_uses_callee_local_last_use() {
    let mut shared = empty_shared_state();
    let callee = shared.symtab.intern("zcallee_width_consumer");
    let [width, bits, length] = [1800, 1801, 1802].map(test_name);
    // 被调函数的最后使用和汇合点在 PC 5、6，超出调用者的指令范围。
    let body = vec![
        Instr::Decl(bits, Ty::AnyBits, info()),
        Instr::Decl(length, Ty::I128, info()),
        Instr::Decl(test_name(1803), Ty::Unit, info()),
        Instr::Decl(test_name(1804), Ty::Unit, info()),
        Instr::PrimopBinary(
            Loc::Id(bits),
            primop::binary_primops()["vector_access"],
            Exp::Id(width),
            Exp::I128(0),
            info(),
        ),
        Instr::PrimopUnary(Loc::Id(length), primop::length, Exp::Id(bits), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(length), Exp::I128(32)]), info()),
        Instr::End,
    ];
    let parameter_ty = Box::leak(Box::new(Ty::Vector(Box::new(Ty::AnyBits))));
    shared.functions.insert(callee, (vec![(width, parameter_ty)], &Ty::Bool, Box::leak(body.into_boxed_slice())));
    let code = vec![
        Instr::Jump(input(2), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(4),
        Instr::Call(Loc::Id(RETURN), false, callee, vec![Exp::Id(width)], info()),
        Instr::End,
    ];
    let expected = paths(
        vec![
            Instr::Copy(
                Loc::Id(RETURN),
                Exp::Call(Op::And, vec![Exp::Call(Op::And, vec![input(0), input(1)]), input(2)]),
                info(),
            ),
            Instr::End,
        ],
        &shared,
        3,
        false,
    );
    for strategy in strategies() {
        let (merged, _, _) = paths_with_solver_state(
            code.clone(),
            &shared,
            3,
            limits(strategy),
            crate::memory::Memory::new(),
            |frame, solver| {
                // 这些 SMT 值没有 Sail 位向量标记，生产点因此得保留四个不同位宽的到达项。
                set_width_candidates(frame, |width| {
                    Val::Vector(vec![Val::Symbolic(solver.declare_const(smtlib::Ty::BitVec(width as u32), info()))])
                });
            },
            false,
        );
        assert_eq!(equivalent_paths(&expected, &merged, 3, true), (1, 1), "{strategy:?}");
        assert!(
            merged[0].records.iter().any(|record| {
                record.function == callee
                    && record.branch_pc == 4
                    && record.join == crate::ir::regions::RegionPoint::Instruction(6)
                    && record.parent_record.is_some()
            }),
            "不同位宽应在被调函数最后一次使用之后汇合，{strategy:?}"
        );
    }
}
