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

#[test]
fn region_consumer_closes_widths_through_wrappers() {
    if !run_in_diagnostics_process(concat!(module_path!(), "::region_consumer_closes_widths_through_wrappers")) {
        return;
    }
    // 关闭开关可重跑旧行为的红测，仍要求在纯包装后留下新的汇合记录。
    let enabled = std::env::var_os("ISLA_TEST_DISABLE_WIDTH_CLOSED_CONTINUATION").is_none();
    crate::config::RegionOptions { width_closed_continuation: enabled, ..Default::default() }.configure();
    crate::executor::stats::merge_diagnostics::configure("detail").unwrap();
    // 先生成有状态读拒绝，再在同一诊断进程记录定长汇合成功。
    stateful_memory_callback_preserves_read_count_after_diamond();
    for writes_register in [false, true] {
        let mut shared = empty_shared_state();
        let outer = shared.symtab.intern("zwidth_outer_wrapper");
        let inner = shared.symtab.intern("zwidth_inner_wrapper");
        let before = shared.symtab.intern("zwidth_before");
        let after = shared.symtab.intern("zwidth_after");
        let effect = shared.symtab.intern("zwidth_effect");
        for reg in [before, after, effect] {
            shared.registers.insert(reg, Ty::Bool);
        }
        let [source, bits, forwarded, length, param] = [1800, 1801, 1802, 1803, 1804].map(test_name);
        let mut inner_body = Vec::new();
        if writes_register {
            inner_body.push(Instr::Copy(Loc::Id(effect), Exp::Bool(true), info()));
        }
        inner_body.extend([Instr::Copy(Loc::Id(RETURN), Exp::Id(param), info()), Instr::End]);
        shared
            .functions
            .insert(inner, (vec![(param, &Ty::AnyBits)], &Ty::AnyBits, Box::leak(inner_body.into_boxed_slice())));
        shared.functions.insert(
            outer,
            (
                vec![(param, &Ty::AnyBits)],
                &Ty::AnyBits,
                Box::leak(Box::new([
                    Instr::Call(Loc::Id(RETURN), false, inner, vec![Exp::Id(param)], info()),
                    Instr::End,
                ])),
            ),
        );
        let code = vec![
            Instr::Copy(Loc::Id(before), Exp::Bool(true), info()),
            Instr::Decl(bits, Ty::AnyBits, info()),
            Instr::Decl(forwarded, Ty::AnyBits, info()),
            Instr::Decl(length, Ty::I128, info()),
            Instr::PrimopBinary(
                Loc::Id(bits),
                primop::binary_primops()["vector_access"],
                Exp::Id(source),
                Exp::I128(0),
                info(),
            ),
            Instr::Call(Loc::Id(forwarded), false, outer, vec![Exp::Id(bits)], info()),
            Instr::PrimopUnary(Loc::Id(length), primop::length, Exp::Id(forwarded), info()),
            Instr::Copy(Loc::Id(after), Exp::Bool(false), info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(length), Exp::I128(4)]), info()),
            Instr::End,
        ];
        let run = |strategy, merge| {
            let mut settings = limits(strategy).with_path_merging(merge);
            settings.ordered_events = true;
            let [narrow, wide] = [1805, 1806].map(test_name);
            let mut code = code.clone();
            if !merge {
                code.splice(
                    0..0,
                    [
                        Instr::Jump(input(0), 3, info()),
                        Instr::Copy(Loc::Id(source), Exp::Id(wide), info()),
                        Instr::Goto(4),
                        Instr::Copy(Loc::Id(source), Exp::Id(narrow), info()),
                    ],
                );
            }
            paths_with_solver_state(
                code,
                &shared,
                1,
                settings,
                crate::memory::Memory::new(),
                |frame, solver| {
                    let UVal::Init(Val::Symbolic(guard)) = frame.vars()[&test_name(900)] else { unreachable!() };
                    let make = |width, solver: &mut Solver<B64>| {
                        Val::Vector(vec![Val::Symbolic(solver.declare_bitvector(width, info()))])
                    };
                    let (a, b) = (make(4, solver), make(8, solver));
                    if merge {
                        frame.vars_mut().insert(source, UVal::Init(Val::Guarded(guard, Box::new((a, b)))));
                    } else {
                        frame.vars_mut().extend([
                            (source, UVal::Init(Val::Unit)),
                            (narrow, UVal::Init(a)),
                            (wide, UVal::Init(b)),
                        ]);
                    }
                },
                false,
            )
            .0
        };
        let plain = run(MergeStrategy::Recursive, false);
        for strategy in strategies() {
            let merged = run(strategy, true);
            let expected = if writes_register {
                vec![(before, true), (effect, true), (after, false)]
            } else {
                vec![(before, true), (after, false)]
            };
            for path in plain.iter().chain(&merged) {
                let events: Vec<_> = path
                    .events
                    .iter()
                    .filter_map(|event| match event {
                        Event::Smt(..) | Event::Fork(..) | Event::Merge(..) => None,
                        Event::WriteReg(reg, accessors, Val::Bool(value)) if accessors.is_empty() => {
                            Some((*reg, *value))
                        }
                        other => panic!("出现额外的模型事件：{other:?}"),
                    })
                    .collect();
                assert_eq!(events, expected);
            }
            assert_eq!(
                merged.iter().any(|path| path.records.iter().any(|record| {
                    record.branch_pc == 4 && record.join == crate::ir::regions::RegionPoint::Instruction(7)
                })),
                !writes_register,
                "{strategy:?}"
            );
            assert_eq!(equivalent_paths(&plain, &merged, 1, true), (2, 1));
        }
    }
}

#[test]
fn region_consumer_carries_four_widths_across_return() {
    if !run_in_diagnostics_process(concat!(module_path!(), "::region_consumer_carries_four_widths_across_return")) {
        return;
    }
    crate::config::RegionOptions { width_closed_continuation: true, ..Default::default() }.configure();

    let mut shared = empty_shared_state();
    let producer = shared.symtab.intern("zwidth_producer");
    let wrapper = shared.symtab.intern("zwidth_return_wrapper");
    let caller = shared.symtab.intern("zwidth_return_caller");
    let [source, bits, length] = [1800, 1801, 1802].map(test_name);
    let source_ty = Box::leak(Box::new(Ty::Vector(Box::new(Ty::AnyBits))));
    shared.functions.insert(
        producer,
        (
            vec![(source, source_ty)],
            &Ty::AnyBits,
            Box::leak(Box::new([
                Instr::PrimopBinary(
                    Loc::Id(RETURN),
                    primop::binary_primops()["vector_access"],
                    Exp::Id(source),
                    Exp::I128(0),
                    info(),
                ),
                Instr::End,
            ])),
        ),
    );
    shared.functions.insert(
        wrapper,
        (
            vec![(source, source_ty)],
            &Ty::AnyBits,
            Box::leak(Box::new([
                Instr::Call(Loc::Id(RETURN), false, producer, vec![Exp::Id(source)], info()),
                Instr::End,
            ])),
        ),
    );
    shared.functions.insert(
        caller,
        (
            vec![(source, source_ty)],
            &Ty::Bool,
            Box::leak(Box::new([
                Instr::Decl(bits, Ty::AnyBits, info()),
                Instr::Decl(length, Ty::I128, info()),
                Instr::Call(Loc::Id(bits), false, wrapper, vec![Exp::Id(source)], info()),
                Instr::PrimopUnary(Loc::Id(length), primop::length, Exp::Id(bits), info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(length), Exp::I128(32)]), info()),
                Instr::End,
            ])),
        ),
    );
    let expected = paths(
        vec![Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::And, vec![input(0), input(1)]), info()), Instr::End],
        &shared,
        2,
        false,
    );
    for strategy in strategies() {
        let (merged, _, _) = paths_with_solver_state(
            vec![Instr::Call(Loc::Id(RETURN), false, caller, vec![Exp::Id(source)], info()), Instr::End],
            &shared,
            2,
            limits(strategy),
            crate::memory::Memory::new(),
            |frame, _| set_width_candidates(frame, |width| Val::Vector(vec![Val::Bits(B64::new(0, width as u32))])),
            false,
        );
        assert_eq!(equivalent_paths(&expected, &merged, 2, true), (1, 1), "{strategy:?}");
        assert!(
            merged[0].records.iter().any(|record| {
                record.function == caller
                    && record.branch_pc == 2
                    && record.join == crate::ir::regions::RegionPoint::Instruction(4)
            }),
            "四种位宽应穿过两个返回边界，{strategy:?}"
        );
    }
}

#[test]
fn region_sym_bits_concretizes_at_boundaries() {
    if !run_in_diagnostics_process(concat!(module_path!(), "::region_sym_bits_concretizes_at_boundaries")) {
        return;
    }
    crate::smt::configure_solver_options(crate::smt::SolverOptions { sym_bits: true, ..Default::default() });
    let mut shared = empty_shared_state();
    let reg = shared.symtab.intern("zsym_bits_reg");
    shared.registers.insert(reg, Ty::Bits(8));
    let [source, result] = [1800, 1801].map(test_name);
    let make = |symbol, solver: &mut Solver<B64>, wide| {
        let len = solver.define_const(
            smtlib::Exp::Ite(
                Box::new(smtlib::Exp::Var(symbol)),
                Box::new(crate::primop_util::smt_i128(8)),
                Box::new(crate::primop_util::smt_i128(wide)),
            ),
            info(),
        );
        let data = solver.define_bitvector(smtlib::bits64(0x55, 16), info());
        UVal::Init(Val::SymBits { data, len, cap: 16 })
    };
    let run = |instrs, wide| {
        paths_with_solver_state(
            instrs,
            &shared,
            1,
            limits(MergeStrategy::Recursive).with_path_merging(false),
            crate::memory::Memory::new(),
            |frame, solver| {
                let UVal::Init(Val::Symbolic(symbol)) = frame.vars()[&test_name(900)] else { unreachable!() };
                frame.vars_mut().insert(source, make(symbol, solver, wide));
                frame.vars_mut().insert(result, UVal::Init(Val::Unit));
            },
            false,
        )
        .0
    };

    let paths = run(
        vec![
            Instr::PrimopUnary(Loc::Id(RETURN), primop::unary_primops()["string_of_bits"], Exp::Id(source), info()),
            Instr::End,
        ],
        16,
    );
    assert_eq!(paths.len(), 2);
    assert!(paths.iter().all(|path| matches!(path.value, Val::String(_))));

    let paths = run(
        vec![
            Instr::Copy(Loc::Id(reg), Exp::Id(source), info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
            Instr::End,
        ],
        8,
    );
    assert_eq!(paths.len(), 1);
    assert!(paths[0]
        .events
        .iter()
        .any(|event| matches!(event, Event::WriteReg(name, _, Val::Symbolic(_)) if *name == reg)));
    assert!(matches!(paths[0].value, Val::Symbolic(_)));

    let paths = run(
        vec![
            Instr::Monomorphize(source, Ty::AnyBits, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(source), info()),
            Instr::End,
        ],
        16,
    );
    assert_eq!(paths.len(), 2);
    assert!(paths.iter().all(|path| matches!(path.value, Val::Bits(_))));

    let paths = run(vec![Instr::Copy(Loc::Id(RETURN), Exp::Id(source), info()), Instr::End], 16);
    assert_eq!(paths.len(), 2);
    assert!(paths.iter().all(|path| matches!(path.value, Val::Symbolic(_))));

    let write = primop::memory::variadic_primops::<B64>()["write_mem"];
    let paths = run(
        vec![
            Instr::PrimopVariadic(
                Loc::Id(result),
                write,
                vec![Exp::Unit, Exp::Unit, Exp::Bits(B64::new(0x2000, 64)), Exp::Unit, Exp::Id(source)],
                info(),
            ),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(result), info()),
            Instr::End,
        ],
        16,
    );
    let mut sizes: Vec<_> = paths
        .iter()
        .flat_map(|path| &path.events)
        .filter_map(|event| if let Event::WriteMem { bytes, .. } = event { Some(*bytes) } else { None })
        .collect();
    sizes.sort_unstable();
    assert_eq!(sizes, [1, 2]);

    let bytes = test_name(1802);
    let length = Instr::PrimopUnary(Loc::Id(bytes), primop::length, Exp::Id(source), info());
    let read = primop::memory::variadic_primops::<B64>()["read_mem"];
    let paths = run(
        vec![
            Instr::Decl(bytes, Ty::I128, info()),
            length.clone(),
            Instr::PrimopVariadic(
                Loc::Id(RETURN),
                read,
                vec![Exp::Unit, Exp::Unit, Exp::Bits(B64::new(0x2000, 64)), Exp::Id(bytes)],
                info(),
            ),
            Instr::End,
        ],
        16,
    );
    let mut sizes: Vec<_> = paths
        .iter()
        .flat_map(|path| &path.events)
        .filter_map(|event| if let Event::ReadMem { bytes, .. } = event { Some(*bytes) } else { None })
        .collect();
    sizes.sort_unstable();
    assert_eq!(sizes, [8, 16]);

    let paths = run(
        vec![
            Instr::Decl(bytes, Ty::I128, info()),
            length,
            Instr::PrimopBinary(
                Loc::Id(RETURN),
                primop::binary_primops()["vector_init"],
                Exp::Id(bytes),
                Exp::Unit,
                info(),
            ),
            Instr::End,
        ],
        16,
    );
    let mut sizes: Vec<_> = paths
        .iter()
        .map(|path| {
            let Val::Vector(values) = &path.value else { panic!("宿主分配必须返回向量") };
            values.len()
        })
        .collect();
    sizes.sort_unstable();
    assert_eq!(sizes, [8, 16]);
}
