//! 核对不同位宽在候选合并、消费和重放时的原生语义。
use super::*;
use crate::config::MergeStrategy;

fn settings(strategy: MergeStrategy) -> ExecutionLimits {
    let mut settings = ExecutionLimits::default().with_path_merging(true);
    settings.merge_strategy = strategy;
    settings
}

#[test]
fn region_union_width_caller_checks_tag_in_one_frame() {
    let mut shared = empty_shared_state();
    let defs = crate::ir_parser::IrParser::new()
        .parse(&mut shared.symtab, crate::ir_lexer::new_ir_lexer("union zResult { zOk: %bv, zErr: %unit }"))
        .unwrap();
    shared.type_info = IRTypeInfo::new::<B64>(&defs);
    let ok = shared.symtab.lookup("zOk");
    let err = shared.symtab.lookup("zErr");
    let union = shared.symtab.lookup("zResult");
    let result = shared.symtab.intern("zresult");
    let producer = shared.symtab.intern("zproduce");
    let param = shared.symtab.intern("zparam");
    let wide = shared.symtab.intern("zwide");
    let leave = |tag, payload| Instr::Call(Loc::Id(RETURN), false, tag, vec![payload], info());
    let producer_code = vec![
        Instr::Jump(Exp::Id(param), 6, info()),
        Instr::Jump(Exp::Id(wide), 4, info()),
        leave(ok, Exp::Bits(B64::new(5, 32))),
        Instr::Goto(7),
        leave(ok, Exp::Bits(B64::new(7, 64))),
        Instr::Goto(7),
        leave(err, Exp::Unit),
        Instr::End,
    ];
    shared.functions.insert(
        producer,
        (
            vec![(param, &Ty::Bool), (wide, &Ty::Bool)],
            Box::leak(Box::new(Ty::Union(union))),
            Box::leak(producer_code.into_boxed_slice()),
        ),
    );
    let program = vec![
        Instr::Decl(result, Ty::Union(union), info()),
        Instr::Call(Loc::Id(result), false, producer, vec![input(0), input(1)], info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Kind(ok, Box::new(Exp::Id(result))), info()),
        Instr::End,
    ];
    let expected = paths(program.clone(), &shared, 2, false);
    assert_eq!(expected.len(), 3);
    for strategy in [MergeStrategy::Recursive, MergeStrategy::Flat] {
        let actual =
            paths_with_state(program.clone(), &shared, 2, settings(strategy), crate::memory::Memory::new(), |_| {});
        assert_eq!(actual.len(), 1, "{strategy:?}");
        equivalent_paths(&expected, &actual, 2, true);
    }
}

#[test]
fn region_union_width_primops_preserve_width_until_consumed() {
    let shared = empty_shared_state();
    let width = test_name(1850);
    let extended = test_name(1851);
    let length = test_name(1852);
    let appended = test_name(1853);
    let sliced = test_name(1854);
    let op = |name| primop::binary_primops::<B64>()[name];
    let result = |op, value| Exp::Call(op, vec![Exp::Id(value), Exp::Bits(B64::new(0x3a5, 64))]);
    let program = vec![
        Instr::Decl(width, Ty::AnyBits, info()),
        Instr::Decl(length, Ty::I128, info()),
        Instr::Decl(extended, Ty::Bits(64), info()),
        Instr::Decl(appended, Ty::AnyBits, info()),
        Instr::Decl(sliced, Ty::Bits(12), info()),
        Instr::Jump(input(0), 8, info()),
        Instr::Copy(Loc::Id(width), Exp::Bits(B64::new(0xa, 4)), info()),
        Instr::Goto(9),
        Instr::Copy(Loc::Id(width), Exp::Bits(B64::new(0x3a, 8)), info()),
        Instr::PrimopUnary(Loc::Id(length), primop::unary_primops()["length"], Exp::Id(width), info()),
        Instr::PrimopBinary(Loc::Id(extended), op("zero_extend"), Exp::Id(width), Exp::I128(64), info()),
        Instr::PrimopBinary(Loc::Id(appended), op("append"), Exp::Id(width), Exp::Bits(B64::new(5, 4)), info()),
        Instr::Copy(Loc::Id(sliced), Exp::Call(Op::Slice(12), vec![Exp::Id(appended), Exp::I64(0)]), info()),
        Instr::Copy(
            Loc::Id(RETURN),
            Exp::Call(
                Op::And,
                vec![
                    Exp::Call(Op::Eq, vec![Exp::Id(length), Exp::I128(8)]),
                    Exp::Call(
                        Op::And,
                        vec![
                            result(Op::Neq, extended),
                            Exp::Call(Op::Eq, vec![Exp::Id(sliced), Exp::Bits(B64::new(0x3a5, 12))]),
                        ],
                    ),
                ],
            ),
            info(),
        ),
        Instr::End,
    ];
    let expected = paths(program.clone(), &shared, 1, false);
    assert_eq!(expected.len(), 2);
    for strategy in [MergeStrategy::Recursive, MergeStrategy::Flat] {
        let actual =
            paths_with_state(program.clone(), &shared, 1, settings(strategy), crate::memory::Memory::new(), |_| {});
        assert_eq!(actual.len(), 1, "{strategy:?}");
        equivalent_paths(&expected, &actual, 1, true);
    }
}

#[test]
fn region_union_width_struct_vector_and_normalization() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let outer = solver.declare_const(smtlib::Ty::Bool, info());
    let inner = solver.declare_const(smtlib::Ty::Bool, info());
    let short = Val::Bits(B64::zeros(0));
    let symbol = solver.declare_bitvector(4, info());
    let long = Val::MixedBits(vec![BitsSegment::Concrete(B64::new(3, 4)), BitsSegment::Symbolic(symbol)]);
    let field = test_name(1850);
    let wrap = |value| Val::Struct([(field, Val::Vector(vec![value]))].into_iter().collect());
    let merge = crate::primop_util::merge_concrete_val;
    let nested = merge(inner, &wrap(short.clone()), &wrap(long.clone()), &mut solver, info()).unwrap();
    let result = merge(outer, &nested, &wrap(short.clone()), &mut solver, info()).unwrap();
    let Val::Struct(fields) = result else { panic!("应保留结构体") };
    let Val::Vector(values) = &fields[&field] else { panic!("应保留向量") };
    let Val::Guarded(guard, alternatives) = &values[0] else { panic!("应只保留两个不同位宽的备选") };
    assert_eq!(alternatives.as_ref(), &(short, long));
    use smtlib::Exp::*;
    let expected = Or(Box::new(Not(Box::new(Var(outer)))), Box::new(Var(inner)));
    assert!(solver.check_sat_with(&Neq(Box::new(Var(*guard)), Box::new(expected)), info()).is_unsat().unwrap());

    let tag = test_name(1851);
    let poisoned = Val::Ctor(tag, Box::new(Val::Poison));
    let ok = Val::Ctor(tag, Box::new(values[0].clone()));
    assert!(matches!(merge(outer, &ok, &poisoned, &mut solver, info()), Err(ExecError::IncompatibleUnionPayload)));
}

#[test]
fn region_union_width_preserves_out_of_bounds_error() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let shared = empty_shared_state();
    for strategy in [MergeStrategy::Recursive, MergeStrategy::Flat] {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let pick = solver.declare_const(smtlib::Ty::Bool, info());
        let width = test_name(1850);
        let code = vec![
            Instr::Decl(width, Ty::AnyBits, info()),
            Instr::Jump(input(0), 4, info()),
            Instr::Copy(Loc::Id(width), Exp::Bits(B64::new(3, 4)), info()),
            Instr::Goto(5),
            Instr::Copy(Loc::Id(width), Exp::Bits(B64::new(3, 8)), info()),
            Instr::PrimopVariadic(
                Loc::Id(RETURN),
                primop::variadic_primops()["vector_subrange"],
                vec![Exp::Id(width), Exp::I128(5), Exp::I128(0)],
                info(),
            ),
            Instr::End,
        ];
        let mut frame = make_frame(code);
        frame.vars_mut().insert(test_name(900), UVal::Init(Val::Symbolic(pick)));
        let state = TaskState::new().with_execution_limits(settings(strategy));
        let outcomes = Mutex::new(Vec::new());
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            &shared,
            &outcomes,
            &|_, _, result, _, mut solver, outcomes| {
                let selected = match result {
                    Ok((Run::Finished(Val::Bits(bits)), _)) if bits == B64::new(3, 6) => true,
                    Err((ExecError::Type(message, _), _)) if message == "vector_subrange out of bounds" => false,
                    _ => panic!("意外的切片出口"),
                };
                assert!(solver.check_sat_with(&smtlib::Exp::Bool(true), info()).is_sat().unwrap());
                assert!(solver
                    .check_sat_with(
                        &smtlib::Exp::Neq(Box::new(smtlib::Exp::Var(pick)), Box::new(smtlib::Exp::Bool(selected))),
                        info(),
                    )
                    .is_unsat()
                    .unwrap());
                outcomes.lock().unwrap().push(selected);
            },
        );
        let mut outcomes = outcomes.into_inner().unwrap();
        outcomes.sort_unstable();
        assert_eq!(outcomes, [false, true], "{strategy:?}");
    }
}
