use super::*;

#[test]
fn 符号解包必须分离成功与类型错误且只读取一次() {
    for workers in [0, 1, 4] {
        for owned in [false, true] {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let flag = solver.declare_const(smtlib::Ty::Bool, info());
            let a = test_name(870);
            let b = test_name(871);
            let value = test_name(872);
            let field = test_name(873);
            let mut shared = empty_shared_state();
            let reg = shared.symtab.intern("zunwrap_register");
            let ctor = symbolic_ctor_choice(
                flag,
                (a, Val::Bits(B64::new(11, 8))),
                (b, Val::Bits(B64::new(22, 8))),
                &mut solver,
            );
            let exp = if owned {
                Exp::Field(Box::new(Exp::Struct(value, vec![(field, Exp::Id(reg))])), field)
            } else {
                Exp::Id(reg)
            };
            let mut frame =
                make_frame(vec![Instr::Copy(Loc::Id(RETURN), Exp::Unwrap(a, Box::new(exp)), info()), Instr::End]);
            frame.regs_mut().insert(reg, false, UVal::Init(ctor));
            let state = TaskState::new();
            let out = Arc::new(Mutex::new((0, 0)));
            let task = frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver));
            drop(frame);
            start_multi(workers, Some(10), vec![task], &shared, out.clone(), &|_, _, result, _, mut solver, out| {
                assert!(solver.check_sat(info()).is_sat().unwrap());
                assert_eq!(
                    solver.trace().to_vec().iter().filter(|e| matches!(e, Event::ReadReg(r, ..) if *r == reg)).count(),
                    1
                );
                let mut counts = out.lock().unwrap();
                match result {
                    Ok((Run::Finished(value), _)) => {
                        assert_eq!(value, Val::Bits(B64::new(11, 8)));
                        assert!(solver
                            .check_sat_with(&smtlib::Exp::Not(Box::new(smtlib::Exp::Var(flag))), info())
                            .is_unsat()
                            .unwrap());
                        counts.0 += 1;
                    }
                    Err((ExecError::Type(_, _), _)) => {
                        assert!(solver.check_sat_with(&smtlib::Exp::Var(flag), info()).is_unsat().unwrap());
                        counts.1 += 1;
                    }
                    _ => panic!("解包必须成功或报告类型错误"),
                }
            });
            assert_eq!(*out.lock().unwrap(), (1, 1));
        }
    }
}

#[test]
fn 切片所有入口必须检查完整边界() {
    for op in ["set_slice", "set_slice_int", "bitvector_update"] {
        for symbolic_bits in [false, true] {
            for symbolic_update in [false, true] {
                for n in [-1, 0, 7, 8, i128::from(i64::MAX)] {
                    let ctx = Context::new(Config::new());
                    let mut solver = Solver::<B64>::new(&ctx);
                    let mut frame = make_frame(vec![Instr::End]);
                    let bits = if op == "set_slice_int" {
                        if symbolic_bits {
                            Val::Symbolic(solver.define_const(crate::primop_util::smt_i128(0), info()))
                        } else {
                            Val::I128(0)
                        }
                    } else if symbolic_bits {
                        Val::Symbolic(solver.define_bitvector(smtlib::bits64(0, 8), info()))
                    } else {
                        Val::Bits(B64::new(0, 8))
                    };
                    let update = if symbolic_update {
                        Val::Symbolic(solver.define_bitvector(smtlib::bits64(3, 2), info()))
                    } else {
                        Val::Bits(B64::new(3, 2))
                    };
                    let index = if op == "bitvector_update" { Val::I64(n.try_into().unwrap()) } else { Val::I128(n) };
                    let args = match op {
                        "set_slice" => vec![Val::I128(8), Val::I128(2), bits, index, update],
                        "set_slice_int" => vec![Val::I128(2), bits, index, update],
                        _ => vec![bits, index, update],
                    };
                    let result = primop::variadic_primops()[op](args, &mut solver, &mut frame, info());
                    let limit = if op == "set_slice_int" { 126 } else { 6 };
                    if n < 0 || n > limit {
                        assert!(
                            matches!(result, Err(ExecError::OutOfBounds("vector_update"))),
                            "{op} n={n}: {result:?}"
                        );
                    } else {
                        assert!(result.is_ok(), "{op} n={n}: {result:?}");
                    }
                }
            }
        }
    }
}

#[test]
fn 位向量更新与嵌套切片表达式必须保留越界路径() {
    for expression in [false, true] {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let width = if expression { 64 } else { 128 };
        let index = solver.declare_const(smtlib::Ty::BitVec(width), info());
        solver.assert(smtlib::Exp::Or(
            Box::new(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(index)), Box::new(smtlib::bits64(0, width)))),
            Box::new(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(index)), Box::new(smtlib::bits64(8, width)))),
        ));
        let n = test_name(874);
        let args = vec![Exp::Bits(B64::zeros(8)), Exp::Id(n), Exp::Bits(B64::new(1, 1))];
        let instr = if expression {
            Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::SetSlice, args), info())
        } else {
            Instr::PrimopVariadic(Loc::Id(RETURN), primop::variadic_primops()["vector_update"], args, info())
        };
        let mut frame = make_frame(vec![instr, Instr::End]);
        frame.vars_mut().insert(n, UVal::Init(Val::Symbolic(index)));
        let state = TaskState::new();
        let out = Mutex::new((0, 0));
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            &empty_shared_state(),
            &out,
            &|_, _, result, _, mut solver, out| {
                assert!(solver.check_sat(info()).is_sat().unwrap());
                let mut counts = out.lock().unwrap();
                match result {
                    Ok((Run::Finished(value), _)) => {
                        assert!(solver
                            .check_sat_with(
                                &smtlib::Exp::Neq(
                                    Box::new(smt_value(&value, info()).unwrap()),
                                    Box::new(smtlib::bits64(1, 8))
                                ),
                                info()
                            )
                            .is_unsat()
                            .unwrap());
                        counts.0 += 1;
                    }
                    Err((ExecError::OutOfBounds(_), _)) => counts.1 += 1,
                    _ => panic!("切片必须成功或报告越界"),
                }
            },
        );
        assert_eq!(*out.lock().unwrap(), (1, 1));
    }
}

#[test]
fn 寄存器解引用与向量单项符号索引必须保留事件() {
    for name in ["_TLB", "core_TLB", "_TLB_cache"] {
        let mut shared = empty_shared_state();
        let encoded = zencode::encode(name);
        let reg = shared.symtab.intern(&encoded);
        let mut frame =
            make_frame(vec![Instr::Call(Loc::Id(RETURN), false, REG_DEREF, vec![Exp::Ref(reg)], info()), Instr::End]);
        frame.regs_mut().insert(reg, false, UVal::Init(Val::Bits(B64::new(42, 8))));
        let state = TaskState::new();
        let out = Mutex::new(Vec::new());
        start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, solver, out| {
            assert!(matches!(result, Ok((Run::Finished(_), _))));
            out.lock().unwrap().push(
                solver.trace().to_vec().iter().filter(|e| matches!(e, Event::ReadReg(r, ..) if *r == reg)).count(),
            );
        });
        // dc76449 撤回这两条访问路径的 _TLB 特判，所有名称均须保留事件。
        assert_eq!(*out.lock().unwrap(), vec![1]);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let index = solver.define_const(smtlib::bits64(0, 128), info());
        let refs = Val::Vector(vec![Val::Ref(reg)]);
        read_register_from_vector(
            Val::Symbolic(index),
            refs.clone(),
            &mut frame.local_state,
            &shared,
            &mut solver,
            info(),
        )
        .unwrap();
        write_register_from_vector(
            Val::Symbolic(index),
            Val::Bits(B64::new(9, 8)),
            refs,
            &mut frame.local_state,
            &shared,
            &mut solver,
            info(),
        )
        .unwrap();
        let trace = solver.trace().to_vec();
        assert_eq!(trace.iter().filter(|e| matches!(e, Event::ReadReg(r, ..) if *r == reg)).count(), 1);
        assert_eq!(trace.iter().filter(|e| matches!(e, Event::WriteReg(r, ..) if *r == reg)).count(), 1);
    }
}

#[test]
fn 空切片在末尾更新必须保持原值而超长更新必须拒绝() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let mut frame = make_frame(vec![Instr::End]);
    let op = primop::variadic_primops()["set_slice"];
    for (length, offset, update_width, valid) in
        [(64, 64, 0, true), (0, 0, 0, true), (8, 0, 9, false), (0, 0, 1, false)]
    {
        let result = op(
            vec![
                Val::I128(length),
                Val::I128(update_width),
                Val::Bits(B64::zeros(length.try_into().unwrap())),
                Val::I128(offset),
                Val::Bits(B64::zeros(update_width.try_into().unwrap())),
            ],
            &mut solver,
            &mut frame,
            info(),
        );
        if valid {
            assert_eq!(result.unwrap(), Val::Bits(B64::zeros(length.try_into().unwrap())));
        } else {
            assert!(matches!(result, Err(ExecError::OutOfBounds("vector_update"))));
        }
    }
    let op = primop::variadic_primops()["set_slice_int"];
    let result = op(
        vec![Val::I128(0), Val::I128(42), Val::I128(128), Val::Bits(B64::zeros(0))],
        &mut solver,
        &mut frame,
        info(),
    );
    assert_eq!(result.unwrap(), Val::I128(42));
}
