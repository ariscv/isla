use super::*;

#[test]
fn 超宽地址重叠区域必须保持分派优先级和完整事件地址() {
    for width in [1, 8, 64, 65, 129, 257, 1024] {
        for fetch in [false, true] {
            crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let address = solver.declare_bitvector(width, info());
            let low = if width > 64 {
                smtlib::Exp::Extract(63, 0, Box::new(smtlib::Exp::Var(address)))
            } else {
                smtlib::Exp::Var(address)
            };
            solver.assert(smtlib::Exp::Bvule(Box::new(low), Box::new(smtlib::bits64(1, width.min(64)))));
            let mut memory = crate::memory::Memory::new();
            memory.add_symbolic_code_region(0..2);
            memory.add_symbolic_region(0..16);
            let result = memory.read(
                Val::Unit,
                Val::Symbolic(address),
                Val::I128(1),
                &mut solver,
                false,
                if fetch { ReadOpts::ifetch() } else { ReadOpts::default() },
            );
            assert!(result.is_ok(), "整个地址域均由首个代码区域处理：{result:?}");
            let events = solver.trace().to_vec();
            let reads: Vec<_> = events
                .iter()
                .filter_map(|event| match event {
                    Event::ReadMem { address, region, opts, .. } => Some((address, *region, opts.is_ifetch)),
                    _ => None,
                })
                .collect();
            assert_eq!(reads, vec![(&Val::Symbolic(address), "symbolic code", fetch)]);
            assert!(solver.check_sat(info()).is_sat().unwrap());
            let mut replay = Solver::from_checkpoint(&ctx, checkpoint(&mut solver));
            assert_eq!(replay.length(address), Some(width));
            assert!(replay.is_sail_bitvector(address));
            assert!(replay.check_sat(info()).is_sat().unwrap());
        }
    }
}

#[test]
fn 寄存器向量的合并写索引必须保留错误构造子解包路径() {
    let mut observations = Vec::new();
    for enabled in [false, true] {
        let mut shared = empty_shared_state();
        let a = shared.symtab.intern("zreview33_write_A");
        let b = shared.symtab.intern("zreview33_write_B");
        let r0 = shared.symtab.intern("zreview33_write_r0");
        let r1 = shared.symtab.intern("zreview33_write_r1");
        let condition = test_name(804);
        let index = test_name(805);
        let refs = test_name(806);
        let update = test_name(807);
        let ignored = test_name(808);
        let mut frame = make_frame(vec![
            Instr::Decl(condition, Ty::Bool, info()),
            Instr::Decl(index, Ty::Bits(1), info()),
            Instr::Jump(Exp::Id(condition), 5, info()),
            Instr::Copy(Loc::Id(index), Exp::Bits(B64::new(0, 1)), info()),
            Instr::Goto(6),
            Instr::Copy(Loc::Id(index), Exp::Bits(B64::new(1, 1)), info()),
            Instr::Call(
                Loc::Id(ignored),
                false,
                crate::ir::WRITE_REGISTER_FROM_VECTOR,
                vec![Exp::Id(index), Exp::Id(update), Exp::Id(refs)],
                info(),
            ),
            Instr::Copy(Loc::Id(RETURN), Exp::Unwrap(a, Box::new(Exp::Id(r0))), info()),
            Instr::End,
        ]);
        frame.vars_mut().insert(ignored, UVal::Init(Val::Unit));
        frame.lets_mut().insert(refs, UVal::Init(Val::Vector(vec![Val::Ref(r0), Val::Ref(r1)])));
        frame.lets_mut().insert(update, UVal::Init(Val::Ctor(b, Box::new(Val::Bits(B64::new(22, 8))))));
        for reg in [r0, r1] {
            frame.regs_mut().insert(reg, false, UVal::Init(Val::Ctor(a, Box::new(Val::Bits(B64::new(11, 8))))));
        }
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
        let out = Mutex::new((0, 0, false));
        start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, mut solver, out| {
            let mut actual = out.lock().unwrap();
            match result {
                Ok((Run::Finished(_), frame)) => {
                    actual.0 += 1;
                    let UVal::Init(value) = &frame.vars()[&index] else { panic!("索引必须初始化") };
                    let invalid =
                        smtlib::Exp::Eq(Box::new(smt_value(value, info()).unwrap()), Box::new(smtlib::bits64(0, 1)));
                    actual.2 |= solver.check_sat_with(&invalid, info()).is_sat().unwrap();
                }
                Err((ExecError::Type(..), _)) => actual.1 += 1,
                _ => panic!("只能正常结束或报告标签类型错误"),
            }
        });
        observations.push((enabled, out.into_inner().unwrap()));
    }
    assert_eq!(
        observations,
        vec![(false, (1, 1, false)), (true, (1, 1, false))],
        "索引 0 把首个寄存器写为 B 后不能成功解包为 A"
    );
}

#[test]
fn 寄存器向量的合并索引必须保留错误构造子解包路径() {
    let mut observations = Vec::new();
    for enabled in [false, true] {
        let mut shared = empty_shared_state();
        let a = shared.symtab.intern("zreview33_A");
        let b = shared.symtab.intern("zreview33_B");
        let r0 = shared.symtab.intern("zreview33_r0");
        let r1 = shared.symtab.intern("zreview33_r1");
        let condition = test_name(800);
        let index = test_name(801);
        let refs = test_name(802);
        let selected = test_name(803);
        let mut frame = make_frame(vec![
            Instr::Decl(condition, Ty::Bool, info()),
            Instr::Decl(index, Ty::Bits(1), info()),
            Instr::Jump(Exp::Id(condition), 5, info()),
            Instr::Copy(Loc::Id(index), Exp::Bits(B64::new(0, 1)), info()),
            Instr::Goto(6),
            Instr::Copy(Loc::Id(index), Exp::Bits(B64::new(1, 1)), info()),
            Instr::Call(
                Loc::Id(selected),
                false,
                crate::ir::READ_REGISTER_FROM_VECTOR,
                vec![Exp::Id(index), Exp::Id(refs)],
                info(),
            ),
            Instr::Copy(Loc::Id(RETURN), Exp::Unwrap(a, Box::new(Exp::Id(selected))), info()),
            Instr::End,
        ]);
        frame.vars_mut().insert(selected, UVal::Init(Val::Unit));
        frame.lets_mut().insert(refs, UVal::Init(Val::Vector(vec![Val::Ref(r0), Val::Ref(r1)])));
        frame.regs_mut().insert(r0, false, UVal::Init(Val::Ctor(a, Box::new(Val::Bits(B64::new(11, 8))))));
        frame.regs_mut().insert(r1, false, UVal::Init(Val::Ctor(b, Box::new(Val::Bits(B64::new(22, 8))))));
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
        let out = Mutex::new((0, 0, false));
        start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, mut solver, out| {
            let mut actual = out.lock().unwrap();
            match result {
                Ok((Run::Finished(_), frame)) => {
                    actual.0 += 1;
                    let UVal::Init(value) = &frame.vars()[&index] else { panic!("索引必须初始化") };
                    let invalid =
                        smtlib::Exp::Eq(Box::new(smt_value(value, info()).unwrap()), Box::new(smtlib::bits64(1, 1)));
                    actual.2 |= solver.check_sat_with(&invalid, info()).is_sat().unwrap();
                }
                Err((ExecError::Type(..), _)) => actual.1 += 1,
                _ => panic!("只能正常结束或报告标签类型错误"),
            }
        });
        observations.push((enabled, out.into_inner().unwrap()));
    }
    assert_eq!(
        observations,
        vec![(false, (1, 1, false)), (true, (1, 1, false))],
        "索引 1 的 B 构造子不能被成功解包为 A"
    );
}

fn review34_检查符号构造子解包(through_field: bool) {
    let mut observations = Vec::new();
    for enabled in [false, true] {
        let mut shared = empty_shared_state();
        let a = shared.symtab.intern("zreview34_A");
        let b = shared.symtab.intern("zreview34_B");
        let value = test_name(850);
        let field = test_name(851);
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let flag = solver.declare_const(smtlib::Ty::Bool, info());
        let ctor =
            symbolic_ctor_choice(flag, (a, Val::Bits(B64::new(11, 8))), (b, Val::Bits(B64::new(22, 8))), &mut solver);
        let expr = if through_field { Exp::Field(Box::new(Exp::Id(value)), field) } else { Exp::Id(value) };
        let unwrap = Exp::Unwrap(a, Box::new(expr.clone()));
        let mut frame = make_frame(vec![
            Instr::Jump(Exp::Kind(a, Box::new(expr)), 3, info()),
            Instr::Copy(Loc::Id(RETURN), unwrap.clone(), info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(RETURN), unwrap, info()),
            Instr::End,
        ]);
        frame.vars_mut().insert(
            value,
            UVal::Init(if through_field { Val::Struct(HashMap::from_iter([(field, ctor)])) } else { ctor }),
        );
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
        let out = Mutex::new((0, 0, false, 0));
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            &shared,
            &out,
            &|_, _, result, _, mut solver, out| {
                let mut actual = out.lock().unwrap();
                actual.3 += solver.trace().to_vec().iter().filter(|ev| matches!(ev, Event::Merge(..))).count();
                match result {
                    Ok((Run::Finished(_), _)) => {
                        actual.0 += 1;
                        actual.2 |= solver
                            .check_sat_with(&smtlib::Exp::Not(Box::new(smtlib::Exp::Var(flag))), info())
                            .is_sat()
                            .unwrap();
                    }
                    Err((ExecError::Type(..), _)) => actual.1 += 1,
                    _ => panic!("只能正常结束或报告标签错误"),
                }
            },
        );
        observations.push((enabled, out.into_inner().unwrap()));
    }
    eprintln!("字段访问={through_field}，合并开关及(完成,类型错误,错误标签可成功,合流次数)：{observations:?}");
    assert_eq!(observations[0].1, (1, 1, false, 0));
    assert_eq!(observations[1].1 .1, 1, "合流不能吞掉标签 B 的错误路径");
    assert!(!observations[1].1 .2, "成功路径不得允许标签 B");
}

#[test]
fn review34_菱形推测必须保留直接解包的错误标签路径() {
    review34_检查符号构造子解包(false);
}

#[test]
fn review34_菱形推测必须保留字段解包的错误标签路径() {
    review34_检查符号构造子解包(true);
}

#[test]
fn review34_臂条件能证明标签正确时允许合流且不得泄漏条件() {
    let mut shared = empty_shared_state();
    let a = shared.symtab.intern("zreview34_safe_A");
    let b = shared.symtab.intern("zreview34_safe_B");
    let value = test_name(852);
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let flag = solver.declare_const(smtlib::Ty::Bool, info());
    let ctor =
        symbolic_ctor_choice(flag, (a, Val::Bits(B64::new(11, 8))), (b, Val::Bits(B64::new(22, 8))), &mut solver);
    let mut frame = make_frame(vec![
        Instr::Jump(Exp::Bool(true), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Unwrap(b, Box::new(Exp::Id(value))), info()),
        Instr::Goto(4),
        Instr::Copy(Loc::Id(RETURN), Exp::Unwrap(a, Box::new(Exp::Id(value))), info()),
        Instr::End,
    ]);
    frame.vars_mut().insert(value, UVal::Init(ctor));
    assert_eq!(merge_region_for_test(flag, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(), Some(4));
    let result = eval_exp(&Exp::Id(RETURN), &mut frame.local_state, &shared, &mut solver, info()).unwrap().into_owned();
    for (condition, expected) in
        [(smtlib::Exp::Var(flag), 11), (smtlib::Exp::Not(Box::new(smtlib::Exp::Var(flag))), 22)]
    {
        let bad = smtlib::Exp::And(
            Box::new(condition.clone()),
            Box::new(smtlib::Exp::Neq(
                Box::new(smt_value(&result, info()).unwrap()),
                Box::new(smtlib::bits64(expected, 8)),
            )),
        );
        assert!(solver.check_sat_with(&condition, info()).is_sat().unwrap());
        assert!(solver.check_sat_with(&bad, info()).is_unsat().unwrap());
    }
}

#[test]
fn review34_位向量访问也必须保留混合索引的越界路径() {
    for enabled in [false, true] {
        let condition = test_name(864);
        let bits = test_name(865);
        let index = test_name(866);
        let vector = test_name(867);
        let mut frame = make_frame(vec![
            Instr::Decl(condition, Ty::Bool, info()),
            Instr::Decl(bits, Ty::Bits(8), info()),
            Instr::Decl(index, Ty::I128, info()),
            Instr::Jump(Exp::Id(condition), 6, info()),
            Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(0, 8)), info()),
            Instr::Goto(7),
            Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(2, 8)), info()),
            Instr::PrimopUnary(Loc::Id(index), primop::unary_primops()["sail_unsigned"], Exp::Id(bits), info()),
            Instr::PrimopBinary(
                Loc::Id(RETURN),
                primop::binary_primops()["vector_access"],
                Exp::Id(vector),
                Exp::Id(index),
                info(),
            ),
            Instr::End,
        ]);
        frame.lets_mut().insert(vector, UVal::Init(Val::Bits(B64::new(2, 2))));
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
        let out = Mutex::new((0, 0));
        start_single(
            frame.task(TaskId::fresh(), &state),
            &empty_shared_state(),
            &out,
            &|_, _, result, _, mut solver, out| {
                let mut actual = out.lock().unwrap();
                match result {
                    Ok((Run::Finished(value), _)) => {
                        let nonzero = smtlib::Exp::Neq(
                            Box::new(smt_value(&value, info()).unwrap()),
                            Box::new(smtlib::bits64(0, 1)),
                        );
                        assert!(solver.check_sat_with(&nonzero, info()).is_unsat().unwrap());
                        actual.0 += 1;
                    }
                    Err((ExecError::OutOfBounds("vector_access"), _)) => actual.1 += 1,
                    _ => panic!("位向量访问只能正常结束或报告越界"),
                }
            },
        );
        assert_eq!(out.into_inner().unwrap(), (1, 1));
    }
}

#[test]
fn review34_臂内标签仍有正确与错误候选时必须拒绝合流并回滚() {
    for owned in [false, true] {
        let mut shared = empty_shared_state();
        let a = shared.symtab.intern("zreview34_mixed_A");
        let b = shared.symtab.intern("zreview34_mixed_B");
        let value = test_name(868);
        let field = test_name(869);
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let condition = solver.declare_const(smtlib::Ty::Bool, info());
        let flag = solver.declare_const(smtlib::Ty::Bool, info());
        let ctor =
            symbolic_ctor_choice(flag, (a, Val::Bits(B64::new(11, 8))), (b, Val::Bits(B64::new(22, 8))), &mut solver);
        let expr = if owned {
            Exp::Field(Box::new(Exp::Struct(test_name(870), vec![(field, Exp::Id(value))])), field)
        } else {
            Exp::Id(value)
        };
        let unwrap = Exp::Unwrap(a, Box::new(expr));
        let mut frame = make_frame(vec![
            Instr::Jump(Exp::Bool(true), 3, info()),
            Instr::Copy(Loc::Id(RETURN), unwrap.clone(), info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(RETURN), unwrap, info()),
            Instr::End,
        ]);
        frame.vars_mut().insert(value, UVal::Init(ctor));
        let before = solver.trace().to_vec().len();
        assert_eq!(
            merge_region_for_test(condition, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(),
            None
        );
        assert_eq!(solver.trace().to_vec().len(), before);
        assert_eq!(frame.pc, 0);
        for arm in [true, false] {
            for tag in [true, false] {
                let choice = |sym, selected| {
                    if selected {
                        smtlib::Exp::Var(sym)
                    } else {
                        smtlib::Exp::Not(Box::new(smtlib::Exp::Var(sym)))
                    }
                };
                assert!(solver
                    .check_sat_with(
                        &smtlib::Exp::And(Box::new(choice(condition, arm)), Box::new(choice(flag, tag))),
                        info()
                    )
                    .is_sat()
                    .unwrap());
            }
        }
    }
}

#[test]
fn review34_普通向量访问必须保留合并后索引的越界错误路径() {
    let mut observations = Vec::new();
    for enabled in [false, true] {
        let condition = test_name(860);
        let bits = test_name(861);
        let index = test_name(862);
        let vector = test_name(863);
        let mut frame = make_frame(vec![
            Instr::Decl(condition, Ty::Bool, info()),
            Instr::Decl(bits, Ty::Bits(8), info()),
            Instr::Decl(index, Ty::I128, info()),
            Instr::Jump(Exp::Id(condition), 6, info()),
            Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(0, 8)), info()),
            Instr::Goto(7),
            Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(2, 8)), info()),
            Instr::PrimopUnary(Loc::Id(index), primop::unary_primops()["sail_unsigned"], Exp::Id(bits), info()),
            Instr::PrimopBinary(
                Loc::Id(RETURN),
                primop::binary_primops()["vector_access"],
                Exp::Id(vector),
                Exp::Id(index),
                info(),
            ),
            Instr::End,
        ]);
        frame.lets_mut().insert(vector, UVal::Init(Val::Vector(vec![Val::I128(10), Val::I128(20)])));
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
        let out = Mutex::new((0, 0));
        start_single(frame.task(TaskId::fresh(), &state), &empty_shared_state(), &out, &|_, _, result, _, _, out| {
            let mut actual = out.lock().unwrap();
            match result {
                Ok((Run::Finished(_), _)) => actual.0 += 1,
                Err((ExecError::OutOfBounds("vector_access"), _)) => actual.1 += 1,
                _ => panic!("只能正常结束或报告越界错误"),
            }
        });
        observations.push((enabled, out.into_inner().unwrap()));
    }
    eprintln!("合并开关及(成功路径,越界错误路径)：{observations:?}");
    assert_eq!(observations[0].1, (1, 1));
    assert_eq!(observations[1].1, (1, 1), "合流不能通过追加边界断言静默删除索引 2 的错误路径");
}
