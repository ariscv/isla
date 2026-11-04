use super::*;

#[test]
fn 超宽地址重叠区域必须保持分派优先级和完整事件地址() {
    for width in [1, 8, 64, 65, 129, 257, 1024] {
        for fetch in [false, true] {
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
