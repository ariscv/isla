use super::*;

#[test]
fn 普通读跨符号区域必须逐地址保留区域名称() {
    let mut mismatches = Vec::new();
    for enabled in [false, true] {
        for op in ["read_mem", "read_mem_exclusive", "platform_read_memt"] {
            for second_region in [false, true] {
                let condition = test_name(780);
                let address = test_name(781);
                let mut frame = make_frame(vec![
                    Instr::Decl(condition, Ty::Bool, info()),
                    Instr::Decl(address, Ty::Bits(64), info()),
                    Instr::Jump(Exp::Id(condition), 5, info()),
                    Instr::Copy(Loc::Id(address), Exp::Bits(B64::new(0x1000, 64)), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(address), Exp::Bits(B64::new(0x2000, 64)), info()),
                    Instr::PrimopVariadic(
                        Loc::Id(RETURN),
                        primop::variadic_primops()[op],
                        if op == "platform_read_memt" {
                            vec![Exp::Unit, Exp::Id(address), Exp::I128(1)]
                        } else {
                            vec![Exp::Unit, Exp::I128(64), Exp::Id(address), Exp::I128(1)]
                        },
                        info(),
                    ),
                    Instr::End,
                ]);
                frame.memory_mut().add_symbolic_region(0x1000..0x1001);
                if second_region {
                    frame.memory_mut().add_symbolic_code_region(0x2000..0x2001);
                }
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let out = Mutex::new(Vec::new());
                start_single(
                    frame.task(TaskId::fresh(), &state),
                    &empty_shared_state(),
                    &out,
                    &|_, _, result, _, mut solver, out| {
                        assert!(matches!(result, Ok((Run::Finished(_), _))), "合法读取必须完成");
                        let events: Vec<_> = solver.trace().to_vec().into_iter().cloned().collect();
                        let reads: Vec<_> = events
                            .iter()
                            .filter_map(|event| match event {
                                Event::ReadMem { address, region, .. } => Some((address, *region)),
                                _ => None,
                            })
                            .collect();
                        assert_eq!(reads.len(), 1, "重试只能提交一个读事件");
                        for (candidate, expected) in
                            [(0x1000, "symbolic"), (0x2000, if second_region { "symbolic code" } else { "default" })]
                        {
                            let selected = smtlib::Exp::Eq(
                                Box::new(smt_value(reads[0].0, info()).unwrap()),
                                Box::new(smtlib::bits64(candidate, 64)),
                            );
                            if solver.check_sat_with(&selected, info()).is_sat().unwrap() && reads[0].1 != expected {
                                out.lock().unwrap().push((candidate, expected, reads[0].1));
                            }
                        }
                    },
                );
                mismatches.extend(out.into_inner().unwrap().into_iter().map(|item| (enabled, op, second_region, item)));
            }
        }
    }
    assert!(mismatches.is_empty(), "合并前后区域元数据必须逐地址一致：{mismatches:?}");
}

#[test]
fn relaxed寄存器不同构造子历史必须可读且保留标签候选() {
    let mut failures = Vec::new();
    for enabled in [false, true] {
        let mut shared = empty_shared_state();
        let reg = shared.symtab.intern("zreview32_relaxed");
        let a = shared.symtab.intern("zreview32_A");
        let b = shared.symtab.intern("zreview32_B");
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut frame = make_frame(vec![Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()), Instr::End]);
        frame.regs_mut().insert(reg, true, UVal::Init(Val::Ctor(a, Box::new(Val::Bits(B64::new(11, 8))))));
        frame.regs_mut().assign(reg, Val::Ctor(b, Box::new(Val::Bits(B64::new(22, 8)))), &shared);
        frame.regs_mut().forget_last_reads();
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
        let out = Mutex::new(Vec::new());
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            &shared,
            &out,
            &|_, _, result, _, mut solver, out| match result {
                Ok((Run::Finished(value), _)) => {
                    for ctor in [a, b] {
                        let kind = match &value {
                            Val::Ctor(tag, _) => smtlib::Exp::Bool(*tag == ctor),
                            Val::SymbolicCtor(tag, _) => {
                                smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(*tag)), Box::new(ctor.to_smt()))
                            }
                            value => panic!("读取必须返回构造子：{value:?}"),
                        };
                        if solver.check_sat_with(&kind, info()).is_sat().unwrap() {
                            out.lock().unwrap().push(Ok(ctor));
                        }
                    }
                }
                Err((error, _)) => out.lock().unwrap().push(Err(format!("{error:?}"))),
                _ => panic!("读取必须正常结束"),
            },
        );
        let values = out.into_inner().unwrap();
        if !values.contains(&Ok(a)) || !values.contains(&Ok(b)) {
            failures.push((enabled, values));
        }
    }
    assert!(failures.is_empty(), "合法历史读取必须保留两个构造子标签：{failures:?}");
}

#[test]
fn 宽位单态化必须保持稀疏候选及相关补码值域() {
    use crate::bitvector::b129::B129;
    for width in [1, 63, 64, 65, 127, 128, 129] {
        for workers in [0, 3] {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let source = solver.declare_bitvector(width, info());
            let inverse = solver.define_bitvector(smtlib::Exp::Bvnot(Box::new(smtlib::Exp::Var(source))), info());
            let choices = if width == 1 {
                vec![B129::zeros(width), B129::ones(width)]
            } else {
                vec![B129::zeros(width), B129::new(1, width), B129::zeros(width).set_slice(width - 1, B129::BIT_ONE)]
            };
            solver.assert(choices.iter().fold(smtlib::Exp::Bool(false), |acc, choice| {
                smtlib::Exp::Or(
                    Box::new(acc),
                    Box::new(smtlib::Exp::Eq(
                        Box::new(smtlib::Exp::Var(source)),
                        Box::new(crate::primop_util::smt_sbits(*choice)),
                    )),
                )
            }));
            let x = test_name(782);
            let y = test_name(783);
            let instrs = vec![
                Instr::Monomorphize(x, Ty::AnyBits, info()),
                Instr::Monomorphize(y, Ty::Bits(width), info()),
                Instr::End,
            ];
            let defs: &'static [crate::ir::Def<Name, B129>] = &[];
            let shared = SharedState::new(
                Symtab::new(),
                defs,
                IRTypeInfo::new(defs),
                HashSet::new(),
                HashSet::new(),
                HashSet::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            );
            let mut frame = LocalFrame::new(test_name(25), &[], &Ty::Unit, None, Box::leak(instrs.into_boxed_slice()));
            frame.vars_mut().insert(x, UVal::Init(Val::Symbolic(source)));
            frame.vars_mut().insert(y, UVal::Init(Val::Symbolic(inverse)));
            let state = TaskState::new()
                .with_execution_limits(ExecutionLimits::default().with_max_forks_per_path((choices.len() - 1) as u32));
            let out = Arc::new(Mutex::new(Vec::new()));
            let task = frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver));
            drop(frame);
            start_multi(workers, None, vec![task], &shared, out.clone(), &|_, _, result, _, mut solver, out| {
                let Ok((Run::Finished(_), frame)) = result else { panic!("有限候选必须全部完成") };
                let UVal::Init(Val::Bits(value)) = frame.vars()[&x] else { panic!("必须具化首个值") };
                let UVal::Init(Val::Bits(complement)) = frame.vars()[&y] else { panic!("必须具化相关值") };
                assert!(choices.contains(&value), "不得产生候选集外的默认值");
                assert_eq!(complement, !value);
                let wrong = smtlib::Exp::Neq(
                    Box::new(smtlib::Exp::Var(source)),
                    Box::new(crate::primop_util::smt_sbits(value)),
                );
                assert!(solver.check_sat_with(&wrong, info()).is_unsat().unwrap(), "候选必须断言回 SMT");
                out.lock().unwrap().push(value);
            });
            let actual = out.lock().unwrap();
            assert_eq!(actual.len(), choices.len());
            for choice in &choices {
                assert_eq!(actual.iter().filter(|value| *value == choice).count(), 1);
            }
        }
    }
}

#[test]
fn 超宽读事件必须保留符号高位和相关长度排除约束() {
    use std::collections::BTreeSet;
    for width in [8, 65, 129, 256] {
        for op in ["read_mem_ifetch", "read_mem_exclusive", "platform_read_memt"] {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let address = solver.declare_bitvector(width, info());
            let length = solver.declare_const(smtlib::Ty::BitVec(128), info());
            let low = if width > 64 {
                smtlib::Exp::Extract(63, 0, Box::new(smtlib::Exp::Var(address)))
            } else {
                smtlib::Exp::Var(address)
            };
            let candidates = [(5, 1), (5, 4), (7, 1), (7, 2), (16, 4)];
            let selected = |a, n| {
                smtlib::Exp::And(
                    Box::new(smtlib::Exp::Eq(Box::new(low.clone()), Box::new(smtlib::bits64(a, width.min(64))))),
                    Box::new(smtlib::Exp::Eq(
                        Box::new(smtlib::Exp::Var(length)),
                        Box::new(crate::primop_util::smt_i128(n)),
                    )),
                )
            };
            solver.assert(candidates.iter().fold(smtlib::Exp::Bool(false), |acc, (a, n)| {
                smtlib::Exp::Or(Box::new(acc), Box::new(selected(*a, *n)))
            }));
            let a = test_name(784);
            let n = test_name(785);
            let mut frame = make_frame(vec![
                Instr::PrimopVariadic(
                    Loc::Id(RETURN),
                    primop::variadic_primops()[op],
                    if op == "platform_read_memt" {
                        vec![Exp::Unit, Exp::Id(a), Exp::Id(n)]
                    } else {
                        vec![Exp::Unit, Exp::I128(width.into()), Exp::Id(a), Exp::Id(n)]
                    },
                    info(),
                ),
                Instr::End,
            ]);
            frame.vars_mut().insert(a, UVal::Init(Val::Symbolic(address)));
            frame.vars_mut().insert(n, UVal::Init(Val::Symbolic(length)));
            frame.memory_mut().add_symbolic_code_region(0..32);
            frame.memory_mut().add_excluded_region(8..16);
            let state = TaskState::new();
            let out = Mutex::new(BTreeSet::new());
            start_single(
                frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
                &empty_shared_state(),
                &out,
                &|_, _, result, _, mut solver, out| {
                    let events: Vec<_> = solver.trace().to_vec().into_iter().cloned().collect();
                    let reads: Vec<_> = events
                        .iter()
                        .filter_map(|event| match event {
                            Event::ReadMem { address, bytes, region, .. } => Some((address, *bytes, *region)),
                            _ => None,
                        })
                        .collect();
                    match result {
                        Ok((Run::Finished(_), _)) => {
                            assert_eq!(reads.len(), 1);
                            assert_eq!(reads[0].2, "symbolic code");
                            assert_eq!(
                                crate::primop_util::length_bits(reads[0].0, &mut solver, info()).unwrap(),
                                width
                            );
                            assert!(solver
                                .check_sat_with(
                                    &smtlib::Exp::Neq(
                                        Box::new(smt_value(reads[0].0, info()).unwrap()),
                                        Box::new(smtlib::Exp::Var(address)),
                                    ),
                                    info()
                                )
                                .is_unsat()
                                .unwrap());
                            for (a, n) in candidates {
                                for high in [false, true] {
                                    let mut query = selected(a, n);
                                    if width > 64 {
                                        query = smtlib::Exp::And(
                                            Box::new(query),
                                            Box::new(smtlib::Exp::Eq(
                                                Box::new(smtlib::Exp::Extract(
                                                    width - 1,
                                                    width - 1,
                                                    Box::new(smtlib::Exp::Var(address)),
                                                )),
                                                Box::new(smtlib::bits64(u64::from(high), 1)),
                                            )),
                                        );
                                    }
                                    if solver.check_sat_with(&query, info()).is_sat().unwrap() {
                                        assert_eq!(reads[0].1, n as u32);
                                        out.lock().unwrap().insert((a, n, high));
                                    }
                                }
                            }
                        }
                        Err((ExecError::BadRead(_), _)) => assert!(reads.is_empty(), "失败访问不得提交事件"),
                        _ => panic!("仅允许完成或排除区域错误"),
                    }
                },
            );
            let expected: BTreeSet<_> = [(5, 1), (7, 1), (16, 4)]
                .into_iter()
                .flat_map(|(a, n)| [false, true].map(|high| (a, n, high)))
                .collect();
            assert_eq!(*out.lock().unwrap(), expected, "宽度={width}，操作={op}");
        }
    }
}

#[test]
fn 极端菱形回边与连续寄存器事件必须逐输入一致() {
    use std::collections::BTreeSet;
    for padding in [0, 27, 28, 29, 30, 31, 63, 64, 65] {
        for special_name in ["_TLB", "core_TLB", "普通源寄存器"] {
            for enabled in [false, true] {
                let mut shared = empty_shared_state();
                let encoded = zencode::encode(special_name);
                let source = shared.symtab.intern(&encoded);
                let dest = shared.symtab.intern("zreview32_dest");
                let condition = test_name(786);
                let counter = test_name(787);
                let looping = test_name(788);
                let temporary = test_name(789);
                let mut instrs = vec![
                    Instr::Decl(condition, Ty::Bool, info()),
                    Instr::Init(counter, Ty::I128, Exp::I128(0), info()),
                    Instr::Decl(looping, Ty::Bool, info()),
                    Instr::Decl(temporary, Ty::Bits(8), info()),
                    Instr::Jump(Exp::Id(condition), 0, info()),
                    Instr::Copy(Loc::Id(dest), Exp::Bits(B64::new(1, 8)), info()),
                    Instr::Copy(Loc::Id(source), Exp::Bits(B64::new(2, 8)), info()),
                ];
                for _ in 0..padding {
                    instrs.push(Instr::Copy(Loc::Id(temporary), Exp::Bits(B64::zeros(8)), info()));
                }
                let skip = instrs.len();
                instrs.push(Instr::Goto(0));
                let then = instrs.len();
                instrs.push(Instr::Copy(Loc::Id(dest), Exp::Bits(B64::new(7, 8)), info()));
                instrs.push(Instr::Copy(Loc::Id(source), Exp::Bits(B64::new(8, 8)), info()));
                for _ in 0..padding {
                    instrs.push(Instr::Copy(Loc::Id(temporary), Exp::Bits(B64::zeros(8)), info()));
                }
                let join = instrs.len();
                instrs[4] = Instr::Jump(Exp::Id(condition), then, info());
                instrs[skip] = Instr::Goto(join);
                instrs.extend([
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(dest), info()),
                    Instr::Copy(Loc::Id(temporary), Exp::Id(source), info()),
                    Instr::PrimopBinary(
                        Loc::Id(counter),
                        primop::binary_primops()["add_int"],
                        Exp::Id(counter),
                        Exp::I128(1),
                        info(),
                    ),
                    Instr::PrimopBinary(
                        Loc::Id(looping),
                        primop::binary_primops()["lt"],
                        Exp::Id(counter),
                        Exp::I128(2),
                        info(),
                    ),
                    Instr::Jump(Exp::Id(looping), 4, info()),
                    Instr::End,
                ]);
                let mut frame = make_frame(instrs);
                frame.regs_mut().insert(source, false, UVal::Init(Val::Bits(B64::zeros(8))));
                frame.regs_mut().insert(dest, false, UVal::Init(Val::Bits(B64::zeros(8))));
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let out = Mutex::new(BTreeSet::new());
                start_single(
                    frame.task(TaskId::fresh(), &state),
                    &shared,
                    &out,
                    &|_, _, result, _, mut solver, out| {
                        let Ok((Run::Finished(value), frame)) = result else { panic!("有界回边必须完成") };
                        let UVal::Init(cond) = &frame.vars()[&condition] else { panic!("条件必须初始化") };
                        let wrong = smtlib::Exp::Neq(
                            Box::new(smt_value(&value, info()).unwrap()),
                            Box::new(smtlib::Exp::Ite(
                                Box::new(smt_value(cond, info()).unwrap()),
                                Box::new(smtlib::bits64(7, 8)),
                                Box::new(smtlib::bits64(1, 8)),
                            )),
                        );
                        assert!(solver.check_sat_with(&wrong, info()).is_unsat().unwrap());
                        let events: Vec<_> = solver
                            .trace()
                            .to_vec()
                            .into_iter()
                            .rev()
                            .filter_map(|event| match event {
                                Event::ReadReg(name, _, _) => Some((false, *name)),
                                Event::WriteReg(name, _, _) => Some((true, *name)),
                                _ => None,
                            })
                            .collect();
                        let mut expected = Vec::new();
                        for _ in 0..2 {
                            expected.push((true, dest));
                            if special_name != "_TLB" {
                                expected.push((true, source));
                            }
                            expected.push((false, dest));
                            if special_name != "_TLB" {
                                expected.push((false, source));
                            }
                        }
                        assert_eq!(events, expected, "填充={padding}，寄存器={special_name}，合并={enabled}");
                        for boolean in [false, true] {
                            let query = smtlib::Exp::Eq(
                                Box::new(smt_value(cond, info()).unwrap()),
                                Box::new(smtlib::Exp::Bool(boolean)),
                            );
                            if solver.check_sat_with(&query, info()).is_sat().unwrap() {
                                out.lock().unwrap().insert(boolean);
                            }
                        }
                    },
                );
                assert_eq!(*out.lock().unwrap(), BTreeSet::from([false, true]));
            }
        }
    }
}
