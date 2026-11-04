use super::*;

#[test]
fn 合并后的普通读必须保留符号区域名称() {
    let mut observations = Vec::new();
    for enabled in [false, true] {
        for code in [false, true] {
            let condition = test_name(750);
            let address = test_name(751);
            let mut frame = make_frame(vec![
                Instr::Decl(condition, Ty::Bool, info()),
                Instr::Decl(address, Ty::Bits(64), info()),
                Instr::Jump(Exp::Id(condition), 5, info()),
                Instr::Copy(Loc::Id(address), Exp::Bits(B64::new(0x1000, 64)), info()),
                Instr::Goto(6),
                Instr::Copy(Loc::Id(address), Exp::Bits(B64::new(0x1001, 64)), info()),
                Instr::PrimopVariadic(
                    Loc::Id(RETURN),
                    primop::variadic_primops()["read_mem"],
                    vec![Exp::Unit, Exp::I128(64), Exp::Id(address), Exp::I128(1)],
                    info(),
                ),
                Instr::End,
            ]);
            if code {
                frame.memory_mut().add_symbolic_code_region(0x1000..0x2000);
            } else {
                frame.memory_mut().add_symbolic_region(0x1000..0x2000);
            }
            let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
            let out = Mutex::new(Vec::new());
            start_single(
                frame.task(TaskId::fresh(), &state),
                &empty_shared_state(),
                &out,
                &|_, _, result, _, solver, out| {
                    assert!(matches!(result, Ok((Run::Finished(_), _))), "合法读取必须完成");
                    let events: Vec<_> = solver.trace().to_vec().into_iter().cloned().collect();
                    let names: Vec<_> = events
                        .iter()
                        .filter_map(|event| match event {
                            Event::ReadMem { region, .. } => Some(*region),
                            _ => None,
                        })
                        .collect();
                    assert_eq!(names.len(), 1);
                    out.lock().unwrap().extend(names);
                },
            );
            observations.push((enabled, code, out.into_inner().unwrap()));
        }
    }
    assert!(
        observations.iter().all(|(_, code, regions)| regions
            .iter()
            .all(|region| *region == if *code { "symbolic code" } else { "symbolic" })),
        "普通读的区域元数据必须与具体地址分派一致：{observations:?}"
    );
}

#[test]
fn 合并索引经向量选出构造子后必须保留错误解包路径() {
    let mut observations = Vec::new();
    for enabled in [false, true] {
        let mut shared = empty_shared_state();
        let tag_a = shared.symtab.intern("zA");
        let tag_b = shared.symtab.intern("zB");
        let union = test_name(755);
        shared.type_info.unions.insert(union, vec![(tag_a, Ty::Bits(8)), (tag_b, Ty::Bits(8))]);
        shared.type_info.union_ctors.extend([tag_a, tag_b]);
        let condition = test_name(750);
        let bits = test_name(751);
        let index = test_name(752);
        let vector = test_name(753);
        let selected = test_name(754);
        let mut bindings = Bindings::default();
        bindings.insert(
            vector,
            UVal::Init(Val::Vector(vec![
                Val::Ctor(tag_a, Box::new(Val::Bits(B64::new(11, 8)))),
                Val::Ctor(tag_b, Box::new(Val::Bits(B64::new(22, 8)))),
            ])),
        );
        let results = run_all_with_bindings(
            vec![
                Instr::Decl(condition, Ty::Bool, info()),
                Instr::Decl(bits, Ty::Bits(1), info()),
                Instr::Jump(Exp::Id(condition), 5, info()),
                Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(0, 1)), info()),
                Instr::Goto(6),
                Instr::Copy(Loc::Id(bits), Exp::Bits(B64::new(1, 1)), info()),
                Instr::Decl(index, Ty::I128, info()),
                Instr::Decl(selected, Ty::Union(union), info()),
                Instr::PrimopUnary(Loc::Id(index), primop::unary_primops()["sail_unsigned"], Exp::Id(bits), info()),
                Instr::PrimopBinary(
                    Loc::Id(selected),
                    primop::binary_primops()["vector_access"],
                    Exp::Id(vector),
                    Exp::Id(index),
                    info(),
                ),
                Instr::Copy(Loc::Id(RETURN), Exp::Unwrap(tag_a, Box::new(Exp::Id(selected))), info()),
                Instr::End,
            ],
            ExecutionLimits::default().with_path_merging(enabled),
            shared,
            RegisterBindings::new(),
            bindings,
        );
        observations.push((
            enabled,
            results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count(),
            results.iter().filter(|r| matches!(r, Err(ExecError::Type(..)))).count(),
        ));
    }
    assert_eq!(observations, vec![(false, 1, 1), (true, 1, 1)], "向量消费者不能重新引入无法安全解包的标签合并");
}

#[test]
fn 具体区和受约束区的符号宽地址读事件必须保留原始地址() {
    use crate::bitvector::b129::B129;
    let mut observations = Vec::new();
    for width in [65, 129, 256] {
        for constrained in [false, true] {
            for fetch in [false, true] {
                let ctx = Context::new(Config::new());
                let mut solver = Solver::<B129>::new(&ctx);
                let address = solver.declare_bitvector(width, info());
                solver.assert_eq(
                    smtlib::Exp::Extract(63, 0, Box::new(smtlib::Exp::Var(address))),
                    smtlib::bits64(0x1000, 64),
                );
                let mut memory = crate::memory::Memory::new();
                if constrained {
                    memory.add_region(crate::memory::Region::Constrained(
                        0x1000..0x1001,
                        Arc::new(|solver| solver.define_bitvector(smtlib::bits64(42, 8), info())),
                    ));
                } else {
                    memory.add_concrete_region(0x1000..0x1001, HashMap::from([(0x1000, 42)]));
                }
                memory
                    .read(
                        Val::Unit,
                        Val::Symbolic(address),
                        Val::I128(1),
                        &mut solver,
                        false,
                        if fetch { ReadOpts::ifetch() } else { ReadOpts::default() },
                    )
                    .unwrap();
                let events: Vec<_> = solver.trace().to_vec().into_iter().cloned().collect();
                let event_address = events
                    .iter()
                    .find_map(|event| match event {
                        Event::ReadMem { address, .. } => Some(address.clone()),
                        _ => None,
                    })
                    .unwrap();
                let event_width = crate::primop_util::length_bits(&event_address, &mut solver, info()).unwrap();
                observations.push((width, constrained, fetch, event_width));
            }
        }
    }
    assert!(
        observations.iter().all(|(width, _, _, actual)| width == actual),
        "具体区分派不得将完整事件地址替换为低位投影：{observations:?}"
    );
}

#[test]
fn 边界菱形和回边必须保持单态化候选与特殊寄存器事件() {
    use std::collections::BTreeSet;
    for arm_length in [1, 31, 63, 64, 65] {
        for enabled in [false, true] {
            for register_name in ["_TLB", "cache_TLB", "普通寄存器"] {
                let encoded = zencode::encode(register_name);
                let mut shared = empty_shared_state();
                let reg = shared.symtab.intern(&encoded);
                let condition = test_name(760);
                let value = test_name(761);
                let iterations = test_name(762);
                let looping = test_name(763);
                let mut instrs = vec![
                    Instr::Decl(condition, Ty::Bool, info()),
                    Instr::Decl(value, Ty::Bits(8), info()),
                    Instr::Init(iterations, Ty::I128, Exp::I128(0), info()),
                    Instr::Decl(looping, Ty::Bool, info()),
                    Instr::Jump(Exp::Id(condition), 0, info()),
                ];
                for _ in 0..arm_length {
                    instrs.push(Instr::Copy(Loc::Id(value), Exp::Bits(B64::new(7, 8)), info()));
                }
                let skip_then = instrs.len();
                instrs.push(Instr::Goto(0));
                let then = instrs.len();
                for _ in 0..arm_length {
                    instrs.push(Instr::Copy(Loc::Id(value), Exp::Bits(B64::new(9, 8)), info()));
                }
                let join = instrs.len();
                instrs[4] = Instr::Jump(Exp::Id(condition), then, info());
                instrs[skip_then] = Instr::Goto(join);
                instrs.extend([
                    Instr::PrimopBinary(
                        Loc::Id(iterations),
                        primop::binary_primops()["add_int"],
                        Exp::Id(iterations),
                        Exp::I128(1),
                        info(),
                    ),
                    Instr::PrimopBinary(
                        Loc::Id(looping),
                        primop::binary_primops()["lt"],
                        Exp::Id(iterations),
                        Exp::I128(3),
                        info(),
                    ),
                    Instr::Jump(Exp::Id(looping), join, info()),
                    Instr::Monomorphize(value, Ty::Bits(8), info()),
                    Instr::Copy(Loc::Id(reg), Exp::Id(value), info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
                    Instr::End,
                ]);
                let mut frame = make_frame(instrs);
                frame.regs_mut().insert(reg, false, UVal::Init(Val::Bits(B64::zeros(8))));
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let out = Arc::new(Mutex::new(BTreeSet::new()));
                let task = frame.task(TaskId::fresh(), &state);
                drop(frame);
                start_multi(3, None, vec![task], &shared, out.clone(), &|_, _, result, _, mut solver, out| {
                    let Ok((Run::Finished(Val::Bits(actual)), frame)) = result else {
                        panic!("有限控制流与单态化必须完成")
                    };
                    assert!(matches!(frame.vars()[&iterations], UVal::Init(Val::I128(3))));
                    let UVal::Init(Val::Symbolic(cond)) = frame.vars()[&condition] else {
                        panic!("分支条件必须保留")
                    };
                    let wrong = smtlib::Exp::Neq(
                        Box::new(crate::primop_util::smt_sbits(actual)),
                        Box::new(smtlib::Exp::Ite(
                            Box::new(smtlib::Exp::Var(cond)),
                            Box::new(smtlib::bits64(9, 8)),
                            Box::new(smtlib::bits64(7, 8)),
                        )),
                    );
                    assert!(solver.check_sat_with(&wrong, info()).is_unsat().unwrap(), "结果必须属于对应分支的候选域");
                    let events: Vec<_> = solver.trace().to_vec().into_iter().cloned().collect();
                    let writes = events
                        .iter()
                        .filter(|event| matches!(event, Event::WriteReg(name, _, _) if *name == reg))
                        .count();
                    let reads = events
                        .iter()
                        .filter(|event| matches!(event, Event::ReadReg(name, _, _) if *name == reg))
                        .count();
                    assert_eq!(writes, usize::from(register_name != "_TLB"));
                    assert_eq!(reads, usize::from(!register_name.contains("_TLB")));
                    out.lock().unwrap().insert(actual.lower_u64());
                });
                assert_eq!(*out.lock().unwrap(), BTreeSet::from([7, 9]), "臂长度={arm_length}，合并={enabled}");
            }
        }
    }
}

#[test]
fn 相关符号长度与超宽取指地址必须保留合法组合和完整轨迹() {
    use std::collections::BTreeSet;
    for width in [8, 64, 129, 256] {
        let shared = empty_shared_state();
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let address = solver.declare_bitvector(width, info());
        let length = solver.declare_const(smtlib::Ty::BitVec(128), info());
        let low = if width > 64 {
            smtlib::Exp::Extract(63, 0, Box::new(smtlib::Exp::Var(address)))
        } else {
            smtlib::Exp::Var(address)
        };
        let candidates = [(6, 1), (6, 2), (6, 4), (7, 1), (7, 2), (16, 4)];
        let selected = |a, n| {
            smtlib::Exp::And(
                Box::new(smtlib::Exp::Eq(Box::new(low.clone()), Box::new(smtlib::bits64(a, width.min(64))))),
                Box::new(smtlib::Exp::Eq(
                    Box::new(smtlib::Exp::Var(length)),
                    Box::new(crate::primop_util::smt_i128(n)),
                )),
            )
        };
        solver.assert(
            candidates.iter().fold(smtlib::Exp::Bool(false), |acc, (a, n)| {
                smtlib::Exp::Or(Box::new(acc), Box::new(selected(*a, *n)))
            }),
        );
        let a = test_name(770);
        let n = test_name(771);
        let mut frame = make_frame(vec![
            Instr::PrimopVariadic(
                Loc::Id(RETURN),
                primop::variadic_primops()["read_mem_ifetch"],
                vec![Exp::Unit, Exp::I128(i128::from(width)), Exp::Id(a), Exp::Id(n)],
                info(),
            ),
            Instr::End,
        ]);
        frame.vars_mut().insert(a, UVal::Init(Val::Symbolic(address)));
        frame.vars_mut().insert(n, UVal::Init(Val::Symbolic(length)));
        frame.memory_mut().add_symbolic_code_region(0..32);
        frame.memory_mut().add_excluded_region(8..16);
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_max_forks_per_path(4));
        let out = Arc::new(Mutex::new(BTreeSet::new()));
        let task = frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver));
        drop(frame);
        start_multi(3, None, vec![task], &shared, out.clone(), &|_, _, result, _, mut solver, out| {
            let events: Vec<_> = solver.trace().to_vec().into_iter().cloned().collect();
            match result {
                Ok((Run::Finished(_), _)) => {
                    let reads: Vec<_> = events
                        .iter()
                        .filter_map(|event| match event {
                            Event::ReadMem { address, bytes, opts, region, .. } => {
                                Some((address.clone(), *bytes, opts.clone(), *region))
                            }
                            _ => None,
                        })
                        .collect();
                    assert_eq!(reads.len(), 1, "重试不得重复读事件");
                    assert!(reads[0].2.is_ifetch);
                    assert_eq!(reads[0].3, "symbolic code");
                    assert_eq!(crate::primop_util::length_bits(&reads[0].0, &mut solver, info()).unwrap(), width);
                    for (a, n) in candidates {
                        if solver.check_sat_with(&selected(a, n), info()).is_sat().unwrap() {
                            assert!(!(a < 16 && u128::from(a) + n as u128 > 8));
                            assert_eq!(reads[0].1, n as u32);
                            if width > 64 {
                                let high_set = smtlib::Exp::And(
                                    Box::new(selected(a, n)),
                                    Box::new(smtlib::Exp::Eq(
                                        Box::new(smtlib::Exp::Extract(
                                            width - 1,
                                            width - 1,
                                            Box::new(smtlib::Exp::Var(address)),
                                        )),
                                        Box::new(smtlib::bits64(1, 1)),
                                    )),
                                );
                                assert!(
                                    solver.check_sat_with(&high_set, info()).is_sat().unwrap(),
                                    "高位候选不能被区域分派收窄"
                                );
                            }
                            out.lock().unwrap().insert((a, n));
                        }
                    }
                }
                Err((ExecError::BadRead(_), _)) | Ok((Run::Dead, _)) => {
                    assert!(!events.iter().any(|event| matches!(event, Event::ReadMem { .. })))
                }
                _ => panic!("合法组合必须完成，排除组合只能判死"),
            }
        });
        assert_eq!(*out.lock().unwrap(), BTreeSet::from([(6, 1), (6, 2), (7, 1), (16, 4)]));
    }
}
