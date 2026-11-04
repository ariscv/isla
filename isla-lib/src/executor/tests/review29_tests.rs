use super::*;

#[test]
fn 超宽地址和符号长度的排除拆分必须保持全部合法组合() {
    use crate::bitvector::b129::B129;
    use std::collections::BTreeSet;
    for width in [64, 65, 129, 256] {
        for workers in [0, 3] {
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
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let address = solver.declare_bitvector(width, info());
            let length = solver.declare_const(smtlib::Ty::BitVec(128), info());
            let candidates: Vec<_> = [4_u64, 7, 8, 16]
                .into_iter()
                .map(|low| {
                    let mut bits = vec![false; width as usize];
                    for i in 0..64 {
                        bits[i] = low & (1 << i) != 0;
                    }
                    if width > 64 {
                        bits[width as usize - 1] = true;
                    }
                    (low, smtlib::Exp::Bits(bits))
                })
                .collect();
            solver.assert(candidates.iter().fold(smtlib::Exp::Bool(false), |acc, (_, value)| {
                smtlib::Exp::Or(
                    Box::new(acc),
                    Box::new(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(address)), Box::new(value.clone()))),
                )
            }));
            solver.assert(smtlib::Exp::Or(
                Box::new(smtlib::Exp::Eq(
                    Box::new(smtlib::Exp::Var(length)),
                    Box::new(crate::primop_util::smt_i128(1)),
                )),
                Box::new(smtlib::Exp::Eq(
                    Box::new(smtlib::Exp::Var(length)),
                    Box::new(crate::primop_util::smt_i128(4)),
                )),
            ));
            let a = test_name(680);
            let n = test_name(681);
            let instrs = vec![
                Instr::PrimopVariadic(
                    Loc::Id(RETURN),
                    primop::variadic_primops()["read_mem"],
                    vec![Exp::Unit, Exp::I128(i128::from(width)), Exp::Id(a), Exp::Id(n)],
                    info(),
                ),
                Instr::End,
            ];
            let mut frame =
                LocalFrame::new(test_name(25), &[], &Ty::AnyBits, None, Box::leak(instrs.into_boxed_slice()));
            frame.vars_mut().insert(a, UVal::Init(Val::Symbolic(address)));
            frame.vars_mut().insert(n, UVal::Init(Val::Symbolic(length)));
            frame.memory_mut().add_excluded_region(8..16);
            let state = TaskState::new();
            let out = Arc::new(Mutex::new(BTreeSet::new()));
            let task = frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver));
            drop(frame);
            start_multi(workers, None, vec![task], &shared, out.clone(), &|_, _, result, _, mut solver, out| {
                match result {
                    Ok((Run::Finished(_), _)) => {
                        let events = solver.trace().to_vec();
                        let reads: Vec<_> = events
                            .iter()
                            .filter_map(|event| match event {
                                Event::ReadMem { address, bytes, .. } => Some((address.clone(), *bytes)),
                                _ => None,
                            })
                            .collect();
                        assert_eq!(reads.len(), 1, "重试不得重复发出内存事件");
                        assert_eq!(crate::primop_util::length_bits(&reads[0].0, &mut solver, info()).unwrap(), width);
                        for (low, value) in &candidates {
                            for bytes in [1, 4] {
                                let selected = smtlib::Exp::And(
                                    Box::new(smtlib::Exp::Eq(
                                        Box::new(smtlib::Exp::Var(address)),
                                        Box::new(value.clone()),
                                    )),
                                    Box::new(smtlib::Exp::Eq(
                                        Box::new(smtlib::Exp::Var(length)),
                                        Box::new(crate::primop_util::smt_i128(bytes)),
                                    )),
                                );
                                if solver.check_sat_with(&selected, info()).is_sat().unwrap() {
                                    assert!(!(*low < 16 && *low + bytes as u64 > 8), "禁止保留排除区域组合");
                                    assert_eq!(reads[0].1, bytes as u32);
                                    out.lock().unwrap().insert((*low, bytes));
                                }
                            }
                        }
                    }
                    Err((ExecError::BadRead(_), _)) | Ok((Run::Dead, _)) => {
                        assert!(!solver.trace().to_vec().iter().any(|event| matches!(event, Event::ReadMem { .. })));
                    }
                    _ => panic!("合法组合只能完成，非法组合只能判死"),
                }
            });
            assert_eq!(
                *out.lock().unwrap(),
                BTreeSet::from([(4, 1), (4, 4), (7, 1), (16, 1), (16, 4)]),
                "位宽={width}，线程={workers}"
            );
        }
    }
}

#[test]
fn 空位向量的宽切片必须与具体索引一致补零() {
    for width in [65, 128, 129, 256] {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let from = solver.declare_const(smtlib::Ty::BitVec(128), info());
        solver.assert(smtlib::Exp::Or(
            Box::new(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(from)), Box::new(crate::primop_util::smt_i128(0)))),
            Box::new(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(from)), Box::new(crate::primop_util::smt_i128(1)))),
        ));
        // 相同的合法输入，仅索引表示方式不同；具体索引已能返回宽位 SMT 零值。
        let concrete = primop::op_slice(Val::Bits(B64::zeros(0)), Val::I128(0), width, &mut solver, info()).unwrap();
        let symbolic =
            primop::op_slice(Val::Bits(B64::zeros(0)), Val::Symbolic(from), width, &mut solver, info()).unwrap();
        assert_eq!(crate::primop_util::length_bits(&symbolic, &mut solver, info()).unwrap(), width);
        assert!(solver
            .check_sat_with(
                &smtlib::Exp::Neq(
                    Box::new(smt_value(&concrete, info()).unwrap()),
                    Box::new(smt_value(&symbolic, info()).unwrap())
                ),
                info()
            )
            .is_unsat()
            .unwrap());
    }
}

#[test]
fn 连续单态化必须保留宽位候选域与相关性() {
    use crate::bitvector::b129::B129;
    for width in [65, 128, 129] {
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
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B129>::new(&ctx);
        let source = solver.declare_bitvector(width, info());
        let choices = [B129::new(7, width), B129::ones(width), B129::zeros(width).set_slice(width - 1, B129::BIT_ONE)];
        solver.assert(choices.iter().fold(smtlib::Exp::Bool(false), |acc, bits| {
            smtlib::Exp::Or(
                Box::new(acc),
                Box::new(smtlib::Exp::Eq(
                    Box::new(smtlib::Exp::Var(source)),
                    Box::new(crate::primop_util::smt_sbits(*bits)),
                )),
            )
        }));
        let inverse = solver.define_bitvector(smtlib::Exp::Bvnot(Box::new(smtlib::Exp::Var(source))), info());
        let x = test_name(680);
        let y = test_name(681);
        let instrs = vec![
            Instr::Monomorphize(x, Ty::AnyBits, info()),
            Instr::Monomorphize(y, Ty::Bits(width), info()),
            Instr::End,
        ];
        let mut frame = LocalFrame::new(test_name(25), &[], &Ty::Unit, None, Box::leak(instrs.into_boxed_slice()));
        frame.vars_mut().insert(x, UVal::Init(Val::Symbolic(source)));
        frame.vars_mut().insert(y, UVal::Init(Val::Symbolic(inverse)));
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_max_forks_per_path(2));
        let out = Mutex::new(Vec::new());
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            &shared,
            &out,
            &|_, _, result, _, mut solver, out| {
                let Ok((Run::Finished(_), frame)) = result else { panic!("连续单态化必须完成") };
                let UVal::Init(Val::Bits(a)) = frame.vars()[&x] else { panic!("首个值必须具体化") };
                let UVal::Init(Val::Bits(b)) = frame.vars()[&y] else { panic!("第二个值必须具体化") };
                assert!(choices.contains(&a));
                assert_eq!(b, !a);
                assert!(solver
                    .check_sat_with(
                        &smtlib::Exp::Neq(
                            Box::new(smtlib::Exp::Var(source)),
                            Box::new(crate::primop_util::smt_sbits(a))
                        ),
                        info()
                    )
                    .is_unsat()
                    .unwrap());
                out.lock().unwrap().push(a);
            },
        );
        let actual = out.into_inner().unwrap();
        assert_eq!(actual.len(), choices.len());
        for choice in choices {
            assert_eq!(actual.iter().filter(|value| **value == choice).count(), 1);
        }
    }
}

#[test]
fn 宽地址读取的唯一低位投影不得替换事件地址() {
    use crate::bitvector::b129::B129;
    let mut observations = Vec::new();
    for width in [65, 128, 129] {
        for enabled in [false, true] {
            for op in ["read_mem", "read_mem_ifetch", "read_mem_exclusive", "platform_read_memt"] {
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
                let cond = test_name(680);
                let address = test_name(681);
                let left = test_name(682);
                let right = test_name(683);
                let instrs = vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(address, Ty::Bits(width), info()),
                    Instr::Jump(Exp::Id(cond), 5, info()),
                    Instr::Copy(Loc::Id(address), Exp::Id(left), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(address), Exp::Id(right), info()),
                    Instr::PrimopVariadic(
                        Loc::Id(RETURN),
                        primop::variadic_primops()[op],
                        if op == "platform_read_memt" {
                            vec![Exp::Unit, Exp::Id(address), Exp::I128(1)]
                        } else {
                            vec![Exp::Unit, Exp::I128(i128::from(width)), Exp::Id(address), Exp::I128(1)]
                        },
                        info(),
                    ),
                    Instr::End,
                ];
                let mut frame =
                    LocalFrame::new(test_name(25), &[], &Ty::Bits(8), None, Box::leak(instrs.into_boxed_slice()));
                let low = B129::new(0x1000, width);
                frame.lets_mut().insert(left, UVal::Init(Val::Bits(low)));
                frame.lets_mut().insert(right, UVal::Init(Val::Bits(low.set_slice(width - 1, B129::BIT_ONE))));
                // 区域按插入顺序分派，前面的符号代码区优先处理读取。
                frame.memory_mut().add_symbolic_code_region(0x1000..0x1001);
                frame.memory_mut().add_concrete_region(0x1000..0x1001, HashMap::default());
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let out = Mutex::new(Vec::new());
                start_single(
                    frame.task(TaskId::fresh(), &state),
                    &shared,
                    &out,
                    &|_, _, result, _, mut solver, out| {
                        let Ok((Run::Finished(_), frame)) = result else { panic!("合法读取必须完成") };
                        let UVal::Init(original) = &frame.vars()[&address] else { panic!("地址必须初始化") };
                        let events = solver.trace().to_vec();
                        let event_address = events
                            .iter()
                            .find_map(|event| match event {
                                Event::ReadMem { address, .. } => Some(address.clone()),
                                _ => None,
                            })
                            .expect("必须保留读取事件");
                        let event_width = crate::primop_util::length_bits(&event_address, &mut solver, info()).unwrap();
                        let mismatch = event_width != width
                            || solver
                                .check_sat_with(
                                    &smtlib::Exp::Neq(
                                        Box::new(smt_value(original, info()).unwrap()),
                                        Box::new(smt_value(&event_address, info()).unwrap()),
                                    ),
                                    info(),
                                )
                                .is_sat()
                                .unwrap();
                        out.lock().unwrap().push((event_width, mismatch));
                    },
                );
                observations.push((width, enabled, op, out.into_inner().unwrap()));
            }
        }
    }
    assert!(
        observations.iter().all(|(width, _, _, paths)| !paths.is_empty()
            && paths.iter().all(|(actual, mismatch)| actual == width && !mismatch)),
        "读取区域分派不得损坏完整地址：{observations:?}"
    );
}
