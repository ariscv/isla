use super::*;

#[test]
fn 唯一低位投影不得改变宽地址写事件() {
    use crate::bitvector::b129::B129;
    let mut observations = Vec::new();
    for width in [65, 128, 129] {
        for enabled in [false, true] {
            for tagged in [false, true] {
                for exclusive in [false, true] {
                    if tagged && exclusive {
                        continue;
                    }
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
                    let op = if tagged {
                        "platform_write_memt"
                    } else if exclusive {
                        "write_mem_exclusive"
                    } else {
                        "write_mem"
                    };
                    let args = if tagged {
                        vec![
                            Exp::Unit,
                            Exp::Id(address),
                            Exp::I128(1),
                            Exp::Bits(B64::new(42, 8)),
                            Exp::Bits(B64::BIT_ONE),
                        ]
                    } else {
                        vec![
                            Exp::Unit,
                            Exp::I128(i128::from(width)),
                            Exp::Id(address),
                            Exp::I128(1),
                            Exp::Bits(B64::new(42, 8)),
                        ]
                    };
                    let instrs = vec![
                        Instr::Decl(cond, Ty::Bool, info()),
                        Instr::Decl(address, Ty::Bits(width), info()),
                        Instr::Jump(Exp::Id(cond), 5, info()),
                        Instr::Copy(Loc::Id(address), Exp::Id(left), info()),
                        Instr::Goto(6),
                        Instr::Copy(Loc::Id(address), Exp::Id(right), info()),
                        Instr::PrimopVariadic(Loc::Id(RETURN), primop::variadic_primops()[op], args, info()),
                        Instr::End,
                    ];
                    let mut frame =
                        LocalFrame::new(test_name(25), &[], &Ty::Bool, None, Box::leak(instrs.into_boxed_slice()));
                    let low = B129::new(0x1000, width);
                    frame.lets_mut().insert(left, UVal::Init(Val::Bits(low)));
                    frame.lets_mut().insert(right, UVal::Init(Val::Bits(low.set_slice(width - 1, B129::BIT_ONE))));
                    frame.memory_mut().add_concrete_region(0x1000..0x1001, HashMap::default());
                    let state =
                        TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                    let out = Mutex::new(Vec::new());
                    start_single(
                        frame.task(TaskId::fresh(), &state),
                        &shared,
                        &out,
                        &|_, _, result, _, mut solver, out| {
                            let Ok((Run::Finished(_), frame)) = result else { panic!("合法写入必须完成") };
                            let UVal::Init(original) = &frame.vars()[&address] else { panic!("地址必须初始化") };
                            let events = solver.trace().to_vec();
                            let event_address = events
                                .iter()
                                .find_map(|event| match event {
                                    Event::WriteMem { address, .. } => Some(address.clone()),
                                    _ => None,
                                })
                                .expect("必须保留写事件");
                            let event_width =
                                crate::primop_util::length_bits(&event_address, &mut solver, info()).unwrap();
                            let mismatch = if event_width == width {
                                solver
                                    .check_sat_with(
                                        &smtlib::Exp::Neq(
                                            Box::new(smt_value(original, info()).unwrap()),
                                            Box::new(smt_value(&event_address, info()).unwrap()),
                                        ),
                                        info(),
                                    )
                                    .is_sat()
                                    .unwrap()
                            } else {
                                true
                            };
                            out.lock().unwrap().push((event_width, mismatch));
                        },
                    );
                    observations.push((width, enabled, tagged, exclusive, out.into_inner().unwrap()));
                }
            }
        }
    }
    eprintln!("宽地址写事件对照：{observations:?}");
    assert!(
        observations.iter().all(|(width, _, _, _, paths)| !paths.is_empty()
            && paths.iter().all(|(actual, mismatch)| actual == width && !mismatch)),
        "区域分派的低位投影不能替换写事件的完整地址：{observations:?}"
    );
}

#[test]
fn 排除谓词必须与完整低位投影访问区间一致() {
    use crate::bitvector::b129::B129;
    for width in [8, 64, 65, 128, 129, 256] {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B129>::new(&ctx);
        let address = solver.declare_bitvector(width, info());
        let regions = vec![
            crate::memory::Region::<B129>::Excluded(8..16),
            crate::memory::Region::<B129>::Excluded(u64::MAX - 4..u64::MAX),
            crate::memory::Region::<B129>::Excluded(256..512),
        ];
        for bytes in [1, 4, 8, u32::MAX] {
            let allowed =
                crate::memory::smt_excluded_constraint(&regions, &smtlib::Exp::Var(address), bytes, &mut solver)
                    .unwrap();
            for low in [0, 4, 7, 8, 15, 16, 255, 256, 511, 512, u64::MAX - 8, u64::MAX - 4, u64::MAX] {
                if width < 64 && low >= (1u64 << width) {
                    continue;
                }
                let mut bits = vec![false; width as usize];
                for i in 0..width.min(64) {
                    bits[i as usize] = (low >> i) & 1 != 0;
                }
                if width > 64 {
                    bits[width as usize - 1] = true;
                }
                let concrete = smtlib::Exp::Bits(bits);
                let overlap = regions.iter().any(|region| {
                    let range = region.region_range();
                    low < range.end && u128::from(low) + u128::from(bytes) > u128::from(range.start)
                });
                let mismatch = smtlib::Exp::And(
                    Box::new(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(address)), Box::new(concrete))),
                    Box::new(smtlib::Exp::Eq(Box::new(allowed.clone()), Box::new(smtlib::Exp::Bool(overlap)))),
                );
                assert!(
                    solver.check_sat_with(&mismatch, info()).is_unsat().unwrap(),
                    "宽度={width}，地址={low}，字节数={bytes}"
                );
            }
        }
    }
}

#[test]
fn 单态化必须保留有符号整数极值与布尔完整候选域() {
    for ty in [Ty::I64, Ty::I128, Ty::Bool] {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let (sort, choices) = match ty {
            Ty::I64 => {
                (smtlib::Ty::BitVec(64), vec![Val::I64(i64::MIN), Val::I64(-1), Val::I64(0), Val::I64(i64::MAX)])
            }
            Ty::I128 => {
                (smtlib::Ty::BitVec(128), vec![Val::I128(i128::MIN), Val::I128(-1), Val::I128(0), Val::I128(i128::MAX)])
            }
            Ty::Bool => (smtlib::Ty::Bool, vec![Val::Bool(false), Val::Bool(true)]),
            _ => unreachable!(),
        };
        let source = solver.declare_const(sort, info());
        solver.assert(choices.iter().fold(smtlib::Exp::Bool(false), |acc, value| {
            smtlib::Exp::Or(
                Box::new(acc),
                Box::new(smtlib::Exp::Eq(
                    Box::new(smtlib::Exp::Var(source)),
                    Box::new(smt_value(value, info()).unwrap()),
                )),
            )
        }));
        let id = test_name(680);
        let mut frame = make_frame(vec![
            Instr::Monomorphize(id, ty.clone(), info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(id), info()),
            Instr::End,
        ]);
        frame.vars_mut().insert(id, UVal::Init(Val::Symbolic(source)));
        let state = TaskState::new()
            .with_execution_limits(ExecutionLimits::default().with_max_forks_per_path((choices.len() - 1) as u32));
        let out = Mutex::new(Vec::new());
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            &empty_shared_state(),
            &out,
            &|_, _, result, _, mut solver, out| {
                let Ok((Run::Finished(value), _)) = result else { panic!("合法有限候选必须完成") };
                assert!(choices.contains(&value));
                assert!(solver
                    .check_sat_with(
                        &smtlib::Exp::Neq(
                            Box::new(smtlib::Exp::Var(source)),
                            Box::new(smt_value(&value, info()).unwrap())
                        ),
                        info()
                    )
                    .is_unsat()
                    .unwrap());
                out.lock().unwrap().push(value);
            },
        );
        let actual = out.into_inner().unwrap();
        assert_eq!(actual.len(), choices.len());
        for choice in &choices {
            assert_eq!(actual.iter().filter(|value| *value == choice).count(), 1);
        }
    }
}

#[test]
fn 写入拆分必须保留所有合法起始地址和数据值域() {
    for op in ["write_mem", "write_mem_exclusive", "platform_write_memt"] {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let addr = solver.declare_bitvector(64, info());
        let data = solver.declare_bitvector(32, info());
        solver.assert(smtlib::Exp::Bvult(Box::new(smtlib::Exp::Var(addr)), Box::new(smtlib::bits64(8, 64))));
        let address_id = test_name(680);
        let data_id = test_name(681);
        let args = if op == "platform_write_memt" {
            vec![Exp::Unit, Exp::Id(address_id), Exp::I128(4), Exp::Id(data_id), Exp::Bits(B64::BIT_ONE)]
        } else {
            vec![Exp::Unit, Exp::I128(64), Exp::Id(address_id), Exp::I128(4), Exp::Id(data_id)]
        };
        let mut frame = make_frame(vec![
            Instr::PrimopVariadic(Loc::Id(RETURN), primop::variadic_primops()[op], args, info()),
            Instr::End,
        ]);
        frame.vars_mut().insert(address_id, UVal::Init(Val::Symbolic(addr)));
        frame.vars_mut().insert(data_id, UVal::Init(Val::Symbolic(data)));
        frame.memory_mut().add_excluded_region(8..16);
        let out = Mutex::new((std::collections::BTreeSet::new(), 0));
        let state = TaskState::new();
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            &empty_shared_state(),
            &out,
            &|_, _, result, _, mut solver, out| {
                let mut out = out.lock().unwrap();
                match result {
                    Ok((Run::Finished(_), _)) => {
                        for address in 0..8 {
                            for value in [0, 1, u64::from(u32::MAX)] {
                                let candidate = smtlib::Exp::And(
                                    Box::new(smtlib::Exp::Eq(
                                        Box::new(smtlib::Exp::Var(addr)),
                                        Box::new(smtlib::bits64(address, 64)),
                                    )),
                                    Box::new(smtlib::Exp::Eq(
                                        Box::new(smtlib::Exp::Var(data)),
                                        Box::new(smtlib::bits64(value, 32)),
                                    )),
                                );
                                if solver.check_sat_with(&candidate, info()).is_sat().unwrap() {
                                    out.0.insert((address, value));
                                }
                            }
                        }
                    }
                    Err((ExecError::BadWrite(_), _)) => {
                        assert!(!solver.trace().to_vec().iter().any(|event| matches!(event, Event::WriteMem { .. })));
                        out.1 += 1;
                    }
                    _ => panic!("只允许完成或排除区域访问错误"),
                }
            },
        );
        let (actual, rejected) = out.into_inner().unwrap();
        let expected: std::collections::BTreeSet<_> =
            (0..=4).flat_map(|address| [0, 1, u64::from(u32::MAX)].map(|value| (address, value))).collect();
        assert_eq!(actual, expected, "操作={op}");
        assert_eq!(rejected, 1);
    }
}

#[test]
fn 混合特殊寄存器读取与普通写入不得改变轨迹() {
    for name in ["_TLB", "core_TLB", "_TLB_cache", "ordinary_reg"] {
        for enabled in [false, true] {
            let mut shared = empty_shared_state();
            let encoded = zencode::encode(name);
            let source = shared.symtab.intern(&encoded);
            let encoded = zencode::encode("目标寄存器");
            let dest = shared.symtab.intern(&encoded);
            let cond = test_name(680);
            let mut frame = make_frame(vec![
                Instr::Decl(cond, Ty::Bool, info()),
                Instr::Jump(Exp::Id(cond), 4, info()),
                Instr::Copy(Loc::Id(dest), Exp::Id(source), info()),
                Instr::Goto(5),
                Instr::Copy(Loc::Id(dest), Exp::Id(source), info()),
                Instr::End,
            ]);
            frame.regs_mut().insert(source, false, UVal::Init(Val::Bits(B64::new(17, 8))));
            frame.regs_mut().insert(dest, false, UVal::Init(Val::Bits(B64::new(0, 8))));
            let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
            let out = Mutex::new(Vec::new());
            start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, solver, out| {
                let Ok((Run::Finished(_), frame)) = result else { panic!("混合寄存器读写必须完成") };
                assert_eq!(frame.regs().get_last_if_initialized(dest), Some(&Val::Bits(B64::new(17, 8))));
                let events: Vec<_> = solver
                    .trace()
                    .to_vec()
                    .into_iter()
                    .rev()
                    .filter_map(|event| match event {
                        Event::ReadReg(id, _, _) => Some((false, *id)),
                        Event::WriteReg(id, _, _) => Some((true, *id)),
                        _ => None,
                    })
                    .collect();
                let mut expected = Vec::new();
                if name != "_TLB" {
                    expected.push((false, source));
                }
                expected.push((true, dest));
                assert_eq!(events, expected);
                out.lock().unwrap().push(());
            });
            assert_eq!(out.into_inner().unwrap().len(), if enabled { 1 } else { 2 });
        }
    }
}

#[test]
fn 交叉跳转与连续菱形必须逐输入保持结果和路径覆盖() {
    use std::collections::BTreeSet;
    for blocks in [1, 15, 16, 21, 22, 33] {
        for seed in 0..4 {
            let conditions = [test_name(680), test_name(681), test_name(682)];
            let value = test_name(683);
            let mut instrs = conditions.iter().map(|id| Instr::Decl(*id, Ty::Bool, info())).collect::<Vec<_>>();
            instrs.push(Instr::Decl(value, Ty::Bits(8), info()));
            instrs.push(Instr::Copy(Loc::Id(value), Exp::Bits(B64::zeros(8)), info()));
            for block in 0..blocks {
                let next = (block + 1 + (block * 7 + seed) % 3).min(blocks);
                instrs.push(Instr::Jump(Exp::Id(conditions[(block + seed) % 3]), 5 + next * 3, info()));
                instrs.push(Instr::Copy(Loc::Id(value), Exp::Bits(B64::new((block + 1) as u64, 8)), info()));
                instrs.push(Instr::Goto(5 + (block + 1) * 3));
            }
            instrs.push(Instr::Copy(Loc::Id(RETURN), Exp::Id(value), info()));
            instrs.push(Instr::End);
            for enabled in [false, true] {
                let frame = make_frame(instrs.clone());
                let out = Mutex::new(BTreeSet::new());
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                start_single(
                    frame.task(TaskId::fresh(), &state),
                    &empty_shared_state(),
                    &out,
                    &|_, _, result, _, mut solver, out| {
                        let Ok((Run::Finished(actual), frame)) = result else {
                            panic!("有限前向控制流必须正常完成")
                        };
                        for input in 0..8 {
                            let mut selected = smtlib::Exp::Bool(true);
                            for (i, id) in conditions.iter().enumerate() {
                                if let UVal::Init(condition) = &frame.vars()[id] {
                                    selected = smtlib::Exp::And(
                                        Box::new(selected),
                                        Box::new(smtlib::Exp::Eq(
                                            Box::new(smt_value(condition, info()).unwrap()),
                                            Box::new(smtlib::Exp::Bool(input & (1 << i) != 0)),
                                        )),
                                    );
                                }
                            }
                            if !solver.check_sat_with(&selected, info()).is_sat().unwrap() {
                                continue;
                            }
                            let mut expected = 0;
                            let mut block = 0;
                            while block < blocks {
                                if input & (1 << ((block + seed) % 3)) != 0 {
                                    block = (block + 1 + (block * 7 + seed) % 3).min(blocks);
                                } else {
                                    expected = block + 1;
                                    block += 1;
                                }
                            }
                            let wrong = smtlib::Exp::And(
                                Box::new(selected),
                                Box::new(smtlib::Exp::Neq(
                                    Box::new(smt_value(&actual, info()).unwrap()),
                                    Box::new(smtlib::bits64(expected as u64, 8)),
                                )),
                            );
                            assert!(
                                solver.check_sat_with(&wrong, info()).is_unsat().unwrap(),
                                "块数={blocks}，种子={seed}，合并={enabled}，输入={input}"
                            );
                            out.lock().unwrap().insert(input);
                        }
                    },
                );
                assert_eq!(
                    out.into_inner().unwrap(),
                    BTreeSet::from([0, 1, 2, 3, 4, 5, 6, 7]),
                    "块数={blocks}，种子={seed}，合并={enabled}"
                );
            }
        }
    }
}

#[test]
fn 宽位符号程序计数器必须与等值具体计数器保持公告限制一致() {
    use crate::bitvector::b129::B129;
    let mut observations = Vec::new();
    for width in [64, 65, 128, 129] {
        for symbolic_pc in [false, true] {
            let result = std::panic::catch_unwind(|| {
                let defs: &'static [crate::ir::Def<Name, B129>] = &[];
                let mut shared = SharedState::new(
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
                let pc = shared.symtab.intern("zreview28_pc");
                let ctx = Context::new(Config::new());
                let mut solver = Solver::<B129>::new(&ctx);
                let bits = B129::new(0x1000, width);
                let pc_value = if symbolic_pc {
                    Val::Symbolic(solver.define_bitvector(crate::primop_util::smt_sbits(bits), info()))
                } else {
                    Val::Bits(bits)
                };
                let instrs = vec![
                    Instr::Call(Loc::Id(RETURN), false, INSTR_ANNOUNCE, vec![Exp::Bits(B64::new(0x13, 32))], info()),
                    Instr::End,
                ];
                let mut frame =
                    LocalFrame::new(test_name(25), &[], &Ty::Unit, None, Box::leak(instrs.into_boxed_slice()));
                frame.regs_mut().insert(pc, false, UVal::Init(pc_value));
                let state = TaskState::new().with_pc_limit(pc, 1);
                let out = Mutex::new(Vec::new());
                start_single(
                    frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
                    &shared,
                    &out,
                    &|_, _, result, _, _, out| {
                        out.lock().unwrap().push(matches!(result, Ok((Run::Finished(_), _))));
                    },
                );
                out.into_inner().unwrap() == vec![true]
            });
            observations.push((width, symbolic_pc, matches!(result, Ok(true))));
        }
    }
    eprintln!("宽位 PC 公告对照：{observations:?}");
    assert!(observations.iter().all(|(_, _, passed)| *passed), "等值符号 PC 不得导致公告 panic：{observations:?}");
}
