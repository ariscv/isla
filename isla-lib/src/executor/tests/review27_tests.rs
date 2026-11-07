use super::*;

#[test]
fn 宽地址普通写独占写和带标签写必须一致检查排除区域() {
    use crate::bitvector::b129::B129;
    let mut observations = Vec::new();
    for width in [65, 128, 129] {
        for exclusive in [false, true] {
            for tagged in [false, true] {
                crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
                let ctx = Context::new(Config::new());
                let mut solver = Solver::<B129>::new(&ctx);
                let cond = solver.declare_const(smtlib::Ty::Bool, info());
                let high = B129::zeros(width).set_slice(64, B129::BIT_ONE);
                let left = Val::Bits(high | B129::new(0x1000, width));
                let right = Val::Bits(high | B129::new(0x1001, width));
                let merged = crate::primop_util::merge_val(cond, &left, &right, &mut solver, info()).unwrap();
                let mut memory = crate::memory::Memory::new();
                memory.add_excluded_region(0x1000..0x1002);
                let tag = if tagged { Some(Val::Bits(B129::BIT_ONE)) } else { None };
                let opts = if exclusive { WriteOpts::exclusive() } else { WriteOpts::default() };
                for address in [left, right] {
                    assert!(matches!(
                        memory.write(
                            Val::Unit,
                            address,
                            Val::Bits(B129::new(42, 8)),
                            &mut solver,
                            tag.clone(),
                            opts.clone()
                        ),
                        Err(ExecError::BadWrite(_))
                    ));
                }
                let result = memory.write(Val::Unit, merged, Val::Bits(B129::new(42, 8)), &mut solver, tag, opts);
                observations.push((width, exclusive, tagged, result));
            }
        }
    }
    assert!(
        observations.iter().all(|(_, _, _, result)| matches!(result, Err(ExecError::BadWrite(_)))),
        "符号写不得绕过具体写已经命中的排除区域：{observations:?}"
    );
}

#[test]
fn 宽位单态化必须完整枚举候选并维持检查点约束() {
    use crate::bitvector::b129::B129;

    for width in [65, 128, 129] {
        for ty in [Ty::Bits(width), Ty::AnyBits] {
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
            crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B129>::new(&ctx);
            let source = solver.declare_bitvector(width, info());
            let choices =
                [B129::zeros(width), B129::zeros(width).set_slice(width - 1, B129::BIT_ONE), B129::ones(width)];
            let constraint = choices.iter().fold(smtlib::Exp::Bool(false), |acc, bits| {
                smtlib::Exp::Or(
                    Box::new(acc),
                    Box::new(smtlib::Exp::Eq(
                        Box::new(smtlib::Exp::Var(source)),
                        Box::new(crate::primop_util::smt_sbits(*bits)),
                    )),
                )
            });
            solver.assert(constraint);
            let x = test_name(650);
            let instrs = vec![
                Instr::Monomorphize(x, ty.clone(), info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(x), info()),
                Instr::End,
            ];
            let mut frame =
                LocalFrame::new(test_name(25), &[], &Ty::AnyBits, None, Box::leak(instrs.into_boxed_slice()));
            frame.vars_mut().insert(x, UVal::Init(Val::Symbolic(source)));
            let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_max_forks_per_path(2));
            let out = Mutex::new(Vec::new());
            start_single(
                frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
                &shared,
                &out,
                &|_, _, result, _, mut replay, out| {
                    let Ok((Run::Finished(Val::Bits(bits)), frame)) = result else {
                        panic!("全部候选必须成功单态化")
                    };
                    assert!(choices.contains(&bits), "单态化不得产生候选域外的值");
                    let opposite = smtlib::Exp::Neq(
                        Box::new(smtlib::Exp::Var(source)),
                        Box::new(crate::primop_util::smt_sbits(bits)),
                    );
                    assert!(replay.check_sat_with(&opposite, info()).is_unsat().unwrap(), "结果必须与原始符号值相等");
                    assert!(frame.execution_limit_state.total_forks() <= 2);
                    out.lock().unwrap().push(bits);
                },
            );
            let results = out.into_inner().unwrap();
            assert_eq!(results.len(), 3, "宽度={width}，类型={ty:?}，必须恰好枚举三个候选");
            for bits in choices {
                assert_eq!(results.iter().filter(|result| **result == bits).count(), 1);
            }
        }
    }
}

#[test]
fn 菱形长度边界与循环后继不能丢失可行路径() {
    for arm_length in [1, 30, 31, 32, 62, 63, 64, 65] {
        for enabled in [false, true] {
            let cond = test_name(650);
            let value = test_name(651);
            let counter = test_name(652);
            let mut instrs = vec![
                Instr::Decl(cond, Ty::Bool, info()),
                Instr::Decl(value, Ty::Bits(8), info()),
                Instr::Decl(counter, Ty::I128, info()),
                Instr::Copy(Loc::Id(counter), Exp::I128(0), info()),
                Instr::Jump(Exp::Id(cond), 0, info()),
            ];
            for _ in 0..arm_length {
                instrs.push(Instr::Copy(Loc::Id(value), Exp::Bits(B64::new(1, 8)), info()));
            }
            let go = instrs.len();
            instrs.push(Instr::Goto(0));
            let then = instrs.len();
            for _ in 0..arm_length {
                instrs.push(Instr::Copy(Loc::Id(value), Exp::Bits(B64::new(2, 8)), info()));
            }
            let join = instrs.len();
            instrs[4] = Instr::Jump(Exp::Id(cond), then, info());
            instrs[go] = Instr::Goto(join);
            instrs.extend([
                Instr::PrimopBinary(
                    Loc::Id(counter),
                    primop::binary_primops()["add_int"],
                    Exp::Id(counter),
                    Exp::I128(1),
                    info(),
                ),
                Instr::Decl(test_name(653), Ty::Bool, info()),
                Instr::PrimopBinary(
                    Loc::Id(test_name(653)),
                    primop::binary_primops()["lt"],
                    Exp::Id(counter),
                    Exp::I128(3),
                    info(),
                ),
                Instr::Jump(Exp::Id(test_name(653)), join, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(value), info()),
                Instr::End,
            ]);
            let frame = make_frame(instrs);
            let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
            let out = Mutex::new(Vec::new());
            start_single(
                frame.task(TaskId::fresh(), &state),
                &empty_shared_state(),
                &out,
                &|_, _, result, _, mut solver, out| {
                    let Ok((Run::Finished(value), frame)) = result else {
                        panic!("有限菱形及有限循环必须完成")
                    };
                    assert!(matches!(frame.vars()[&counter], UVal::Init(Val::I128(3))));
                    let UVal::Init(condition) = &frame.vars()[&cond] else { panic!("条件必须已初始化") };
                    let expected = smtlib::Exp::Ite(
                        Box::new(smt_value(condition, info()).unwrap()),
                        Box::new(smtlib::bits64(2, 8)),
                        Box::new(smtlib::bits64(1, 8)),
                    );
                    assert!(solver
                        .check_sat_with(
                            &smtlib::Exp::Neq(Box::new(smt_value(&value, info()).unwrap()), Box::new(expected)),
                            info()
                        )
                        .is_unsat()
                        .unwrap());
                    out.lock().unwrap().push(());
                },
            );
            assert!(!out.into_inner().unwrap().is_empty(), "臂长={arm_length}，合并={enabled}");
        }
    }
}

#[test]
fn 高位非零的宽地址不能因合并改变内存分派() {
    use crate::bitvector::b129::B129;

    let mut observations = Vec::new();
    for excluded in [false, true] {
        for width in [65, 128, 129] {
            for enabled in [false, true] {
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
                let cond = test_name(650);
                let address = test_name(651);
                let left = test_name(652);
                let right = test_name(653);
                let instrs = vec![
                    Instr::Decl(cond, Ty::Bool, info()),
                    Instr::Decl(address, Ty::Bits(width), info()),
                    Instr::Jump(Exp::Id(cond), 5, info()),
                    Instr::Copy(Loc::Id(address), Exp::Id(left), info()),
                    Instr::Goto(6),
                    Instr::Copy(Loc::Id(address), Exp::Id(right), info()),
                    Instr::PrimopVariadic(
                        Loc::Id(RETURN),
                        primop::variadic_primops()["read_mem"],
                        vec![Exp::Unit, Exp::I128(i128::from(width)), Exp::Id(address), Exp::I128(1)],
                        info(),
                    ),
                    Instr::End,
                ];
                let mut frame =
                    LocalFrame::new(test_name(25), &[], &Ty::AnyBits, None, Box::leak(instrs.into_boxed_slice()));
                let high = B129::zeros(width).set_slice(64, B129::BIT_ONE);
                frame.lets_mut().insert(left, UVal::Init(Val::Bits(high | B129::new(0x1000, width))));
                frame.lets_mut().insert(right, UVal::Init(Val::Bits(high | B129::new(0x1001, width))));
                if excluded {
                    frame.memory_mut().add_excluded_region(0x1000..0x1002);
                } else {
                    frame.memory_mut().add_concrete_region(0x1000..0x1002, HashMap::from([(0x1000, 1), (0x1001, 2)]));
                }
                let state =
                    TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
                let out = Mutex::new(Vec::new());
                start_single(
                    frame.task(TaskId::fresh(), &state),
                    &shared,
                    &out,
                    &|_, _, result, _, mut solver, out| {
                        let merged = solver.trace().to_vec().iter().any(|event| matches!(event, Event::Merge(..)));
                        let outcome = match result {
                            Ok((Run::Finished(value), frame)) => {
                                let UVal::Init(condition) = &frame.vars()[&cond] else {
                                    panic!("条件必须已初始化")
                                };
                                let expected = smtlib::Exp::Ite(
                                    Box::new(smt_value(condition, info()).unwrap()),
                                    Box::new(smtlib::bits64(2, 8)),
                                    Box::new(smtlib::bits64(1, 8)),
                                );
                                let wrong = solver
                                    .check_sat_with(
                                        &smtlib::Exp::Neq(
                                            Box::new(smt_value(&value, info()).unwrap()),
                                            Box::new(expected),
                                        ),
                                        info(),
                                    )
                                    .is_sat()
                                    .unwrap();
                                Ok(wrong)
                            }
                            Err((error, _)) => Err(format!("{error:?}")),
                            _ => panic!("访存必须完成或报告访问错误"),
                        };
                        out.lock().unwrap().push((merged, outcome));
                    },
                );
                observations.push((excluded, width, enabled, out.into_inner().unwrap()));
            }
        }
    }
    eprintln!("宽地址具体及符号分派：{observations:?}");
    assert!(
        observations.iter().all(|(excluded, _, _, paths)| {
            !paths.is_empty()
                && paths.iter().all(|(_, outcome)| {
                    if *excluded {
                        matches!(outcome, Err(error) if error.contains("BadRead"))
                    } else {
                        matches!(outcome, Ok(false))
                    }
                })
        }),
        "合并不得让具体读取变成任意值，也不得绕过排除区域：{observations:?}"
    );
}

#[test]
fn 合并写事件必须与普通赋值的过滤规则一致() {
    let mut observations = Vec::new();
    for name in ["_TLB", "core_TLB", "_TLB_cache", "ordinary_reg"] {
        for enabled in [false, true] {
            let mut shared = empty_shared_state();
            let encoded = zencode::encode(name);
            let reg = shared.symtab.intern(&encoded);
            let cond = test_name(650);
            let mut frame = make_frame(vec![
                Instr::Decl(cond, Ty::Bool, info()),
                Instr::Jump(Exp::Id(cond), 4, info()),
                Instr::Copy(Loc::Id(reg), Exp::Bool(false), info()),
                Instr::Goto(5),
                Instr::Copy(Loc::Id(reg), Exp::Bool(true), info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
                Instr::End,
            ]);
            frame.regs_mut().insert(reg, false, UVal::Init(Val::Bool(false)));
            let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
            let out = Mutex::new(Vec::new());
            start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, solver, out| {
                assert!(matches!(result, Ok((Run::Finished(_), _))));
                let events = solver.trace().to_vec();
                let writes =
                    events.iter().filter(|event| matches!(event, Event::WriteReg(r, _, _) if *r == reg)).count();
                let merges = events.iter().filter(|event| matches!(event, Event::Merge(..))).count();
                out.lock().unwrap().push((writes, merges));
            });
            let paths = out.into_inner().unwrap();
            assert_eq!(paths.len(), if enabled { 1 } else { 2 });
            assert!(paths.iter().all(|(_, merges)| *merges == usize::from(enabled)));
            observations.push((name, enabled, paths));
        }
    }
    eprintln!("普通和合并后的写事件：{observations:?}");
    assert!(
        observations
            .iter()
            .all(|(name, _, paths)| { paths.iter().all(|(writes, _)| *writes == usize::from(*name != "_TLB")) }),
        "路径合并不得改变普通赋值的写事件过滤规则：{observations:?}"
    );
}

#[test]
fn 符号访存长度拆分必须覆盖每一个合法地址() {
    use std::collections::BTreeSet;

    for name in ["read_mem", "read_mem_exclusive", "platform_read_memt", "read_mem_ifetch"] {
        for enabled in [false, true] {
            let cond = test_name(650);
            let addr = test_name(651);
            let len_bits = test_name(652);
            let len = test_name(653);
            let mut frame = make_frame(vec![
                Instr::Decl(cond, Ty::Bool, info()),
                Instr::Decl(addr, Ty::Bits(64), info()),
                Instr::Copy(
                    Loc::Id(addr),
                    Exp::Call(Op::Concat, vec![Exp::Bits(B64::zeros(61)), Exp::Undefined(Ty::Bits(3))]),
                    info(),
                ),
                Instr::Decl(len_bits, Ty::Bits(8), info()),
                Instr::Decl(len, Ty::I128, info()),
                Instr::Jump(Exp::Id(cond), 8, info()),
                Instr::Copy(Loc::Id(len_bits), Exp::Bits(B64::new(4, 8)), info()),
                Instr::Goto(9),
                Instr::Copy(Loc::Id(len_bits), Exp::Bits(B64::new(8, 8)), info()),
                Instr::PrimopUnary(Loc::Id(len), primop::unary_primops()["sail_unsigned"], Exp::Id(len_bits), info()),
                Instr::PrimopVariadic(
                    Loc::Id(RETURN),
                    primop::variadic_primops()[name],
                    if name == "platform_read_memt" {
                        vec![Exp::Unit, Exp::Id(addr), Exp::Id(len)]
                    } else {
                        vec![Exp::Unit, Exp::I128(64), Exp::Id(addr), Exp::Id(len)]
                    },
                    info(),
                ),
                Instr::End,
            ]);
            frame.memory_mut().add_symbolic_code_region(0..8);
            frame.memory_mut().add_excluded_region(8..16);
            let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
            let out = Mutex::new((BTreeSet::new(), Vec::new()));
            start_single(
                frame.task(TaskId::fresh(), &state),
                &empty_shared_state(),
                &out,
                &|_, _, result, _, mut solver, out| {
                    let mut out = out.lock().unwrap();
                    match result {
                        Ok((Run::Finished(_), frame)) => {
                            let UVal::Init(address) = &frame.vars()[&addr] else { panic!("地址必须已初始化") };
                            let UVal::Init(length) = &frame.vars()[&len] else { panic!("长度必须已初始化") };
                            for candidate_len in [4, 8] {
                                for candidate_addr in 0..8 {
                                    let possible = smtlib::Exp::And(
                                        Box::new(smtlib::Exp::Eq(
                                            Box::new(smt_value(address, info()).unwrap()),
                                            Box::new(smtlib::bits64(candidate_addr, 64)),
                                        )),
                                        Box::new(smtlib::Exp::Eq(
                                            Box::new(smt_value(length, info()).unwrap()),
                                            Box::new(crate::primop_util::smt_i128(candidate_len)),
                                        )),
                                    );
                                    if solver.check_sat_with(&possible, info()).is_sat().unwrap() {
                                        out.0.insert((candidate_len, candidate_addr));
                                    }
                                }
                            }
                        }
                        Err((error, _)) => out.1.push(format!("{error:?}")),
                        _ => panic!("访存路径必须正常完成或报告访问错误"),
                    }
                },
            );
            let (actual, errors) = out.into_inner().unwrap();
            let expected = BTreeSet::from([(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (8, 0)]);
            assert_eq!(actual, expected, "操作={name}，合并={enabled}，错误={errors:?}");
        }
    }
}

#[test]
fn 宽位合并后的算术切片与具体执行逐值相同() {
    use crate::bitvector::b129::B129;
    for width in [1, 2, 8, 63, 64, 65, 127, 128, 129] {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B129>::new(&ctx);
        let cond = solver.declare_const(smtlib::Ty::Bool, info());
        let a = B129::new(1, width);
        let b = B129::ones(width);
        let merged = crate::primop_util::merge_val(cond, &Val::Bits(a), &Val::Bits(b), &mut solver, info()).unwrap();
        for select in [false, true] {
            let selected = if select { a } else { b };
            for name in ["add_bits", "sub_bits", "xor_bits", "and_bits", "or_bits", "eq_bits", "neq_bits"] {
                let op = primop::binary_primops::<B129>()[name];
                let actual = op(merged.clone(), Val::Bits(a), &mut solver, info()).unwrap();
                let expected = op(Val::Bits(selected), Val::Bits(a), &mut solver, info()).unwrap();
                let mismatch = smtlib::Exp::And(
                    Box::new(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(cond)), Box::new(smtlib::Exp::Bool(select)))),
                    Box::new(smtlib::Exp::Neq(
                        Box::new(smt_value(&actual, info()).unwrap()),
                        Box::new(smt_value(&expected, info()).unwrap()),
                    )),
                );
                assert!(
                    solver.check_sat_with(&mismatch, info()).is_unsat().unwrap(),
                    "操作={name}，宽度={width}，选臂={select}"
                );
            }
            for from in [-1, 0, i128::from(width - 1), i128::from(width), i128::MAX] {
                for length in [1, 64, 65, 129, 256] {
                    let actual =
                        primop::op_slice(merged.clone(), Val::I128(from), length, &mut solver, info()).unwrap();
                    let expected =
                        primop::op_slice(Val::Bits(selected), Val::I128(from), length, &mut solver, info()).unwrap();
                    let mismatch = smtlib::Exp::And(
                        Box::new(smtlib::Exp::Eq(
                            Box::new(smtlib::Exp::Var(cond)),
                            Box::new(smtlib::Exp::Bool(select)),
                        )),
                        Box::new(smtlib::Exp::Neq(
                            Box::new(smt_value(&actual, info()).unwrap()),
                            Box::new(smt_value(&expected, info()).unwrap()),
                        )),
                    );
                    assert!(
                        solver.check_sat_with(&mismatch, info()).is_unsat().unwrap(),
                        "切片宽度={width}，起点={from}，长度={length}，选臂={select}"
                    );
                }
            }
        }
    }
}
