use super::*;

#[test]
fn 构造子合并后必须保留错误标签解包的失败路径() {
    let mut observations = Vec::new();
    for enabled in [false, true] {
        let mut shared = empty_shared_state();
        let tag_a = shared.symtab.intern("zA");
        let tag_b = shared.symtab.intern("zB");
        let union = test_name(700);
        shared.type_info.unions.insert(union, vec![(tag_a, Ty::Bits(8)), (tag_b, Ty::Bits(8))]);
        shared.type_info.union_ctors.extend([tag_a, tag_b]);
        let cond = test_name(701);
        let value = test_name(702);
        let left = test_name(703);
        let right = test_name(704);
        let mut lets = HashMap::default();
        lets.insert(left, UVal::Init(Val::Ctor(tag_a, Box::new(Val::Bits(B64::new(11, 8))))));
        lets.insert(right, UVal::Init(Val::Ctor(tag_b, Box::new(Val::Bits(B64::new(22, 8))))));
        let results = run_all_with_bindings(
            vec![
                Instr::Decl(cond, Ty::Bool, info()),
                Instr::Decl(value, Ty::Union(union), info()),
                Instr::Jump(Exp::Id(cond), 5, info()),
                Instr::Copy(Loc::Id(value), Exp::Id(left), info()),
                Instr::Goto(6),
                Instr::Copy(Loc::Id(value), Exp::Id(right), info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Unwrap(tag_a, Box::new(Exp::Id(value))), info()),
                Instr::End,
            ],
            ExecutionLimits::default().with_path_merging(enabled),
            shared,
            RegisterBindings::new(),
            lets,
        );
        let completed = results.iter().filter(|r| matches!(r, Ok(Run::Finished(_)))).count();
        let errors = results.iter().filter(|r| matches!(r, Err(ExecError::Type(..)))).count();
        observations.push((enabled, completed, errors));
    }
    assert_eq!(observations, vec![(false, 1, 1), (true, 1, 1)], "错误标签解包不能成为成功路径");
}

#[test]
fn 重复寄存器引用的符号写索引必须保留全部写入() {
    let mut observations = Vec::new();
    for enabled in [false, true] {
        let mut shared = empty_shared_state();
        let reg = shared.symtab.intern("z重复引用的目标");
        let cond = test_name(710);
        let index = test_name(711);
        let refs = test_name(712);
        let mut frame = make_frame(vec![
            Instr::Decl(cond, Ty::Bool, info()),
            Instr::Decl(index, Ty::Bits(1), info()),
            Instr::Jump(Exp::Id(cond), 5, info()),
            Instr::Copy(Loc::Id(index), Exp::Bits(B64::new(0, 1)), info()),
            Instr::Goto(6),
            Instr::Copy(Loc::Id(index), Exp::Bits(B64::new(1, 1)), info()),
            Instr::Call(
                Loc::Id(RETURN),
                false,
                crate::ir::WRITE_REGISTER_FROM_VECTOR,
                vec![Exp::Id(index), Exp::Bits(B64::new(42, 8)), Exp::Id(refs)],
                info(),
            ),
            Instr::End,
        ]);
        frame.regs_mut().insert(reg, false, UVal::Init(Val::Bits(B64::new(17, 8))));
        frame.lets_mut().insert(refs, UVal::Init(Val::Vector(vec![Val::Ref(reg), Val::Ref(reg)])));
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
        let out = Mutex::new(Vec::new());
        start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, mut solver, out| {
            let Ok((Run::Finished(_), frame)) = result else { panic!("合法寄存器写入必须完成") };
            let value = frame.regs().get_last_if_initialized(reg).unwrap();
            let wrong = solver
                .check_sat_with(
                    &smtlib::Exp::Neq(Box::new(smt_value(value, info()).unwrap()), Box::new(smtlib::bits64(42, 8))),
                    info(),
                )
                .is_sat()
                .unwrap();
            out.lock().unwrap().push(wrong);
        });
        observations.push((enabled, out.into_inner().unwrap()));
    }
    assert!(
        observations.iter().all(|(_, paths)| !paths.is_empty() && paths.iter().all(|wrong| !wrong)),
        "相同寄存器的每一个合法引用索引都必须写入 42：{observations:?}"
    );
}

#[test]
fn 超宽地址跨排除边界的读写必须保持完整候选域和事件地址() {
    use crate::bitvector::b129::B129;
    use std::collections::BTreeSet;
    for width in [65, 129, 256] {
        for operation in ["read_mem", "read_mem_ifetch", "platform_read_memt", "write_mem", "platform_write_memt"] {
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
                let projection = smtlib::Exp::Extract(63, 0, Box::new(smtlib::Exp::Var(address)));
                solver.assert([4, 7, 8, 16].into_iter().fold(smtlib::Exp::Bool(false), |acc, low| {
                    smtlib::Exp::Or(
                        Box::new(acc),
                        Box::new(smtlib::Exp::Eq(Box::new(projection.clone()), Box::new(smtlib::bits64(low, 64)))),
                    )
                }));
                let write = operation.contains("write");
                solver.assert(if write {
                    smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(length)), Box::new(crate::primop_util::smt_i128(2)))
                } else {
                    smtlib::Exp::Or(
                        Box::new(smtlib::Exp::Eq(
                            Box::new(smtlib::Exp::Var(length)),
                            Box::new(crate::primop_util::smt_i128(1)),
                        )),
                        Box::new(smtlib::Exp::Eq(
                            Box::new(smtlib::Exp::Var(length)),
                            Box::new(crate::primop_util::smt_i128(2)),
                        )),
                    )
                });
                let a = test_name(720);
                let n = test_name(721);
                let arguments = match operation {
                    "platform_read_memt" => vec![Exp::Unit, Exp::Id(a), Exp::Id(n)],
                    "platform_write_memt" => {
                        vec![Exp::Unit, Exp::Id(a), Exp::Id(n), Exp::Bits(B64::new(42, 16)), Exp::Bits(B64::BIT_ONE)]
                    }
                    "write_mem" => {
                        vec![Exp::Unit, Exp::I128(width.into()), Exp::Id(a), Exp::Id(n), Exp::Bits(B64::new(42, 16))]
                    }
                    _ => vec![Exp::Unit, Exp::I128(width.into()), Exp::Id(a), Exp::Id(n)],
                };
                let instrs = vec![
                    Instr::PrimopVariadic(Loc::Id(RETURN), primop::variadic_primops()[operation], arguments, info()),
                    Instr::End,
                ];
                let mut frame =
                    LocalFrame::new(test_name(25), &[], &Ty::Unit, None, Box::leak(instrs.into_boxed_slice()));
                frame.vars_mut().insert(a, UVal::Init(Val::Symbolic(address)));
                frame.vars_mut().insert(n, UVal::Init(Val::Symbolic(length)));
                frame.memory_mut().add_symbolic_code_region(0..32);
                frame.memory_mut().add_excluded_region(8..16);
                let state = TaskState::new();
                let out = Arc::new(Mutex::new(BTreeSet::new()));
                let task = frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver));
                drop(frame);
                start_multi(workers, None, vec![task], &shared, out.clone(), &|_, _, result, _, mut solver, out| {
                    let events = solver.trace().to_vec();
                    let accesses: Vec<_> = events
                        .iter()
                        .filter_map(|event| match event {
                            Event::ReadMem { address, bytes, .. } | Event::WriteMem { address, bytes, .. } => {
                                Some((address.clone(), *bytes))
                            }
                            _ => None,
                        })
                        .collect();
                    match result {
                        Ok((Run::Finished(_), _)) => {
                            assert_eq!(accesses.len(), 1, "拆分重试不得重复提交访问事件");
                            assert_eq!(
                                crate::primop_util::length_bits(&accesses[0].0, &mut solver, info()).unwrap(),
                                width
                            );
                            assert!(solver
                                .check_sat_with(
                                    &smtlib::Exp::Neq(
                                        Box::new(smt_value(&accesses[0].0, info()).unwrap()),
                                        Box::new(smtlib::Exp::Var(address)),
                                    ),
                                    info()
                                )
                                .is_unsat()
                                .unwrap());
                            for low in [4, 7, 8, 16] {
                                for bytes in [1, 2] {
                                    for high in [false, true] {
                                        let selected = smtlib::Exp::And(
                                            Box::new(smtlib::Exp::Eq(
                                                Box::new(projection.clone()),
                                                Box::new(smtlib::bits64(low, 64)),
                                            )),
                                            Box::new(smtlib::Exp::And(
                                                Box::new(smtlib::Exp::Eq(
                                                    Box::new(smtlib::Exp::Var(length)),
                                                    Box::new(crate::primop_util::smt_i128(bytes)),
                                                )),
                                                Box::new(smtlib::Exp::Eq(
                                                    Box::new(smtlib::Exp::Extract(
                                                        width - 1,
                                                        width - 1,
                                                        Box::new(smtlib::Exp::Var(address)),
                                                    )),
                                                    Box::new(smtlib::bits64(u64::from(high), 1)),
                                                )),
                                            )),
                                        );
                                        if solver.check_sat_with(&selected, info()).is_sat().unwrap() {
                                            assert_eq!(accesses[0].1, bytes as u32);
                                            assert!(!(low < 16 && low + bytes as u64 > 8));
                                            out.lock().unwrap().insert((low, bytes, high));
                                        }
                                    }
                                }
                            }
                        }
                        Err((ExecError::BadRead(_) | ExecError::BadWrite(_), _)) | Ok((Run::Dead, _)) => {
                            assert!(accesses.is_empty())
                        }
                        _ => panic!("排除拆分不得产生其他执行结果"),
                    }
                });
                let pairs = if write { vec![(4, 2), (16, 2)] } else { vec![(4, 1), (4, 2), (7, 1), (16, 1), (16, 2)] };
                let expected: BTreeSet<_> =
                    pairs.into_iter().flat_map(|(a, n)| [(a, n, false), (a, n, true)]).collect();
                assert_eq!(*out.lock().unwrap(), expected, "操作={operation}，位宽={width}，线程={workers}");
            }
        }
    }
}

#[test]
fn 宽位单态化必须保留与窄候选相关的全部模型() {
    use crate::bitvector::b129::B129;
    use std::collections::BTreeSet;
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
        let source = solver.declare_bitvector(2, info());
        let extended = solver.define_bitvector(
            smtlib::Exp::Concat(
                Box::new(smtlib::Exp::Extract(1, 1, Box::new(smtlib::Exp::Var(source)))),
                Box::new(smtlib::Exp::ZeroExtend(126, Box::new(smtlib::Exp::Var(source)))),
            ),
            info(),
        );
        let x = test_name(730);
        let y = test_name(731);
        let instrs =
            vec![Instr::Monomorphize(y, Ty::AnyBits, info()), Instr::Monomorphize(x, Ty::Bits(2), info()), Instr::End];
        let mut frame = LocalFrame::new(test_name(25), &[], &Ty::Unit, None, Box::leak(instrs.into_boxed_slice()));
        frame.vars_mut().insert(x, UVal::Init(Val::Symbolic(source)));
        frame.vars_mut().insert(y, UVal::Init(Val::Symbolic(extended)));
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_max_forks_per_path(3));
        let out = Arc::new(Mutex::new(BTreeSet::new()));
        let task = frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver));
        drop(frame);
        start_multi(workers, None, vec![task], &shared, out.clone(), &|_, _, result, _, mut solver, out| {
            let Ok((Run::Finished(_), frame)) = result else { panic!("单态化必须完成") };
            let UVal::Init(Val::Bits(a)) = frame.vars()[&x] else { panic!("窄候选必须具体化") };
            let UVal::Init(Val::Bits(b)) = frame.vars()[&y] else { panic!("宽候选必须具体化") };
            assert_eq!(b.len(), 129);
            assert_eq!(b.slice(128, 1).unwrap().lower_u64(), a.lower_u64() >> 1);
            assert_eq!(b.slice(0, 128).unwrap().lower_u64(), a.lower_u64());
            assert!(
                solver
                    .check_sat_with(
                        &smtlib::Exp::Neq(
                            Box::new(smtlib::Exp::Var(extended)),
                            Box::new(crate::primop_util::smt_sbits(b)),
                        ),
                        info()
                    )
                    .is_unsat()
                    .unwrap()
            );
            assert!(out.lock().unwrap().insert(a.lower_u64()), "不得重复枚举");
        });
        assert_eq!(*out.lock().unwrap(), BTreeSet::from([0, 1, 2, 3]));
    }
}
