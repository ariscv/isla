use super::*;

#[test]
fn review35_vector_update_must_keep_oob_path() {
    let mut observations = Vec::new();
    for width in [64, 128] {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let index = solver.declare_const(smtlib::Ty::BitVec(width), info());
        solver.assert(smtlib::Exp::Or(
            Box::new(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(index)), Box::new(smtlib::bits64(0, width)))),
            Box::new(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(index)), Box::new(smtlib::bits64(2, width)))),
        ));
        let n = test_name(860);
        let values = test_name(861);
        let mut frame = make_frame(vec![
            Instr::PrimopVariadic(
                Loc::Id(RETURN),
                primop::variadic_primops()["vector_update"],
                vec![Exp::Id(values), Exp::Id(n), Exp::Bits(B64::new(0xa5, 8))],
                info(),
            ),
            Instr::End,
        ]);
        frame.vars_mut().insert(n, UVal::Init(Val::Symbolic(index)));
        frame.vars_mut().insert(values, UVal::Init(Val::Vector(vec![Val::Bits(B64::new(0, 8)); 2])));
        let state = TaskState::new();
        let out = Mutex::new((0, 0));
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            &empty_shared_state(),
            &out,
            &|_, _, result, _, _, out| {
                let mut counts = out.lock().unwrap();
                match result {
                    Ok((Run::Finished(_), _)) => counts.0 += 1,
                    Err((ExecError::OutOfBounds(_), _)) => counts.1 += 1,
                    _ => panic!("应完成更新或报告越界"),
                }
            },
        );
        observations.push((width, *out.lock().unwrap()));
    }
    assert!(observations.iter().all(|(_, counts)| *counts == (1, 1)), "越界路径不得由断言抹掉：{observations:?}");
}

#[test]
fn review35_bitvector_update_must_reject_oob() {
    let mut failures = Vec::new();
    for n in [-1, 8, 1_i128 << 64] {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let index = solver.declare_const(smtlib::Ty::BitVec(128), info());
        solver.assert_eq(smtlib::Exp::Var(index), crate::primop_util::smt_i128(n));
        let mut frame = make_frame(vec![Instr::End]);
        let actual = primop::vector_update(
            vec![Val::Bits(B64::new(0, 8)), Val::Symbolic(index), Val::Bits(B64::new(1, 1))],
            &mut solver,
            &mut frame,
            info(),
        );
        if !matches!(actual, Err(ExecError::OutOfBounds(_))) {
            failures.push((n, actual));
        }
    }
    assert!(failures.is_empty(), "越界位更新必须报告OutOfBounds：{failures:?}");
}

#[test]
fn review35_unwrap_must_not_succeed_for_wrong_symbolic_tag() {
    let mut failures = Vec::new();
    for owned in [false, true] {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let flag = solver.declare_const(smtlib::Ty::Bool, info());
        let a = test_name(862);
        let b = test_name(863);
        let value = test_name(864);
        let field = test_name(865);
        let ctor =
            symbolic_ctor_choice(flag, (a, Val::Bits(B64::new(11, 8))), (b, Val::Bits(B64::new(22, 8))), &mut solver);
        let mut frame = make_frame(vec![Instr::End]);
        frame.vars_mut().insert(value, UVal::Init(ctor));
        let exp = if owned {
            Exp::Field(Box::new(Exp::Struct(test_name(866), vec![(field, Exp::Id(value))])), field)
        } else {
            Exp::Id(value)
        };
        let actual = eval_exp(
            &Exp::Unwrap(a, Box::new(exp)),
            &mut frame.local_state,
            &empty_shared_state(),
            &mut solver,
            info(),
        )
        .map(Cow::into_owned);
        if actual.is_ok()
            && solver.check_sat_with(&smtlib::Exp::Not(Box::new(smtlib::Exp::Var(flag))), info()).is_sat().unwrap()
        {
            failures.push((owned, actual));
        }
    }
    assert!(failures.is_empty(), "成功解包仍允许标签B：{failures:?}");
}

#[test]
fn review35_vector_register_access_must_filter_tlb() {
    let mut failures = Vec::new();
    for write in [false, true] {
        let mut shared = empty_shared_state();
        let encoded = crate::zencode::encode("_TLB");
        let tlb = shared.symtab.intern(&encoded);
        let mut frame = make_frame(vec![Instr::End]);
        frame.regs_mut().insert(tlb, false, UVal::Init(Val::Bits(B64::new(0, 8))));
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let refs = Val::Vector(vec![Val::Ref(tlb)]);
        if write {
            write_register_from_vector(
                Val::I128(0),
                Val::Bits(B64::new(1, 8)),
                refs,
                &mut frame.local_state,
                &shared,
                &mut solver,
                info(),
            )
            .unwrap();
        } else {
            read_register_from_vector(Val::I128(0), refs, &mut frame.local_state, &shared, &mut solver, info())
                .unwrap();
        }
        if solver
            .trace()
            .to_vec()
            .iter()
            .any(|e| matches!(e, Event::ReadReg(reg, ..) | Event::WriteReg(reg, ..) if *reg == tlb))
        {
            failures.push(write);
        }
    }
    assert!(failures.is_empty(), "向量寄存器入口漏过滤整个_TLB，write={failures:?}");
}

#[test]
fn review35_concrete_vector_indices_must_not_truncate() {
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let access = primop::binary_primops::<B64>()["vector_access"];
    let mut failures = Vec::new();
    for n in [1_i128 << 64, -(1_i128 << 64)] {
        let actual = access(Val::Vector(vec![Val::Bool(false)]), Val::I128(n), &mut solver, info());
        if !matches!(actual, Err(ExecError::OutOfBounds(_))) {
            failures.push((n, false, actual));
        }
        let mut frame = make_frame(vec![Instr::End]);
        let actual = primop::vector_update(
            vec![Val::Vector(vec![Val::Bool(false)]), Val::I128(n), Val::Bool(true)],
            &mut solver,
            &mut frame,
            info(),
        );
        if !matches!(actual, Err(ExecError::OutOfBounds(_))) {
            failures.push((n, true, actual));
        }
    }
    assert!(failures.is_empty(), "宽整数索引被截断为0：{failures:?}");
}

#[test]
fn review35_b129_arithmetic_independent_oracle() {
    use crate::bitvector::b129::B129;
    use num_bigint::{BigInt, Sign};
    for width in [1u32, 64, 128, 129] {
        let modulus: BigInt = BigInt::from(1) << width;
        for value in [BigInt::from(0), BigInt::from(1), &modulus - 1, BigInt::from(1) << (width - 1)] {
            let input_bits: Vec<bool> =
                (0..width).map(|i| ((&value >> i) & BigInt::from(1)) == BigInt::from(1)).collect();
            let bits = input_bits.iter().enumerate().fold(B129::zeros(width), |bv, (i, bit)| {
                if *bit {
                    bv.set_slice(i as u32, B129::BIT_ONE)
                } else {
                    bv
                }
            });
            for n in [i128::MIN, -1, 0, 1, i128::MAX] {
                for subtract in [false, true] {
                    let expected = if subtract { &value - BigInt::from(n) } else { &value + BigInt::from(n) };
                    let expected: BigInt = ((expected % &modulus) + &modulus) % &modulus;
                    assert_ne!(expected.sign(), Sign::Minus);
                    let expected_bits: Vec<bool> =
                        (0..width).map(|i| ((&expected >> i) & BigInt::from(1)) == BigInt::from(1)).collect();
                    let actual = if subtract { bits.sub_i128(n) } else { bits.add_i128(n) };
                    assert_eq!(actual.to_vec(), expected_bits, "width={width}, n={n}, sub={subtract}");
                }
            }
            let expected_ctz = input_bits.iter().position(|b| *b).unwrap_or(width as usize) as u32;
            assert_eq!(bits.trailing_zeros(), expected_ctz);
        }
    }
}

#[test]
fn review35_fp_classification_and_conversion_markers() {
    use crate::bitvector::b129::B129;
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B129>::new(&ctx);
    let unary = primop::unary_primops::<B129>();
    let binary = primop::binary_primops::<B129>();
    for (width, exp_bits, fraction_bits) in [(16, 5, 10), (32, 8, 23), (64, 11, 52), (128, 15, 112)] {
        let sign = 1u128 << (width - 1);
        let inf = ((1u128 << exp_bits) - 1) << fraction_bits;
        for (value, expected) in [
            (0, [true, false, false, false]),
            (sign, [true, false, false, false]),
            (inf, [false, true, false, false]),
            (inf | 1, [false, false, true, false]),
            (1, [false, false, false, true]),
        ] {
            let bits = B129::get_slice_int(width, value as i128, 0);
            let ieee = solver.define_bitvector(crate::primop_util::smt_sbits(bits), info());
            let fp = unary[&format!("fp{width}_from_ieee")](Val::Symbolic(ieee), &mut solver, info()).unwrap();
            for (operation, expected) in
                ["fp_is_zero", "fp_is_infinite", "fp_is_nan", "fp_is_subnormal"].into_iter().zip(expected)
            {
                let result = unary[operation](fp.clone(), &mut solver, info()).unwrap();
                assert!(solver.check_sat(info()).is_sat().unwrap());
                assert_eq!(Model::new(&solver).get_val(&result).unwrap(), Val::Bool(expected));
            }
        }
        let one = ((1u128 << (exp_bits - 1)) - 1) << fraction_bits;
        let ieee =
            solver.define_bitvector(crate::primop_util::smt_sbits(B129::get_slice_int(width, one as i128, 0)), info());
        let fp = unary[&format!("fp{width}_from_ieee")](Val::Symbolic(ieee), &mut solver, info()).unwrap();
        for signed in ["signed"] {
            for result_width in [16, 32, 64, 128] {
                let rounding = unary["round_toward_zero"](Val::Unit, &mut solver, info()).unwrap();
                let result =
                    binary[&format!("fp_to_{signed}{result_width}")](rounding, fp.clone(), &mut solver, info())
                        .unwrap();
                let Val::Symbolic(sym) = result else { panic!("应返回符号位向量") };
                assert_eq!(solver.length(sym), Some(result_width));
                assert!(solver.is_sail_bitvector(sym));
                let mut replay = Solver::from_checkpoint(&ctx, checkpoint(&mut solver));
                assert!(replay.is_sail_bitvector(sym));
                assert!(replay.check_sat(info()).is_sat().unwrap());
                assert_eq!(Model::new(&replay).get_val(&result).unwrap(), Val::Bits(B129::new(1, result_width)));
            }
        }
    }
}

#[test]
fn review35_named_tlb_register_must_keep_read_dependency() {
    let mut observations = Vec::new();
    for enabled in [false, true] {
        let mut shared = empty_shared_state();
        let encoded = crate::zencode::encode("core_TLB");
        let reg = shared.symtab.intern(&encoded);
        let cond = test_name(867);
        let mut frame = make_frame(vec![
            Instr::Decl(cond, Ty::Bool, info()),
            Instr::Jump(Exp::Id(cond), 4, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
            Instr::Goto(5),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
            Instr::End,
        ]);
        frame.regs_mut().insert(reg, false, UVal::Uninit(&Ty::Bits(8)));
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
        let out = Mutex::new(Vec::new());
        start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, solver, out| {
            let Ok((Run::Finished(value), _)) = result else { panic!("应完成读取") };
            let events: Vec<_> = solver.trace().to_vec().into_iter().cloned().collect();
            let references = crate::simplify::EventReferences::from_events(&events);
            out.lock().unwrap().push(references.value_taints(&value, &events).registers.contains(&(reg, Vec::new())));
        });
        observations.push((enabled, out.into_inner().unwrap()));
    }
    assert!(
        observations.iter().all(|(_, paths)| !paths.is_empty() && paths.iter().all(|taint| *taint)),
        "非整个_TLB的寄存器读依赖丢失：{observations:?}"
    );
}

#[test]
fn review35_diamond_depth_and_workers_differential() {
    use std::collections::BTreeSet;
    for balanced in [false, true] {
        for max_depth in 0..8 {
            let mut observations = Vec::new();
            for workers in [0, 1, 4] {
                for enabled in [false, true] {
                    let c = test_name(868);
                    let instrs = vec![
                        Instr::Decl(c, Ty::Bool, info()),
                        Instr::Jump(Exp::Id(c), 5, info()),
                        if balanced {
                            Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(0, 8)), info())
                        } else {
                            Instr::Goto(3)
                        },
                        Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(1, 8)), info()),
                        Instr::Goto(7),
                        Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(2, 8)), info()),
                        Instr::Goto(7),
                        Instr::Goto(8),
                        Instr::End,
                    ];
                    let frame = make_frame(instrs);
                    let state = TaskState::new().with_execution_limits(
                        ExecutionLimits::default().with_path_merging(enabled).with_max_path_depth(max_depth),
                    );
                    let out = Arc::new(Mutex::new(BTreeSet::new()));
                    let task = frame.task(TaskId::fresh(), &state);
                    drop(frame);
                    start_multi(
                        workers,
                        Some(5),
                        vec![task],
                        &empty_shared_state(),
                        out.clone(),
                        &|_, _, result, _, mut solver, out| {
                            let (kind, frame) = match result {
                                Ok((Run::Finished(_), frame)) => (0, frame),
                                Err((ExecError::DepthLimitReached, frame)) => (1, frame),
                                _ => panic!("应完成或达到深度限制"),
                            };
                            let Some(UVal::Init(value)) = frame.vars().get(&c) else { panic!("条件必须初始化") };
                            for direction in [false, true] {
                                let condition = smtlib::Exp::Eq(
                                    Box::new(smt_value(value, info()).unwrap()),
                                    Box::new(smtlib::Exp::Bool(direction)),
                                );
                                if solver.check_sat_with(&condition, info()).is_sat().unwrap() {
                                    out.lock().unwrap().insert((direction, kind));
                                }
                            }
                        },
                    );
                    observations.push(out.lock().unwrap().clone());
                }
            }
            assert!(observations.iter().all(|set| set == &observations[0]), "深度={max_depth}：{observations:?}");
        }
    }
}
