use isla::isarch::memory_model::install_seq_memory;
use isla_lib::bitvector::{b129::B129, b64::B64, BV};
use isla_lib::executor::LocalFrame;
use isla_lib::ir::{Instr, Name, Ty, Val};
use isla_lib::memory::{Memory, Region};
use isla_lib::primop;
use isla_lib::primop_util::{smt_i128, smt_sbits, smt_value};
use isla_lib::smt::{
    smtlib::{bits64, Exp},
    Config, Context, ReadOpts, Solver, WriteOpts,
};
use isla_lib::source_loc::SourceLoc;
use std::sync::Arc;
fn info() -> SourceLoc {
    SourceLoc::unknown()
}
#[test]
fn review37_constrained_write_read_coherence() {
    let mut mismatches = vec![];
    for sw in [false, true] {
        for sr in [false, true] {
            let ctx = Context::new(Config::new());
            let mut s = Solver::<B64>::new(&ctx);
            let mut m = Memory::new();
            m.add_region(Region::Constrained(
                0x1000..0x1001,
                Arc::new(|s| s.define_bitvector(bits64(0x42, 8), info())),
            ));
            install_seq_memory(&mut m, 64, &mut s);
            let a = s.define_bitvector(bits64(0x1000, 64), info());
            let addr = |sym| {
                if sym {
                    Val::Symbolic(a)
                } else {
                    Val::Bits(B64::new(0x1000, 64))
                }
            };
            m.write(Val::Unit, addr(sw), Val::Bits(B64::new(0xa5, 8)), &mut s, None, WriteOpts::default()).unwrap();
            let v = m.read(Val::Unit, addr(sr), Val::I128(1), &mut s, false, ReadOpts::default()).unwrap();
            assert!(s.check_sat(info()).is_sat().unwrap());
            let wrong = s
                .check_sat_with(&Exp::Neq(Box::new(smt_value(&v, info()).unwrap()), Box::new(bits64(0xa5, 8))), info())
                .is_sat()
                .unwrap();
            if wrong {
                mismatches.push((sw, sr));
            }
        }
    }
    assert!(mismatches.is_empty(), "写入0xa5后仍可读出0x42：(符号写,符号读)={mismatches:?}");
}
#[test]
fn review37_abs_min_differential() {
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B129>::new(&ctx);
    let f = primop::unary_primops()["abs_int"];
    let n = s.define_const(smt_i128(i128::MIN), info());
    let sym = f(Val::Symbolic(n), &mut s, info()).unwrap();
    assert!(s
        .check_sat_with(&Exp::Neq(Box::new(smt_value(&sym, info()).unwrap()), Box::new(smt_i128(i128::MIN))), info())
        .is_unsat()
        .unwrap());
    let concrete = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(Val::I128(i128::MIN), &mut s, info())));
    assert!(concrete.is_ok(), "符号MIN绝对值可执行，具体MIN却使宿主进程panic");
}
#[test]
fn review37_b129_arithmetic_differential() {
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B129>::new(&ctx);
    for width in [0, 1, 7, 63, 64, 65, 127, 128, 129] {
        for x in [B129::zeros(width), B129::ones(width), B129::new(1, width.max(1)).slice(0, width).unwrap()] {
            for n in [i128::MIN, i128::MAX, -1, 0, 1] {
                for (op, expected) in [("add_bits_int", x.add_i128(n)), ("sub_bits_int", x.sub_i128(n))] {
                    let result = primop::binary_primops()[op](
                        Val::Bits(x),
                        Val::Symbolic(s.define_const(smt_i128(n), info())),
                        &mut s,
                        info(),
                    )
                    .unwrap();
                    if width == 0 {
                        assert_eq!(result, Val::Bits(expected));
                        continue;
                    }
                    assert!(
                        s.check_sat_with(
                            &Exp::Neq(Box::new(smt_value(&result, info()).unwrap()), Box::new(smt_sbits(expected))),
                            info()
                        )
                        .is_unsat()
                        .unwrap(),
                        "{op} width={width} n={n}"
                    );
                }
            }
        }
    }
}
#[test]
fn review37_set_slice_integer_empty_boundary() {
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B129>::new(&ctx);
    let instrs = [Instr::End];
    let mut frame = LocalFrame::new(Name::from_u32(100), &[], &Ty::Unit, None, &instrs);
    let f = primop::variadic_primops()["set_slice_int"];
    for n in [0, 127, 128] {
        let result =
            f(vec![Val::I128(0), Val::I128(-1), Val::I128(n), Val::Bits(B129::zeros(0))], &mut s, &mut frame, info())
                .unwrap();
        assert_eq!(result, Val::I128(-1));
    }
}
#[test]
fn review37_shadowed_generator_does_not_block_array_reads() {
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let mut m = Memory::new();
    m.add_zero_region(0x1000..0x1002);
    m.add_region(Region::Constrained(0x1000..0x1002, Arc::new(|s| s.define_bitvector(bits64(0x4242, 16), info()))));
    install_seq_memory(&mut m, 64, &mut s);
    let a = s.declare_bitvector(64, info());
    s.assert(Exp::Or(
        Box::new(Exp::Eq(Box::new(Exp::Var(a)), Box::new(bits64(0x1000, 64)))),
        Box::new(Exp::Eq(Box::new(Exp::Var(a)), Box::new(bits64(0x1001, 64)))),
    ));
    let result = m.read(Val::Unit, Val::Symbolic(a), Val::I128(1), &mut s, false, ReadOpts::default());
    assert!(result.is_ok(), "两个地址均由前面的零区域处理，后面的生成器不得阻塞读取：{result:?}");
    let v = result.unwrap();
    assert!(s
        .check_sat_with(&Exp::Neq(Box::new(smt_value(&v, info()).unwrap()), Box::new(bits64(0, 8))), info())
        .is_unsat()
        .unwrap());
}
#[test]
fn review37_fp_from_integer_preserves_target_format() {
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B129>::new(&ctx);
    let u = primop::unary_primops();
    let b = primop::binary_primops();
    let mut wrong = vec![];
    for width in [16, 32, 64, 128] {
        for signed in [false, true] {
            let rm = u["round_toward_zero"](Val::Unit, &mut s, info()).unwrap();
            let n = Val::Symbolic(s.define_bitvector(bits64(2049, 16), info()));
            let key = format!("fp{width}_from_{}", if signed { "signed" } else { "unsigned" });
            let out = b[&key](rm.clone(), n, &mut s, info()).unwrap();
            let roundtrip = b["fp_to_signed64"](rm, out, &mut s, info()).unwrap();
            let expected = if width == 16 { 2048 } else { 2049 };
            assert!(s.check_sat(info()).is_sat().unwrap());
            if !s
                .check_sat_with(
                    &Exp::Neq(Box::new(smt_value(&roundtrip, info()).unwrap()), Box::new(bits64(expected, 64))),
                    info(),
                )
                .is_unsat()
                .unwrap()
            {
                wrong.push(key);
            }
        }
    }
    assert!(wrong.is_empty(), "2049可由fp32/64/128精确表示，实际却按fp16截断成2048：{wrong:?}");
}
#[test]
fn review37_shadowed_generator_end_to_end_preserves_paths() {
    use isla_lib::executor::{start_multi, ExecutionLimits, Run, TaskId, TaskState};
    use isla_lib::ir::{Exp as IrExp, Loc, SharedState, Symtab, UVal, RETURN};
    use isla_lib::smt::checkpoint;
    use std::sync::Mutex;
    let mut observations = vec![];
    for workers in [0, 1, 4] {
        for merge in [false, true] {
            let mut symtab = Symtab::new();
            let function = symtab.intern("zreview37");
            let addr = symtab.intern("zaddress");
            let shared = SharedState::<B64>::empty(symtab);
            let instrs = vec![
                Instr::PrimopVariadic(
                    Loc::Id(RETURN),
                    primop::variadic_primops()["read_mem"],
                    vec![IrExp::Unit, IrExp::I128(64), IrExp::Id(addr), IrExp::I128(1)],
                    info(),
                ),
                Instr::End,
            ];
            let mut frame = LocalFrame::new(function, &[], &Ty::AnyBits, None, &instrs);
            let ctx = Context::new(Config::new());
            let mut s = Solver::<B64>::new(&ctx);
            let a = s.declare_bitvector(64, info());
            s.assert(Exp::Or(
                Box::new(Exp::Eq(Box::new(Exp::Var(a)), Box::new(bits64(0x1000, 64)))),
                Box::new(Exp::Eq(Box::new(Exp::Var(a)), Box::new(bits64(0x1001, 64)))),
            ));
            frame.vars_mut().insert(addr, UVal::Init(Val::Symbolic(a)));
            frame.memory_mut().add_zero_region(0x1000..0x1002);
            frame.memory_mut().add_region(Region::Constrained(
                0x1000..0x1002,
                Arc::new(|s| s.define_bitvector(bits64(0x4242, 16), info())),
            ));
            install_seq_memory(frame.memory_mut(), 64, &mut s);
            let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(merge));
            let out = Arc::new(Mutex::new((false, false, vec![])));
            let collector: &isla_lib::executor::Collector<'_, B64, Mutex<(bool, bool, Vec<String>)>> =
                Box::leak(Box::new(
                    move |_,
                          _,
                          result,
                          _: &SharedState<B64>,
                          mut solver: Solver<B64>,
                          out: &Mutex<(bool, bool, Vec<String>)>| {
                        let mut got = out.lock().unwrap();
                        match result {
                            Ok((Run::Finished(v), _)) => {
                                for (i, candidate) in [0x1000, 0x1001].into_iter().enumerate() {
                                    let reachable = solver
                                        .check_sat_with(
                                            &Exp::Eq(Box::new(Exp::Var(a)), Box::new(bits64(candidate, 64))),
                                            info(),
                                        )
                                        .is_sat()
                                        .unwrap();
                                    if i == 0 {
                                        got.0 |= reachable;
                                    } else {
                                        got.1 |= reachable;
                                    }
                                }
                                assert!(solver
                                    .check_sat_with(
                                        &Exp::Neq(Box::new(smt_value(&v, info()).unwrap()), Box::new(bits64(0, 8))),
                                        info()
                                    )
                                    .is_unsat()
                                    .unwrap());
                            }
                            Err((error, _)) => got.2.push(format!("{error:?}")),
                            _ => panic!("读取应完成或明确报告错误"),
                        }
                    },
                ));
            start_multi(
                workers,
                None,
                vec![frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut s))],
                &shared,
                out.clone(),
                collector,
            );
            observations.push((workers, merge, out.lock().unwrap().clone()));
        }
    }
    assert!(
        observations.iter().all(|(_, _, v)| v.0 && v.1 && v.2.is_empty()),
        "被遮蔽的生成器吞掉了零区域全部合法路径：{observations:?}"
    );
}
#[test]
fn review37_diamond_extremes_preserve_values_and_register_dependencies() {
    use isla_lib::executor::{start_single, ExecutionLimits, Run, TaskId, TaskState};
    use isla_lib::ir::{Exp as IrExp, Loc, SharedState, Symtab, UVal, RETURN};
    use isla_lib::smt::Event;
    use std::sync::Mutex;
    for width in [1, 8, 64, 128, 129] {
        for name in ["_TLB", "core_TLB", "_TLB_cache", "rdata"] {
            for merge in [false, true] {
                let mut symtab = Symtab::new();
                let function = symtab.intern("zreview37_diamond");
                let encoded = isla_lib::zencode::encode(name);
                let reg = symtab.intern(&encoded);
                let flag = symtab.intern("zflag");
                let shared = SharedState::<B129>::empty(symtab);
                let data_ty = Ty::Bits(width);
                let instrs = [
                    Instr::Jump(IrExp::Id(flag), 3, info()),
                    Instr::PrimopBinary(
                        Loc::Id(RETURN),
                        primop::binary_primops()["add_bits_int"],
                        IrExp::Id(reg),
                        IrExp::I128(-1),
                        info(),
                    ),
                    Instr::Goto(4),
                    Instr::PrimopBinary(
                        Loc::Id(RETURN),
                        primop::binary_primops()["sub_bits_int"],
                        IrExp::Id(reg),
                        IrExp::I128(i128::MIN),
                        info(),
                    ),
                    Instr::End,
                ];
                let mut frame = LocalFrame::new(function, &[], &Ty::AnyBits, None, &instrs);
                frame.regs_mut().insert(reg, false, UVal::Uninit(&data_ty));
                frame.regs_mut().insert(flag, false, UVal::Uninit(&Ty::Bool));
                let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(merge));
                let out = Mutex::new((0, 0));
                start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, mut s, out| {
                    let Ok((Run::Finished(v), f)) = result else { panic!("菱形必须完成") };
                    let data = smt_value(f.regs().get_last_if_initialized(reg).unwrap(), info()).unwrap();
                    let condition = smt_value(f.regs().get_last_if_initialized(flag).unwrap(), info()).unwrap();
                    let add = Exp::Bvadd(
                        Box::new(data.clone()),
                        Box::new(isla_lib::primop_util::smt_int_to_bits(smt_i128(-1), width)),
                    );
                    let sub = Exp::Bvsub(
                        Box::new(data),
                        Box::new(isla_lib::primop_util::smt_int_to_bits(smt_i128(i128::MIN), width)),
                    );
                    let expected = Exp::Ite(Box::new(condition), Box::new(sub), Box::new(add));
                    assert!(s.check_sat(info()).is_sat().unwrap());
                    assert!(s
                        .check_sat_with(&Exp::Neq(Box::new(smt_value(&v, info()).unwrap()), Box::new(expected)), info())
                        .is_unsat()
                        .unwrap());
                    let events: Vec<_> = s.trace().to_vec().into_iter().cloned().collect();
                    let reads = events.iter().filter(|e| matches!(e,Event::ReadReg(id,_,_) if *id==reg)).count();
                    assert_eq!(reads, usize::from(name != "_TLB"));
                    let refs = isla_lib::simplify::EventReferences::from_events(&events);
                    assert_eq!(refs.value_taints(&v, &events).registers.contains(&(reg, vec![])), name != "_TLB");
                    let mut got = out.lock().unwrap();
                    got.0 += 1;
                    got.1 += events.iter().filter(|e| matches!(e, Event::Merge(..))).count();
                });
                assert_eq!(*out.lock().unwrap(), if merge { (1, 1) } else { (2, 0) }, "width={width} register={name}");
            }
        }
    }
}
