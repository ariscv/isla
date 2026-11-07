use isla::isarch::memory_model::install_seq_memory;
use isla_lib::bitvector::{b129::B129, b64::B64, BV};
use isla_lib::executor::LocalFrame;
use isla_lib::ir::{Instr, Name, Ty, Val};
use isla_lib::memory::{Memory, Region};
use isla_lib::primop;
use isla_lib::primop_util::{smt_i128, smt_value};
use isla_lib::smt::{
    smtlib::{self, Exp},
    Config, Context, ReadOpts, Solver,
};
use isla_lib::source_loc::SourceLoc;
use std::sync::Arc;
fn info() -> SourceLoc {
    SourceLoc::unknown()
}

#[test]
fn review36_get_slice_int_concrete_129_must_match_symbolic() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B129>::new(&ctx);
    let instrs = [Instr::End];
    let mut frame = LocalFrame::new(Name::from_u32(100), &[], &Ty::Unit, None, &instrs);
    let f = primop::variadic_primops()["get_slice_int"];
    let number = solver.define_const(smt_i128(-1), info());
    let symbolic =
        f(vec![Val::I128(129), Val::Symbolic(number), Val::I128(0)], &mut solver, &mut frame, info()).unwrap();
    assert!(solver.check_sat(info()).is_sat().unwrap());
    assert!(solver
        .check_sat_with(
            &Exp::Neq(Box::new(smt_value(&symbolic, info()).unwrap()), Box::new(primop::smt_ones(129))),
            info()
        )
        .is_unsat()
        .unwrap());
    let concrete = f(vec![Val::I128(129), Val::I128(-1), Val::I128(0)], &mut solver, &mut frame, info()).unwrap();
    assert_eq!(concrete, Val::Bits(B129::ones(129)));
}

#[test]
fn review36_seq_constrained_region_must_match_concrete_address() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let mut memory = Memory::<B64>::new();
    memory.add_region(Region::Constrained(
        0x1000..0x1001,
        Arc::new(|s| s.define_bitvector(smtlib::bits64(0x42, 8), info())),
    ));
    install_seq_memory(&mut memory, 64, &mut solver);
    let concrete = memory
        .read(Val::Unit, Val::Bits(B64::new(0x1000, 64)), Val::I128(1), &mut solver, false, ReadOpts::default())
        .unwrap();
    let address = solver.declare_bitvector(64, info());
    solver.assert_eq(Exp::Var(address), smtlib::bits64(0x1000, 64));
    let symbolic =
        memory.read(Val::Unit, Val::Symbolic(address), Val::I128(1), &mut solver, false, ReadOpts::default()).unwrap();
    assert!(solver.check_sat(info()).is_sat().unwrap());
    assert!(
        solver
            .check_sat_with(
                &Exp::Neq(
                    Box::new(smt_value(&concrete, info()).unwrap()),
                    Box::new(smt_value(&symbolic, info()).unwrap())
                ),
                info()
            )
            .is_unsat()
            .unwrap(),
        "同一Constrained区域的具体读为0x42，符号读却允许不同值"
    );
}

#[test]
fn review36_b64_subtract_min_must_match_symbolic() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let f = primop::binary_primops()["sub_bits_int"];
    let bits = B64::new(1, 64);
    let symbol = solver.define_bitvector(smtlib::bits64(1, 64), info());
    let symbolic = f(Val::Symbolic(symbol), Val::I128(i128::MIN), &mut solver, info()).unwrap();
    assert!(solver.check_sat(info()).is_sat().unwrap());
    assert!(solver
        .check_sat_with(
            &Exp::Neq(Box::new(smt_value(&symbolic, info()).unwrap()), Box::new(smtlib::bits64(1, 64))),
            info()
        )
        .is_unsat()
        .unwrap());
    let concrete = f(Val::Bits(bits), Val::I128(i128::MIN), &mut solver, info()).unwrap();
    assert_eq!(concrete, Val::Bits(bits));
}

#[test]
fn review36_seq_wrapped_access_must_not_touch_excluded_byte() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    use isla_lib::error::ExecError;
    use isla_lib::smt::WriteOpts;
    let mut observations = Vec::new();
    for symbolic in [false, true] {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        install_seq_memory(&mut memory, 64, &mut solver);
        let address = if symbolic {
            Val::Symbolic(solver.define_bitvector(smtlib::bits64(u64::MAX, 64), info()))
        } else {
            Val::Bits(B64::new(u64::MAX, 64))
        };
        // 对照：数组的逐字节地址确实在 64 位处回绕，第二字节写到地址 0。
        memory
            .write(Val::Unit, address.clone(), Val::Bits(B64::new(0xa542, 16)), &mut solver, None, WriteOpts::default())
            .unwrap();
        let at_zero = memory
            .read(Val::Unit, Val::Bits(B64::zeros(64)), Val::I128(1), &mut solver, false, ReadOpts::default())
            .unwrap();
        assert!(solver.check_sat(info()).is_sat().unwrap());
        assert!(solver
            .check_sat_with(
                &Exp::Neq(Box::new(smt_value(&at_zero, info()).unwrap()), Box::new(smtlib::bits64(0xa5, 8))),
                info(),
            )
            .is_unsat()
            .unwrap());
        // 独立的内存和求解器从一开始就排除字节 0；同样的读写必须被拒绝。
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        memory.add_excluded_region(0..1);
        install_seq_memory(&mut memory, 64, &mut solver);
        let address = if symbolic {
            Val::Symbolic(solver.define_bitvector(smtlib::bits64(u64::MAX, 64), info()))
        } else {
            Val::Bits(B64::new(u64::MAX, 64))
        };
        let write = memory.write(
            Val::Unit,
            address.clone(),
            Val::Bits(B64::new(0xa542, 16)),
            &mut solver,
            None,
            WriteOpts::default(),
        );
        let read = memory.read(Val::Unit, address, Val::I128(2), &mut solver, false, ReadOpts::default());
        observations.push((
            symbolic,
            matches!(write, Err(ExecError::BadWrite(_))),
            matches!(read, Err(ExecError::BadRead(_))),
        ));
    }
    assert!(
        observations.iter().all(|(_, rejected_write, rejected_read)| *rejected_write && *rejected_read),
        "跨64位边界的第二个Store/Select落入排除字节0：(符号地址,拒绝写,拒绝读)={observations:?}"
    );
}

#[test]
fn review36_seq_constrained_diamond_must_preserve_values() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    use isla_lib::executor::{start_single, ExecutionLimits, Run, TaskId, TaskState};
    use isla_lib::ir::{Exp as IRExp, IRTypeInfo, Loc, SharedState, Symtab, RETURN};
    use std::{collections::HashSet, sync::Mutex};
    let defs = &[];
    let mut symtab = Symtab::new();
    let cond = symtab.intern("zc36");
    let addr = symtab.intern("za36");
    let function = symtab.intern("zf36");
    let shared = SharedState::<B64>::new(
        symtab,
        defs,
        IRTypeInfo::new(defs),
        HashSet::new(),
        HashSet::new(),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    let instrs = vec![
        Instr::Decl(cond, Ty::Bool, info()),
        Instr::Decl(addr, Ty::Bits(64), info()),
        Instr::Jump(IRExp::Id(cond), 5, info()),
        Instr::Copy(Loc::Id(addr), IRExp::Bits(B64::new(0x1000, 64)), info()),
        Instr::Goto(6),
        Instr::Copy(Loc::Id(addr), IRExp::Bits(B64::new(0x1001, 64)), info()),
        Instr::PrimopVariadic(
            Loc::Id(RETURN),
            primop::variadic_primops()["read_mem"],
            vec![IRExp::Unit, IRExp::I128(64), IRExp::Id(addr), IRExp::I128(1)],
            info(),
        ),
        Instr::End,
    ];
    let mut observations = Vec::new();
    for enabled in [false, true] {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut frame = LocalFrame::new(function, &[], &Ty::Bits(8), None, &instrs);
        for (a, b) in [(0x1000, 0x11), (0x1001, 0x22)] {
            frame.memory_mut().add_region(Region::Constrained(
                a..a + 1,
                Arc::new(move |s| s.define_bitvector(smtlib::bits64(b, 8), info())),
            ));
        }
        install_seq_memory(frame.memory_mut(), 64, &mut solver);
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
        let out = Mutex::new((0, 0, false));
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, isla_lib::smt::checkpoint(&mut solver)),
            &shared,
            &out,
            &|_, _, result, _, mut solver, out| {
                let Ok((Run::Finished(value), _)) = result else { panic!("区域读取必须完成") };
                let mut obs = out.lock().unwrap();
                obs.0 += 1;
                obs.1 +=
                    solver.trace().to_vec().iter().filter(|e| matches!(e, isla_lib::smt::Event::Merge(..))).count();
                let allowed = Exp::Or(
                    Box::new(Exp::Eq(Box::new(smt_value(&value, info()).unwrap()), Box::new(smtlib::bits64(0x11, 8)))),
                    Box::new(Exp::Eq(Box::new(smt_value(&value, info()).unwrap()), Box::new(smtlib::bits64(0x22, 8)))),
                );
                obs.2 |= solver.check_sat_with(&Exp::Not(Box::new(allowed)), info()).is_sat().unwrap();
            },
        );
        observations.push((enabled, out.into_inner().unwrap()));
    }
    eprintln!("合流开关、完成数、合流数、可读出非法值：{observations:?}");
    assert_eq!(observations[0].1, (2, 0, false));
    assert!(observations[1].1 .1 > 0);
    assert!(!observations[1].1 .2, "合流不能将0x11/0x22区域读变成任意字节：{observations:?}");
}

#[test]
fn review36_b129_ripple_oracle_all_widths() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    fn ripple(a: &[bool], n: i128, subtract: bool) -> Vec<bool> {
        let mut carry = subtract;
        a.iter()
            .enumerate()
            .map(|(i, &a)| {
                let nbit = if i < 128 { (n as u128 >> i) & 1 != 0 } else { n < 0 };
                let b = if subtract { !nbit } else { nbit };
                let result = a ^ b ^ carry;
                carry = (a && b) || (a && carry) || (b && carry);
                result
            })
            .collect()
    }
    let mut seed = 0xe2f5_b106_773a_98d3u64;
    for width in 0..=129 {
        for iteration in 0..32 {
            let mut input = Vec::new();
            let mut bits = B129::zeros(width);
            for i in 0..width {
                seed ^= seed << 13;
                seed ^= seed >> 7;
                seed ^= seed << 17;
                let b = seed & 1 != 0;
                input.push(b);
                if b {
                    bits = bits.set_slice(i, B129::BIT_ONE);
                }
            }
            let n = match iteration % 4 {
                0 => i128::MIN,
                1 => i128::MAX,
                2 => 0,
                _ => ((seed as u128) << 64 | (!seed) as u128) as i128,
            };
            assert_eq!(bits.add_i128(n).to_vec(), ripple(&input, n, false), "加法 width={width} n={n}");
            assert_eq!(bits.sub_i128(n).to_vec(), ripple(&input, n, true), "减法 width={width} n={n}");
            assert_eq!(bits.trailing_zeros() as usize, input.iter().position(|b| *b).unwrap_or(width as usize));
        }
    }
}

#[test]
fn review36_signed_fp_conversion_markers_all_widths() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    use isla_lib::smt::{checkpoint, Model};
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B129>::new(&ctx);
    let unary = primop::unary_primops::<B129>();
    let binary = primop::binary_primops::<B129>();
    for source in [16, 32, 64, 128] {
        let fp = unary[&format!("fp{source}_zero")](Val::Unit, &mut solver, info()).unwrap();
        for width in [16, 32, 64, 128] {
            let rm = unary["round_toward_zero"](Val::Unit, &mut solver, info()).unwrap();
            let value = binary[&format!("fp_to_signed{width}")](rm, fp.clone(), &mut solver, info()).unwrap();
            let Val::Symbolic(sym) = value else { panic!("转换必须返回符号位向量") };
            assert_eq!(solver.length(sym), Some(width));
            assert!(solver.is_sail_bitvector(sym));
            let mut replay = Solver::from_checkpoint(&ctx, checkpoint(&mut solver));
            assert!(replay.is_sail_bitvector(sym));
            assert!(replay.check_sat(info()).is_sat().unwrap());
            assert_eq!(Model::new(&replay).get_val(&value).unwrap(), Val::Bits(B129::zeros(width)));
        }
    }
}

#[derive(Clone)]
struct Review36Device {
    value: u8,
}
impl isla_lib::memory::CustomRegion<B64> for Review36Device {
    fn read(
        &self,
        kind: Val<B64>,
        address: u64,
        bytes: u32,
        solver: &mut Solver<B64>,
        tag: bool,
    ) -> Result<Val<B64>, isla_lib::error::ExecError> {
        let _ = (kind, address, bytes, solver, tag);
        Ok(Val::Bits(B64::new(u64::from(self.value), 8)))
    }
    fn write(
        &mut self,
        kind: Val<B64>,
        address: u64,
        data: Val<B64>,
        solver: &mut Solver<B64>,
        tag: Option<Val<B64>>,
    ) -> Result<Val<B64>, isla_lib::error::ExecError> {
        let _ = (kind, address, solver, tag);
        let Val::Bits(data) = data else { panic!("设备测试只写具体字节") };
        self.value = data.lower_u8();
        Ok(Val::Bool(true))
    }
    fn initial_value(&self, address: u64, bytes: u32) -> Option<B64> {
        let _ = (address, bytes);
        Some(B64::new(u64::from(self.value), 8))
    }
    fn region_name(&self) -> &'static str {
        "review36_device"
    }
    fn clone_dyn(&self) -> Box<dyn Send + Sync + isla_lib::memory::CustomRegion<B64>> {
        Box::new(self.clone())
    }
}

#[test]
fn review36_seq_custom_diamond_write_must_reach_device() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    use isla_lib::executor::{start_single, ExecutionLimits, Run, TaskId, TaskState};
    use isla_lib::ir::{Exp as IRExp, IRTypeInfo, Loc, SharedState, Symtab, RETURN};
    use std::{collections::HashSet, sync::Mutex};
    let defs = &[];
    let mut symtab = Symtab::new();
    let cond = symtab.intern("zc36");
    let addr = symtab.intern("za36");
    let temp = symtab.intern("zt36");
    let function = symtab.intern("zf36");
    let shared = SharedState::<B64>::new(
        symtab,
        defs,
        IRTypeInfo::new(defs),
        HashSet::new(),
        HashSet::new(),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    let instrs = vec![
        Instr::Decl(cond, Ty::Bool, info()),
        Instr::Decl(addr, Ty::Bits(64), info()),
        Instr::Decl(temp, Ty::Bool, info()),
        Instr::Jump(IRExp::Id(cond), 6, info()),
        Instr::Copy(Loc::Id(addr), IRExp::Bits(B64::new(0x1000, 64)), info()),
        Instr::Goto(7),
        Instr::Copy(Loc::Id(addr), IRExp::Bits(B64::new(0x1001, 64)), info()),
        Instr::PrimopVariadic(
            Loc::Id(temp),
            primop::variadic_primops()["platform_write_mem"],
            vec![IRExp::Unit, IRExp::I128(64), IRExp::Id(addr), IRExp::I128(1), IRExp::Bits(B64::new(0xa5, 8))],
            info(),
        ),
        Instr::PrimopVariadic(
            Loc::Id(RETURN),
            primop::variadic_primops()["platform_read_mem"],
            vec![IRExp::Unit, IRExp::I128(64), IRExp::Bits(B64::new(0x1000, 64)), IRExp::I128(1)],
            info(),
        ),
        Instr::End,
    ];
    let mut observations = Vec::new();
    for enabled in [false, true] {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut frame = LocalFrame::new(function, &[], &Ty::Bits(8), None, &instrs);
        frame.memory_mut().add_region(Region::Custom(0x1000..0x1002, Box::new(Review36Device { value: 0 })));
        install_seq_memory(frame.memory_mut(), 64, &mut solver);
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
        let out = Mutex::new(Vec::new());
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, isla_lib::smt::checkpoint(&mut solver)),
            &shared,
            &out,
            &|_, _, result, _, _, out| {
                let Ok((Run::Finished(Val::Bits(value)), _)) = result else { panic!("设备读取必须完成") };
                out.lock().unwrap().push(value.lower_u8());
            },
        );
        observations.push((enabled, out.into_inner().unwrap()));
    }
    eprintln!("合流开关、设备写后读：{observations:?}");
    assert!(
        observations.iter().all(|(_, values)| !values.is_empty() && values.iter().all(|v| *v == 0xa5)),
        "合流丢失设备写副作用：{observations:?}"
    );
}
