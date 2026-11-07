use isla::isarch::memory_model::install_seq_memory;
use isla_lib::bitvector::{b129::B129, b64::B64, BV};
use isla_lib::error::ExecError;
use isla_lib::ir::Val;
use isla_lib::memory::{CustomRegion, Memory, Region};
use isla_lib::primop_util::smt_value;
use isla_lib::smt::smtlib::{bits64, Exp};
use isla_lib::smt::{Config, Context, Event, ReadOpts, Solver, WriteOpts};
use isla_lib::source_loc::SourceLoc;
use std::sync::Arc;

#[derive(Clone)]
struct Device(u8);

impl CustomRegion<B64> for Device {
    fn read(&self, _: Val<B64>, _: u64, _: u32, _: &mut Solver<B64>, _: bool) -> Result<Val<B64>, ExecError> {
        Ok(Val::Bits(B64::new(u64::from(self.0), 8)))
    }

    fn write(
        &mut self,
        _: Val<B64>,
        _: u64,
        data: Val<B64>,
        _: &mut Solver<B64>,
        _: Option<Val<B64>>,
    ) -> Result<Val<B64>, ExecError> {
        let Val::Bits(data) = data else { panic!("测试设备要求具体字节") };
        self.0 = data.lower_u8();
        Ok(Val::Bool(true))
    }

    fn initial_value(&self, _: u64, _: u32) -> Option<B64> {
        Some(B64::new(u64::from(self.0), 8))
    }

    fn region_name(&self) -> &'static str {
        "device"
    }

    fn clone_dyn(&self) -> Box<dyn Send + Sync + CustomRegion<B64>> {
        Box::new(self.clone())
    }
}

#[test]
fn 设备符号唯一地址执行副作用而混合地址先拆分() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let mut memory = Memory::new();
    memory.add_region(Region::Custom(0x1000..0x1002, Box::new(Device(0))));
    memory.add_zero_region(0x2000..0x2002);
    install_seq_memory(&mut memory, 64, &mut solver);
    let address = solver.declare_bitvector(129, info);
    let low = Exp::Extract(63, 0, Box::new(Exp::Var(address)));
    solver.assert(Exp::Or(
        Box::new(Exp::Eq(Box::new(low.clone()), Box::new(bits64(0x1000, 64)))),
        Box::new(Exp::Eq(Box::new(low.clone()), Box::new(bits64(0x2000, 64)))),
    ));
    let data = Val::Bits(B64::new(0xa5, 8));
    assert!(matches!(
        memory.write(Val::Unit, Val::Symbolic(address), data.clone(), &mut solver, None, WriteOpts::default()),
        Err(ExecError::SymbolicLength("write_mem_address", _))
    ));
    assert!(solver
        .check_sat_with(&Exp::Eq(Box::new(low.clone()), Box::new(bits64(0x2000, 64))), info)
        .is_sat()
        .unwrap());
    assert!(
        !solver.trace().to_vec().iter().any(|event| matches!(event, Event::WriteMem { .. })),
        "拆分前不得提交数组写事件"
    );
    assert_eq!(memory.in_custom_region(0x1000).unwrap().initial_value(0x1000, 1), Some(B64::zeros(8)));
    solver.assert_eq(low, bits64(0x1000, 64));
    memory.write(Val::Unit, Val::Symbolic(address), data.clone(), &mut solver, None, WriteOpts::default()).unwrap();
    assert_eq!(
        memory.read(Val::Unit, Val::Symbolic(address), Val::I128(1), &mut solver, false, ReadOpts::default()).unwrap(),
        data
    );
    assert!(solver.check_sat(info).is_sat().unwrap());
}

#[test]
fn 多字节生成器保持整区域读取约束和原始地址() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let mut memory = Memory::new();
    memory.add_region(Region::Constrained(
        0x1000..0x1002,
        Arc::new(move |solver| solver.define_bitvector(bits64(0xa542, 16), info)),
    ));
    install_seq_memory(&mut memory, 64, &mut solver);
    let address = solver.declare_bitvector(129, info);
    solver.assert_eq(Exp::Extract(63, 0, Box::new(Exp::Var(address))), bits64(0x1000, 64));
    let value =
        memory.read(Val::Unit, Val::Symbolic(address), Val::I128(2), &mut solver, false, ReadOpts::default()).unwrap();
    assert!(solver.check_sat(info).is_sat().unwrap());
    assert!(solver
        .check_sat_with(&Exp::Neq(Box::new(smt_value(&value, info).unwrap()), Box::new(bits64(0xa542, 16))), info)
        .is_unsat()
        .unwrap());
    assert!(
        matches!(solver.trace().to_vec().iter().find(|event| matches!(event, Event::ReadMem { .. })), Some(Event::ReadMem {address: Val::Symbolic(a), bytes: 2, region: "constrained", ..}) if *a == address)
    );
    assert!(
        matches!(
            memory.read(Val::Unit, Val::Symbolic(address), Val::I128(1), &mut solver, false, ReadOpts::default()),
            Err(ExecError::BadRead(_))
        ),
        "符号读取必须与具体读取保持相同的整区域契约"
    );
}

#[test]
fn 整数切片全宽度逐位核对符号扩展() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    for width in 0..=129 {
        for from in [0, 1, 63, 64, 127] {
            for integer in [i128::MIN, i128::MAX, -1, 0, 1] {
                let actual = B129::get_slice_int(width, integer, from).to_vec();
                let expected: Vec<_> = (0..width)
                    .map(|i| {
                        let bit = i + from;
                        if bit < 128 {
                            ((integer as u128) >> bit) & 1 != 0
                        } else {
                            integer < 0
                        }
                    })
                    .collect();
                assert_eq!(actual, expected, "width={width} from={from} int={integer}");
            }
        }
    }
}

#[test]
fn 窄位向量减去整数极值按模截断() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    for width in 0..=64 {
        let mask = if width == 0 { 0 } else { u64::MAX >> (64 - width) };
        for integer in [i128::MIN, i128::MAX, i128::from(i64::MIN), i128::from(i64::MAX), -1, 0, 1] {
            let input = B64::new(0x8123_4567_89ab_cdef & mask, width);
            let expected = (u128::from(input.lower_u64()).wrapping_sub(integer as u128) & u128::from(mask)) as u64;
            assert_eq!(input.sub_i128(integer), B64::new(expected, width));
        }
    }
}

#[test]
fn 回绕排除约束保留合法候选并独立验证读写() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    for (address_width, index_width) in [(32, 32), (64, 32), (65, 32), (64, 64), (129, 64)] {
        let maximum = if index_width == 64 { u64::MAX } else { u64::from(u32::MAX) };
        for write in [false, true] {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let mut memory = Memory::new();
            memory.add_excluded_region(0..1);
            install_seq_memory(&mut memory, index_width, &mut solver);
            let address = solver.declare_bitvector(address_width, info);
            solver.assert(Exp::Or(
                Box::new(Exp::Eq(Box::new(Exp::Var(address)), Box::new(bits64(maximum, address_width)))),
                Box::new(Exp::Eq(Box::new(Exp::Var(address)), Box::new(bits64(0x100, address_width)))),
            ));
            if write {
                memory
                    .write(
                        Val::Unit,
                        Val::Symbolic(address),
                        Val::Bits(B64::new(0xa542, 16)),
                        &mut solver,
                        None,
                        WriteOpts::default(),
                    )
                    .unwrap();
            } else {
                memory
                    .read(Val::Unit, Val::Symbolic(address), Val::I128(2), &mut solver, false, ReadOpts::default())
                    .unwrap();
            }
            assert!(solver.check_sat(info).is_sat().unwrap());
            assert!(solver
                .check_sat_with(&Exp::Eq(Box::new(Exp::Var(address)), Box::new(bits64(maximum, address_width))), info)
                .is_unsat()
                .unwrap());
            assert!(solver
                .check_sat_with(&Exp::Eq(Box::new(Exp::Var(address)), Box::new(bits64(0x100, address_width))), info)
                .is_sat()
                .unwrap());
        }
    }
}

#[test]
fn 具体区域遮蔽生成器时符号读取仍保留数组更新() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let mut memory = Memory::new();
    memory.add_zero_region(0x1000..0x1002);
    memory.add_region(Region::Constrained(
        0x1000..0x1001,
        Arc::new(move |solver| solver.define_bitvector(bits64(0x42, 8), info)),
    ));
    install_seq_memory(&mut memory, 64, &mut solver);
    let address = solver.define_bitvector(bits64(0x1000, 64), info);
    memory
        .write(Val::Unit, Val::Symbolic(address), Val::Bits(B64::new(0xa5, 8)), &mut solver, None, WriteOpts::default())
        .unwrap();
    let value =
        memory.read(Val::Unit, Val::Symbolic(address), Val::I128(1), &mut solver, false, ReadOpts::default()).unwrap();
    assert!(solver.check_sat(info).is_sat().unwrap());
    assert!(solver
        .check_sat_with(&Exp::Neq(Box::new(smt_value(&value, info).unwrap()), Box::new(bits64(0xa5, 8))), info)
        .is_unsat()
        .unwrap());
}
