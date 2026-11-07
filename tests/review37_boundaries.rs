use isla::isarch::memory_model::install_seq_memory;
use isla_lib::bitvector::{b64::B64, BV};
use isla_lib::error::ExecError;
use isla_lib::ir::Val;
use isla_lib::memory::{CustomRegion, Memory, Region};
use isla_lib::primop;
use isla_lib::primop_util::{smt_i128, smt_value};
use isla_lib::smt::smtlib::{bits64, Exp};
use isla_lib::smt::{Config, Context, Event, ReadOpts, Solver, WriteOpts};
use isla_lib::source_loc::SourceLoc;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

#[derive(Clone)]
struct UnreachableDevice;

impl CustomRegion<B64> for UnreachableDevice {
    fn read(&self, _: Val<B64>, _: u64, _: u32, _: &mut Solver<B64>, _: bool) -> Result<Val<B64>, ExecError> {
        panic!("遮蔽区域或拆分前不得调用设备读")
    }

    fn write(
        &mut self,
        _: Val<B64>,
        _: u64,
        _: Val<B64>,
        _: &mut Solver<B64>,
        _: Option<Val<B64>>,
    ) -> Result<Val<B64>, ExecError> {
        panic!("遮蔽区域或拆分前不得调用设备写")
    }

    fn initial_value(&self, _: u64, _: u32) -> Option<B64> {
        panic!("普通数组读取不得查询设备初值")
    }

    fn region_name(&self) -> &'static str {
        "unreachable device"
    }

    fn clone_dyn(&self) -> Box<dyn Send + Sync + CustomRegion<B64>> {
        Box::new(self.clone())
    }
}

#[test]
fn 设备可见范围决定是否拆分且完全遮蔽时保持读写一致性() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    for fully_shadowed in [false, true] {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::new();
        memory.add_zero_region(0x1000..if fully_shadowed { 0x1002 } else { 0x1001 });
        memory.add_region(Region::Custom(0x1000..0x1002, Box::new(UnreachableDevice)));
        install_seq_memory(&mut memory, 64, &mut solver);
        let address = solver.declare_bitvector(64, info);
        solver.assert(Exp::Or(
            Box::new(Exp::Eq(Box::new(Exp::Var(address)), Box::new(bits64(0x1000, 64)))),
            Box::new(Exp::Eq(Box::new(Exp::Var(address)), Box::new(bits64(0x1001, 64)))),
        ));
        let read =
            memory.read(Val::Unit, Val::Symbolic(address), Val::I128(1), &mut solver, false, ReadOpts::default());
        if !fully_shadowed {
            assert!(matches!(read, Err(ExecError::SymbolicLength("read_mem_address", _))));
            assert!(matches!(
                memory.write(
                    Val::Unit,
                    Val::Symbolic(address),
                    Val::Bits(B64::new(0xa5, 8)),
                    &mut solver,
                    None,
                    WriteOpts::default()
                ),
                Err(ExecError::SymbolicLength("write_mem_address", _))
            ));
            assert!(!solver
                .trace()
                .to_vec()
                .iter()
                .any(|e| matches!(e, Event::ReadMem { .. } | Event::WriteMem { .. })));
        } else {
            assert!(solver.check_sat(info).is_sat().unwrap());
            assert!(solver
                .check_sat_with(
                    &Exp::Neq(Box::new(smt_value(&read.unwrap(), info).unwrap()), Box::new(bits64(0, 8))),
                    info
                )
                .is_unsat()
                .unwrap());
            memory
                .write(
                    Val::Unit,
                    Val::Symbolic(address),
                    Val::Bits(B64::new(0xa5, 8)),
                    &mut solver,
                    None,
                    WriteOpts::default(),
                )
                .unwrap();
            let after = memory
                .read(Val::Unit, Val::Symbolic(address), Val::I128(1), &mut solver, false, ReadOpts::default())
                .unwrap();
            assert!(solver.check_sat(info).is_sat().unwrap());
            assert!(solver
                .check_sat_with(&Exp::Neq(Box::new(smt_value(&after, info).unwrap()), Box::new(bits64(0xa5, 8))), info)
                .is_unsat()
                .unwrap());
            // 具体地址写也必须采用相同的遮蔽优先级。
            memory
                .write(
                    Val::Unit,
                    Val::Bits(B64::new(0x1000, 64)),
                    Val::Bits(B64::new(0x7e, 8)),
                    &mut solver,
                    None,
                    WriteOpts::default(),
                )
                .unwrap();
            let after = memory
                .read(Val::Unit, Val::Bits(B64::new(0x1000, 64)), Val::I128(1), &mut solver, false, ReadOpts::default())
                .unwrap();
            assert!(solver.check_sat(info).is_sat().unwrap());
            assert!(solver
                .check_sat_with(&Exp::Neq(Box::new(smt_value(&after, info).unwrap()), Box::new(bits64(0x7e, 8))), info)
                .is_unsat()
                .unwrap());
        }
        for candidate in [0x1000, 0x1001] {
            assert!(solver
                .check_sat_with(&Exp::Eq(Box::new(Exp::Var(address)), Box::new(bits64(candidate, 64))), info)
                .is_sat()
                .unwrap());
        }
    }
}

#[test]
fn 遮蔽生成器不得执行或约束当前数组() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let mut memory = Memory::new();
    memory.add_zero_region(0x1000..0x1002);
    memory.add_region(Region::Constrained(0x1000..0x1002, Arc::new(|_| panic!("被遮蔽的生成器不得调用"))));
    install_seq_memory(&mut memory, 64, &mut solver);
    let value = memory
        .read(Val::Unit, Val::Bits(B64::new(0x1000, 64)), Val::I128(2), &mut solver, false, ReadOpts::default())
        .unwrap();
    assert!(solver.check_sat(info).is_sat().unwrap());
    assert!(solver
        .check_sat_with(&Exp::Neq(Box::new(smt_value(&value, info).unwrap()), Box::new(bits64(0, 16))), info)
        .is_unsat()
        .unwrap());
}

#[test]
fn 关联生成器初值与局部写入在宽地址下保持一致() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    for width in [32, 64, 65, 129] {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::new();
        let calls = Arc::new(AtomicUsize::new(0));
        let generated = calls.clone();
        memory.add_region(Region::Constrained(
            0x1000..0x1002,
            Arc::new(move |solver| {
                generated.fetch_add(1, Ordering::SeqCst);
                let byte = solver.declare_bitvector(8, info);
                solver.define_bitvector(Exp::Concat(Box::new(Exp::Var(byte)), Box::new(Exp::Var(byte))), info)
            }),
        ));
        install_seq_memory(&mut memory, 64, &mut solver);
        let address = solver.declare_bitvector(width, info);
        let original = if width > 64 {
            Exp::Concat(Box::new(bits64(1, width - 64)), Box::new(bits64(0x1000, 64)))
        } else {
            bits64(0x1000, width)
        };
        solver.assert_eq(Exp::Var(address), original);
        let before = memory
            .read(Val::Unit, Val::Symbolic(address), Val::I128(2), &mut solver, false, ReadOpts::default())
            .unwrap();
        assert_eq!(calls.load(Ordering::SeqCst), 1, "一次整区域读取只能调用一次生成器");
        let before = smt_value(&before, info).unwrap();
        assert!(solver.check_sat(info).is_sat().unwrap());
        assert!(solver
            .check_sat_with(
                &Exp::Neq(
                    Box::new(Exp::Extract(7, 0, Box::new(before.clone()))),
                    Box::new(Exp::Extract(15, 8, Box::new(before.clone())))
                ),
                info
            )
            .is_unsat()
            .unwrap());
        memory
            .write(
                Val::Unit,
                Val::Bits(B64::new(0x1001, 64)),
                Val::Bits(B64::new(0x7e, 8)),
                &mut solver,
                None,
                WriteOpts::default(),
            )
            .unwrap();
        let after = memory
            .read(Val::Unit, Val::Symbolic(address), Val::I128(2), &mut solver, false, ReadOpts::default())
            .unwrap();
        let expected = Exp::Concat(Box::new(bits64(0x7e, 8)), Box::new(Exp::Extract(7, 0, Box::new(before))));
        assert!(solver.check_sat(info).is_sat().unwrap());
        assert!(solver
            .check_sat_with(&Exp::Neq(Box::new(smt_value(&after, info).unwrap()), Box::new(expected)), info)
            .is_unsat()
            .unwrap());
        assert!(solver.trace().to_vec().iter().any(|e| matches!(e, Event::ReadMem { address: Val::Symbolic(a), bytes: 2, region: "constrained", .. } if *a == address)));
        assert!(matches!(
            memory.read(Val::Unit, Val::Symbolic(address), Val::I128(1), &mut solver, false, ReadOpts::default()),
            Err(ExecError::BadRead(_))
        ));
    }
}

#[test]
fn 整数绝对值保留具体溢出与符号位向量契约() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let abs = primop::unary_primops()["abs_int"];
    for (input, expected) in
        [(i128::MIN, i128::MIN), (i128::MIN + 1, i128::MAX), (-1, 1), (0, 0), (1, 1), (i128::MAX, i128::MAX)]
    {
        if input == i128::MIN {
            assert!(matches!(abs(Val::I128(input), &mut solver, info), Err(ExecError::Overflow)));
        } else {
            assert_eq!(abs(Val::I128(input), &mut solver, info).unwrap(), Val::I128(expected));
        }
        let input = solver.define_const(smt_i128(input), info);
        let result = abs(Val::Symbolic(input), &mut solver, info).unwrap();
        assert!(solver.check_sat(info).is_sat().unwrap());
        assert!(solver
            .check_sat_with(&Exp::Neq(Box::new(smt_value(&result, info).unwrap()), Box::new(smt_i128(expected))), info)
            .is_unsat()
            .unwrap());
    }
}
