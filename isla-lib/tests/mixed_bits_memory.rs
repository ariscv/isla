use isla_lib::bitvector::{b64::B64, BV};
use isla_lib::ir::Val;
use isla_lib::memory::Memory;
use isla_lib::primop::binary_primops;
use isla_lib::smt::{
    configure_tastic,
    smtlib::{Exp, Ty},
    Config, Context, Event, Model, ReadOpts, SmtResult, Solver, Tactic, WriteOpts,
};
use isla_lib::source_loc::SourceLoc;

#[test]
fn append_memory_read_address() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let page = solver.declare_const(Ty::BitVec(52), info);
    let address =
        binary_primops::<B64>()["append"](Val::Symbolic(page), Val::Bits(B64::new(8, 12)), &mut solver, info).unwrap();
    solver.assert_eq(Exp::Var(page), Exp::Bits64(B64::new(0x12345, 52)));
    let memory = Memory::<B64>::new();
    let result = memory.read(Val::Unit, address, Val::I128(8), &mut solver, false, ReadOpts::default());
    println!("拼接地址读取: {:?}", result);
    assert!(result.is_ok());
    assert_eq!(solver.check_sat(info), SmtResult::Sat);
    let events = solver.trace().to_vec();
    let addresses: Vec<_> = events
        .iter()
        .filter_map(|event| match event {
            Event::ReadMem { address, bytes, .. } => {
                assert_eq!(*bytes, 8);
                Some(address)
            }
            Event::WriteMem { address, bytes, data, .. } => {
                assert_eq!(*bytes, 8);
                assert_eq!(*data, Val::Bits(B64::new(42, 64)));
                Some(address)
            }
            _ => None,
        })
        .collect();
    assert_eq!(addresses.len(), 1, "每次访存必须保留唯一访问事件");
    assert_eq!(Model::new(&solver).get_val(addresses[0]).unwrap(), Val::Bits(B64::new(0x12345008, 64)));
}

#[test]
fn append_memory_write_address() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let page = solver.declare_const(Ty::BitVec(52), info);
    let address =
        binary_primops::<B64>()["append"](Val::Symbolic(page), Val::Bits(B64::new(8, 12)), &mut solver, info).unwrap();
    solver.assert_eq(Exp::Var(page), Exp::Bits64(B64::new(0x12345, 52)));
    let mut memory = Memory::<B64>::new();
    let result = memory.write(Val::Unit, address, Val::Bits(B64::new(42, 64)), &mut solver, None, WriteOpts::default());
    println!("拼接地址写入: {:?}", result);
    assert!(result.is_ok());
    assert_eq!(solver.check_sat(info), SmtResult::Sat);
    let events = solver.trace().to_vec();
    let addresses: Vec<_> = events
        .iter()
        .filter_map(|event| match event {
            Event::ReadMem { address, bytes, .. } => {
                assert_eq!(*bytes, 8);
                Some(address)
            }
            Event::WriteMem { address, bytes, data, .. } => {
                assert_eq!(*bytes, 8);
                assert_eq!(*data, Val::Bits(B64::new(42, 64)));
                Some(address)
            }
            _ => None,
        })
        .collect();
    assert_eq!(addresses.len(), 1, "每次访存必须保留唯一访问事件");
    assert_eq!(Model::new(&solver).get_val(addresses[0]).unwrap(), Val::Bits(B64::new(0x12345008, 64)));
}
