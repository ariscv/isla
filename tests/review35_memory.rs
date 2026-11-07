use isla::isarch::memory_model::install_seq_memory;
use isla_lib::bitvector::{b129::B129, b64::B64, BV};
use isla_lib::ir::Val;
use isla_lib::memory::Memory;
use isla_lib::primop_util::smt_value;
use isla_lib::smt::{
    smtlib::{self, Exp},
    Config, Context, Event, ReadOpts, Solver, WriteOpts,
};
use isla_lib::source_loc::SourceLoc;

fn read_with_width(width: u32) {
    let info = SourceLoc::unknown();
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let mut memory = Memory::new();
    memory.add_zero_region(0x2000000..0x20c0000);
    install_seq_memory(&mut memory, 64, &mut solver);
    let address = solver.declare_const(smtlib::Ty::BitVec(width), info);
    let low = if width > 64 { Exp::Extract(63, 0, Box::new(Exp::Var(address))) } else { Exp::Var(address) };
    solver.assert_eq(low, smtlib::bits64(0x2000000, width.min(64)));
    let value =
        memory.read(Val::Unit, Val::Symbolic(address), Val::I128(1), &mut solver, false, ReadOpts::default()).unwrap();
    assert!(solver.check_sat(info).is_sat().unwrap());
    assert!(solver
        .check_sat_with(&Exp::Neq(Box::new(smt_value(&value, info).unwrap()), Box::new(smtlib::bits64(0, 8))), info)
        .is_unsat()
        .unwrap());
    assert!(solver
        .trace()
        .to_vec()
        .iter()
        .any(|e| matches!(e, Event::ReadMem {address: Val::Symbolic(a), ..} if *a == address)));
}
#[test]
fn review35_seq_width_64() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    read_with_width(64);
}
#[test]
fn review35_seq_width_65() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    read_with_width(65);
}
#[test]
fn review35_seq_width_129() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    read_with_width(129);
}
#[test]
fn review35_seq_width_1024() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    read_with_width(1024);
}
#[test]
fn review35_seq_concrete_wide_read() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B129>::new(&ctx);
    let mut memory = Memory::new();
    memory.add_zero_region(0x2000000..0x20c0000);
    install_seq_memory(&mut memory, 64, &mut solver);
    let address = B129::new(0x2000000, 129);
    memory.read(Val::Unit, Val::Bits(address), Val::I128(1), &mut solver, false, ReadOpts::default()).unwrap();
    assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
}
#[test]
fn review35_seq_initial_and_write_read_matrix() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let info = SourceLoc::unknown();
    for sw in [false, true] {
        for sr in [false, true] {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let mut memory = Memory::new();
            memory.add_zero_region(0x2000000..0x20c0000);
            install_seq_memory(&mut memory, 64, &mut solver);
            let a = solver.declare_const(smtlib::Ty::BitVec(64), info);
            solver.assert_eq(Exp::Var(a), smtlib::bits64(0x2000000, 64));
            let address = |symbolic| if symbolic { Val::Symbolic(a) } else { Val::Bits(B64::new(0x2000000, 64)) };
            let initial =
                memory.read(Val::Unit, address(sr), Val::I128(1), &mut solver, false, ReadOpts::default()).unwrap();
            assert!(solver
                .check_sat_with(
                    &Exp::Neq(Box::new(smt_value(&initial, info).unwrap()), Box::new(smtlib::bits64(0, 8))),
                    info
                )
                .is_unsat()
                .unwrap());
            memory
                .write(Val::Unit, address(sw), Val::Bits(B64::new(0xa5, 8)), &mut solver, None, WriteOpts::default())
                .unwrap();
            let after =
                memory.read(Val::Unit, address(sr), Val::I128(1), &mut solver, false, ReadOpts::default()).unwrap();
            assert!(solver
                .check_sat_with(
                    &Exp::Neq(Box::new(smt_value(&after, info).unwrap()), Box::new(smtlib::bits64(0xa5, 8))),
                    info
                )
                .is_unsat()
                .unwrap());
            assert!(solver.check_sat(info).is_sat().unwrap());
        }
    }
}

#[test]
fn review35_named_tlb_dependency_baseline_comparison() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    use isla_lib::executor::{start_single, LocalFrame, Run, TaskId, TaskState};
    use isla_lib::ir::{Exp as IrExp, IRTypeInfo, Instr, Loc, SharedState, Symtab, Ty as IrTy, UVal, RETURN};
    use std::{collections::HashSet, sync::Mutex};
    let info = SourceLoc::unknown();
    let defs = &[];
    let mut symtab = Symtab::new();
    let reg = symtab.intern("zcore_TLB");
    let function = symtab.intern("zreview35");
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
    let instrs = vec![Instr::Copy(Loc::Id(RETURN), IrExp::Id(reg), info), Instr::End];
    let mut frame = LocalFrame::new(function, &[], &IrTy::Bits(8), None, &instrs);
    frame.regs_mut().insert(reg, false, UVal::Uninit(&IrTy::Bits(8)));
    let state = TaskState::new();
    let out = Mutex::new(Vec::new());
    start_single(frame.task(TaskId::fresh(), &state), &shared, &out, &|_, _, result, _, solver, out| {
        let Ok((Run::Finished(value), _)) = result else { panic!("应完成读取") };
        let events: Vec<_> = solver.trace().to_vec().into_iter().cloned().collect();
        let references = isla_lib::simplify::EventReferences::from_events(&events);
        out.lock().unwrap().push(references.value_taints(&value, &events).registers.contains(&(reg, Vec::new())));
    });
    assert_eq!(*out.lock().unwrap(), vec![true], "core_TLB应保留数据依赖");
}

fn write_with_width(width: u32) {
    let info = SourceLoc::unknown();
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    let mut memory = Memory::new();
    memory.add_zero_region(0x2000000..0x20c0000);
    install_seq_memory(&mut memory, 64, &mut solver);
    let address = solver.declare_const(smtlib::Ty::BitVec(width), info);
    let low = if width > 64 { Exp::Extract(63, 0, Box::new(Exp::Var(address))) } else { Exp::Var(address) };
    solver.assert_eq(low, smtlib::bits64(0x2000000, 64));
    memory
        .write(Val::Unit, Val::Symbolic(address), Val::Bits(B64::new(0xa5, 8)), &mut solver, None, WriteOpts::default())
        .unwrap();
    let value =
        memory.read(Val::Unit, Val::Symbolic(address), Val::I128(1), &mut solver, false, ReadOpts::default()).unwrap();
    assert!(solver.check_sat(info).is_sat().unwrap());
    assert!(solver
        .check_sat_with(&Exp::Neq(Box::new(smt_value(&value, info).unwrap()), Box::new(smtlib::bits64(0xa5, 8))), info)
        .is_unsat()
        .unwrap());
}
#[test]
fn review35_seq_write_width_64() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    write_with_width(64);
}
#[test]
fn review35_seq_write_width_65() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    write_with_width(65);
}
#[test]
fn review35_seq_write_width_129() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    write_with_width(129);
}
#[test]
fn review35_seq_write_width_1024() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    write_with_width(1024);
}
