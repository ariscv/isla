use std::collections::HashSet;
use std::sync::Mutex;

use isla::isarch::memory_model::install_seq_memory;
use isla_lib::bitvector::{b64::B64, BV};
use isla_lib::executor::{start_single, ExecutionLimits, LocalFrame, Run, TaskId, TaskState};
use isla_lib::ir::{Exp, IRTypeInfo, Instr, Loc, SharedState, Symtab, Ty, RETURN};
use isla_lib::primop;
use isla_lib::primop_util::smt_value;
use isla_lib::smt::{checkpoint, smtlib, Config, Context, Event, Solver};
use isla_lib::source_loc::SourceLoc;

#[test]
fn review34_自约束内存的具体区域读不能因菱形合流变为任意值() {
    let info = SourceLoc::unknown();
    let defs = &[];
    let mut symtab = Symtab::new();
    let condition = symtab.intern("zreview34_condition");
    let address = symtab.intern("zreview34_address");
    let function = symtab.intern("zreview34_function");
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
        Instr::Decl(condition, Ty::Bool, info),
        Instr::Decl(address, Ty::Bits(64), info),
        Instr::Jump(Exp::Id(condition), 5, info),
        Instr::Copy(Loc::Id(address), Exp::Bits(B64::new(0x2000000, 64)), info),
        Instr::Goto(6),
        Instr::Copy(Loc::Id(address), Exp::Bits(B64::new(0x2000001, 64)), info),
        Instr::PrimopVariadic(
            Loc::Id(RETURN),
            primop::variadic_primops()["read_mem"],
            vec![Exp::Unit, Exp::I128(64), Exp::Id(address), Exp::I128(1)],
            info,
        ),
        Instr::End,
    ];
    let mut observations = Vec::new();
    for enabled in [false, true] {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut frame = LocalFrame::new(function, &[], &Ty::Bits(8), None, &instrs);
        frame.memory_mut().add_zero_region(0x2000000..0x20c0000);
        install_seq_memory(frame.memory_mut(), 64, &mut solver);
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(enabled));
        let out = Mutex::new((0, false, 0, Vec::new()));
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            &shared,
            &out,
            &|_, _, result, _, mut solver, out| {
                let Ok((Run::Finished(value), _)) = result else { panic!("合法数据读必须完成") };
                let mut actual = out.lock().unwrap();
                actual.0 += 1;
                actual.1 |= solver
                    .check_sat_with(
                        &smtlib::Exp::Neq(Box::new(smt_value(&value, info).unwrap()), Box::new(smtlib::bits64(0, 8))),
                        info,
                    )
                    .is_sat()
                    .unwrap();
                for event in solver.trace().to_vec() {
                    match event {
                        Event::Merge(..) => actual.2 += 1,
                        Event::ReadMem { region, .. } => actual.3.push(*region),
                        _ => (),
                    }
                }
            },
        );
        observations.push((enabled, out.into_inner().unwrap()));
    }
    eprintln!("合并开关及(完成路径,可读出非零,合流次数,区域)：{observations:?}");
    assert_eq!(observations[0].1 .0, 2);
    assert!(!observations[0].1 .1, "两个具体地址都必须读出已知零值");
    assert!(!observations[1].1 .1, "合流后同一具体零区域也必须只读出零值");
}
