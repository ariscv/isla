//! 后续轮次独审回归：断言死臂不能向最终前态足迹发布读取。
use super::*;

#[test]
fn region_loop_round_review_dead_prefix_discards_register_read() {
    let mut shared = empty_shared_state();
    let reg = shared.symtab.intern("zdead_loop_prefix");
    shared.registers.insert(reg, Ty::Bool);
    let counter = test_name(1300);
    let unit = test_name(1301);
    for (initialized, survivor_reads) in [(false, false), (true, false), (true, true)] {
        let program = vec![
            Instr::Jump(input(0), 3, info()),
            Instr::Copy(Loc::Id(RETURN), if survivor_reads { Exp::Id(reg) } else { Exp::Bool(true) }, info()),
            Instr::Goto(13),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
            Instr::Init(counter, Ty::I128, Exp::I128(0), info()),
            Instr::Jump(input(1), 9, info()),
            Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(counter), Exp::I128(1)]), 11, info()),
            Instr::PrimopBinary(
                Loc::Id(counter),
                primop::binary_primops()["add_int"],
                Exp::Id(counter),
                Exp::I128(1),
                info(),
            ),
            Instr::Goto(5),
            Instr::PrimopBinary(
                Loc::Id(unit),
                primop::binary_primops()["optimistic_assert"],
                input(0).bool_not(),
                Exp::String("后续轮次所有出口死亡".into()),
                info(),
            ),
            Instr::Goto(13),
            Instr::PrimopBinary(
                Loc::Id(unit),
                primop::binary_primops()["optimistic_assert"],
                input(0).bool_not(),
                Exp::String("后续轮次另一出口死亡".into()),
                info(),
            ),
            Instr::Goto(13),
            Instr::End,
        ];
        let forked = paths_with_state(
            program.clone(),
            &shared,
            2,
            ExecutionLimits::default().with_region_loop_analysis(true),
            crate::memory::Memory::new(),
            |frame| {
                if initialized {
                    frame.regs_mut().assign(reg, Val::Bool(true), &shared);
                }
                frame.vars_mut().insert(unit, UVal::Init(Val::Unit));
            },
        );
        let merged = paths_with_state(
            program,
            &shared,
            2,
            ExecutionLimits::default().with_path_merging(true).with_region_loop_analysis(true),
            crate::memory::Memory::new(),
            |frame| {
                if initialized {
                    frame.regs_mut().assign(reg, Val::Bool(true), &shared);
                }
                frame.vars_mut().insert(unit, UVal::Init(Val::Unit));
            },
        );
        equivalent_paths(&forked, &merged, 2, false);
        assert_eq!(merged.len(), 1);
        assert!(merged[0].records.iter().any(|record| record.branch_pc == 0));
        assert_eq!(
            merged[0].events.iter().filter(|event| matches!(event, Event::ReadReg(name, _, _) if *name == reg)).count(),
            usize::from(survivor_reads),
            "整条逻辑臂死亡后须撤销前缀读取；存活兄弟臂仍须独立发布其读取"
        );
        if !initialized {
            assert!(merged[0].registers.get_last_if_initialized(reg).is_none(), "死臂惰性初值不得提升到存活兄弟臂");
        }
    }
}
