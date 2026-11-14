//! 常量剪边、额外出口与槽位活跃性必须使用同一份证明。
use super::*;
use crate::bitvector::b64::B64;
use crate::ir::{Ty, HAVE_EXCEPTION};
use crate::source_loc::SourceLoc;

fn analyzed(body: &[Instr<Name, B64>]) -> FunctionRegions<B64> {
    FunctionRegions::with_options(
        body,
        RegionOptions {
            recreated_slot_liveness: true,
            filter_assertion_failures: true,
            have_exception: Some(HAVE_EXCEPTION),
            ..RegionOptions::default()
        },
    )
    .with_constant_returns(HashMap::new())
}

fn name(id: u32) -> Name {
    Name::from_u32(id + 100)
}
fn jump(pc: usize) -> Instr<Name, B64> {
    Instr::Jump(Exp::Id(name(0)), pc, SourceLoc::unknown())
}
fn decl(id: Name) -> Instr<Name, B64> {
    Instr::Decl(id, Ty::Bool, SourceLoc::unknown())
}
fn copy(id: Name, exp: Exp<Name>) -> Instr<Name, B64> {
    Instr::Copy(Loc::Id(id), exp, SourceLoc::unknown())
}

fn guarded_read(condition: Exp<Name>) -> Vec<Instr<Name, B64>> {
    vec![
        jump(3),
        decl(name(1)),
        Instr::Goto(4),
        decl(name(2)),
        Instr::Jump(condition, 6, SourceLoc::unknown()),
        Instr::Goto(7),
        copy(RETURN, Exp::Id(name(1))),
        Instr::End,
    ]
}

#[test]
fn constant_liveness_false_read_dies_but_true_and_symbolic_reads_stay_live() {
    for (condition, live) in [(Exp::Bool(false), false), (Exp::Bool(true), true), (Exp::Id(name(4)), true)] {
        let body = guarded_read(condition);
        let mut regions = analyzed(&body);
        assert_eq!(regions.analysis().future_reads[4].contains(&name(1)), live);
        assert_eq!(regions.region(0).unwrap().local_variables.contains(&name(1)), !live);
        assert_eq!(regions.analysis().full_cfg.successors(4).count(), regions.cfg().successors(4).count());
        assert!(!regions.region(0).unwrap().local_variables.contains(&RETURN));
    }
}

#[test]
fn constant_liveness_prunes_internal_dead_edge_from_extra_boundary() {
    let body = vec![
        jump(6),
        decl(name(1)),
        Instr::Jump(Exp::Bool(false), 8, SourceLoc::unknown()),
        copy(RETURN, Exp::Bool(true)),
        Instr::Goto(7),
        Instr::End,
        copy(RETURN, Exp::Bool(false)),
        Instr::End,
        copy(RETURN, Exp::Id(name(1))),
        Instr::End,
    ];
    let mut regions = analyzed(&body);
    assert!(!regions.analysis().future_reads[2].contains(&name(1)));
    let region = regions.region(0).unwrap();
    assert_eq!(region.join, RegionPoint::Instruction(7));
    assert!(!region.nodes.contains(&8));
    assert!(region.local_variables.contains(&name(1)), "不可达读取不能作为额外出口重新引入");
}

#[test]
fn constant_liveness_unknown_call_and_conflicting_facts_keep_both_edges() {
    let info = SourceLoc::unknown();
    for middle in [
        vec![Instr::Call(Loc::Id(name(5)), false, name(9), vec![], info)],
        vec![jump(3), copy(name(4), Exp::Bool(true))],
    ] {
        let mut body = vec![Instr::Init(name(4), super::super::Ty::Bool, Exp::Bool(false), info)];
        body.extend(middle);
        let branch = body.len();
        body.push(Instr::Jump(Exp::Id(name(4)), branch + 2, info));
        body.push(Instr::End);
        body.push(copy(RETURN, Exp::Id(name(1))));
        body.push(Instr::End);
        let regions = analyzed(&body);
        assert_eq!(regions.cfg().successors(branch).count(), 2);
        assert_eq!(regions.analysis().full_cfg.successors(branch).count(), 2);
        assert!(regions.analysis().future_reads[branch].contains(&name(1)));
    }
}

#[test]
fn constant_liveness_keeps_exception_boundary_and_backedge_reads() {
    let info = SourceLoc::unknown();
    for inverted in [false, true] {
        let condition = if inverted { Exp::Id(HAVE_EXCEPTION).bool_not() } else { Exp::Id(HAVE_EXCEPTION) };
        let body = vec![
            jump(6),
            decl(name(1)),
            Instr::Jump(condition, if inverted { 4 } else { 9 }, info),
            Instr::Goto(if inverted { 9 } else { 4 }),
            copy(RETURN, Exp::Bool(true)),
            Instr::Goto(7),
            copy(RETURN, Exp::Bool(false)),
            Instr::End,
            Instr::End,
            copy(RETURN, Exp::Id(name(1))),
            Instr::Exit(super::super::ExitCause::Explicit, info),
        ];
        let mut regions = analyzed(&body);
        assert_eq!(regions.cfg().successors(2).count(), 1);
        assert_eq!(regions.analysis().full_cfg.successors(2).count(), 2);
        assert_eq!(regions.region(0).unwrap().join, RegionPoint::Instruction(7));
        assert!(!regions.region(0).unwrap().local_variables.contains(&name(1)));
    }
    let body = vec![
        copy(RETURN, Exp::Id(name(1))),
        jump(4),
        decl(name(1)),
        Instr::Goto(5),
        copy(RETURN, Exp::Bool(false)),
        jump(0),
        Instr::End,
    ];
    let mut regions = analyzed(&body);
    assert!(regions.analysis().future_reads[5].contains(&name(1)));
    assert!(!regions.region(1).unwrap().local_variables.contains(&name(1)));
}

#[test]
fn constant_liveness_preserves_return_escaped_and_entry_slots() {
    let body = vec![jump(3), decl(RETURN), Instr::Goto(4), decl(name(2)), Instr::End];
    assert!(analyzed(&body).analysis().future_reads[4].contains(&RETURN));
    assert!(!analyzed(&body).region(0).unwrap().local_variables.contains(&RETURN));
    let mut body = guarded_read(Exp::Bool(false));
    body[6] = copy(name(5), Exp::Ref(name(1)));
    assert!(!analyzed(&body).region(0).unwrap().local_variables.contains(&name(1)), "取地址仍全函数保守保留");
    let body = vec![decl(name(1)), jump(4), decl(name(1)), Instr::Goto(5), decl(name(2)), Instr::End];
    assert!(!analyzed(&body).region(1).unwrap().local_variables.contains(&name(1)), "入口已有槽仍不能删除");
}
