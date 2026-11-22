//! 区域臂任务的纯数据交付契约；运行时领取在后续阶段接入。
use super::*;

#[test]
fn 区域臂重命名按区域和逻辑臂稳定排序() {
    use crate::executor::region_arm::{ArmPath, RegionId};
    use crate::smt::SymRemap;

    let a = RegionId::new(vec![3, 1]);
    let b = RegionId::new(vec![3, 2]);
    let remap = SymRemap::for_region_arms(
        Sym::from_u32(40),
        vec![
            (b, ArmPath::new(vec![1]), vec![Sym::from_u32(7)]),
            (a.clone(), ArmPath::new(vec![1, 0]), vec![Sym::from_u32(5), Sym::from_u32(6)]),
            (a, ArmPath::new(vec![0]), vec![Sym::from_u32(4)]),
        ],
    );

    assert_eq!(remap.get(Sym::from_u32(4)), Sym::from_u32(40));
    assert_eq!(remap.get(Sym::from_u32(5)), Sym::from_u32(41));
    assert_eq!(remap.get(Sym::from_u32(6)), Sym::from_u32(42));
    assert_eq!(remap.get(Sym::from_u32(7)), Sym::from_u32(43));
}

#[test]
fn 区域臂重命名覆盖定义事件和值且不与串行定义重叠() {
    use crate::smt::smtlib::{Def, Exp, Ty};
    use crate::smt::{Event, SymRemap};

    let remote_a = Sym::from_u32(9);
    let remote_b = Sym::from_u32(10);
    let remap = SymRemap::from_pairs([(remote_a, Sym::from_u32(20)), (remote_b, Sym::from_u32(21))]);
    let events = vec![
        Event::<B64>::Smt(Def::DeclareConst(remote_a, Ty::BitVec(64)), Default::default(), info()),
        Event::Smt(
            Def::DefineConst(
                remote_b,
                Exp::Bvadd(Box::new(Exp::Var(remote_a)), Box::new(Exp::Bits64(B64::from_u64(1)))),
            ),
            Default::default(),
            info(),
        ),
        Event::WriteReg(
            test_name(9910),
            Vec::new(),
            Val::Guarded(remote_a, Box::new((Val::Symbolic(remote_b), Val::Bits(B64::zeros(64))))),
        ),
    ];
    let mapped: Vec<_> = events.iter().map(|event| remap.event(event)).collect();
    let definitions: Vec<_> = mapped.iter().filter_map(Event::defines).collect();

    assert_eq!(definitions, vec![Sym::from_u32(20), Sym::from_u32(21)]);
    assert!(definitions.iter().all(|symbol| symbol.as_u32() >= 20));
    let Event::WriteReg(_, _, value) = &mapped[2] else { panic!("寄存器事件必须保留") };
    let symbols = value.symbolic_variables();
    assert!(symbols.contains(&Sym::from_u32(20)) && symbols.contains(&Sym::from_u32(21)) && symbols.len() == 2);
}

#[test]
fn 区域臂任务开关默认关闭() {
    assert!(!crate::config::PathMergeConfig::default().arms_as_tasks);
}

#[test]
fn 空闲_worker_能认领_b_臂且_a_只能观察到交付() {
    use crate::executor::region_arm::{ArmJobState, JoinCell};
    use std::sync::Arc;

    let cell = Arc::new(JoinCell::new());
    let worker = {
        let cell = Arc::clone(&cell);
        std::thread::spawn(move || {
            assert!(cell.try_claim());
            cell.deliver(Ok(()));
        })
    };
    worker.join().unwrap();
    assert_eq!(cell.state(), ArmJobState::Arrived);
    assert!(!cell.try_claim());
}
