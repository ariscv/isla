use super::*;
use crate::executor::{region_engine::branch_arm, region_engine::join_groups, region_merge::prepare_region_base};
use crate::ir::regions::{Region, RegionKind, RegionPoint};

fn permutations(prefix: &mut [usize], start: usize, check: &mut impl FnMut(&[usize])) {
    if start == prefix.len() {
        check(prefix);
    }
    for position in start..prefix.len() {
        prefix.swap(start, position);
        permutations(prefix, start + 1, check);
        prefix.swap(start, position);
    }
}

#[test]
fn region_join_plan_fixed_tree_integer_permutations() {
    check_arrival_permutations(false);
}

#[test]
fn region_join_plan_fixed_tree_union_permutations() {
    check_arrival_permutations(true);
}

fn check_arrival_permutations(union: bool) {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let mut shared = empty_shared_state();
    let slot = shared.symtab.intern("zjoinplan_value");
    let p = shared.symtab.intern("zP");
    let q = shared.symtab.intern("zQ");
    let frame = make_frame(vec![Instr::Goto(1), Instr::Goto(2), Instr::End]);
    let region = Arc::new(Region {
        branch_pc: 0,
        has_back_edge: false,
        join: RegionPoint::Instruction(1),
        nodes: Default::default(),
        kind: RegionKind::Reconvergent,
        local_variables: Default::default(),
    });
    let mut limits = ExecutionLimits::default().with_path_merging(true);
    limits.merge_concrete_values = false;
    let state = TaskState::new().with_execution_limits(limits);
    let base = prepare_region_base(&frame, &region, 1, crate::config::MergeMode::Adaptive, &state, info());
    let context = Context::new(Config::new());
    for count in 3..=5 {
        let mut order: Vec<_> = (0..count).collect();
        permutations(&mut order, 0, &mut |order| {
            let mut solver = Solver::new(&context);
            let selector = solver.declare_const(smtlib::Ty::BitVec(64), info());
            let input = solver.declare_const(smtlib::Ty::BitVec(64), info());
            let tx = solver.start_transaction();
            let leaves = (0..count)
                .map(|index| {
                    let owner = solver.new_logical_arm(None);
                    let guard = smtlib::Exp::Eq(
                        Box::new(smtlib::Exp::Var(selector)),
                        Box::new(crate::primop_util::smt_i64(index as i64)),
                    );
                    let mut leaf = branch_arm(&base, 1, guard, owner);
                    let value = match (union, index) {
                        (false, 1) => Val::Symbolic(input),
                        (false, _) => Val::I64(3 + 2 * index as i64),
                        (true, 1 | 3) => Val::Ctor(q, Box::new(Val::Unit)),
                        (true, 2) => Val::Ctor(p, Box::new(Val::String("c".into()))),
                        (true, _) => Val::Ctor(p, Box::new(Val::String("a".into()))),
                    };
                    leaf.vars_mut().insert(slot, UVal::Init(value));
                    leaf
                })
                .collect::<Vec<_>>();
            let arrivals = order
                .iter()
                .map(|&index| join_groups::Arrival {
                    source: (usize::from(index % 2 == 1), index),
                    frame: leaves[index].clone(),
                })
                .collect();
            let condition = solver.declare_const(smtlib::Ty::Bool, info());
            let before = solver.next_join_symbol();
            let plan = join_groups::JoinPlan::prepare(
                arrivals,
                condition,
                true,
                &base,
                &region,
                &state,
                &shared,
                &solver,
                info(),
            )
            .unwrap();
            assert_eq!(solver.next_join_symbol(), before, "纯计划不得分配实际符号");
            let expected = if union {
                let first = (0..count).filter(|&i| i != 2).map(|i| (i % 2, i));
                let mut first = first.collect::<Vec<_>>();
                first.sort_unstable();
                vec![first, vec![(0, 2)]]
            } else {
                let mut all = (0..count).map(|i| (i % 2, i)).collect::<Vec<_>>();
                all.sort_unstable();
                vec![all]
            };
            assert_eq!(plan.groups(), expected, "固定树，{count} 个片段，到达排列 {order:?}");
            // 实际发布逐步核对每个计划节点恰好消费一次。
            let joined = plan.construct(&base, &region, &state, &shared, &mut solver, info()).unwrap();
            match (union, joined) {
                (true, join_groups::Joined::Groups { frames, .. }) => assert_eq!(frames.len(), 2),
                (false, join_groups::Joined::Complete { .. }) => (),
                _ => panic!("计划分区和构造结果不一致"),
            }
            solver.rollback_transaction(tx);
        });
    }
}
