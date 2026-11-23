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
    check_arrival_permutations(ValueShape::Integer, crate::config::MergeStrategy::Recursive);
}

#[test]
fn region_join_plan_struct_integer_permutations() {
    check_arrival_permutations(ValueShape::StructInteger, crate::config::MergeStrategy::Recursive);
}

#[test]
fn region_join_plan_fixed_tree_union_permutations() {
    check_arrival_permutations(ValueShape::Union, crate::config::MergeStrategy::Recursive);
}

#[test]
fn region_join_plan_d8_five_leaves_in_stack_and_fifo_order() {
    for strategy in [crate::config::MergeStrategy::Recursive, crate::config::MergeStrategy::Flat] {
        check_arrival_permutations(ValueShape::Strings, strategy);
    }
}

#[derive(Clone, Copy)]
enum ValueShape {
    Integer,
    StructInteger,
    Union,
    Strings,
}

fn check_arrival_permutations(shape: ValueShape, strategy: crate::config::MergeStrategy) {
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
    let strings = matches!(shape, ValueShape::Strings);
    limits.merge_concrete_values = strings;
    limits.merge_strategy = strategy;
    let state = TaskState::new().with_execution_limits(limits);
    let base = prepare_region_base(&frame, &region, 1, crate::config::MergeMode::Adaptive, &state, info());
    let context = Context::new(Config::new());
    for count in (if strings { 5 } else { 3 })..=5 {
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
                    let value = match (shape, index) {
                        (ValueShape::StructInteger, _) => {
                            let field = if index == 1 { Val::Symbolic(input) } else { Val::I64(3 + 2 * index as i64) };
                            Val::Struct([(p, field)].into_iter().collect())
                        }
                        (ValueShape::Integer, 1) => Val::Symbolic(input),
                        (ValueShape::Integer, _) => Val::I64(3 + 2 * index as i64),
                        (ValueShape::Union, 1 | 3) => Val::Ctor(q, Box::new(Val::Unit)),
                        (ValueShape::Union, 2) => Val::Ctor(p, Box::new(Val::String("c".into()))),
                        (ValueShape::Union, _) => Val::Ctor(p, Box::new(Val::String("a".into()))),
                        (ValueShape::Strings, _) => Val::String(["a", "b", "c", "a", "b"][index].into()),
                    };
                    leaf.vars_mut().insert(slot, UVal::Init(value));
                    leaf
                })
                .collect::<Vec<_>>();
            let mut pending = crate::executor::region_engine::ReadyFragments::new(&state);
            pending.extend(order[..2].iter().copied());
            let first = pending.pop().unwrap();
            pending.extend(order[2..].iter().copied());
            let arrivals = std::iter::once(first)
                .chain(std::iter::from_fn(|| pending.pop()))
                .map(|index| join_groups::Arrival {
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
            let union = matches!(shape, ValueShape::Union);
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

struct PlanCase<'ctx> {
    leaves: Vec<LocalFrame<'static, B64>>,
    base: LocalFrame<'static, B64>,
    region: Region,
    state: TaskState<B64>,
    shared: SharedState<'static, B64>,
    solver: Solver<'ctx, B64>,
    condition: Sym,
}

impl<'ctx> PlanCase<'ctx> {
    fn new(ctx: &'ctx Context, values: impl FnOnce(Sym, Name, Name) -> Vec<Val<B64>>) -> Self {
        let mut shared = empty_shared_state();
        let slot = shared.symtab.intern("zvalue");
        let k = shared.symtab.intern("zk");
        let q = shared.symtab.intern("zq");
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
        let mut solver = Solver::new(ctx);
        let selector = solver.declare_const(smtlib::Ty::BitVec(64), info());
        let input = solver.declare_const(smtlib::Ty::BitVec(64), info());
        let condition = solver.declare_const(smtlib::Ty::Bool, info());
        solver.start_transaction();
        let leaves = values(input, k, q)
            .into_iter()
            .enumerate()
            .map(|(i, value)| {
                let guard = smtlib::Exp::Eq(
                    Box::new(smtlib::Exp::Var(selector)),
                    Box::new(crate::primop_util::smt_i64(i as i64)),
                );
                let mut leaf = branch_arm(&base, 1, guard, solver.new_logical_arm(None));
                leaf.vars_mut().insert(slot, UVal::Init(value));
                leaf
            })
            .collect();
        Self { leaves, base, region: (*region).clone(), state, shared, solver, condition }
    }

    fn arrivals(&self, order: &[usize]) -> Vec<join_groups::Arrival<'static, B64>> {
        // 按输入排列重新赋来源坐标，避免被 prepare 的来源排序直接还原。
        order
            .iter()
            .enumerate()
            .map(|(pos, &i)| join_groups::Arrival { source: (0, pos), frame: self.leaves[i].clone() })
            .collect()
    }

    fn prepare(&self, arrivals: Vec<join_groups::Arrival<'static, B64>>) -> join_groups::JoinPlan<'static, B64> {
        join_groups::JoinPlan::prepare(
            arrivals,
            self.condition,
            true,
            &self.base,
            &self.region,
            &self.state,
            &self.shared,
            &self.solver,
            info(),
        )
        .unwrap()
    }

    fn check_oracle(&mut self) {
        let n = self.leaves.len();
        let mut order: Vec<_> = (0..n).collect();
        let arrivals = self.arrivals(&order);
        // 对每个非空块独立测试全部排列。位掩码仅用于此 n ≤ 6 的对照。
        let mut feasible = vec![false; 1 << n];
        let mut orders = 0;
        for (mask, ok) in feasible.iter_mut().enumerate().skip(1) {
            let mut block: Vec<_> = (0..n).filter(|i| mask & (1 << i) != 0).collect();
            permutations(&mut block, 0, &mut |perm| {
                orders += 1;
                *ok |= join_groups::JoinPlan::feasible_order(
                    &arrivals,
                    perm,
                    &self.base,
                    &self.region,
                    &self.state,
                    &self.shared,
                    &self.solver,
                    info(),
                );
            });
        }
        fn partitions(
            i: usize,
            n: usize,
            blocks: &mut Vec<usize>,
            feasible: &[bool],
            best: &mut usize,
            count: &mut usize,
        ) {
            if i == n {
                *count += 1;
                if blocks.iter().all(|&b| feasible[b]) {
                    *best = (*best).min(blocks.len());
                }
                return;
            }
            let member = 1 << i;
            for b in 0..blocks.len() {
                blocks[b] |= member;
                partitions(i + 1, n, blocks, feasible, best, count);
                blocks[b] ^= member;
            }
            blocks.push(member);
            partitions(i + 1, n, blocks, feasible, best, count);
            blocks.pop();
        }
        let (mut best, mut count) = (n, 0);
        partitions(0, n, &mut Vec::new(), &feasible, &mut best, &mut count);
        assert_eq!(count, [1, 1, 2, 5, 15, 52, 203][n]);
        let mut schedules = 0;
        let mut check = |perm: &[usize]| {
            schedules += 1;
            let mark = self.solver.next_join_symbol();
            let plan = self.prepare(self.arrivals(perm));
            assert_eq!(mark, self.solver.next_join_symbol());
            assert_eq!(plan.groups().len(), best, "排列 {perm:?}");
            let tx = self.solver.start_transaction();
            plan.construct(&self.base, &self.region, &self.state, &self.shared, &mut self.solver, info()).unwrap();
            self.solver.rollback_transaction(tx);
        };
        if n <= 5 {
            permutations(&mut order, 0, &mut check)
        } else {
            check(&order)
        }
        println!("oracle n={n} orders={orders} partitions={count} schedules={schedules} minimum={best}");
    }
}

#[test]
fn region_join_plan_exhaustive_oracle() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    // 0、1 和 2 分别是两个具体整数、符号整数；3..5 包结构体，6..7 是字符串。
    let mut cases = vec![
        vec![3, 4, 5],
        vec![0, 1, 2, 6],
        vec![3, 4, 5, 7],
        vec![0, 1, 2, 6, 7],
        vec![3, 4, 5, 3, 7],
        vec![3, 4, 5, 0, 1, 2],
        vec![0, 1, 2, 3, 6, 7],
        vec![6, 7, 6, 7, 7, 6],
    ];
    // 固定随机源，使不同类型的重复、缺失与最后到达的符号成员都可复验。
    let mut seed = 20261124u64;
    let mut code = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (seed >> 61) as u8
    };
    for n in 4..=6 {
        cases.extend((0..12).map(|_| (0..n).map(|_| code()).collect::<Vec<_>>()));
    }
    for codes in cases {
        PlanCase::new(&ctx, |x, k, _| {
            codes
                .iter()
                .map(|c| {
                    let integer = match c % 3 {
                        0 => Val::I64(3),
                        1 => Val::I64(7),
                        _ => Val::Symbolic(x),
                    };
                    match c {
                        0..=2 => integer,
                        3..=5 => Val::Struct([(k, integer)].into_iter().collect()),
                        6 => Val::String("p".into()),
                        7 => Val::String("q".into()),
                        _ => unreachable!(),
                    }
                })
                .collect()
        })
        .check_oracle();
    }

    // 冲突边依次为 0–2、2–3、3–1。贪心先配 0、1 后剩三组；最优是 {0,3} 和 {1,2}。
    PlanCase::new(&ctx, |_, p, q| (0..4).map(|i| conflict_value(i, p, q)).collect()).check_oracle();
}

fn conflict_value(i: usize, p: Name, q: Name) -> Val<B64> {
    if i >= 4 {
        return Val::I64(i as i64);
    }
    Val::Vector(
        [(0, 2), (2, 3), (3, 1)]
            .into_iter()
            .map(|(a, b)| {
                if i == a || i == b {
                    Val::Ctor(p, Box::new(Val::String(if i == a { "p" } else { "q" }.into())))
                } else {
                    Val::Ctor(q, Box::new(Val::Unit))
                }
            })
            .collect(),
    )
}

#[test]
#[ignore = "显式采集 n=3..64 的汇合计划耗时"]
fn region_join_plan_partition_timings() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    for n in 3..=64 {
        for shape in ["nested", "distinct", "labels", "conflicts"] {
            let case = PlanCase::new(&ctx, |x, k, q| {
                (0..n)
                    .map(|i| match shape {
                        "nested" => Val::Struct(
                            [(k, if i + 1 == n { Val::Symbolic(x) } else { Val::I64(i as i64) })].into_iter().collect(),
                        ),
                        "conflicts" => conflict_value(i, k, q),
                        "distinct" => Val::I64(i as i64),
                        "labels" => Val::String((i % 3).to_string()),
                        _ => unreachable!(),
                    })
                    .collect()
            });
            let order: Vec<_> = (0..n).collect();
            let mut times = Vec::new();
            let mut calls = 0;
            let mut groups = 0;
            for _ in 0..5 {
                let arrivals = case.arrivals(&order);
                join_groups::FOLD_ATTEMPTS.set(0);
                let start = std::time::Instant::now();
                let plan = case.prepare(arrivals);
                times.push(start.elapsed().as_nanos());
                calls = join_groups::FOLD_ATTEMPTS.get();
                groups = plan.groups().len();
            }
            assert_eq!(
                groups,
                match shape {
                    "nested" => 1,
                    "conflicts" => 2 + n.saturating_sub(4),
                    "distinct" => n,
                    "labels" => 3,
                    _ => unreachable!(),
                }
            );
            times.sort_unstable();
            println!("bench,{shape},{n},{groups},{calls},{}", times[2]);
        }
    }
}

#[test]
fn outer_join_merges_equivalent_fragments_to_fewest_paths() {
    use super::region_merge_tests::{equivalent_paths, input, paths_with_state};
    let mut shared = empty_shared_state();
    let slot = shared.symtab.intern("zlabel");
    let write = |s: &str| Instr::Copy(Loc::Id(slot), Exp::String(s.into()), info());
    for (labels, expected) in [(["p", "q", "p", "q"], 2), (["p", "q", "q", "s"], 3), (["p", "q", "r", "s"], 4)] {
        let program = vec![
            Instr::Decl(slot, Ty::String, info()),
            Instr::Jump(input(0), 7, info()),
            Instr::Jump(input(1), 5, info()),
            write(labels[0]),
            Instr::Goto(6),
            write(labels[1]),
            Instr::Goto(12),
            Instr::Jump(input(2), 10, info()),
            write(labels[2]),
            Instr::Goto(11),
            write(labels[3]),
            Instr::Goto(12),
            Instr::PrimopBinary(
                Loc::Id(RETURN),
                primop::binary_primops()["eq_string"],
                Exp::Id(slot),
                Exp::String("q".into()),
                info(),
            ),
            Instr::End,
        ];
        let run = |limits| paths_with_state(program.clone(), &shared, 3, limits, crate::memory::Memory::new(), |_| ());
        let ordinary = run(ExecutionLimits::default().with_path_merging(false));
        for strategy in [crate::config::MergeStrategy::Recursive, crate::config::MergeStrategy::Flat] {
            let mut limits = ExecutionLimits::default().with_path_merging(true);
            limits.merge_concrete_values = false;
            limits.merge_strategy = strategy;
            assert_eq!(equivalent_paths(&ordinary, &run(limits), 3, true), (4, expected));
        }
    }
}

#[test]
fn region_join_plan_struct_bridge_preserves_path_results() {
    use super::region_merge_tests::{equivalent_paths, input, paths_with_state};
    let mut shared = empty_shared_state();
    let slot = shared.symtab.intern("zrecord");
    let ty = shared.symtab.intern("zrecord_type");
    let k = shared.symtab.intern("zk");
    let bit = shared.symtab.intern("zbit");
    let field = |value| Instr::Copy(Loc::Id(slot), Exp::Struct(ty, vec![(k, value)]), info());
    for observed in [0, 1, 3, 7] {
        let program = vec![
            Instr::Decl(slot, Ty::Struct(ty), info()),
            Instr::Decl(bit, Ty::Bits(1), info()),
            Instr::PrimopUnary(Loc::Id(bit), primop::unary_primops()["isla_bool_to_bit"], input(2), info()),
            Instr::Jump(input(0), 6, info()),
            field(Exp::Call(Op::Unsigned(64), vec![Exp::Id(bit)])),
            Instr::Goto(11),
            Instr::Jump(input(1), 9, info()),
            field(Exp::I64(3)),
            Instr::Goto(10),
            field(Exp::I64(7)),
            Instr::Goto(11),
            Instr::Copy(
                Loc::Id(RETURN),
                Exp::Call(Op::Eq, vec![Exp::Field(Box::new(Exp::Id(slot)), k), Exp::I64(observed)]),
                info(),
            ),
            Instr::End,
        ];
        let run = |limits| paths_with_state(program.clone(), &shared, 3, limits, crate::memory::Memory::new(), |_| ());
        let ordinary = run(ExecutionLimits::default().with_path_merging(false));
        for strategy in [crate::config::MergeStrategy::Recursive, crate::config::MergeStrategy::Flat] {
            let mut limits = ExecutionLimits::default().with_path_merging(true);
            limits.merge_concrete_values = false;
            limits.merge_strategy = strategy;
            assert_eq!(equivalent_paths(&ordinary, &run(limits), 3, true), (3, 1));
        }
    }
}
