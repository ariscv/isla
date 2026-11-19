use super::*;
use crate::config::MergeStrategy;
use smtlib::Exp as Formula;

const VPN: u64 = 0x0001_7934_69b2_9735;

fn equal(sym: Sym, value: u64, width: u32) -> Formula<Sym> {
    Formula::Eq(Box::new(Formula::Var(sym)), Box::new(smtlib::bits64(value, width)))
}

#[test]
fn region_slice_endpoints_keep_eight_guards_and_join() {
    use smtlib::Exp::{Bool, Bvadd, Bvmul, Bvsub, Ite, Not, Or, Var, ZeroExtend};

    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    for no_smt in [true, false] {
        for strategy in [None, Some(MergeStrategy::Recursive), Some(MergeStrategy::Flat)] {
            let mut config = Config::new();
            config.solver_options.finite_domain_enumeration = true;
            config.solver_options.no_smt = no_smt;
            let context = Context::new(config);
            let verification = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&context);
            let level = solver.declare_bitvector(8, info());
            let mode = solver.declare_const(smtlib::Ty::Bool, info());
            solver.assert(
                (1..=4)
                    .map(|value| equal(level, value, 8))
                    .reduce(|lhs, rhs| Or(Box::new(lhs), Box::new(rhs)))
                    .unwrap(),
            );
            let wide_level = solver.define_const(ZeroExtend(120, Box::new(Var(level))), info());
            let size = solver.define_const(
                Ite(Box::new(Var(mode)), Box::new(smtlib::bits64(9, 128)), Box::new(smtlib::bits64(10, 128))),
                info(),
            );
            let next = solver.define_const(Bvadd(Box::new(Var(wide_level)), Box::new(smtlib::bits64(1, 128))), info());
            let end = solver.define_const(Bvmul(Box::new(Var(next)), Box::new(Var(size))), info());
            let high = solver.define_const(Bvsub(Box::new(Var(end)), Box::new(smtlib::bits64(1, 128))), info());
            let low = solver.define_const(Bvmul(Box::new(Var(wide_level)), Box::new(Var(size))), info());
            let (hi, lo, slice) = (test_name(1820), test_name(1821), test_name(1822));
            let mut frame = make_frame(vec![
                Instr::Decl(slice, Ty::AnyBits, info()),
                Instr::PrimopVariadic(
                    Loc::Id(slice),
                    primop::variadic_primops()["vector_subrange"],
                    vec![Exp::Bits(B64::new(VPN, 64)), Exp::Id(hi), Exp::Id(lo)],
                    info(),
                ),
                Instr::PrimopBinary(
                    Loc::Id(RETURN),
                    primop::binary_primops()["zero_extend"],
                    Exp::Id(slice),
                    Exp::I128(10),
                    info(),
                ),
                Instr::End,
            ]);
            frame.vars_mut().insert(hi, UVal::Init(Val::Symbolic(high)));
            frame.vars_mut().insert(lo, UVal::Init(Val::Symbolic(low)));
            let mut limits = ExecutionLimits::default().with_path_merging(strategy.is_some());
            if let Some(strategy) = strategy {
                limits.merge_strategy = strategy;
            }
            let state = TaskState::new().with_execution_limits(limits);
            let queue = Worker::new_lifo();
            let sink = SingleForkSink { queue: &queue };
            queue.push(frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)));
            let shared = empty_shared_state();
            let mut paths = 0;
            let mut coverage = [0; 8];
            let mut queries = 0;
            while let Some(mut task) = queue.pop() {
                let mut solver = Solver::from_checkpoint(&context, task.checkpoint);
                if let Some((def, event)) = task.fork_cond {
                    solver.add_event(event);
                    solver.add(def);
                }
                let start = crate::smt::test_query_count();
                let result = run_loop(
                    0,
                    task.id,
                    &mut task.fraction,
                    PathTimeout::unlimited(),
                    None,
                    &sink,
                    &mut unfreeze_frame(&task.frame),
                    &state,
                    &shared,
                    &mut solver,
                );
                queries += crate::smt::test_query_count() - start;
                let Run::Finished(result) = result.unwrap() else { panic!("每个守卫都应正常完成") };
                paths += 1;
                let point = checkpoint(&mut solver);
                for (index, count) in coverage.iter_mut().enumerate() {
                    let mut verify = Solver::from_checkpoint(&verification, point.clone());
                    let level_value = (index / 2 + 1) as u64;
                    let size_value = (9 + index % 2) as u64;
                    verify.assert(equal(level, level_value, 8));
                    verify.assert_eq(Var(mode), Bool(size_value == 9));
                    if !verify.check_sat(info()).is_sat().unwrap() {
                        continue;
                    }
                    *count += 1;
                    let expected = (VPN >> (level_value * size_value)) & ((1 << size_value) - 1);
                    let value = match &result {
                        Val::Bits(bits) => {
                            assert_eq!(bits.len(), 10);
                            bits.lower_u64()
                        }
                        Val::Symbolic(sym) => {
                            assert!(verify
                                .check_sat_with(&Not(Box::new(equal(*sym, expected, 10))), info())
                                .is_unsat()
                                .unwrap());
                            expected
                        }
                        _ => panic!("切片结果应为统一的 10 位位向量"),
                    };
                    assert_eq!(value, expected, "输入 {index}，合并策略 {strategy:?}");
                }
            }
            assert_eq!(coverage, [1; 8], "每个输入必须由恰好一个路径守卫覆盖");
            assert_eq!(paths, if strategy.is_some() { 1 } else { 8 }, "{strategy:?}, no_smt={no_smt}");
            if no_smt {
                assert_eq!(queries, 0);
            }
        }
    }
}
