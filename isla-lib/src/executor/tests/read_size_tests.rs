use super::*;
use crate::config::MergeStrategy;
use crate::smt::FiniteDomain;
use smtlib::Exp as Formula;

const ADDRESS: u64 = 0x1000;

fn equal(symbol: Sym, value: u64, width: u32) -> Formula<Sym> {
    Formula::Eq(Box::new(Formula::Var(symbol)), Box::new(smtlib::bits64(value, width)))
}

fn read_with_finite_size(no_smt: bool, strategy: Option<MergeStrategy>, constrained: bool, excluded: bool) {
    use Formula::{Bvule, Extract, Not, Or, SignExtend, Var, ZeroExtend};

    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    crate::smt::enable_trace_event_guards();
    let mut config = Config::new();
    config.solver_options.finite_domain_enumeration = true;
    config.solver_options.no_smt = no_smt;
    let context = Context::new(config);
    let verification = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let input = solver.declare_bitvector(8, info());
    if constrained {
        solver.assert(
            [1, 2, 4, 8].into_iter().map(|n| equal(input, n, 8)).reduce(|a, b| Or(Box::new(a), Box::new(b))).unwrap(),
        );
        solver.assert(Not(Box::new(equal(input, 2, 8))));
        let independent = solver.declare_bitvector(64, info());
        solver.assert(Bvule(Box::new(Var(independent)), Box::new(smtlib::bits64(100, 64))));
    }
    let wide = solver.define_const(ZeroExtend(120, Box::new(Var(input))), info());
    let machine_int = solver.define_const(Extract(63, 0, Box::new(Var(wide))), info());
    let bytes = solver.define_const(SignExtend(64, Box::new(Var(machine_int))), info());
    if constrained {
        assert!(matches!(solver.finite_domain(bytes), FiniteDomain::Bounded(values) if values.len() == 3));
    } else {
        assert!(matches!(solver.finite_domain(bytes), FiniteDomain::Unknown));
    }

    let length = test_name(1860);
    let data = test_name(1861);
    let mut frame = make_frame(vec![
        Instr::Decl(data, Ty::AnyBits, info()),
        Instr::PrimopVariadic(
            Loc::Id(data),
            primop::variadic_primops()["read_mem"],
            vec![Exp::Unit, Exp::I128(64), Exp::Bits(B64::new(ADDRESS, 64)), Exp::Id(length)],
            info(),
        ),
        Instr::PrimopBinary(
            Loc::Id(RETURN),
            primop::binary_primops()["zero_extend"],
            Exp::Id(data),
            Exp::I128(64),
            info(),
        ),
        Instr::End,
    ]);
    frame.vars_mut().insert(length, UVal::Init(Val::Symbolic(bytes)));
    if excluded {
        let memory = frame.memory_mut();
        memory.add_excluded_region(ADDRESS + 4..ADDRESS + 8);
        memory.add_concrete_region(ADDRESS..ADDRESS + 8, (0..8).map(|i| (ADDRESS + i, i as u8)).collect());
    }
    let mut limits =
        ExecutionLimits::default().with_path_merging(strategy.is_some()).with_region_global_state(strategy.is_some());
    if let Some(strategy) = strategy {
        limits.merge_strategy = strategy;
    }
    let state = TaskState::new().with_execution_limits(limits);
    let shared = empty_shared_state();
    let queue = Worker::new_lifo();
    queue.push(frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)));
    let mut queries = 0;
    let mut coverage = [0; 4];
    let mut paths = 0;
    let mut rejected = 0;
    while let Some(mut task) = queue.pop() {
        let mut solver = Solver::from_checkpoint(&context, task.checkpoint);
        if let Some((def, event)) = task.fork_cond {
            solver.add_event(event);
            solver.add(def);
        }
        let start = crate::smt::test_query_count();
        let run = run_loop(
            0,
            task.id,
            &mut task.fraction,
            PathTimeout::unlimited(),
            None,
            &SingleForkSink { queue: &queue },
            &mut unfreeze_frame(&task.frame),
            &state,
            &shared,
            &mut solver,
        );
        queries += crate::smt::test_query_count() - start;
        if !constrained {
            assert!(matches!(run, Err(ExecError::Smt(crate::error::SmtError::NoSmt { .. }))));
            assert!(!solver.trace().to_vec().iter().any(|event| event.is_memory_read_or_write()));
            paths += 1;
            continue;
        }
        if excluded && matches!(run, Err(ExecError::BadRead(..))) {
            let mut verify = Solver::from_checkpoint(&verification, checkpoint(&mut solver));
            assert!(verify.check_sat(info()).is_sat().unwrap());
            assert!(verify.check_sat_with(&Not(Box::new(equal(input, 8, 8))), info()).is_unsat().unwrap());
            assert!(!solver.trace().to_vec().iter().any(|event| event.is_memory_read_or_write()));
            rejected += 1;
            continue;
        }
        let Run::Finished(result) = run.unwrap() else { panic!("有限长度必须正常完成") };
        paths += 1;
        let point = checkpoint(&mut solver);
        for (index, size) in [1, 2, 4, 8].into_iter().enumerate() {
            let mut verify = Solver::from_checkpoint(&verification, point.clone());
            verify.assert(equal(input, size, 8));
            if verify.check_sat(info()).is_unsat().unwrap() {
                continue;
            }
            coverage[index] += 1;
            let mut active_reads = 0;
            let trace = solver.trace();
            for (event, guard) in trace.events_with_guards_rev() {
                let Event::ReadMem { address, bytes, value, .. } = event else { continue };
                if let Some(guard) = guard {
                    if verify.check_sat_with(guard, info()).is_unsat().unwrap() {
                        continue;
                    }
                    assert!(verify.check_sat_with(&Not(Box::new(guard.clone())), info()).is_unsat().unwrap());
                }
                active_reads += 1;
                assert_eq!(*address, Val::Bits(B64::new(ADDRESS, 64)));
                assert_eq!(u64::from(*bytes), size);
                let bits = bytes * 8;
                assert_eq!(crate::primop_util::length_bits(value, &mut verify, info()).unwrap(), bits);
                let actual = smt_value(&result, info()).unwrap();
                let mut expected = smt_value(value, info()).unwrap();
                if bits < 64 {
                    expected = ZeroExtend(64 - bits, Box::new(expected));
                }
                let differs = Formula::Neq(Box::new(actual), Box::new(expected));
                assert!(verify.check_sat_with(&differs, info()).is_unsat().unwrap());
            }
            assert_eq!(active_reads, 1);
        }
    }
    assert_eq!(paths, if constrained && strategy.is_none() { 3 - usize::from(excluded) } else { 1 });
    assert_eq!(rejected, usize::from(excluded));
    assert_eq!(coverage, if constrained { [1, 0, 1, usize::from(!excluded)] } else { [0; 4] });
    if no_smt {
        assert_eq!(queries, 0);
    }
}

#[test]
fn region_finite_domain_read_size_preserves_guards_and_footprint() {
    for no_smt in [true, false] {
        for strategy in [None, Some(MergeStrategy::Recursive), Some(MergeStrategy::Flat)] {
            read_with_finite_size(no_smt, strategy, true, false);
        }
    }
}

#[test]
fn region_finite_domain_read_size_unknown_preserves_error() {
    read_with_finite_size(true, Some(MergeStrategy::Recursive), false, false);
}

#[test]
fn region_finite_domain_read_size_checks_the_entire_interval() {
    read_with_finite_size(true, Some(MergeStrategy::Recursive), true, true);
}

#[test]
fn finite_domain_shifted_memory_width_reaches_slice() {
    use super::symbolic_finite_domain_tests::run_length_consumer;
    use Formula::{Bvmul, Bvsub, Extract, Not, Var};

    let (results, queries) = run_length_consumer(true, true, |solver, address, variable| {
        let low = solver.define_bitvector(Extract(2, 0, Box::new(Var(address))), info());
        solver.assert(Not(Box::new(equal(low, 0, 3))));
        let unary = primop::unary_primops();
        let count = unary["count_trailing_zeros"](Val::Symbolic(low), solver, info()).unwrap();
        let Val::Symbolic(bytes) = unary["pow2"](count, solver, info()).unwrap() else {
            panic!("访问长度必须依赖符号地址");
        };
        let bits = solver.define_const(Bvmul(Box::new(Var(bytes)), Box::new(smtlib::bits64(8, 128))), info());
        let high = solver.define_const(Bvsub(Box::new(Var(bits)), Box::new(smtlib::bits64(1, 128))), info());
        (
            high,
            Instr::PrimopVariadic(
                Loc::Id(RETURN),
                primop::variadic_primops()["vector_subrange"],
                vec![Exp::Bits(B64::ones(32)), Exp::Id(variable), Exp::I128(0)],
                info(),
            ),
        )
    });
    let mut widths: Vec<_> = results.into_iter().map(|result| result.unwrap()).collect();
    widths.sort_unstable();
    assert_eq!(widths, [(8, vec![1, 3, 5, 7, 9]), (16, vec![2, 6]), (32, vec![4])]);
    assert_eq!(queries, 0);
}
