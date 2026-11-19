use super::*;
use crate::config::MergeStrategy;
use crate::smt::{smtlib::bits64, Model};

const BASE: u64 = 0x1000;

fn store(dst: Name, address: Exp<Name>, bytes: u32, value: u64) -> Instr<Name, B64> {
    Instr::PrimopVariadic(
        Loc::Id(dst),
        primop::variadic_primops()["platform_write_mem"],
        vec![Exp::Unit, Exp::I128(64), address, Exp::I128(i128::from(bytes)), Exp::Bits(B64::new(value, 8 * bytes))],
        info(),
    )
}

#[test]
fn region_memory_write_projections_match_forks() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    for case in 0..5 {
        for strategy in [None, Some(MergeStrategy::Recursive), Some(MergeStrategy::Flat)] {
            use smtlib::Exp::{Bool, Bvadd, Eq, Var, ZeroExtend};
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let branch = solver.declare_const(smtlib::Ty::Bool, info());
            let offset = solver.declare_bitvector(1, info());
            let address = solver.define_bitvector(
                Bvadd(Box::new(bits64(BASE, 64)), Box::new(ZeroExtend(63, Box::new(Var(offset))))),
                info(),
            );
            let dst = test_name(2900);
            let address_id = test_name(2901);
            let constant = |n| Exp::Bits(B64::new(n, 64));
            let (mut left, mut right) = match case {
                0 => (vec![store(dst, constant(BASE), 1, 0xA1)], vec![store(dst, constant(BASE), 1, 0xB2)]),
                1 => (vec![store(dst, constant(BASE + 1), 1, 0xA1)], vec![store(dst, constant(BASE), 1, 0xA1)]),
                2 => (
                    vec![store(dst, constant(BASE + 1), 1, 0xB2), store(dst, constant(BASE), 1, 0xA1)],
                    vec![store(dst, constant(BASE), 1, 0xA1), store(dst, constant(BASE + 1), 1, 0xB2)],
                ),
                3 => (vec![store(dst, constant(BASE), 2, 0xB2A1)], vec![store(dst, constant(BASE), 1, 0xA1)]),
                _ => (vec![store(dst, constant(BASE), 2, 0xB2A1), store(dst, Exp::Id(address_id), 2, 0xD4C3)], vec![]),
            };
            let target = left.len() + 2;
            let join = target + right.len();
            let mut program = vec![Instr::Jump(Exp::Id(test_name(0)), target, info())];
            program.append(&mut left);
            program.push(Instr::Goto(join));
            program.append(&mut right);
            program.push(Instr::PrimopVariadic(
                Loc::Id(RETURN),
                primop::variadic_primops()["platform_read_mem"],
                vec![Exp::Unit, Exp::I128(64), constant(BASE), Exp::I128(3)],
                info(),
            ));
            program.push(Instr::End);
            let mut frame = make_frame(program);
            frame.vars_mut().insert(test_name(0), UVal::Init(Val::Symbolic(branch)));
            frame.vars_mut().insert(address_id, UVal::Init(Val::Symbolic(address)));
            frame.vars_mut().insert(dst, UVal::Init(Val::Bool(false)));
            frame.memory_mut().add_concrete_region(BASE..BASE + 3, HashMap::new());
            crate::memory::install_seq_memory(frame.memory_mut(), 64, &mut solver, false);
            let mut limits =
                ExecutionLimits::default().with_path_merging(strategy.is_some()).with_region_global_state(true);
            if let Some(strategy) = strategy {
                limits.merge_strategy = strategy;
            }
            let state = TaskState::new().with_execution_limits(limits);
            let shared = empty_shared_state();
            let queue = Worker::new_lifo();
            queue.push(frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)));
            let mut paths = 0;
            let mut coverage = 0;
            while let Some(mut task) = queue.pop() {
                let mut solver = Solver::from_checkpoint(&ctx, task.checkpoint);
                if let Some((def, event)) = task.fork_cond {
                    solver.add_event(event);
                    solver.add(def);
                }
                let Run::Finished(value) = run_loop(
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
                )
                .unwrap() else {
                    panic!("访存夹具必须正常结束")
                };
                paths += 1;
                let point = checkpoint(&mut solver);
                for direction in [false, true] {
                    for delta in [0, 1] {
                        let mut verify = Solver::from_checkpoint(&ctx, point.clone());
                        verify.assert(Eq(Box::new(Var(branch)), Box::new(Bool(direction))));
                        verify.assert(Eq(Box::new(Var(offset)), Box::new(bits64(delta, 1))));
                        if verify.check_sat(info()).is_unsat().unwrap() {
                            continue;
                        }
                        coverage += 1;
                        let mut model = Model::new(&mut verify);
                        model.set_complete_model(true);
                        let bits = |value: &Val<B64>, model: &mut Model<'_, B64>| match model.get_val(value).unwrap() {
                            Val::Bits(bits) => bits.lower_u64(),
                            value => panic!("需要具体位向量，得到 {value:?}"),
                        };
                        let mut writes = Vec::new();
                        for (event, guard) in solver.trace().events_with_guards_rev() {
                            let Event::WriteMem { address, data, bytes, write_kind, opts, .. } = event else {
                                continue;
                            };
                            if let Some(guard) = guard {
                                if model.get_exp(guard).unwrap().unwrap_exp() == Bool(false) {
                                    continue;
                                }
                            }
                            assert_eq!(*write_kind, Val::Unit);
                            assert!(!opts.is_exclusive());
                            writes.push((bits(address, &mut model), *bytes, bits(data, &mut model)));
                        }
                        writes.reverse();
                        let expected = match (case, direction) {
                            (0, false) => vec![(BASE, 1, 0xA1)],
                            (0, true) => vec![(BASE, 1, 0xB2)],
                            (1, false) => vec![(BASE + 1, 1, 0xA1)],
                            (1, true) => vec![(BASE, 1, 0xA1)],
                            (2, false) => vec![(BASE + 1, 1, 0xB2), (BASE, 1, 0xA1)],
                            (2, true) => vec![(BASE, 1, 0xA1), (BASE + 1, 1, 0xB2)],
                            (3, false) => vec![(BASE, 2, 0xB2A1)],
                            (3, true) => vec![(BASE, 1, 0xA1)],
                            (_, false) => vec![(BASE, 2, 0xB2A1), (BASE + delta, 2, 0xD4C3)],
                            (_, true) => vec![],
                        };
                        assert_eq!(writes, expected);
                        let mut initial = [0; 3];
                        for (address, width, data) in expected {
                            for i in 0..width {
                                initial[(address - BASE) as usize + i as usize] = (data >> (8 * i)) as u8;
                            }
                        }
                        assert_eq!(
                            bits(&value, &mut model),
                            u64::from(u32::from_le_bytes([initial[0], initial[1], initial[2], 0]))
                        );
                    }
                }
            }
            assert_eq!(coverage, 4);
            assert_eq!(paths, if strategy.is_some() { 1 } else { 2 }, "场景 {case}，策略 {strategy:?}");
        }
    }
}

#[derive(Clone)]
struct CountingDevice(Arc<AtomicUsize>);

impl crate::memory::CustomRegion<B64> for CountingDevice {
    fn read(&self, _: Val<B64>, _: u64, _: u32, _: &mut Solver<B64>, _: bool) -> Result<Val<B64>, ExecError> {
        panic!("此夹具只检查设备写入")
    }

    fn write(
        &mut self,
        _: Val<B64>,
        _: u64,
        _: Val<B64>,
        _: &mut Solver<B64>,
        _: Option<Val<B64>>,
    ) -> Result<Val<B64>, ExecError> {
        self.0.fetch_add(1, Ordering::Relaxed);
        Ok(Val::Bool(false))
    }

    fn initial_value(&self, _: u64, _: u32) -> Option<B64> {
        None
    }

    fn region_name(&self) -> &'static str {
        "fixture device"
    }

    fn clone_dyn(&self) -> Box<dyn Send + Sync + crate::memory::CustomRegion<B64>> {
        Box::new(self.clone())
    }
}

#[test]
fn region_memory_write_barriers_roll_back_before_device_or_exclusive_attempt() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let shared = empty_shared_state();
    let plain = TaskState::new();
    let dst = test_name(2910);
    let guard_id = test_name(2911);
    let concrete = |n| Exp::Bits(B64::new(n, 64));
    for exclusive in [false, true] {
        let mut state = TaskState::new()
            .with_execution_limits(ExecutionLimits::default().with_path_merging(true).with_region_global_state(true));
        state.speculation_stats = speculation::SpeculationStats::new(true);
        let attempts = Arc::new(AtomicUsize::new(0));
        let mut solver = Solver::<B64>::new(&context);
        let cond = solver.declare_const(smtlib::Ty::Bool, info());
        let blocked = if exclusive {
            Instr::PrimopVariadic(
                Loc::Id(dst),
                primop::variadic_primops()["platform_write_mem_exclusive"],
                vec![Exp::Unit, Exp::I128(64), concrete(BASE + 4), Exp::I128(1), Exp::Bits(B64::new(7, 8))],
                info(),
            )
        } else {
            store(dst, concrete(BASE + 8), 1, 0xFF)
        };
        let mut frame = make_frame(vec![
            Instr::Jump(Exp::Id(guard_id), 2, info()),
            Instr::Goto(4),
            store(dst, concrete(BASE), 1, 0xAA),
            blocked,
            Instr::Copy(Loc::Id(RETURN), Exp::Id(dst), info()),
            Instr::End,
        ]);
        frame.vars_mut().insert(guard_id, UVal::Init(Val::Symbolic(cond)));
        frame.vars_mut().insert(dst, UVal::Init(Val::Bool(false)));
        frame
            .memory_mut()
            .add_region(crate::memory::Region::Custom(BASE + 8..BASE + 16, Box::new(CountingDevice(attempts.clone()))));
        frame.memory_mut().add_concrete_region(BASE..BASE + 8, HashMap::from([(BASE + 4, 0x5A)]));
        crate::memory::install_seq_memory(frame.memory_mut(), 64, &mut solver, false);
        let version = frame.memory().ram_version().unwrap();
        let queue = Worker::new_lifo();
        let sink = SingleForkSink { queue: &queue };
        let result = region_merge::try_region(
            cond,
            2,
            0,
            TaskId::fresh(),
            &mut Fraction::one(),
            PathTimeout::unlimited(),
            None,
            &sink,
            &mut frame,
            &state,
            &shared,
            &mut solver,
            info(),
        );
        assert!(matches!(result, Ok(region_merge::RegionResult::Rejected)));
        assert_eq!(state.speculation_stats().reject_json()["reason_counts"]["state_effect"].as_u64(), Some(1));
        assert_eq!(solver.transaction_depth(), 0);
        assert_eq!(attempts.load(Ordering::Relaxed), 0);
        assert_eq!(frame.memory().ram_version(), Some(version));
        assert!(solver.trace().to_vec().iter().all(|event| !event.is_memory_write()));
        assert!(queue.is_empty());

        let mut frame = frame;
        solver.assert(smtlib::Exp::Var(cond));
        let mut fraction = Fraction::one();
        let result = run_loop(
            0,
            TaskId::fresh(),
            &mut fraction,
            PathTimeout::unlimited(),
            None,
            &sink,
            &mut frame,
            &plain,
            &shared,
            &mut solver,
        )
        .unwrap();
        let Run::Finished(result) = result else { panic!("屏障外的普通执行应完成") };
        assert_eq!(attempts.load(Ordering::Relaxed), usize::from(!exclusive));
        assert_eq!(
            solver.trace().to_vec().iter().filter(|event| event.is_memory_write()).count(),
            1 + usize::from(exclusive)
        );
        if exclusive {
            let result = smt_value(&result, info()).unwrap();
            solver.assert(smtlib::Exp::Not(Box::new(result)));
            let value = frame
                .memory()
                .read(
                    Val::Unit,
                    Val::Bits(B64::new(BASE + 4, 64)),
                    Val::I128(1),
                    &mut solver,
                    false,
                    Default::default(),
                )
                .unwrap();
            let differs = smtlib::Exp::Neq(Box::new(smt_value(&value, info()).unwrap()), Box::new(bits64(0x5A, 8)));
            assert!(solver.check_sat(info()).is_sat().unwrap());
            assert!(solver.check_sat_with(&differs, info()).is_unsat().unwrap());
        }
    }
}
