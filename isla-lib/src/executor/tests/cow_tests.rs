use super::*;

#[test]
fn 恢复帧执行无修改指令后直到实际写入才分离局部状态() {
    for stale_retry in [false, true] {
        for write_register in [false, true] {
            let shared = empty_shared_state();
            let mut parent = make_frame(vec![Instr::Goto(1)]);
            let name = test_name(42);
            parent.vars_mut().insert(name, UVal::Init(Val::Bool(false)));
            parent.regs_mut().insert(name, false, UVal::Init(Val::Bool(false)));
            if stale_retry {
                parent.pending_retry_operand = Some((99, Val::Unit));
            }
            let frozen = freeze_frame(&parent);
            let mut resumed = unfreeze_frame(&frozen);
            let state = TaskState::new();
            let queue = Worker::new_lifo();
            let mut fraction = Fraction::one();
            let ctx = Context::new(Config::new());
            let mut solver = Solver::new(&ctx);

            let result = run_loop(
                0,
                TaskId::from_usize(0),
                &mut fraction,
                PathTimeout::unlimited(),
                None,
                &SingleForkSink { queue: &queue },
                &mut resumed,
                &state,
                &shared,
                &mut solver,
            );

            assert!(matches!(result, Ok(Run::Finished(Val::Unit))));
            assert!(Arc::ptr_eq(&frozen.local_state, &resumed.local_state), "空缓存清理不得克隆局部状态");
            assert!(resumed.pending_retry_operand.is_none());
            if write_register {
                resumed.regs_mut().insert(name, false, UVal::Init(Val::Bool(true)));
                assert_eq!(resumed.regs().get_last_if_initialized(name), Some(&Val::Bool(true)));
            } else {
                resumed.vars_mut().insert(name, UVal::Init(Val::Bool(true)));
                assert!(matches!(resumed.vars().get(&name), Some(UVal::Init(Val::Bool(true)))));
            }
            assert!(!Arc::ptr_eq(&frozen.local_state, &resumed.local_state));
            assert!(matches!(frozen.local_state.vars.get(&name), Some(UVal::Init(Val::Bool(false)))));
            assert_eq!(frozen.local_state.regs.get_last_if_initialized(name), Some(&Val::Bool(false)));
        }
    }
}

#[test]
fn 恢复帧清理非空表达式缓存时分离且保留冻结快照() {
    let shared = empty_shared_state();
    let mut parent = make_frame(vec![Instr::Goto(1)]);
    Arc::make_mut(&mut parent.local_state).expression_values.insert(42, Val::Bool(true));
    Arc::make_mut(&mut parent.local_state).expression_retry_operands = Some(vec![Val::Bool(false)]);
    let frozen = freeze_frame(&parent);
    let mut resumed = unfreeze_frame(&frozen);
    let state = TaskState::new();
    let queue = Worker::new_lifo();
    let mut fraction = Fraction::one();
    let ctx = Context::new(Config::new());
    let mut solver = Solver::new(&ctx);

    let result = run_loop(
        0,
        TaskId::from_usize(0),
        &mut fraction,
        PathTimeout::unlimited(),
        None,
        &SingleForkSink { queue: &queue },
        &mut resumed,
        &state,
        &shared,
        &mut solver,
    );

    assert!(matches!(result, Ok(Run::Finished(Val::Unit))));
    assert!(!Arc::ptr_eq(&frozen.local_state, &resumed.local_state));
    assert!(resumed.local_state.expression_values.is_empty());
    assert!(resumed.local_state.expression_retry_operands.is_none());
    assert_eq!(frozen.local_state.expression_values.get(&42), Some(&Val::Bool(true)));
    assert_eq!(frozen.local_state.expression_retry_operands, Some(vec![Val::Bool(false)]));
}
