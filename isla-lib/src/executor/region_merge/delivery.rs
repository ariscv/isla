//! 区域认证完成后的交付。子层结果属于父臂，普通执行才能生成任务检查点。
use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn finish<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
    outcome: &RegionResult,
    frame: &mut LocalFrame<'ir, B>,
    record_start: usize,
    errors: &mut ArmErrorSink<'ir, 'task, B>,
    task_id: TaskId,
    fraction: &mut Fraction,
    stop: Option<&'task StopConditions>,
    sink: &S,
    state: &'task TaskState<B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) {
    let cut = matches!(outcome, RegionResult::VerifiedPrefix(_));
    let dead_cut = cut && frame.region_arrivals.is_empty();
    let grouped = !dead_cut
        && matches!(
            outcome,
            RegionResult::GuardedExits | RegionResult::Separate { .. } | RegionResult::VerifiedPrefix(_)
        );
    let records = (cut && diagnostics::enabled()).then(|| prefix_commit::record_count(frame, record_start));
    if dead_cut {
        solver.commit_dead_transaction();
    } else if !grouped {
        solver.commit_transaction();
    }
    let pending = std::mem::take(errors.tasks.get_mut().unwrap());
    if frame.region_execution.is_some() {
        for task in pending {
            sink.submit_consumer_error(task);
        }
    } else {
        publish_arm_errors(frame, pending, solver, fraction, sink, shared);
    }
    if grouped {
        publish_join_groups(frame, record_start, cut, task_id, fraction, stop, sink, state, shared, solver, info);
    } else if frame.region_execution.is_none() && !dead_cut {
        publish_committed_records(frame, record_start, task_id, shared, solver);
    }
    if let (RegionResult::VerifiedPrefix(error), Some(records)) = (outcome, records) {
        diagnostics::record_prefix_commit(error, records, &shared.symtab);
    }
}

/// 有父事务时保留逻辑臂，没有父事务时才投影为普通任务。
#[allow(clippy::too_many_arguments)]
fn publish_join_groups<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
    frame: &mut LocalFrame<'ir, B>,
    record_start: usize,
    verified_prefix: bool,
    task_id: TaskId,
    fraction: &mut Fraction,
    stop: Option<&'task StopConditions>,
    sink: &S,
    state: &'task TaskState<B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) {
    use smtlib::Exp::Var;
    let groups = &frame.region_arrivals;
    let count = groups.len();
    assert!(count > 0);
    let owners: Vec<_> = groups.iter().map(|group| group.region_arm.expect("每个汇合组必须拥有逻辑臂")).collect();
    if frame.region_execution.is_some() {
        assert!(solver.commit_region_groups(&owners).is_none(), "父区域必须持有事务");
        return;
    }
    let groups = std::mem::take(&mut frame.region_arrivals);
    let selectors: Vec<_> = groups
        .iter()
        .map(|group| {
            let guard = group.local_state.speculative_access.as_ref().unwrap().guard.as_ref().unwrap();
            match guard {
                Var(sym) => *sym,
                _ => solver.define_const(guard.clone(), info),
            }
        })
        .collect();
    let effects = solver.commit_region_groups(&owners).expect("普通任务的检查点需要已发布的组");
    let fork_bits = usize::BITS - (count - 1).leading_zeros();
    for (index, ((mut group, effects), selector)) in groups.into_iter().zip(effects).zip(selectors).enumerate() {
        let guard = Var(selector);
        group.region_arm = None;
        let fork = (count > 1).then(|| {
            let limits = cost::make_mut(&mut group.execution_limit_state);
            let id = limits.record_fork();
            for bit in (0..fork_bits).rev() {
                limits.advance_path_signature(index & (1 << bit) != 0);
            }
            Event::Fork(id, selector, u32::try_from(index).expect("汇合组编号溢出"), info)
        });
        solver.select_region_group(effects);
        publish_register_writes(&mut group, shared, solver);
        if verified_prefix {
            // 前缀没有到达外层汇合点。只发布真正完成的子记录，访存守卫随迹发布。
            publish_region_records(&mut group, record_start, task_id, shared, solver);
        } else {
            publish_committed_records(&mut group, record_start, task_id, shared, solver);
        }
        group.capture_path_smt_stats();
        if index + 1 == count {
            if let Some(fork) = fork {
                solver.add_event(fork);
            }
            solver.assert(guard.clone());
            super::btrace_push_branch_condition!(group, guard);
            *frame = group;
        } else {
            let frozen = super::trace_fork_frame_with_branch_condition!(&group, group.pc, guard.clone());
            fraction.halve();
            sink.submit(Task {
                id: task_id,
                fraction: fraction.clone(),
                frame: frozen,
                checkpoint: solver.region_group_checkpoint(),
                fork_cond: Some((smtlib::Def::Assert(guard), fork.expect("多个汇合组必须有分叉事件"))),
                state,
                stop_conditions: stop,
            });
        }
    }
}
