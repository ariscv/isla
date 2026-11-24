//! 根提交时分摊错误叶查询，按原次序交付求解调用记录与判定。
use super::*;
use crate::smt::{ArmErrorQueries, ArmErrorSmtCall};

pub(super) fn publish<'ir, 'task, B: BV>(
    errors: Vec<Task<'ir, 'task, B>>,
    solver: &Solver<B>,
    scheduler: Option<region_arm::Scheduler<'_, 'ir, B>>,
    mut deliver: impl FnMut(Task<'ir, 'task, B>, Option<SmtResult>),
) {
    let count = errors.len();
    let parallel = scheduler.and_then(|scheduler| {
        let limits = errors.first()?.state.execution_limits.as_ref()?;
        let minimum = limits.parallel.min_error_leaves.get();
        (count >= minimum.max(2)).then_some(())?;
        let config = solver.arm_error_worker_config()?;
        let slots: Vec<_> = (1..count / (minimum / 2).max(1)).map_while(|_| scheduler.threads.reserve()).collect();
        (!slots.is_empty()).then_some((slots, config))
    });
    let Some((slots, config)) = parallel else {
        let mut queries = solver.arm_error_queries(count);
        for task in errors {
            let result = check(&task, solver, queries.as_mut());
            deliver(task, result);
        }
        return;
    };

    // 每个 Context 回放一段连续的错误叶，保留相邻失败点共享的 SMT 前缀。
    let chunks = slots.len() + 1;
    let size = count.div_ceil(chunks);
    let stop = AtomicBool::new(false);
    let purpose = stats::region_progress::query_label();
    std::thread::scope(|scope| {
        let _stop_on_panic = StopOnPanic(&stop);
        let mut tasks = errors.into_iter();
        let local: Vec<_> = tasks.by_ref().take(size).collect();
        let mut workers = Vec::new();
        for slot in slots {
            let leaves: Vec<_> = tasks.by_ref().take(size).collect();
            if leaves.is_empty() {
                break;
            }
            let (config, stop) = (&config, &stop);
            workers.push(scope.spawn(move || {
                let _slot = slot;
                let _stop_on_panic = StopOnPanic(stop);
                let _purpose = stats::region_progress::QueryScope::enter(purpose);
                #[cfg(test)]
                region_arm::observe(leaves[0].state, "certification_worker").expect("认证线程观察点不可失败");
                let context = Context::new(config());
                let solver = Solver::new(&context);
                let mut queries = solver.arm_error_queries(leaves.len().max(2)).unwrap();
                leaves
                    .into_iter()
                    .take_while(|_| !stop.load(Ordering::Acquire))
                    .map(|task| {
                        let (result, call) = ArmErrorSmtCall::capture(|| check(&task, &solver, Some(&mut queries)));
                        (task, result, call)
                    })
                    .collect::<Vec<_>>()
            }));
        }
        assert_eq!(tasks.len(), 0, "分批必须覆盖所有错误叶");
        let worker_count = workers.len();
        let mut queries = solver.arm_error_queries(local.len().max(2)).unwrap();
        for task in local {
            if stop.load(Ordering::Acquire) {
                break;
            }
            let result = check(&task, solver, Some(&mut queries));
            deliver(task, result);
        }
        for worker in workers {
            let results = worker.join().unwrap_or_else(|panic| std::panic::resume_unwind(panic));
            for (task, result, call) in results {
                if let Some(call) = call {
                    call.publish();
                }
                deliver(task, result);
            }
        }
        if crate::config::RegionOptions::current().progress {
            eprintln!(
                "{}",
                serde_json::json!({"kind":"region_error_certification",
                "root_attempt":diagnostics::root_attempt(),"leaves":count,"chunks":1+worker_count})
            );
        }
    });
}

struct StopOnPanic<'a>(&'a AtomicBool);
impl Drop for StopOnPanic<'_> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            self.0.store(true, Ordering::Release);
        }
    }
}

fn check<B: BV>(task: &Task<B>, solver: &Solver<B>, queries: Option<&mut ArmErrorQueries<'_, B>>) -> Option<SmtResult> {
    let _checks = program_control::CheckScope::enter(task.state.stopped_paths.is_some());
    if task.state.stopping() {
        return Some(SmtResult::Error(SmtError::ProgramStopped));
    }
    let Some((_, Event::Fork(_, guard, _, location))) = task.fork_cond.as_ref() else {
        unreachable!("失败前沿必须有分叉元数据")
    };
    #[cfg(test)]
    if let Some(hook) = &task.state.arm_test_hook {
        let Some((_, Event::Fork(_, _, index, _))) = task.fork_cond.as_ref() else { unreachable!() };
        if let Err(error) = hook(&format!("certification_check/{index}")) {
            let ExecError::Smt(cause) = error else { panic!("错误叶注入必须是求解错误") };
            return Some(SmtResult::Error(cause));
        }
    }
    solver.check_arm_error(*guard, &task.checkpoint, *location, queries)
}
