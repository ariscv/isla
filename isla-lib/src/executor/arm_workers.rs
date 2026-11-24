//! 普通任务与远端臂共用固定执行线程及原有的全局名额。
use super::arm_cost::ArmCpu;
use super::*;
use crate::smt::ArmReplay;
use region_merge::parallel_arms::{arm_context, execute_job};
use std::panic::{catch_unwind, AssertUnwindSafe};

// 退还名额后只短暂保留入口。繁忙的线程也定期重建 Context，释放 Z3 的原生表和作用域。
const CACHE_IDLE: Duration = Duration::from_secs(1);
const CACHE_JOBS: usize = 128;

pub(super) struct WorkerArm<'ir, 'task, B: BV> {
    pub work: region_arm::QueuedArm<'ir, B>,
    pub state: &'task TaskState<B>,
    pub stop: Option<&'task StopConditions>,
    pub queue: Arc<region_arm::ArmQueue<'ir, B>>,
}

pub(super) enum WorkerJob<'ir, 'task, B: BV> {
    Task(Task<'ir, 'task, B>),
    Arm(WorkerArm<'ir, 'task, B>),
}

struct WorkerPlace<'ir, 'task, B: BV> {
    idle: bool,
    affinity: Option<(TaskId, Checkpoint<B>)>,
    assigned: Option<WorkerJob<'ir, 'task, B>>,
}

struct WorkerSlots<'ir, 'task, B: BV> {
    closed: bool,
    pending: VecDeque<WorkerJob<'ir, 'task, B>>,
    places: Vec<WorkerPlace<'ir, 'task, B>>,
}

pub(super) struct WorkerQueue<'ir, 'task, B: BV> {
    inner: Mutex<WorkerSlots<'ir, 'task, B>>,
    ready: Vec<Condvar>,
    pub panic: Mutex<Option<Box<dyn std::any::Any + Send>>>,
}

impl<'ir, 'task, B: BV> WorkerQueue<'ir, 'task, B> {
    pub(super) fn new(count: usize) -> Self {
        Self {
            inner: Mutex::new(WorkerSlots {
                closed: false,
                pending: VecDeque::new(),
                places: (0..count).map(|_| WorkerPlace { idle: true, affinity: None, assigned: None }).collect(),
            }),
            ready: (0..count).map(|_| Condvar::new()).collect(),
            panic: Mutex::new(None),
        }
    }

    pub(super) fn push(&self, job: WorkerJob<'ir, 'task, B>) {
        let mut state = self.inner.lock().unwrap();
        assert!(!state.closed, "执行线程池关闭后不得派发任务");
        let chosen = state
            .places
            .iter()
            .enumerate()
            .filter(|(_, worker)| worker.idle)
            .max_by_key(|(index, worker)| {
                let score = match (&job, &worker.affinity) {
                    (WorkerJob::Arm(arm), Some((task, checkpoint))) if *task == arm.work.job.task => {
                        (2, checkpoint.shared_arm_depth(&arm.work.job.checkpoint))
                    }
                    // 普通任务和无公共前缀的臂优先使用尚未缓存入口的线程。
                    _ => (usize::from(worker.affinity.is_none()), 0),
                };
                (score, std::cmp::Reverse(*index))
            })
            .map(|(index, _)| index);
        if let Some(index) = chosen {
            let worker = &mut state.places[index];
            assert!(worker.assigned.is_none());
            worker.assigned = Some(job);
            worker.idle = false;
            self.ready[index].notify_one();
        } else {
            state.pending.push_back(job);
        }
    }

    fn advertise(&self, tid: usize, affinity: Option<(TaskId, Checkpoint<B>)>) {
        let mut state = self.inner.lock().unwrap();
        let worker = &mut state.places[tid];
        assert!(!worker.idle && worker.assigned.is_none());
        worker.affinity = affinity;
        worker.idle = true;
    }

    fn take(&self, tid: usize, cached: bool) -> Option<WorkerJob<'ir, 'task, B>> {
        let ready = &self.ready[tid];
        let no_work = |state: &mut WorkerSlots<'ir, 'task, B>| {
            !state.closed && state.pending.is_empty() && state.places[tid].assigned.is_none()
        };
        let state = self.inner.lock().unwrap();
        let mut state = if cached {
            let (mut state, wait) = ready.wait_timeout_while(state, CACHE_IDLE, no_work).unwrap();
            if wait.timed_out() && no_work(&mut state) {
                state.places[tid].affinity = None;
                return None;
            }
            state
        } else {
            ready.wait_while(state, no_work).unwrap()
        };
        let worker = &mut state.places[tid];
        let assigned = worker.assigned.take();
        let affinity = worker.affinity.take();
        worker.idle = false;
        if let Some(job) = assigned {
            return Some(job);
        }
        if let Some((task, checkpoint)) = affinity {
            let best = state
                .pending
                .iter()
                .enumerate()
                .filter_map(|(index, job)| {
                    let WorkerJob::Arm(arm) = job else { return None };
                    (arm.work.job.task == task)
                        .then(|| (checkpoint.shared_arm_depth(&arm.work.job.checkpoint), std::cmp::Reverse(index)))
                })
                .max();
            if let Some((_, std::cmp::Reverse(index))) = best {
                return state.pending.remove(index);
            }
        }
        state.pending.pop_front()
    }

    pub(super) fn close(&self) {
        let mut state = self.inner.lock().unwrap();
        assert!(state.pending.is_empty() && state.places.iter().all(|worker| worker.assigned.is_none()));
        state.closed = true;
        for ready in &self.ready {
            ready.notify_all();
        }
    }

    fn record_panic(&self, result: std::thread::Result<()>) -> bool {
        if let Err(payload) = result {
            self.panic.lock().unwrap().get_or_insert(payload);
            true
        } else {
            false
        }
    }
}

impl<'ir, 'task, 'collector, B: BV, R: Send + Sync> MultiRuntime<'ir, 'task, 'collector, B, R> {
    pub(super) fn worker_loop<'scope, 'env>(self: &Arc<Self>, scope: &'scope thread::Scope<'scope, 'env>, tid: usize)
    where
        'ir: 'scope,
        'task: 'scope,
        'collector: 'scope,
    {
        let queue = self.workers.as_ref().unwrap();
        let mut next = queue.take(tid, false);
        while let Some(job) = next {
            let mut arm = match job {
                WorkerJob::Arm(arm) => arm,
                WorkerJob::Task(task) => {
                    let result = catch_unwind(AssertUnwindSafe(|| Arc::clone(self).execute_task(scope, tid, task)));
                    queue.record_panic(result);
                    queue.advertise(tid, None);
                    self.on_task_finished(scope);
                    next = queue.take(tid, false);
                    continue;
                }
            };
            next = {
                let options = arm.work.job.options;
                let startup = arm.work.job.cost.as_ref().map(|_| ArmCpu::start());
                let ctx = arm_context(options);
                let mut replay = ArmReplay::new(&ctx);
                let mut startup = startup.map(|timer| timer.elapsed());
                let mut leased_jobs = 0;
                loop {
                    let task = arm.work.job.task;
                    let checkpoint = arm.work.job.checkpoint.clone();
                    let cell = Arc::clone(&arm.work.cell);
                    let sink = MultiForkSink {
                        runtime: Arc::clone(self),
                        arms: Some(arm.queue),
                        state: arm.state,
                        stop: arm.stop,
                        scope,
                    };
                    let result = catch_unwind(AssertUnwindSafe(|| {
                        execute_job(
                            arm.work,
                            &mut replay,
                            startup.take().unwrap_or_default(),
                            tid,
                            sink.arm_scheduler(),
                            arm.state,
                            arm.stop,
                            self.shared_state,
                        );
                    }));
                    let failed = queue.record_panic(result);
                    leased_jobs += 1;
                    let recycle = leased_jobs == CACHE_JOBS;
                    queue.advertise(tid, (!failed && !recycle).then_some((task, checkpoint)));
                    self.active_threads.fetch_sub(1, Ordering::AcqRel);
                    self.try_refill_threads(scope);
                    cell.worker_finished();
                    if failed || recycle {
                        break None;
                    }
                    match queue.take(tid, true) {
                        Some(WorkerJob::Arm(job)) if job.work.job.options == options => arm = job,
                        other => break other,
                    }
                }
            };
            if next.is_none() {
                next = queue.take(tid, false);
            }
        }
    }
}
