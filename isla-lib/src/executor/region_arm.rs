//! 区域臂跨 Context 移交的纯数据标识。
//!
//! 跨线程交付使用稳定的区域和逻辑臂次序，不能以
//! worker、到达时间或全局计数决定符号编号。
use super::{Fraction, Frame, PathTimeout, SourceLoc, TaskId, TaskState};
use crate::bitvector::BV;
use crate::error::ExecError;
use crate::executor::frame::LocalFrame;
use crate::smt::{ArmSuffixEvent, Checkpoint, DeferredArmAssertions, Event, Solver, Sym, SymRemap};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};

pub(super) struct ThreadSlot<'a> {
    pub(super) tid: usize,
    pub(super) release: Option<Box<dyn FnOnce() + Send + 'a>>,
}

impl Drop for ThreadSlot<'_> {
    fn drop(&mut self) {
        self.release.take().unwrap()();
    }
}

pub(super) struct Cancellation {
    flag: Arc<AtomicBool>,
    parent: Option<Arc<Self>>,
}

impl Cancellation {
    pub(super) fn new(flag: Arc<AtomicBool>, parent: Option<Arc<Self>>) -> Arc<Self> {
        Arc::new(Self { flag, parent })
    }

    pub(super) fn is_cancelled(&self) -> bool {
        std::iter::successors(Some(self), |node| node.parent.as_deref()).any(|node| node.flag.load(Ordering::Acquire))
    }
}

pub(super) trait ArmThreads: Sync {
    fn reserve(&self) -> Option<ThreadSlot<'_>>;
}

#[derive(Clone, Copy)]
pub(super) struct Scheduler<'a, 'ir, B: BV> {
    pub threads: &'a dyn ArmThreads,
    pub queue: &'a ArmQueue<'ir, B>,
}

pub(super) struct ArmJob<'ir, B: BV> {
    pub checkpoint: Checkpoint<B>,
    pub options: (crate::smt::SolverOptions, bool),
    pub base: LocalFrame<'ir, B>,
    pub pc: usize,
    pub guard: crate::smt::smtlib::Exp<Sym>,
    pub task: TaskId,
    pub fraction: Fraction,
    pub timeout: PathTimeout,
    pub info: SourceLoc,
}

pub(super) type Delivery<'ir, B> = Option<RemoteArrival<'ir, B>>;
pub(super) type ArmCell<'ir, B> = JoinCell<Delivery<'ir, B>>;
pub(super) struct QueuedArm<'ir, B: BV> {
    pub job: ArmJob<'ir, B>,
    pub cell: Arc<ArmCell<'ir, B>>,
    pub failure: ExecError,
    pub parent_attempt: Option<usize>,
}

/// 普通任务独占队列。只有等候子臂的线程才借出自己的执行名额。
pub(super) struct ArmQueue<'ir, B: BV> {
    inner: Mutex<(usize, std::collections::VecDeque<QueuedArm<'ir, B>>)>,
    changed: Condvar,
}

impl<'ir, B: BV> ArmQueue<'ir, B> {
    pub(super) fn new() -> Self {
        Self { inner: Mutex::new((0, Default::default())), changed: Condvar::new() }
    }

    pub(super) fn has_helper(&self) -> bool {
        let queue = self.inner.lock().unwrap();
        queue.0 > queue.1.len()
    }

    pub(super) fn enqueue(&self, work: QueuedArm<'ir, B>) {
        self.inner.lock().unwrap().1.push_back(work);
        self.changed.notify_one();
    }

    pub(super) fn retire(&self, cell: &ArmCell<'ir, B>) {
        self.inner.lock().unwrap().1.retain(|work| !std::ptr::eq(work.cell.as_ref(), cell));
        self.changed.notify_all();
    }

    pub(super) fn wake(&self) {
        let _lock = self.inner.lock().unwrap();
        self.changed.notify_all();
    }

    pub(super) fn help_until(
        &self,
        cell: &ArmCell<'ir, B>,
        mut execute: impl FnMut(QueuedArm<'ir, B>),
        state: &TaskState<B>,
    ) {
        let mut queue = self.inner.lock().unwrap();
        while cell.state() == ArmJobState::Claimed {
            if let Some(work) = queue.1.pop_front() {
                drop(queue);
                execute(work);
                queue = self.inner.lock().unwrap();
            } else {
                queue.0 += 1;
                #[cfg(test)]
                observe(state, "idle_helper").expect("等待名额观察点不可失败");
                let _ = state;
                queue = self.changed.wait(queue).unwrap();
                queue.0 -= 1;
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ArmJobState {
    Queued,
    Reclaimed,
    Claimed,
    Arrived,
    Cancelled,
}

/// 状态与返回值共用锁，唤醒前先发布结果，等待者始终在锁内检查谓词。
pub(crate) struct JoinCell<T> {
    inner: Mutex<(ArmJobState, Option<Result<T, ExecError>>)>,
    changed: Condvar,
    pub(super) cancelled: Arc<AtomicBool>,
}

impl<T> JoinCell<T> {
    pub(crate) fn new() -> Self {
        Self {
            inner: Mutex::new((ArmJobState::Queued, None)),
            changed: Condvar::new(),
            cancelled: Arc::new(AtomicBool::new(false)),
        }
    }

    #[cfg(test)]
    pub(super) fn observe_id<B>(&self, state: &TaskState<B>, point: &str) -> Result<(), ExecError> {
        if let Some(hook) = &state.arm_test_hook {
            hook(&format!("{point}/{self:p}"))?;
        }
        Ok(())
    }

    pub(crate) fn try_claim(&self) -> bool {
        self.claim_as(ArmJobState::Claimed)
    }

    pub(super) fn try_reclaim(&self) -> bool {
        self.claim_as(ArmJobState::Reclaimed)
    }

    fn claim_as(&self, state: ArmJobState) -> bool {
        let mut slot = self.inner.lock().unwrap();
        if slot.0 != ArmJobState::Queued {
            return false;
        }
        slot.0 = state;
        true
    }

    pub(crate) fn deliver(&self, result: Result<T, ExecError>) {
        let mut slot = self.inner.lock().unwrap();
        if self.cancelled.load(Ordering::Acquire) {
            return;
        }
        assert_eq!(slot.0, ArmJobState::Claimed);
        slot.0 = if result.is_ok() { ArmJobState::Arrived } else { ArmJobState::Cancelled };
        slot.1 = Some(result);
        self.changed.notify_all();
    }

    pub(super) fn cancel(&self, error: ExecError) {
        let mut slot = self.inner.lock().unwrap();
        if matches!(slot.0, ArmJobState::Queued | ArmJobState::Claimed) {
            self.cancelled.store(true, Ordering::Release);
            *slot = (ArmJobState::Cancelled, Some(Err(error)));
            self.changed.notify_all();
        }
    }

    pub(crate) fn state(&self) -> ArmJobState {
        self.inner.lock().unwrap().0
    }

    pub(super) fn take(&self) -> Result<T, ExecError> {
        let slot = self.inner.lock().unwrap();
        self.changed
            .wait_while(slot, |slot| slot.0 == ArmJobState::Claimed)
            .unwrap()
            .1
            .take()
            .expect("远端臂只能交付一次")
    }
}

pub(super) fn transferable_entry<B>(frame: &LocalFrame<B>) -> bool {
    frame.region_arrivals.is_empty()
        && frame.arm_error.is_none()
        && frame.pending_retry_operand.is_none()
        && frame.local_state.expression_retry_operands.is_none()
}

/// 仅用于测试确定认领和到达次序；生产诊断记录实际的领取、取回及导入。
#[inline]
pub(super) fn observe<B>(state: &TaskState<B>, point: &'static str) -> Result<(), ExecError> {
    #[cfg(test)]
    if let Some(hook) = &state.arm_test_hook {
        hook(point)?;
    }
    let _ = state;
    if matches!(point, "worker_claimed" | "reclaimed" | "imported" | "failed" | "serial_retry" | "no_slot")
        && crate::config::RegionOptions::current().progress
    {
        eprintln!("[REGION_ARM] {point}");
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct RegionId(Vec<usize>);

impl RegionId {
    pub(crate) fn new(path: Vec<usize>) -> Self {
        Self(path)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ArmPath(Vec<usize>);

impl ArmPath {
    pub(crate) fn new(path: Vec<usize>) -> Self {
        Self(path)
    }
}

/// 在 A 已占用的编号之后，为远端臂的新符号分配稳定的连续范围。
///
/// 入口前缀符号不在输入列表中；它们必须保持原编号。每个逻辑臂内的符号按其
/// 本地创建次序排序，臂之间按 `(RegionId, ArmPath)` 排序。
pub(crate) fn remap_region_arm_symbols(first_target: Sym, arms: Vec<(RegionId, ArmPath, Vec<Sym>)>) -> SymRemap {
    SymRemap::for_region_arms(first_target, arms)
}

/// 在根事务创建前取得远端 B 臂的重放入口。
///
/// 这个边界故意单独命名：阶段 3 的 `RegionArmJob` 只能保存它，不能保存活动
/// 事务的 Solver 状态。
pub(crate) fn capture_arm_entry_checkpoint<B: BV>(solver: &mut Solver<B>) -> Checkpoint<B> {
    assert_eq!(solver.transaction_depth(), 0, "远端臂入口必须位于根事务之前");
    solver.arm_entry_checkpoint()
}

/// B worker 交付给固定 A 汇合者的纯 Rust 数据。它不携带 Z3 AST、Solver 或 Context。
pub(super) struct ErrorLeaf<'ir, B> {
    pub task: TaskId,
    pub fraction: Fraction,
    pub frame: Frame<'ir, B>,
    pub checkpoint: Checkpoint<B>,
    pub fork: (crate::smt::smtlib::Def, Event<B>),
}

pub(crate) struct RemoteArrival<'ir, B> {
    pub(super) errors: Vec<ErrorLeaf<'ir, B>>,
    pub(super) dead: bool,
    pub(crate) region: RegionId,
    pub(crate) arm: ArmPath,
    pub(crate) symbols: std::ops::Range<u32>,
    pub(crate) suffix: Vec<ArmSuffixEvent<B>>,
    pub(crate) deferred: Option<DeferredArmAssertions>,
    pub(crate) frame: LocalFrame<'ir, B>,
}

impl<'ir, B: BV> RemoteArrival<'ir, B> {
    pub(crate) fn remap_symbols(&mut self, remap: &SymRemap, history_prefix: usize) {
        assert!(
            self.suffix.iter().all(|item| !matches!(item.event, Event::WriteMem { .. })),
            "首版远端臂不得移交已写入且不可重命名的 Memory"
        );
        for item in &mut self.suffix {
            item.guard = item.guard.as_ref().map(|guard| remap.exp(guard));
            item.event = remap.event(&item.event);
        }
        if let Some(deferred) = &mut self.deferred {
            deferred.remap_symbols(remap);
        }
        self.frame.remap_symbols(remap, history_prefix);
    }
}
