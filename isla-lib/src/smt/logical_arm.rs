//! 逻辑臂跨越多个原生作用域，拥有区域事务内的事件及周期贡献。
use super::*;
use std::num::NonZeroUsize;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct LogicalArm(NonZeroUsize);

#[derive(Clone, Copy, Default)]
struct EffectOwner {
    arm: Option<LogicalArm>,
    cycle: bool,
}

#[derive(Default)]
pub(super) struct LogicalArms {
    parents: Vec<Option<LogicalArm>>,
    active: Option<LogicalArm>,
    owners: Vec<EffectOwner>,
}

impl LogicalArms {
    pub(super) fn record_event(&mut self) {
        if !self.parents.is_empty() {
            self.owners.push(EffectOwner { arm: self.active, cycle: false });
        }
    }

    pub(super) fn mark_cycle(&mut self) {
        if !self.parents.is_empty() {
            self.owners.last_mut().expect("周期计数必须有缓冲事件").cycle = true;
        }
    }

    pub(super) fn truncate(&mut self, len: usize) {
        self.owners.truncate(len);
    }

    pub(super) fn record_global_event(&mut self) {
        if !self.parents.is_empty() {
            self.owners.push(EffectOwner::default());
        }
    }

    pub(super) fn clear(&mut self) {
        assert!(self.active.is_none(), "根事务必须在全部逻辑臂停止后关闭");
        self.parents.clear();
        self.owners.clear();
    }

    pub(super) fn heap_bytes(&self) -> usize {
        self.parents.capacity() * std::mem::size_of::<Option<LogicalArm>>()
            + self.owners.capacity() * std::mem::size_of::<EffectOwner>()
    }
}

impl<B: BV> Solver<'_, B> {
    pub(crate) fn current_logical_arm(&self) -> Option<LogicalArm> {
        self.logical_arms.active
    }

    pub(crate) fn new_logical_arm(&mut self, parent: Option<LogicalArm>) -> LogicalArm {
        assert!(!self.savepoints.is_empty(), "逻辑臂必须属于区域事务");
        assert!(parent.is_none_or(|id| id.0.get() <= self.logical_arms.parents.len()), "父臂必须已分配");
        if self.logical_arms.parents.is_empty() {
            self.logical_arms.owners.resize(self.transaction_events.len(), EffectOwner::default());
        }
        self.logical_arms.parents.push(parent);
        LogicalArm(NonZeroUsize::new(self.logical_arms.parents.len()).unwrap())
    }

    pub(crate) fn with_logical_arm<T>(&mut self, arm: LogicalArm, f: impl FnOnce(&mut Self) -> T) -> T {
        assert!(arm.0.get() <= self.logical_arms.parents.len(), "只能恢复已分配的逻辑臂");
        let prior = self.logical_arms.active.replace(arm);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(self)));
        assert_eq!(std::mem::replace(&mut self.logical_arms.active, prior), Some(arm));
        match result {
            Ok(value) => value,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }

    /// 调用方已确定整条逻辑臂的正常出口不可达。只撤去该臂及后代的事件。
    /// 已提交断言受完整守卫保护；保留它们及定义，以供冻结的义务和其它存活记录使用。
    pub(crate) fn discard_logical_arm_effects(&mut self, arm: LogicalArm) {
        assert!(!self.savepoints.is_empty(), "死臂必须在根提交前撤销");
        let journal = &self.logical_arms;
        assert_eq!(journal.owners.len(), self.transaction_events.len(), "事件归属必须对齐");
        assert_eq!(self.transaction_event_guards.len(), self.transaction_events.len(), "事件条件必须对齐");
        let owned_by_arm = |mut owner: Option<LogicalArm>| {
            while let Some(id) = owner {
                if id == arm {
                    return true;
                }
                owner = journal.parents[id.0.get() - 1];
            }
            false
        };
        assert!(!owned_by_arm(journal.active), "先退出当前原生作用域再丢弃逻辑臂");
        let savepoint = self.savepoints.last().unwrap().events_len;
        let mut removed_cycles = 0;
        let remove: Vec<_> = self
            .transaction_events
            .iter()
            .zip(&journal.owners)
            .enumerate()
            .map(|(index, (event, owner))| {
                let drop = !matches!(event, Event::Smt(..)) && owned_by_arm(owner.arm);
                if drop {
                    assert!(index >= savepoint, "逻辑臂事件不能越过活动保存点");
                    removed_cycles += i128::from(owner.cycle);
                }
                drop
            })
            .collect();
        assert!(removed_cycles <= self.cycles, "撤销的周期不能超过当前计数");
        self.cycles -= removed_cycles;
        let mut drop = remove.iter();
        self.transaction_events.retain(|_| !drop.next().unwrap());
        let mut drop = remove.iter();
        self.transaction_event_guards.retain(|_| !drop.next().unwrap());
        let mut drop = remove.iter();
        self.logical_arms.owners.retain(|_| !drop.next().unwrap());
    }
}
