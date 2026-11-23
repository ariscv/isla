//! 逻辑臂跨越多个原生作用域，拥有区域事务内的事件及周期贡献。
mod dependencies;
use super::*;
use std::num::NonZeroUsize;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct LogicalArm(NonZeroUsize);

#[derive(Clone, Copy, Default)]
struct EffectOwner {
    arm: Option<LogicalArm>,
    cycle: bool,
    register_read: Option<NonZeroUsize>,
    discarded: bool,
}

struct Arm {
    parent: Option<LogicalArm>,
    sources: Vec<LogicalArm>,
}

#[derive(Default)]
pub(super) struct LogicalArms {
    arms: Vec<Arm>,
    active: Option<LogicalArm>,
    owners: Vec<EffectOwner>,
}

impl LogicalArms {
    pub(super) fn record_event(&mut self) {
        if !self.arms.is_empty() {
            self.owners.push(EffectOwner { arm: self.active, ..EffectOwner::default() });
        }
    }

    pub(super) fn mark_cycle(&mut self) {
        if !self.arms.is_empty() {
            self.owners.last_mut().expect("周期计数必须有缓冲事件").cycle = true;
        }
    }

    pub(super) fn mark_register_read(&mut self, occurrence: usize) {
        assert!(self.active.is_some(), "区域读取必须属于活动逻辑臂");
        self.owners.last_mut().expect("区域读取必须有缓冲事件").register_read =
            Some(NonZeroUsize::new(occurrence.checked_add(1).expect("读取序号溢出")).unwrap());
    }

    pub(super) fn has_register_reads(&self) -> bool {
        self.owners.iter().any(|owner| owner.register_read.is_some())
    }

    pub(super) fn truncate(&mut self, len: usize) {
        self.owners.truncate(len);
    }

    pub(super) fn record_global_event(&mut self) {
        if !self.arms.is_empty() {
            self.owners.push(EffectOwner::default());
        }
    }

    pub(super) fn clear(&mut self) {
        assert!(self.active.is_none(), "根事务必须在全部逻辑臂停止后关闭");
        self.arms.clear();
        self.owners.clear();
    }

    pub(super) fn heap_bytes(&self) -> usize {
        self.arms.capacity() * std::mem::size_of::<Arm>()
            + self.arms.iter().map(|arm| arm.sources.capacity() * std::mem::size_of::<LogicalArm>()).sum::<usize>()
            + self.owners.capacity() * std::mem::size_of::<EffectOwner>()
    }

    fn reachable(&self, arm: LogicalArm, neighbours: impl Fn(LogicalArm, &Arm, &mut Vec<LogicalArm>)) -> Vec<bool> {
        let mut seen = vec![false; self.arms.len()];
        let mut pending = vec![arm];
        while let Some(id) = pending.pop() {
            let index = id.0.get() - 1;
            if !std::mem::replace(&mut seen[index], true) {
                let arm = &self.arms[index];
                pending.extend(&arm.sources);
                neighbours(id, arm, &mut pending);
            }
        }
        seen
    }

    /// 汇合组可见其成员、成员依赖及共同执行前缀。
    pub(super) fn group_events(
        &self,
        arm: Option<LogicalArm>,
    ) -> impl Iterator<Item = (bool, bool, Option<NonZeroUsize>)> + '_ {
        let seen = arm.map(|arm| self.reachable(arm, |_, arm, pending| pending.extend(arm.parent)));
        self.owners.iter().map(move |owner| {
            let selected =
                !owner.discarded && owner.arm.is_none_or(|id| seen.as_ref().is_none_or(|seen| seen[id.0.get() - 1]));
            (selected, owner.cycle, owner.register_read)
        })
    }
}

impl<B: BV> Solver<'_, B> {
    pub(crate) fn current_logical_arm(&self) -> Option<LogicalArm> {
        self.logical_arms.active
    }

    pub(crate) fn new_logical_arm(&mut self, parent: Option<LogicalArm>) -> LogicalArm {
        assert!(!self.savepoints.is_empty(), "逻辑臂必须属于区域事务");
        assert!(parent.is_none_or(|id| id.0.get() <= self.logical_arms.arms.len()), "父臂必须已分配");
        if self.logical_arms.arms.is_empty() {
            self.logical_arms.owners.resize(self.transaction_events.len(), EffectOwner::default());
        }
        self.logical_arms.arms.push(Arm { parent, sources: Vec::new() });
        LogicalArm(NonZeroUsize::new(self.logical_arms.arms.len()).unwrap())
    }

    pub(crate) fn with_logical_arm<T>(&mut self, arm: LogicalArm, f: impl FnOnce(&mut Self) -> T) -> T {
        assert!(arm.0.get() <= self.logical_arms.arms.len(), "只能恢复已分配的逻辑臂");
        let prior = self.logical_arms.active.replace(arm);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(self)));
        assert_eq!(std::mem::replace(&mut self.logical_arms.active, prior), Some(arm));
        match result {
            Ok(value) => value,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }

    pub(crate) fn join_logical_arm(&mut self, owner: LogicalArm, sources: impl IntoIterator<Item = LogicalArm>) {
        let inputs = &mut self.logical_arms.arms[owner.0.get() - 1].sources;
        inputs.extend(sources.into_iter().filter(|source| *source != owner));
    }

    /// 调用方已确定整条逻辑臂的正常出口不可达。只撤去该臂及后代的事件。
    /// 已提交断言受完整守卫保护；保留它们及定义，以供冻结的义务和其它存活记录使用。
    pub(crate) fn discard_logical_arm_effects(&mut self, arm: LogicalArm) {
        assert!(!self.savepoints.is_empty(), "死臂必须在根提交前撤销");
        let journal = &mut self.logical_arms;
        assert_eq!(journal.owners.len(), self.transaction_events.len(), "事件归属必须对齐");
        assert_eq!(self.transaction_event_guards.len(), self.transaction_events.len(), "事件条件必须对齐");
        let children = journal.children();
        // 撤销时沿下游作用域和本组成员走，不越过各组共用的前缀。
        let seen = journal.reachable(arm, |id, _, pending| pending.extend(&children[id.0.get() - 1]));
        let owned_by_arm = |owner: Option<LogicalArm>| owner.is_some_and(|id| seen[id.0.get() - 1]);
        assert!(!owned_by_arm(journal.active), "先退出当前原生作用域再丢弃逻辑臂");
        let savepoint = self.savepoints.last().unwrap().events_len;
        let mut removed_cycles = 0;
        let remove: Vec<_> = self
            .transaction_events
            .iter()
            .zip(&mut journal.owners)
            .enumerate()
            .map(|(index, (event, owner))| {
                if !matches!(event, Event::Smt(..)) && owned_by_arm(owner.arm) {
                    assert!(index >= savepoint, "逻辑臂事件不能越过活动保存点");
                    if owner.register_read.is_some() {
                        // 保留原始位置供仍实际读取的臂使用，撤去死臂的读取条件。
                        owner.discarded = true;
                        return false;
                    }
                    removed_cycles += i128::from(owner.cycle);
                    return true;
                }
                false
            })
            .collect();
        assert!(removed_cycles <= self.cycles, "撤销的周期不能超过当前计数");
        self.cycles -= removed_cycles;
        let first_removed = remove.iter().position(|drop| *drop);
        if let Some(start) = first_removed {
            self.invalidate_error_snapshot(start);
        }
        if let (Some(prefix), Some(start)) = (&mut self.finite_prefix, first_removed) {
            prefix.remove_suffix(finite_domain::BUFFERED, &self.transaction_events, start);
        }
        let mut drop = remove.iter();
        self.transaction_events.retain(|_| !drop.next().unwrap());
        if let (Some(prefix), Some(start)) = (&mut self.finite_prefix, first_removed) {
            for (index, event) in self.transaction_events.iter().enumerate().skip(start) {
                prefix.push(finite_domain::BUFFERED, index, event);
            }
        }
        let mut drop = remove.iter();
        self.transaction_event_guards.retain(|_| !drop.next().unwrap());
        let mut drop = remove.iter();
        self.logical_arms.owners.retain(|_| !drop.next().unwrap());
    }
}
