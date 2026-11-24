//! 按函数和区域入口 PC 记录 B 臂收益。每线程每个站点只在首次查找时加锁。
use crate::ir::Name;
use crate::timing::thread_cpu_time;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::sync::{Arc, Mutex, Weak};
use std::time::Duration;

type Site = (Name, usize);
type Sites = HashMap<Site, Arc<ArmCost>>;

#[derive(Default)]
pub(super) struct ArmCosts(Mutex<Sites>);

thread_local! {
    static LOCAL_SITES: RefCell<(Weak<ArmCosts>, Sites)> = RefCell::default();
    static HELP_CPU: Cell<Duration> = const { Cell::new(Duration::ZERO) };
}

impl ArmCosts {
    pub(super) fn site(self: &Arc<Self>, function: Name, pc: usize) -> Arc<ArmCost> {
        LOCAL_SITES.with_borrow_mut(|(owner, local)| {
            if owner.as_ptr() != Arc::as_ptr(self) {
                local.clear();
                *owner = Arc::downgrade(self);
            }
            Arc::clone(
                local
                    .entry((function, pc))
                    .or_insert_with(|| Arc::clone(self.0.lock().unwrap().entry((function, pc)).or_default())),
            )
        })
    }
}

pub(super) struct ArmCost {
    pub body: AtomicU64,
    pub dispatch: AtomicU64,
    pub restore: AtomicU64,
    pub import: AtomicU64,
}

impl Default for ArmCost {
    fn default() -> Self {
        // 步骤 2 的 LOAD 入口中位数为 13.78 ms。先采用 14 ms 及 1 ms 导入先验，
        // 派发后的实测更新同一站点。零正文表示尚未完成串行采样。
        Self { body: 0.into(), dispatch: 0.into(), restore: 14_000_000.into(), import: 1_000_000.into() }
    }
}

impl ArmCost {
    pub(super) fn admits(&self, percent: u32) -> bool {
        let cost: u128 =
            [&self.dispatch, &self.restore, &self.import].into_iter().map(|v| v.load(Relaxed) as u128).sum();
        (self.body.load(Relaxed) as u128) * 100 > cost * (percent as u128)
    }

    pub(super) fn sample(counter: &AtomicU64, elapsed: Duration) {
        let sample = u64::try_from(elapsed.as_nanos()).unwrap_or(u64::MAX).max(1);
        let _ = counter.fetch_update(Relaxed, Relaxed, |previous| {
            Some(if previous == 0 { sample } else { ((previous as u128 * 7 + sample as u128) / 8) as u64 })
        });
    }
}

/// 同线程帮做的子臂 CPU 仅计入子臂，避免把等待方样本抬高。
pub(super) struct ArmCpu {
    start: Duration,
    helper: Duration,
}

impl ArmCpu {
    pub(super) fn start() -> Self {
        Self { start: thread_cpu_time(), helper: HELP_CPU.get() }
    }

    pub(super) fn elapsed(&self) -> Duration {
        (thread_cpu_time() - self.start).saturating_sub(HELP_CPU.get() - self.helper)
    }

    pub(super) fn finish_help(self) {
        HELP_CPU.set(self.helper + (thread_cpu_time() - self.start));
    }
}
