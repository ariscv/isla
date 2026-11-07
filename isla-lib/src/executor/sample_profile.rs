//! 常驻判定的可选线程局部计时；阶段必须互不嵌套。
use crate::timing::thread_cpu_time;
use serde::Serialize;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::time::{Duration, Instant};

#[derive(Clone, Default, Serialize)]
pub struct Measurement {
    pub calls: u64,
    pub wall_seconds: f64,
    pub cpu_seconds: f64,
}

pub type Measurements = BTreeMap<&'static str, Measurement>;
thread_local! {
    static TOTALS: RefCell<Option<Measurements>> = const { RefCell::new(None) };
}

pub fn reset() {
    TOTALS.with(|totals| *totals.borrow_mut() = Some(BTreeMap::new()));
}

pub fn take() -> Measurements {
    TOTALS.with(|totals| totals.borrow_mut().take().expect("尚未开始阶段计时"))
}

pub fn add(total: &mut Measurements, extra: &Measurements) {
    for (stage, value) in extra {
        let row = total.entry(stage).or_default();
        row.calls += value.calls;
        row.wall_seconds += value.wall_seconds;
        row.cpu_seconds += value.cpu_seconds;
    }
}

pub struct Span {
    stage: &'static str,
    start: Option<(Instant, Duration)>,
}
impl Span {
    pub fn new(stage: &'static str) -> Self {
        let enabled = TOTALS.with(|totals| totals.borrow().is_some());
        Self { stage, start: enabled.then(|| (Instant::now(), thread_cpu_time())) }
    }
}
impl Drop for Span {
    fn drop(&mut self) {
        if let Some((wall, cpu)) = self.start {
            let cpu = (thread_cpu_time() - cpu).as_secs_f64();
            let wall = wall.elapsed().as_secs_f64();
            TOTALS.with(|totals| {
                let mut totals = totals.borrow_mut();
                let row = totals.as_mut().expect("计时阶段尚未结束").entry(self.stage).or_default();
                row.calls += 1;
                row.wall_seconds += wall;
                row.cpu_seconds += cpu;
            });
        }
    }
}
