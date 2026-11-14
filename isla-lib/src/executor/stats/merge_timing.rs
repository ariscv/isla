//! 只在合并诊断开启时使用；包含时间用于定位，独占与根时间用于可相加的成本归属。
use super::merge_diagnostics;
use crate::timeout::SmtOperation;
use serde_json::{json, Value};
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

#[derive(Clone, Copy, Default)]
pub(super) struct Measure {
    pub wall: Duration,
    pub smt: Duration,
    pub queries: u64,
    pub model: Duration,
    pub model_calls: u64,
}
impl Measure {
    fn add(&mut self, other: Self) {
        self.wall += other.wall;
        self.smt += other.smt;
        self.queries += other.queries;
        self.model += other.model;
        self.model_calls += other.model_calls;
    }
    pub(super) fn subtract(self, other: Self) -> Self {
        Self {
            wall: self.wall.checked_sub(other.wall).expect("子区域耗时必须包含在父区域内"),
            smt: self.smt.checked_sub(other.smt).expect("子查询必须包含在父查询内"),
            queries: self.queries.checked_sub(other.queries).unwrap(),
            model: self.model.checked_sub(other.model).unwrap(),
            model_calls: self.model_calls.checked_sub(other.model_calls).unwrap(),
        }
    }
}
#[derive(Default)]
struct Aggregate {
    count: u64,
    sum: Measure,
    max: Measure,
}
impl Aggregate {
    fn record(&mut self, value: Measure) {
        self.count += 1;
        self.sum.add(value);
        self.max.wall = self.max.wall.max(value.wall);
        self.max.smt = self.max.smt.max(value.smt);
        self.max.queries = self.max.queries.max(value.queries);
        self.max.model = self.max.model.max(value.model);
        self.max.model_calls = self.max.model_calls.max(value.model_calls);
    }
    fn json(&self) -> Value {
        let metric = |sum: f64, max: f64| json!({"sum":sum,"mean":if self.count == 0 {0.0} else {sum/self.count as f64},"max":max});
        json!({"count":self.count,
            "wall_seconds":metric(self.sum.wall.as_secs_f64(),self.max.wall.as_secs_f64()),
            "smt_seconds":metric(self.sum.smt.as_secs_f64(),self.max.smt.as_secs_f64()),
            "queries":{"sum":self.sum.queries,"mean":if self.count==0 {0.0} else {self.sum.queries as f64/self.count as f64},"max":self.max.queries},
            "model_seconds":metric(self.sum.model.as_secs_f64(),self.max.model.as_secs_f64()),
            "model_calls":{"sum":self.sum.model_calls,"mean":if self.count==0 {0.0} else {self.sum.model_calls as f64/self.count as f64},"max":self.max.model_calls}})
    }
}
#[derive(Default)]
struct Costs {
    inclusive: Aggregate,
    exclusive: Aggregate,
    root: Aggregate,
}
impl Costs {
    fn record(&mut self, inclusive: Measure, exclusive: Measure, root: bool) {
        self.inclusive.record(inclusive);
        self.exclusive.record(exclusive);
        if root {
            self.root.record(inclusive);
        }
    }
    fn json(&self) -> Value {
        json!({"inclusive":self.inclusive.json(),"exclusive":self.exclusive.json(),"root":self.root.json()})
    }
}
#[derive(Default)]
pub(super) struct Counts {
    started: u64,
    finished: u64,
    outcomes: BTreeMap<String, Costs>,
    sites: BTreeMap<String, Costs>,
    other_sites: Costs,
    outside: Aggregate,
    all_smt: Aggregate,
}
impl Counts {
    pub(super) fn begin(&mut self) {
        self.started += 1;
    }
    pub(super) fn finish(&mut self, origin: &Value, outcome: &str, inclusive: Measure, exclusive: Measure, root: bool) {
        self.finished += 1;
        self.outcomes.entry(outcome.into()).or_default().record(inclusive, exclusive, root);
        let key = json!({"origin":origin,"outcome":outcome}).to_string();
        if key.len() > 1024 || (!self.sites.contains_key(&key) && self.sites.len() == 4096) {
            self.other_sites.record(inclusive, exclusive, root);
        } else {
            self.sites.entry(key).or_default().record(inclusive, exclusive, root);
        }
    }
    pub(super) fn rows(&self) -> Vec<Value> {
        self.outcomes
            .iter()
            .map(|(outcome, costs)| {
                let mut value = costs.json();
                value["outcome"] = json!(outcome);
                value
            })
            .collect()
    }
    pub(super) fn site_rows(&self) -> Vec<Value> {
        self.sites
            .iter()
            .map(|(key, costs)| {
                let mut value = costs.json();
                value["key"] = serde_json::from_str(key).unwrap();
                value
            })
            .collect()
    }
    pub(super) fn summary(&self) -> Value {
        json!({"schema":1,"kind":"merge_timing_summary","started":self.started,"finished":self.finished,
            "in_flight":self.started.checked_sub(self.finished).expect("结束尝试不能多于开始尝试"),"outcomes":self.rows(),
            "outside_smt":self.outside.json(),"all_smt":self.all_smt.json(),"other_sites":self.other_sites.json(),
            "note":"线程墙钟秒；inclusive含嵌套不可相加，exclusive扣子区域，root按最外结果归属；只含已返回调用和已结束尝试"})
    }
}
static COUNTS: OnceLock<Mutex<Counts>> = OnceLock::new();
struct Attempt {
    started: Instant,
    origin: Value,
    outcome: String,
    direct: Measure,
    children: Measure,
}
thread_local! {
    static ATTEMPTS: RefCell<Vec<Attempt>> = const { RefCell::new(Vec::new()) };
}
pub(super) fn reset() {
    *COUNTS.get_or_init(|| Mutex::new(Counts::default())).lock().unwrap() = Counts::default();
}
pub(super) struct AttemptGuard;
impl AttemptGuard {
    pub(super) fn start(origin: Value) -> Self {
        let started = Instant::now();
        COUNTS.get().unwrap().lock().unwrap().begin();
        ATTEMPTS.with(|stack| {
            stack.borrow_mut().push(Attempt {
                started,
                origin,
                outcome: "unfinished".into(),
                direct: Measure::default(),
                children: Measure::default(),
            })
        });
        Self
    }
    pub(super) fn finish(&mut self, outcome: String) {
        ATTEMPTS.with(|stack| stack.borrow_mut().last_mut().unwrap().outcome = outcome);
    }
}
impl Drop for AttemptGuard {
    fn drop(&mut self) {
        let (attempt, inclusive, exclusive, root) = ATTEMPTS.with(|stack| {
            let mut stack = stack.borrow_mut();
            let attempt = stack.pop().unwrap();
            let mut inclusive = attempt.direct;
            inclusive.add(attempt.children);
            inclusive.wall = attempt.started.elapsed();
            let exclusive = inclusive.subtract(attempt.children);
            let root = stack.is_empty();
            if let Some(parent) = stack.last_mut() {
                parent.children.add(inclusive);
            }
            (attempt, inclusive, exclusive, root)
        });
        COUNTS.get().unwrap().lock().unwrap().finish(&attempt.origin, &attempt.outcome, inclusive, exclusive, root);
    }
}
/// 复用真实Z3调用已有计时，命中已有模型或常量化简不伪装成查询。
#[inline]
pub(crate) fn record_smt_call(operation: SmtOperation, wall: Duration) {
    if !merge_diagnostics::enabled() {
        return;
    }
    let measure = match operation {
        SmtOperation::ModelEval => Measure { wall, model: wall, model_calls: 1, ..Measure::default() },
        SmtOperation::CheckSat | SmtOperation::CheckSatAssuming => {
            Measure { wall, smt: wall, queries: 1, ..Measure::default() }
        }
    };
    let inside = ATTEMPTS.with(|stack| {
        let mut stack = stack.borrow_mut();
        if let Some(attempt) = stack.last_mut() {
            attempt.direct.add(measure);
            true
        } else {
            false
        }
    });
    let mut counts = COUNTS.get().unwrap().lock().unwrap();
    counts.all_smt.record(measure);
    if !inside {
        counts.outside.record(measure);
    }
}
/// 在同一诊断snapshot与stderr锁内输出；有界位置表单行输出。
pub(super) fn write_snapshot(out: &mut impl std::io::Write, snapshot: usize, trigger: &str) {
    let counts = COUNTS.get().unwrap().lock().unwrap();
    for mut row in counts.site_rows() {
        row["schema"] = json!(1);
        row["kind"] = json!("merge_timing_site");
        row["snapshot"] = json!(snapshot);
        writeln!(out, "{row}").unwrap();
    }
    let mut summary = counts.summary();
    summary["snapshot"] = json!(snapshot);
    summary["trigger"] = json!(trigger);
    writeln!(out, "{summary}").unwrap();
}
#[cfg(test)]
pub(crate) fn summary_for_test() -> Value {
    COUNTS.get().unwrap().lock().unwrap().summary()
}
