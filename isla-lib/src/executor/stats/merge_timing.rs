//! 只在合并诊断开启时使用；包含时间用于定位，独占与根时间用于可相加的成本归属。
use super::merge_diagnostics;
use crate::timeout::SmtOperation;
use serde_json::{json, Value};
use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};
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
    live: BTreeMap<usize, LiveAttempt>,
    outcomes: BTreeMap<String, Costs>,
    sites: BTreeMap<String, Costs>,
    other_sites: Costs,
    outside: Aggregate,
    all_smt: Aggregate,
}
struct LiveAttempt {
    parent: Option<usize>,
    task: usize,
    origin: Value,
    started: Instant,
    start_steps: u64,
    start_forks: usize,
    start_branches: u64,
    steps: u64,
    forks: usize,
    branches: u64,
    call_instance: Option<usize>,
    pte: Option<(Option<i64>, Option<i64>)>,
    position: Value,
    sampled: Instant,
}
impl Counts {
    #[allow(clippy::too_many_arguments)]
    fn begin_live(
        &mut self,
        id: usize,
        parent: Option<usize>,
        task: usize,
        origin: Value,
        now: Instant,
        steps: u64,
        forks: usize,
    ) {
        let mut position = origin.clone();
        position["phase"] = json!("admission");
        self.live.insert(
            id,
            LiveAttempt {
                parent,
                task,
                origin,
                started: now,
                start_steps: steps,
                start_forks: forks,
                start_branches: BRANCHES.with(Cell::get),
                steps: 0,
                forks: 0,
                branches: 0,
                call_instance: None,
                pte: None,
                position,
                sampled: now,
            },
        );
    }
    fn sample_live(&mut self, ids: &[usize], steps: u64, forks: usize, position: Value, now: Instant) {
        for id in ids {
            let row = self.live.get_mut(id).unwrap();
            row.steps = steps - row.start_steps;
            row.forks = forks - row.start_forks;
            row.branches = BRANCHES.with(Cell::get) - row.start_branches;
            row.position = position.clone();
            row.sampled = now;
        }
    }
    fn end_live(&mut self, id: usize) -> LiveAttempt {
        self.live.remove(&id).expect("结束的区域必须曾登记为在途")
    }
    fn live_rows(&self, now: Instant) -> Vec<Value> {
        self.live
            .iter()
            .map(|(id, row)| {
                json!({
                    "attempt":id, "parent_attempt":row.parent, "task":row.task, "origin":row.origin,
                    "current":row.position, "steps":row.steps, "live_forks":row.forks,
                    "both_feasible_nested":row.branches,"call_instance":row.call_instance,"pte_width_level":row.pte,
                    "wall_seconds":now.duration_since(row.started).as_secs_f64(),
                    "sample_age_seconds":now.duration_since(row.sampled).as_secs_f64()
                })
            })
            .collect()
    }
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
    id: usize,
    tracked: bool,
    started: Instant,
    origin: Value,
    outcome: String,
    direct: Measure,
    children: Measure,
    translation: Option<usize>,
    selected: bool,
    joins: JoinCounts,
    delivered: Option<usize>,
}
#[derive(Default, serde::Serialize)]
struct JoinCounts {
    joins_started: usize,
    joins_delivered: usize,
    arrivals: usize,
    output_frames: usize,
}
impl JoinCounts {
    fn arrivals(&mut self, count: usize) {
        self.joins_started += 1;
        self.arrivals += count;
    }
    fn delivered(&mut self, count: usize) {
        self.joins_delivered += 1;
        self.output_frames += count;
    }
}
thread_local! {
    static ATTEMPTS: RefCell<Vec<Attempt>> = const { RefCell::new(Vec::new()) };
    static STEPS: Cell<u64> = const { Cell::new(0) };
    static FORKS: Cell<usize> = const { Cell::new(0) };
    static BRANCHES: Cell<u64> = const { Cell::new(0) };
}
pub(super) fn reset() {
    *COUNTS.get_or_init(|| Mutex::new(Counts::default())).lock().unwrap() = Counts::default();
}
pub(super) struct AttemptGuard {
    progress: super::region_progress::AttemptGuard,
}
impl AttemptGuard {
    pub(super) fn start(id: usize, task: usize, origin: Value) -> Self {
        let progress = super::region_progress::AttemptGuard::start(origin.clone());
        let started = Instant::now();
        let tracked = crate::config::RegionOptions::current().progress;
        ATTEMPTS.with(|stack| {
            let mut stack = stack.borrow_mut();
            let mut counts = COUNTS.get().unwrap().lock().unwrap();
            counts.begin();
            if tracked {
                let parent = stack.last().filter(|attempt| attempt.tracked).map(|attempt| attempt.id);
                counts.begin_live(
                    id,
                    parent,
                    task,
                    origin.clone(),
                    started,
                    STEPS.with(Cell::get),
                    FORKS.with(Cell::get),
                );
            }
            let translation = stack
                .last()
                .and_then(|attempt| attempt.translation)
                .or_else(|| (tracked && origin["function"] == "translateAddr" && origin["pc"] == 13).then_some(id));
            let selected = tracked
                && (translation.is_some()
                    || matches!(
                        origin["function"].as_str(),
                        Some("pmpCheck" | "pt_walk" | "translateAddr" | "translate_TLB_miss" | "translate_TLB_hit")
                    ));
            stack.push(Attempt {
                id,
                tracked,
                started,
                origin,
                outcome: "unfinished".into(),
                direct: Measure::default(),
                children: Measure::default(),
                translation,
                selected,
                joins: JoinCounts::default(),
                delivered: None,
            })
        });
        Self { progress }
    }
    pub(super) fn finish(&mut self, outcome: String) {
        self.progress.finish(&outcome);
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
        let mut counts = COUNTS.get().unwrap().lock().unwrap();
        let live = attempt.tracked.then(|| counts.end_live(attempt.id));
        counts.finish(&attempt.origin, &attempt.outcome, inclusive, exclusive, root);
        drop(counts);
        if attempt.selected {
            static ROWS: AtomicUsize = AtomicUsize::new(0);
            let row = ROWS.fetch_add(1, Ordering::Relaxed);
            if row < 100_000 {
                let live = live.unwrap();
                eprintln!(
                    "{}",
                    json!({"kind":"translate_stats_attempt","attempt":attempt.id,
                    "parent_attempt":live.parent,"translate_attempt":attempt.translation,"task":live.task,
                    "origin":attempt.origin,"outcome":attempt.outcome,"call_instance":live.call_instance,
                    "pte_width_level":live.pte,"steps":STEPS.with(Cell::get)-live.start_steps,
                    "both_feasible_nested":BRANCHES.with(Cell::get)-live.start_branches,"joins":attempt.joins,
                    "delivered_frames":attempt.delivered,"wall_seconds":inclusive.wall.as_secs_f64(),
                    "exclusive_wall_seconds":exclusive.wall.as_secs_f64()})
                );
            } else if row == 100_000 {
                eprintln!("{}", json!({"kind":"translate_stats_truncated","limit":100_000}));
            }
        }
    }
}

pub(crate) fn observe_frame<B: crate::bitvector::BV>(
    frame: &crate::executor::LocalFrame<B>,
    symtab: &crate::ir::Symtab,
) {
    ATTEMPTS.with(|stack| {
        let stack = stack.borrow();
        let Some(attempt) = stack.last().filter(|attempt| attempt.selected) else { return };
        let pte = symtab.get("zpt_walk").and_then(|pt_walk| {
            let vars = if frame.function_name == pt_walk {
                &frame.local_state.vars
            } else {
                let index = frame.backtrace.iter().rposition(|(function, _)| *function == pt_walk)?;
                &frame.stack_vars[index]
            };
            let integer = |name| match vars.get(&symtab.get(name)?) {
                Some(crate::ir::UVal::Init(crate::ir::Val::I64(value))) => Some(*value),
                _ => None,
            };
            Some((integer("zsv_width"), integer("zlevel")))
        });
        let mut counts = COUNTS.get().unwrap().lock().unwrap();
        let live = counts.live.get_mut(&attempt.id).unwrap();
        live.call_instance = Some(frame.local_state.call_instance);
        live.pte = pte;
    });
}

pub(crate) fn observe_join(arrivals: usize) {
    ATTEMPTS.with(|stack| {
        if let Some(attempt) = stack.borrow_mut().last_mut().filter(|attempt| attempt.selected) {
            attempt.joins.arrivals(arrivals);
        }
    });
}

pub(crate) fn observe_join_output(frames: usize) {
    ATTEMPTS.with(|stack| {
        if let Some(attempt) = stack.borrow_mut().last_mut().filter(|attempt| attempt.selected) {
            attempt.joins.delivered(frames);
        }
    });
}

pub(crate) fn observe_delivery(frames: usize) {
    ATTEMPTS.with(|stack| {
        if let Some(attempt) = stack.borrow_mut().last_mut().filter(|attempt| attempt.selected) {
            attempt.delivered = Some(frames);
        }
    });
}

pub(crate) fn both_feasible_branch() {
    BRANCHES.with(|count| count.set(count.get() + 1));
}
pub(crate) fn live_attempt() -> Option<usize> {
    ATTEMPTS.with(|stack| stack.borrow().last().filter(|attempt| attempt.tracked).map(|attempt| attempt.id))
}

/// 一个打开的二臂分叉保留一个备用前沿。嵌套分叉在退出时恢复外层值。
pub(crate) struct LiveForks(Option<usize>);
impl LiveForks {
    pub(crate) fn start() -> Self {
        Self(live_attempt().map(|_| FORKS.with(Cell::get)))
    }

    pub(crate) fn set(&self, additional: usize) {
        if let Some(base) = self.0 {
            FORKS.with(|forks| forks.set(base + additional));
        }
    }
}
impl Drop for LiveForks {
    fn drop(&mut self) {
        self.set(0);
    }
}

pub(crate) fn live_step(function: crate::ir::Name, pc: usize, symtab: &crate::ir::Symtab) {
    let steps = STEPS.with(|steps| {
        let next = steps.get() + 1;
        steps.set(next);
        next
    });
    if steps % 256 == 0 {
        live_sample(function, pc, symtab, "instruction");
    }
}

pub(crate) fn live_sample(function: crate::ir::Name, pc: usize, symtab: &crate::ir::Symtab, phase: &'static str) {
    ATTEMPTS.with(|stack| {
        let stack = stack.borrow();
        if !stack.last().is_some_and(|attempt| attempt.tracked) {
            return;
        }
        let ids: Vec<_> = stack.iter().filter(|attempt| attempt.tracked).map(|attempt| attempt.id).collect();
        let position = json!({"function":crate::zencode::decode(symtab.to_str(function)), "pc":pc, "phase":phase});
        COUNTS.get().unwrap().lock().unwrap().sample_live(
            &ids,
            STEPS.with(Cell::get),
            FORKS.with(Cell::get),
            position,
            Instant::now(),
        );
    });
}

/// 复用真实Z3调用已有计时，命中已有模型或常量化简不伪装成查询。
#[inline]
pub(crate) fn record_smt_call(operation: SmtOperation, wall: Duration) {
    if !merge_diagnostics::enabled() {
        return;
    }
    super::region_progress::smt(operation, wall);
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
    for mut row in counts.live_rows(Instant::now()) {
        row["schema"] = json!(1);
        row["kind"] = json!("merge_inflight");
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn translate_stats_counts_arrivals_and_outputs_separately() {
        let mut joins = JoinCounts::default();
        joins.arrivals(3);
        joins.delivered(2);
        joins.arrivals(2); // 没有成功交付的汇合
        joins.arrivals(0);
        joins.delivered(0);
        assert_eq!(
            json!(joins),
            json!({
                "joins_started":3, "joins_delivered":2, "arrivals":5, "output_frames":2
            })
        );
    }

    #[test]
    fn region_inflight_snapshot_tracks_nested_attempts() {
        let mut counts = Counts::default();
        let start = Instant::now();
        counts.begin_live(10, None, 3, json!({"function":"outer","pc":5}), start, 4, 1);
        counts.begin_live(11, Some(10), 3, json!({"function":"inner","pc":7}), start, 9, 2);
        counts.sample_live(&[10, 11], 19, 4, json!({"function":"leaf","pc":13}), start);
        let rows = counts.live_rows(start + Duration::from_secs(8));
        assert_eq!(rows[0]["steps"], 15);
        assert_eq!(rows[0]["live_forks"], 3);
        assert_eq!(rows[1]["steps"], 10);
        assert_eq!(rows[1]["live_forks"], 2);
        assert_eq!(rows[1]["parent_attempt"], 10);
        assert_eq!(rows[1]["current"]["pc"], 13);
        assert_eq!(rows[1]["wall_seconds"], 8.0);
        counts.end_live(11);
        assert_eq!(counts.live_rows(start).len(), 1);
    }
}
