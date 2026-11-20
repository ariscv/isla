//! 单路径活动墙钟分账。保存点仅记录净值，实际发生的成本只增不减。

use std::cell::RefCell;
use std::sync::{
    atomic::{AtomicU64, Ordering},
    Arc, OnceLock,
};
use std::time::{Duration, Instant};

use serde::Serialize;

use crate::ir::{Name, Symtab};
use crate::source_loc::SourceLoc;
use crate::timeout::{PathTimeSnapshot, SmtOperation};

const MARKS: &[u64] = &[60, 120, 180, 240, 300, 360, 420, 480, 600, 720, 900, 1200, 2400, 3600];

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Category {
    Interpreter,
    Merge,
    Frame,
    Event,
    Log,
    SolverSetup,
    Smt,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
struct QueryTotals {
    ns: u64,
    calls: u64,
    checks: u64,
}

impl QueryTotals {
    fn since(self, previous: Self) -> Self {
        Self { ns: self.ns - previous.ns, calls: self.calls - previous.calls, checks: self.checks - previous.checks }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct Watermark {
    retained: QueryTotals,
    retained_steps: u64,
    retained_wall_ns: [u64; 7],
}

#[derive(Clone, Copy, Debug, Serialize)]
struct Check {
    source: SourceLoc,
    operation: &'static str,
    ns: u64,
    ordinal: u64,
    at_ns: u64,
    pmp_rounds: u64,
    assertions_and_assumptions: Option<(u32, usize)>,
}

#[derive(Clone, Debug, Default, Serialize)]
pub(crate) struct Totals {
    // 与 Category 同序。所有类别互斥，数组和为同一时点的活动墙钟。
    wall_ns: [u64; 7],
    rolled_wall_ns: [u64; 7],
    performed: QueryTotals,
    rolled: QueryTotals,
    steps: u64,
    rolled_steps: u64,
    rollbacks: u64,
    pmp_calls: u64,
    pmp_rounds: u64,
    pmp_last_rounds: u64,
    pmp_peak_rounds: u64,
    phys_pcs: [u64; 32],
    max_check: Option<Check>,
    last_check: Option<Check>,
    slow_checks: std::collections::VecDeque<Check>,
    // 子路径继承此前已到达的计时地标，可用地标所属任务编号关联后继终态。
    marks: Vec<u64>,
}

impl Totals {
    fn retained(&self) -> QueryTotals {
        self.performed.since(self.rolled)
    }

    fn watermark(&self) -> Watermark {
        Watermark {
            retained: self.retained(),
            retained_steps: self.steps - self.rolled_steps,
            retained_wall_ns: std::array::from_fn(|i| self.wall_ns[i] - self.rolled_wall_ns[i]),
        }
    }

    fn rollback(&mut self, saved: Watermark) {
        self.rolled = self.performed.since(saved.retained);
        self.rolled_steps = self.steps - saved.retained_steps;
        self.rolled_wall_ns = std::array::from_fn(|i| self.wall_ns[i] - saved.retained_wall_ns[i]);
        self.rollbacks += 1;
    }

    fn record_query(
        &mut self,
        operation: SmtOperation,
        source: SourceLoc,
        ns: u64,
        assertions_and_assumptions: Option<(u32, usize)>,
    ) {
        self.performed.ns += ns;
        self.performed.calls += 1;
        let operation = match operation {
            SmtOperation::ModelEval => return,
            SmtOperation::CheckSat => "check",
            SmtOperation::CheckSatAssuming => "assumptions",
        };
        self.performed.checks += 1;
        let check = Check {
            source,
            operation,
            ns,
            ordinal: self.performed.checks,
            at_ns: self.wall_ns.iter().sum(),
            pmp_rounds: self.pmp_rounds,
            assertions_and_assumptions,
        };
        self.last_check = Some(check);
        if self.max_check.is_none_or(|max| ns > max.ns) {
            self.max_check = Some(check);
        }
        if ns >= 1_000_000_000 {
            if self.slow_checks.len() == 8 {
                self.slow_checks.pop_front();
            }
            self.slow_checks.push_back(check);
        }
    }
}

struct State {
    totals: Totals,
    current: Category,
    since: Instant,
    segment: u64,
    pmp: Option<Name>,
    phys: Option<Name>,
}

impl State {
    fn new(totals: Totals, at: Instant) -> Self {
        Self { totals, current: Category::Interpreter, since: at, segment: 0, pmp: None, phys: None }
    }

    fn switch(&mut self, next: Category, at: Instant) {
        self.totals.wall_ns[self.current as usize] += at.duration_since(self.since).as_nanos() as u64;
        self.since = at;
        self.current = next;
    }

    fn snapshot(&mut self, at: Instant) -> Totals {
        self.switch(self.current, at);
        self.totals.clone()
    }
}

thread_local! { static ACTIVE: RefCell<Option<State>> = const { RefCell::new(None) }; }

pub(crate) fn enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("ISLA_PATH_ACCOUNT").is_some_and(|value| value == "1"))
}

pub(crate) fn active() -> bool {
    ACTIVE.with(|active| active.borrow().is_some())
}

pub(in crate::executor) struct TaskScope;

impl TaskScope {
    pub(in crate::executor) fn start(prefix: Option<&Totals>, at: Instant, symtab: &Symtab) -> Self {
        static NEXT_SEGMENT: AtomicU64 = AtomicU64::new(1);
        let mut state = State::new(prefix.cloned().unwrap_or_default(), at);
        state.segment = NEXT_SEGMENT.fetch_add(1, Ordering::Relaxed);
        state.pmp = symtab.get("zpmpCheck");
        state.phys = symtab.get("zphys_access_check");
        ACTIVE.with(|active| assert!(active.replace(Some(state)).is_none(), "路径分账不能嵌套启动"));
        Self
    }
}

impl Drop for TaskScope {
    fn drop(&mut self) {
        ACTIVE.with(|active| assert!(active.replace(None).is_some(), "缺少活动的路径分账"));
    }
}

pub(crate) struct Scope(Option<Category>);

impl Scope {
    pub(crate) fn enter(category: Category) -> Self {
        Self::enter_at(category, Instant::now)
    }

    fn enter_at(category: Category, now: impl FnOnce() -> Instant) -> Self {
        Self(ACTIVE.with(|active| {
            let mut active = active.borrow_mut();
            let state = active.as_mut()?;
            let previous = state.current;
            if previous == category {
                return None;
            }
            state.switch(category, now());
            Some(previous)
        }))
    }

    pub(crate) fn smt(started: Instant) -> Self {
        Self::enter_at(Category::Smt, || started)
    }

    pub(crate) fn finish_query(
        mut self,
        started: Instant,
        wall: Duration,
        operation: SmtOperation,
        source: SourceLoc,
        formula_size: impl FnOnce() -> Option<(u32, usize)>,
    ) {
        if let Some(previous) = self.0.take() {
            ACTIVE.with(|active| {
                let mut active = active.borrow_mut();
                let state = active.as_mut().expect("查询离开了所属路径");
                state.switch(previous, started + wall);
                let size = (operation != SmtOperation::ModelEval
                    && (wall >= Duration::from_secs(1)
                        || state.totals.max_check.is_none_or(|max| wall.as_nanos() > u128::from(max.ns))))
                .then(formula_size)
                .flatten();
                state.totals.record_query(operation, source, wall.as_nanos() as u64, size);
            });
        }
    }
}

impl Drop for Scope {
    fn drop(&mut self) {
        if let Some(previous) = self.0 {
            ACTIVE.with(|active| {
                active.borrow_mut().as_mut().expect("分账作用域离开了所属路径").switch(previous, Instant::now());
            });
        }
    }
}

pub(crate) fn watermark() -> Option<Watermark> {
    ACTIVE.with(|active| {
        active.borrow_mut().as_mut().map(|state| {
            state.switch(state.current, Instant::now());
            state.totals.watermark()
        })
    })
}

pub(crate) fn rollback(saved: Watermark) {
    ACTIVE.with(|active| {
        let mut active = active.borrow_mut();
        let state = active.as_mut().expect("保存点离开了所属路径");
        state.switch(state.current, Instant::now());
        state.totals.rollback(saved);
    });
}

pub(in crate::executor) fn snapshot(at: Instant) -> Option<Arc<Totals>> {
    ACTIVE.with(|active| active.borrow_mut().as_mut().map(|state| Arc::new(state.snapshot(at))))
}

pub(in crate::executor) fn step(function: Name, pc: usize) {
    ACTIVE.with(|active| {
        if let Some(state) = active.borrow_mut().as_mut() {
            let totals = &mut state.totals;
            totals.steps += 1;
            if Some(function) == state.pmp && pc == 0 {
                totals.pmp_calls += 1;
                totals.pmp_last_rounds = 0;
            }
            if Some(function) == state.phys {
                if let Some(count) = totals.phys_pcs.get_mut(pc) {
                    *count += 1;
                }
            }
        }
    });
}

pub(in crate::executor) fn back_edge(function: Name) {
    ACTIVE.with(|active| {
        if let Some(state) = active.borrow_mut().as_mut().filter(|state| Some(function) == state.pmp) {
            let totals = &mut state.totals;
            totals.pmp_rounds += 1;
            totals.pmp_last_rounds += 1;
            totals.pmp_peak_rounds = totals.pmp_peak_rounds.max(totals.pmp_last_rounds);
        }
    });
}

pub(in crate::executor) fn mark(active_wall: Duration) -> bool {
    ACTIVE.with(|active| {
        let mut active = active.borrow_mut();
        let Some(state) = active.as_mut() else { return false };
        let before = state.totals.marks.len();
        while MARKS.get(state.totals.marks.len()).is_some_and(|&mark| active_wall.as_secs() >= mark) {
            state.totals.marks.push(state.segment);
        }
        before != state.totals.marks.len()
    })
}

#[allow(clippy::too_many_arguments)]
pub(in crate::executor) fn emit(
    event: &str,
    timing: PathTimeSnapshot,
    at: Instant,
    site: &str,
    task: usize,
    signature: u64,
    fork_count: u64,
    steps: u64,
    files: &[&str],
) {
    let sample = ACTIVE.with(|active| {
        let mut active = active.borrow_mut();
        active.as_mut().map(|state| (state.segment, state.snapshot(at)))
    });
    if let Some((segment, totals)) = sample {
        let _scope = Scope::enter(Category::Log);
        eprintln!(
            "[PATH_ACCOUNT] {}",
            serde_json::json!({
                "event": event, "segment": segment, "task": task,
                "path_signature": format!("{signature:016x}"), "forks": fork_count,
                "site": site, "control_steps": steps,
                "active_ns": timing.active_wall.as_nanos() as u64,
                "cpu_ns": timing.executor_cpu.as_nanos() as u64,
                "max_source": totals.max_check.map(|check| check.source.location_string(files)),
                "last_source": totals.last_check.map(|check| check.source.location_string(files)),
                "slow_sources": totals.slow_checks.iter().map(|check| check.source.location_string(files)).collect::<Vec<_>>(),
                "retained": totals.retained(), "totals": totals,
            })
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_rollbacks_keep_all_actual_smt_work_and_the_maximum_check() {
        let mut totals = Totals::default();
        let loc = crate::source_loc::SourceLoc::unknown();
        let outer = totals.watermark();
        totals.wall_ns[Category::Interpreter as usize] += 20;
        totals.record_query(SmtOperation::CheckSat, loc, 30, None);
        totals.steps += 10;
        let inner = totals.watermark();
        totals.wall_ns[Category::Interpreter as usize] += 30;
        totals.record_query(SmtOperation::CheckSatAssuming, loc, 90, None);
        totals.steps += 20;
        totals.rollback(inner);
        totals.record_query(SmtOperation::ModelEval, loc, 15, None);
        totals.steps += 5;
        totals.rollback(outer);
        totals.record_query(SmtOperation::CheckSat, loc, 25, None);

        assert_eq!(totals.performed, QueryTotals { ns: 160, calls: 4, checks: 3 });
        assert_eq!(totals.rolled, QueryTotals { ns: 135, calls: 3, checks: 2 });
        assert_eq!(totals.retained(), QueryTotals { ns: 25, calls: 1, checks: 1 });
        assert_eq!(totals.max_check.as_ref().unwrap().ns, 90);
        assert_eq!(totals.steps, 35);
        assert_eq!(totals.rolled_steps, 35);
        assert_eq!(totals.rolled_wall_ns[Category::Interpreter as usize], 50);
    }

    #[test]
    fn real_solver_rollback_keeps_the_actual_check_and_its_location() {
        use crate::bitvector::b64::B64;
        use crate::smt::{self, Config, Context, SmtResult, Solver, Tactic};

        smt::configure_tastic(Tactic::Qfaufbv);
        let symtab = Symtab::new();
        let _task = TaskScope::start(None, Instant::now(), &symtab);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let tx = solver.start_transaction();
        let location = SourceLoc::new(0, 10, 2, 10, 5);
        assert_eq!(solver.check_sat(location), SmtResult::Sat);
        solver.rollback_transaction(tx);
        let totals = snapshot(Instant::now()).unwrap();
        assert_eq!(totals.performed.checks, 1);
        assert_eq!(totals.rolled.checks, 1);
        assert_eq!(totals.retained().checks, 0);
        assert_eq!(totals.max_check.unwrap().source, location);
        assert_eq!(totals.wall_ns[Category::Smt as usize], totals.performed.ns);
        assert_eq!(totals.rolled_wall_ns[Category::Smt as usize], totals.rolled.ns);
    }

    #[test]
    fn nested_wall_categories_exclude_smt_and_resume_with_the_inherited_prefix() {
        let start = Instant::now();
        let at = |ns| start + Duration::from_nanos(ns);
        let mut parent = State::new(Totals::default(), at(0));
        parent.switch(Category::Merge, at(10));
        parent.switch(Category::Smt, at(20));
        parent.switch(Category::Merge, at(80));
        parent.switch(Category::Interpreter, at(90));

        let mut child = State::new(parent.snapshot(at(100)), at(1000));
        child.switch(Category::Log, at(1010));
        child.switch(Category::Interpreter, at(1015));
        let child = child.snapshot(at(1020));
        let parent = parent.snapshot(at(130));
        assert_eq!(child.wall_ns, [35, 20, 0, 0, 5, 0, 60]);
        assert_eq!(parent.wall_ns, [50, 20, 0, 0, 0, 0, 60]);
    }
}
