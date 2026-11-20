//! 默认关闭的每轮互斥成本分账；不参与执行决策。

use std::cell::RefCell;
use std::sync::Arc;
use std::time::Instant;

use super::path_account;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Category {
    Guard,
    Savepoint,
    StateCow,
    FrameClone,
    StateMerge,
    EventBuffer,
    Definitions,
    Translate,
    Simplify,
    ReplayAssert,
    Traverse,
    Release,
    Diagnostics,
    Interpreter,
    Unknown,
    NativeScope,
}
const N: usize = 16;
const NAMES: [&str; N] = [
    "guard",
    "savepoint",
    "state_cow",
    "frame_clone",
    "state_merge",
    "event_buffer",
    "definitions",
    "translate",
    "simplify",
    "replay_assert",
    "traverse",
    "release",
    "diagnostics",
    "interpreter",
    "unknown",
    "native_scope",
];
#[derive(Clone, Copy, Default, serde::Serialize)]
struct Measure {
    ns: u64,
    calls: u64,
    units: u64,
    bytes: u64,
}
struct State {
    since: Instant,
    current: Option<Category>,
    totals: [Measure; N],
}
impl State {
    fn settle(&mut self) {
        let now = Instant::now();
        self.totals[self.current.unwrap_or(Category::Unknown) as usize].ns +=
            now.duration_since(self.since).as_nanos() as u64;
        self.since = now;
    }
}
thread_local! { static STATE: RefCell<State> = RefCell::new(State {since:Instant::now(),current:None,totals:[Measure::default();N]}); }
#[cfg(test)]
thread_local! {static TEST_ENABLED:std::cell::Cell<Option<bool>>=const{std::cell::Cell::new(None)};}
pub(crate) fn enabled() -> bool {
    #[cfg(test)]
    if let Some(value) = TEST_ENABLED.with(std::cell::Cell::get) {
        return value;
    }
    crate::config::RegionOptions::current().probe_round_cost
}
pub(crate) struct Scope {
    previous: Option<Category>,
    active: bool,
    _path: Option<path_account::Scope>,
}
impl Scope {
    pub(crate) fn enter(category: Category) -> Self {
        use path_account::Category as PathCategory;
        let path_category = match category {
            Category::Interpreter => Some(PathCategory::Interpreter),
            Category::Guard | Category::StateMerge => Some(PathCategory::Merge),
            Category::Savepoint | Category::FrameClone | Category::Release => Some(PathCategory::Frame),
            Category::EventBuffer => Some(PathCategory::Event),
            Category::Definitions
            | Category::Translate
            | Category::Simplify
            | Category::ReplayAssert
            | Category::Traverse
            | Category::NativeScope => Some(PathCategory::SolverSetup),
            Category::StateCow | Category::Diagnostics | Category::Unknown => None,
        };
        let path = path_category.map(path_account::Scope::enter);
        if !enabled() {
            return Self { previous: None, active: false, _path: path };
        }
        STATE.with(|state| {
            let mut state = state.borrow_mut();
            state.totals[category as usize].calls += 1;
            // 同类递归不再读时钟；不同类子调用才切换独占时间归属。
            if state.current == Some(category) {
                return Self { previous: None, active: false, _path: path };
            }
            state.settle();
            let previous = state.current;
            state.current = Some(category);
            Self { previous, active: true, _path: path }
        })
    }
}
impl Drop for Scope {
    fn drop(&mut self) {
        if self.active {
            STATE.with(|state| {
                let mut state = state.borrow_mut();
                state.settle();
                state.current = self.previous;
            });
        }
    }
}
pub(crate) fn count(category: Category, units: usize, bytes: usize) {
    if enabled() {
        STATE.with(|state| {
            let mut state = state.borrow_mut();
            let row = &mut state.totals[category as usize];
            row.units += units as u64;
            row.bytes += bytes as u64;
        });
    }
}
pub(crate) fn reset_boundary() {
    if enabled() {
        STATE.with(|state| {
            let mut state = state.borrow_mut();
            state.totals = [Measure::default(); N];
            state.since = Instant::now();
        });
    }
}
fn take_round() -> serde_json::Value {
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        state.settle();
        NAMES
            .iter()
            .zip(state.totals.iter())
            .map(|(name, metric)| ((*name).to_string(), serde_json::to_value(metric).unwrap()))
            .collect::<serde_json::Map<_, _>>()
            .into()
    })
}
pub(crate) fn snapshot() -> Option<serde_json::Value> {
    enabled().then(take_round)
}
/// 保留Arc::make_mut的原有语义；仅诊断其真实COW时间，bytes是对象浅大小。
pub(crate) fn make_mut<T: Clone>(value: &mut Arc<T>) -> &mut T {
    let timer = Scope::enter(Category::StateCow);
    if enabled() && Arc::strong_count(value) > 1 {
        count(Category::StateCow, 1, std::mem::size_of::<T>());
    }
    let frame_copy = (path_account::active() && Arc::strong_count(value) > 1)
        .then(|| path_account::Scope::enter(path_account::Category::Frame));
    let result = Arc::make_mut(value);
    drop(frame_copy);
    drop(timer);
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn nested_cost_scopes_partition_elapsed_and_reset_at_boundary() {
        TEST_ENABLED.with(|v| v.set(Some(true)));
        reset_boundary();
        let started = std::time::Instant::now();
        {
            let outer = Scope::enter(Category::Guard);
            std::thread::sleep(std::time::Duration::from_millis(2));
            {
                let inner = Scope::enter(Category::Savepoint);
                count(Category::Savepoint, 17, 128);
                std::thread::sleep(std::time::Duration::from_millis(2));
                drop(inner);
            }
            drop(outer);
        }
        let row = take_round();
        assert!(row["guard"]["ns"].as_u64().unwrap() > 0);
        assert!(row["savepoint"]["ns"].as_u64().unwrap() > 0);
        assert_eq!(row["savepoint"]["units"], 17);
        let total: u64 = row.as_object().unwrap().values().map(|v| v["ns"].as_u64().unwrap()).sum();
        assert!(total >= 4_000_000);
        assert!(total <= started.elapsed().as_nanos() as u64 + 1_000_000, "嵌套时间不能重复累计");
        reset_boundary();
        let empty = take_round();
        assert_eq!(empty["savepoint"]["ns"], 0);
        TEST_ENABLED.with(|v| v.set(Some(false)));
        let guard = Scope::enter(Category::Guard);
        drop(guard);
        assert!(snapshot().is_none());
        TEST_ENABLED.with(|v| v.set(None));
    }
}
