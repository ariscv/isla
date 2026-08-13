use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use crate::timeout::PathTimeSnapshot;
use crate::timing::thread_cpu_time;

pub(super) type PathTimeTotals = PathTimeSnapshot;

#[derive(Copy, Clone, Debug)]
pub(super) struct ActiveSlice {
    wall_start: Instant,
    thread_cpu_start: Duration,
}

#[derive(Debug, Default)]
struct PathTimingState {
    totals: PathTimeTotals,
    active: Option<ActiveSlice>,
}

/// Mutable timing state for one logical path while it is owned by an executor worker.
///
/// Nested function frames clone this handle because they belong to the same logical
/// path. A fork must use [`PathTiming::fork_snapshot`] and construct a new handle,
/// otherwise parent and child would incorrectly share their post-fork totals.
#[derive(Clone, Debug, Default)]
pub(super) struct PathTiming {
    state: Arc<Mutex<PathTimingState>>,
}

impl PathTiming {
    #[cfg(test)]
    pub(super) fn from_totals(totals: PathTimeTotals) -> Self {
        PathTiming::from_snapshot(totals)
    }

    pub(super) fn from_snapshot(totals: PathTimeTotals) -> Self {
        PathTiming { state: Arc::new(Mutex::new(PathTimingState { totals, active: None })) }
    }

    pub(super) fn start_active(&self) {
        self.start_active_at(Instant::now(), thread_cpu_time());
    }

    pub(super) fn start_active_at(&self, wall_now: Instant, thread_cpu_now: Duration) {
        let mut state = self.state.lock().expect("path timing state poisoned");
        assert!(state.active.is_none(), "path already has an active timing slice");
        state.active = Some(ActiveSlice { wall_start: wall_now, thread_cpu_start: thread_cpu_now });
    }

    pub(super) fn pause_active(&self) {
        self.pause_active_at(Instant::now(), thread_cpu_time());
    }

    pub(super) fn pause_active_at(&self, wall_now: Instant, thread_cpu_now: Duration) {
        let mut state = self.state.lock().expect("path timing state poisoned");
        let active = state.active.take().expect("path has no active timing slice");
        accumulate_active(&mut state.totals, active, wall_now, thread_cpu_now);
    }

    pub(super) fn snapshot(&self) -> PathTimeSnapshot {
        self.snapshot_at(Instant::now(), thread_cpu_time())
    }

    pub(super) fn snapshot_at(&self, wall_now: Instant, thread_cpu_now: Duration) -> PathTimeSnapshot {
        let state = self.state.lock().expect("path timing state poisoned");
        let mut totals = state.totals;
        if let Some(active) = state.active {
            accumulate_active(&mut totals, active, wall_now, thread_cpu_now);
        }
        totals
    }

    pub(super) fn fork_snapshot(&self) -> PathTimeSnapshot {
        self.snapshot()
    }

    #[cfg(test)]
    pub(super) fn totals(&self) -> PathTimeSnapshot {
        let state = self.state.lock().expect("path timing state poisoned");
        assert!(state.active.is_none(), "settled path totals requested while path is active");
        state.totals
    }

    #[cfg(test)]
    pub(super) fn is_active(&self) -> bool {
        self.state.lock().expect("path timing state poisoned").active.is_some()
    }
}

fn accumulate_active(totals: &mut PathTimeTotals, active: ActiveSlice, wall_now: Instant, thread_cpu_now: Duration) {
    let wall_delta = wall_now.duration_since(active.wall_start);
    let cpu_delta = thread_cpu_now.checked_sub(active.thread_cpu_start).expect("thread CPU clock moved backwards");
    totals.active_wall = totals.active_wall.checked_add(wall_delta).expect("active wall duration overflow");
    totals.executor_cpu = totals.executor_cpu.checked_add(cpu_delta).expect("executor CPU duration overflow");
}

#[derive(Copy, Clone, Debug)]
pub(super) struct PathTimeout {
    duration: Option<Duration>,
}

impl PathTimeout {
    #[cfg(test)]
    pub(super) fn unlimited() -> Self {
        PathTimeout { duration: None }
    }

    pub(super) fn from_seconds(timeout: Option<u64>) -> Self {
        PathTimeout { duration: timeout.map(Duration::from_secs) }
    }

    #[cfg(test)]
    pub(super) fn timed_out(self, timing: PathTimeSnapshot) -> bool {
        self.duration.map_or(false, |duration| timing.active_wall >= duration)
    }

    /// 配置的单路径预算；`--timeout` 未配置时为 `None`。
    pub(super) fn limit(self) -> Option<Duration> {
        self.duration
    }

    pub(super) fn timed_out_with(self, snapshot: impl FnOnce() -> PathTimeSnapshot) -> bool {
        match self.duration {
            Some(duration) => snapshot().active_wall >= duration,
            None => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ms(value: u64) -> Duration {
        Duration::from_millis(value)
    }

    #[test]
    fn active_wall_and_thread_cpu_are_accounted_independently() {
        let base = Instant::now();
        let timing = PathTiming::default();

        timing.start_active_at(base, ms(10));
        let active = timing.snapshot_at(base + ms(40), ms(25));
        assert_eq!(active.active_wall, ms(40));
        assert_eq!(active.executor_cpu, ms(15));

        timing.pause_active_at(base + ms(50), ms(30));
        let paused = timing.totals();
        assert_eq!(paused.active_wall, ms(50));
        assert_eq!(paused.executor_cpu, ms(20));
    }

    #[test]
    fn timeout_basis_none_zero_and_inclusive_boundary_are_stable() {
        let totals = PathTimeTotals { active_wall: ms(10), executor_cpu: ms(4) };

        assert!(!PathTimeout::unlimited().timed_out(totals));
        assert!(PathTimeout { duration: Some(Duration::ZERO) }.timed_out(totals));
        assert!(PathTimeout { duration: Some(ms(10)) }.timed_out(totals));
        assert!(!PathTimeout { duration: Some(ms(11)) }.timed_out(totals));
    }

    #[test]
    fn unlimited_timeout_does_not_request_a_timing_snapshot() {
        let mut snapshot_requested = false;

        assert!(!PathTimeout::unlimited().timed_out_with(|| {
            snapshot_requested = true;
            PathTimeSnapshot::default()
        }));
        assert!(!snapshot_requested);
    }

    #[test]
    fn forked_paths_share_only_the_settled_prefix() {
        let base = Instant::now();
        let parent = PathTiming::default();
        parent.start_active_at(base, ms(5));
        let prefix = parent.snapshot_at(base + ms(20), ms(12));

        let child = PathTiming::from_totals(prefix);
        child.start_active_at(base + ms(30), ms(100));
        child.pause_active_at(base + ms(40), ms(103));

        parent.pause_active_at(base + ms(50), ms(20));

        assert_eq!(parent.totals().active_wall, ms(50));
        assert_eq!(parent.totals().executor_cpu, ms(15));
        assert_eq!(child.totals().active_wall, ms(30));
        assert_eq!(child.totals().executor_cpu, ms(10));
    }

    #[test]
    #[should_panic(expected = "path already has an active timing slice")]
    fn starting_two_active_slices_panics() {
        let timing = PathTiming::default();
        let now = Instant::now();
        timing.start_active_at(now, Duration::ZERO);
        timing.start_active_at(now, Duration::ZERO);
    }

    #[test]
    #[should_panic(expected = "path has no active timing slice")]
    fn pausing_without_an_active_slice_panics() {
        PathTiming::default().pause_active_at(Instant::now(), Duration::ZERO);
    }
}
