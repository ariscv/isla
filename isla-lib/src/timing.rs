//! 通用的耗时测量辅助组件。

use std::time::{Duration, Instant};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TimeMeasure {
    WallTime,
    ThreadCpuTime,
}

#[derive(Copy, Clone, Debug)]
enum TimePoint {
    Wall(Instant),
    ThreadCpu(Duration),
}

#[derive(Copy, Clone, Debug)]
pub struct Timer {
    measure: TimeMeasure,
    started: TimePoint,
}

impl Timer {
    pub fn start(measure: TimeMeasure) -> Self {
        Timer { measure, started: now(measure) }
    }

    pub fn elapsed(self) -> Duration {
        elapsed_since(self.started, now(self.measure))
    }
}

pub fn thread_cpu_time() -> Duration {
    let mut value = libc::timespec { tv_sec: 0, tv_nsec: 0 };
    let result = unsafe { libc::clock_gettime(libc::CLOCK_THREAD_CPUTIME_ID, &mut value) };
    assert_eq!(result, 0, "CLOCK_THREAD_CPUTIME_ID is unavailable");
    assert!(value.tv_sec >= 0, "thread CPU clock returned negative seconds");
    assert!((0..1_000_000_000).contains(&value.tv_nsec), "thread CPU clock returned invalid nanoseconds");
    Duration::new(value.tv_sec as u64, value.tv_nsec as u32)
}

fn now(measure: TimeMeasure) -> TimePoint {
    match measure {
        TimeMeasure::WallTime => TimePoint::Wall(Instant::now()),
        TimeMeasure::ThreadCpuTime => TimePoint::ThreadCpu(thread_cpu_time()),
    }
}

fn elapsed_since(started: TimePoint, finished: TimePoint) -> Duration {
    match (started, finished) {
        (TimePoint::Wall(started), TimePoint::Wall(finished)) => finished.duration_since(started),
        (TimePoint::ThreadCpu(started), TimePoint::ThreadCpu(finished)) => {
            finished.checked_sub(started).expect("thread CPU clock moved backwards")
        }
        _ => panic!("timer changed time measure while running"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wall_timer_measures_sleep() {
        let timer = Timer::start(TimeMeasure::WallTime);
        std::thread::sleep(Duration::from_millis(10));
        assert!(timer.elapsed() >= Duration::from_millis(10));
    }

    #[test]
    fn thread_cpu_timer_excludes_most_sleep_time() {
        let timer = Timer::start(TimeMeasure::ThreadCpuTime);
        std::thread::sleep(Duration::from_millis(20));
        assert!(timer.elapsed() < Duration::from_millis(10));
    }

    #[test]
    fn thread_cpu_clock_is_monotonic() {
        let before = thread_cpu_time();
        let after = thread_cpu_time();
        assert!(after >= before);
    }
}
