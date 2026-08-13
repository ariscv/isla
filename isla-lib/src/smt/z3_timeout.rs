//! Z3 timeout 调用边界。
//!
//! 前半部分封装 thread-interrupt 状态与 watchdog；后半部分集中封装所有受保护的
//! `Z3_*` 调用。local/thread-interrupt 的执行差异只在这些 wrapper 内选择。

use std::cell::RefCell;
use std::convert::TryInto;
use std::sync::Arc;
use std::sync::OnceLock;
use std::time::Duration;
use std::time::Instant;

use z3_sys::{
    Z3_ast, Z3_context, Z3_lbool, Z3_model, Z3_model_eval, Z3_solver, Z3_solver_check, Z3_solver_check_assumptions,
};

use crate::error::SmtError;
use crate::source_loc::SourceLoc;
#[cfg(feature = "smt-thread-interrupt")]
use crate::timeout::SmtTimeout;
use crate::timeout::{SmtCallStats, SmtOperation, TimeoutSmtDump};
#[cfg(feature = "smt-thread-interrupt")]
use z3_sys::Z3_interrupt;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(super) enum Z3TimeoutError {
    Interrupted,
}

#[cfg(feature = "smt-thread-interrupt")]
struct Z3InterruptHandle {
    context: Z3_context,
}

#[cfg(feature = "smt-thread-interrupt")]
unsafe impl Send for Z3InterruptHandle {}
#[cfg(feature = "smt-thread-interrupt")]
unsafe impl Sync for Z3InterruptHandle {}

#[cfg(feature = "smt-thread-interrupt")]
impl Z3InterruptHandle {
    fn from_context(context: Z3_context) -> Self {
        Z3InterruptHandle { context }
    }

    fn interrupt(self) {
        unsafe { Z3_interrupt(self.context) }
    }
}

static OPERATION_TIMEOUT: OnceLock<Duration> = OnceLock::new();

/// 已配置的单次 SMT operation deadline；未配置 `--smt-timeout` 时为 `None`。
pub fn configured_operation_timeout() -> Option<Duration> {
    OPERATION_TIMEOUT.get().copied()
}

// 每条路径的 SMT 调用统计。一个 worker 线程同一时刻只推进一条路径（`run_loop` 在路径
// 开始时重置），所以线程局部就等于路径局部；统计本身只有几个标量，始终开启。
thread_local! {
    static PATH_SMT_STATS: RefCell<SmtCallStats> = const { RefCell::new(SmtCallStats::empty()) };
}

fn record_path_smt_call(operation: SmtOperation, source_loc: SourceLoc, wall: Duration, timed_out: bool) {
    PATH_SMT_STATS.with(|stats| stats.borrow_mut().record(operation, source_loc, wall, timed_out))
}

/// 清空当前线程的路径级 SMT 统计，路径开始执行时调用。
pub fn reset_path_smt_stats() {
    PATH_SMT_STATS.with(|stats| *stats.borrow_mut() = SmtCallStats::empty())
}

/// 读取当前线程的路径级 SMT 统计。
pub fn path_smt_stats() -> SmtCallStats {
    PATH_SMT_STATS.with(|stats| stats.borrow().clone())
}

// 修改这个值即可同时调整最慢和最快求解耗时的输出条数。
#[cfg(feature = "smtperf")]
const SMTPERF_EXTREME_COUNT: usize = 3;

#[cfg(feature = "smtperf")]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct SmtSolveTiming {
    operation: SmtOperation,
    duration: Duration,
}

#[cfg(feature = "smtperf")]
thread_local! {
    static SMT_SOLVE_TIMINGS: RefCell<Vec<SmtSolveTiming>> = RefCell::new(Vec::new());
}

#[cfg(feature = "smtperf")]
fn record_solve_result<T>(operation: SmtOperation, duration: Duration, result: &Result<T, Z3TimeoutError>) {
    if result.is_ok() {
        SMT_SOLVE_TIMINGS.with(|timings| timings.borrow_mut().push(SmtSolveTiming { operation, duration }));
    }
}

#[cfg(feature = "smtperf")]
fn solve_timing_extremes(timings: &[SmtSolveTiming], count: usize) -> (Vec<&SmtSolveTiming>, Vec<&SmtSolveTiming>) {
    let mut sorted: Vec<_> = timings.iter().collect();
    sorted.sort_by_key(|timing| timing.duration);

    let fastest = sorted.iter().take(count).copied().collect();
    let slowest = sorted.iter().rev().take(count).copied().collect();
    (slowest, fastest)
}

#[cfg(feature = "smtperf")]
fn solve_timing_report(timings: &[SmtSolveTiming]) -> String {
    let (slowest, fastest) = solve_timing_extremes(timings, SMTPERF_EXTREME_COUNT);
    let mut msg = format!("SMT 未超时求解耗时样本总数: {}\n", timings.len());

    for (index, timing) in slowest.iter().enumerate() {
        msg += &format!(
            "SMT 最慢 #{}: {}us, operation: {:?}\n",
            index + 1,
            timing.duration.as_micros(),
            timing.operation,
        );
    }
    for (index, timing) in fastest.iter().enumerate() {
        msg += &format!(
            "SMT 最快 #{}: {}us, operation: {:?}\n",
            index + 1,
            timing.duration.as_micros(),
            timing.operation,
        );
    }

    msg
}

#[cfg(feature = "smtperf")]
pub(super) fn take_smtperf_report() -> String {
    let timings = SMT_SOLVE_TIMINGS.with(|timings| std::mem::take(&mut *timings.borrow_mut()));
    solve_timing_report(&timings)
}

#[cfg(feature = "smt-thread-interrupt")]
fn operation_timeout() -> Duration {
    OPERATION_TIMEOUT.get().copied().unwrap_or(Duration::from_secs(60))
}

pub fn configure_z3_timeout(timeout: Option<Duration>) {
    if let Some(timeout) = timeout {
        assert!(!timeout.is_zero(), "Z3 timeout must be non-zero");
        assert!(timeout.as_millis() > 0, "Z3 timeout must be at least one millisecond");
        if let Some(configured) = OPERATION_TIMEOUT.get() {
            assert_eq!(*configured, timeout, "Z3 timeout was configured more than once with different values");
        } else {
            OPERATION_TIMEOUT.set(timeout).expect("Z3 timeout configuration changed concurrently");
        }
    }
}

pub(super) fn timeout_error(
    operation: SmtOperation,
    source_loc: SourceLoc,
    operation_wall: Duration,
    dump: Arc<TimeoutSmtDump>,
) -> SmtError {
    #[cfg(feature = "smt-thread-interrupt")]
    {
        SmtError::Timeout(Arc::new(SmtTimeout {
            source_loc,
            operation,
            limit: operation_timeout(),
            operation_wall,
            dump,
        }))
    }
    #[cfg(not(feature = "smt-thread-interrupt"))]
    {
        drop((operation, source_loc, operation_wall, dump));
        panic!("local Z3 wrapper reported an interrupt")
    }
}

#[cfg(feature = "smt-thread-interrupt")]
fn thread_interrupt_call<T>(context: Z3_context, call: impl FnOnce() -> T) -> Result<T, Z3TimeoutError> {
    thread_interrupt_call_with_timeout(context, operation_timeout(), call)
}

#[cfg(feature = "smt-thread-interrupt")]
fn thread_interrupt_call_with_timeout<T>(
    context: Z3_context,
    duration: Duration,
    call: impl FnOnce() -> T,
) -> Result<T, Z3TimeoutError> {
    assert!(!duration.is_zero(), "thread-interrupt timeout must be non-zero");
    let interrupt = Z3InterruptHandle::from_context(context);
    const ACTIVE: u8 = 0;
    const COMPLETED: u8 = 1;
    const INTERRUPTING: u8 = 2;
    let call_state = Arc::new(std::sync::atomic::AtomicU8::new(ACTIVE));
    let result = std::thread::scope(|scope| {
        let (armed_tx, armed_rx) = std::sync::mpsc::sync_channel::<()>(0);
        let (completed_tx, completed_rx) = std::sync::mpsc::channel::<()>();
        let watchdog_state = Arc::clone(&call_state);
        let watchdog = scope.spawn(move || {
            let deadline = Instant::now().checked_add(duration).expect("thread-interrupt deadline overflow");
            armed_tx.send(()).expect("thread-interrupt caller disappeared before watchdog was armed");
            match completed_rx.recv_timeout(deadline.saturating_duration_since(Instant::now())) {
                Ok(()) => (),
                Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
                    if watchdog_state
                        .compare_exchange(
                            ACTIVE,
                            INTERRUPTING,
                            std::sync::atomic::Ordering::AcqRel,
                            std::sync::atomic::Ordering::Acquire,
                        )
                        .is_ok()
                    {
                        interrupt.interrupt();
                    }
                }
                Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => (),
            }
        });
        armed_rx.recv().expect("thread-interrupt watchdog exited before it was armed");
        let result = call();
        match call_state.compare_exchange(
            ACTIVE,
            COMPLETED,
            std::sync::atomic::Ordering::AcqRel,
            std::sync::atomic::Ordering::Acquire,
        ) {
            Ok(_) | Err(INTERRUPTING) => (),
            Err(COMPLETED) => panic!("thread-interrupt Z3 FFI completion was recorded twice"),
            Err(state) => panic!("thread-interrupt Z3 FFI entered an invalid state {}", state),
        }
        let _ = completed_tx.send(());
        watchdog.join().expect("thread-interrupt watchdog panicked");
        result
    });
    if call_state.load(std::sync::atomic::Ordering::Acquire) == INTERRUPTING {
        Err(Z3TimeoutError::Interrupted)
    } else {
        Ok(result)
    }
}

macro_rules! interruptible_z3_call {
    ($operation:expr, $source_loc:expr, $context:expr, $call:expr) => {{
        let started = Instant::now();
        let result = interruptible_z3_call!($context, $call);
        let elapsed = started.elapsed();
        record_path_smt_call($operation, $source_loc, elapsed, result.is_err());
        #[cfg(feature = "smtperf")]
        record_solve_result($operation, elapsed, &result);
        result
    }};
    ($context:expr, $call:expr) => {{
        #[cfg(feature = "smt-thread-interrupt")]
        {
            thread_interrupt_call($context, || $call)
        }
        #[cfg(not(feature = "smt-thread-interrupt"))]
        {
            Ok($call)
        }
    }};
}

#[allow(non_snake_case)]
pub(super) fn timeout_Z3_solver_check(
    context: Z3_context,
    solver: Z3_solver,
    source_loc: SourceLoc,
) -> Result<Z3_lbool, Z3TimeoutError> {
    interruptible_z3_call!(SmtOperation::CheckSat, source_loc, context, unsafe { Z3_solver_check(context, solver) })
}

#[allow(non_snake_case)]
pub(super) fn timeout_Z3_solver_check_assumptions(
    context: Z3_context,
    solver: Z3_solver,
    assumptions: &[Z3_ast],
    source_loc: SourceLoc,
) -> Result<Z3_lbool, Z3TimeoutError> {
    let count = assumptions.len().try_into().expect("too many Z3 check assumptions");
    interruptible_z3_call!(SmtOperation::CheckSatAssuming, source_loc, context, unsafe {
        Z3_solver_check_assumptions(context, solver, count, assumptions.as_ptr())
    })
}

#[allow(non_snake_case)]
pub(super) fn timeout_Z3_model_eval(
    context: Z3_context,
    model: Z3_model,
    ast: Z3_ast,
    model_completion: bool,
    result: &mut Z3_ast,
    source_loc: SourceLoc,
) -> Result<bool, Z3TimeoutError> {
    interruptible_z3_call!(SmtOperation::ModelEval, source_loc, context, unsafe {
        Z3_model_eval(context, model, ast, model_completion, result)
    })
}

#[cfg(all(test, not(feature = "smt-thread-interrupt")))]
mod direct_tests {
    use super::*;
    use crate::timeout::SmtDumpSource;

    struct TestDump;

    impl SmtDumpSource for TestDump {
        fn materialize(&self) -> Result<String, String> {
            Ok("(check-sat)\n".to_string())
        }
    }

    #[test]
    #[should_panic(expected = "local Z3 wrapper reported an interrupt")]
    fn direct_timeout_error_panics() {
        timeout_error(
            SmtOperation::CheckSat,
            SourceLoc::unknown(),
            Duration::from_secs(1),
            Arc::new(TimeoutSmtDump::new(Arc::new(TestDump))),
        );
    }
}

#[cfg(all(test, feature = "smt-thread-interrupt"))]
mod tests {
    use super::*;
    use crate::smt::{Config, Context};

    #[test]
    fn thread_timeout_waits_for_the_wrapped_call_to_return() {
        let context = Context::new(Config::new());
        let started = Instant::now();
        let result = thread_interrupt_call_with_timeout(context.z3_ctx, Duration::from_millis(10), || {
            std::thread::sleep(Duration::from_millis(40));
            7
        });
        assert_eq!(result, Err(Z3TimeoutError::Interrupted));
        assert!(started.elapsed() >= Duration::from_millis(40));
    }
}

#[cfg(all(test, feature = "smtperf"))]
mod smtperf_tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::smt::smtlib::Exp;
    use crate::smt::{Config, Context, SmtResult, Solver};
    use z3_sys::Z3_L_TRUE;

    #[test]
    fn smtperf_wrapper_only_records_completed_solve_times() {
        let completed = Ok(Z3_L_TRUE);
        let timed_out: Result<Z3_lbool, Z3TimeoutError> = Err(Z3TimeoutError::Interrupted);

        record_solve_result(SmtOperation::CheckSat, Duration::from_millis(7), &completed);
        record_solve_result(SmtOperation::CheckSatAssuming, Duration::from_secs(10), &timed_out);

        let report = take_smtperf_report();
        assert!(report.contains("SMT 未超时求解耗时样本总数: 1"));
        assert!(report.contains("7000us"));
        assert!(!report.contains("10000000us"));
    }

    #[test]
    fn smtperf_wrapper_selects_requested_slowest_and_fastest_solve_times() {
        let timings: Vec<_> = [9, 1, 7, 3, 5, 2, 8]
            .into_iter()
            .map(|millis| SmtSolveTiming { operation: SmtOperation::CheckSat, duration: Duration::from_millis(millis) })
            .collect();

        let (slowest, fastest) = solve_timing_extremes(&timings, 3);
        let slowest: Vec<_> = slowest.iter().map(|timing| timing.duration.as_millis()).collect();
        let fastest: Vec<_> = fastest.iter().map(|timing| timing.duration.as_millis()).collect();

        assert_eq!(slowest, vec![9, 8, 7]);
        assert_eq!(fastest, vec![1, 2, 3]);
    }

    #[test]
    fn smtperf_generic_wrapper_records_operation() {
        let result = interruptible_z3_call!(SmtOperation::ModelEval, std::ptr::null_mut(), true);

        assert_eq!(result, Ok(true));
        let report = take_smtperf_report();
        assert!(report.contains("SMT 未超时求解耗时样本总数: 1"));
        assert!(report.contains("operation: ModelEval"));
    }

    #[test]
    fn smtperf_solver_wrapper_collects_check_sat() {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);

        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        assert_eq!(solver.check_sat_with(&Exp::Bool(true), SourceLoc::unknown()), SmtResult::Sat);

        let report = take_smtperf_report();
        assert!(report.contains("SMT 未超时求解耗时样本总数: 2"));
        assert!(report.contains("operation: CheckSat"));
        assert!(report.contains("operation: CheckSatAssuming"));
    }
}
