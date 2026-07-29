//! Z3 timeout 调用边界。
//!
//! 前半部分封装 thread-interrupt 状态与 watchdog；后半部分集中封装所有受保护的
//! `Z3_*` 调用。local/thread-interrupt 的执行差异只在这些 wrapper 内选择。

use std::convert::TryInto;
use std::sync::Arc;
use std::sync::OnceLock;
use std::time::Duration;
#[cfg(feature = "smt-thread-interrupt")]
use std::time::Instant;

use z3_sys::{
    Z3_ast, Z3_context, Z3_lbool, Z3_model, Z3_model_eval, Z3_solver, Z3_solver_check, Z3_solver_check_assumptions,
};

use crate::error::SmtError;
use crate::source_loc::SourceLoc;
#[cfg(feature = "smt-thread-interrupt")]
use crate::timeout::SmtTimeout;
use crate::timeout::{SmtOperation, TimeoutSmtDump};
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
pub(super) fn timeout_Z3_solver_check(context: Z3_context, solver: Z3_solver) -> Result<Z3_lbool, Z3TimeoutError> {
    interruptible_z3_call!(context, unsafe { Z3_solver_check(context, solver) })
}

#[allow(non_snake_case)]
pub(super) fn timeout_Z3_solver_check_assumptions(
    context: Z3_context,
    solver: Z3_solver,
    assumptions: &[Z3_ast],
) -> Result<Z3_lbool, Z3TimeoutError> {
    let count = assumptions.len().try_into().expect("too many Z3 check assumptions");
    interruptible_z3_call!(context, unsafe {
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
) -> Result<bool, Z3TimeoutError> {
    interruptible_z3_call!(context, unsafe { Z3_model_eval(context, model, ast, model_completion, result) })
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
