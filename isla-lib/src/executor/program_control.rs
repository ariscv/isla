//! solve-state 的整场墙钟与进程信号。信号处理器只记录首次请求。
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::mpsc;
use std::time::{Duration, Instant};

const INACTIVE: i32 = -2;
const TIMEOUT: i32 = -1;
const RUNNING: i32 = 0;
static STATE: AtomicI32 = AtomicI32::new(INACTIVE);

extern "C" fn request(reason: i32) {
    let _ = STATE.compare_exchange(RUNNING, reason, Ordering::Relaxed, Ordering::Relaxed);
}

pub fn active() -> bool {
    STATE.load(Ordering::Relaxed) != INACTIVE
}

pub fn reason() -> Option<&'static str> {
    match STATE.load(Ordering::Relaxed) {
        TIMEOUT => Some("program-timeout"),
        libc::SIGINT => Some("SIGINT"),
        libc::SIGTERM => Some("SIGTERM"),
        _ => None,
    }
}

thread_local! {
    static CHECKS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// 仅允许中断探索中的查询。收集器和缓存读回保留独立的验证 Context。
pub(crate) struct CheckScope(bool);
impl CheckScope {
    pub(crate) fn enter(enabled: bool) -> Self {
        Self(CHECKS.replace(enabled))
    }
}
impl Drop for CheckScope {
    fn drop(&mut self) {
        CHECKS.set(self.0);
    }
}
pub(crate) fn checks_enabled() -> bool {
    CHECKS.get()
}

pub struct ProgramControl {
    previous: Vec<(i32, libc::sigaction)>,
    timer: Option<(mpsc::Sender<()>, std::thread::JoinHandle<()>)>,
}

impl ProgramControl {
    pub fn install() -> Self {
        assert_eq!(STATE.swap(RUNNING, Ordering::Relaxed), INACTIVE);
        let mut previous = Vec::new();
        for signal in [libc::SIGINT, libc::SIGTERM] {
            unsafe {
                let mut action: libc::sigaction = std::mem::zeroed();
                let mut old = std::mem::zeroed();
                action.sa_sigaction = request as *const () as usize;
                action.sa_flags = libc::SA_RESTART;
                libc::sigemptyset(&mut action.sa_mask);
                assert_eq!(libc::sigaction(signal, &action, &mut old), 0);
                previous.push((signal, old));
            }
        }
        Self { previous, timer: None }
    }

    pub fn set_timeout(&mut self, start: Instant, limit: Duration) {
        let deadline = (!limit.is_zero()).then(|| start + limit);
        if deadline.is_some_and(|at| at <= Instant::now()) {
            request(TIMEOUT);
        }
        let (stop, receiver) = mpsc::channel();
        self.timer = Some((
            stop,
            std::thread::spawn(move || {
                // 信号处理器不能调用 Z3。重复通知覆盖登记 Context 到进入 FFI 的短窗口。
                loop {
                    let now = Instant::now();
                    if deadline.is_some_and(|at| at <= now) {
                        request(TIMEOUT);
                    }
                    if reason().is_some() {
                        crate::smt::interrupt_program_checks();
                    }
                    let tick = Duration::from_millis(20);
                    let wait = deadline.filter(|at| *at > now).map_or(tick, |at| (at - now).min(tick));
                    if receiver.recv_timeout(wait) != Err(mpsc::RecvTimeoutError::Timeout) {
                        return;
                    }
                }
            }),
        ));
    }
}

impl Drop for ProgramControl {
    fn drop(&mut self) {
        if let Some((stop, thread)) = self.timer.take() {
            drop(stop);
            thread.join().unwrap();
        }
        for (signal, previous) in &self.previous {
            unsafe { assert_eq!(libc::sigaction(*signal, previous, std::ptr::null_mut()), 0) };
        }
        STATE.store(INACTIVE, Ordering::Relaxed);
    }
}
