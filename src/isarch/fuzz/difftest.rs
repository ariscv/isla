//! 有界批次队列与 Python worker 池；按输入编号收齐，取消时清理进程树。
use super::{io, Executor};
use isla_lib::executor::samples::Sample;
use serde_json::{json, Value};
use std::os::unix::process::CommandExt;
use std::{
    path::PathBuf,
    process::Command,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
    thread::JoinHandle,
    time::{Duration, Instant},
};

static CANCELLED: AtomicBool = AtomicBool::new(false);
static ACTIVE: AtomicBool = AtomicBool::new(false);
extern "C" fn cancelled(signal: libc::c_int) {
    assert!(signal == libc::SIGINT || signal == libc::SIGTERM);
    CANCELLED.store(true, Ordering::SeqCst);
}

#[derive(Clone, Debug)]
pub struct Config {
    pub worker: PathBuf,
    pub profile: PathBuf,
    pub lock: PathBuf,
    pub files: PathBuf,
    pub observer: PathBuf,
    pub output: PathBuf,
    pub workers: usize,
    pub timeout: u64,
}

pub(super) fn cancelled_requested() -> bool {
    CANCELLED.load(Ordering::SeqCst)
}

pub struct DifftestExecutor {
    input: Option<crossbeam::channel::Sender<(usize, Sample)>>,
    output: crossbeam::channel::Receiver<(usize, Value)>,
    pending: usize,
    stop: Arc<AtomicBool>,
    workers: Vec<JoinHandle<()>>,
    handlers: Vec<(i32, libc::sigaction)>,
    subreaper: i32,
}

// 子进程可能自行 setsid；只杀 worker 所在进程组不能覆盖 emu。
fn descendants(pid: i32, out: &mut Vec<i32>) {
    let path = format!("/proc/{pid}/task/{pid}/children");
    match std::fs::read_to_string(path) {
        Ok(children) => {
            for child in children.split_whitespace() {
                let child = child.parse::<i32>().unwrap();
                descendants(child, out);
                out.push(child);
            }
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => (),
        Err(error) => panic!("读取所属进程树失败：{error}"),
    }
}

fn stop_process(child: &mut std::process::Child) {
    let mut owned = Vec::new();
    descendants(child.id() as i32, &mut owned);
    unsafe {
        libc::kill(child.id() as i32, libc::SIGTERM);
    }
    let grace = Instant::now();
    while grace.elapsed() < Duration::from_millis(500) {
        if child.try_wait().unwrap().is_some() {
            break;
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    for pid in &owned {
        unsafe {
            libc::kill(*pid, libc::SIGKILL);
        }
    }
    unsafe {
        libc::kill(-(child.id() as i32), libc::SIGKILL);
    }
    child.wait().expect("回收 Python worker 失败");
    let started = Instant::now();
    for pid in owned {
        loop {
            let result = unsafe { libc::waitpid(pid, std::ptr::null_mut(), libc::WNOHANG) };
            if result == pid || result == -1 {
                break;
            }
            assert!(started.elapsed() < Duration::from_secs(5), "子进程未能退出：{pid}");
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}

fn run(config: &Config, index: usize, sample: &Sample, stop: &AtomicBool) -> Value {
    let directory = config.output.join(format!("input-{index:06}"));
    std::fs::create_dir_all(&directory).unwrap();
    let input = directory.join("certified.jsonl");
    io::write_lines(&input, &[sample]);
    let log = std::fs::File::create(directory.join("worker.log")).unwrap();
    let mut command = Command::new("python3");
    command
        .arg(&config.worker)
        .args(["--input"])
        .arg(&input)
        .arg("--profile")
        .arg(&config.profile)
        .arg("--lock")
        .arg(&config.lock)
        .arg("--files")
        .arg(&config.files)
        .arg("--observer")
        .arg(&config.observer)
        .arg("--output")
        .arg(&directory)
        .arg("--timeout")
        .arg(config.timeout.to_string())
        .env("PYTHONDONTWRITEBYTECODE", "1")
        .env("TMPDIR", &directory)
        .stdout(log.try_clone().unwrap())
        .stderr(log)
        .process_group(0);
    let failure = |bucket: &str, reason: String| json!({"sample_id":sample.sample_id,"bucket":bucket,"reason":reason,"agree":false,"isla_cause":Value::Null,"xs_cause":Value::Null,"nemu_cause":Value::Null,"isla_consistent_side":"unobserved","phase":"worker","mismatch":{"filtered":false,"known_rule":Value::Null,"group_key":Value::Null},"elf_sha256":Value::Null});
    if stop.load(Ordering::SeqCst) || CANCELLED.load(Ordering::SeqCst) {
        return failure("cancelled", "批次已取消".into());
    }
    let parent_pid = std::process::id() as libc::pid_t;
    unsafe {
        command.pre_exec(move || {
            if libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGTERM) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            if libc::getppid() != parent_pid {
                libc::_exit(1);
            }
            Ok(())
        });
    }
    let mut child = command.spawn().expect("无法启动 Python worker");
    let started = Instant::now();
    let result = loop {
        if stop.load(Ordering::SeqCst) || CANCELLED.load(Ordering::SeqCst) {
            stop_process(&mut child);
            break failure("cancelled", "批次已取消，已清理进程树".into());
        }
        if started.elapsed() > Duration::from_secs(config.timeout + 30) {
            stop_process(&mut child);
            break failure("timeout", "Python worker 超时，已清理进程树".into());
        }
        if let Some(status) = child.try_wait().unwrap() {
            if status.success() {
                let value: Value = serde_json::from_reader(
                    std::fs::File::open(directory.join("result.json")).expect("worker 缺少 result.json"),
                )
                .expect("worker 结果 JSON 损坏");
                assert_eq!(value["sample_id"], sample.sample_id);
                break value;
            }
            // 外部构建／运行失败保留为执行结果，绝不记为一致或套用窄规则。
            stop_process(&mut child);
            break failure("worker-error", format!("Python worker 退出 {status}，见 worker.log"));
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    io::write_json(&directory.join("result.json"), &result);
    result
}

impl DifftestExecutor {
    pub fn new(config: Config) -> Self {
        assert!((1..=12).contains(&config.workers), "emu 并发数必须在 1 到 12 之间");
        assert!((1..=600).contains(&config.timeout));
        assert!(!ACTIVE.swap(true, Ordering::SeqCst), "一个进程只能持有一个硬件执行池");
        CANCELLED.store(false, Ordering::SeqCst);
        let mut handlers = Vec::new();
        let mut subreaper = 0;
        unsafe {
            assert_eq!(libc::prctl(libc::PR_GET_CHILD_SUBREAPER, &mut subreaper), 0);
            assert_eq!(libc::prctl(libc::PR_SET_CHILD_SUBREAPER, 1), 0);
            for signal in [libc::SIGINT, libc::SIGTERM] {
                let mut action: libc::sigaction = std::mem::zeroed();
                let mut previous: libc::sigaction = std::mem::zeroed();
                action.sa_sigaction = cancelled as *const () as usize;
                libc::sigemptyset(&mut action.sa_mask);
                assert_eq!(libc::sigaction(signal, &action, &mut previous), 0);
                handlers.push((signal, previous));
            }
        }
        let (input_tx, input_rx) = crossbeam::channel::bounded::<(usize, Sample)>(config.workers * 2);
        let (output_tx, output) = crossbeam::channel::unbounded();
        let stop = Arc::new(AtomicBool::new(false));
        let workers = (0..config.workers)
            .map(|_| {
                let input_rx = input_rx.clone();
                let output_tx = output_tx.clone();
                let stop = stop.clone();
                let config = config.clone();
                std::thread::spawn(move || {
                    for (index, sample) in input_rx {
                        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            run(&config, index, &sample, &stop)
                        }));
                        match result {
                            Ok(result) => {
                                if output_tx.send((index, result)).is_err() {
                                    break;
                                }
                            }
                            Err(_) => {
                                stop.store(true, Ordering::SeqCst);
                                output_tx.send((index, json!({"internal_error":true}))).unwrap();
                            }
                        }
                    }
                })
            })
            .collect();
        Self { input: Some(input_tx), output, pending: 0, stop, workers, handlers, subreaper }
    }
}
impl Executor for DifftestExecutor {
    type Input = (usize, Sample);
    type Output = (usize, Value);
    fn submit(&mut self, batch: Vec<Self::Input>) {
        assert_eq!(self.pending, 0, "上一批硬件结果尚未收齐");
        self.pending = batch.len();
        for input in batch {
            self.input.as_ref().unwrap().send(input).expect("硬件 worker 异常退出");
        }
    }
    fn drain(&mut self) -> Vec<Self::Output> {
        let mut results =
            (0..self.pending).map(|_| self.output.recv().expect("硬件 worker 异常退出")).collect::<Vec<_>>();
        assert!(!results.iter().any(|(_, row)| row["internal_error"] == true), "硬件 worker 内部不变量违反");
        results.sort_by_key(|r| r.0);
        self.pending = 0;
        results
    }
}
impl Drop for DifftestExecutor {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::SeqCst);
        drop(self.input.take());
        for worker in self.workers.drain(..) {
            worker.join().expect("硬件 worker 异常退出");
        }
        unsafe {
            for (signal, action) in &self.handlers {
                assert_eq!(libc::sigaction(*signal, action, std::ptr::null_mut()), 0);
            }
            assert_eq!(libc::prctl(libc::PR_SET_CHILD_SUBREAPER, self.subreaper), 0);
        }
        ACTIVE.store(false, Ordering::SeqCst);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn executor_orders_results_and_cancels_independent_process_groups() {
        let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join(format!("output/fuzz-step4/unit-process-{}-{nonce}", std::process::id()));
        std::fs::create_dir_all(&root).unwrap();
        let worker = root.join("fake.py");
        std::fs::write(
            &worker,
            r#"import argparse,json,pathlib,subprocess,sys,time,os,signal
p=argparse.ArgumentParser()
for key in ['input','profile','lock','files','observer','output','timeout']:p.add_argument('--'+key)
a=p.parse_args();d=pathlib.Path(a.output);s=json.loads(pathlib.Path(a.input).read_text());i=s['sample_id']
if i==99:
 signal.signal(signal.SIGTERM,signal.SIG_IGN)
 c=subprocess.Popen([sys.executable,'-c','import time;time.sleep(300)'],start_new_session=True)
 (d/'child.pid').write_text(str(c.pid));time.sleep(300)
else:
 time.sleep((3-i)*.02)
 (d/'result.json').write_text(json.dumps(dict(sample_id=i,agree=True)))
"#,
        )
        .unwrap();
        let config = Config {
            worker,
            profile: root.join("profile"),
            lock: root.join("lock"),
            files: root.join("files"),
            observer: root.join("observer"),
            output: root.clone(),
            workers: 2,
            timeout: 1,
        };
        let mut executor = DifftestExecutor::new(config.clone());
        let sample = super::super::tests::example_sample();
        executor.submit(
            (0..3)
                .map(|id| {
                    let mut sample = sample.clone();
                    sample.sample_id = id;
                    (id as usize, sample)
                })
                .collect(),
        );
        assert_eq!(executor.drain().iter().map(|r| r.0).collect::<Vec<_>>(), vec![0, 1, 2]);
        let mut sleeping = sample.clone();
        sleeping.sample_id = 99;
        executor.submit(vec![(99, sleeping)]);
        let pid_path = root.join("input-000099/child.pid");
        let started = Instant::now();
        while !pid_path.exists() {
            assert!(started.elapsed() < Duration::from_secs(5));
            std::thread::sleep(Duration::from_millis(10));
        }
        let pid = std::fs::read_to_string(pid_path).unwrap().parse::<i32>().unwrap();
        unsafe {
            libc::raise(libc::SIGTERM);
        }
        assert_eq!(executor.drain()[0].1["bucket"], "cancelled");
        drop(executor);
        assert_eq!(unsafe { libc::kill(pid, 0) }, -1, "取消后不能遗留子进程或僵尸进程");
        let timeout_root = root.join("timeout");
        let mut timeout_config = config;
        timeout_config.output = timeout_root.clone();
        let mut executor = DifftestExecutor::new(timeout_config);
        let mut sleeping = sample;
        sleeping.sample_id = 99;
        executor.submit(vec![(99, sleeping)]);
        assert_eq!(executor.drain()[0].1["bucket"], "timeout");
        let pid = std::fs::read_to_string(timeout_root.join("input-000099/child.pid")).unwrap().parse::<i32>().unwrap();
        drop(executor);
        assert_eq!(unsafe { libc::kill(pid, 0) }, -1, "超时后不能遗留独立进程组");
        // 单独验证直接回收一个普通会话。
        let mut child =
            Command::new("python3").arg("-c").arg("import time;time.sleep(300)").process_group(0).spawn().unwrap();
        let pid = child.id() as i32;
        stop_process(&mut child);
        assert_eq!(unsafe { libc::kill(pid, 0) }, -1);
    }
}
