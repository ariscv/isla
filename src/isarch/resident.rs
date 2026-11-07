//! M0：完成路径留在内存，恢复一次后重复调用现有 judge。
use super::target::Target;
use isla_lib::bitvector::BV;
use isla_lib::executor::samples::{profile, SampleChecker, SamplePath};
use isla_lib::executor::RegionMergeRecord;
use isla_lib::ir::SharedState;
use isla_lib::smt::{Checkpoint, Config, Context, Solver};
use isla_lib::timing::thread_cpu_time;
use serde_json::json;
use std::collections::BTreeMap;
use std::sync::mpsc;
use std::time::Instant;

#[path = "resident_fast.rs"]
mod fast;

pub struct ResidentPath<B: BV> {
    pub checkpoint: Checkpoint<B>,
    pub path: SamplePath<B>,
    pub records: Vec<RegionMergeRecord<B>>,
    pub signature: u64,
}

fn thread_cpu_seconds() -> f64 {
    thread_cpu_time().as_secs_f64()
}

pub fn run<B: BV>(
    mut paths: Vec<ResidentPath<B>>,
    checker: &SampleChecker,
    shared: &SharedState<B>,
    target: &dyn Target<B>,
    num_threads: usize,
    exploration_seconds: f64,
    fast: bool,
) {
    paths.sort_by_key(|path| path.signature);
    let status = std::fs::read_to_string("/proc/self/status").expect("读取 RSS 失败");
    let memory: Vec<_> =
        status.lines().filter(|line| line.starts_with("VmRSS:") || line.starts_with("VmHWM:")).collect();
    eprintln!(
        "[JUDGE_RESIDENT_SAVED] {}",
        json!({"paths":paths.len(), "exploration_seconds":exploration_seconds, "memory":memory})
    );
    assert!(!paths.is_empty(), "常驻 judge 没有完成路径");
    if fast {
        fast::run(&paths, checker, shared, target, num_threads);
        return;
    }
    let workers = num_threads.min(paths.len());
    assert!(workers > 0);
    let started = Instant::now();
    let (ready_tx, ready_rx) = mpsc::channel();
    let (done_tx, done_rx) = mpsc::channel();
    std::thread::scope(|scope| {
        let mut inputs = Vec::new();
        for worker in 0..workers {
            let (input_tx, input_rx) = mpsc::channel::<usize>();
            inputs.push(input_tx);
            let ready_tx = ready_tx.clone();
            let done_tx = done_tx.clone();
            let paths = &paths;
            scope.spawn(move || {
                profile::reset();
                let timing = profile::Span::new("context");
                let mut config = Config::new();
                config.set_param_value("model", "true");
                let context = Context::new(config);
                drop(timing);
                let mut restored = Vec::new();
                let mut timings = Vec::new();
                for path in paths.iter().skip(worker).step_by(workers) {
                    let start = Instant::now();
                    let cpu = thread_cpu_seconds();
                    let solver = Solver::from_checkpoint(&context, path.checkpoint.clone());
                    timings.push(json!({"path_signature":path.signature, "wall_seconds":start.elapsed().as_secs_f64(), "cpu_seconds":thread_cpu_seconds()-cpu}));
                    restored.push((path, solver));
                }
                ready_tx.send((timings, profile::take())).unwrap();
                for index in input_rx {
                    let cpu = thread_cpu_seconds();
                    let wall = Instant::now();
                    let mut by_path = Vec::new();
                    let outcome = restored.iter_mut().try_for_each(|(path, solver)| {
                        profile::reset();
                        let outcome = checker.judge_only(index, &path.path, solver, shared, path.signature, &path.records, |sample, model| {
                            sample.isa_state = super::samples::isa_state(target, sample, model, shared)?;
                            Ok(())
                        }).map(|judged| drop(judged));
                        by_path.push((path.signature, profile::take()));
                        outcome
                    });
                    let failed = outcome.is_err();
                    done_tx.send((thread_cpu_seconds()-cpu, wall.elapsed().as_secs_f64(), by_path, outcome)).unwrap();
                    if failed {
                        return;
                    }
                }
            });
        }
        drop(ready_tx);
        drop(done_tx);
        let mut restoration = Vec::new();
        let mut startup = profile::Measurements::new();
        for _ in 0..workers {
            let (paths, stages) = ready_rx.recv().expect("恢复线程异常退出");
            restoration.extend(paths);
            profile::add(&mut startup, &stages);
        }
        restoration.sort_by_key(|row| row["path_signature"].as_u64().unwrap());
        eprintln!(
            "[JUDGE_RESIDENT_RESTORED] {}",
            json!({"wall_seconds":started.elapsed().as_secs_f64(), "paths":restoration, "stages":startup})
        );
        let batch = Instant::now();
        let mut measurements = Vec::new();
        let mut total_cpu = 0.0;
        let mut stages = profile::Measurements::new();
        let mut critical_stages = profile::Measurements::new();
        let mut path_totals = BTreeMap::<u64, profile::Measurements>::new();
        let mut main_cpu = 0.0;
        for (index, sample) in checker.samples.iter().enumerate() {
            let wall = Instant::now();
            let main_start = thread_cpu_seconds();
            for input in &inputs {
                input.send(index).expect("判定线程异常退出");
            }
            let mut cpu = 0.0;
            let mut slowest = 0.0;
            let mut critical = profile::Measurements::new();
            let mut sample_stages = profile::Measurements::new();
            for _ in 0..workers {
                let (seconds, elapsed, by_path, outcome) = done_rx.recv().expect("判定线程异常退出");
                let mut worker_stages = profile::Measurements::new();
                for (signature, timings) in by_path {
                    profile::add(path_totals.entry(signature).or_default(), &timings);
                    profile::add(&mut worker_stages, &timings);
                }
                profile::add(&mut sample_stages, &worker_stages);
                if elapsed > slowest {
                    slowest = elapsed;
                    critical = worker_stages;
                }
                outcome.expect("常驻 judge 判定失败");
                cpu += seconds;
            }
            main_cpu += thread_cpu_seconds() - main_start;
            total_cpu += cpu;
            profile::add(&mut stages, &sample_stages);
            profile::add(&mut critical_stages, &critical);
            measurements.push(
                json!({"sample_id":sample.sample_id, "wall_seconds":wall.elapsed().as_secs_f64(), "cpu_seconds":cpu, "stages":sample_stages, "critical_stages":critical}),
            );
        }
        eprintln!(
            "[JUDGE_RESIDENT_MEASUREMENTS] {}",
            json!({"threads":num_threads, "workers":workers, "batch_wall_seconds":batch.elapsed().as_secs_f64(), "batch_cpu_seconds":total_cpu, "samples":measurements, "stages":stages, "critical_stages":critical_stages, "paths":path_totals, "main_cpu_seconds":main_cpu})
        );
    });
    eprintln!("[JUDGE_RESIDENT_REPORT] {}", checker.report());
}
