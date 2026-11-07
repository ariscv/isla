//! 快档按输入并行；每个线程持有全部路径，避免逐输入的全线程屏障。
use super::*;
use isla_lib::executor::samples::fast::FastFacts;

pub(super) fn run<B: BV>(
    paths: &[ResidentPath<B>],
    checker: &SampleChecker,
    shared: &SharedState<B>,
    target: &dyn Target<B>,
    num_threads: usize,
) {
    let started = Instant::now();
    let cpu = thread_cpu_seconds();
    let facts = {
        let mut config = Config::new();
        config.set_param_value("model", "true");
        let context = Context::new(config);
        paths
            .iter()
            .map(|path| {
                let mut solver = Solver::from_checkpoint(&context, path.checkpoint.clone());
                FastFacts::analyze(&path.path, &mut solver, &path.records).expect("路径静态事实分析失败")
            })
            .collect::<Vec<_>>()
    };
    eprintln!(
        "[JUDGE_RESIDENT_INDEX] {}",
        json!({"wall_seconds":started.elapsed().as_secs_f64(),
        "cpu_seconds":thread_cpu_seconds()-cpu,
        "paths":paths.iter().zip(&facts).map(|(path,facts)|json!({"path_signature":path.signature,"facts":facts})).collect::<Vec<_>>() })
    );
    let workers = num_threads.min(checker.samples.len().max(1));
    let started = Instant::now();
    let (ready_tx, ready_rx) = mpsc::channel();
    let (done_tx, done_rx) = mpsc::channel();
    let (input_tx, input_rx) = crossbeam::channel::bounded::<usize>(workers * 2);
    std::thread::scope(|scope| {
        for _ in 0..workers {
            let input_rx = input_rx.clone();
            let ready_tx = ready_tx.clone();
            let done_tx = done_tx.clone();
            let facts = &facts;
            scope.spawn(move || {
                profile::reset();
                let timing = profile::Span::new("context");
                let mut config = Config::new();
                config.set_param_value("model", "true");
                let context = Context::new(config);
                drop(timing);
                let mut restored = Vec::new();
                let mut timings = Vec::new();
                for path in paths {
                    let start = Instant::now();
                    let cpu = thread_cpu_seconds();
                    let solver = Solver::from_checkpoint(&context, path.checkpoint.clone());
                    timings.push(json!({"path_signature":path.signature,"wall_seconds":start.elapsed().as_secs_f64(),"cpu_seconds":thread_cpu_seconds()-cpu}));
                    restored.push(solver);
                }
                ready_tx.send((timings, profile::take())).unwrap();
                for index in input_rx {
                    let wall = Instant::now();
                    let cpu = thread_cpu_seconds();
                    let mut by_path = Vec::new();
                    let outcome = paths.iter().zip(&mut restored).zip(facts).try_for_each(|((path,solver),facts)| {
                        profile::reset();
                        let outcome = checker.classify_only(index, &path.path, solver, shared, path.signature,
                            &path.records, facts, |sample,model| {
                                sample.isa_state = super::super::samples::isa_state(target,sample,model,shared)?;
                                Ok(())
                            }).map(drop);
                        by_path.push((path.signature,profile::take()));
                        outcome
                    });
                    let failed = outcome.is_err();
                    done_tx.send((index,thread_cpu_seconds()-cpu,wall.elapsed().as_secs_f64(),by_path,outcome)).unwrap();
                    if failed { return; }
                }
            });
        }
        drop(input_rx);
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
            json!({"wall_seconds":started.elapsed().as_secs_f64(),"paths":restoration,"stages":startup})
        );
        let batch = Instant::now();
        for index in 0..checker.samples.len() {
            input_tx.send(index).expect("判定线程异常退出");
        }
        drop(input_tx);
        let mut measurements = Vec::new();
        let mut stages = profile::Measurements::new();
        let mut path_totals = BTreeMap::<u64, profile::Measurements>::new();
        let mut total_cpu = 0.0;
        for _ in 0..checker.samples.len() {
            let (index, cpu, wall, by_path, outcome) = done_rx.recv().expect("判定线程异常退出");
            outcome.expect("快档判定失败");
            total_cpu += cpu;
            let mut sample_stages = profile::Measurements::new();
            for (signature, timings) in by_path {
                profile::add(path_totals.entry(signature).or_default(), &timings);
                profile::add(&mut sample_stages, &timings);
            }
            profile::add(&mut stages, &sample_stages);
            measurements
                .push(json!({"sample_id":checker.samples[index].sample_id,"wall_seconds":wall,"cpu_seconds":cpu,
                "stages":sample_stages,"critical_stages":sample_stages}));
        }
        measurements.sort_by_key(|row| row["sample_id"].as_u64().unwrap());
        eprintln!(
            "[JUDGE_RESIDENT_MEASUREMENTS] {}",
            json!({"mode":"fast","threads":num_threads,"workers":workers,
            "batch_wall_seconds":batch.elapsed().as_secs_f64(),"batch_cpu_seconds":total_cpu,
            "samples":measurements,"stages":stages,"paths":path_totals})
        );
    });
    eprintln!("[JUDGE_RESIDENT_REPORT] {}", checker.report());
}
