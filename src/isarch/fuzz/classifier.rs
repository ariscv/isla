//! 从已有检查点恢复一次，认证与快档共用同一批常驻求解器。
use super::corpus::Directory;
use super::io::{canonical_coordinates, write_json, write_lines};
use super::{Executor, LogFeedback, Mode, ReplayScheduler, Scheduler, Session};
use crate::isarch::resident::ResidentPath;
use crate::isarch::target::Target;
use isla_lib::bitvector::BV;
use isla_lib::executor::samples::{fast::FastFacts, Sample};
use isla_lib::ir::SharedState;
use isla_lib::smt::{Config, Context, Solver};
use serde_json::{json, Value};
use std::time::Instant;

pub(super) type Job = (usize, Sample, bool);
pub(super) type Outcome = (usize, Option<Value>);
struct ModelExecutor {
    input: crossbeam::channel::Sender<Job>,
    output: crossbeam::channel::Receiver<Outcome>,
    pending: usize,
}
impl Executor for ModelExecutor {
    type Input = Job;
    type Output = Outcome;
    fn submit(&mut self, batch: Vec<Job>) {
        assert_eq!(self.pending, 0, "上一批尚未完成");
        self.pending = batch.len();
        for job in batch {
            self.input.send(job).expect("判定线程异常退出");
        }
    }
    fn drain(&mut self) -> Vec<Outcome> {
        let mut rows = (0..self.pending).map(|_| self.output.recv().expect("判定线程异常退出")).collect::<Vec<_>>();
        rows.sort_by_key(|(index, _)| *index);
        self.pending = 0;
        rows
    }
}

pub(super) fn classify(
    executor: &mut impl Executor<Input = Job, Output = Outcome>,
    samples: &[Sample],
    certified: bool,
    batch_size: usize,
) -> Vec<Option<Value>> {
    let mut scheduler = ReplayScheduler::new(samples.len());
    let mut rows = Vec::new();
    loop {
        let batch = scheduler.next_batch(batch_size);
        if batch.is_empty() {
            break;
        }
        executor.submit(batch.iter().map(|i| (*i, samples[*i].clone(), certified)).collect());
        let completed = executor.drain();
        assert_eq!(completed.len(), batch.len());
        for ((index, row), expected) in completed.into_iter().zip(&batch) {
            assert_eq!(index, *expected);
            rows.push(row);
        }
        scheduler.on_batch_end(batch.len());
        eprintln!("[FUZZ_PROGRESS] {}", json!({"certified":certified,"completed":rows.len(),"total":samples.len()}));
    }
    rows
}

pub fn run<B: BV>(
    session: &Session,
    mut paths: Vec<ResidentPath<B>>,
    shared: &SharedState<B>,
    target: &dyn Target<B>,
    threads: usize,
    exploration_seconds: f64,
) {
    assert!(!paths.is_empty(), "fuzz 没有完成路径");
    assert!(threads > 0);
    paths.sort_by_key(|p| p.signature);
    let options = &session.options;
    let output = &options.output;
    let index_start = Instant::now();
    let facts = {
        let mut config = Config::new();
        config.set_param_value("model", "true");
        let context = Context::new(config);
        super::dag::export(&paths, &context, shared, output);
        paths
            .iter()
            .map(|p| {
                let mut solver = Solver::from_checkpoint(&context, p.checkpoint.clone());
                FastFacts::analyze(&p.path, &mut solver, &p.records).expect("路径静态事实分析失败")
            })
            .collect::<Vec<_>>()
    };
    write_json(
        &output.join("path-index.json"),
        &paths.iter().zip(&facts).map(|(p, f)| json!({"path_signature":p.signature,"facts":f})).collect::<Vec<_>>(),
    );
    let index_seconds = index_start.elapsed().as_secs_f64();
    let (input_tx, input_rx) = crossbeam::channel::bounded::<Job>(threads * 2);
    let (output_tx, output_rx) = crossbeam::channel::unbounded();
    let (ready_tx, ready_rx) = crossbeam::channel::unbounded();
    std::thread::scope(|scope| {
        let restore = Instant::now();
        for _ in 0..threads {
            let input_rx = input_rx.clone();
            let output_tx = output_tx.clone();
            let ready_tx = ready_tx.clone();
            let paths = &paths;
            let facts = &facts;
            scope.spawn(move || {
                let mut config = Config::new();
                config.set_param_value("model", "true");
                let context = Context::new(config);
                let mut solvers =
                    paths.iter().map(|p| Solver::from_checkpoint(&context, p.checkpoint.clone())).collect::<Vec<_>>();
                ready_tx.send(()).unwrap();
                for (index, input, certified) in input_rx {
                    let mut accepted = None;
                    for ((path, solver), fact) in paths.iter().zip(&mut solvers).zip(facts) {
                        let consume = |sample: &mut Sample, model: &mut isla_lib::smt::Model<B>| {
                            sample.isa_state = crate::isarch::samples::isa_state(target, sample, model, shared)?;
                            Ok(())
                        };
                        let row = if certified {
                            path.path.judge(solver, shared, &input, &path.records, path.signature, consume)
                        } else {
                            path.path.classify(solver, shared, &input, &path.records, path.signature, fact, consume)
                        }
                        .expect("fuzz 判定失败");
                        if let Some(row) = row {
                            assert!(accepted.is_none(), "输入 {} 被多条路径接纳", input.sample_id);
                            let mut row = serde_json::to_value(row).unwrap();
                            canonical_coordinates(&mut row);
                            accepted = Some(row);
                        }
                    }
                    output_tx.send((index, accepted)).unwrap();
                }
            });
        }
        drop(input_rx);
        drop(output_tx);
        drop(ready_tx);
        for _ in 0..threads {
            ready_rx.recv().expect("恢复线程异常退出");
        }
        let restore_seconds = restore.elapsed().as_secs_f64();
        let mut executor = ModelExecutor { input: input_tx, output: output_rx, pending: 0 };
        let started = Instant::now();
        let mut corpus_rows = classify(&mut executor, &session.corpus, true, options.batch_size);
        let reconfirm_seconds = started.elapsed().as_secs_f64();
        let directory = Directory::reconfirm(&options.scenario, &session.corpus, &corpus_rows, output);
        for row in corpus_rows.iter_mut().flatten() {
            let identity = directory.identity(&options.scenario, row);
            row["sample"]["class_id"] = json!(directory.classes[&identity].0);
        }
        write_lines(
            &output.join("corpus-judged.jsonl"),
            &corpus_rows.iter().map(|r| r.as_ref().unwrap()).collect::<Vec<_>>(),
        );
        let mut feedback = LogFeedback::default();
        let started = Instant::now();
        let (samples, records, mut judged, campaign_timing) = if matches!(options.mode, Mode::Campaign) {
            super::campaign::run(
                options,
                &session.corpus,
                &directory,
                &paths,
                shared,
                target,
                &mut executor,
                &mut feedback,
            )
        } else {
            let (samples, records, audit) = super::replay::prepare(options, &session.corpus);
            write_json(&output.join("input-audit.json"), &audit);
            let judged = classify(&mut executor, &samples, false, options.batch_size);
            (samples, records, judged, Value::Null)
        };
        let judge_seconds = started.elapsed().as_secs_f64();
        write_lines(&output.join("mutants.jsonl"), &samples);
        for row in judged.iter_mut().flatten() {
            let identity = directory.identity(&options.scenario, row);
            row["sample"]["class_id"] = json!(directory.classes.get(&identity).map(|(class_id, _)| class_id));
        }
        super::report::write(options, &directory, &samples, &records, &judged, &mut feedback);
        write_lines(&output.join("judged.jsonl"), &judged.iter().flatten().collect::<Vec<_>>());
        write_lines(
            &output.join("classified.jsonl"),
            &judged.iter().flatten().map(|r| &r["sample"]).collect::<Vec<_>>(),
        );
        write_lines(&output.join("observations.jsonl"), &feedback.rows);
        write_json(
            &output.join("timing.json"),
            &json!({"threads":threads,"exploration_seconds":exploration_seconds,"index_seconds":index_seconds,"restore_seconds":restore_seconds,"reconfirm_seconds":reconfirm_seconds,"judge_seconds":judge_seconds,"loop_seconds":started.elapsed().as_secs_f64(),"campaign":campaign_timing}),
        );
        eprintln!(
            "[FUZZ_COMPLETE] {}",
            json!({"corpus":session.corpus.len(),"mutants":samples.len(),"judge_seconds":judge_seconds})
        );
    });
}

#[cfg(test)]
pub(super) fn test_executor_order() {
    let (input_tx, input_rx) = crossbeam::channel::unbounded();
    let (output_tx, output_rx) = crossbeam::channel::unbounded();
    let mut executor = ModelExecutor { input: input_tx, output: output_rx, pending: 0 };
    let sample = super::tests::example_sample();
    executor.submit(vec![(0, sample.clone(), false), (1, sample, false)]);
    assert_eq!(input_rx.recv().unwrap().0, 0);
    assert_eq!(input_rx.recv().unwrap().0, 1);
    output_tx.send((1, Some(json!({"sample_id":1})))).unwrap();
    output_tx.send((0, None)).unwrap();
    let rows = executor.drain();
    assert_eq!(rows[0].0, 0);
    assert_eq!(rows[1].0, 1);
    assert_eq!(executor.pending, 0);
}
