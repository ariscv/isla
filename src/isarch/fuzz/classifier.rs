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
    mut cache: crate::isarch::path_cache::Run<B>,
    execution_limits: &isla_lib::executor::ExecutionLimits,
) {
    assert!(!paths.is_empty(), "fuzz 没有完成路径");
    assert!(threads > 0);
    paths.sort_by_key(|p| p.signature);
    let options = &session.options;
    let output = &options.output;
    let generated;
    let corpus = if options.corpus.is_some() {
        &session.corpus
    } else {
        assert!(cache.loaded.is_some(), "初始 corpus 只从缓存生成");
        let started = Instant::now();
        let path = output.join("initial-corpus.jsonl");
        let writer =
            isla_lib::executor::samples::outputs::SampleOutputs::open(&[isla_lib::config::SampleOutputConfig {
                format: isla_lib::config::SampleOutputFormat::V1Jsonl,
                path: path.clone(),
            }]);
        let mut limits = execution_limits.clone();
        limits.merge_enumeration.enabled = true;
        limits.merge_enumeration.mode = isla_lib::config::MergeEnumerationMode::Samples;
        limits.merge_enumeration.class_cap = 1;
        limits.merge_enumeration.sample_stride = 1;
        limits.merge_enumeration.enumeration_threads = limits.merge_enumeration.enumeration_threads.min(threads);
        limits.merge_enumeration.max_output_bytes = None;
        let context = Context::new(Config::new());
        let mut enumerations = Vec::new();
        for resident in &paths {
            let mut solver = Solver::from_checkpoint(&context, resident.checkpoint.clone());
            let enumeration = crate::isarch::samples::export_cached_path(
                resident,
                &mut solver,
                shared,
                target,
                &limits,
                Some(&writer),
                None,
            )
            .expect("缓存初始 corpus 枚举失败")
            .expect("初始 corpus 必须开启枚举");
            enumerations.push(json!({"path_signature":resident.signature,"enumeration":enumeration}));
        }
        writer.finish();
        generated =
            isla_lib::executor::samples::SampleChecker::load(&path, None).expect("读取生成的初始 corpus 失败").samples;
        assert!(!generated.is_empty(), "缓存未生成任何 corpus entry");
        write_json(&output.join("initial-corpus-enumeration.json"), &enumerations);
        cache.stages.record(
            "initial_corpus_enumeration",
            started.elapsed().as_secs_f64(),
            json!({"entries":generated.len(),"class_cap":1,"sample_stride":1}),
        );
        &generated
    };
    let index_start = Instant::now();
    let mut cache_timing = cache.loaded.as_mut().map(|loaded| std::mem::take(&mut loaded.timing)).unwrap_or_default();
    cache_timing.paths = paths.len();
    if cache.loaded.is_none() || cache.options.export_dag {
        let context = Context::new(Config::new());
        let started = Instant::now();
        cache_timing.dag_replay_seconds = super::dag::export(&paths, &context, shared, output);
        cache_timing.dag_seconds = started.elapsed().as_secs_f64() - cache_timing.dag_replay_seconds;
        cache.stages.record("dag", started.elapsed().as_secs_f64(), json!({"paths":paths.len(),"z3_replay_seconds":cache_timing.dag_replay_seconds,"export_seconds":cache_timing.dag_seconds}));
    }
    let facts_started = Instant::now();
    let facts = if let Some(loaded) = &cache.loaded {
        assert_eq!(
            paths.iter().map(|p| p.signature).collect::<Vec<_>>(),
            loaded.manifest.path_signatures,
            "缓存路径顺序变化"
        );
        if cache.options.recompute_facts {
            let recomputed = crate::isarch::path_cache::analyze(&paths, &mut cache_timing);
            let verified =
                recomputed.iter().cloned().map(Into::into).collect::<Vec<isla_lib::executor::path_cache::Facts>>();
            // false 表示未证明，允许读回后取得更强证明；缓存声称已证明的条件仍须逐项核对。
            assert_eq!(loaded.facts.len(), verified.len(), "缓存静态事实条目数变化");
            for (saved, current) in loaded.facts.iter().zip(&verified) {
                assert!(!saved.guard_unique || current.guard_unique, "缓存守卫唯一性证明重新分析不一致");
                assert!(!saved.post_unique || current.post_unique, "缓存后态唯一性证明重新分析不一致");
                assert!(!saved.simple_pre || current.simple_pre, "缓存前态形状证明重新分析不一致");
            }
            recomputed
        } else {
            loaded.facts.iter().cloned().map(Into::into).collect::<Vec<FastFacts>>()
        }
    } else {
        crate::isarch::path_cache::analyze(&paths, &mut cache_timing)
    };
    cache.stages.record("fast_facts", facts_started.elapsed().as_secs_f64(), json!({"paths":paths.len(),"recomputed":cache.loaded.is_none() || cache.options.recompute_facts,"z3_replay_seconds":cache_timing.facts_replay_seconds,"analysis_seconds":cache_timing.facts_seconds}));
    if cache.options.enabled() {
        let source = crate::isarch::path_cache::current_source();
        if cache.options.write.is_some() {
            crate::isarch::path_cache::save(
                &cache.options,
                &cache.clause,
                &paths,
                &facts,
                shared,
                target,
                &cache.summary,
                &source,
                &mut cache_timing,
                &cache.stages,
            );
        }
        crate::isarch::path_cache::write_provenance(
            output,
            cache.loaded.as_ref().map(|l| &l.manifest),
            &source,
            &cache.options,
        );
    }
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
        cache_timing.replay_seconds = restore_seconds;
        cache.stages.record("checkpoint_restore", restore_seconds, json!({"threads":threads,"paths":paths.len()}));
        let mut executor = ModelExecutor { input: input_tx, output: output_rx, pending: 0 };
        let started = Instant::now();
        let mut corpus_rows = classify(&mut executor, corpus, true, options.batch_size);
        let reconfirm_seconds = started.elapsed().as_secs_f64();
        let directory = Directory::reconfirm(&options.scenario, corpus, &corpus_rows, output);
        for row in corpus_rows.iter_mut().flatten() {
            let identity = directory.identity(&options.scenario, row);
            row["sample"]["class_id"] = json!(directory.classes[&identity].0);
        }
        write_lines(
            &output.join("corpus-judged.jsonl"),
            &corpus_rows.iter().map(|r| r.as_ref().unwrap()).collect::<Vec<_>>(),
        );
        cache.stages.record(
            "corpus_certification",
            started.elapsed().as_secs_f64(),
            json!({"entries":corpus.len(),"certified":true}),
        );
        let mut feedback = LogFeedback::default();
        cache_timing.to_campaign_seconds = cache.started.elapsed().as_secs_f64();
        write_json(&output.join("path-cache-timing.json"), &cache_timing);
        eprintln!("[PATH_CACHE_READY] {}", serde_json::to_string(&cache_timing).unwrap());
        cache.stages.record("campaign_start", 0.0, json!({"to_campaign_seconds":cache_timing.to_campaign_seconds}));
        let started = Instant::now();
        let (samples, records, mut judged, campaign_timing) = if matches!(options.mode, Mode::Campaign) {
            super::campaign::run(
                options,
                corpus,
                &directory,
                &paths,
                shared,
                target,
                &mut executor,
                &mut feedback,
                threads,
            )
        } else {
            let (samples, records, audit) = super::replay::prepare(options, corpus);
            write_json(&output.join("input-audit.json"), &audit);
            let judged = classify(&mut executor, &samples, options.certify_all, options.batch_size);
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
        cache.stages.record(
            "campaign_end",
            started.elapsed().as_secs_f64(),
            json!({"mutants":samples.len(),"corpus":corpus.len()}),
        );
        eprintln!(
            "[FUZZ_COMPLETE] {}",
            json!({"corpus":corpus.len(),"mutants":samples.len(),"judge_seconds":judge_seconds})
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
