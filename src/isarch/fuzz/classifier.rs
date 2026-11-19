//! 从已有检查点恢复一次，认证与快档共用同一批常驻求解器。
use super::corpus::Directory;
use super::io::{canonical_coordinates, write_json, write_lines};
use super::{Executor, LogFeedback, Mode, ReplayScheduler, Scheduler, Session};
use crate::isarch::resident::ResidentPath;
use crate::isarch::target::Target;
use isla_lib::bitvector::BV;
use isla_lib::executor::samples::{fast::FastFacts, profile, Sample};
use isla_lib::ir::SharedState;
use isla_lib::smt::{Config, Context, Solver};
use serde_json::{json, Value};
use std::time::Instant;

pub(super) type Job = (usize, Sample, bool);
pub(super) type Outcome = (usize, Option<Value>);
struct ModelExecutor {
    input: Vec<crossbeam::channel::Sender<Vec<Job>>>,
    output: crossbeam::channel::Receiver<Outcome>,
    pending: usize,
}
impl Executor for ModelExecutor {
    type Input = Job;
    type Output = Outcome;
    fn submit(&mut self, batch: Vec<Job>) {
        assert_eq!(self.pending, 0, "上一批尚未完成");
        self.pending = batch.len();
        for input in &self.input {
            input.send(batch.clone()).expect("判定线程异常退出");
        }
    }
    fn drain(&mut self) -> Vec<Outcome> {
        let mut partial = std::collections::BTreeMap::<usize, (usize, Option<Value>)>::new();
        for _ in 0..self.pending * self.input.len() {
            let (index, row) = self.output.recv().expect("判定线程异常退出");
            let (count, accepted) = partial.entry(index).or_default();
            *count += 1;
            if row.is_some() {
                assert!(accepted.is_none(), "输入 {index} 被多条路径接纳");
                *accepted = row;
            }
        }
        assert_eq!(partial.len(), self.pending, "判定结果编号数不符");
        let rows = partial
            .into_iter()
            .map(|(index, (count, row))| {
                assert_eq!(count, self.input.len(), "输入未经过全部路径分区");
                (index, row)
            })
            .collect();
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
        let batch_started = Instant::now();
        executor.submit(batch.iter().map(|i| (*i, samples[*i].clone(), certified)).collect());
        let completed = executor.drain();
        assert_eq!(completed.len(), batch.len());
        for ((index, row), expected) in completed.into_iter().zip(&batch) {
            assert_eq!(index, *expected);
            rows.push(row);
        }
        scheduler.on_batch_end(batch.len());
        eprintln!(
            "[FUZZ_PROGRESS] {}",
            json!({"certified":certified,"completed":rows.len(),"total":samples.len(),"batch_seconds":batch_started.elapsed().as_secs_f64()})
        );
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
        let sampling_input = if matches!(options.mode, Mode::ExportCorpus) { options.inputs.as_ref() } else { None };
        let sampling: super::sampling::Sampling = if let Some(input) = sampling_input {
            serde_json::from_reader(std::fs::File::open(input).expect("读取抽样配置失败")).expect("抽样配置非法")
        } else {
            Default::default()
        };
        let limits = super::sampling::limits(execution_limits);
        let next = std::sync::atomic::AtomicUsize::new(0);
        let results = std::sync::Mutex::new(Vec::new());
        let excluded_errors = std::sync::atomic::AtomicUsize::new(0);
        let selected_paths = paths.iter().enumerate().filter(|(i, _)| sampling.selected(*i)).count();
        // 跨路径并行；每条路径只枚举调用方规定的少量类。
        std::thread::scope(|scope| {
            for _ in 0..threads {
                let (paths, writer, limits, next, results, sampling, excluded_errors) =
                    (&paths, &writer, &limits, &next, &results, &sampling, &excluded_errors);
                scope.spawn(move || {
                    let context=Context::new(Config::new());
                    loop {
                        let i=next.fetch_add(1,std::sync::atomic::Ordering::Relaxed);
                        let Some(resident)=paths.get(i) else {break};
                        if !sampling.selected(i) {continue;}
                        if sampling.exclude_model_errors && !matches!(resident.path.terminal, isla_lib::executor::samples::Terminal::Normal) {
                            excluded_errors.fetch_add(1,std::sync::atomic::Ordering::Relaxed);
                            continue;
                        }
                        let began=Instant::now();
                        let mut solver=Solver::from_checkpoint(&context,resident.checkpoint.clone());
                        // 初始corpus只需要类内一个满足解；沿已有接口省去逐位最小化。
                        // 不向模型添加前态约束；未约束位仍由原生model completion给值。
                        let representative=isla_lib::executor::samples::SampleRandomization{seed:&|_,_|0,prepare:&|_,_,_,_|Ok(())};
                        let enumeration=crate::isarch::samples::export_cached_path_randomized(resident,&mut solver,shared,target,limits,Some(writer),None,Some(&representative))
                            .expect("缓存初始corpus枚举失败").expect("初始corpus必须开启枚举");
                        let row=json!({"path_signature":resident.signature,"enumeration":enumeration,"seconds":began.elapsed().as_secs_f64()});
                        eprintln!("[CORPUS_EXPORT] {}",json!({"path_index":i,"paths":paths.len(),"path_signature":resident.signature,"classes":enumeration["counted_classes"],"exported":enumeration["exported_samples"],"seconds":began.elapsed().as_secs_f64()}));
                        write_json(&output.join(format!("export-path-{}.json",resident.signature)),&row);
                        results.lock().unwrap().push(row);
                    }
                });
            }
        });
        let mut enumerations = results.into_inner().unwrap();
        enumerations.sort_by_key(|row| row["path_signature"].as_u64().unwrap());
        writer.finish();
        write_json(
            &output.join("sampling-summary.json"),
            &json!({
                "method":"路径签名排序后等步长选路，每条选中路径最多path_cap个解，class_cap=1",
                "sampling":sampling,"cache_paths":paths.len(),"selected_paths":selected_paths,
                "exported_paths":enumerations.len(),"excluded_model_error_paths":excluded_errors.load(std::sync::atomic::Ordering::Relaxed),
                "class_cap":1,"path_cap":limits.merge_enumeration.path_cap,"sample_stride":limits.merge_enumeration.sample_stride,
                "full_guard_class_corpus":false,"seconds":started.elapsed().as_secs_f64()
            }),
        );
        generated =
            isla_lib::executor::samples::SampleChecker::load(&path, None).expect("读取生成的初始 corpus 失败").samples;
        assert!(!generated.is_empty(), "缓存未生成任何 corpus entry");
        write_json(&output.join("initial-corpus-enumeration.json"), &enumerations);
        cache.stages.record(
            "initial_corpus_enumeration",
            started.elapsed().as_secs_f64(),
            json!({"entries":generated.len(),"class_cap":1,"sample_stride":limits.merge_enumeration.sample_stride,"path_cap":limits.merge_enumeration.path_cap}),
        );
        &generated
    };
    if matches!(options.mode, Mode::ReproducibilityProbe) {
        super::ablation::reproducibility::run(options, corpus, &paths, shared, target);
        return;
    }
    if matches!(options.mode, Mode::MutationProbe) {
        super::ablation::mutation_probe(options, corpus, &paths, shared, target);
        return;
    }
    if matches!(options.mode, Mode::ExportCorpus) {
        write_json(
            &output.join("export-complete.json"),
            &json!({"complete":true,"entries":corpus.len(),"paths":paths.len(),"class_cap":1,"full_guard_class_corpus":false,"seconds":cache.started.elapsed().as_secs_f64()}),
        );
        return;
    }
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
    let filter_started = Instant::now();
    let filters = if std::env::var_os("ISARCH_JUDGE_FULL_SCAN").is_some() {
        Vec::new()
    } else {
        paths.iter().map(|path| super::prefilter::Prefilter::new(path, shared)).collect::<Vec<_>>()
    };
    cache.stages.record(
        "judge_prefilter_compile",
        filter_started.elapsed().as_secs_f64(),
        json!({"paths":filters.len()}),
    );
    let index_seconds = index_start.elapsed().as_secs_f64();
    let (output_tx, output_rx) = crossbeam::channel::unbounded();
    let (ready_tx, ready_rx) = crossbeam::channel::unbounded();
    std::thread::scope(|scope| {
        let restore = Instant::now();
        let mut inputs = Vec::new();
        for worker in 0..threads {
            let (input_tx, input_rx) = crossbeam::channel::bounded::<Vec<Job>>(1);
            inputs.push(input_tx);
            let output_tx = output_tx.clone();
            let ready_tx = ready_tx.clone();
            let paths = &paths;
            let facts = &facts;
            let filters = &filters;
            scope.spawn(move || {
                ready_tx.send(()).unwrap();
                for batch in input_rx {
                    let batch_started = Instant::now();
                    profile::reset();
                    let mut checks = 0usize;
                    let mut screened = 0usize;
                    let mut restored = 0usize;
                    let mut accepted_count = 0usize;
                    let mut accepted = vec![None; batch.len()];
                    for path_index in (worker..paths.len()).step_by(threads) {
                        let path = &paths[path_index];
                        let fact = &facts[path_index];
                        let screen_span = profile::Span::new("prefilter");
                        let candidates = batch.iter().enumerate().filter_map(|(offset, (_, input, _))| {
                            if !filters.is_empty() && filters[path_index].rejects(input) {
                                screened += 1;
                                None
                            } else { Some(offset) }
                        }).collect::<Vec<_>>();
                        drop(screen_span);
                        if candidates.is_empty() { continue; }
                        restored += 1;
                        // 一次只保留一个路径的Z3上下文；释放后再检查下个路径，避免已实例化状态累计。
                        let restore_span = profile::Span::new("restore");
                        let mut config = Config::new();
                        config.set_param_value("model", "true");
                        let context = Context::new(config);
                        let mut solver = Solver::from_checkpoint(&context, path.checkpoint.clone());
                        drop(restore_span);
                        for offset in candidates {
                            let (_, input, certified) = &batch[offset];
                            checks += 1;
                            let consume = |sample: &mut Sample, model: &mut isla_lib::smt::Model<B>| {
                                let timing = profile::Span::new("isa_state");
                                sample.isa_state = crate::isarch::samples::isa_state(target, sample, model, shared)?;
                                drop(timing);
                                Ok(())
                            };
                            let row = if *certified {
                                path.path.judge(&mut solver, shared, input, &path.records, path.signature, consume)
                            } else {
                                path.path.classify(
                                    &mut solver,
                                    shared,
                                    input,
                                    &path.records,
                                    path.signature,
                                    fact,
                                    consume,
                                )
                            }
                            .expect("fuzz 判定失败");
                            if let Some(row) = row {
                                accepted_count += 1;
                                assert!(accepted[offset].is_none(), "输入 {} 被多条路径接纳", input.sample_id);
                                let mut row = serde_json::to_value(row).unwrap();
                                canonical_coordinates(&mut row);
                                accepted[offset] = Some(row);
                            }
                        }
                    }
                    eprintln!("[JUDGE_COST] {}", json!({"worker":worker,"inputs":batch.len(),"certified":batch[0].2,"checks":checks,"screened":screened,"restored":restored,"accepted":accepted_count,"seconds":batch_started.elapsed().as_secs_f64(),"stages":profile::take()}));
                    for ((index, _, _), row) in batch.into_iter().zip(accepted) {
                        output_tx.send((index, row)).unwrap();
                    }
                }
            });
        }
        drop(output_tx);
        drop(ready_tx);
        for _ in 0..threads {
            ready_rx.recv().expect("恢复线程异常退出");
        }
        let restore_seconds = restore.elapsed().as_secs_f64();
        cache.stages.record("judge_workers_ready", restore_seconds, json!({"threads":threads,"paths":paths.len(),"checkpoint_replay_in":"corpus_certification_and_mutant_judge"}));
        let mut executor = ModelExecutor { input: inputs, output: output_rx, pending: 0 };
        let started = Instant::now();
        let mut corpus_rows = classify(&mut executor, corpus, true, options.batch_size);
        let reconfirm_seconds = started.elapsed().as_secs_f64();
        let directory = if matches!(options.mode, Mode::Ablation) {
            Directory::reconfirm_sampled(&options.scenario, corpus, &corpus_rows, output)
        } else {
            Directory::reconfirm(&options.scenario, corpus, &corpus_rows, output)
        };
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
        if matches!(options.mode, Mode::Ablation) {
            super::ablation::run(
                options,
                corpus,
                &corpus_rows,
                &directory,
                &paths,
                shared,
                target,
                &mut executor,
                threads,
                reconfirm_seconds,
            );
            return;
        }
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
    let (first_tx, first_rx) = crossbeam::channel::unbounded();
    let (second_tx, second_rx) = crossbeam::channel::unbounded();
    let (output_tx, output_rx) = crossbeam::channel::unbounded();
    let mut executor = ModelExecutor { input: vec![first_tx, second_tx], output: output_rx, pending: 0 };
    let sample = super::tests::example_sample();
    executor.submit(vec![(0, sample.clone(), false), (1, sample, false)]);
    for receiver in [&first_rx, &second_rx] {
        let jobs = receiver.recv().unwrap();
        assert_eq!(jobs.len(), 2);
        assert_eq!(jobs[0].0, 0);
        assert_eq!(jobs[1].0, 1);
    }
    output_tx.send((1, Some(json!({"sample_id":1})))).unwrap();
    output_tx.send((0, None)).unwrap();
    output_tx.send((1, None)).unwrap();
    output_tx.send((0, Some(json!({"sample_id":0})))).unwrap();
    let rows = executor.drain();
    assert_eq!(rows[0], (0, Some(json!({"sample_id":0}))));
    assert_eq!(rows[1], (1, Some(json!({"sample_id":1}))));
    assert_eq!(executor.pending, 0);
}

#[cfg(test)]
mod sampling_tests {
    #[test]
    fn bounded_sampling_visits_each_path_and_keeps_configured_caps() {
        let sampling: super::super::sampling::Sampling =
            serde_json::from_str(r#"{"path_stride":4,"path_offset":1,"exclude_model_errors":true}"#).unwrap();
        assert_eq!((0..10).filter(|i| sampling.selected(*i)).collect::<Vec<_>>(), vec![1, 5, 9]);
        let mut limits = isla_lib::executor::ExecutionLimits::default();
        limits.merge_enumeration.path_cap = 2;
        limits.merge_enumeration.sample_stride = 3;
        let configured = super::super::sampling::limits(&limits);
        assert_eq!(configured.merge_enumeration.path_cap, 2);
        assert_eq!(configured.merge_enumeration.sample_stride, 3);
        assert_eq!(configured.merge_enumeration.class_cap, 1);
    }
}

#[cfg(test)]
mod partition_tests {
    use super::*;
    #[test]
    #[should_panic(expected = "被多条路径接纳")]
    fn partitioned_judge_rejects_two_accepted_paths() {
        let (first_tx, _) = crossbeam::channel::unbounded();
        let (second_tx, _) = crossbeam::channel::unbounded();
        let (output_tx, output) = crossbeam::channel::unbounded();
        let mut executor = ModelExecutor { input: vec![first_tx, second_tx], output, pending: 1 };
        output_tx.send((0, Some(json!({"sample_id":0})))).unwrap();
        output_tx.send((0, Some(json!({"sample_id":0})))).unwrap();
        executor.drain();
    }
}
