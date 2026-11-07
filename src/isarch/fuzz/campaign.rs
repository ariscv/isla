//! 轮转且优先变异次数少的类；反馈只观察，决策不读取其分数。
use super::{
    corpus::{ClassIdentity, Directory},
    mutator::SolverMutator,
    random_stream, Executor, Feedback, LogFeedback, Mode, Mutator, Options, Scheduler,
};
use crate::isarch::{resident::ResidentPath, target::Target};
use isla_lib::{
    bitvector::BV,
    executor::samples::Sample,
    ir::SharedState,
    smt::{Config, Context},
};
use rand::RngCore;
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

pub struct ClassScheduler {
    counts: Vec<usize>,
    cursor: usize,
    position: usize,
    total: usize,
}
impl ClassScheduler {
    pub fn new(classes: usize, total: usize) -> Self {
        assert!(classes > 0);
        Self { counts: vec![0; classes], cursor: 0, position: 0, total }
    }
}
impl Scheduler for ClassScheduler {
    fn next_batch(&self, limit: usize) -> Vec<usize> {
        assert!(limit > 0);
        let mut counts = self.counts.clone();
        let mut cursor = self.cursor;
        (0..limit.min(self.total - self.position))
            .map(|_| {
                let index = (0..counts.len())
                    .map(|offset| (cursor + offset) % counts.len())
                    .min_by_key(|i| counts[*i])
                    .unwrap();
                counts[index] += 1;
                cursor = (index + 1) % counts.len();
                index
            })
            .collect()
    }
    fn on_batch_end(&mut self, completed: usize) {
        for index in self.next_batch(completed) {
            self.counts[index] += 1;
            self.cursor = (index + 1) % self.counts.len();
        }
        self.position += completed;
        assert!(self.position <= self.total);
    }
}

pub fn neighbors(parent: &ClassIdentity, classes: &[ClassIdentity], hits: &[usize]) -> Vec<usize> {
    assert_eq!(classes.len(), hits.len());
    let mut candidates = classes
        .iter()
        .enumerate()
        .filter(|(_, key)| key.path_signature == parent.path_signature && *key != parent)
        .map(|(i, key)| {
            assert_eq!(parent.guard_vector.len(), key.guard_vector.len());
            (parent.guard_vector.bytes().zip(key.guard_vector.bytes()).filter(|(a, b)| a != b).count(), hits[i], i)
        })
        .collect::<Vec<_>>();
    candidates.sort();
    candidates.into_iter().map(|(_, _, i)| i).collect()
}

pub(super) fn run<B: BV>(
    options: &Options,
    corpus: &[Sample],
    directory: &Directory,
    paths: &[ResidentPath<B>],
    shared: &SharedState<B>,
    target: &dyn Target<B>,
    executor: &mut impl Executor<Input = super::classifier::Job, Output = super::classifier::Outcome>,
    feedback: &mut LogFeedback,
) -> (Vec<Sample>, Vec<Value>, Vec<Option<Value>>, Value) {
    let started = Instant::now();
    let mut config = Config::new();
    config.set_param_value("model", "true");
    let context = Context::new(config);
    let mutators = paths
        .iter()
        .map(|p| (p.signature, SolverMutator::new(p, &context, shared, target)))
        .collect::<BTreeMap<_, _>>();
    let classes = directory.classes.keys().cloned().collect::<Vec<_>>();
    let parents = corpus.iter().map(|s| (s.sample_id, s)).collect::<BTreeMap<_, _>>();
    let mut scheduler = ClassScheduler::new(classes.len(), options.budget);
    let (controls, control_records) = if options.control_percent > 0 {
        let mut replay_options = options.clone();
        replay_options.mode = Mode::ReplayLog;
        let (samples, records, audit) = super::replay::prepare(&replay_options, corpus);
        super::io::write_json(&options.output.join("control-input-audit.json"), &audit);
        (samples, records)
    } else {
        (Vec::new(), Vec::new())
    };
    let mut samples = Vec::new();
    let mut records = Vec::new();
    let mut judged = Vec::new();
    let mut certifications = Vec::new();
    let mut hits = vec![0; classes.len()];
    let quota = options.budget.div_ceil(classes.len());
    // 对照允许独立重复，统一在 A/B 之后产生；A 的历史因此覆盖此前全部 mutant。
    let guided_budget = options.budget - options.budget * options.control_percent / 100;
    let mut attempts = 0;
    let mut exhausted = 0;
    let mut generate_seconds = 0.0;
    let mut fast_seconds = 0.0;
    let mut certify_seconds = 0.0;
    let mut admitted = BTreeSet::new();
    let mut corpus_added = Vec::new();
    loop {
        let batch = scheduler.next_batch(options.batch_size);
        if batch.is_empty() {
            break;
        }
        let begin = samples.len();
        let mut pending_hits = hits.clone();
        let generate_start = Instant::now();
        for parent_index in &batch {
            let id = samples.len() as u64;
            let mut rng = random_stream(options.random_seed, &options.scenario, id);
            if id as usize >= guided_budget {
                let index = (rng.next_u64() % controls.len() as u64) as usize;
                let mut sample = controls[index].clone();
                sample.sample_id = id;
                let mut record = control_records[index].clone();
                record["sample_id"] = json!(id);
                record["control_source_sample_id"] = control_records[index]["sample_id"].clone();
                record["form"] = json!("recorded_control");
                samples.push(sample);
                records.push(record);
                continue;
            }
            let parent_identity = &classes[*parent_index];
            let parent = parents[&directory.classes[parent_identity].1];
            let candidates = neighbors(parent_identity, &classes, &pending_hits);
            let use_neighbor = rng.next_u64() & 1 != 0 && !candidates.is_empty();
            let targets = if use_neighbor {
                candidates.into_iter().filter(|i| pending_hits[*i] < quota).collect::<Vec<_>>()
            } else {
                vec![*parent_index]
            };
            let mut generated = None;
            for target_index in targets {
                let identity = &classes[target_index];
                let mut record = json!({"sample_id":id,"operator":if use_neighbor {"B"} else {"A"},"form":if use_neighbor {"neighbor"} else {"within_class"},"parent_sample_id":parent.sample_id,"parent_path_signature":parent.path_signature,"parent_class_id":parent.class_id,"target_identity":identity});
                let mutator = &mutators[&parent.path_signature];
                attempts += 1;
                if let Some(sample) = mutator.try_mutate(parent, &record, &mut rng) {
                    record["changes"] = json!(*mutator.changes.borrow());
                    pending_hits[target_index] += 1;
                    generated = Some((sample, record));
                    break;
                }
                exhausted += 1;
            }
            // 邻类额度用完是正常的调度状态；显式另发形态 A 请求，并记录原因。
            if generated.is_none() && use_neighbor {
                let mut record = json!({"sample_id":id,"operator":"A","form":"within_class","parent_sample_id":parent.sample_id,"parent_path_signature":parent.path_signature,"parent_class_id":parent.class_id,"target_identity":parent_identity,"schedule_reason":"邻类额度或可变空间已用完"});
                let mutator = &mutators[&parent.path_signature];
                attempts += 1;
                let sample = mutator.mutate(parent, &record, &mut rng);
                record["changes"] = json!(*mutator.changes.borrow());
                pending_hits[*parent_index] += 1;
                generated = Some((sample, record));
            }
            let (sample, record) = generated.expect("形态 A 的所有可变字段取值已耗尽");
            samples.push(sample);
            records.push(record);
            if samples.len() % 32 == 0 {
                eprintln!(
                    "[FUZZ_GENERATE] {}",
                    json!({"mutants":samples.len(),"budget":options.budget,"seconds":started.elapsed().as_secs_f64()})
                );
            }
        }
        generate_seconds += generate_start.elapsed().as_secs_f64();
        let fast_start = Instant::now();
        let mut rows = super::classifier::classify(executor, &samples[begin..], false, options.batch_size);
        fast_seconds += fast_start.elapsed().as_secs_f64();
        let certification_indices = rows
            .iter()
            .enumerate()
            .filter_map(|(i, row)| {
                let row = row.as_ref()?;
                let key = directory.identity(&options.scenario, row);
                (options.certify_all || (!directory.classes.contains_key(&key) && !admitted.contains(&key)))
                    .then_some(i)
            })
            .collect::<Vec<_>>();
        if !certification_indices.is_empty() {
            let cert_start = Instant::now();
            let inputs = certification_indices.iter().map(|i| samples[begin + i].clone()).collect::<Vec<_>>();
            let certified = super::classifier::classify(executor, &inputs, true, options.batch_size);
            certify_seconds += cert_start.elapsed().as_secs_f64();
            for (i, certified) in certification_indices.into_iter().zip(certified) {
                assert_eq!(rows[i], certified, "快档与认证档结果不同");
                records[begin + i]["actual_certified"] = json!(true);
                certifications.push(certified.as_ref().unwrap().clone());
                rows[i] = certified;
            }
        }
        for (i, row) in rows.iter_mut().enumerate() {
            let record = &mut records[begin + i];
            let actual = row.as_ref().map(|r| directory.identity(&options.scenario, r));
            record["actual_identity"] = json!(actual);
            if !record["target_identity"].is_null() {
                assert_eq!(record["target_identity"], json!(actual), "求解器 mutant 未命中目标类");
            }
            if let Some(key) = &actual {
                if let Some(index) = classes.iter().position(|k| k == key) {
                    hits[index] += 1;
                } else if admitted.insert(key.clone()) {
                    assert_eq!(record["actual_certified"], true, "新 corpus entry 必须先认证");
                    let sample = &row.as_ref().unwrap()["sample"];
                    corpus_added.push(sample.clone());
                    feedback.on_corpus_add(samples[begin + i].sample_id);
                }
                row.as_mut().unwrap()["sample"]["class_id"] = json!(directory.classes.get(key).map(|(id, _)| id));
            }
        }
        judged.extend(rows);
        scheduler.on_batch_end(batch.len());
        eprintln!(
            "[FUZZ_CAMPAIGN] {}",
            json!({"mutants":samples.len(),"budget":options.budget,"attempts":attempts,"exhausted":exhausted,"seconds":started.elapsed().as_secs_f64()})
        );
    }
    super::io::write_lines(&options.output.join("certified.jsonl"), &certifications);
    super::io::write_lines(&options.output.join("corpus-added.jsonl"), &corpus_added);
    (
        samples,
        records,
        judged,
        json!({"campaign_seconds":started.elapsed().as_secs_f64(),"generate_seconds":generate_seconds,"fast_seconds":fast_seconds,"certify_seconds":certify_seconds,"solver_attempts":attempts,"exhausted_requests":exhausted,"certified":certifications.len(),"corpus_added":corpus_added.len()}),
    )
}
