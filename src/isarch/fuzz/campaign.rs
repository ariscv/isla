//! 轮转且优先变异次数少的类；反馈只观察，决策不读取其分数。
use super::{
    corpus::{ClassIdentity, Directory},
    generation::{GenerationPool, Job},
    random_stream, Executor, Feedback, LogFeedback, Mode, Options, Oracle, Scheduler,
};
use crate::isarch::{resident::ResidentPath, target::Target};
use isla_lib::{bitvector::BV, executor::samples::Sample, ir::SharedState};
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
    threads: usize,
) -> (Vec<Sample>, Vec<Value>, Vec<Option<Value>>, Value) {
    let started = Instant::now();
    GenerationPool::with(paths, shared, target, threads, |generator| {
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
        let exhausted = 0;
        let mut generate_seconds = 0.0;
        let mut fast_seconds = 0.0;
        let mut certify_seconds = 0.0;
        let mut admitted = BTreeSet::new();
        let mut corpus_added = Vec::new();
        let mut hardware = options.difftest.clone().map(super::difftest::DifftestExecutor::new);
        let oracle = super::oracle::ThreeWayOracle;
        let mut hardware_results = Vec::new();
        let mut findings = Vec::new();
        let mut groups = BTreeMap::<String, Value>::new();
        let mut rules = BTreeMap::from([("R-XS-001".to_string(), 0usize)]);
        let mut agree = 0usize;
        let mut infrastructure = 0usize;
        let mut filtered = 0usize;
        let mut hardware_seconds = 0.0;
        loop {
            let batch = scheduler.next_batch(options.batch_size);
            if batch.is_empty() {
                break;
            }
            let begin = samples.len();
            let mut pending_hits = hits.clone();
            let generate_start = Instant::now();
            let mut jobs = Vec::new();
            let mut completed = Vec::new();
            for (offset, parent_index) in batch.iter().enumerate() {
                let id = (begin + offset) as u64;
                let mut rng = random_stream(options.random_seed, &options.scenario, id);
                if id as usize >= guided_budget {
                    let index = (rng.next_u64() % controls.len() as u64) as usize;
                    let mut sample = controls[index].clone();
                    sample.sample_id = id;
                    let mut record = control_records[index].clone();
                    record["sample_id"] = json!(id);
                    record["control_source_sample_id"] = control_records[index]["sample_id"].clone();
                    record["form"] = json!("recorded_control");
                    completed.push((id, sample, record));
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
                let target_index = targets.first().copied().unwrap_or(*parent_index);
                let identity = &classes[target_index];
                let neighbor = target_index != *parent_index;
                let mut record = json!({"sample_id":id,"operator":if neighbor {"B"} else {"A"},"form":if neighbor {"neighbor"} else {"within_class"},"parent_sample_id":parent.sample_id,"parent_path_signature":parent.path_signature,"parent_class_id":parent.class_id,"target_identity":identity});
                if use_neighbor && !neighbor {
                    record["schedule_reason"] = json!("邻类额度已用完");
                }
                pending_hits[target_index] += 1;
                attempts += 1;
                jobs.push(Job { target_index, parent: parent.clone(), record, rng });
            }
            generator.submit(jobs);
            completed.extend(generator.drain());
            completed.sort_by_key(|(id, _, _)| *id);
            for (offset, (id, sample, record)) in completed.into_iter().enumerate() {
                assert_eq!(id as usize, begin + offset);
                samples.push(sample);
                records.push(record);
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
                    (options.certify_all
                        || hardware.is_some()
                        || (!directory.classes.contains_key(&key) && !admitted.contains(&key)))
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
            if let Some(hardware) = &mut hardware {
                let execution_started = Instant::now();
                hardware.submit(
                    rows.iter()
                        .enumerate()
                        .filter_map(|(i, row)| {
                            let row = row.as_ref()?;
                            assert_eq!(records[begin + i]["actual_certified"], true, "上硬件前必须认证");
                            Some((begin + i, serde_json::from_value(row["sample"].clone()).unwrap()))
                        })
                        .collect(),
                );
                let results = hardware.drain();
                hardware_seconds += execution_started.elapsed().as_secs_f64();
                for (index, observed) in results {
                    let result = &rows[index - begin].as_ref().unwrap()["sample"]["result"];
                    let exception = result["value"]["struct"]
                        .as_object()
                        .and_then(|fields| fields.values().find_map(|v| v["ctor"].as_str()));
                    let cause = match exception {
                        None => 0,
                        Some("E_Load_Access_Fault") => 5,
                        Some("E_SAMO_Access_Fault") => 7,
                        Some("E_Load_Page_Fault") => 13,
                        Some("E_SAMO_Page_Fault") => 15,
                        Some(other) => panic!("未登记的 Isla 异常：{other}"),
                    };
                    if let Some(mut finding) = oracle.compare(&json!({"isla_cause":cause}), &observed) {
                        finding["sample_id"] = json!(index);
                        let identity = records[index]["actual_identity"].clone();
                        let key = json!({"target_class":identity,"fields":finding["fields"],"phase":finding["phase"]});
                        finding["group_key"] = key.clone();
                        let group = groups
                            .entry(serde_json::to_string(&key).unwrap())
                            .or_insert_with(|| json!({"key":key,"count":0,"representative":index}));
                        group["count"] = json!(group["count"].as_u64().unwrap() + 1);
                        if finding["filtered"] == true {
                            filtered += 1;
                            *rules.entry(finding["rule_id"].as_str().unwrap().into()).or_default() += 1;
                        }
                        if finding["infrastructure"] == true {
                            infrastructure += 1;
                        }
                        feedback.on_mismatch(index as u64, &finding);
                        findings.push(finding);
                    } else {
                        agree += 1;
                    }
                    hardware_results.push(observed);
                }
                // 所有状态只在整批结果收齐后落盘。
                super::io::write_lines(&options.output.join("difftest-results.jsonl"), &hardware_results);
                super::io::write_lines(&options.output.join("findings.jsonl"), &findings);
                super::io::write_json(
                    &options.output.join("findings-summary.json"),
                    &json!({"executed":hardware_results.len(),"agree":agree,"mismatch":findings.len()-infrastructure,"filtered":filtered,"new_disagreements":findings.len()-infrastructure-filtered,"infrastructure_failures":infrastructure,"rule_counts":rules,"groups":groups.values().collect::<Vec<_>>() }),
                );
            }
            judged.extend(rows);
            scheduler.on_batch_end(batch.len());
            if hardware.is_some() && super::difftest::cancelled_requested() {
                break;
            }
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
            json!({"campaign_seconds":started.elapsed().as_secs_f64(),"generate_seconds":generate_seconds,"fast_seconds":fast_seconds,"hardware_seconds":hardware_seconds,"certify_seconds":certify_seconds,"solver_attempts":attempts,"exhausted_requests":exhausted,"certified":certifications.len(),"corpus_added":corpus_added.len()}),
        )
    })
}
