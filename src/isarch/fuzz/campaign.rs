//! 在批次边界提交覆盖与评分；保留类轮转的无反馈基线。
use super::{
    corpus::{ClassIdentity, Directory},
    feedback::{CoverageFeedback, Feature},
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

pub struct FeedbackScheduler {
    counts: Vec<usize>,
    scores: Vec<f64>,
    position: usize,
    total: usize,
}
impl FeedbackScheduler {
    pub fn new(scores: Vec<f64>, total: usize) -> Self {
        assert!(!scores.is_empty());
        assert!(scores.iter().all(|s| s.is_finite() && *s > 0.0));
        Self { counts: vec![0; scores.len()], scores, position: 0, total }
    }
    pub fn set_scores(&mut self, scores: Vec<f64>) {
        assert_eq!(scores.len(), self.scores.len());
        assert!(scores.iter().all(|s| s.is_finite() && *s > 0.0));
        self.scores = scores;
    }
}
impl Scheduler for FeedbackScheduler {
    fn next_batch(&self, limit: usize) -> Vec<usize> {
        assert!(limit > 0);
        let mut counts = self.counts.clone();
        (0..limit.min(self.total - self.position))
            .map(|_| {
                let index = (0..counts.len())
                    .min_by(|a, b| {
                        ((counts[*a] + 1) as f64 / self.scores[*a])
                            .total_cmp(&((counts[*b] + 1) as f64 / self.scores[*b]))
                            .then(a.cmp(b))
                    })
                    .unwrap();
                counts[index] += 1;
                index
            })
            .collect()
    }
    fn on_batch_end(&mut self, completed: usize) {
        for index in self.next_batch(completed) {
            self.counts[index] += 1;
        }
        self.position += completed;
        assert!(self.position <= self.total);
    }
}

struct CorpusEntry {
    sample: Sample,
    feature: Feature,
    input_id: String,
    selections: usize,
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
        let initial_identities = corpus
            .iter()
            .map(|sample| classes.iter().find(|key| directory.classes[*key].1 == sample.sample_id).unwrap().clone())
            .collect::<Vec<_>>();
        let initial_features = super::feedback::extract(corpus, &initial_identities, &options.output);
        let mut coverage = CoverageFeedback::default();
        let mut entries = classes.iter().map(|_| Vec::<CorpusEntry>::new()).collect::<Vec<_>>();
        for ((sample, identity), feature) in corpus.iter().zip(&initial_identities).zip(initial_features) {
            coverage.observe(sample.sample_id, &feature);
            let index = classes.iter().position(|key| key == identity).unwrap();
            entries[index].push(CorpusEntry {
                sample: sample.clone(),
                feature,
                input_id: format!("initial:{}", sample.sample_id),
                selections: 0,
            });
        }
        let initial_coverage = coverage.summary();
        let mut scores = entries.iter().map(|list| coverage.score(&list[0].feature)).collect::<Vec<_>>();
        let mut weighted = FeedbackScheduler::new(scores.clone(), options.budget);
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
        let mut mutant_buckets = BTreeSet::new();
        let mut observations = Vec::new();
        let mut batch_scores = Vec::new();
        let mut corpus_added = Vec::new();
        let mut hardware = options.difftest.clone().map(super::difftest::DifftestExecutor::new);
        let oracle = super::oracle::ThreeWayOracle;
        let mut hardware_results = Vec::new();
        let mut hardware_timing = Vec::new();
        let mut findings = Vec::new();
        let mut groups = BTreeMap::<String, Value>::new();
        let mut rules = BTreeMap::from([("R-XS-001".to_string(), 0usize)]);
        let mut agree = 0usize;
        let mut infrastructure = 0usize;
        let mut filtered = 0usize;
        let mut hardware_seconds = 0.0;
        loop {
            let batch = if options.feedback {
                weighted.next_batch(options.batch_size)
            } else {
                scheduler.next_batch(options.batch_size)
            };
            if batch.is_empty() {
                break;
            }
            let begin = samples.len();
            let mut pending_hits = hits.clone();
            let mut pending_selections = entries
                .iter()
                .map(|list| list.iter().map(|entry| entry.selections).collect::<Vec<_>>())
                .collect::<Vec<_>>();
            batch_scores.push(json!({"begin":begin,"scores":scores}));
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
                    let key = classes
                        .iter()
                        .find(|key| {
                            key.path_signature == record["parent_path_signature"].as_u64().unwrap()
                                && directory.classes[*key].0 as u64 == record["parent_class_id"].as_u64().unwrap()
                        })
                        .unwrap();
                    record["parent_corpus_entry"] =
                        json!({"identity":key,"input_id":format!("initial:{}",directory.classes[key].1)});
                    completed.push((id, sample, record));
                    continue;
                }
                let parent_identity = &classes[*parent_index];
                let entry_index = if options.feedback {
                    (0..entries[*parent_index].len())
                        .min_by(|a, b| {
                            ((pending_selections[*parent_index][*a] + 1) as f64
                                / coverage.score(&entries[*parent_index][*a].feature))
                            .total_cmp(
                                &((pending_selections[*parent_index][*b] + 1) as f64
                                    / coverage.score(&entries[*parent_index][*b].feature)),
                            )
                            .then(a.cmp(b))
                        })
                        .unwrap()
                } else {
                    0
                };
                pending_selections[*parent_index][entry_index] += 1;
                let entry = &entries[*parent_index][entry_index];
                let parent = &entry.sample;
                let candidates = neighbors(parent_identity, &classes, &pending_hits);
                let use_neighbor = rng.next_u64() & 1 != 0 && !candidates.is_empty();
                let targets = if use_neighbor {
                    candidates.into_iter().filter(|i| options.feedback || pending_hits[*i] < quota).collect::<Vec<_>>()
                } else {
                    vec![*parent_index]
                };
                let target_index = if options.feedback && !targets.is_empty() {
                    let distance = |index: usize| {
                        parent_identity
                            .guard_vector
                            .bytes()
                            .zip(classes[index].guard_vector.bytes())
                            .filter(|(a, b)| a != b)
                            .count()
                    };
                    *targets
                        .iter()
                        .min_by(|a, b| {
                            distance(**a)
                                .cmp(&distance(**b))
                                .then_with(|| {
                                    ((pending_hits[**a] + 1) as f64 / scores[**a])
                                        .total_cmp(&((pending_hits[**b] + 1) as f64 / scores[**b]))
                                })
                                .then(a.cmp(b))
                        })
                        .unwrap()
                } else {
                    targets.first().copied().unwrap_or(*parent_index)
                };
                let identity = &classes[target_index];
                let neighbor = target_index != *parent_index;
                let mut record = json!({"sample_id":id,"operator":if neighbor {"B"} else {"A"},"form":if neighbor {"neighbor"} else {"within_class"},"parent_sample_id":parent.sample_id,"parent_path_signature":parent.path_signature,"parent_class_id":parent.class_id,"target_identity":identity});
                record["parent_corpus_entry"] = json!({"identity":parent_identity,"input_id":entry.input_id});
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
            let accepted =
                rows.iter().enumerate().filter_map(|(i, row)| row.as_ref().map(|row| (i, row))).collect::<Vec<_>>();
            let feature_samples = accepted
                .iter()
                .map(|(_, row)| serde_json::from_value(row["sample"].clone()).unwrap())
                .collect::<Vec<Sample>>();
            let feature_identities =
                accepted.iter().map(|(_, row)| directory.identity(&options.scenario, row)).collect::<Vec<_>>();
            let mut features = accepted
                .iter()
                .map(|(i, _)| begin + i)
                .zip(super::feedback::extract(&feature_samples, &feature_identities, &options.output))
                .collect::<BTreeMap<_, _>>();
            let certification_indices = rows
                .iter()
                .enumerate()
                .filter_map(|(i, row)| {
                    row.as_ref()?;
                    (options.certify_all
                        || hardware.is_some()
                        || (options.feedback && coverage.is_novel(&features[&(begin + i)])))
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
                    } else {
                        panic!("当前场景的完整类目录中缺少实际类");
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
                for (index, raw_observed) in results {
                    // 路径、ELF 来源和计时保留在逐例原始记录；确定性接口只保留三方语义字段。
                    let observed = Value::Object(
                        [
                            "sample_id",
                            "agree",
                            "bucket",
                            "reason",
                            "isla_cause",
                            "xs_cause",
                            "nemu_cause",
                            "isla_consistent_side",
                            "phase",
                            "mismatch",
                        ]
                        .into_iter()
                        .map(|field| (field.into(), raw_observed[field].clone()))
                        .collect(),
                    );
                    hardware_timing.push(json!({"sample_id":index,"emu_seconds":raw_observed["elapsed"],"known_rule":raw_observed["mismatch"]["known_rule"]}));
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
                        features.get_mut(&index).unwrap().mismatch = Some(finding.clone());
                        feedback.on_mismatch(index as u64, &finding);
                        findings.push(finding);
                    } else {
                        agree += 1;
                    }
                    hardware_results.push(observed);
                }
                // 所有状态只在整批结果收齐后落盘。
                super::io::write_lines(&options.output.join("difftest-results.jsonl"), &hardware_results);
                super::io::write_lines(&options.output.join("hardware-timing.jsonl"), &hardware_timing);
                super::io::write_lines(&options.output.join("findings.jsonl"), &findings);
                super::io::write_json(
                    &options.output.join("findings-summary.json"),
                    &json!({"executed":hardware_results.len(),"agree":agree,"mismatch":findings.len()-infrastructure,"filtered":filtered,"new_disagreements":findings.len()-infrastructure-filtered,"infrastructure_failures":infrastructure,"rule_counts":rules,"groups":groups.values().collect::<Vec<_>>() }),
                );
            }
            // 本批全部结果已收齐；按编号接纳，批内同一新桶只接纳首个输入。
            for (index, feature) in features {
                let novel = coverage.is_novel(&feature);
                mutant_buckets.extend(feature.buckets.iter().map(|bucket| (feature.identity.clone(), bucket.clone())));
                observations.push(json!({"sample_id":index,"feature":feature,"novel":novel}));
                coverage.observe(index as u64, &feature);
                if options.feedback && novel {
                    assert_eq!(records[index]["actual_certified"], true, "新增 corpus entry 必须先认证");
                    let sample: Sample =
                        serde_json::from_value(rows[index - begin].as_ref().unwrap()["sample"].clone()).unwrap();
                    let input_id = format!("mutant:{index}");
                    corpus_added.push(json!({"identity":feature.identity,"input_id":input_id,"parent":records[index]["parent_corpus_entry"],"sample":sample}));
                    coverage.on_corpus_add(index as u64);
                    feedback.on_corpus_add(index as u64);
                    let class_index = classes.iter().position(|key| key == &feature.identity).unwrap();
                    entries[class_index].push(CorpusEntry { sample, feature, input_id, selections: 0 });
                }
            }
            for (list, counts) in entries.iter_mut().zip(pending_selections) {
                for (entry, count) in list.iter_mut().zip(counts) {
                    entry.selections = count;
                }
            }
            judged.extend(rows);
            if options.feedback {
                weighted.on_batch_end(batch.len());
            } else {
                scheduler.on_batch_end(batch.len());
            }
            coverage.end_batch();
            scores = entries.iter().map(|list| coverage.score(&list[0].feature)).collect();
            weighted.set_scores(scores.clone());
            super::io::write_json(
                &options.output.join("feedback-summary.json"),
                &json!({"mode":if options.feedback {"coverage"} else {"none"},"initial":initial_coverage,"final":coverage.summary(),"mutant_class_value_buckets":mutant_buckets.len()}),
            );
            super::io::write_lines(&options.output.join("feedback-observations.jsonl"), &observations);
            super::io::write_lines(&options.output.join("schedule-scores.jsonl"), &batch_scores);
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
