//! 初始 corpus 的共同硬件观察，作为所有臂的第0例起点。
use super::{emu, execute_batches, io, mismatch_feature, observe, perf, testcase, Runtime, Signals, STOP};
use isla_lib::executor::samples::Sample;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::ErrorKind,
    path::{Path, PathBuf},
    sync::atomic::Ordering,
    time::Instant,
};

#[derive(Deserialize, Serialize)]
pub(super) struct Observation {
    pub perf: BTreeMap<String, u64>,
    pub fixed: Value,
    pub baseline: Value,
    pub known_replay: Option<Value>,
    pub fixed_replay: Option<Value>,
}

impl Observation {
    pub fn needs_known_replay(fixed: &Value, baseline: &Value) -> bool {
        fixed["agree"] == true && baseline["mismatch"]["known_rule"] == observe::KNOWN_RULE
    }

    pub fn complete(&self, signals: &[String]) -> bool {
        observe::complete_probe(&self.fixed)
            && observe::complete_probe(&self.baseline)
            && complete_replay(&self.known_replay, Self::needs_known_replay(&self.fixed, &self.baseline))
            && complete_replay(&self.fixed_replay, mismatch_feature(&self.fixed).is_some())
            && if self.fixed["agree"] == true {
                signals.iter().all(|name| self.perf.contains_key(name))
            } else {
                self.perf.is_empty()
            }
    }
}

fn complete_replay(replay: &Option<Value>, required: bool) -> bool {
    match replay {
        Some(result) => required && observe::complete_probe(result),
        None => !required,
    }
}

// 启动参数、预热、观察器判定或测试编译协议改变时更新此版本。
pub(super) const PROTOCOL: u32 = 1;

#[derive(Deserialize, Serialize)]
struct Checkpoint<I, O, S> {
    input: I,
    conditions: Conditions<I, S>,
    observation: O,
}

#[derive(Deserialize, Serialize)]
struct Conditions<V, S> {
    execution: V,
    signals: S,
}

struct Checkpoints {
    directory: PathBuf,
    conditions: Value,
    writer: Option<fs::File>,
}

impl Checkpoints {
    pub fn prepare(directory: PathBuf, conditions: Value) -> Self {
        fs::create_dir_all(&directory).unwrap();
        let writer = fs::File::open(&directory).unwrap();
        writer.try_lock().expect("初始观察目录已有准备进程");
        Self { directory, conditions, writer: Some(writer) }
    }

    pub fn reuse(directory: PathBuf, conditions: Value) -> Self {
        Self { directory, conditions, writer: None }
    }

    pub fn read(&self, index: usize, input: &Value, signals: &[String]) -> Option<Observation> {
        let path = self.directory.join(format!("{index:06}.json"));
        let bytes = match fs::read(&path) {
            Ok(bytes) => bytes,
            Err(error) if error.kind() == ErrorKind::NotFound => return None,
            Err(error) => panic!("读取初始观察 {} 失败：{error}", path.display()),
        };
        let row: Checkpoint<Value, Observation, BTreeSet<String>> = serde_json::from_slice(&bytes).ok()?;
        let signals_match =
            row.observation.fixed["agree"] != true || signals.iter().all(|name| row.conditions.signals.contains(name));
        (row.input == *input
            && row.conditions.execution == self.conditions
            && signals_match
            && row.observation.complete(signals))
        .then_some(row.observation)
    }

    pub fn write(&self, index: usize, input: &Value, signals: &[String], observation: &Observation) {
        assert!(self.writer.is_some(), "只有准备进程可以写入初始观察");
        let path = self.directory.join(format!("{index:06}.json"));
        let conditions = Conditions { execution: &self.conditions, signals };
        io::write_json_atomic(&path, &Checkpoint { input, conditions, observation });
    }
}

pub(super) struct State {
    pub feedback: perf::Coverage,
    pub heldout: perf::Coverage,
    pub mismatches: BTreeSet<String>,
    pub known_first: Option<usize>,
}

impl State {
    pub fn new<'a>(rows: impl IntoIterator<Item = &'a Observation>, selected: &[String], holdout: &[String]) -> Self {
        let mut state = Self {
            feedback: perf::Coverage::default(),
            heldout: perf::Coverage::default(),
            mismatches: BTreeSet::new(),
            known_first: None,
        };
        for row in rows {
            if row.fixed["agree"] == true {
                state.feedback.observe(&row.perf, selected);
                state.heldout.observe(&row.perf, holdout);
            }
            if let Some(key) = mismatch_feature(&row.fixed) {
                state.mismatches.insert(key);
            }
            if Observation::needs_known_replay(&row.fixed, &row.baseline)
                && row
                    .known_replay
                    .as_ref()
                    .is_some_and(|replay| replay["mismatch"]["known_rule"] == observe::KNOWN_RULE)
            {
                state.known_first = Some(0);
            }
        }
        state
    }
}

pub(super) fn input_reference(sample: &Sample, generated: &testcase::Generated) -> Value {
    json!({
        "id":sample.sample_id,
        "terminal":sample.terminal,
        "pre_registers":sample.pre_registers,"pre_memory":sample.pre_memory,
        "post_registers":sample.post_registers,"post_memory":sample.post_memory,
        "result":sample.result,
        "instruction":generated.instruction.word,"expected":generated.expected,
        "program":generated.assembly,"linker":generated.linker,
    })
}

pub(super) fn initial_observations<T: Send>(
    runtime: &Runtime,
    output: &Path,
    inputs: Vec<(Option<Value>, T)>,
    all_selected: &[String],
    signals: &Signals,
    conditions: Value,
    judge_seconds: f64,
    filter_seconds: f64,
    observe_entry: impl Fn(T, &Path) -> (Observation, emu::InitialTiming) + Sync,
) -> Vec<Observation> {
    let started = Instant::now();
    let cache = if runtime.prepare_only {
        let directory = runtime.reuse_initial.clone().unwrap_or_else(|| output.join("initial-cache"));
        Some(Checkpoints::prepare(directory, conditions))
    } else {
        runtime.reuse_initial.as_ref().map(|source| Checkpoints::reuse(source.clone(), conditions))
    };
    let total = inputs.len();
    let mut rows = (0..total).map(|_| None).collect::<Vec<Option<Observation>>>();
    let mut pending = Vec::new();
    let mut reused = 0;
    let mut missing = Vec::new();
    for (index, (input, job)) in inputs.into_iter().enumerate() {
        if let Some(row) = cache.as_ref().and_then(|cache| cache.read(index, input.as_ref().unwrap(), all_selected)) {
            rows[index] = Some(row);
            reused += 1;
        } else if !runtime.prepare_only && runtime.reuse_initial.is_some() {
            missing.push(index);
        } else {
            pending.push((index, input, job));
        }
    }
    let timing = execute_batches(pending, runtime.workers, |(index, input, job)| {
        if STOP.load(Ordering::SeqCst) {
            return None;
        }
        let started = Instant::now();
        let directory = output.join("initial-hardware").join(format!("{index:06}"));
        let (mut observation, mut timing) = observe_entry(job, &directory);
        if runtime.prepare_only {
            observation.perf.retain(|name, _| all_selected.binary_search(name).is_ok());
            if observation.complete(all_selected) {
                cache.as_ref().unwrap().write(index, input.as_ref().unwrap(), all_selected, &observation);
            }
        }
        io::write_json(&directory.join("initial-observation.json"), &observation);
        eprintln!("[ABLATION_INITIAL] {}", json!({"entry":index,"total":total}));
        timing.worker_seconds = started.elapsed().as_secs_f64();
        Some((index, observation, timing))
    });
    let mut batch_tail_worker_seconds = 0.0;
    for batch in timing.chunks(runtime.workers) {
        let durations = batch.iter().flatten().map(|(_, _, row)| row.worker_seconds);
        let last = durations.clone().fold(0.0, f64::max);
        batch_tail_worker_seconds += durations.map(|seconds| last - seconds).sum::<f64>();
    }
    let mut timings = BTreeMap::new();
    for (index, row, timing) in timing.into_iter().flatten() {
        rows[index] = Some(row);
        timings.insert(index, timing);
    }
    let mut not_reusable = Vec::new();
    let mut summary_rows = Vec::new();
    for (index, row) in rows.iter().enumerate() {
        let complete = row.as_ref().is_some_and(|row| row.complete(all_selected));
        if !complete {
            not_reusable.push(index);
        }
        if complete || cache.is_none() {
            summary_rows.extend(row);
        }
    }
    let state = State::new(summary_rows.iter().copied(), &signals.treatment, &signals.holdout);
    let elapsed = started.elapsed().as_secs_f64();
    let summary = json!({
        "entries":rows.iter().flatten().count(),
        "expected_entries":total,
        "complete_reusable":total-not_reusable.len(),
        "reused_entries":reused,
        "observed_entries":timings.len(),
        "initial_emu_runs":timings.values().map(|row|row.emu_runs).sum::<usize>(),
        "not_reusable_entries":not_reusable,
        "missing_reuse_entries":missing,
        "cache_directory":cache.as_ref().map(|cache| &cache.directory),
        "workers":runtime.workers,
        "interrupted":STOP.load(Ordering::SeqCst),
        "judge_seconds":judge_seconds,
        "filter_seconds":filter_seconds,
        "initial_seconds":elapsed,
        "batch_tail_worker_seconds":batch_tail_worker_seconds,
        "observed_timings":timings,
        "R_XS_001_first":state.known_first,
        "initial_mismatch_signatures":state.mismatches,
        "replayed_divergence_signatures":summary_rows.into_iter().filter_map(|row| {
            let key = mismatch_feature(&row.fixed)?;
            (row.fixed_replay.as_ref().and_then(mismatch_feature).as_ref()==Some(&key)).then_some(key)
        }).collect::<BTreeSet<_>>()
    });
    io::write_json(&output.join("initial-hardware-summary.json"), &summary);
    eprintln!(
        "[ABLATION_INITIAL_READY] {}",
        json!({"seconds":elapsed,"observed_entries":timings.len(),"reused_entries":reused,"complete_reusable":total-not_reusable.len()})
    );
    if cache.is_some() && !STOP.load(Ordering::SeqCst) {
        assert!(not_reusable.is_empty(), "初始观察未齐备，详见 initial-hardware-summary.json");
    }
    rows.into_iter().flatten().collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn checkpoint_cold_warm_and_resume_keep_case_zero_in_order() {
        use super::super::{random_stream, select_request, ClassIdentity, Entry};
        use rand::RngCore;
        use std::sync::Mutex;

        let directory = std::env::temp_dir().join(format!("isla-initial-observations-{}", std::process::id()));
        let prepared = directory.join("prepared");
        let warm_output = directory.join("warm");
        let resumed_output = directory.join("resumed");
        fs::create_dir_all(&warm_output).unwrap();
        fs::create_dir_all(&resumed_output).unwrap();
        let checkpoint_dir = prepared.join("initial-cache");
        let conditions = json!({"protocol":1});
        let signals = Signals {
            treatment: vec!["feedback".into()],
            holdout: vec!["heldout".into()],
            universe: Vec::new(),
            random_selection_seed: 0,
        };
        let selected = ["feedback".to_owned(), "heldout".to_owned(), "random".to_owned()];
        let inputs = [
            json!({"id":42,"pre":1,"instruction":7,"expected":0}),
            json!({"id":42,"pre":2,"instruction":7,"expected":0}),
        ];
        let classes = ["0", "1"].map(|guard| ClassIdentity {
            scenario_config_id: "fixture".into(),
            path_signature: 1,
            guard_vector: guard.into(),
        });
        let entries = classes
            .iter()
            .zip(&inputs)
            .map(|(identity, input)| {
                let mut sample = super::super::super::tests::example_sample();
                sample.sample_id = input["id"].as_u64().unwrap();
                sample.pre_memory[0].value = Some(input["pre"].as_u64().unwrap() as u8);
                Entry { sample, identity: identity.clone(), selections: 0, score: 1, generation: 0 }
            })
            .collect::<Vec<_>>();
        let mut runtime: Runtime = serde_json::from_value(json!({
            "loader":"loader","library_path":"lib","emu":"simulator","unpatched":"comparison",
            "nemu":"reference","observer":"observer","compiler":"compiler","platform":"platform",
            "signals":"signals","seeds":[3],"budget":1,"workers":2,"timeout_seconds":1,"prepare_only":true
        }))
        .unwrap();
        let launches = Mutex::new(Vec::new());
        let round = |runtime: &Runtime, output: &Path| {
            let rows = initial_observations(
                runtime,
                output,
                inputs.iter().cloned().enumerate().map(|(index, input)| (Some(input), index)).collect(),
                &selected,
                &signals,
                conditions.clone(),
                0.0,
                0.0,
                |index, directory| {
                    launches.lock().unwrap().push(index);
                    fs::create_dir_all(directory).unwrap();
                    let agreeing = json!({
                        "agree":true,"bucket":"agree","isla_consistent_side":"both",
                        "xs_cause":0,"nemu_cause":0,"native_exit_symbol":"exit",
                        "observation":{"isla_consistent_side":"both","native_guided_exec":false,"native_result":{"event":"step","mcause":0}}
                    });
                    let differing = json!({
                        "agree":false,"bucket":"xs!=expected","reason":"test","isla_consistent_side":"nemu",
                        "xs_cause":1,"nemu_cause":0,"native_exit_symbol":"exit",
                        "observation":{"isla_consistent_side":"nemu","native_guided_exec":false,"native_result":{"event":"step","mcause":0}}
                    });
                    let row = if index == 0 {
                        let mut known = differing;
                        known["mismatch"] = json!({"known_rule":observe::KNOWN_RULE});
                        Observation {
                            perf: BTreeMap::from([("feedback".into(), 2), ("heldout".into(), 3), ("random".into(), 0)]),
                            fixed: agreeing,
                            baseline: known.clone(),
                            known_replay: Some(known),
                            fixed_replay: None,
                        }
                    } else {
                        Observation {
                            perf: BTreeMap::new(),
                            fixed: differing.clone(),
                            baseline: agreeing,
                            known_replay: None,
                            fixed_replay: Some(differing),
                        }
                    };
                    (row, emu::InitialTiming { emu_runs: 3, ..emu::InitialTiming::default() })
                },
            );
            let state = State::new(&rows, &signals.treatment, &signals.holdout);
            assert_eq!(state.feedback.signatures, BTreeSet::from(["2".into()]));
            assert_eq!(state.heldout.signatures, BTreeSet::from(["2".into()]));
            assert_eq!(
                State::new(&rows, &["random".into()], &signals.holdout).feedback.signatures,
                BTreeSet::from(["0".into()])
            );
            assert_eq!(state.known_first, Some(0));
            assert_eq!(state.mismatches.len(), 1);
            let summary: Value =
                serde_json::from_reader(fs::File::open(output.join("initial-hardware-summary.json")).unwrap()).unwrap();
            assert_eq!(summary["complete_reusable"], 2);
            assert_eq!(summary["replayed_divergence_signatures"], json!(state.mismatches));
            let mut rng = random_stream(runtime.seeds[0], "fixture", 0);
            let (parent, target, operator) = select_request(&entries, &classes, &[0, 0], None, true, &mut rng);
            let first_request = json!({
                "parent":entries[parent].identity,"pre_memory":entries[parent].sample.pre_memory,
                "target":target,"operator":operator,"solver_seed":rng.next_u64() as u32,
            });
            ((json!(rows), first_request), summary)
        };
        let take_launches = || {
            let mut launched = std::mem::take(&mut *launches.lock().unwrap());
            launched.sort_unstable();
            launched
        };

        let (cold, cold_summary) = round(&runtime, &prepared);
        assert_eq!(take_launches(), [0, 1]);
        assert_eq!(cold_summary["initial_emu_runs"], 6);

        runtime.prepare_only = false;
        runtime.reuse_initial = Some(checkpoint_dir.clone());
        let (warm, warm_summary) = round(&runtime, &warm_output);
        assert_eq!(warm, cold);
        assert!(take_launches().is_empty());
        assert_eq!(warm_summary["initial_emu_runs"], 0);
        assert_eq!(warm_summary["reused_entries"], 2);
        assert!(!warm_output.join("initial-hardware").exists());

        let reader = Checkpoints::reuse(checkpoint_dir.clone(), conditions.clone());
        assert!(reader.read(1, &inputs[0], &selected).is_none(), "相同编号的不同前态不可复用");
        let mut changed_input = inputs[0].clone();
        changed_input["instruction"] = json!(8);
        assert!(reader.read(0, &changed_input, &selected).is_none());
        changed_input = inputs[0].clone();
        changed_input["expected"] = json!(1);
        assert!(reader.read(0, &changed_input, &selected).is_none());
        assert!(reader.read(0, &inputs[0], &["missing".into()]).is_none());
        assert!(reader.read(0, &inputs[0], &[]).is_some());
        let path = checkpoint_dir.join("000000.json");
        let bytes = fs::read(&path).unwrap();
        let mut invalid: Value = serde_json::from_slice(&bytes).unwrap();
        invalid["conditions"]["signals"] = json!(["heldout", "random"]);
        fs::write(&path, serde_json::to_vec(&invalid).unwrap()).unwrap();
        assert!(reader.read(0, &inputs[0], &selected).is_none());
        fs::write(&path, bytes).unwrap();
        let changed = Checkpoints::reuse(checkpoint_dir.clone(), json!({"protocol":2}));
        assert!(changed.read(0, &inputs[0], &selected).is_none());

        let path = checkpoint_dir.join("000001.json");
        let mut interrupted: Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        interrupted["observation"]["fixed_replay"] = Value::Null;
        let incomplete = serde_json::to_vec(&interrupted).unwrap();
        fs::write(&path, &incomplete).unwrap();
        assert!(std::panic::catch_unwind(|| round(&runtime, &warm_output)).is_err());
        assert_eq!(fs::read(&path).unwrap(), incomplete);
        assert!(take_launches().is_empty());
        fs::rename(&path, path.with_extension("json.tmp")).unwrap();

        runtime.prepare_only = true;
        let (resumed, resumed_summary) = round(&runtime, &resumed_output);
        assert_eq!(resumed, cold);
        assert_eq!(take_launches(), [1]);
        assert_eq!(resumed_summary["initial_emu_runs"], 3);
        assert_eq!(resumed_summary["reused_entries"], 1);
        assert!(reader.read(1, &inputs[1], &selected).is_some());
        assert!(!path.with_extension("json.tmp").exists());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn initial_corpus_is_case_zero_and_requires_confirmed_known_bug() {
        let rows = vec![
            Observation {
                perf: BTreeMap::from([("feedback".into(), 1), ("heldout".into(), 2)]),
                fixed: json!({"agree":true}),
                baseline: json!({"mismatch":{"known_rule":observe::KNOWN_RULE}}),
                known_replay: None,
                fixed_replay: None,
            },
            Observation {
                perf: BTreeMap::new(),
                fixed: json!({"agree":false,"bucket":"xs!=expected","reason":"test","isla_consistent_side":"nemu"}),
                baseline: Value::Null,
                known_replay: None,
                fixed_replay: None,
            },
        ];
        let mut rows = rows;
        let state = State::new(&rows, &["feedback".into()], &["heldout".into()]);
        assert_eq!(state.known_first, None, "观察到一次还不能算独立确认");
        assert_eq!(state.mismatches.len(), 1);
        assert_eq!(state.heldout.signatures, BTreeSet::from(["2".into()]));
        assert_eq!(state.feedback.signatures, BTreeSet::from(["1".into()]));
        rows[0].known_replay = Some(json!({"mismatch":{"known_rule":observe::KNOWN_RULE}}));
        assert_eq!(State::new(&rows, &["feedback".into()], &["heldout".into()]).known_first, Some(0));
        rows[0].fixed["agree"] = json!(false);
        assert_eq!(State::new(&rows, &["feedback".into()], &["heldout".into()]).known_first, None);
    }
}
