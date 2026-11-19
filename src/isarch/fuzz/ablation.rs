//! 四臂共用全符号DAG、显式硬件过滤及按输入编号独立的随机流。
mod baseline;
mod classify;
mod eligibility;
mod emu;
pub(super) mod input_domain;
mod lineage;
mod observe;
mod perf;
pub(super) mod reproducibility;

use super::{
    corpus::{ClassIdentity, Directory},
    generation::{GenerationPool, Job},
    io, random_stream, testcase, Executor, Feedback, Mutator, Options,
};
use crate::isarch::{resident::ResidentPath, target::Target};
use isla_lib::{bitvector::BV, executor::samples::Sample, ir::SharedState};
use lineage::AdmissionReason;
use rand::{seq::SliceRandom, RngCore};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fs,
    io::Write,
    path::{Path, PathBuf},
    sync::atomic::{AtomicBool, Ordering},
    time::Instant,
};

static STOP: AtomicBool = AtomicBool::new(false);
fn disable_core_dumps() {
    let limit = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
    assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_CORE, &limit) }, 0);
}
extern "C" fn stop(signal: i32) {
    assert!(signal == libc::SIGTERM || signal == libc::SIGINT);
    STOP.store(true, Ordering::SeqCst);
}

fn install_stop_handlers() {
    unsafe {
        libc::signal(libc::SIGTERM, stop as *const () as usize);
        libc::signal(libc::SIGINT, stop as *const () as usize);
    }
}

/// inspect只做前态初筛；filter验证L1可恢复性；run再执行硬件。三者都不替代模型认证。
pub fn case_main() {
    disable_core_dumps();
    use std::io::BufRead;
    let args = std::env::args().collect::<Vec<_>>();
    if args.get(1).is_some_and(|mode| mode == "lineage") {
        assert_eq!(args.len(), 3, "用法：ablation-case lineage 运行目录");
        match lineage::summarize(Path::new(&args[2])) {
            Ok(summary) => println!("{}", serde_json::to_string_pretty(&summary).unwrap()),
            Err(error) => {
                eprintln!("{error}");
                std::process::exit(1);
            }
        }
        return;
    }
    assert_eq!(
        args.len(),
        5,
        "用法：ablation-case inspect|filter|run 输入.jsonl runtime.json 输出目录，或 ablation-case lineage 运行目录"
    );
    assert!(matches!(args[1].as_str(), "inspect" | "filter" | "run"), "未知检查模式");
    let runtime = Runtime::read(Path::new(&args[3]));
    let platform: testcase::Platform = serde_json::from_reader(fs::File::open(&runtime.platform).unwrap()).unwrap();
    let output = Path::new(&args[4]);
    fs::create_dir_all(output).unwrap();
    let mut counts = BTreeMap::<String, usize>::new();
    let mut primary = BTreeMap::<String, usize>::new();
    let mut total = 0usize;
    let mut precheck_kept = 0usize;
    let mut kept = 0usize;
    let mut candidates = fs::File::create(output.join("candidates.jsonl")).unwrap();
    let mut rejected = fs::File::create(output.join("rejected.jsonl")).unwrap();
    let mut observations = Vec::new();
    let mut construction = Vec::new();
    for line in std::io::BufReader::new(fs::File::open(&args[2]).unwrap()).lines() {
        let value: Value = serde_json::from_str(&line.unwrap()).unwrap();
        let sample: Sample =
            serde_json::from_value(if value.get("sample").is_some() { value["sample"].clone() } else { value })
                .unwrap();
        total += 1;
        let checked = eligibility::precheck(&sample).and_then(|()| {
            precheck_kept += 1;
            if args[1] == "inspect" {
                Ok(None)
            } else {
                eligibility::check(&sample, &platform).map(Some)
            }
        });
        let generated = match checked {
            Ok(generated) => generated,
            Err(exclusion) => {
                *primary.entry(exclusion.reasons.first().unwrap().clone()).or_default() += 1;
                for reason in &exclusion.reasons {
                    *counts.entry(reason.clone()).or_default() += 1;
                }
                append(&mut rejected, &json!({"sample_id":sample.sample_id,"exclusion":exclusion}));
                continue;
            }
        };
        kept += 1;
        append(&mut candidates, &sample);
        if args[1] == "run" {
            let signals: Signals = serde_json::from_reader(fs::File::open(&runtime.signals).unwrap()).unwrap();
            let selected = signals.treatment.iter().chain(&signals.holdout).cloned().collect::<Vec<_>>();
            let case = output.join(format!("case-{}", sample.sample_id));
            let result = emu::run(&runtime, &platform, sample, generated.unwrap(), &case, true, &selected);
            observations.push(json!({"fixed":result.fixed,"baseline":result.baseline}));
        } else if let Some(generated) = generated {
            construction.push(json!({
                "sample_id":sample.sample_id,"cause":generated.expected.cause,"record":generated.construction
            }));
        }
    }
    let mut summary = json!({
        "mode":args[1],"total":total,"precheck_kept":precheck_kept,"kept":kept,"rejected":total-kept,
        "reasons":counts,"primary_reasons":primary,"all_reason_counts_overlap":true,
        "reason_fractions":counts.iter().map(|(reason,count)|(reason,*count as f64 /total.max(1) as f64)).collect::<BTreeMap<_,_>>(),
        "observations":observations,"is_model_certification":false
    });
    if args[1] == "filter" {
        summary["construction"] = Value::Array(construction);
    }
    io::write_json(&output.join("summary.json"), &summary);
}

pub(super) fn check_constructible(sample: &Sample, platform: &testcase::Platform) -> Result<(), Value> {
    eligibility::check(sample, platform).map(|_| ()).map_err(|exclusion| serde_json::to_value(exclusion).unwrap())
}

/// 在指定路径上核对既有父输入并抽查随机取点的硬件接纳率；不计入正式消融。
pub(super) fn mutation_probe<B: BV>(
    options: &Options,
    corpus: &[Sample],
    paths: &[ResidentPath<B>],
    shared: &SharedState<B>,
    target: &dyn Target<B>,
) {
    disable_core_dumps();
    use isla_lib::smt::{Config, Context, Solver};
    let platform: testcase::Platform = serde_json::from_reader(
        fs::File::open(options.inputs.as_ref().expect("mutation-probe需要--fuzz-inputs platform.json")).unwrap(),
    )
    .unwrap();
    let platform_config: Value =
        serde_json::from_reader(fs::File::open(options.inputs.as_ref().unwrap()).unwrap()).unwrap();
    let input_domain: Option<input_domain::InputDomain> =
        platform_config.get("input_domain").cloned().map(|v| serde_json::from_value(v).unwrap());
    let mut parents = fs::File::create(options.output.join("parents-judged.jsonl")).unwrap();
    let mut mutants = fs::File::create(options.output.join("probe-mutants.jsonl")).unwrap();
    let mut reasons = BTreeMap::<String, usize>::new();
    let mut accepted = 0usize;
    let mut attempted = 0usize;
    let mut parents_executable = 0usize;
    for input in corpus {
        let path = paths.iter().find(|path| path.signature == input.path_signature).unwrap();
        let context = Context::new(Config::new());
        let mut solver = Solver::from_checkpoint(&context, path.checkpoint.clone());
        let row = path
            .path
            .judge(&mut solver, shared, input, &path.records, path.signature, |sample, model| {
                sample.isa_state = crate::isarch::samples::isa_state(target, sample, model, shared)?;
                Ok(())
            })
            .expect("探针父输入judge失败")
            .expect("探针父输入不属于指定缓存路径");
        let row = serde_json::to_value(row).unwrap();
        assert_eq!(row["guard_unique"], true);
        assert_eq!(row["post_unique"], true);
        let parent: Sample = serde_json::from_value(row["sample"].clone()).unwrap();
        append(&mut parents, &row);
        if eligibility::check(&parent, &platform).is_ok() {
            parents_executable += 1;
        }
        let identity = ClassIdentity {
            scenario_config_id: options.scenario.clone(),
            path_signature: path.signature,
            guard_vector: row["guard_vector"].as_str().unwrap().into(),
        };
        let mutator = super::mutator::SolverMutator::new(path, &context, shared, target, &options.mutation_config)
            .with_input_domain(
                input_domain::InputDomain::compile_optional(input_domain.as_ref(), &path.path, shared)
                    .expect("探针输入域无效"),
            );
        for i in 0..options.budget.min(16) {
            let id = attempted as u64;
            let mut rng = random_stream(options.random_seed, &options.scenario, id);
            let record = json!({"sample_id":id,"target_identity":identity,"operator":"A"});
            let sample = mutator.try_mutate(&parent, &record, &mut rng);
            attempted += 1;
            let Some(sample) = sample else {
                append(&mut mutants, &json!({"parent_sample_id":input.sample_id,"request":i,"exhausted":true}));
                break;
            };
            let judged = path
                .path
                .judge(&mut solver, shared, &sample, &path.records, path.signature, |sample, model| {
                    sample.isa_state = crate::isarch::samples::isa_state(target, sample, model, shared)?;
                    Ok(())
                })
                .expect("探针mutant认证失败")
                .expect("探针mutant未被目标路径接纳");
            assert_eq!(judged.guard_vector, identity.guard_vector);
            let sample = judged.sample;
            match eligibility::check(&sample, &platform) {
                Ok(_) => {
                    accepted += 1;
                    append(
                        &mut mutants,
                        &json!({"parent_sample_id":input.sample_id,"request":i,"precheck_accepted":true,"sample":sample}),
                    );
                }
                Err(exclusion) => {
                    for reason in &exclusion.reasons {
                        *reasons.entry(reason.clone()).or_default() += 1;
                    }
                    append(
                        &mut mutants,
                        &json!({"parent_sample_id":input.sample_id,"request":i,"precheck_accepted":false,"exclusion":exclusion,"sample":sample}),
                    );
                }
            }
        }
        eprintln!(
            "[ABLATION_MUTATION_PROBE] {}",
            json!({"attempted":attempted,"precheck_accepted":accepted,"parents_executable":parents_executable})
        );
    }
    io::write_json(
        &options.output.join("mutation-probe-summary.json"),
        &json!({"parents":corpus.len(),"parents_executable":parents_executable,"attempted":attempted,"mutant_precheck_accepted":accepted,"reasons":reasons,"input_domain":input_domain,"certification":"父输入与mutant均指定路径完整judge及L1；仍须正式完整DAG认证"}),
    );
}

#[derive(Clone, Deserialize)]
pub(super) struct Runtime {
    pub loader: PathBuf,
    pub library_path: PathBuf,
    pub emu: PathBuf,
    pub unpatched: PathBuf,
    pub nemu: PathBuf,
    pub observer: PathBuf,
    pub compiler: PathBuf,
    pub platform: PathBuf,
    pub signals: PathBuf,
    pub seeds: Vec<u64>,
    pub budget: usize,
    #[serde(default = "default_arms")]
    pub arms: Vec<String>,
    pub workers: usize,
    pub timeout_seconds: u64,
    #[serde(default)]
    pub first_request_only: bool,
    #[serde(default)]
    pub filter_only: bool,
    /// 只准备第 0 例的观察。设置 reuse_initial 时在该目录恢复准备。
    #[serde(default)]
    pub prepare_only: bool,
    /// 单臂只读的缓存目录，相对路径以 runtime 文件所在目录为基准。
    #[serde(default)]
    pub reuse_initial: Option<PathBuf>,
    /// 声明会影响硬件观察的组件行为版本。
    #[serde(default)]
    pub initial_components: BTreeMap<String, String>,
    #[serde(default)]
    pub input_domain: Option<input_domain::InputDomain>,
}
fn default_arms() -> Vec<String> {
    ["B0", "B1", "B2", "T"].map(String::from).to_vec()
}
impl Runtime {
    fn read(path: &Path) -> Self {
        let mut runtime: Self = serde_json::from_reader(fs::File::open(path).unwrap()).unwrap();
        let base = path.parent().unwrap();
        for p in [
            &mut runtime.loader,
            &mut runtime.library_path,
            &mut runtime.emu,
            &mut runtime.unpatched,
            &mut runtime.nemu,
            &mut runtime.observer,
            &mut runtime.platform,
            &mut runtime.signals,
        ] {
            *p = fs::canonicalize(if p.is_absolute() { p.clone() } else { base.join(&*p) }).unwrap();
        }
        // 保留编译器别名的文件名，L1据其前缀寻找配套nm／objdump。
        if !runtime.compiler.is_absolute() {
            runtime.compiler = base.join(&runtime.compiler);
        }
        assert!(runtime.compiler.is_file(), "编译器不存在");
        assert!(!(runtime.filter_only && runtime.first_request_only), "过滤与首请求诊断不能同时开启");
        if let Some(directory) = runtime.reuse_initial.as_mut() {
            if !directory.is_absolute() {
                *directory = base.join(&*directory);
            }
        }
        if runtime.prepare_only || runtime.reuse_initial.is_some() {
            assert!(!runtime.filter_only, "初始观察复用与过滤模式不能同时开启");
            assert!(!runtime.prepare_only || !runtime.first_request_only, "准备模式不运行首请求");
            assert!(
                ["simulator", "comparison_simulator", "reference", "observer", "toolchain"].iter().all(|role| {
                    runtime.initial_components.get(*role).is_some_and(|version| !version.trim().is_empty())
                }),
                "初始观察复用需要声明各组件的行为版本"
            );
        }
        assert!(
            !runtime.arms.is_empty()
                && runtime.arms.iter().all(|arm| ["B0", "B1", "B2", "T"].contains(&arm.as_str()))
                && runtime.arms.iter().collect::<BTreeSet<_>>().len() == runtime.arms.len(),
            "arms 必须为互异的 B0/B1/B2/T 子集"
        );
        assert!(!runtime.seeds.is_empty() && runtime.workers > 0 && runtime.budget > 0);
        assert!(!runtime.first_request_only || runtime.budget == 1, "首请求诊断预算必须为1");
        runtime
    }
}

#[derive(Deserialize, Serialize)]
struct Signals {
    treatment: Vec<String>,
    holdout: Vec<String>,
    universe: Vec<String>,
    random_selection_seed: u64,
}
#[derive(Clone, Deserialize, Serialize)]
struct Entry {
    sample: Sample,
    identity: ClassIdentity,
    selections: usize,
    score: usize,
    #[serde(default)]
    generation: usize,
}

fn admission_reason(
    arm: &str,
    novel_mismatch: bool,
    novel_model: impl FnOnce() -> bool,
    novel_perf: impl FnOnce() -> bool,
) -> Option<AdmissionReason> {
    let mismatch = novel_mismatch.then_some(AdmissionReason::NewMismatch);
    match arm {
        "B0" => None,
        "B1" => novel_model().then_some(AdmissionReason::NewModelCoverage).or(mismatch),
        "B2" | "T" => novel_perf().then_some(AdmissionReason::NewPerfSignature).or(mismatch),
        _ => unreachable!(),
    }
}

fn admit(
    entries: &mut Vec<Entry>,
    bursts: &mut VecDeque<(usize, bool)>,
    parent: usize,
    sample: &Sample,
    identity: &ClassIdentity,
    reason: Option<AdmissionReason>,
) -> Option<usize> {
    reason?;
    let index = entries.len();
    entries[parent].score = (entries[parent].score + 1).min(5);
    // 父 entry 奖励独立保存，连发四次按 A/B/A/B 请求，邻类不存在时沿用既有 A 规则。
    for form in [false, true, false, true] {
        bursts.push_back((parent, form));
    }
    entries.push(Entry {
        sample: sample.clone(),
        identity: identity.clone(),
        selections: 0,
        score: 1,
        generation: entries[parent].generation + 1,
    });
    Some(index)
}

fn choose(entries: &[Entry], guided: bool) -> usize {
    (0..entries.len())
        .min_by(|a, b| {
            ((entries[*a].selections + 1) as f64 / if guided { entries[*a].score as f64 } else { 1.0 })
                .total_cmp(&((entries[*b].selections + 1) as f64 / if guided { entries[*b].score as f64 } else { 1.0 }))
                .then(a.cmp(b))
        })
        .unwrap()
}

fn select_request<'a>(
    entries: &'a [Entry],
    classes: &'a [ClassIdentity],
    hits: &[usize],
    burst: Option<(usize, bool)>,
    guided: bool,
    rng: &mut impl RngCore,
) -> (usize, &'a ClassIdentity, &'static str) {
    let parent = burst.map_or_else(|| choose(entries, guided), |(parent, _)| parent);
    let neighbors = super::campaign::neighbors(&entries[parent].identity, classes, hits);
    let use_neighbor = burst.map(|(_, use_b)| use_b).unwrap_or_else(|| rng.next_u64() & 1 != 0);
    if use_neighbor && !neighbors.is_empty() {
        (parent, &classes[neighbors[0]], "B")
    } else {
        (parent, &entries[parent].identity, "A")
    }
}

fn complete_observation(result: &Value) -> bool {
    result["infrastructure"] != true && (result["agree"] == true || mismatch_feature(result).is_some())
}

fn mismatch_feature(result: &Value) -> Option<String> {
    if result["agree"] == true
        || result["infrastructure"] == true
        || matches!(result["bucket"].as_str(), Some("timeout" | "limit" | "framework-abort" | "other-failure"))
    {
        return None;
    }
    Some(serde_json::to_string(&json!({"bucket":result["bucket"],"reason":result["reason"],"xs_cause":result["xs_cause"],"nemu_cause":result["nemu_cause"],"side":result["isla_consistent_side"]})).unwrap())
}

fn append(file: &mut fs::File, row: &impl Serialize) {
    serde_json::to_writer(&mut *file, row).unwrap();
    file.write_all(b"\n").unwrap();
    file.flush().unwrap();
}

// 硬件并发独立于取点批量；返回次序仍与输入一致，避免线程完成次序改变反馈。
fn execute_batches<T: Send, R: Send>(items: Vec<T>, workers: usize, run: impl Fn(T) -> R + Sync) -> Vec<R> {
    assert!(workers > 0);
    let mut items = items.into_iter();
    let mut result = Vec::new();
    loop {
        let batch = items.by_ref().take(workers).collect::<Vec<_>>();
        if batch.is_empty() {
            break;
        }
        result.extend(std::thread::scope(|scope| {
            let run = &run;
            let handles = batch.into_iter().map(|item| scope.spawn(move || run(item))).collect::<Vec<_>>();
            handles.into_iter().map(|handle| handle.join().unwrap()).collect::<Vec<_>>()
        }));
    }
    result
}

fn campaign<B: BV>(
    options: &Options,
    runtime: &Runtime,
    platform: &testcase::Platform,
    signals: &Signals,
    random: &[String],
    all_selected: &[String],
    seed: u64,
    arm: &str,
    initial: &[Entry],
    initial_hardware: &[baseline::Observation],
    directory: &Directory,
    paths: &[ResidentPath<B>],
    shared: &SharedState<B>,
    target: &dyn Target<B>,
    executor: &mut impl Executor<Input = super::classifier::Job, Output = super::classifier::Outcome>,
    threads: usize,
) -> Value {
    let began = Instant::now();
    let output = options.output.join(format!("{arm}-seed-{seed}"));
    fs::create_dir(&output).unwrap();
    let mut events = fs::File::create(output.join("attempts.jsonl")).unwrap();
    let mut accepted_log = fs::File::create(output.join("certified.jsonl")).unwrap();
    let mut lineage_log = fs::File::create(output.join("lineage.jsonl")).unwrap();
    let mut curves = fs::File::create(output.join("curves.csv")).unwrap();
    writeln!(curves, "cases,heldout_signal_bins,heldout_signatures,corpus_entries,known_first,seconds").unwrap();
    let mut entries = initial.to_vec();
    let classes = initial.iter().map(|entry| entry.identity.clone()).collect::<Vec<_>>();
    let mut bursts = VecDeque::<(usize, bool)>::new();
    let mut coverage = super::feedback::CoverageFeedback::default();
    for entry in initial {
        let (buckets, potential) = super::value_features::extract(&entry.sample);
        coverage.observe(
            entry.sample.sample_id,
            &super::feedback::Feature { identity: entry.identity.clone(), buckets, potential, mismatch: None },
        );
    }
    let selected = if arm == "B2" { random } else { &signals.treatment };
    let baseline = baseline::State::new(initial_hardware, selected, &signals.holdout);
    let mut feedback_perf = baseline.feedback;
    let mut heldout = baseline.heldout;
    let initial_mismatches = baseline.mismatches;
    let mut mismatches = initial_mismatches.clone();
    let mut new_candidates = BTreeSet::new();
    let mut cases = 0usize;
    let mut attempts = 0usize;
    let mut known_first = baseline.known_first;
    writeln!(
        curves,
        "0,{},{},{},{},0",
        heldout.bins.len(),
        heldout.signatures.len(),
        initial.len(),
        known_first.map_or(String::new(), |value| value.to_string())
    )
    .unwrap();
    curves.flush().unwrap();
    let mut last_progress = Instant::now();
    let mut form_counts = BTreeMap::<String, usize>::new();
    let mut rejected = BTreeMap::<String, usize>::new();
    let mut infrastructure = 0usize;
    let mut agree = 0usize;
    let mut hits = vec![0usize; classes.len()];
    let first_mutant = initial.iter().map(|entry| entry.sample.sample_id).max().unwrap() + 1;
    GenerationPool::with_domain(
        paths,
        shared,
        target,
        threads,
        &options.mutation_config,
        runtime.input_domain.as_ref(),
        |generator| {
            while cases < runtime.budget
                && !(runtime.first_request_only && attempts > 0)
                && !STOP.load(Ordering::SeqCst)
                && last_progress.elapsed().as_secs() < 1800
            {
                let batch = options.batch_size.min(threads).min(runtime.budget - cases);
                let mut jobs = Vec::new();
                for _ in 0..batch {
                    let stream = attempts as u64;
                    let id = first_mutant + stream;
                    let mut rng = random_stream(seed, &options.scenario, stream);
                    let burst = bursts.pop_front();
                    let (parent, identity, operator) =
                        select_request(&entries, &classes, &hits, burst, arm != "B0", &mut rng);
                    let path_index = paths.iter().position(|path| path.signature == identity.path_signature).unwrap();
                    let record = json!({"sample_id":id,"attempt":attempts,"parent_entry":parent,"parent_sample_id":entries[parent].sample.sample_id,"parent_identity":entries[parent].identity,"target_identity":identity,"operator":operator,"forced_burst":burst.is_some(),"rng_stream":stream});
                    entries[parent].selections += 1;
                    jobs.push(Job { target_index: path_index, parent: entries[parent].sample.clone(), record, rng });
                    attempts += 1;
                }
                generator.submit(jobs);
                let mut inputs = Vec::new();
                let mut records = Vec::new();
                for (id, sample, record) in generator.drain() {
                    if record["attempt"] == 0 {
                        io::write_json(&output.join("first-request.json"), &json!({"record":&record,"sample":&sample}));
                    }
                    if runtime.first_request_only {
                        continue;
                    }
                    let Some(sample) = sample else {
                        let reason = record["generation_status"].as_str().unwrap_or("target_class_exhausted");
                        *rejected.entry(reason.into()).or_default() += 1;
                        append(&mut events, &json!({"sample_id":id,"record":record,"accepted":false,"reason":reason}));
                        continue;
                    };
                    if let Err(exclusion) = eligibility::precheck(&sample) {
                        for reason in &exclusion.reasons {
                            *rejected.entry(reason.clone()).or_default() += 1;
                        }
                        append(
                            &mut events,
                            &json!({"sample_id":id,"record":record,"accepted":false,"phase":"precheck","exclusion":exclusion}),
                        );
                        continue;
                    }
                    inputs.push(sample);
                    records.push(record);
                }
                if inputs.is_empty() {
                    continue;
                }
                let judged = super::classifier::classify(executor, &inputs, true, runtime.workers);
                let mut prepared = Vec::new();
                for (row, record) in judged.into_iter().zip(records) {
                    let row = row.expect("mutant未被完整DAG接纳");
                    assert_eq!(row["guard_unique"], true);
                    assert_eq!(row["post_unique"], true);
                    let identity = directory.identity(&options.scenario, &row);
                    assert_eq!(
                        serde_json::to_value(&identity).unwrap(),
                        record["target_identity"],
                        "mutant未命中目标类"
                    );
                    let mut sample: Sample = serde_json::from_value(row["sample"].clone()).unwrap();
                    sample.class_id = Some(directory.classes[&identity].0);
                    match eligibility::check(&sample, platform) {
                        Ok(generated) => prepared.push((sample, generated, record, identity, row)),
                        Err(exclusion) => {
                            for reason in &exclusion.reasons {
                                *rejected.entry(reason.clone()).or_default() += 1;
                            }
                            append(
                                &mut events,
                                &json!({"record":record,"accepted":false,"phase":"complete_testcase","exclusion":exclusion}),
                            );
                        }
                    }
                }
                let hardware =
                    execute_batches(prepared, runtime.workers, |(sample, generated, record, identity, row)| {
                        let directory = output.join(format!("case-{:06}", sample.sample_id));
                        (
                            emu::run(
                                runtime,
                                platform,
                                sample,
                                generated,
                                &directory,
                                known_first.is_none(),
                                all_selected,
                            ),
                            record,
                            identity,
                            row,
                        )
                    });
                for (hardware, record, identity, certification) in hardware {
                    let Some(observation) = observe::record_mutant(
                        &record,
                        &hardware.fixed,
                        &mut lineage_log,
                        &mut cases,
                        &mut infrastructure,
                    ) else {
                        append(
                            &mut events,
                            &json!({"record":record,"accepted":false,"phase":"hardware_infrastructure","fixed":hardware.fixed}),
                        );
                        continue;
                    };
                    last_progress = Instant::now();
                    *form_counts.entry(record["operator"].as_str().unwrap().to_owned()).or_default() += 1;
                    let parent = record["parent_entry"].as_u64().unwrap() as usize;
                    let mismatch = &observation.mismatch_signature;
                    let novel_mismatch = mismatch.as_ref().is_some_and(|key| mismatches.insert(key.clone()));
                    let (buckets, potential) = super::value_features::extract(&hardware.sample);
                    let feature =
                        super::feedback::Feature { identity: identity.clone(), buckets, potential, mismatch: None };
                    let reason = admission_reason(
                        arm,
                        novel_mismatch,
                        || coverage.is_novel(&feature),
                        || !hardware.perf.is_empty() && feedback_perf.observe(&hardware.perf, selected),
                    );
                    coverage.observe(hardware.sample.sample_id, &feature);
                    if !hardware.perf.is_empty() {
                        heldout.observe(&hardware.perf, &signals.holdout);
                    }
                    if observation.agree {
                        agree += 1;
                    }
                    let case_dir = hardware.built.elf.parent().unwrap();
                    // 已知问题必须同时满足独立NEMU窄规则、修复版一致和未修版重放。
                    if known_first.is_none()
                        && hardware.baseline["mismatch"]["known_rule"] == observe::KNOWN_RULE
                        && hardware.fixed["agree"] == true
                    {
                        let replay = emu::probe(
                            runtime,
                            &hardware.sample,
                            platform,
                            &hardware.generated,
                            &hardware.built,
                            &case_dir.join("known-replay"),
                            true,
                            &[],
                        )
                        .0;
                        if replay["mismatch"]["known_rule"] == observe::KNOWN_RULE {
                            known_first = Some(cases);
                        }
                    }
                    let mut confirmed_candidate = false;
                    if let Some(key) = mismatch {
                        if !initial_mismatches.contains(key) && !new_candidates.contains(key) {
                            let replay = emu::probe(
                                runtime,
                                &hardware.sample,
                                platform,
                                &hardware.generated,
                                &hardware.built,
                                &case_dir.join("fixed-replay"),
                                false,
                                all_selected,
                            )
                            .0;
                            if mismatch_feature(&replay).as_ref() == Some(key) {
                                new_candidates.insert(key.clone());
                                confirmed_candidate = true;
                            }
                        }
                    }
                    let new_entry_index = admit(&mut entries, &mut bursts, parent, &hardware.sample, &identity, reason);
                    append(
                        &mut lineage_log,
                        &lineage::Mutant::new(
                            &record,
                            &entries[parent],
                            &identity,
                            observation,
                            arm,
                            reason,
                            new_entry_index,
                        ),
                    );
                    if let Some(index) = classes.iter().position(|class| class == &identity) {
                        hits[index] += 1;
                    }
                    append(
                        &mut accepted_log,
                        &json!({"case":cases,"record":record,"certification":certification,"sample":hardware.sample,"fixed":hardware.fixed,"baseline":hardware.baseline,"new_feedback":reason.is_some(),"new_divergence_candidate_replayed":confirmed_candidate,"corpus_entries":entries.len()}),
                    );
                    writeln!(
                        curves,
                        "{cases},{},{},{},{},{}",
                        heldout.bins.len(),
                        heldout.signatures.len(),
                        entries.len(),
                        known_first.map_or(String::new(), |v| v.to_string()),
                        began.elapsed().as_secs_f64()
                    )
                    .unwrap();
                    curves.flush().unwrap();
                    if hardware.fixed["agree"] == true
                        && (hardware.baseline.is_null() || hardware.baseline["agree"] == true)
                    {
                        fs::remove_file(&hardware.built.elf).unwrap();
                        fs::remove_file(case_dir.join("objdump.txt")).unwrap();
                    }
                }
                eprintln!(
                    "[ABLATION_PROGRESS] {}",
                    json!({"arm":arm,"seed":seed,"cases":cases,"budget":runtime.budget,"attempts":attempts,"heldout":heldout.summary(),"corpus":entries.len(),"known_first":known_first})
                );
            }
        },
    );
    assert!(arm != "B0" || entries.len() == initial.len(), "B0 不应新增 corpus entry");
    let summary = json!({"arm":arm,"seed":seed,"budget":runtime.budget,"cases":cases,"attempts":attempts,"complete":if runtime.first_request_only {attempts==1}else{cases==runtime.budget},"first_request_only":runtime.first_request_only,"seconds":began.elapsed().as_secs_f64(),"agree":agree,"infrastructure":infrastructure,"initial_corpus":initial.len(),"final_corpus":entries.len(),"corpus_added":entries.len()-initial.len(),"heldout":heldout.summary(),"R_XS_001_first":known_first,"replayed_new_divergence_signature_candidates":new_candidates,"forms":form_counts,"rejected_attempt_reasons":rejected,"rejected_reasons_may_overlap":true,"stop_without_progress_seconds":last_progress.elapsed().as_secs_f64()});
    io::write_json(&output.join("summary.json"), &summary);
    summary
}

pub(super) fn run<B: BV>(
    options: &Options,
    corpus: &[Sample],
    corpus_rows: &[Option<Value>],
    directory: &Directory,
    paths: &[ResidentPath<B>],
    shared: &SharedState<B>,
    target: &dyn Target<B>,
    executor: &mut impl Executor<Input = super::classifier::Job, Output = super::classifier::Outcome>,
    threads: usize,
    judge_seconds: f64,
) {
    disable_core_dumps();
    let runtime = Runtime::read(options.inputs.as_ref().expect("ablation需要--fuzz-inputs runtime.json"));
    let platform_config = fs::read(&runtime.platform).unwrap();
    let platform: testcase::Platform = serde_json::from_slice(&platform_config).unwrap();
    let filter_started = Instant::now();
    let signals: Signals = serde_json::from_reader(fs::File::open(&runtime.signals).unwrap()).unwrap();
    let excluded_names = signals.treatment.iter().chain(&signals.holdout).cloned().collect::<BTreeSet<_>>();
    assert_eq!(excluded_names.len(), signals.treatment.len() + signals.holdout.len(), "T与留出信号必须互斥");
    let mut pool = signals.universe.iter().filter(|name| !excluded_names.contains(*name)).cloned().collect::<Vec<_>>();
    pool.shuffle(&mut random_stream(signals.random_selection_seed, "perf-counter-selection", 0));
    let random = pool[..signals.treatment.len()].to_vec();
    io::write_json(&options.output.join("input-domain.json"), &runtime.input_domain);
    io::write_json(
        &options.output.join("signal-selection.json"),
        &json!({"T":signals.treatment,"B2":random,"holdout":signals.holdout,"random_selection_seed":signals.random_selection_seed}),
    );
    let all_selected = signals
        .treatment
        .iter()
        .chain(&random)
        .chain(&signals.holdout)
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let mut filter_log = fs::File::create(options.output.join("corpus-filter.jsonl")).unwrap();
    let mut primary = BTreeMap::<String, usize>::new();
    let mut reasons = BTreeMap::<String, usize>::new();
    let mut entries = Vec::new();
    let mut generated_inputs = Vec::new();
    for (input, row) in corpus.iter().zip(corpus_rows) {
        let row = row.as_ref().unwrap();
        let sample: Sample = serde_json::from_value(row["sample"].clone()).unwrap();
        let identity = directory.identity(&options.scenario, row);
        match eligibility::check(&sample, &platform) {
            Ok(generated) => {
                generated_inputs.push(generated);
                append(
                    &mut filter_log,
                    &json!({"sample_id":input.sample_id,"identity":identity,"accepted":true,"reasons":[]}),
                );
                entries.push(Entry { sample, identity, selections: 0, score: 1, generation: 0 });
            }
            Err(exclusion) => {
                *primary.entry(exclusion.reasons.first().unwrap().clone()).or_default() += 1;
                for reason in &exclusion.reasons {
                    *reasons.entry(reason.clone()).or_default() += 1;
                }
                append(
                    &mut filter_log,
                    &json!({"sample_id":input.sample_id,"identity":identity,"accepted":false,"exclusion":exclusion}),
                );
            }
        }
    }
    let counts = |counts: &BTreeMap<String, usize>| {
        counts.iter().map(|(reason,count)|json!({"reason":reason,"count":count,"fraction_of_input_candidates":*count as f64/corpus.len() as f64})).collect::<Vec<_>>()
    };
    io::write_json(
        &options.output.join("filter-summary.json"),
        &json!({"total_entries":corpus.len(),"input_guard_classes":directory.classes.len(),"kept_entries":entries.len(),"kept_guard_classes":entries.iter().map(|e|&e.identity).collect::<BTreeSet<_>>().len(),"excluded_entries":corpus.len()-entries.len(),"excluded_fraction":(corpus.len()-entries.len()) as f64/corpus.len() as f64,"primary_reason_counts":counts(&primary),"all_reason_counts":counts(&reasons),"all_reason_counts_overlap":true}),
    );
    io::write_lines(
        &options.output.join("executable-corpus.jsonl"),
        &entries.iter().map(|entry| &entry.sample).collect::<Vec<_>>(),
    );
    if runtime.filter_only {
        return;
    }
    assert!(!entries.is_empty(), "硬件过滤后corpus为空，详见filter-summary.json");
    if runtime.prepare_only {
        install_stop_handlers();
    }
    let checkpointed = runtime.prepare_only || runtime.reuse_initial.is_some();
    let conditions = if checkpointed {
        json!({
            "protocol":baseline::PROTOCOL,
            "platform":serde_json::from_slice::<Value>(&platform_config).unwrap(),
            "components":runtime.initial_components,
            "timeout_seconds":runtime.timeout_seconds,
        })
    } else {
        Value::Null
    };
    let initial_inputs = entries
        .iter()
        .zip(generated_inputs)
        .map(|(entry, generated)| {
            let input = checkpointed.then(|| baseline::input_reference(&entry.sample, &generated));
            (input, (&entry.sample, generated))
        })
        .collect();
    let initial_hardware = baseline::initial_observations(
        &runtime,
        &options.output,
        initial_inputs,
        &all_selected,
        &signals,
        conditions,
        judge_seconds,
        filter_started.elapsed().as_secs_f64(),
        |(sample, generated), directory| {
            emu::observe_initial(&runtime, &platform, sample, generated, directory, &all_selected)
        },
    );
    if runtime.prepare_only {
        return;
    }
    install_stop_handlers();
    let mut summaries = Vec::new();
    let mut first_comparisons = Vec::new();
    for seed in &runtime.seeds {
        let mut expected_first = None::<Value>;
        for arm in &runtime.arms {
            if STOP.load(Ordering::SeqCst) {
                break;
            }
            summaries.push(campaign(
                options,
                &runtime,
                &platform,
                &signals,
                &random,
                &all_selected,
                *seed,
                arm,
                &entries,
                &initial_hardware,
                directory,
                paths,
                shared,
                target,
                executor,
                threads,
            ));
            let first_path = options.output.join(format!("{arm}-seed-{seed}/first-request.json"));
            if first_path.exists() {
                let first: Value = serde_json::from_reader(fs::File::open(first_path).unwrap()).unwrap();
                let input = json!({"parent":first["record"]["parent_identity"],"target":first["record"]["target_identity"],"operator":first["record"]["operator"],"pre_registers":first["sample"]["pre_registers"],"pre_memory":first["sample"]["pre_memory"]});
                let same = expected_first.as_ref().is_none_or(|expected| expected == &input);
                first_comparisons.push(json!({"seed":seed,"arm":arm,"same_first_request":same}));
                io::write_json(&options.output.join("first-request-comparison.json"), &first_comparisons);
                assert!(same, "相同随机流的四臂首请求不一致");
                expected_first.get_or_insert(input);
            }
            io::write_json(
                &options.output.join("ablation-summary.json"),
                &json!({"runs":summaries,"complete":summaries.len()==runtime.seeds.len()*runtime.arms.len() && summaries.iter().all(|row|row["complete"]==true)}),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn infrastructure_observations_cannot_update_budget_or_feedback() {
        assert!(!complete_observation(&json!({"agree":false,"infrastructure":true,"bucket":"mismatch"})));
        assert!(!complete_observation(&json!({"agree":false,"bucket":"timeout"})));
        assert!(complete_observation(&json!({"agree":true})));
        assert!(complete_observation(
            &json!({"agree":false,"infrastructure":false,"bucket":"mismatch","reason":"cause"})
        ));
    }
    #[test]
    fn novelty_reward_is_per_entry_and_baseline_rotates() {
        let sample = super::super::tests::example_sample();
        let identity = ClassIdentity { scenario_config_id: "test".into(), path_signature: 1, guard_vector: "0".into() };
        let mut entries = vec![
            Entry { sample: sample.clone(), identity: identity.clone(), selections: 0, score: 1, generation: 0 },
            Entry { sample, identity, selections: 0, score: 4, generation: 0 },
        ];
        assert_eq!(choose(&entries, false), 0);
        assert_eq!(choose(&entries, true), 1);
        entries[0].selections = 1;
        assert_eq!(choose(&entries, false), 1);
    }
}

#[cfg(test)]
mod batch_tests {
    use super::*;
    #[test]
    fn hardware_batches_bound_parallelism_and_keep_input_order() {
        use std::sync::atomic::AtomicUsize;
        let active = AtomicUsize::new(0);
        let peak = AtomicUsize::new(0);
        let result = execute_batches((0..12).collect(), 3, |i| {
            let count = active.fetch_add(1, Ordering::SeqCst) + 1;
            peak.fetch_max(count, Ordering::SeqCst);
            std::thread::sleep(std::time::Duration::from_millis(5));
            active.fetch_sub(1, Ordering::SeqCst);
            i * 2
        });
        assert_eq!(result, (0..12).map(|i| i * 2).collect::<Vec<_>>());
        assert!(peak.load(Ordering::SeqCst) <= 3);
        assert_eq!(active.load(Ordering::SeqCst), 0);
    }
}

#[cfg(test)]
mod runtime_tests {
    use super::*;
    #[test]
    fn compiler_alias_is_preserved_for_companion_tool_lookup() {
        use std::os::unix::fs::symlink;
        let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join(format!("output/ablation-runtime-unit-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let program = std::env::current_exe().unwrap();
        let compiler = directory.join("tool-gcc");
        if compiler.exists() {
            fs::remove_file(&compiler).unwrap();
        }
        symlink(&program, &compiler).unwrap();
        let mut config = json!({"seeds":[42],"budget":1,"workers":1,"timeout_seconds":1});
        for key in ["loader", "library_path", "emu", "unpatched", "nemu", "observer", "platform", "signals"] {
            config[key] = json!(program);
        }
        config["compiler"] = json!(compiler);
        let path = directory.join("runtime.json");
        io::write_json(&path, &config);
        let runtime = Runtime::read(&path);
        assert_eq!(runtime.compiler, compiler, "编译器别名决定nm／objdump的文件名前缀");
        assert!(!runtime.prepare_only);
        assert!(runtime.reuse_initial.is_none());

        config["prepare_only"] = json!(true);
        config["reuse_initial"] = json!("observations");
        config["initial_components"] = json!({
            "simulator":"fixed-v1","comparison_simulator":"baseline-v1","reference":"reference-v1",
            "observer":"observer-v1","toolchain":"toolchain-v1",
        });
        io::write_json(&path, &config);
        let runtime = Runtime::read(&path);
        assert!(runtime.prepare_only);
        assert_eq!(runtime.reuse_initial, Some(directory.join("observations")));
        fs::remove_dir_all(directory).unwrap();
    }
}
