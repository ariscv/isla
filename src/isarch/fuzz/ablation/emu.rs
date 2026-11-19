//! 本机Rust执行与独立NEMU观察；外部整场任务由scheduler约束。
use super::super::testcase::{self, Built, Generated, Platform};
use super::{baseline::Observation, classify, io, mismatch_feature, observe, perf, Runtime, STOP};
use isla_lib::executor::samples::Sample;
use serde::Serialize;
use serde_json::{json, Value};
use std::{
    collections::BTreeMap,
    fs,
    os::unix::process::{CommandExt, ExitStatusExt},
    path::Path,
    process::{Command, Stdio},
    sync::atomic::Ordering,
    time::{Duration, Instant},
};

pub(super) struct ResultRow {
    pub sample: Sample,
    pub generated: Generated,
    pub built: Built,
    pub fixed: Value,
    pub baseline: Value,
    pub perf: BTreeMap<String, u64>,
    pub build_seconds: f64,
}

fn warmup(built: &Built, writes: usize) -> usize {
    let disassembly = fs::read_to_string(built.elf.parent().unwrap().join("objdump.txt")).unwrap();
    let prefix = disassembly
        .lines()
        .filter(|line| {
            let words = line.split_whitespace().collect::<Vec<_>>();
            if words.len() < 3 || !words[0].ends_with(':') || words[1].len() != 8 {
                return false;
            }
            u64::from_str_radix(words[0].trim_end_matches(':'), 16)
                .is_ok_and(|pc| pc >= built.symbols["_start"] && pc < built.symbols["payload_ins"])
        })
        .count();
    prefix + writes.saturating_sub(1) * 5 + 6 - if writes == 0 { 5 } else { 0 }
}

pub(super) fn probe(
    runtime: &Runtime,
    sample: &Sample,
    platform: &Platform,
    generated: &Generated,
    built: &Built,
    directory: &Path,
    baseline: bool,
    selected: &[String],
) -> (Value, BTreeMap<String, u64>) {
    fs::create_dir_all(directory).unwrap();
    let directory = fs::canonicalize(directory).unwrap();
    let stdout = fs::File::create(directory.join("stdout.log")).unwrap();
    let stderr = fs::File::create(directory.join("stderr.log")).unwrap();
    let emulator = if baseline { &runtime.unpatched } else { &runtime.emu };
    let warmup = warmup(built, generated.writes.len());
    let arguments = vec![
        "--library-path".to_owned(),
        runtime.library_path.display().to_string(),
        emulator.display().to_string(),
        "-i".into(),
        built.elf.display().to_string(),
        "--diff".into(),
        runtime.observer.display().to_string(),
        "-C".into(),
        "100000".into(),
        "-W".into(),
        warmup.to_string(),
        "--force-dump-result".into(),
    ];
    let trace_path = directory.join("native-nemu-trace.jsonl");
    match fs::remove_file(&trace_path) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => panic!("清理上次观察追踪失败：{error}"),
    }
    let started = Instant::now();
    let mut child = Command::new(&runtime.loader)
        .args(&arguments)
        .current_dir(&directory)
        .env("LD_LIBRARY_PATH", &runtime.library_path)
        .env("XIANGSHAN_DIFF_SO", &runtime.nemu)
        .env("PAYLOAD_PC", format!("{:#x}", built.symbols["payload_ins"]))
        .env("EXIT_LOW", format!("{:#x}", built.symbols["good_trap_ins"]))
        .env("EXIT_HIGH", format!("{:#x}", built.symbols["fail_memory_trap"]))
        .stdin(Stdio::null())
        .stdout(stdout)
        .stderr(stderr)
        .process_group(0)
        .spawn()
        .expect("启动emu失败");
    let mut timed_out = false;
    let code = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status.code().map(i64::from).or_else(|| status.signal().map(|s| -i64::from(s)));
        }
        if STOP.load(Ordering::SeqCst) || started.elapsed() > Duration::from_secs(runtime.timeout_seconds) {
            timed_out = true;
            unsafe {
                libc::kill(-(child.id() as i32), libc::SIGTERM);
            }
            std::thread::sleep(Duration::from_millis(100));
            unsafe {
                libc::kill(-(child.id() as i32), libc::SIGKILL);
            }
            child.wait().expect("回收emu失败");
            break None;
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let out = fs::read_to_string(directory.join("stdout.log")).unwrap();
    let err = fs::read_to_string(directory.join("stderr.log")).unwrap();
    let log = format!("{out}\n{err}");
    let mut result = classify::classify_log(&log, code, &built.symbols);
    let trace = if !timed_out && log.contains("ECFG3_NATIVE child_status=0") && trace_path.exists() {
        fs::read_to_string(trace_path)
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).expect("NEMU追踪损坏"))
            .collect::<Vec<Value>>()
    } else {
        Vec::new()
    };
    if !trace.is_empty() {
        result = observe::finish_result(
            sample,
            generated,
            platform,
            &built.symbols,
            result,
            &trace,
            &log,
            &directory.display().to_string(),
        );
    } else {
        result["infrastructure"] = json!(true);
        result["agree"] = json!(false);
        result["bucket"] = json!("other-failure");
    }
    let counters = if !baseline && !timed_out && result["agree"] == true {
        assert!(log.contains("Warmup finished"), "没有完成预热清零");
        perf::parse(&err)
    } else {
        BTreeMap::new()
    };
    let kept = selected
        .iter()
        .filter_map(|name| counters.get(name).map(|value| (name.clone(), *value)))
        .collect::<BTreeMap<_, _>>();
    result["elapsed_seconds"] = json!(started.elapsed().as_secs_f64());
    result["command"] = json!({"program":runtime.loader,"args":arguments,"warmup":warmup});
    io::write_json(&directory.join("result.json"), &result);
    if !kept.is_empty() {
        io::write_json(&directory.join("perf-selected.json"), &kept);
    }
    // 所选原始计数完整保留；只在成功例删除无关的22593项转储，避免长期占满数据盘。
    if result["agree"] == true {
        let compact = err.lines().filter(|line| !line.contains("[PERF ]")).collect::<Vec<_>>().join("\n");
        fs::write(directory.join("stderr.log"), compact).unwrap();
    }
    (result, counters)
}

pub(super) fn run(
    runtime: &Runtime,
    platform: &Platform,
    sample: Sample,
    generated: Generated,
    directory: &Path,
    baseline: bool,
    selected: &[String],
) -> ResultRow {
    fs::create_dir_all(directory).unwrap();
    let options =
        super::super::TestcaseOptions { compiler: runtime.compiler.clone(), entry_mode: testcase::EntryMode::Mprv };
    let started = Instant::now();
    let built = testcase::build(&generated, &options, directory).expect("L1编译失败");
    let build_seconds = started.elapsed().as_secs_f64();
    let (fixed, perf) =
        probe(runtime, &sample, platform, &generated, &built, &directory.join("fixed"), false, selected);
    let unpatched = if baseline && !STOP.load(Ordering::SeqCst) {
        probe(runtime, &sample, platform, &generated, &built, &directory.join("unpatched"), true, &[]).0
    } else {
        Value::Null
    };
    ResultRow { sample, generated, built, fixed, baseline: unpatched, perf, build_seconds }
}

#[derive(Default, Serialize)]
pub(super) struct InitialTiming {
    pub compile_seconds: f64,
    pub fixed_seconds: f64,
    pub baseline_seconds: f64,
    pub confirmation_seconds: f64,
    pub worker_seconds: f64,
    pub emu_runs: usize,
}

pub(super) fn observe_initial(
    runtime: &Runtime,
    platform: &Platform,
    sample: &Sample,
    generated: Generated,
    directory: &Path,
    selected: &[String],
) -> (Observation, InitialTiming) {
    let row = run(runtime, platform, sample.clone(), generated, directory, true, selected);
    let known_replay = if Observation::needs_known_replay(&row.fixed, &row.baseline) && !STOP.load(Ordering::SeqCst) {
        Some(
            probe(
                runtime,
                &row.sample,
                platform,
                &row.generated,
                &row.built,
                &directory.join("known-replay"),
                true,
                &[],
            )
            .0,
        )
    } else {
        None
    };
    let fixed_replay = if !STOP.load(Ordering::SeqCst) && mismatch_feature(&row.fixed).is_some() {
        Some(
            probe(
                runtime,
                &row.sample,
                platform,
                &row.generated,
                &row.built,
                &directory.join("fixed-replay"),
                false,
                selected,
            )
            .0,
        )
    } else {
        None
    };
    let seconds = |result: &Value| result["elapsed_seconds"].as_f64().unwrap_or(0.0);
    let timing = InitialTiming {
        compile_seconds: row.build_seconds,
        fixed_seconds: seconds(&row.fixed),
        baseline_seconds: seconds(&row.baseline),
        confirmation_seconds: known_replay.iter().chain(&fixed_replay).map(seconds).sum(),
        emu_runs: 1
            + usize::from(!row.baseline.is_null())
            + usize::from(known_replay.is_some())
            + usize::from(fixed_replay.is_some()),
        ..InitialTiming::default()
    };
    let observation =
        Observation { perf: row.perf, fixed: row.fixed, baseline: row.baseline, known_replay, fixed_replay };
    (observation, timing)
}
