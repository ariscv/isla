use super::*;
use crate::isarch::target::RV64;
use dto::{CheckpointData, HeadPrefix, TraceWriter};
use isla_lib::{
    bitvector::b64::B64,
    error::ExecError,
    executor::samples::{SamplePath, Terminal},
    ir::{Symtab, Val},
    smt::{self, Model, SmtResult},
    source_loc::SourceLoc,
};

#[test]
fn shared_arm_error_leaf_publication_matches_legacy_cache_and_judge() {
    smt::configure_tastic(smt::Tactic::Qfaufbv);
    let shared = SharedState::<B64>::empty(Symtab::new());
    let context = Context::new(Config::new());
    // 旧保存布局的金样来自执行器的真实错误叶：共同父段和头部前缀，两臂各有守卫。
    let golden: Value =
        serde_json::from_str(include_str!("../../../isla-lib/src/smt/testdata/arm-error-snapshots.json")).unwrap();
    let checkpoints: [CheckpointData; 2] = serde_json::from_value(golden["cache"][0].clone()).unwrap();
    let flat: Vec<Segment<B64>> = serde_json::from_value(golden["cache"][1].clone()).unwrap();
    let mut compact: Vec<_> = flat.iter().cloned().map(LinkedSegment::from).collect();
    let shared_prefix: Vec<_> = compact[1].events.drain(..2).collect();
    assert_eq!(compact[2].events.drain(..2).collect::<Vec<_>>(), shared_prefix);
    compact[1].head_prefix = Some(HeadPrefix::Define(shared_prefix));
    compact[2].head_prefix = Some(HeadPrefix::Reference(1));
    let reader = TraceReader::from_linked(&compact);
    let paths = checkpoints
        .iter()
        .enumerate()
        .map(|(index, point)| {
            let flag = Val::Symbolic(Sym::from_u32(0));
            ResidentPath {
                signature: 42 + index as u64,
                checkpoint: reader.restore(point),
                path: SamplePath {
                    terminal: Terminal::ExecutionError {
                        message: format!("失败臂 {index}"),
                        location: "fixture.sail:42".into(),
                    },
                    pre: [("input".into(), flag.clone())].into(),
                    post: [("output".into(), flag.clone())].into(),
                    result: flag,
                    memory: vec![],
                    memory_guards: Default::default(),
                },
                records: Vec::new().into(),
                pure_definitions: vec![],
            }
        })
        .collect::<Vec<_>>();
    let facts = [
        Facts { guard_unique: true, post_unique: true, simple_pre: true },
        Facts { guard_unique: false, post_unique: true, simple_pre: true },
    ];
    let fast_facts = facts.clone().map(Into::into);
    let directory =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(format!("output/shared-error-cache-{}", std::process::id()));
    fs::create_dir_all(directory.parent().unwrap()).unwrap();
    fs::create_dir(&directory).unwrap();
    let stages = Stages::new(Some(&directory), Instant::now());
    let cache = directory.join("cache");
    let source = json!({"command":[],"inputs":{},"binary":{"path":"fixture","sha256":"fixture"}});
    let summary = super::super::solve_summary::SolveSummary::default().json();
    let publish = |dir: PathBuf, paths: &[ResidentPath<B64>]| {
        save(
            &Options { write: Some(dir), format: vec![Encoding::Json, Encoding::Bin], ..Default::default() },
            "generic",
            paths,
            &fast_facts,
            &shared,
            &RV64::default(),
            &summary,
            &source,
            &mut Timing::default(),
            &stages,
        );
    };
    publish(cache.clone(), &paths);
    assert!(!cache.join("manifest.pending").exists());
    let rows = fs::read_to_string(directory.join("path-cache-stages.jsonl"))
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str::<Value>(line).unwrap())
        .collect::<Vec<_>>();
    let capture = rows.iter().find(|row| row["stage"] == "cache_capture").unwrap();
    for (name, detail) in [("convert", "conversion"), ("validate", "validation"), ("write", "write")] {
        let start = format!("cache_capture_{name}_begin");
        let end = format!("cache_capture_{name}_end");
        assert!(rows.iter().any(|row| row["stage"] == start));
        assert!(rows.iter().any(|row| row["stage"] == end));
        let phase = &capture[detail];
        assert!(phase["start"]["at_seconds"].as_f64().unwrap() <= phase["end"]["at_seconds"].as_f64().unwrap());
        if cfg!(target_os = "linux") {
            assert!(phase["start"]["rss_bytes"].as_u64().unwrap() > 0);
            assert!(phase["end"]["rss_bytes"].as_u64().unwrap() > 0);
        }
    }
    let manifest_path = cache.join("manifest.json");
    let mut manifest: Value = serde_json::from_reader(File::open(&manifest_path).unwrap()).unwrap();
    assert_eq!(manifest["schema_version"], 7);
    assert_eq!(manifest["execution_error_paths"], 2);
    let actual: Envelope<LinkedSegment<B64>> =
        serde_json::from_reader(File::open(cache.join("segments.json")).unwrap()).unwrap();
    assert_eq!(actual.entries, compact);
    let expected_paths = paths
        .iter()
        .zip(&checkpoints)
        .zip(&facts)
        .map(|((path, point), facts)| capture_path(path, point.clone(), facts.clone()))
        .collect::<Vec<_>>();

    let sample = |path: &ResidentPath<B64>| {
        let mut solver = Solver::from_checkpoint(&context, path.checkpoint.clone());
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        let mut model = Model::new(&solver);
        let mut input_path = path.path.clone();
        input_path.terminal = Terminal::Normal;
        input_path.materialize(&mut model, &shared, "fork", path.signature, None).unwrap()
    };
    let inputs = paths.iter().map(sample).collect::<Vec<_>>();
    for schema in [7, 6] {
        if schema == 6 {
            let envelope = Envelope { batch_id: actual.batch_id.clone(), entries: flat.clone() };
            serde_json::to_writer(File::create(cache.join("segments.json")).unwrap(), &envelope).unwrap();
            bincode::serialize_into(File::create(cache.join("segments.bin")).unwrap(), &envelope).unwrap();
            manifest["schema_version"] = json!(schema);
            serde_json::to_writer(File::create(&manifest_path).unwrap(), &manifest).unwrap();
        }
        for encoding in [Encoding::Json, Encoding::Bin] {
            let restored = load(&cache, encoding, true, &shared, "generic", &stages);
            assert_eq!(restored.facts, facts);
            let mut writer = TraceWriter::default();
            for (index, (resident, fact)) in restored.paths.iter().zip(restored.facts).enumerate() {
                assert_eq!(capture_path(resident, writer.capture(&resident.checkpoint), fact), expected_paths[index]);
                let mut solver = Solver::from_checkpoint(&context, resident.checkpoint.clone());
                for (input_index, input) in inputs.iter().enumerate() {
                    let actual = resident.path.judge(
                        &mut solver,
                        &shared,
                        input,
                        &resident.records,
                        resident.signature,
                        |_, _| panic!("错误叶不能导出样本"),
                    );
                    if index == input_index {
                        match actual {
                            Err(ExecError::ReachableExecutionError { message, location }) => {
                                assert_eq!(
                                    Terminal::ExecutionError { message, location },
                                    expected_paths[index].path.terminal
                                );
                            }
                            _ => panic!("同侧输入必须报告可达错误叶"),
                        }
                    } else {
                        assert!(actual.unwrap().is_none());
                    }
                }
            }
            assert_eq!(writer.segments, flat);
        }
    }
    let failed = directory.join("invalid");
    let mut paths = paths;
    paths[1].signature = paths[0].signature;
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| publish(failed.clone(), &paths))).is_err());
    assert!(failed.join("segments.bin").exists(), "应在已写完段文件后触发路径校验失败");
    assert!(!failed.join("manifest.json").exists());
    fs::remove_dir_all(directory).unwrap();
}
