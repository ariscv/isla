//! isarch 缓存适配：来源、文件发布、Target 数据和常驻路径。
#[cfg(test)]
#[path = "path_cache_memory_write_tests.rs"]
mod memory_write_tests;
#[cfg(test)]
#[path = "path_cache/publish_tests.rs"]
mod publish_tests;
#[cfg(test)]
mod tests {
    use super::*;
    use dto::TraceWriter;
    use isla_lib::{bitvector::b64::B64, ir::Symtab};
    use std::time::{SystemTime, UNIX_EPOCH};
    #[test]
    fn 阶段日志立即落盘并保留顺序() {
        let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join(format!("output/path-cache/stages-test-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let stages = Stages::new(Some(&directory), Instant::now());
        stages.record("exploration", 1.0, json!({"paths": 2}));
        stages.record("dag", 2.0, json!({}));
        let rows = fs::read_to_string(directory.join("path-cache-stages.jsonl"))
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str::<Value>(line).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            rows.iter().map(|row| row["stage"].as_str().unwrap()).collect::<Vec<_>>(),
            vec!["exploration", "dag"]
        );
        assert_eq!(rows[0]["seconds"], 1.0);
        assert!(rows.iter().all(|row| row["since_start"].as_f64().unwrap() >= 0.0));
        fs::remove_dir_all(directory).unwrap();
    }
    #[test]
    fn solver_timeout_invalid_cache_is_rejected_before_loading_data() {
        let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join(format!("output/path-cache/solver-invalid-test-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let shared = SharedState::<B64>::empty(Symtab::new());
        for raw in [
            json!({"schema_version":CACHE_SCHEMA_VERSION, "valid":false, "invalid_reasons":["solver_timeout_dropped_paths"]}),
            json!({"schema_version":3, "errors":{"valid":false}}),
        ] {
            fs::write(directory.join("manifest.json"), serde_json::to_vec(&raw).unwrap()).unwrap();
            let error = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                load::<B64>(&directory, Encoding::Json, false, &shared, "generic", &Stages::new(None, Instant::now()))
            }));
            let Err(error) = error else {
                panic!("已作废的缓存被接纳");
            };
            let message = error.downcast_ref::<String>().expect("期望明确的作废错误");
            assert!(message.contains("路径缓存结果作废") && message.contains("--check-samples"));
        }
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    #[should_panic(expected = "manifest")]
    fn 残缺目录必须拒绝() {
        let shared = SharedState::<B64>::empty(Symtab::new());
        load::<B64>(
            std::path::Path::new("output/path-cache/不存在的缓存"),
            Encoding::Json,
            false,
            &shared,
            "generic",
            &Stages::new(None, Instant::now()),
        );
    }
    #[test]
    #[should_panic(expected = "批次")]
    fn 混合批次必须拒绝() {
        let envelope = Envelope { batch_id: "old".into(), entries: vec![1u32] };
        let entry =
            DataFile { file: "paths.json".into(), encoding: Encoding::Json, entries: 1, batch_id: "new".into() };
        check_envelope(&envelope, &entry, "new");
    }
    #[test]
    fn dag_only_requires_write_and_parses_without_enumeration() {
        let mut cli = getopts::Options::new();
        Options::add_cli(&mut cli);
        let matches = cli.parse(["--path-cache-only", "--path-cache-write", "unused"]).unwrap();
        let parsed = Options::parse(&matches);
        assert!(parsed.dag_only);
        let matches = cli.parse(["--path-cache-only"]).unwrap();
        assert!(std::panic::catch_unwind(|| Options::parse(&matches)).is_err());
    }

    #[test]
    fn arm_error_leaf_cache_preserves_type_and_excludes_normal_count() {
        arm_error_cache_roundtrip(true);
    }

    #[test]
    fn checked_arm_error_leaf_cache_publishes_and_loads_without_uncertified_flag() {
        arm_error_cache_roundtrip(false);
    }

    #[test]
    fn path_cache_save_validation_does_not_rebuild_all_events() {
        let source = include_str!("../../isla-lib/src/executor/path_cache/validate.rs");
        assert!(!source.contains("TraceReader"), "结构校验不能重建完整执行事件树");
        let source = include_str!("path_cache/publish.rs");
        assert!(!source.contains("TraceWriter"), "发布不能收集完整段 DTO");
        assert!(!source.contains("Vec<CachedPath"), "发布不能收集完整路径 DTO");
    }

    fn arm_error_cache_roundtrip(uncertified: bool) {
        use super::super::target::RV64;
        use isla_lib::{
            executor::samples::{SamplePath, Terminal},
            ir::Val,
            smt::{self, checkpoint},
        };
        smt::configure_tastic(smt::Tactic::Qfaufbv);
        let shared = SharedState::<B64>::empty(Symtab::new());
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let path = SamplePath {
            terminal: Terminal::ExecutionError { message: "失败臂".into(), location: "fixture.sail:42".into() },
            pre: Default::default(),
            post: Default::default(),
            result: Val::Unit,
            memory: vec![],
            memory_guards: Default::default(),
        };
        let paths = vec![ResidentPath {
            signature: 42,
            checkpoint: checkpoint(&mut solver),
            path,
            records: Vec::new().into(),
            pure_definitions: vec![],
        }];
        let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(format!(
            "output/arm-error-cache-{}-{}",
            uncertified,
            std::process::id()
        ));
        assert!(!directory.exists());
        let options = Options {
            write: Some(directory.clone()),
            format: vec![Encoding::Json, Encoding::Bin],
            ..Default::default()
        };
        let summary = super::super::solve_summary::SolveSummary { uncertified, ..Default::default() }.json();
        save(
            &options,
            "generic",
            &paths,
            &[Facts { guard_unique: false, post_unique: false, simple_pre: false }.into()],
            &shared,
            &RV64::default(),
            &summary,
            &json!({"command":[],"inputs":{},"binary":{"path":"fixture","sha256":"fixture"}}),
            &mut Timing::default(),
            &Stages::new(None, Instant::now()),
        );
        let manifest: Value = serde_json::from_reader(File::open(directory.join("manifest.json")).unwrap()).unwrap();
        assert_eq!(manifest["normal_paths"], 0);
        assert_eq!(manifest["execution_error_paths"], 1);
        assert_eq!(manifest["certification"] == "uncertified", uncertified);
        let restored = load_for_judge::<B64>(
            &directory,
            Encoding::Bin,
            uncertified,
            &shared,
            "generic",
            &Stages::new(None, Instant::now()),
        );
        assert_eq!(restored.manifest.errors.uncertified, uncertified);
        assert_eq!(restored.manifest.execution_error_paths, 1);
        let json_paths: Envelope<dto::CachedPath<B64>> =
            serde_json::from_reader(File::open(directory.join("paths.json")).unwrap()).unwrap();
        let bin_paths: Envelope<dto::CachedPath<B64>> =
            bincode::deserialize_from(File::open(directory.join("paths.bin")).unwrap()).unwrap();
        assert_eq!(json_paths.entries, bin_paths.entries);
        assert!(matches!(json_paths.entries[0].path.terminal, Terminal::ExecutionError { .. }));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn sail_exception_terminal_dual_encoding_and_old_schema_rejection() {
        use super::super::target::RV64;
        use isla_lib::{
            executor::samples::SamplePath,
            smt::{self, checkpoint},
        };
        smt::configure_tastic(smt::Tactic::Qfaufbv);
        let shared = SharedState::<B64>::empty(Symtab::new());
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let raw = json!({"pre":{},"post":{},"result":{"String":"reserved"},
            "memory":[],"memory_guards":[],
            "terminal":{"SailException":{"throw_location":"fixture.sail:42"}}});
        let dto: dto::PathData<B64> = serde_json::from_value(raw).unwrap();
        let path: SamplePath<B64> = dto.into();
        assert_eq!(
            serde_json::to_value(dto::PathData::from(path.clone())).unwrap()["terminal"],
            json!({"SailException":{"throw_location":"fixture.sail:42"}}),
            "异常终态字段不得丢失"
        );
        let paths = vec![ResidentPath {
            signature: 42,
            checkpoint: checkpoint(&mut solver),
            path,
            records: Vec::new().into(),
            pure_definitions: vec![],
        }];
        let directory =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(format!("output/exception-cache-{}", std::process::id()));
        assert!(!directory.exists());
        let options = Options {
            write: Some(directory.clone()),
            format: vec![Encoding::Json, Encoding::Bin],
            ..Default::default()
        };
        let mut summary = super::super::solve_summary::SolveSummary::default().json();
        summary["model-exception-paths"] = json!(1);
        save(
            &options,
            "generic",
            &paths,
            &[Facts { guard_unique: false, post_unique: false, simple_pre: false }.into()],
            &shared,
            &RV64::default(),
            &summary,
            &json!({"command":[],"inputs":{},"binary":{"path":"fixture","sha256":"fixture"}}),
            &mut Timing::default(),
            &Stages::new(None, Instant::now()),
        );
        for encoding in [Encoding::Json, Encoding::Bin] {
            let loaded =
                load::<B64>(&directory, encoding, true, &shared, "generic", &Stages::new(None, Instant::now()));
            assert_eq!(loaded.manifest.schema_version, CACHE_SCHEMA_VERSION);
            assert_eq!(loaded.manifest.normal_paths, 0);
            assert_eq!(loaded.manifest.model_exception_paths, 1);
            let restored = &loaded.paths[0].path;
            assert_eq!(
                serde_json::to_value(dto::PathData::from(restored.clone())).unwrap()["terminal"],
                json!({"SailException":{"throw_location":"fixture.sail:42"}})
            );
            assert_eq!(solver.check_sat(isla_lib::source_loc::SourceLoc::unknown()), smt::SmtResult::Sat);
            let sample = restored.materialize(&mut smt::Model::new(&solver), &shared, "fork", 42, None).unwrap();
            assert_eq!(restored.check(&mut solver, &shared, &sample).unwrap(), Some(true));
            let mut wrong = serde_json::to_value(&sample).unwrap();
            wrong["terminal"] = json!("Normal");
            let wrong = serde_json::from_value(wrong).unwrap();
            assert_eq!(restored.check(&mut solver, &shared, &wrong).unwrap(), Some(false), "异常不能认证成正常终态");
            let judged = restored.judge(&mut solver, &shared, &sample, &[], 42, |_, _| Ok(())).unwrap().unwrap();
            assert_eq!(
                serde_json::to_value(judged.sample).unwrap()["terminal"],
                json!({"SailException":{"throw_location":"fixture.sail:42"}})
            );
        }
        let candidate_dir = directory.with_extension("uncertified");
        let candidate_options = Options { write: Some(candidate_dir.clone()), ..options.clone() };
        let mut candidate_summary = summary.clone();
        candidate_summary["uncertified"] = json!(true);
        candidate_summary["status"] = json!("partial");
        save(
            &candidate_options,
            "generic",
            &paths,
            &[Facts { guard_unique: false, post_unique: false, simple_pre: false }.into()],
            &shared,
            &RV64::default(),
            &candidate_summary,
            &json!({"command":[],"inputs":{},"binary":{"path":"fixture","sha256":"fixture"}}),
            &mut Timing::default(),
            &Stages::new(None, Instant::now()),
        );
        let candidate: Value =
            serde_json::from_reader(File::open(candidate_dir.join("manifest.json")).unwrap()).unwrap();
        assert_eq!(candidate["certification"], "uncertified");
        assert_eq!(candidate["completeness"], "partial");
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| load::<B64>(
                &candidate_dir,
                Encoding::Bin,
                false,
                &shared,
                "generic",
                &Stages::new(None, Instant::now())
            )))
            .is_err(),
            "未认证缓存不能直接送入样例认证"
        );
        fs::remove_dir_all(candidate_dir).unwrap();
        let mut manifest: Value =
            serde_json::from_reader(File::open(directory.join("manifest.json")).unwrap()).unwrap();
        for version in [1, 2, 3] {
            manifest["schema_version"] = json!(version);
            fs::write(directory.join("manifest.json"), serde_json::to_vec(&manifest).unwrap()).unwrap();
            assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| load::<B64>(
                &directory,
                Encoding::Bin,
                false,
                &shared,
                "generic",
                &Stages::new(None, Instant::now())
            )))
            .is_err());
        }
        let mut writer = TraceWriter::default();
        writer.capture(&paths[0].checkpoint);
        let legacy_segments =
            Envelope { batch_id: manifest["batch_id"].as_str().unwrap().into(), entries: writer.segments };
        serde_json::to_writer(File::create(directory.join("segments.json")).unwrap(), &legacy_segments).unwrap();
        bincode::serialize_into(File::create(directory.join("segments.bin")).unwrap(), &legacy_segments).unwrap();
        for version in [4, 5] {
            manifest["schema_version"] = json!(version);
            fs::write(directory.join("manifest.json"), serde_json::to_vec(&manifest).unwrap()).unwrap();
            let legacy =
                load::<B64>(&directory, Encoding::Bin, true, &shared, "generic", &Stages::new(None, Instant::now()));
            assert_eq!(legacy.manifest.schema_version, version);
        }
        manifest["schema_version"] = json!(3);
        fs::write(directory.join("manifest.json"), serde_json::to_vec(&manifest).unwrap()).unwrap();
        // 旧 JSON 的窄编号可直接读入；旧二进制的字段宽度不兼容。
        let loaded =
            load::<B64>(&directory, Encoding::Json, false, &shared, "generic", &Stages::new(None, Instant::now()));
        assert_eq!(loaded.manifest.schema_version, 3);
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn old_cache_filters_exception_values_and_keeps_facts_aligned() {
        use super::super::{solve_summary::SolveSummary, target::RV64};
        use isla_lib::{
            executor::samples::{SamplePath, Terminal},
            ir::Val,
            smt::checkpoint,
        };
        let mut symtab = Symtab::new();
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let internal = symtab.intern("zError_internal_error");
        let other = symtab.intern("zError_not_implemented");
        let shared = SharedState::<B64>::empty(symtab);
        let context = Context::new(Config::new());
        let mut solver = Solver::new(&context);
        let paths: Vec<_> = (0..4)
            .map(|index| ResidentPath {
                signature: index,
                checkpoint: checkpoint(&mut solver),
                path: SamplePath {
                    terminal: if index == 0 {
                        Terminal::Normal
                    } else {
                        Terminal::SailException { throw_location: "throw.sail:1".into() }
                    },
                    pre: Default::default(),
                    post: Default::default(),
                    memory: vec![],
                    memory_guards: Default::default(),
                    result: Val::Ctor(
                        if index == 3 { other } else { internal },
                        Box::new(Val::String("site.sail:42: message".into())),
                    ),
                },
                records: Vec::new().into(),
                pure_definitions: vec![],
            })
            .collect();
        let root =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(format!("output/filter-old-cache-{}", std::process::id()));
        let directory = root.join("old");
        let facts: Vec<Facts> = (0..4)
            .map(|index| Facts { guard_unique: index == 0, post_unique: index == 3, simple_pre: false })
            .collect();
        let stages = Stages::new(None, Instant::now());
        let source = json!({"command":[],"inputs":{},"binary":{"path":"fixture","sha256":"fixture"}});
        save(
            &Options {
                write: Some(directory.clone()),
                format: vec![Encoding::Json, Encoding::Bin],
                ..Default::default()
            },
            "generic",
            &paths,
            &facts.iter().cloned().map(Into::into).collect::<Vec<FastFacts>>(),
            &shared,
            &RV64::default(),
            &SolveSummary { model_exception_paths: 3, ..Default::default() }.json(),
            &source,
            &mut Timing::default(),
            &stages,
        );
        // 旧 schema=3 元数据没有过滤字段；路径格式和来源记录完全不改。
        let mut manifest: Value =
            serde_json::from_reader(File::open(directory.join("manifest.json")).unwrap()).unwrap();
        manifest["errors"].as_object_mut().unwrap().remove("filtered-model-exception-paths");
        manifest["errors"].as_object_mut().unwrap().remove("filtered-model-exception-sites");
        fs::write(directory.join("manifest.json"), serde_json::to_vec(&manifest).unwrap()).unwrap();
        for encoding in [Encoding::Json, Encoding::Bin] {
            let mut loaded = load::<B64>(&directory, encoding, true, &shared, "generic", &stages);
            let summary = loaded.filter_model_exceptions(&[], &shared);
            assert_eq!(summary.model_exception_paths, 3);
            assert_eq!(summary.filtered_model_exception_paths, 0);
            assert_eq!(loaded.paths.len(), 4);
            assert_eq!(loaded.facts, facts);
            let mut loaded = load::<B64>(&directory, encoding, true, &shared, "generic", &stages);
            let summary = loaded.filter_model_exceptions(&["Error_internal_error".into()], &shared);
            assert_eq!(summary.model_exception_paths, 1);
            assert_eq!(summary.filtered_model_exception_paths, 2);
            assert_eq!(summary.filtered_model_exception_sites.values().copied().collect::<Vec<_>>(), vec![2]);
            assert!(summary.filtered_model_exception_sites.keys().next().unwrap().contains("site.sail:42: message"));
            assert_eq!(loaded.path_signatures, vec![0, 3]);
            assert_eq!(loaded.paths.iter().map(|path| path.signature).collect::<Vec<_>>(), vec![0, 3]);
            assert_eq!(loaded.facts, vec![facts[0].clone(), facts[3].clone()]);
            assert_eq!(loaded.manifest.path_signatures, vec![0, 1, 2, 3], "保留原始缓存来源记录");
            let new_directory = root.join(format!("filtered-{encoding:?}"));
            save(
                &Options {
                    write: Some(new_directory.clone()),
                    format: vec![Encoding::Json, Encoding::Bin],
                    ..Default::default()
                },
                "generic",
                &loaded.paths,
                &loaded.facts.iter().cloned().map(Into::into).collect::<Vec<FastFacts>>(),
                &shared,
                &RV64::default(),
                &summary.json(),
                &source,
                &mut Timing::default(),
                &stages,
            );
            let mut roundtrip = load::<B64>(&new_directory, encoding, true, &shared, "generic", &stages);
            let restored = roundtrip.filter_model_exceptions(&["Error_internal_error".into()], &shared);
            assert_eq!(restored.json(), summary.json(), "重新读取不重复累计已过滤路径");
        }
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn 双编码_完整快照_target_与文件损坏检查() {
        use super::super::target::RV64;
        use isla_lib::{
            bitvector::BV,
            executor::samples::SamplePath,
            ir::Val,
            smt::{self, checkpoint, smtlib::Ty},
            source_loc::SourceLoc,
        };
        smt::configure_tastic(smt::Tactic::Qfaufbv);
        let shared = SharedState::<B64>::empty(Symtab::new());
        let mut target = RV64::default();
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let symbol = solver.declare_const(Ty::BitVec(8), SourceLoc::unknown());
        target.pre_state_mut().insert(Name::from_u32(0), Val::Symbolic(symbol));
        target.platform = super::super::target::riscv::RiscvPlatformConfig::from_merged_toml(
            &"[[pma_regions]]\nname='generic'\nbase=0\nsize='symbolic'\nattr='ram'".parse().unwrap(),
        )
        .unwrap();
        target.model_bindings.push(("pma_regions.generic.size".into(), symbol));
        solver.add_event(smt::Event::Fork(
            u64::from(u32::MAX) + 1,
            symbol,
            0,
            isla_lib::source_loc::SourceLoc::unknown(),
        ));
        let paths = vec![ResidentPath {
            pure_definitions: vec![],
            signature: 42,
            checkpoint: checkpoint(&mut solver),
            path: SamplePath {
                terminal: Default::default(),
                pre: std::collections::BTreeMap::from([("value".into(), Val::Symbolic(symbol))]),
                post: Default::default(),
                result: Val::Bits(B64::new(7, 8)),
                memory: vec![],
                memory_guards: Default::default(),
            },
            records: Vec::new().into(),
        }];
        let facts = vec![Facts { guard_unique: true, post_unique: false, simple_pre: true }.into()];
        let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(format!(
            "output/path-cache/unit-{}-{}",
            std::process::id(),
            SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()
        ));
        let options = Options {
            write: Some(directory.clone()),
            format: vec![Encoding::Json, Encoding::Bin],
            ..Default::default()
        };
        save(
            &options,
            "generic",
            &paths,
            &facts,
            &shared,
            &target,
            &super::super::solve_summary::SolveSummary::default().json(),
            &json!({"command":[],"inputs":{},"binary":{"path":"synthetic","sha256":"synthetic"}}),
            &mut Timing::default(),
            &Stages::new(None, Instant::now()),
        );
        let json =
            load::<B64>(&directory, Encoding::Json, true, &shared, "generic", &Stages::new(None, Instant::now()));
        let bin = load::<B64>(&directory, Encoding::Bin, true, &shared, "generic", &Stages::new(None, Instant::now()));
        let encoded_manifest = bincode::serialize(&json.manifest).unwrap();
        assert_eq!(json.manifest, bincode::deserialize(&encoded_manifest).unwrap());
        let mut a = TraceWriter::default();
        let mut b = TraceWriter::default();
        assert_eq!(a.capture(&json.paths[0].checkpoint), b.capture(&bin.paths[0].checkpoint));
        assert_eq!(a.segments, b.segments);
        assert_eq!(json.facts, bin.facts);
        let mut restored = RV64::default();
        restored.platform = target.platform.clone();
        assert_eq!(json.manifest.pma_sizes, vec![("generic".to_string(), symbol.as_u32())]);
        restore_target(&json.manifest, &mut restored);
        assert_eq!(target.pre_state().get(&Name::from_u32(0)), restored.pre_state().get(&Name::from_u32(0)));
        assert_eq!(target.model_bindings(), restored.model_bindings());
        let reject = || {
            assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| load::<B64>(
                &directory,
                Encoding::Json,
                false,
                &shared,
                "generic",
                &Stages::new(None, Instant::now()),
            )))
            .is_err())
        };
        let manifest = fs::read(directory.join("manifest.json")).unwrap();
        let mut changed: Value = serde_json::from_slice(&manifest).unwrap();
        changed["schema_version"] = json!(1);
        fs::write(directory.join("manifest.json"), serde_json::to_vec(&changed).unwrap()).unwrap();
        reject();
        changed["schema_version"] = json!(CACHE_SCHEMA_VERSION);
        changed["paths"][0]["entries"] = json!(2);
        fs::write(directory.join("manifest.json"), serde_json::to_vec(&changed).unwrap()).unwrap();
        reject();
        fs::write(directory.join("manifest.json"), &manifest).unwrap();
        let data = fs::read(directory.join("paths.json")).unwrap();
        let mut changed: Value = serde_json::from_slice(&data).unwrap();
        changed["batch_id"] = json!("mixed");
        fs::write(directory.join("paths.json"), serde_json::to_vec(&changed).unwrap()).unwrap();
        reject();
        fs::write(directory.join("paths.json"), &data).unwrap();
        fs::remove_file(directory.join("segments.bin")).unwrap();
        reject();
        fs::remove_dir_all(directory).unwrap();
    }
}

use super::{resident::ResidentPath, target::Target};
use isla_lib::{
    bitvector::BV,
    executor::{
        path_cache::{
            self as dto, CachedPath, Facts, LinkedSegment, NameEnvironment, PathValidator, Segment, TracePlan,
            TraceReader,
        },
        samples::fast::FastFacts,
    },
    ir::{Name, SharedState},
    smt::{Config, Context, Solver, Sym},
};
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use serde_json::{json, Value};
use std::{
    fs::{self, File},
    io::Write,
    path::{Path, PathBuf},
    time::Instant,
};

/// 每个完成阶段立即追加一行，不依赖 campaign 的最终收尾。
pub struct Stages {
    started: Instant,
    path: Option<PathBuf>,
}
impl Stages {
    pub fn new(output: Option<&Path>, started: Instant) -> Self {
        let path = output.map(|output| {
            fs::create_dir_all(output).expect("创建阶段日志目录失败");
            output.join("path-cache-stages.jsonl")
        });
        Self { started, path }
    }
    pub fn record(&self, stage: &str, seconds: f64, details: Value) {
        let mut row = json!({"stage":stage,"seconds":seconds,"since_start":self.started.elapsed().as_secs_f64()});
        for (key, value) in details.as_object().expect("阶段详情必须是对象") {
            assert!(row.get(key).is_none(), "阶段详情覆盖固定字段：{key}");
            row.as_object_mut().unwrap().insert(key.clone(), value.clone());
        }
        let text = serde_json::to_string(&row).expect("阶段日志编码失败");
        if let Some(path) = &self.path {
            let mut file = fs::OpenOptions::new().create(true).append(true).open(path).expect("打开阶段日志失败");
            writeln!(file, "{text}").expect("追加阶段日志失败");
            file.sync_data().expect("同步阶段日志失败");
        }
        eprintln!("[PATH_CACHE_STAGE] {text}");
    }
}

// schema 7 以段号引用共享前缀。schema 3–6 保存展开后的事件。
const CACHE_SCHEMA_VERSION: u32 = 7;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Encoding {
    Json,
    Bin,
}
#[derive(Clone, Debug, Default)]
pub struct Options {
    pub read: Option<PathBuf>,
    pub write: Option<PathBuf>,
    pub format: Vec<Encoding>,
    pub encoding: Option<Encoding>,
    pub crosscheck: bool,
    pub export_dag: bool,
    pub recompute_facts: bool,
    /// 只保存完整符号路径；类枚举与可选快档证明留待读回后执行。
    pub dag_only: bool,
}
impl Options {
    pub fn enabled(&self) -> bool {
        self.read.is_some() || self.write.is_some()
    }
    pub fn add_cli(opts: &mut getopts::Options) {
        opts.optopt("", "path-cache-write", "探索完成后写出缓存（必须是新目录）", "<dir>");
        opts.optflag("", "path-cache-only", "仅写符号路径，跳过类枚举和具体样例生成");
        opts.optopt("", "path-cache-read", "读回缓存并跳过探索", "<dir>");
        opts.optopt("", "path-cache-format", "写出格式 json、bin、both，默认 both", "<format>");
        opts.optopt("", "path-cache-encoding", "读入格式 json、bin，默认 json", "<encoding>");
        opts.optflag("", "path-cache-crosscheck", "同时解码 JSON 和 bin，逐字段核对");
        opts.optflag("", "path-cache-export-dag", "读缓存后重新导出 DAG");
        opts.optflag("", "path-cache-recompute-facts", "读缓存后重新分析并核对静态事实");
    }
    pub fn parse(matches: &getopts::Matches) -> Self {
        let read = matches.opt_str("path-cache-read").map(PathBuf::from);
        let write = matches.opt_str("path-cache-write").map(PathBuf::from);
        assert!(!(read.is_some() && write.is_some()), "缓存读写不能同时指定");
        let format = match matches.opt_str("path-cache-format").as_deref().unwrap_or("both") {
            "json" => vec![Encoding::Json],
            "bin" => vec![Encoding::Bin],
            "both" => vec![Encoding::Json, Encoding::Bin],
            value => panic!("缓存写出格式无效：{value}"),
        };
        let encoding = match matches.opt_str("path-cache-encoding").as_deref().unwrap_or("json") {
            "json" => Encoding::Json,
            "bin" => Encoding::Bin,
            value => panic!("缓存读取格式无效：{value}"),
        };
        for name in
            ["path-cache-encoding", "path-cache-crosscheck", "path-cache-export-dag", "path-cache-recompute-facts"]
        {
            assert!(!matches.opt_present(name) || read.is_some(), "--{name} 需要 --path-cache-read");
        }
        assert!(
            !matches.opt_present("path-cache-format") || write.is_some(),
            "--path-cache-format 需要 --path-cache-write"
        );
        assert!(
            !matches.opt_present("path-cache-only") || write.is_some(),
            "--path-cache-only 需要 --path-cache-write"
        );
        Self {
            dag_only: matches.opt_present("path-cache-only"),
            read,
            write,
            format,
            encoding: Some(encoding),
            crosscheck: matches.opt_present("path-cache-crosscheck"),
            export_dag: matches.opt_present("path-cache-export-dag"),
            recompute_facts: matches.opt_present("path-cache-recompute-facts"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct DataFile {
    pub file: String,
    pub encoding: Encoding,
    pub entries: u64,
    pub batch_id: String,
}
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
struct Envelope<T> {
    batch_id: String,
    entries: Vec<T>,
}
// manifest 虽然只发布 JSON，也使用完整静态类型，避免引入 deserialize_any。
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct SourceFile {
    pub path: PathBuf,
    pub sha256: String,
}
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct SourceRecord {
    pub command: Vec<String>,
    pub inputs: std::collections::BTreeMap<String, SourceFile>,
    pub binary: SourceFile,
}
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub struct ExplorationSummary {
    #[serde(default)]
    pub uncertified: bool,
    pub sampled_paths: u64,
    pub errors: u64,
    #[serde(default)]
    pub failure_reasons: std::collections::BTreeMap<isla_lib::executor::SpeculativeRejectReason, u64>,
    pub execution_timeouts: u64,
    pub smt_timeouts: u64,
    pub unfinished_paths: u64,
    pub model_exception_paths: u64,
    #[serde(default)]
    pub filtered_model_exception_paths: u64,
    #[serde(default)]
    pub filtered_model_exception_sites: std::collections::BTreeMap<String, u64>,
    pub assertion_filtered_paths: u64,
    pub omitted_cases: u64,
    pub model_query_timeouts: u64,
    pub encoding_filtered_paths: u64,
    pub pending_batches: u64,
    pub status: String,
    pub model_coverage: String,
}
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Manifest<B> {
    pub schema_version: u32,
    pub bit_width: u32,
    pub batch_id: String,
    pub source: SourceRecord,
    pub current_ir_review: String,
    pub completeness: String,
    pub errors: ExplorationSummary,
    pub clause: String,
    pub segments: Vec<DataFile>,
    pub paths: Vec<DataFile>,
    pub path_signatures: Vec<u64>,
    pub normal_paths: u64,
    pub model_exception_paths: u64,
    #[serde(default)]
    pub execution_error_paths: u64,
    pub pre_state: Vec<(Name, dto::value::Val<B>)>,
    pub pma_sizes: Vec<(String, u32)>,
    pub names: NameEnvironment,
}

#[derive(Default, Serialize)]
pub struct Timing {
    pub manifest_seconds: f64,
    pub parse_seconds: f64,
    pub crosscheck_seconds: f64,
    pub rebuild_seconds: f64,
    pub validate_seconds: f64,
    pub capture_seconds: f64,
    pub write_seconds: f64,
    pub json_write_seconds: f64,
    pub bin_write_seconds: f64,
    pub json_bytes: u64,
    pub bin_bytes: u64,
    pub dag_seconds: f64,
    pub dag_replay_seconds: f64,
    pub facts_seconds: f64,
    pub facts_replay_seconds: f64,
    pub replay_seconds: f64,
    pub to_campaign_seconds: f64,
    pub paths: usize,
    pub segments: usize,
    pub unshared_segments: u64,
}
pub struct Loaded<B: BV> {
    /// 当前策略下保留的路径清单；manifest 继续保留缓存原始来源记录。
    pub path_signatures: Vec<u64>,
    pub paths: Vec<ResidentPath<B>>,
    pub facts: Vec<Facts>,
    pub manifest: Manifest<B>,
    pub timing: Timing,
}
impl<B: BV> Loaded<B> {
    pub(super) fn filter_model_exceptions(
        &mut self,
        names: &[String],
        shared: &SharedState<B>,
    ) -> super::solve_summary::SolveSummary {
        let mut summary = restored_summary(&self.manifest.errors);
        assert_eq!(self.paths.len(), self.facts.len(), "缓存路径与分析结果数量不同");
        let mut facts = std::mem::take(&mut self.facts).into_iter();
        self.paths.retain(|path| {
            let fact = facts.next().expect("缓存路径缺少分析结果");
            if matches!(path.path.terminal, isla_lib::executor::samples::Terminal::SailException { .. }) {
                if let Some(site) = isla_lib::executor::model_exception::filtered_site(names, &path.path.result, shared)
                {
                    summary.model_exception_paths =
                        summary.model_exception_paths.checked_sub(1).expect("缓存异常终态计数不足");
                    summary.record_filtered_model_exception(site);
                    return false;
                }
            }
            self.facts.push(fact);
            true
        });
        self.path_signatures = self.paths.iter().map(|path| path.signature).collect();
        summary
    }
}

fn check_envelope<T>(envelope: &Envelope<T>, file: &DataFile, batch: &str) {
    assert_eq!(file.batch_id, batch, "缓存 manifest 混用批次");
    assert_eq!(envelope.batch_id, batch, "缓存数据混用批次");
    assert_eq!(envelope.entries.len() as u64, file.entries, "缓存数据条目数不一致");
}
fn read_data<T: DeserializeOwned>(dir: &Path, files: &[DataFile], encoding: Encoding, batch: &str) -> Vec<T> {
    let candidates = files.iter().filter(|f| f.encoding == encoding).collect::<Vec<_>>();
    assert_eq!(candidates.len(), 1, "缓存必须有且仅有一个指定编码的数据文件");
    let entry = candidates[0];
    assert!(
        entry.file == format!("segments.{}", extension(encoding))
            || entry.file == format!("paths.{}", extension(encoding)),
        "缓存文件名无效"
    );
    let bytes = fs::read(dir.join(&entry.file)).expect("缓存数据文件缺失或不可读取");
    let envelope: Envelope<T> = match encoding {
        Encoding::Json => serde_json::from_slice(&bytes).expect("缓存 JSON 损坏"),
        Encoding::Bin => {
            use bincode::Options;
            bincode::DefaultOptions::new()
                .with_fixint_encoding()
                .reject_trailing_bytes()
                .deserialize(&bytes)
                .expect("缓存 bincode 损坏")
        }
    };
    check_envelope(&envelope, entry, batch);
    envelope.entries
}
fn read_segments<B: BV>(dir: &Path, manifest: &Manifest<B>, encoding: Encoding) -> Vec<LinkedSegment<B>> {
    if manifest.schema_version < CACHE_SCHEMA_VERSION {
        let segments: Vec<Segment<B>> = read_data(dir, &manifest.segments, encoding, &manifest.batch_id);
        segments.into_iter().map(Into::into).collect()
    } else {
        read_data(dir, &manifest.segments, encoding, &manifest.batch_id)
    }
}

fn extension(encoding: Encoding) -> &'static str {
    match encoding {
        Encoding::Json => "json",
        Encoding::Bin => "bin",
    }
}
pub fn current_source() -> Value {
    use sha2::{Digest, Sha256};
    let mut source = super::solve_summary::input_manifest();
    let executable = std::env::current_exe().expect("读取可执行文件路径失败");
    let bytes = fs::read(&executable).expect("读取可执行文件失败");
    let mut digest = Sha256::new();
    digest.input(bytes);
    source["binary"] = json!({"path":executable,"sha256":format!("{:x}",digest.result())});
    source
}

pub fn load<B: BV>(
    dir: &Path,
    encoding: Encoding,
    crosscheck: bool,
    shared: &SharedState<B>,
    clause: &str,
    stages: &Stages,
) -> Loaded<B> {
    load_inner(dir, encoding, crosscheck, shared, clause, stages, false)
}

/// 候选缓存只能送入真正重新求解的 judge；导样本和 fuzz 继续使用 load。
pub fn load_for_judge<B: BV>(
    dir: &Path,
    encoding: Encoding,
    crosscheck: bool,
    shared: &SharedState<B>,
    clause: &str,
    stages: &Stages,
) -> Loaded<B> {
    load_inner(dir, encoding, crosscheck, shared, clause, stages, true)
}

fn load_inner<B: BV>(
    dir: &Path,
    encoding: Encoding,
    crosscheck: bool,
    shared: &SharedState<B>,
    clause: &str,
    stages: &Stages,
    allow_uncertified: bool,
) -> Loaded<B> {
    let started = Instant::now();
    let raw: Value =
        serde_json::from_reader(File::open(dir.join("manifest.json")).expect("缓存 manifest 缺失，目录尚未发布"))
            .expect("缓存 manifest 损坏");
    assert!(
        raw["schema_version"] == json!(CACHE_SCHEMA_VERSION)
            || raw["schema_version"] == json!(6)
            || raw["schema_version"] == json!(5)
            || raw["schema_version"] == json!(4)
            || (raw["schema_version"] == json!(3) && encoding == Encoding::Json && !crosscheck),
        "缓存 schema 不兼容。schema 3 请显式读取 JSON 且关闭双格式核对，或重新生成缓存"
    );
    assert!(
        raw["valid"] != json!(false) && raw["errors"]["valid"] != json!(false),
        "路径缓存结果作废，拒绝用于 judge、--check-samples 或 fuzz：{}",
        raw["invalid_reasons"]
    );
    if !allow_uncertified {
        assert_ne!(raw["certification"], json!("uncertified"), "未认证候选缓存必须先离线检查，不能直接用于样例或fuzz");
    }
    let manifest: Manifest<B> = serde_json::from_value(raw).expect("缓存 manifest 字段损坏");
    if !allow_uncertified {
        assert!(!manifest.errors.uncertified, "未认证候选摘要不能作为已检查缓存读入");
    }
    assert_eq!(manifest.bit_width, B::MAX_WIDTH, "缓存位宽不兼容");
    assert_eq!(manifest.current_ir_review, "未做当前 IR 复核", "缓存 IR 复核标注无效");
    assert!(matches!(manifest.completeness.as_str(), "complete" | "partial"), "缓存完整性标注无效");
    assert_eq!(manifest.clause, clause, "缓存 clause 不一致");
    let summary = restored_summary(&manifest.errors);
    assert_eq!(manifest.errors.status, summary.status(), "缓存摘要状态不一致");
    assert_eq!(
        manifest.completeness,
        if summary.status() == "finished" { "complete" } else { "partial" },
        "缓存完整性与摘要不一致"
    );
    manifest.names.validate(&shared.symtab, &shared.type_info);
    for entry in manifest.segments.iter().chain(&manifest.paths) {
        assert_eq!(entry.batch_id, manifest.batch_id, "缓存 manifest 混用批次");
        assert!(dir.join(&entry.file).is_file(), "缓存 manifest 声明的数据文件缺失");
    }
    let manifest_seconds = started.elapsed().as_secs_f64();
    stages.record("cache_manifest", manifest_seconds, json!({}));
    let parsing = Instant::now();
    let segments = read_segments(dir, &manifest, encoding);
    let paths: Vec<CachedPath<B>> = read_data(dir, &manifest.paths, encoding, &manifest.batch_id);
    let exception_count = paths
        .iter()
        .filter(|path| matches!(path.path.terminal, isla_lib::executor::samples::Terminal::SailException { .. }))
        .count() as u64;
    assert_eq!(manifest.model_exception_paths, exception_count, "缓存异常终态计数不一致");
    let error_count = paths
        .iter()
        .filter(|path| matches!(path.path.terminal, isla_lib::executor::samples::Terminal::ExecutionError { .. }))
        .count() as u64;
    assert_eq!(manifest.execution_error_paths, error_count, "缓存执行错误叶子计数不一致");
    assert_eq!(manifest.normal_paths, paths.len() as u64 - exception_count - error_count, "缓存正常终态计数不一致");
    assert_eq!(manifest.errors.model_exception_paths, exception_count, "缓存摘要异常终态计数不一致");
    let parse_seconds = parsing.elapsed().as_secs_f64();
    stages.record(
        &format!("cache_read_{}", extension(encoding)),
        parse_seconds,
        json!({"primary":true,"paths":paths.len(),"segments":segments.len()}),
    );
    let checking = Instant::now();
    if crosscheck {
        let other = match encoding {
            Encoding::Json => Encoding::Bin,
            Encoding::Bin => Encoding::Json,
        };
        let other_segments = read_segments(dir, &manifest, other);
        let other_paths = read_data(dir, &manifest.paths, other, &manifest.batch_id);
        stages.record(
            &format!("cache_read_{}", extension(other)),
            checking.elapsed().as_secs_f64(),
            json!({"primary":false,"paths":paths.len(),"segments":segments.len()}),
        );
        assert_eq!(segments, other_segments, "缓存两种编码的分段不同");
        assert_eq!(paths, other_paths, "缓存两种编码的路径不同");
        stages.record("cache_crosscheck", checking.elapsed().as_secs_f64(), json!({"equal":true}));
    }
    for entry in &manifest.segments {
        assert_eq!(entry.entries, segments.len() as u64, "缓存分段条目数不一致");
        assert_eq!(entry.file, format!("segments.{}", extension(entry.encoding)), "缓存分段文件名无效");
    }
    for entry in &manifest.paths {
        assert_eq!(entry.entries, paths.len() as u64, "缓存路径条目数不一致");
        assert_eq!(entry.file, format!("paths.{}", extension(entry.encoding)), "缓存路径文件名无效");
    }
    let mut timing = Timing {
        manifest_seconds,
        parse_seconds,
        crosscheck_seconds: if crosscheck { checking.elapsed().as_secs_f64() } else { 0.0 },
        paths: paths.len(),
        segments: segments.len(),
        unshared_segments: paths.iter().map(|p| p.checkpoint.num).sum(),
        ..Default::default()
    };
    assert_eq!(
        manifest.path_signatures,
        paths.iter().map(|p| p.signature).collect::<Vec<_>>(),
        "缓存 manifest 路径清单不同"
    );
    let started = Instant::now();
    {
        let mut validator = PathValidator::new(&manifest.names, &manifest.pre_state, &manifest.pma_sizes);
        for segment in &segments {
            validator.segment(segment);
        }
        for path in &paths {
            validator.path(path);
        }
    }
    timing.validate_seconds = started.elapsed().as_secs_f64();
    stages.record("cache_validate", timing.validate_seconds, json!({"paths":paths.len(),"segments":segments.len()}));
    let started = Instant::now();
    let reader = TraceReader::from_linked(&segments);
    let mut facts = Vec::new();
    let restored_paths: Vec<ResidentPath<B>> = paths
        .iter()
        .map(|p| {
            facts.push(p.facts.clone());
            ResidentPath {
                signature: p.signature,
                pure_definitions: p.pure_definitions.clone(),
                checkpoint: reader.restore(&p.checkpoint),
                path: p.path.clone().into(),
                records: p.records.iter().cloned().map(Into::into).collect::<Vec<_>>().into(),
            }
        })
        .collect();
    let mut roundtrip = TracePlan::default();
    for ((expected, restored), fact) in paths.iter().zip(&restored_paths).zip(&facts) {
        let actual = capture_path(restored, roundtrip.capture(&restored.checkpoint), fact.clone());
        assert_eq!(*expected, actual, "缓存重建后的路径 DTO 不同");
    }
    let rebuilt = roundtrip.segments();
    assert_eq!(segments.len(), rebuilt.len(), "缓存重建后的段数不同");
    for (expected, actual) in segments.iter().zip(rebuilt) {
        assert_eq!(*expected, actual, "缓存重建后的分段 DTO 不同");
    }
    timing.rebuild_seconds = started.elapsed().as_secs_f64();
    stages.record(
        "dto_rebuild",
        timing.rebuild_seconds,
        json!({"dto_equal":true,"paths":paths.len(),"segments":segments.len()}),
    );
    Loaded { path_signatures: manifest.path_signatures.clone(), paths: restored_paths, facts, manifest, timing }
}

pub fn restore_target<B: BV>(manifest: &Manifest<B>, target: &mut dyn Target<B>) {
    assert_eq!(target.pre_state().len(), 0, "缓存读入前 Target 前态必须为空");
    assert!(target.model_bindings().is_empty(), "缓存读入前 PMA 绑定必须为空");
    for (name, value) in &manifest.pre_state {
        assert!(target.pre_state_mut().insert(*name, value.clone().into()).is_none(), "缓存前态重复");
    }
    // 兼容旧 schema：pma_sizes 保存 region 名，Target 使用完整输出键。
    let bindings = manifest
        .pma_sizes
        .iter()
        .map(|(name, sym)| (format!("pma_regions.{name}.size"), Sym::from_u32(*sym)))
        .collect::<Vec<_>>();
    target.restore_model_bindings(&bindings).expect("缓存模型绑定与当前 target 配置不匹配");
}

mod publish;
pub use publish::save;

fn capture_path<B: BV>(path: &ResidentPath<B>, checkpoint: dto::CheckpointData, facts: Facts) -> CachedPath<B> {
    CachedPath {
        signature: path.signature,
        pure_definitions: path.pure_definitions.clone(),
        checkpoint,
        path: path.path.clone().into(),
        records: path.records.iter().cloned().map(Into::into).collect(),
        facts,
    }
}

pub fn analyze<B: BV>(paths: &[ResidentPath<B>], timing: &mut Timing) -> Vec<FastFacts> {
    let mut config = Config::new();
    config.set_param_value("model", "true");
    let context = Context::new(config);
    paths
        .iter()
        .map(|path| {
            let started = Instant::now();
            let mut solver = Solver::from_checkpoint(&context, path.checkpoint.clone());
            timing.facts_replay_seconds += started.elapsed().as_secs_f64();
            let started = Instant::now();
            let facts = FastFacts::analyze(&path.path, &mut solver, &path.records).expect("路径静态事实分析失败");
            timing.facts_seconds += started.elapsed().as_secs_f64();
            facts
        })
        .collect()
}

pub fn write_provenance<B>(output: &Path, manifest: Option<&Manifest<B>>, source: &Value, options: &Options) {
    let path = output.join("provenance.json");
    let mut provenance: Value = serde_json::from_reader(File::open(&path).unwrap()).expect("provenance 损坏");
    provenance["validity"] = json!("缓存内部认证；未做当前 IR 复核");
    provenance["current_ir_review"] = json!("未做当前 IR 复核");
    provenance["path_cache"] =
        json!({"read":options.read,"write":options.write,"source":manifest.map(|m|&m.source),"current_source":source});
    if let Some(manifest) = manifest {
        let current: SourceRecord = serde_json::from_value(source.clone()).expect("当前来源记录字段无效");
        if manifest.source.inputs != current.inputs || manifest.source.binary.sha256 != current.binary.sha256 {
            eprintln!("warning: 缓存来源记录与当前 IR、配置或二进制不同；未做当前 IR 复核");
        }
    }
    fs::write(path, serde_json::to_vec_pretty(&provenance).unwrap()).unwrap();
}

/// 一次 clause 的缓存上下文；入口计时延续到 campaign 开始。
pub struct Run<B: BV> {
    pub options: Options,
    pub clause: String,
    pub summary: Value,
    pub loaded: Option<Loaded<B>>,
    pub started: Instant,
    pub stages: Stages,
}
impl<B: BV> Run<B> {
    pub fn new(options: &Options, clause: &str, output: &Path) -> Self {
        let started = Instant::now();
        Self {
            options: options.clone(),
            clause: clause.into(),
            summary: Value::Null,
            loaded: None,
            started,
            stages: Stages::new(Some(output), started),
        }
    }
}
pub(super) fn restored_summary(summary: &ExplorationSummary) -> super::solve_summary::SolveSummary {
    let field = |value: u64| value.try_into().expect("缓存执行摘要越界");
    super::solve_summary::SolveSummary {
        solver_path_drops: Default::default(),
        applicable_batches: 1,
        inapplicable_batches: 0,
        uncertified: summary.uncertified,
        sampled_paths: field(summary.sampled_paths),
        errors: field(summary.errors),
        failure_reasons: summary.failure_reasons.iter().map(|(reason, count)| (*reason, field(*count))).collect(),
        execution_timeouts: field(summary.execution_timeouts),
        smt_timeouts: field(summary.smt_timeouts),
        unfinished_paths: field(summary.unfinished_paths),
        model_exception_paths: field(summary.model_exception_paths),
        filtered_model_exception_paths: field(summary.filtered_model_exception_paths),
        filtered_model_exception_sites: summary
            .filtered_model_exception_sites
            .iter()
            .map(|(site, count)| (site.clone(), field(*count)))
            .collect(),
        assertion_filtered_paths: field(summary.assertion_filtered_paths),
        omitted_cases: field(summary.omitted_cases),
        model_query_timeouts: field(summary.model_query_timeouts),
        encoding_filtered_paths: field(summary.encoding_filtered_paths),
        pending_batches: field(summary.pending_batches),
    }
}
