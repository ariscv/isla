//! 缓存发布按顺序转换、校验和写出每个条目。
use super::*;
use isla_lib::executor::samples::Terminal;
use std::{
    io::BufWriter,
    time::{SystemTime, UNIX_EPOCH},
};

struct Phase<'a> {
    stages: &'a Stages,
    name: &'static str,
    first: Option<Value>,
    last: Option<Value>,
    seconds: f64,
}

impl<'a> Phase<'a> {
    fn new(stages: &'a Stages, name: &'static str) -> Self {
        Self { stages, name, first: None, last: None, seconds: 0.0 }
    }

    fn point(&self) -> Value {
        let rss_bytes = fs::read_to_string("/proc/self/status").ok().and_then(|status| {
            let kb = status
                .lines()
                .find_map(|line| line.strip_prefix("VmRSS:"))?
                .split_whitespace()
                .next()?
                .parse::<u64>()
                .ok()?;
            Some(kb * 1024)
        });
        json!({"at_seconds": self.stages.started.elapsed().as_secs_f64(), "rss_bytes": rss_bytes})
    }

    fn measure<T>(&mut self, operation: impl FnOnce() -> T) -> T {
        if self.first.is_none() {
            let first = self.point();
            self.stages.record(&format!("cache_capture_{}_begin", self.name), 0.0, first.clone());
            self.first = Some(first);
        }
        let started = Instant::now();
        let value = operation();
        self.seconds += started.elapsed().as_secs_f64();
        value
    }

    fn finish(&mut self) {
        let last = self.point();
        self.stages.record(&format!("cache_capture_{}_end", self.name), self.seconds, last.clone());
        self.last = Some(last);
    }

    fn details(&self) -> Value {
        json!({"start": self.first, "end": self.last, "seconds": self.seconds})
    }
}

struct DataWriter<'a, 'b> {
    dir: &'a Path,
    formats: &'a [Encoding],
    batch: &'a str,
    timing: &'a mut Timing,
    stages: &'a Stages,
    writing: &'a mut Phase<'b>,
}

struct DataOutput {
    encoding: Encoding,
    file: String,
    output: BufWriter<File>,
    seconds: f64,
}

impl DataWriter<'_, '_> {
    fn write<T: Serialize>(&mut self, name: &str, entries: impl ExactSizeIterator<Item = T>) -> Vec<DataFile> {
        let count = entries.len() as u64;
        let mut outputs = self.writing.measure(|| {
            self.formats
                .iter()
                .map(|&encoding| {
                    let started = Instant::now();
                    let file = format!("{name}.{}", extension(encoding));
                    let mut output = BufWriter::new(File::create(self.dir.join(&file)).expect("创建缓存数据失败"));
                    match encoding {
                        Encoding::Json => {
                            write!(output, "{{\n  \"batch_id\": ").expect("写入缓存 JSON 头失败");
                            serde_json::to_writer(&mut output, self.batch).expect("写入缓存批次失败");
                            write!(output, ",\n  \"entries\": [").expect("写入缓存 JSON 序列头失败");
                        }
                        Encoding::Bin => {
                            // bincode 序列布局为批次字符串、固定宽度长度、随后逐条编码。
                            bincode::serialize_into(&mut output, &(self.batch, count))
                                .expect("写入缓存 bincode 头失败");
                        }
                    }
                    DataOutput { encoding, file, output, seconds: started.elapsed().as_secs_f64() }
                })
                .collect::<Vec<_>>()
        });
        for (index, entry) in entries.enumerate() {
            self.writing.measure(|| {
                for output in &mut outputs {
                    let started = Instant::now();
                    match output.encoding {
                        Encoding::Json => {
                            if index != 0 {
                                write!(output.output, ",").expect("写入缓存 JSON 分隔符失败");
                            }
                            write!(output.output, "\n    ").expect("写入缓存 JSON 换行失败");
                            serde_json::to_writer_pretty(&mut output.output, &entry).expect("写入缓存 JSON 条目失败");
                        }
                        Encoding::Bin => {
                            bincode::serialize_into(&mut output.output, &entry).expect("写入缓存 bincode 条目失败");
                        }
                    }
                    output.seconds += started.elapsed().as_secs_f64();
                }
            });
        }
        outputs
            .into_iter()
            .map(|mut output| {
                let bytes = self.writing.measure(|| {
                    let started = Instant::now();
                    if output.encoding == Encoding::Json {
                        let end = if count == 0 { "]\n}" } else { "\n  ]\n}" };
                        write!(output.output, "{end}").expect("写入缓存 JSON 尾失败");
                    }
                    output.output.flush().expect("刷新缓存数据失败");
                    output.output.get_ref().sync_all().expect("同步缓存数据失败");
                    let bytes = output.output.get_ref().metadata().expect("读取缓存文件大小失败").len();
                    output.seconds += started.elapsed().as_secs_f64();
                    bytes
                });
                match output.encoding {
                    Encoding::Json => {
                        self.timing.json_write_seconds += output.seconds;
                        self.timing.json_bytes += bytes;
                    }
                    Encoding::Bin => {
                        self.timing.bin_write_seconds += output.seconds;
                        self.timing.bin_bytes += bytes;
                    }
                }
                self.stages.record(
                    &format!("cache_write_{}", extension(output.encoding)),
                    output.seconds,
                    json!({"file":output.file,"bytes":bytes,"entries":count}),
                );
                DataFile { file: output.file, encoding: output.encoding, entries: count, batch_id: self.batch.into() }
            })
            .collect()
    }
}

pub fn save<B: BV>(
    options: &Options,
    clause: &str,
    paths: &[ResidentPath<B>],
    facts: &[FastFacts],
    shared: &SharedState<B>,
    target: &dyn Target<B>,
    summary: &Value,
    source: &Value,
    timing: &mut Timing,
    stages: &Stages,
) {
    let mut conversion = Phase::new(stages, "convert");
    let mut validation = Phase::new(stages, "validate");
    let mut writing = Phase::new(stages, "write");
    let (plan, checkpoints, names, pre_state, pma_sizes) = conversion.measure(|| {
        assert_eq!(paths.len(), facts.len(), "缓存事实与路径数不同");
        let mut plan = TracePlan::default();
        let checkpoints = paths.iter().map(|path| plan.capture(&path.checkpoint)).collect::<Vec<_>>();
        let names = NameEnvironment::capture(&shared.symtab, &shared.type_info);
        let mut pre_state = target.pre_state().iter().map(|(n, v)| (*n, v.clone().into())).collect::<Vec<_>>();
        pre_state.sort_by_key(|(n, _)| *n);
        let pma_sizes = target
            .model_bindings()
            .iter()
            .map(|(name, sym)| {
                let region = name
                    .strip_prefix("pma_regions.")
                    .and_then(|name| name.strip_suffix(".size"))
                    .expect("当前缓存格式只能保存 PMA size 模型绑定");
                (region.to_string(), sym.as_u32())
            })
            .collect::<Vec<_>>();
        (plan, checkpoints, names, pre_state, pma_sizes)
    });
    timing.paths = paths.len();
    timing.segments = plan.segments().len();
    timing.unshared_segments = checkpoints.iter().map(|point| point.num).sum();
    let deduplication_rate =
        (timing.unshared_segments != 0).then(|| 1.0 - timing.segments as f64 / timing.unshared_segments as f64);

    if paths.is_empty() {
        conversion.finish();
        validation.measure(|| ());
        validation.finish();
    }

    let dir = options.write.as_ref().unwrap();
    writing.measure(|| {
        fs::create_dir_all(dir.parent().unwrap()).expect("创建缓存父目录失败");
        fs::create_dir(dir).expect("缓存写出目录必须是新目录");
    });
    let batch_id =
        format!("{}-{}", std::process::id(), SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos());

    let mut validator = PathValidator::new(&names, &pre_state, &pma_sizes);
    let entries = (0..timing.segments).map(|id| {
        let segment = conversion.measure(|| plan.segment(id));
        validation.measure(|| validator.segment(&segment));
        segment
    });
    let mut writer =
        DataWriter { dir, formats: &options.format, batch: &batch_id, timing, stages, writing: &mut writing };
    let segments = writer.write("segments", entries);

    let mut path_signatures = Vec::with_capacity(paths.len());
    let mut model_exception_paths = 0;
    let mut execution_error_paths = 0;
    let entries = paths.iter().zip(checkpoints).zip(facts).enumerate().map(|(index, ((path, checkpoint), facts))| {
        let last = index + 1 == paths.len();
        let cached = conversion.measure(|| {
            path_signatures.push(path.signature);
            match path.path.terminal {
                Terminal::SailException { .. } => model_exception_paths += 1,
                Terminal::ExecutionError { .. } => execution_error_paths += 1,
                Terminal::Normal => {}
            }
            capture_path(path, checkpoint, facts.clone().into())
        });
        if last {
            conversion.finish();
        }
        validation.measure(|| validator.path(&cached));
        if last {
            validation.finish();
        }
        cached
    });
    let paths_files = writer.write("paths", entries);
    drop(validator);
    drop(plan);
    let normal_paths = paths.len() as u64 - model_exception_paths - execution_error_paths;
    assert_eq!(summary["model-exception-paths"].as_u64(), Some(model_exception_paths), "缓存摘要异常终态计数不一致");
    let complete = summary["status"] == "finished"
        && summary["errors"].as_u64() == Some(0)
        && summary["unfinished-paths"].as_u64() == Some(0);
    let manifest = Manifest {
        schema_version: CACHE_SCHEMA_VERSION,
        bit_width: B::MAX_WIDTH,
        batch_id,
        source: serde_json::from_value(source.clone()).expect("缓存来源记录字段无效"),
        current_ir_review: "未做当前 IR 复核".into(),
        completeness: if complete { "complete" } else { "partial" }.into(),
        errors: serde_json::from_value(summary.clone()).expect("缓存执行摘要字段无效"),
        clause: clause.into(),
        segments,
        paths: paths_files,
        path_signatures,
        normal_paths,
        model_exception_paths,
        execution_error_paths,
        pre_state,
        pma_sizes,
        names,
    };
    writing.measure(|| {
        let mut output = BufWriter::new(File::create(dir.join("manifest.pending")).expect("创建 manifest 失败"));
        let mut manifest_value = serde_json::to_value(&manifest).unwrap();
        for key in [
            "valid",
            "invalid_reasons",
            "solver_timeout_dropped_paths",
            "solver_timeout_drop_locations",
            "invalid_message",
        ] {
            if let Some(value) = summary.get(key) {
                // 作废标记属于 JSON manifest，保持有类型的缓存摘要可按原布局二进制往返。
                manifest_value[key] = value.clone();
                manifest_value["errors"][key] = value.clone();
            }
        }
        manifest_value["certification"] = json!(if manifest.errors.uncertified { "uncertified" } else { "checked" });
        serde_json::to_writer_pretty(&mut output, &manifest_value).expect("写入 manifest 失败");
        output.flush().unwrap();
        output.get_ref().sync_all().unwrap();
        drop(output);
        let directory = File::open(dir).expect("打开缓存目录失败");
        directory.sync_all().expect("同步待发布缓存目录失败");
        fs::rename(dir.join("manifest.pending"), dir.join("manifest.json")).expect("发布 manifest 失败");
        directory.sync_all().expect("同步已发布缓存目录失败");
    });
    writing.finish();
    timing.capture_seconds = conversion.seconds + validation.seconds;
    timing.validate_seconds = validation.seconds;
    timing.write_seconds = writing.seconds;
    stages.record(
        "cache_capture",
        timing.capture_seconds,
        json!({
            "paths": timing.paths,
            "segments": timing.segments,
            "unshared_segments": timing.unshared_segments,
            "deduplication_rate": deduplication_rate,
            "conversion": conversion.details(),
            "validation": validation.details(),
            "write": writing.details(),
        }),
    );
    stages.record("cache_write", timing.write_seconds, json!({"json_seconds":timing.json_write_seconds,"bin_seconds":timing.bin_write_seconds,"json_bytes":timing.json_bytes,"bin_bytes":timing.bin_bytes,"paths":timing.paths,"segments":timing.segments,"unshared_segments":timing.unshared_segments,"deduplication_rate":deduplication_rate}));
    eprintln!("[PATH_CACHE_WRITE] {}", serde_json::to_string(timing).unwrap());
}
