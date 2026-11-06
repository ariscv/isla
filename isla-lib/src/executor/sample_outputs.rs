//! 共享完整样本的可组合输出后端；增量保存实际模型状态，不离线猜测未测试位。
use super::*;
use crate::config::{SampleOutputConfig, SampleOutputFormat};
use std::fs::{File, OpenOptions};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

#[path = "sample_binary.rs"]
mod binary;

#[path = "sample_budget.rs"]
mod budget;

/// 每条路径使用独立命名空间；相同路径签名可能在不同 clause 或批次中再次出现。
pub struct SampleOutputs {
    backends: Vec<SampleBackend>,
    budget: Option<std::sync::Arc<Mutex<budget::BudgetWriter>>>,
    monitor: Option<(std::sync::mpsc::Sender<()>, Mutex<Option<std::thread::JoinHandle<()>>>)>,
    summary_path: Option<PathBuf>,
    next_sample: AtomicU64,
    next_path: AtomicU64,
}

/// 所有后端接收同一份已物化完整样本；不会各自查询 Z3 或另选代表模型。
enum SampleBackend {
    V1(SampleWriter),
    Grouped(GroupedWriter),
}

struct GroupedWriter {
    format: SampleOutputFormat,
    file: Mutex<File>,
    directory: PathBuf,
    classes: Mutex<BTreeMap<(u64, Option<usize>), std::sync::Arc<Mutex<ClassSpool>>>>,
}

struct ClassSpool {
    skeleton: Value,
    rows: std::io::BufWriter<File>,
    path: PathBuf,
    count: u64,
    last_solution: Option<usize>,
}

impl Drop for ClassSpool {
    fn drop(&mut self) {
        std::fs::remove_file(&self.path).expect("删除本类临时增量文件失败");
    }
}

impl SampleOutputs {
    pub fn open(configs: &[SampleOutputConfig]) -> Self {
        assert!(!configs.is_empty(), "输出后端不得为空");
        let mut backends = Vec::new();
        let mut next = 0;
        for config in configs {
            if let Some(parent) = config.path.parent() {
                if !parent.as_os_str().is_empty() {
                    std::fs::create_dir_all(parent).expect("创建输出目录失败");
                }
            }
            if config.format == SampleOutputFormat::V1Jsonl {
                let writer = SampleWriter::open(&config.path);
                next = next.max(writer.next.load(Ordering::Relaxed));
                backends.push(SampleBackend::V1(writer));
            } else {
                let mut file = OpenOptions::new()
                    .write(true)
                    .create_new(true)
                    .open(&config.path)
                    .expect("紧凑输出必须使用新文件，禁止覆盖已有结果");
                if config.format == SampleOutputFormat::Binary {
                    binary::header(&mut file);
                }
                let mut name = config.path.as_os_str().to_os_string();
                name.push(format!(
                    ".spool-{}-{}",
                    std::process::id(),
                    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
                ));
                let directory = PathBuf::from(name);
                std::fs::create_dir(&directory).expect("创建类增量暂存目录失败");
                backends.push(SampleBackend::Grouped(GroupedWriter {
                    format: config.format,
                    file: Mutex::new(file),
                    directory,
                    classes: Mutex::new(BTreeMap::new()),
                }));
            }
        }
        Self {
            backends,
            budget: None,
            monitor: None,
            summary_path: None,
            next_sample: AtomicU64::new(next),
            next_path: AtomicU64::new(0),
        }
    }

    pub fn open_budget(configs: &[SampleOutputConfig], limit: u64) -> Self {
        assert_eq!(configs.len(), 1);
        assert_eq!(configs[0].format, SampleOutputFormat::Binary);
        let path = &configs[0].path;
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        let writer = std::sync::Arc::new(Mutex::new(budget::BudgetWriter::open(path, limit)));
        let progress = writer.clone();
        let stop_file = path.with_extension("stop");
        let (sender, receiver) = std::sync::mpsc::channel();
        let monitor = std::thread::spawn(move || {
            let mut previous = 0;
            let mut changed = std::time::Instant::now();
            loop {
                match receiver.recv_timeout(std::time::Duration::from_secs(60)) {
                    Ok(()) | Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => break,
                    Err(std::sync::mpsc::RecvTimeoutError::Timeout) => (),
                }
                let mut writer = progress.lock().unwrap();
                writer.flush_pending();
                let report = writer.progress();
                let total = report["combinations"].as_u64().unwrap();
                if total != previous {
                    previous = total;
                    changed = std::time::Instant::now();
                }
                if changed.elapsed().as_secs() >= 3600 || stop_file.exists() {
                    writer.stop_stalled();
                }
                eprintln!("[MERGE_ENUMERATION_PROGRESS] {}", report);
            }
        });
        Self {
            backends: Vec::new(),
            budget: Some(writer),
            monitor: Some((sender, Mutex::new(Some(monitor)))),
            summary_path: Some(path.with_extension("summary.json")),
            next_sample: AtomicU64::new(0),
            next_path: AtomicU64::new(0),
        }
    }

    pub fn stop_reason(&self) -> Option<&'static str> {
        self.budget.as_ref().and_then(|writer| writer.lock().unwrap().stop_reason())
    }

    pub fn finish_path(&self, path: u64, truncated: bool) {
        if let Some(writer) = &self.budget {
            writer.lock().unwrap().finish_path(path, truncated);
        }
    }

    pub fn start_path(&self, signature: u64) -> u64 {
        let path = self
            .next_path
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| next.checked_add(1))
            .expect("输出路径编号溢出");
        if let Some(writer) = &self.budget {
            writer.lock().unwrap().start_path(path, signature);
        }
        path
    }

    pub fn grouped(&self) -> bool {
        self.budget.is_some() || self.backends.iter().any(|backend| matches!(backend, SampleBackend::Grouped(_)))
    }

    pub fn append(&self, path: u64, solution: usize, slices: &[String], mut sample: Sample) -> bool {
        sample.sample_id = self
            .next_sample
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| next.checked_add(1))
            .expect("样本编号溢出");
        if let Some(writer) = &self.budget {
            return writer.lock().unwrap().append(path, solution, slices, serde_json::to_value(sample).unwrap());
        }
        let value = self.grouped().then(|| serde_json::to_value(&sample).expect("样本序列化失败"));
        for backend in &self.backends {
            match backend {
                SampleBackend::V1(writer) => {
                    writer.append_assigned(&sample);
                }
                SampleBackend::Grouped(writer) => {
                    let class = {
                        let mut classes = writer.classes.lock().unwrap();
                        classes
                            .entry((path, sample.class_id))
                            .or_insert_with(|| {
                                let file = writer.directory.join(format!("{path}-{:?}.jsonl", sample.class_id));
                                let rows = OpenOptions::new().write(true).create_new(true).open(&file).unwrap();
                                std::sync::Arc::new(Mutex::new(ClassSpool {
                                    skeleton: value.as_ref().unwrap().clone(),
                                    rows: std::io::BufWriter::new(rows),
                                    path: file,
                                    count: 0,
                                    last_solution: None,
                                }))
                            })
                            .clone()
                    };
                    let mut class = class.lock().unwrap();
                    if let Some(previous) = class.last_solution {
                        assert!(solution > previous, "同类解编号必须递增");
                    }
                    let mut delta = json!({"set":{},"remove":[]});
                    difference(&class.skeleton, value.as_ref().unwrap(), "", &mut delta);
                    let row = json!({"solution_index":solution,"slice_values":slices,"delta":delta});
                    serde_json::to_writer(&mut class.rows, &row).unwrap();
                    class.rows.write_all(b"\n").unwrap();
                    class.count = class.count.checked_add(1).unwrap();
                    class.last_solution = Some(solution);
                }
            }
        }
        true
    }

    pub fn finish_class(&self, path: u64, class_id: Option<usize>, metadata: &Value) {
        if let Some(writer) = &self.budget {
            writer.lock().unwrap().finish_class(
                path,
                class_id,
                metadata["truncated"].as_bool().expect("流式类结束必须携带最终截断标记"),
            );
            return;
        }
        for backend in &self.backends {
            if let SampleBackend::Grouped(writer) = backend {
                let class = writer.classes.lock().unwrap().remove(&(path, class_id)).expect("结束的类必须已经写出样本");
                let mut class =
                    std::sync::Arc::try_unwrap(class).ok().expect("类结束后不得仍有消费者引用").into_inner().unwrap();
                class.rows.flush().unwrap();
                assert_eq!(class.count, metadata["solution_count"].as_u64().unwrap(), "类的模型与枚举计数必须一致");
                let header = json!({"compact_schema_version":1,"path_signature":class.skeleton["path_signature"],
                    "class_id":class_id,"guard_assignment":metadata["guard_assignment"],
                    "tested_slices":metadata["tested_slices"],"solution_count":class.count,"skeleton":class.skeleton});
                let mut file = writer.file.lock().unwrap();
                if writer.format == SampleOutputFormat::CompactJsonl {
                    let mut prefix = serde_json::to_vec(&header).unwrap();
                    assert_eq!(prefix.pop(), Some(b'}'));
                    prefix.extend_from_slice(b",\"increments\":[");
                    file.write_all(&prefix).unwrap();
                    let rows = std::io::BufReader::new(File::open(&class.path).unwrap());
                    for (index, line) in rows.lines().enumerate() {
                        if index > 0 {
                            file.write_all(b",").unwrap();
                        }
                        file.write_all(line.unwrap().as_bytes()).unwrap();
                    }
                    file.write_all(b"]}\n").unwrap();
                } else {
                    binary::class(&mut file, &header, &class.path, class.count);
                }
            }
        }
    }

    pub fn finish(&self) {
        if let Some((sender, monitor)) = &self.monitor {
            sender.send(()).unwrap();
            monitor.lock().unwrap().take().unwrap().join().unwrap();
        }
        if let Some(writer) = &self.budget {
            let report = writer.lock().unwrap().finish();
            std::fs::write(self.summary_path.as_ref().unwrap(), serde_json::to_vec_pretty(&report).unwrap()).unwrap();
            eprintln!("[SAMPLE_OUTPUT_REPORT] {}", report);
        }
        for backend in &self.backends {
            if let SampleBackend::Grouped(writer) = backend {
                assert!(writer.classes.lock().unwrap().is_empty(), "所有输出类都必须正常收尾");
                let mut file = writer.file.lock().unwrap();
                if writer.format == SampleOutputFormat::Binary {
                    binary::finish(&mut file);
                }
                file.flush().unwrap();
                std::fs::remove_dir(&writer.directory).expect("删除空暂存目录失败");
            }
        }
    }
}

/// 对象递归差量、等长数组逐项差量；结构或长度改变时精确保存该子值。
fn difference(base: &Value, value: &Value, path: &str, delta: &mut Value) {
    if base == value {
        return;
    }
    match (base, value) {
        (Value::Object(left), Value::Object(right)) => {
            for key in left.keys().filter(|key| !right.contains_key(*key)) {
                let key = key.replace('~', "~0").replace('/', "~1");
                delta["remove"].as_array_mut().unwrap().push(json!(format!("{path}/{key}")));
            }
            for (key, right) in right {
                let pointer = format!("{path}/{}", key.replace('~', "~0").replace('/', "~1"));
                if let Some(left) = left.get(key) {
                    difference(left, right, &pointer, delta);
                } else {
                    delta["set"][pointer] = right.clone();
                }
            }
        }
        (Value::Array(left), Value::Array(right)) if left.len() == right.len() => {
            for (index, (left, right)) in left.iter().zip(right).enumerate() {
                difference(left, right, &format!("{path}/{index}"), delta);
            }
        }
        _ => {
            delta["set"][path] = value.clone();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn outputs_同一完整样本写三后端且类内增量不丢字段() {
        let root = std::env::var_os("ISLA_SAMPLE_OUTPUT_FIXTURE")
            .map(PathBuf::from)
            .unwrap_or_else(|| std::env::temp_dir().join(format!("f9-outputs-{}", std::process::id())));
        std::fs::create_dir_all(&root).unwrap();
        let configs = [
            (SampleOutputFormat::V1Jsonl, "v1.jsonl"),
            (SampleOutputFormat::CompactJsonl, "compact.jsonl"),
            (SampleOutputFormat::Binary, "samples.bin"),
        ]
        .map(|(format, path)| SampleOutputConfig { format, path: root.join(path) });
        let outputs = SampleOutputs::open(&configs);
        let budget = SampleOutputs::open_budget(
            &[SampleOutputConfig { format: SampleOutputFormat::Binary, path: root.join("budget.bin") }],
            1_000_000,
        );
        let path = outputs.start_path(7);
        for class in 0..2 {
            for solution in 0..3 {
                let sample = Sample {
                    schema_version: 1,
                    sample_id: 999,
                    mode: "merge".into(),
                    path_signature: 7,
                    class_id: Some(class),
                    truncated: class == 1,
                    pre_registers: BTreeMap::from([("a/b~c".into(), json!({"bits":"0".repeat(129)}))]),
                    post_registers: BTreeMap::from([(
                        "a/b~c".into(),
                        json!({"bits":format!("{}{}",solution%2,"0".repeat(128))}),
                    )]),
                    isa_state: BTreeMap::from([("display".into(), format!("解{solution}"))]),
                    pre_memory: vec![MemoryCell { address: 10, value: None, bytes: 1 }],
                    post_memory: (0..=solution)
                        .map(|offset| MemoryCell { address: 10 + offset, value: Some(offset as u8), bytes: 1 })
                        .collect(),
                    result: json!({"ctor":"完成","value":{"bool":solution%2==0}}),
                    ret_val: "保留原显示文本".into(),
                };
                assert!(budget.append(path, solution as usize, &[format!("#b{solution:02b}")], sample.clone()));
                outputs.append(path, solution as usize, &[format!("#b{solution:02b}")], sample);
            }
            budget.finish_class(path, Some(class), &json!({"truncated":class == 1}));
            outputs.finish_class(
                path,
                Some(class),
                &json!({"guard_assignment":{"1":class==1},"tested_slices":[],"solution_count":3}),
            );
        }
        budget.finish_path(path, false);
        budget.finish();
        outputs.finish();
        let rows = SampleChecker::load(&root.join("v1.jsonl"), None).unwrap().samples;
        assert_eq!(rows.len(), 6);
        assert_eq!(rows.iter().map(|row| row.sample_id).collect::<Vec<_>>(), (0..6).collect::<Vec<_>>());
        let classes: Vec<Value> = std::fs::read_to_string(root.join("compact.jsonl"))
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        assert_eq!(classes.len(), 2);
        assert!(classes.iter().all(|class| class["solution_count"] == 3));
        let binary = std::fs::read(root.join("samples.bin")).unwrap();
        assert_eq!(&binary[..8], b"ISLASB1\0");
        assert_eq!(u32::from_le_bytes(binary[16..20].try_into().unwrap()), 40);
        if std::env::var_os("ISLA_SAMPLE_OUTPUT_FIXTURE").is_none() {
            std::fs::remove_dir_all(root).unwrap();
        }
    }
}
