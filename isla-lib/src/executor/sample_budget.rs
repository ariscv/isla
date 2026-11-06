//! 有预算的二进制流式写出；预算耗尽是正常停止。
use super::*;

pub(super) struct BudgetWriter {
    file: File,
    limit: u64,
    written: u64,
    buffered: u64,
    pending: BTreeMap<(u64, Option<usize>), Chunk>,
    paths: BTreeMap<u64, (u64, u64, bool)>,
    seen_paths: BTreeMap<u64, u64>,
    classes: BTreeMap<(u64, Option<usize>), (u64, bool)>,
    total: u64,
    reason: u64,
    finished: bool,
}

struct Chunk {
    header: Value,
    rows: Vec<u8>,
    count: u64,
}

impl BudgetWriter {
    pub(super) fn open(path: &Path, limit: u64) -> Self {
        let mut file = OpenOptions::new().write(true).create_new(true).open(path).unwrap();
        binary::header_version(&mut file, 2);
        let written = file.stream_position().unwrap();
        assert!(limit >= written + 112, "预算必须容纳文件头、空汇总和正常结束标记");
        Self {
            file,
            limit,
            written,
            buffered: 0,
            pending: BTreeMap::new(),
            paths: BTreeMap::new(),
            seen_paths: BTreeMap::new(),
            classes: BTreeMap::new(),
            total: 0,
            reason: 0,
            finished: false,
        }
    }

    fn reserved(&self) -> u64 {
        // 汇总索引40 + 四个计数32 + 每路径/类32 + EOF40。
        112 + 32 * (self.paths.len() + self.classes.len()) as u64
    }

    pub(super) fn start_path(&mut self, path: u64, signature: u64) {
        assert!(self.seen_paths.insert(path, signature).is_none());
    }

    pub(super) fn buffered_bytes(&self) -> u64 {
        self.buffered
    }

    pub(super) fn stop_reason(&self) -> Option<&'static str> {
        match self.reason {
            0 => None,
            1 => Some("output_budget"),
            2 => Some("no_progress"),
            _ => unreachable!(),
        }
    }

    pub(super) fn stopped(&self) -> bool {
        self.reason != 0
    }

    pub(super) fn stop_stalled(&mut self) {
        if self.reason == 0 {
            self.reason = 2;
        }
    }

    pub(super) fn append(&mut self, path: u64, solution: usize, slices: &[String], sample: Value) -> bool {
        assert!(!self.finished);
        if self.stopped() {
            return false;
        }
        let class = sample["class_id"].as_u64().map(|value| usize::try_from(value).unwrap());
        let key = (path, class);
        assert_eq!(
            solution as u64,
            self.classes.get(&key).map_or(0, |entry| entry.0),
            "完整流式输出的类内解必须连续且唯一"
        );
        self.seen_paths.entry(path).or_insert(sample["path_signature"].as_u64().unwrap());
        let fresh_path = !self.paths.contains_key(&path);
        let fresh_class = !self.classes.contains_key(&key);
        let mut new_chunk = None;
        let skeleton = if let Some(chunk) = self.pending.get(&key) {
            &chunk.header["skeleton"]
        } else {
            new_chunk = Some(Chunk {
                header: json!({"compact_schema_version":1,
                "path_nonce":path,"path_signature":sample["path_signature"],"class_id":class,
                "solution_count":0,"skeleton":sample}),
                rows: Vec::new(),
                count: 0,
            });
            &new_chunk.as_ref().unwrap().header["skeleton"]
        };
        let mut delta = json!({"set":{},"remove":[]});
        difference(skeleton, &sample, "", &mut delta);
        let mut row = Vec::new();
        binary::encode(&mut row, &json!({"solution_index":solution,"slice_values":slices,"delta":delta}));
        let mut extra = row.len() as u64 + 32 * (u64::from(fresh_path) + u64::from(fresh_class));
        if let Some(chunk) = &new_chunk {
            let mut header = Vec::new();
            binary::encode(&mut header, &chunk.header);
            extra += 40 + header.len() as u64;
        }
        if self
            .written
            .checked_add(self.buffered_bytes())
            .unwrap()
            .checked_add(self.reserved())
            .unwrap()
            .checked_add(extra)
            .unwrap()
            > self.limit
        {
            self.reason = 1;
            return false;
        }
        self.buffered += extra - 32 * (u64::from(fresh_path) + u64::from(fresh_class));
        if let Some(chunk) = new_chunk {
            self.pending.insert(key, chunk);
        }
        let chunk = self.pending.get_mut(&key).unwrap();
        chunk.rows.extend_from_slice(&row);
        chunk.count += 1;
        chunk.header["solution_count"] = json!(chunk.count);
        let full = chunk.count >= 256 || chunk.rows.len() >= 256 * 1024;
        let path_stats = self.paths.entry(path).or_insert((sample["path_signature"].as_u64().unwrap(), 0, true));
        path_stats.1 += 1;
        self.classes.entry(key).or_insert((0, true)).0 += 1;
        self.total += 1;
        if full {
            self.flush_chunk(key);
        }
        true
    }

    fn flush_chunk(&mut self, key: (u64, Option<usize>)) {
        if let Some(chunk) = self.pending.remove(&key) {
            let mut header = Vec::new();
            binary::encode(&mut header, &chunk.header);
            for value in [
                chunk.header["path_signature"].as_u64().unwrap(),
                key.1.map_or(u64::MAX, |value| value as u64),
                chunk.count,
                (header.len() + chunk.rows.len()) as u64,
                u64::from(chunk.header["skeleton"]["truncated"].as_bool().unwrap()),
            ] {
                self.file.write_all(&value.to_le_bytes()).unwrap();
            }
            self.buffered -= 40 + (header.len() + chunk.rows.len()) as u64;
            self.file.write_all(&header).unwrap();
            self.file.write_all(&chunk.rows).unwrap();
            self.written = self.file.stream_position().unwrap();
        }
    }

    pub(super) fn finish_class(&mut self, path: u64, class: Option<usize>, truncated: bool) {
        if let Some(stats) = self.classes.get_mut(&(path, class)) {
            stats.1 = truncated;
        }
        self.flush_chunk((path, class));
    }

    pub(super) fn finish_path(&mut self, path: u64, truncated: bool) {
        if let Some(stats) = self.paths.get_mut(&path) {
            stats.2 = truncated;
        }
    }

    pub(super) fn progress(&self) -> Value {
        json!({"combinations":self.total,"bytes":self.written + self.buffered_bytes(),
            "lower_bound":self.total + u64::from(self.stopped()), "max_output_bytes":self.limit})
    }

    pub(super) fn flush_pending(&mut self) {
        for key in self.pending.keys().copied().collect::<Vec<_>>() {
            self.flush_chunk(key);
        }
        self.file.flush().unwrap();
    }

    pub(super) fn finish(&mut self) -> Value {
        assert!(!self.finished);
        for key in self.pending.keys().copied().collect::<Vec<_>>() {
            self.flush_chunk(key);
        }
        let summary_offset = self.written;
        let size = 32 + 32 * (self.paths.len() + self.classes.len()) as u64;
        for value in [0u64, 0, 0, size, 2, self.reason, self.total, self.paths.len() as u64, self.classes.len() as u64]
        {
            self.file.write_all(&value.to_le_bytes()).unwrap();
        }
        for (path, (signature, count, truncated)) in &self.paths {
            for value in [*path, *signature, *count, u64::from(*truncated)] {
                self.file.write_all(&value.to_le_bytes()).unwrap();
            }
        }
        for ((path, class), (count, truncated)) in &self.classes {
            for value in [*path, class.map_or(u64::MAX, |value| value as u64), *count, u64::from(*truncated)] {
                self.file.write_all(&value.to_le_bytes()).unwrap();
            }
        }
        for value in [0u64, 0, 0, summary_offset, u64::MAX] {
            self.file.write_all(&value.to_le_bytes()).unwrap();
        }
        self.file.flush().unwrap();
        self.written = self.file.stream_position().unwrap();
        assert!(self.written <= self.limit);
        self.finished = true;
        let paths: Vec<_> = self
            .seen_paths
            .iter()
            .map(|(path, signature)| {
                let (count, truncated) = match self.paths.get(path) {
                    Some((_, count, truncated)) => (*count, *truncated),
                    None => (0, true),
                };
                json!({"path_nonce":path,"path_signature":signature,"combinations":count,"truncated":truncated})
            })
            .collect();
        let reason = match self.reason {
            0 => None,
            1 => Some("output_budget"),
            2 => Some("no_progress"),
            _ => unreachable!(),
        };
        json!({"combinations":self.total,"bytes":self.written,"max_output_bytes":self.limit,
            "truncated":self.reason != 0 || self.paths.values().any(|stats| stats.2) || self.classes.values().any(|stats| stats.1),"reason":reason,"paths":paths})
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample(index: usize) -> Value {
        json!({"schema_version":1,"sample_id":index,"path_signature":7,"class_id":0,
            "truncated":false,"pre_registers":{"x":{"bits":format!("{index:064b}")}}})
    }

    #[test]
    fn budget_精确边界及胖类拒绝后仍有正常文件尾() {
        let root = std::env::temp_dir().join(format!("f11-budget-{}", std::process::id()));
        std::fs::create_dir_all(&root).unwrap();
        let baseline = root.join("baseline.bin");
        let mut writer = BudgetWriter::open(&baseline, 1_000_000);
        assert!(writer.append(0, 0, &[], sample(0)));
        writer.finish_path(0, false);
        writer.finish();
        let exact = std::fs::metadata(&baseline).unwrap().len();
        for (name, cap, expected) in [("exact", exact, 1), ("short", exact - 1, 0)] {
            let path = root.join(name);
            let mut writer = BudgetWriter::open(&path, cap);
            assert_eq!(writer.append(0, 0, &[], sample(0)), expected == 1);
            if expected == 1 {
                assert!(!writer.append(0, 1, &[], sample(1)));
            }
            writer.finish_path(0, true);
            let summary = writer.finish();
            assert_eq!(summary["combinations"], expected);
            assert_eq!(summary["reason"], "output_budget");
            let bytes = std::fs::read(path).unwrap();
            assert!(bytes.len() as u64 <= cap);
            assert_eq!(&bytes[bytes.len() - 8..], &u64::MAX.to_le_bytes());
        }
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn budget_单个大类连续写入有界缓冲且并发共享预算() {
        let root = std::env::temp_dir().join(format!("f11-concurrent-{}", std::process::id()));
        std::fs::create_dir_all(&root).unwrap();
        let writer = Mutex::new(BudgetWriter::open(&root.join("samples.bin"), 200_000));
        std::thread::scope(|scope| {
            for path in 0..4 {
                let writer = &writer;
                scope.spawn(move || {
                    for index in 0..10_000 {
                        if !writer.lock().unwrap().append(path, index, &[], sample(index)) {
                            break;
                        }
                    }
                    writer.lock().unwrap().finish_path(path, true);
                });
            }
        });
        let mut writer = writer.into_inner().unwrap();
        assert!(writer.buffered_bytes() < 4 * 1024 * 1024);
        let report = writer.finish();
        assert!(report["combinations"].as_u64().unwrap() > 256);
        assert_eq!(report["truncated"], true);
        assert!(std::fs::metadata(root.join("samples.bin")).unwrap().len() <= 200_000);
        std::fs::remove_dir_all(root).unwrap();
    }
}

#[cfg(test)]
mod stop_tests {
    use super::*;
    #[test]
    fn budget_无进展停止保存已接受的组合() {
        let root = std::env::temp_dir().join(format!("f11-stall-{}", std::process::id()));
        std::fs::create_dir_all(&root).unwrap();
        let mut writer = BudgetWriter::open(&root.join("samples.bin"), 10000);
        assert!(writer.append(
            0,
            0,
            &[],
            json!({"schema_version":1,"sample_id":0,"path_signature":7,"class_id":0,"truncated":false})
        ));
        writer.stop_stalled();
        assert!(!writer.append(0, 1, &[], json!(null)));
        let report = writer.finish();
        assert_eq!(report["combinations"], 1);
        assert_eq!(report["reason"], "no_progress");
        std::fs::remove_dir_all(root).unwrap();
    }
}
