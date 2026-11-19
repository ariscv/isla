//! 稳定序列化；对外样本与判定保持 v1，不泄漏进程内守卫编号。
use serde::Serialize;
use serde_json::{json, Value};
use std::io::{BufWriter, Write};
use std::path::Path;

pub fn write_json(path: &Path, value: &impl Serialize) {
    let mut file = BufWriter::new(std::fs::File::create(path).expect("创建 JSON 失败"));
    serde_json::to_writer_pretty(&mut file, value).expect("序列化 JSON 失败");
    writeln!(file).unwrap();
    file.flush().unwrap();
}
/// 调用方持有目录写锁，同一文件每次由一个 worker 提交。
pub fn write_json_atomic(path: &Path, value: &impl Serialize) {
    let temporary = path.with_extension("json.tmp");
    let mut file = BufWriter::new(std::fs::File::create(&temporary).expect("创建临时 JSON 失败"));
    serde_json::to_writer(&mut file, value).expect("序列化 JSON 失败");
    writeln!(file).unwrap();
    file.flush().unwrap();
    file.get_ref().sync_all().unwrap();
    std::fs::rename(temporary, path).expect("提交 JSON 失败");
    std::fs::File::open(path.parent().unwrap()).unwrap().sync_all().unwrap();
}

pub fn write_lines<T: Serialize>(path: &Path, rows: &[T]) {
    let mut file = BufWriter::new(std::fs::File::create(path).expect("创建 JSONL 失败"));
    for row in rows {
        serde_json::to_writer(&mut file, row).expect("序列化 JSONL 失败");
        writeln!(file).unwrap();
    }
    file.flush().unwrap();
}
pub fn canonical_coordinates(row: &mut Value) {
    let vector = row["guard_vector"].as_str().unwrap().to_owned();
    row["guard_order"] = json!((0..vector.len()).collect::<Vec<_>>());
    row["guard_assignment"] = Value::Object(
        vector
            .bytes()
            .enumerate()
            .map(|(i, bit)| {
                assert!(bit == b'0' || bit == b'1');
                (i.to_string(), json!(bit == b'1'))
            })
            .collect(),
    );
}

/// 沿用T3对差异签名的规范序列化；不引入输入哈希有效性锁。
pub fn canonical_json(value: &serde_json::Value) -> String {
    let mut value = value.clone();
    value.sort_all_objects();
    serde_json::to_string(&value).expect("规范JSON序列化失败")
}
