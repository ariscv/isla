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
