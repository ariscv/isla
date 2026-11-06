//! 带自描述文件头的 40 字节小端类索引；载荷为无损的有类型 JSON 树编码。
use super::*;

pub(super) fn header(file: &mut File) {
    let fields = json!({"schema_version":1,"sample_schema_version":1,"compact_schema_version":1,
        "endianness":"little","record_bytes":40,
        "fields":[["path_signature","u64",0],["class_id","u64",8],["solution_count","u64",16],
                  ["payload_bytes","u64",24],["flags","u64",32]],
        "null_class_id":u64::MAX,"end_flags":u64::MAX,"payload_codec":"typed-json-v1",
        "payload_layout":"class_header then solution_count increment values"});
    let metadata = serde_json::to_vec(&fields).unwrap();
    file.write_all(b"ISLASB1\0").unwrap();
    for value in [1u32, 24, 40, u32::try_from(metadata.len()).unwrap()] {
        file.write_all(&value.to_le_bytes()).unwrap();
    }
    file.write_all(&metadata).unwrap();
}

pub(super) fn class(file: &mut File, header: &Value, source: &Path, count: u64) {
    let path = source.with_extension("binary");
    let mut payload = OpenOptions::new().read(true).write(true).create_new(true).open(&path).unwrap();
    {
        let mut buffered = std::io::BufWriter::new(&mut payload);
        encode(&mut buffered, header);
        let lines = std::io::BufReader::new(File::open(source).unwrap());
        for line in lines.lines() {
            encode(&mut buffered, &serde_json::from_str::<Value>(&line.unwrap()).unwrap());
        }
        buffered.flush().unwrap();
    }
    let bytes = payload.metadata().unwrap().len();
    let class_id = match header["class_id"].as_u64() {
        Some(value) => {
            assert_ne!(value, u64::MAX, "保留的空类编号不能作为真实类编号");
            value
        }
        None => {
            assert!(header["class_id"].is_null());
            u64::MAX
        }
    };
    for value in [
        header["path_signature"].as_u64().unwrap(),
        class_id,
        count,
        bytes,
        u64::from(header["skeleton"]["truncated"].as_bool().unwrap()),
    ] {
        file.write_all(&value.to_le_bytes()).unwrap();
    }
    payload.seek(SeekFrom::Start(0)).unwrap();
    std::io::copy(&mut payload, file).unwrap();
    drop(payload);
    std::fs::remove_file(path).unwrap();
}

pub(super) fn finish(file: &mut File) {
    for value in [0u64, 0, 0, 0, u64::MAX] {
        file.write_all(&value.to_le_bytes()).unwrap();
    }
}

fn encode(writer: &mut impl Write, value: &Value) {
    match value {
        Value::Null => writer.write_all(&[0]).unwrap(),
        Value::Bool(false) => writer.write_all(&[1]).unwrap(),
        Value::Bool(true) => writer.write_all(&[2]).unwrap(),
        Value::Number(number) => {
            if let Some(value) = number.as_u64() {
                writer.write_all(&[3]).unwrap();
                writer.write_all(&value.to_le_bytes()).unwrap();
            } else if let Some(value) = number.as_i64() {
                writer.write_all(&[4]).unwrap();
                writer.write_all(&value.to_le_bytes()).unwrap();
            } else {
                writer.write_all(&[5]).unwrap();
                writer.write_all(&number.as_f64().unwrap().to_le_bytes()).unwrap();
            }
        }
        Value::String(text) => {
            let prefixed =
                text.starts_with("#b") && text.len() > 2 && text[2..].bytes().all(|byte| byte == b'0' || byte == b'1');
            let text = if prefixed { &text[2..] } else { text.as_str() };
            let bits = !text.is_empty() && text.bytes().all(|byte| byte == b'0' || byte == b'1');
            writer
                .write_all(&[if prefixed {
                    10
                } else if bits {
                    9
                } else {
                    6
                }])
                .unwrap();
            writer.write_all(&u32::try_from(text.len()).unwrap().to_le_bytes()).unwrap();
            if bits {
                for byte in 0..text.len().checked_add(7).unwrap() / 8 {
                    let mut value = 0;
                    for bit in 0..8 {
                        let position = byte * 8 + bit;
                        if position < text.len() {
                            value |= (text.as_bytes()[text.len() - 1 - position] - b'0') << bit;
                        }
                    }
                    writer.write_all(&[value]).unwrap();
                }
            } else {
                writer.write_all(text.as_bytes()).unwrap();
            }
        }
        Value::Array(values) => {
            writer.write_all(&[7]).unwrap();
            writer.write_all(&u32::try_from(values.len()).unwrap().to_le_bytes()).unwrap();
            for value in values {
                encode(writer, value);
            }
        }
        Value::Object(values) => {
            writer.write_all(&[8]).unwrap();
            writer.write_all(&u32::try_from(values.len()).unwrap().to_le_bytes()).unwrap();
            for (key, value) in values {
                encode(writer, &Value::String(key.clone()));
                encode(writer, value);
            }
        }
    }
}
