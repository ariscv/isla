//! 历史记录只描述显式改动；读取范围取自原批次输入，并逐字节验证。
use super::{random_stream, Mode, Mutator, Options};
use isla_lib::executor::samples::{MemoryCell, Sample, SampleChecker};
use rand_chacha::ChaCha8Rng;
use serde_json::{json, Value};
use std::collections::BTreeMap;

pub struct ReplayMutator {
    pub witnesses: BTreeMap<u64, Sample>,
}
impl Mutator for ReplayMutator {
    fn mutate(&self, parent: &Sample, record: &Value, rng: &mut ChaCha8Rng) -> Sample {
        // 精确回放不消费随机数；未来算子仍使用同一编号独立随机流。
        let _ = rng;
        let id = record["sample_id"].as_u64().unwrap();
        let witness = &self.witnesses[&id];
        let post: BTreeMap<_, _> = parent
            .post_memory
            .iter()
            .map(|cell| {
                assert_eq!(cell.bytes, 1);
                (cell.address, cell.value.unwrap())
            })
            .collect();
        let mut memory = BTreeMap::new();
        for cell in &parent.pre_memory {
            assert_eq!(cell.bytes, 1);
            let value = match cell.value {
                Some(value) => value,
                None => post[&cell.address] ^ 255,
            };
            assert!(memory.insert(cell.address, value).is_none(), "corpus entry 内存地址重复");
        }
        let address = record["address"].as_u64().unwrap();
        assert_eq!(address % 8, 0);
        let old = (0..8).fold(0u64, |word, i| word | ((memory[&(address + i)] as u64) << (8 * i)));
        assert_eq!(old, record["old_value"].as_u64().unwrap(), "变异记录旧值不匹配");
        match record["operator"].as_str().unwrap() {
            "M1" => {
                let mut value = old;
                for bit in record["bits"].as_array().unwrap() {
                    value ^= 1u64 << bit.as_u64().unwrap();
                }
                assert_eq!(value, record["new_value"].as_u64().unwrap());
            }
            "M5" => {
                let mask = record["free_mask"].as_u64().unwrap();
                assert!((1..=7).contains(&mask));
                let value = old ^ ((mask & 1) << 5) ^ ((mask & 2) << 7) ^ ((mask & 4) << 7);
                assert_eq!(value, record["new_value"].as_u64().unwrap());
            }
            "M2" => {
                let ppn = record["ppn"].as_u64().unwrap();
                assert_eq!((old & !(((1u64 << 44) - 1) << 10)) | (ppn << 10), record["new_value"].as_u64().unwrap());
                match record["m2_mode"].as_str().unwrap() {
                    "move" => {
                        let source = record["old_page"].as_u64().unwrap();
                        let target = record["new_page"].as_u64().unwrap();
                        assert_eq!(source, ((old >> 10) & ((1u64 << 44) - 1)) << 12);
                        assert_eq!(target, ppn << 12);
                        assert!(!memory.keys().any(|a| (target..target + 4096).contains(a)));
                        let moved: Vec<_> =
                            memory.range(source..source + 4096).map(|(a, b)| (target + a - source, *b)).collect();
                        memory.extend(moved);
                    }
                    "alias" | "boundary" => (),
                    _ => panic!("未知 M2 模式"),
                }
            }
            _ => panic!("本阶段只回放已有 M1/M2/M5 记录"),
        }
        let value = record["new_value"].as_u64().unwrap();
        for i in 0..8 {
            memory.insert(address + i, (value >> (8 * i)) as u8);
        }
        let mut changed = parent.clone();
        changed.sample_id = id;
        changed.path_signature = 0;
        changed.class_id = None;
        changed.truncated = false;
        // Python 的新读取填值是明确输入约定：页表 0，数据固定标记。
        // 原批次输入只提供读取范围；所有已有字节必须来自父值及记录改动。
        changed.pre_memory = witness
            .pre_memory
            .iter()
            .map(|cell| {
                assert_eq!(cell.bytes, 1);
                let byte = match memory.get(&cell.address) {
                    Some(byte) => *byte,
                    None => {
                        let base = cell.address & !7;
                        let word = witness
                            .pre_memory
                            .iter()
                            .filter(|c| (base..base + 8).contains(&c.address))
                            .fold(0u64, |w, c| w | ((c.value.unwrap() as u64) << (8 * (c.address - base))));
                        assert!(word == 0 || word == 0x5a17c0de12345678, "未记录的新读取填值");
                        (word >> (8 * (cell.address - base))) as u8
                    }
                };
                assert_eq!(Some(byte), cell.value, "回放字节不匹配，地址 {:#x}", cell.address);
                MemoryCell { address: cell.address, value: Some(byte), bytes: 1 }
            })
            .collect();
        changed.post_registers.clear();
        changed.post_memory.clear();
        changed.result = Value::Null;
        changed.ret_val.clear();
        assert_eq!(changed.pre_registers, witness.pre_registers, "原始 mutant 的寄存器与父 corpus entry 不同");
        assert_eq!(changed.isa_state, witness.isa_state);
        changed
    }
}

pub fn prepare(options: &Options, corpus: &[Sample]) -> (Vec<Sample>, Vec<Value>, Value) {
    if matches!(options.mode, Mode::JudgeOnly) {
        let samples =
            SampleChecker::load_judge_inputs(options.inputs.as_ref().unwrap()).expect("读取 mutant 失败").samples;
        let records = samples
            .iter()
            .map(|s| json!({"sample_id":s.sample_id,"operator":"given","parent_corpus_entry":null,"changes":null}))
            .collect();
        return (samples, records, json!({"mode":"judge-only","fcsr_patched":0}));
    }
    let path = options.mutations.as_ref().unwrap();
    let records: Vec<Value> =
        serde_json::from_reader(std::fs::File::open(path).expect("读取变异记录失败")).expect("变异记录损坏");
    let files = if let Some(path) = &options.inputs {
        vec![path.clone()]
    } else {
        let batches: Vec<Value> = serde_json::from_reader(
            std::fs::File::open(path.parent().unwrap().join("judge-batches.json"))
                .expect("缺少 judge-batches.json；也可显式指定 --fuzz-inputs"),
        )
        .unwrap();
        batches
            .iter()
            .filter_map(|b| {
                let args = b["command"].as_array().unwrap();
                let index = args.iter().position(|v| v == "--check-samples").unwrap();
                let path = std::path::PathBuf::from(args[index + 1].as_str().unwrap());
                path.components().any(|c| c.as_os_str().to_string_lossy().starts_with("judge-mutants-")).then_some(path)
            })
            .collect()
    };
    assert!(!files.is_empty(), "未找到历史 mutant 输入");
    let parents: BTreeMap<_, _> = corpus.iter().map(|s| ((s.path_signature, s.class_id.unwrap()), s)).collect();
    let records_by_id: BTreeMap<_, _> = records.iter().map(|r| (r["sample_id"].as_u64().unwrap(), r)).collect();
    assert_eq!(records_by_id.len(), records.len(), "mutant 编号重复");
    let mut witnesses = BTreeMap::new();
    let mut patched = 0;
    for file in files {
        // 原始对象用于证明补 fcsr 只改变两处；期望后态不参与判定。
        for line in std::fs::read_to_string(file).unwrap().lines() {
            let original: Value = serde_json::from_str(line).unwrap();
            let id = original["sample_id"].as_u64().unwrap();
            let record = records_by_id[&id];
            let parent = parents[&(
                record["parent_path_signature"].as_u64().unwrap(),
                record["parent_class_id"].as_u64().unwrap() as usize,
            )];
            let mut input = original.clone();
            let pre_missing = input["pre_registers"].get("fcsr").is_none();
            let isa_missing = input["isa_state"].get("fcsr").is_none();
            if pre_missing {
                input["pre_registers"]["fcsr"] = parent.pre_registers["fcsr"].clone();
            }
            if isa_missing {
                input["isa_state"]["fcsr"] = json!(parent.isa_state["fcsr"]);
            }
            let mut stripped = input.clone();
            if pre_missing {
                stripped["pre_registers"].as_object_mut().unwrap().remove("fcsr");
            }
            if isa_missing {
                stripped["isa_state"].as_object_mut().unwrap().remove("fcsr");
            }
            assert_eq!(stripped, original, "补 fcsr 改变了其他输入");
            assert_eq!(input["pre_memory"], original["pre_memory"], "页表输入改变");
            patched += usize::from(pre_missing || isa_missing);
            let sample: Sample = serde_json::from_value(input).expect("历史输入不是 samples v1");
            assert!(witnesses.insert(id, sample).is_none());
        }
    }
    assert_eq!(witnesses.len(), records.len());
    let mutator = ReplayMutator { witnesses };
    let mut records = records;
    records.sort_by_key(|r| r["sample_id"].as_u64().unwrap());
    let samples = records
        .iter()
        .map(|r| {
            let parent = parents
                [&(r["parent_path_signature"].as_u64().unwrap(), r["parent_class_id"].as_u64().unwrap() as usize)];
            mutator.mutate(
                parent,
                r,
                &mut random_stream(options.random_seed, &options.scenario, r["sample_id"].as_u64().unwrap()),
            )
        })
        .collect();
    let count = records.len();
    // 来源哈希原样保留在记录内，不用它们判定有效性。
    (
        samples,
        records,
        json!({"mode":"replay-log","mutants":count,"fcsr_patched":patched,"only_fcsr_changed":true,"pre_memory_unchanged":true,"replayed_bytes_match":true}),
    )
}
