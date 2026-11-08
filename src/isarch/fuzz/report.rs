//! P1b 同口径的类命中、转移和统计；特征内容只由此适配层定义。
use super::corpus::{ClassIdentity, Directory};
use super::io::{write_json, write_lines};
use super::{Feedback, Options};
use isla_lib::executor::samples::Sample;
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};

pub fn write(
    options: &Options,
    directory: &Directory,
    samples: &[Sample],
    records: &[Value],
    judged: &[Option<Value>],
    feedback: &mut impl Feedback<Feature = Value>,
) {
    let scene = &options.scenario;
    let aliases: BTreeMap<_, _> = directory
        .classes
        .keys()
        .map(|k| k.path_signature)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .enumerate()
        .map(|(i, p)| (p, format!("P{:02}", i + 1)))
        .collect();
    let mut ledger = Vec::new();
    let mut mutation_rows = Vec::new();
    let mut hits = BTreeMap::<ClassIdentity, BTreeMap<String, usize>>::new();
    let mut transitions = BTreeMap::<(String, ClassIdentity, ClassIdentity), usize>::new();
    for ((sample, record), row) in samples.iter().zip(records).zip(judged) {
        let operator = record["operator"].as_str().unwrap();
        let parent = if let (Some(path), Some(class_id)) =
            (record["parent_path_signature"].as_u64(), record["parent_class_id"].as_u64())
        {
            Some(
                directory
                    .classes
                    .iter()
                    .find(|(key, (c, _))| key.path_signature == path && *c == class_id as usize)
                    .expect("找不到父 corpus entry 类")
                    .0
                    .clone(),
            )
        } else {
            None
        };
        let mut metadata = record.clone();
        metadata.as_object_mut().unwrap().remove("prediction_seconds");
        if metadata["parent_corpus_entry"].is_null() {
            metadata["parent_corpus_entry"] =
                json!(parent.as_ref().map(|key| json!({"sample_id":directory.classes[key].1,"identity":key})));
        }
        mutation_rows.push(metadata);
        let actual = row.as_ref().map(|r| directory.identity(scene, r));
        let status = match &actual {
            None => "unaccepted",
            Some(key) if !directory.classes.contains_key(key) => "new",
            Some(_) if parent.is_none() => "accepted",
            Some(key) if parent.as_ref() == Some(key) => "stay",
            Some(_) => "jump",
        };
        if let Some(key) = &actual {
            *hits.entry(key.clone()).or_default().entry(operator.into()).or_default() += 1;
            if status == "jump" {
                if let Some(parent) = &parent {
                    *transitions.entry((operator.into(), parent.clone(), key.clone())).or_default() += 1;
                }
            }
        }
        let result = row.as_ref().map(|r| &r["sample"]["result"]);
        let exception = result
            .and_then(|r| r["value"]["struct"].as_object())
            .and_then(|fields| fields.values().find_map(|v| v["ctor"].as_str()));
        let cause = exception.map(|e| match e {
            "E_Load_Access_Fault" => 5,
            "E_SAMO_Access_Fault" => 7,
            "E_Load_Page_Fault" => 13,
            "E_SAMO_Page_Fault" => 15,
            _ => panic!("P1b 报表中未知异常 {e}"),
        });
        ledger.push(json!({"scene":scene,"sample_id":sample.sample_id,"mutant":format!("mutant-{:04}",sample.sample_id),"operator":operator,
            "parent_sample_id":record["parent_sample_id"],"parent_path":parent.as_ref().map(|k|k.path_signature),
            "parent_path_alias":parent.as_ref().map(|k|&aliases[&k.path_signature]),"parent_class_id":record["parent_class_id"],
            "actual_path":actual.as_ref().map(|k|k.path_signature),"actual_path_alias":actual.as_ref().and_then(|k|aliases.get(&k.path_signature)),
            "actual_class_id":actual.as_ref().and_then(|k|directory.classes.get(k).map(|(c,_)|c)),"guard_vector":actual.as_ref().map(|k|&k.guard_vector),
            "status":status,"result":result.map(|r|&r["ctor"]),"exception_type":exception,"judge_cause":cause.unwrap_or(0),
            "parent_identity":parent,"actual_identity":actual}));
        let features = json!({"class":actual,"result":result,"value_buckets": sample.pre_memory.iter().filter_map(|c|c.value).map(|b|b>>4).collect::<BTreeSet<_>>()});
        feedback.observe(sample.sample_id, &features);
    }
    let mut statistics = BTreeMap::new();
    let operators = records.iter().map(|r| r["operator"].as_str().unwrap()).collect::<BTreeSet<_>>();
    for operator in std::iter::once(None).chain(operators.into_iter().map(Some)) {
        let rows = ledger.iter().filter(|r| operator.is_none_or(|op| r["operator"] == op)).collect::<Vec<_>>();
        let count = |status: &str| rows.iter().filter(|r| r["status"] == status).count();
        let total = rows.len();
        let stay = count("stay");
        let jump = count("jump");
        let unaccepted = count("unaccepted");
        let hit_classes = hits
            .iter()
            .filter(|(k, ops)| directory.classes.contains_key(*k) && operator.is_none_or(|op| ops.contains_key(op)))
            .count();
        let total_classes = directory.classes.len();
        let ratio = |n| if total == 0 { 0.0 } else { n as f64 / total as f64 };
        statistics.insert(operator.map_or_else(||scene.clone(),|op|format!("{scene}/{op}")),json!({"total":total,"accepted":total-unaccepted,"stay":stay,"jump":jump,"new":count("new"),"unaccepted":unaccepted,"stay_ratio":ratio(stay),"jump_ratio":ratio(jump),"total_classes":total_classes,"hit_classes":hit_classes,"unhit_classes":total_classes-hit_classes,"hit_ratio":hit_classes as f64/total_classes as f64}));
    }
    let transition_rows = transitions.iter().map(|((op,parent,actual),count)|json!({"scene":scene,"operator":op,
        "parent_path":parent.path_signature,"parent_path_alias":aliases[&parent.path_signature],"parent_class_id":directory.classes[parent].0,
        "actual_path":actual.path_signature,"actual_path_alias":aliases[&actual.path_signature],"actual_class_id":directory.classes[actual].0,"count":count})).collect::<Vec<_>>();
    let coverage = directory.classes.iter().map(|(k,(class_id,_))|json!({"scene":scene,"identity":k,"path_signature":k.path_signature,"class_id":class_id,"operators":hits.get(k),"hit":hits.contains_key(k)})).collect::<Vec<_>>();
    write_lines(&options.output.join("mutations.jsonl"), &mutation_rows);
    write_json(&options.output.join("ledger.json"), &ledger);
    write_json(&options.output.join("statistics.json"), &statistics);
    write_json(&options.output.join("transitions.json"), &transition_rows);
    write_json(&options.output.join("coverage.json"), &coverage);
}
