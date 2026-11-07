use super::*;
use rand::RngCore;
use serde_json::json;

#[test]
fn mutant_random_stream_is_independent_of_order() {
    let mut first = random_stream(42, "sv39-store", 7);
    let expected = first.next_u64();
    assert_ne!(expected, random_stream(42, "sv39-store", 8).next_u64());
    assert_eq!(expected, random_stream(42, "sv39-store", 7).next_u64());
    assert_ne!(expected, random_stream(42, "sv48-store", 7).next_u64());
    assert_ne!(expected, random_stream(43, "sv39-store", 7).next_u64());
}

#[test]
fn feedback_observes_without_admitting_or_scoring_features() {
    let mut feedback = LogFeedback::default();
    let feature = json!({"任意特征": [1, 2]});
    feedback.observe(3, &feature);
    assert!(!feedback.is_novel(&feature));
    assert_eq!(feedback.score(&feature), 1.0);
    feedback.on_corpus_add(3);
    feedback.on_mismatch(3, &json!({"字段":"x2"}));
    assert_eq!(feedback.rows[0], json!({"sample_id":3,"features":feature}));
}

#[test]
fn scheduler_updates_only_after_a_complete_batch() {
    let mut scheduler = ReplayScheduler::new(5);
    assert_eq!(scheduler.next_batch(2), vec![0, 1]);
    assert_eq!(scheduler.next_batch(2), vec![0, 1]);
    scheduler.on_batch_end(2);
    assert_eq!(scheduler.next_batch(4), vec![2, 3, 4]);
    scheduler.on_batch_end(3);
    assert!(scheduler.next_batch(1).is_empty());
}

#[test]
fn canonical_coordinates_do_not_depend_on_record_numbers() {
    let row = json!({"guard_order":[83,12],"guard_assignment":{"83":false,"12":true},"guard_vector":"01"});
    let mut actual = row.clone();
    canonical_coordinates(&mut actual);
    assert_eq!(actual["guard_order"], json!([0, 1]));
    assert_eq!(actual["guard_assignment"], json!({"0":false,"1":true}));
}

#[test]
fn oracle_has_an_explicit_no_hardware_result() {
    assert_eq!(NoHardwareOracle.compare(&json!({}), &json!({})), None);
}

pub(super) fn example_sample() -> isla_lib::executor::samples::Sample {
    serde_json::from_value(json!({"schema_version":1,"sample_id":10,"mode":"merge","path_signature":123,
        "class_id":0,"truncated":false,"pre_registers":{},"post_registers":{},"isa_state":{},
        "pre_memory":[{"address":4096,"value":1,"bytes":1},{"address":4097,"value":0,"bytes":1},
            {"address":4098,"value":0,"bytes":1},{"address":4099,"value":0,"bytes":1},
            {"address":4100,"value":0,"bytes":1},{"address":4101,"value":0,"bytes":1},
            {"address":4102,"value":0,"bytes":1},{"address":4103,"value":0,"bytes":1}],
        "post_memory":[],"result":{"unit":true},"ret_val":"()"}))
    .unwrap()
}

#[test]
fn replay_mutator_applies_record_and_rejects_wrong_old_value() {
    let parent = example_sample();
    let mut witness = parent.clone();
    witness.pre_memory[0].value = Some(0x81);
    let mutator = super::replay::ReplayMutator { witnesses: [(0, witness)].into_iter().collect() };
    let record = json!({"sample_id":0,"operator":"M1","address":4096,"old_value":1,"new_value":129,"bits":[7]});
    let mutant = mutator.mutate(&parent, &record, &mut random_stream(0, "场景", 0));
    assert_eq!(mutant.sample_id, 0);
    assert_eq!(mutant.pre_memory[0].value, Some(129));
    let mut wrong = record;
    wrong["old_value"] = json!(2);
    assert!(std::panic::catch_unwind(|| mutator.mutate(&parent, &wrong, &mut random_stream(0, "场景", 0))).is_err());
}

#[test]
fn model_executor_drains_in_number_order() {
    super::classifier::test_executor_order();
}

#[test]
fn p1b_path_aliases_start_at_one() {
    use super::corpus::{ClassIdentity, Directory};
    let output = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("output/fuzz-step2/unit/aliases");
    std::fs::create_dir_all(&output).unwrap();
    let sample = example_sample();
    let identity = ClassIdentity { scenario_config_id: "场景".into(), path_signature: 123, guard_vector: "0".into() };
    let directory = Directory { classes: [(identity, (0, 10))].into_iter().collect() };
    let options = Options {
        mode: Mode::ReplayLog,
        scenario: "场景".into(),
        corpus: "unused".into(),
        inputs: None,
        mutations: None,
        output: output.clone(),
        random_seed: 0,
        batch_size: 2,
    };
    let record = json!({"sample_id":0,"operator":"M1","parent_path_signature":123,"parent_class_id":0});
    let judged = json!({"path_signature":123,"guard_vector":"0","sample":{"result":{"ctor":"Retire_Success"}}});
    super::report::write(&options, &directory, &[sample], &[record], &[Some(judged)], &mut LogFeedback::default());
    let ledger: serde_json::Value =
        serde_json::from_reader(std::fs::File::open(output.join("ledger.json")).unwrap()).unwrap();
    assert_eq!(ledger[0]["parent_path_alias"], "P01");
    assert_eq!(ledger[0]["actual_path_alias"], "P01");
}

#[test]
fn reconfirm_rejects_changed_path_state_and_rank() {
    let sample = example_sample();
    let output = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("output/fuzz-step2/unit/reconfirm");
    std::fs::create_dir_all(&output).unwrap();
    let row = json!({"path_signature":123,"guard_vector":"0","guard_unique":true,"post_unique":true,"sample":sample});
    super::corpus::Directory::reconfirm("场景", &[sample.clone()], &[Some(row.clone())], &output);
    for field in ["path_signature", "result", "class_id"] {
        let mut changed = row.clone();
        let mut parent = sample.clone();
        match field {
            "path_signature" => changed["path_signature"] = json!(124),
            "result" => changed["sample"]["result"] = json!({"bool":false}),
            "class_id" => parent.class_id = Some(1),
            _ => unreachable!(),
        }
        assert!(std::panic::catch_unwind(|| super::corpus::Directory::reconfirm(
            "场景",
            &[parent],
            &[Some(changed)],
            &output
        ))
        .is_err());
    }
}

#[test]
fn replay_m2_copies_page_and_m5_changes_only_recorded_bits() {
    use isla_lib::executor::samples::MemoryCell;
    let mut parent = example_sample();
    parent.pre_memory[1].value = Some(8);
    parent.pre_memory.push(MemoryCell { address: 8192, value: Some(9), bytes: 1 });
    let mut witness = parent.clone();
    witness.pre_memory[1].value = Some(12);
    witness.pre_memory.push(MemoryCell { address: 12288, value: Some(9), bytes: 1 });
    let mutator = super::replay::ReplayMutator { witnesses: [(0, witness)].into_iter().collect() };
    let record = json!({"sample_id":0,"operator":"M2","address":4096,"old_value":2049,"new_value":3073,"ppn":3,"m2_mode":"move","old_page":8192,"new_page":12288});
    let actual = mutator.mutate(&parent, &record, &mut random_stream(0, "场景", 0));
    assert_eq!(actual.pre_memory.last().unwrap().value, Some(9));
    let parent = example_sample();
    let mut witness = parent.clone();
    witness.pre_memory[0].value = Some(33);
    witness.pre_memory[1].value = Some(3);
    let mutator = super::replay::ReplayMutator { witnesses: [(0, witness)].into_iter().collect() };
    let record = json!({"sample_id":0,"operator":"M5","address":4096,"old_value":1,"new_value":801,"free_mask":7});
    let actual = mutator.mutate(&parent, &record, &mut random_stream(0, "场景", 0));
    assert_eq!(actual.pre_memory[0].value, Some(33));
    assert_eq!(actual.pre_memory[1].value, Some(3));
}

#[test]
fn mutation_metadata_identifies_current_corpus_entry() {
    use super::corpus::{ClassIdentity, Directory};
    let identity =
        ClassIdentity { scenario_config_id: "场景".into(), path_signature: 123, guard_vector: "01".into() };
    let directory = Directory { classes: [(identity.clone(), (0, 10))].into_iter().collect() };
    let record = json!({"sample_id":0,"parent_sample_id":11,"parent_path_signature":123,"parent_class_id":0,"prediction_seconds":1.2});
    let output = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("output/fuzz-step2/unit/metadata");
    std::fs::create_dir_all(&output).unwrap();
    let options = Options {
        mode: Mode::ReplayLog,
        scenario: "场景".into(),
        corpus: "unused".into(),
        inputs: None,
        mutations: None,
        output: output.clone(),
        random_seed: 0,
        batch_size: 2,
    };
    let mut record = record;
    record["operator"] = json!("M1");
    let judged = json!({"path_signature":123,"guard_vector":"01","sample":{"result":{"ctor":"Retire_Success"}}});
    super::report::write(
        &options,
        &directory,
        &[example_sample()],
        &[record],
        &[Some(judged)],
        &mut LogFeedback::default(),
    );
    let text = std::fs::read_to_string(output.join("mutations.jsonl")).unwrap();
    let row: serde_json::Value = serde_json::from_str(text.trim()).unwrap();
    assert_eq!(row["parent_sample_id"], 11);
    assert_eq!(row["parent_corpus_entry"]["sample_id"], 10);
    assert_eq!(row["parent_corpus_entry"]["identity"], serde_json::to_value(identity).unwrap());
    assert!(row.get("prediction_seconds").is_none());
}

#[test]
fn judge_only_does_not_invent_a_parent_class_transition() {
    use super::corpus::{ClassIdentity, Directory};
    let output = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("output/fuzz-step2/unit/judge-only");
    std::fs::create_dir_all(&output).unwrap();
    let identity = ClassIdentity { scenario_config_id: "场景".into(), path_signature: 123, guard_vector: "0".into() };
    let directory = Directory { classes: [(identity, (0, 10))].into_iter().collect() };
    let options = Options {
        mode: Mode::JudgeOnly,
        scenario: "场景".into(),
        corpus: "unused".into(),
        inputs: None,
        mutations: None,
        output: output.clone(),
        random_seed: 0,
        batch_size: 2,
    };
    let row = json!({"path_signature":123,"guard_vector":"0","sample":{"result":{"ctor":"Retire_Success"}}});
    super::report::write(
        &options,
        &directory,
        &[example_sample()],
        &[json!({"operator":"given"})],
        &[Some(row)],
        &mut LogFeedback::default(),
    );
    let ledger: serde_json::Value =
        serde_json::from_reader(std::fs::File::open(output.join("ledger.json")).unwrap()).unwrap();
    assert_eq!(ledger[0]["status"], "accepted");
}
