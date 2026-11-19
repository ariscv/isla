//! 记录有效 mutant 的父系及接纳依据，并只读核对运行记录。
use super::{complete_observation, mismatch_feature, ClassIdentity, Entry};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::{BufRead, BufReader, ErrorKind},
    path::Path,
};

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum AdmissionReason {
    NewPerfSignature,
    NewModelCoverage,
    NewMismatch,
}

#[derive(Deserialize, Serialize)]
struct Certification {
    guard_unique: bool,
    post_unique: bool,
    l1: bool,
}

#[derive(Clone, Deserialize, Serialize)]
pub(super) struct Observation {
    pub agree: bool,
    pub bucket: String,
    pub mismatch_signature: Option<String>,
}

impl Observation {
    pub(super) fn from_fixed(fixed: &Value) -> Self {
        Self {
            agree: fixed["agree"].as_bool().unwrap(),
            bucket: fixed["bucket"].as_str().unwrap().into(),
            mismatch_signature: mismatch_feature(fixed),
        }
    }
}

#[derive(Deserialize, Serialize)]
struct Feedback {
    arm: String,
    new_signal: bool,
    signal_kind: Option<AdmissionReason>,
}

#[derive(Deserialize, Serialize)]
pub(super) struct Mutant {
    mutant_sample_id: u64,
    parent_entry: usize,
    parent_sample_id: u64,
    parent_generation: usize,
    operator: String,
    target_identity: ClassIdentity,
    actual_identity: ClassIdentity,
    certified: Certification,
    observation: Observation,
    feedback: Feedback,
    admitted: bool,
    admitted_reason: Option<AdmissionReason>,
    new_entry_index: Option<usize>,
}

impl Mutant {
    // 调用点已通过完整 judge、L1 构造和编译，并取得完整硬件观察。
    pub(super) fn new(
        record: &Value,
        parent: &Entry,
        actual_identity: &ClassIdentity,
        observation: Observation,
        arm: &str,
        reason: Option<AdmissionReason>,
        new_entry_index: Option<usize>,
    ) -> Self {
        assert_eq!(reason.is_some(), new_entry_index.is_some());
        Self {
            mutant_sample_id: record["sample_id"].as_u64().unwrap(),
            parent_entry: record["parent_entry"].as_u64().unwrap() as usize,
            parent_sample_id: parent.sample.sample_id,
            parent_generation: parent.generation,
            operator: record["operator"].as_str().unwrap().into(),
            target_identity: serde_json::from_value(record["target_identity"].clone()).unwrap(),
            actual_identity: actual_identity.clone(),
            certified: Certification { guard_unique: true, post_unique: true, l1: true },
            observation,
            feedback: Feedback { arm: arm.into(), new_signal: reason.is_some(), signal_kind: reason },
            admitted: new_entry_index.is_some(),
            admitted_reason: reason,
            new_entry_index,
        }
    }
}

#[derive(Deserialize)]
struct LegacyRecord {
    sample_id: u64,
    parent_entry: usize,
    parent_sample_id: u64,
    operator: String,
    target_identity: ClassIdentity,
}

#[derive(Deserialize)]
struct LegacyCertification {
    guard_unique: bool,
    post_unique: bool,
    path_signature: u64,
    guard_vector: String,
}

#[derive(Deserialize)]
struct CertifiedRow {
    record: LegacyRecord,
    certification: LegacyCertification,
    fixed: Value,
    new_feedback: bool,
    corpus_entries: usize,
}

#[derive(Default, Deserialize)]
struct Metadata {
    arm: Option<String>,
    initial_corpus: Option<usize>,
    cases: Option<usize>,
    corpus_added: Option<usize>,
    infrastructure: Option<usize>,
}

#[derive(Default)]
struct Run {
    rows: Vec<Mutant>,
    mutant_ids: BTreeSet<u64>,
    // entry 下标直接指向产生该 entry 的 mutant 记录。
    admitted: BTreeMap<usize, usize>,
    initial_parents: BTreeMap<usize, u64>,
    initial_corpus: Option<usize>,
    arm: Option<String>,
    generations: BTreeMap<usize, usize>,
    reused: usize,
    longest: Option<usize>,
    witness: Option<(usize, usize)>,
}

impl Run {
    fn backfill(&mut self, row: CertifiedRow) -> Result<Mutant, String> {
        let CertifiedRow { record, certification, fixed, new_feedback, corpus_entries } = row;
        let initial = corpus_entries
            .checked_sub(self.admitted.len() + usize::from(new_feedback))
            .ok_or("旧归档 corpus_entries 小于已接纳数")?;
        if self.initial_corpus.is_some_and(|count| count != initial) {
            return Err("旧归档的 corpus 增量与 new_feedback 不符".into());
        }
        self.initial_corpus = Some(initial);

        if fixed["agree"].as_bool().is_none() || !fixed["bucket"].is_string() || !complete_observation(&fixed) {
            return Err("旧归档的有效 mutant 缺少硬件观察".into());
        }
        let observation = Observation::from_fixed(&fixed);
        let arm = self.arm.as_deref().unwrap_or("unknown");
        let reason = if new_feedback {
            // 旧记录没有按信号记账；B1 的分歧例同时可能新增模型覆盖。
            match (arm, observation.agree) {
                ("B1", true) => Some(AdmissionReason::NewModelCoverage),
                ("B2" | "T", true) => Some(AdmissionReason::NewPerfSignature),
                ("B2" | "T", false) => Some(AdmissionReason::NewMismatch),
                _ => None,
            }
        } else {
            None
        };
        let actual_identity = ClassIdentity {
            scenario_config_id: record.target_identity.scenario_config_id.clone(),
            path_signature: certification.path_signature,
            guard_vector: certification.guard_vector,
        };
        Ok(Mutant {
            mutant_sample_id: record.sample_id,
            parent_entry: record.parent_entry,
            parent_sample_id: record.parent_sample_id,
            parent_generation: self
                .admitted
                .get(&record.parent_entry)
                .map_or(0, |&i| self.rows[i].parent_generation + 1),
            operator: record.operator,
            target_identity: record.target_identity,
            actual_identity,
            certified: Certification {
                guard_unique: certification.guard_unique,
                post_unique: certification.post_unique,
                l1: true,
            },
            observation,
            feedback: Feedback { arm: arm.into(), new_signal: new_feedback, signal_kind: reason },
            admitted: new_feedback,
            admitted_reason: reason,
            new_entry_index: new_feedback.then(|| corpus_entries - 1),
        })
    }

    fn record(&mut self, row: Mutant, backfilled: bool) -> Result<(), String> {
        if !row.certified.guard_unique
            || !row.certified.post_unique
            || !row.certified.l1
            || row.actual_identity != row.target_identity
            || !matches!(row.operator.as_str(), "A" | "B")
        {
            return Err("目标类或认证记录不符".into());
        }
        if row.observation.agree == row.observation.mismatch_signature.is_some()
            || row.observation.bucket.is_empty()
            || (!backfilled && row.observation.agree != (row.observation.bucket == "agree"))
        {
            return Err("硬件观察不完整".into());
        }
        if self.arm.get_or_insert_with(|| row.feedback.arm.clone()) != &row.feedback.arm
            || row.admitted != row.feedback.new_signal
            || row.admitted != row.new_entry_index.is_some()
            || row.admitted_reason != row.feedback.signal_kind
            || (!backfilled && row.admitted != row.admitted_reason.is_some())
            || (row.feedback.arm == "B0" && row.admitted)
        {
            return Err("反馈与 corpus 接纳记录不符".into());
        }
        if !self.mutant_ids.insert(row.mutant_sample_id) {
            return Err("mutant ID 重复".into());
        }
        let index = self.rows.len();
        if let Some(&parent_index) = self.admitted.get(&row.parent_entry) {
            let parent = &self.rows[parent_index];
            if row.parent_sample_id != parent.mutant_sample_id || row.parent_generation != parent.parent_generation + 1
            {
                return Err("父 ID 或代数与先前接纳记录不符".into());
            }
            self.reused += 1;
            self.witness.get_or_insert((parent_index, index));
        } else {
            if row.parent_generation != 0
                || self.initial_corpus.is_some_and(|count| row.parent_entry >= count)
                || self.mutant_ids.contains(&row.parent_sample_id)
                || *self.initial_parents.entry(row.parent_entry).or_insert(row.parent_sample_id) != row.parent_sample_id
            {
                return Err("初始父 entry 不符或缺少先前的接纳记录".into());
            }
        }
        if let Some(entry) = row.new_entry_index {
            let initial = *self.initial_corpus.get_or_insert(entry);
            if entry.checked_sub(initial) != Some(self.admitted.len())
                || self.initial_parents.last_key_value().is_some_and(|(&index, _)| index >= initial)
            {
                return Err("新增 entry 下标与 corpus 增量不符".into());
            }
            self.admitted.insert(entry, index);
        }
        let generation = row.parent_generation + 1;
        *self.generations.entry(generation).or_default() += 1;
        if self.longest.is_none_or(|i| row.parent_generation > self.rows[i].parent_generation) {
            self.longest = Some(index);
        }
        self.rows.push(row);
        Ok(())
    }

    fn ancestors(&self, start: usize) -> Vec<u64> {
        let mut row = &self.rows[start];
        let mut chain = vec![row.mutant_sample_id];
        loop {
            chain.push(row.parent_sample_id);
            match self.admitted.get(&row.parent_entry) {
                Some(&index) => row = &self.rows[index],
                None => return chain,
            }
        }
    }
}

pub(super) fn summarize(directory: &Path) -> Result<Value, String> {
    let native = directory.join("lineage.jsonl");
    let (source, file, backfilled) = match File::open(&native) {
        Ok(file) => ("lineage.jsonl", file, false),
        Err(error) if error.kind() == ErrorKind::NotFound => {
            let legacy = directory.join("certified.jsonl");
            ("certified.jsonl", File::open(&legacy).map_err(|error| format!("{}: {error}", legacy.display()))?, true)
        }
        Err(error) => return Err(format!("{}: {error}", native.display())),
    };

    let summary_path = directory.join("summary.json");
    let metadata: Metadata = match File::open(&summary_path) {
        Ok(file) => serde_json::from_reader(BufReader::new(file))
            .map_err(|error| format!("{}: {error}", summary_path.display()))?,
        Err(error) if error.kind() == ErrorKind::NotFound => Metadata::default(),
        Err(error) => return Err(format!("{}: {error}", summary_path.display())),
    };
    let arm = metadata.arm.or_else(|| {
        let (arm, _) = directory.file_name()?.to_str()?.split_once("-seed-")?;
        matches!(arm, "B0" | "B1" | "B2" | "T").then(|| arm.to_owned())
    });
    let mut run = Run { arm, initial_corpus: metadata.initial_corpus, ..Run::default() };
    let mut infrastructure = 0;
    for (index, line) in BufReader::new(file).lines().enumerate() {
        let read = || -> Result<(), String> {
            let line = line.map_err(|error| error.to_string())?;
            if backfilled {
                let archived = serde_json::from_str(&line).map_err(|error| error.to_string())?;
                let row = run.backfill(archived)?;
                return run.record(row, true);
            }
            let row: Value = serde_json::from_str(&line).map_err(|error| error.to_string())?;
            if row.get("infrastructure_failure").is_some() {
                if !row["infrastructure_failure"].is_object() || row.as_object().unwrap().len() != 1 {
                    return Err("基础设施失败行不能同时含有效 mutant 字段".into());
                }
                infrastructure += 1;
                return Ok(());
            }
            run.record(serde_json::from_value(row).map_err(|error| error.to_string())?, false)
        };
        read().map_err(|error| format!("{source}:{}: {error}", index + 1))?;
    }
    if metadata.cases.is_some_and(|cases| run.rows.len() != cases)
        || metadata.corpus_added.is_some_and(|added| run.admitted.len() != added)
        || (!backfilled && metadata.infrastructure.is_some_and(|count| infrastructure != count))
    {
        return Err("日志计数与 summary.json 不符".into());
    }
    let witness = run.witness.map(|(parent, child)| {
        json!({"admitted_parent":run.rows[parent],"certified_child":run.rows[child],"ancestor_chain":run.ancestors(child)})
    });
    let witness_reason = if witness.is_some() {
        None
    } else if run.rows.is_empty() {
        Some("no_valid_mutants")
    } else if run.admitted.is_empty() {
        Some("no_admitted_entries")
    } else {
        Some("no_admitted_entry_selected_as_parent")
    };
    Ok(json!({
        "source":source,"backfilled":backfilled,"arm":run.arm,"initial_corpus":run.initial_corpus,
        "mutants_by_generation":run.generations,"admitted":run.admitted.len(),"mutants_from_admitted_parent":run.reused,
        "infrastructure_failures":if backfilled {metadata.infrastructure} else {Some(infrastructure)},
        "longest_ancestor_chain":run.longest.map(|index|run.ancestors(index)).unwrap_or_default(),
        "witness_found":witness.is_some(),"witness_reason":witness_reason,"witness":witness
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::isarch::fuzz::ablation::{admission_reason, admit, observe, select_request, Entry};
    use crate::isarch::fuzz::{corpus::Directory, tests::example_sample};
    use rand::rngs::mock::StepRng;
    use serde_json::json;
    use std::collections::{BTreeMap, VecDeque};
    use std::fs;

    #[test]
    fn neighbor_mutant_is_logged_and_can_be_selected_as_parent() {
        let parent = ClassIdentity { scenario_config_id: "test".into(), path_signature: 1, guard_vector: "00".into() };
        let neighbor = ClassIdentity { guard_vector: "01".into(), ..parent.clone() };
        let directory = Directory { classes: BTreeMap::from([(parent.clone(), (0, 10)), (neighbor.clone(), (1, 11))]) };
        let classes = [parent.clone(), neighbor.clone()];
        let sample = |id, class_id| {
            let mut sample = example_sample();
            sample.sample_id = id;
            sample.path_signature = 1;
            sample.class_id = Some(class_id);
            sample
        };
        let mut entries = vec![
            Entry { sample: sample(10, 0), identity: parent, selections: 0, score: 1, generation: 0 },
            Entry { sample: sample(11, 1), identity: neighbor.clone(), selections: 0, score: 1, generation: 0 },
        ];
        let mut rng = StepRng::new(0, 0);
        let (parent_index, target, operator) =
            select_request(&entries, &classes, &[0, 0], Some((0, true)), true, &mut rng);
        assert_eq!((parent_index, target, operator), (0, &neighbor, "B"));
        let certification = json!({"guard_unique":true, "post_unique":true, "path_signature":1, "guard_vector":"01"});
        let actual = directory.identity("test", &certification);
        let request = json!({"sample_id":12,"parent_entry":parent_index,"parent_sample_id":10,"operator":operator,"target_identity":target});
        let observation = Observation { agree: true, bucket: "agree".into(), mismatch_signature: None };
        let mut bursts = VecDeque::new();
        let reason = admission_reason("T", false, || unreachable!(), || true);
        let new_entry_index = admit(&mut entries, &mut bursts, parent_index, &sample(12, 1), &actual, reason);
        assert_eq!(new_entry_index, Some(2));
        assert_eq!(entries.len(), 3);
        assert_eq!(entries[2].generation, 1);
        let admitted =
            Mutant::new(&request, &entries[parent_index], &actual, observation.clone(), "T", reason, new_entry_index);
        let row = serde_json::to_value(&admitted).unwrap();
        assert_eq!(
            row,
            json!({
                "mutant_sample_id":12,"parent_entry":0,"parent_sample_id":10,"parent_generation":0,
                "operator":"B","target_identity":neighbor,"actual_identity":actual,
                "certified":{"guard_unique":true,"post_unique":true,"l1":true},
                "observation":{"agree":true,"bucket":"agree","mismatch_signature":null},
                "feedback":{"arm":"T","new_signal":true,"signal_kind":"new_perf_signature"},
                "admitted":true,"admitted_reason":"new_perf_signature","new_entry_index":2
            })
        );

        entries[0].selections = 2;
        entries[1].selections = 1;
        let (second_parent, target, operator) = select_request(&entries, &classes, &[0, 0], None, true, &mut rng);
        assert_eq!((second_parent, target, operator), (2, &neighbor, "A"));
        let request = json!({"sample_id":13,"parent_entry":second_parent,"parent_sample_id":12,"operator":operator,"target_identity":target});
        let reason = admission_reason("T", false, || unreachable!(), || false);
        let new_entry_index = admit(&mut entries, &mut bursts, second_parent, &sample(13, 1), &actual, reason);
        assert_eq!(new_entry_index, None);
        assert_eq!(entries.len(), 3);
        let child =
            Mutant::new(&request, &entries[second_parent], &actual, observation.clone(), "T", reason, new_entry_index);
        assert_eq!(child.parent_generation, 1);

        let mut old_entry = serde_json::to_value(&entries[0]).unwrap();
        old_entry.as_object_mut().unwrap().remove("generation");
        assert_eq!(serde_json::from_value::<Entry>(old_entry).unwrap().generation, 0);

        let fixture = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join(format!("output/ablation-lineage-unit-{}", std::process::id()));
        fs::create_dir_all(&fixture).unwrap();
        let mut log = fs::File::create(fixture.join("lineage.jsonl")).unwrap();
        let (mut cases, mut failures) = (0, 0);
        for (index, incomplete) in
            [json!({"agree":false,"bucket":"timeout"}), json!({"agree":true,"bucket":"agree"})].iter().enumerate()
        {
            let failed = json!({"sample_id":14 + index,"parent_entry":0,"parent_sample_id":10,"operator":"A"});
            assert!(observe::record_mutant(&failed, incomplete, &mut log, &mut cases, &mut failures).is_none());
        }
        assert_eq!((cases, failures), (0, 2));
        assert_eq!(entries.len(), 3);
        let mut lines = BufReader::new(File::open(fixture.join("lineage.jsonl")).unwrap()).lines();
        for bucket in ["timeout", "agree"] {
            let failed: Value = serde_json::from_str(&lines.next().unwrap().unwrap()).unwrap();
            assert_eq!(failed["infrastructure_failure"]["bucket"], bucket);
            assert_eq!(failed.as_object().unwrap().len(), 1);
        }
        let complete = json!({
            "agree":true,"bucket":"agree","isla_consistent_side":"both","native_exit_symbol":"good_trap_ins",
            "nemu_cause":0,"xs_cause":0,
            "observation":{"isla_consistent_side":"both","native_guided_exec":false,"native_result":{"event":"step","mcause":0}}
        });
        assert!(observe::record_mutant(&request, &complete, &mut log, &mut cases, &mut failures).is_some());
        assert_eq!((cases, failures), (1, 2));
        super::super::append(&mut log, &admitted);
        let summary = summarize(&fixture).unwrap();
        assert_eq!(summary["witness_found"], false);
        assert_eq!(summary["witness_reason"], "no_admitted_entry_selected_as_parent");
        assert_eq!(summary["infrastructure_failures"], 2);
        super::super::append(&mut log, &child);
        let summary = summarize(&fixture).unwrap();
        assert_eq!(summary["witness_found"], true);
        assert_eq!(summary["mutants_by_generation"], json!({"1":1,"2":1}));
        assert_eq!(summary["admitted"], 1);
        assert_eq!(summary["mutants_from_admitted_parent"], 1);
        assert_eq!(summary["longest_ancestor_chain"], json!([13, 12, 10]));
        assert_eq!(summary["witness"]["admitted_parent"]["mutant_sample_id"], 12);
        assert_eq!(summary["witness"]["certified_child"]["mutant_sample_id"], 13);

        let reason = admission_reason("B0", true, || unreachable!(), || unreachable!());
        let mut control_entries = entries[..2].to_vec();
        let mut control_bursts = VecDeque::new();
        let new_entry_index = admit(&mut control_entries, &mut control_bursts, 0, &sample(12, 1), &actual, reason);
        let control = Mutant::new(
            &json!({"sample_id":12,"parent_entry":0,"parent_sample_id":10,"operator":"B","target_identity":neighbor}),
            &control_entries[0],
            &actual,
            observation,
            "B0",
            reason,
            new_entry_index,
        );
        assert!(!control.admitted);
        assert!(!control.feedback.new_signal);
        assert!(control.admitted_reason.is_none());
        assert_eq!(control_entries.len(), 2);
        assert!(control_bursts.is_empty());
        drop(log);
        let mut log = fs::File::create(fixture.join("lineage.jsonl")).unwrap();
        super::super::append(&mut log, &control);
        let summary = summarize(&fixture).unwrap();
        assert_eq!(summary["admitted"], 0);
        assert_eq!(summary["witness_found"], false);
        drop(log);
        fs::remove_dir_all(fixture).unwrap();
    }
}
