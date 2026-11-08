//! 实际类的字段桶、不一致签名及批次评分；不把已知规则当成整类过滤器。
use super::{corpus::ClassIdentity, io, Feedback};
use isla_lib::executor::samples::Sample;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Feature {
    pub identity: ClassIdentity,
    pub buckets: BTreeSet<String>,
    pub potential: usize,
    pub mismatch: Option<Value>,
}
#[derive(Default)]
struct ClassCoverage {
    buckets: BTreeSet<String>,
    potential: usize,
    last_new_batch: usize,
    known: usize,
    unknown: usize,
}
#[derive(Default)]
pub struct CoverageFeedback {
    classes: BTreeMap<ClassIdentity, ClassCoverage>,
    signatures: BTreeSet<String>,
    unknown_signatures: BTreeSet<String>,
    batch: usize,
    pub additions: Vec<u64>,
}
impl Feature {
    fn signature(&self) -> Option<String> {
        self.mismatch.as_ref().filter(|m| m["infrastructure"] == false).map(|m| {
            serde_json::to_string(&json!({"target_class":self.identity,"fields":m["fields"],"phase":m["phase"]}))
                .unwrap()
        })
    }
    #[cfg(test)]
    pub fn example(guards: &str, bucket: &str) -> Self {
        Self {
            identity: ClassIdentity {
                scenario_config_id: "场景".into(),
                path_signature: 1,
                guard_vector: guards.into(),
            },
            buckets: [bucket.into()].into_iter().collect(),
            potential: 9,
            mismatch: None,
        }
    }
}
impl Feedback for CoverageFeedback {
    type Feature = Feature;
    fn is_novel(&self, feature: &Feature) -> bool {
        let new_bucket = !feature.buckets.is_empty()
            && self.classes.get(&feature.identity).is_none_or(|state| !feature.buckets.is_subset(&state.buckets));
        new_bucket
            || feature.signature().is_some_and(|key| {
                feature.mismatch.as_ref().unwrap()["filtered"] == false && !self.unknown_signatures.contains(&key)
            })
    }
    fn observe(&mut self, sample_id: u64, feature: &Feature) {
        let _ = sample_id;
        let state = self.classes.entry(feature.identity.clone()).or_default();
        if !feature.buckets.is_subset(&state.buckets) {
            state.last_new_batch = self.batch;
        }
        state.buckets.extend(feature.buckets.iter().cloned());
        state.potential = state.potential.max(feature.potential);
        if let Some(key) = feature.signature() {
            self.signatures.insert(key.clone());
            if feature.mismatch.as_ref().unwrap()["filtered"] == true {
                state.known += 1;
            } else {
                state.unknown += 1;
                self.unknown_signatures.insert(key);
            }
        }
    }
    fn score(&self, feature: &Feature) -> f64 {
        let state = self.classes.get(&feature.identity).expect("调度类尚未登记反馈");
        let remaining = state.potential.saturating_sub(state.buckets.len());
        let coverage = 1.0 + 4.0 * remaining as f64 / state.potential.max(1) as f64;
        if state.known > 0 && state.unknown == 0 && self.batch >= state.last_new_batch + 2 {
            coverage / 8.0
        } else {
            coverage
        }
    }
    fn on_corpus_add(&mut self, sample_id: u64) {
        self.additions.push(sample_id);
    }
}
impl CoverageFeedback {
    pub fn end_batch(&mut self) {
        self.batch += 1;
    }
    pub fn summary(&self) -> Value {
        json!({"batches":self.batch,"class_value_buckets":self.classes.values().map(|s|s.buckets.len()).sum::<usize>(),
            "mismatch_signatures":self.signatures.len(),"unknown_signatures":self.unknown_signatures.len(),
            "corpus_added":self.additions.len(),"classes":self.classes.iter().map(|(key,state)|json!({"identity":key,"buckets":state.buckets,"potential":state.potential,
                "last_new_batch":state.last_new_batch,"known":state.known,"unknown":state.unknown})).collect::<Vec<_>>()})
    }
}

pub fn extract(samples: &[Sample], identities: &[ClassIdentity], output: &Path) -> Vec<Feature> {
    assert_eq!(samples.len(), identities.len());
    let input = output.join("feature-input.jsonl");
    let result = output.join("feature-output.json");
    io::write_lines(&input, samples);
    let status = std::process::Command::new("python3")
        .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("tools/fuzz/value_features.py"))
        .arg(&input)
        .arg(&result)
        .env("PYTHONDONTWRITEBYTECODE", "1")
        .status()
        .expect("无法启动字段桶解码器");
    assert!(status.success(), "字段桶提取失败");
    let rows: Vec<Value> = serde_json::from_reader(std::fs::File::open(&result).unwrap()).unwrap();
    assert_eq!(rows.len(), samples.len());
    let features = rows
        .into_iter()
        .zip(identities)
        .map(|(row, key)| Feature {
            identity: key.clone(),
            buckets: serde_json::from_value(row["buckets"].clone()).unwrap(),
            potential: row["potential"].as_u64().unwrap() as usize,
            mismatch: None,
        })
        .collect();
    std::fs::remove_file(input).unwrap();
    std::fs::remove_file(result).unwrap();
    features
}
