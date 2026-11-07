//! corpus 的有效性由当前模型重新认证；类号只是兼容输出中的目录名次。
use super::io::write_json;
use isla_lib::executor::samples::Sample;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::path::Path;

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
pub struct ClassIdentity {
    pub scenario_config_id: String,
    pub path_signature: u64,
    pub guard_vector: String,
}
pub struct Directory {
    pub classes: BTreeMap<ClassIdentity, (usize, u64)>,
}
impl Directory {
    pub fn identity(&self, scenario: &str, row: &Value) -> ClassIdentity {
        ClassIdentity {
            scenario_config_id: scenario.into(),
            path_signature: row["path_signature"].as_u64().unwrap(),
            guard_vector: row["guard_vector"].as_str().unwrap().into(),
        }
    }
    pub fn reconfirm(scenario: &str, corpus: &[Sample], judged: &[Option<Value>], output: &Path) -> Self {
        assert_eq!(corpus.len(), judged.len());
        let mut classes = BTreeMap::new();
        let mut rows = Vec::new();
        for (input, row) in corpus.iter().zip(judged) {
            let row = row.as_ref().expect("corpus entry 未被任何路径接纳");
            assert_eq!(row["path_signature"], json!(input.path_signature), "corpus entry 路径改变");
            assert_eq!(row["guard_unique"], true);
            assert_eq!(row["post_unique"], true);
            let expected = serde_json::to_value(input).unwrap();
            for field in
                ["result", "pre_registers", "post_registers", "pre_memory", "post_memory", "ret_val", "isa_state"]
            {
                assert_eq!(row["sample"][field], expected[field], "corpus entry {} 的 {field} 改变", input.sample_id);
            }
            let identity = ClassIdentity {
                scenario_config_id: scenario.into(),
                path_signature: input.path_signature,
                guard_vector: row["guard_vector"].as_str().unwrap().into(),
            };
            assert!(
                classes.insert(identity, (input.class_id.expect("corpus entry 缺少类号"), input.sample_id)).is_none(),
                "corpus 中类重复"
            );
            rows.push(json!({"sample_id": input.sample_id,"accepted_paths":1,"path_same":true,"state_same":true,
                "guard_unique":true,"post_unique":true,"class_rank_same":true}));
        }
        let mut path = None;
        let mut rank = 0;
        for (identity, (class_id, _)) in &classes {
            if path != Some(identity.path_signature) {
                path = Some(identity.path_signature);
                rank = 0;
            }
            assert_eq!(*class_id, rank, "规范守卫向量排序名次与 class_id 不同");
            rank += 1;
        }
        write_json(
            &output.join("reconfirm.json"),
            &json!({"certified":true,"corpus_entries":rows.len(),"entries":rows}),
        );
        let catalog: Vec<_> = classes
            .iter()
            .map(|(identity, (class_id, sample_id))| {
                json!({
                    "scene":scenario,"identity":identity,"path_signature":identity.path_signature,
                    "guard_vector":identity.guard_vector,"class_id":class_id,"corpus_sample_id":sample_id
                })
            })
            .collect();
        write_json(&output.join("seed-map.json"), &catalog);
        Self { classes }
    }
}
