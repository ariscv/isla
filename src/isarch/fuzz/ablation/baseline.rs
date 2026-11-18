//! 初始 corpus 的共同硬件观察，作为所有臂的第0例起点。
use super::{mismatch_feature, observe, perf};
use serde::Serialize;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Serialize)]
pub(super) struct Observation {
    pub perf: BTreeMap<String, u64>,
    pub fixed: Value,
    pub baseline: Value,
    pub known_replay: Option<Value>,
    pub fixed_replay: Option<Value>,
}

pub(super) struct State {
    pub feedback: perf::Coverage,
    pub heldout: perf::Coverage,
    pub mismatches: BTreeSet<String>,
    pub known_first: Option<usize>,
}

impl State {
    pub fn new(rows: &[Observation], selected: &[String], holdout: &[String]) -> Self {
        let mut state = Self {
            feedback: perf::Coverage::default(),
            heldout: perf::Coverage::default(),
            mismatches: BTreeSet::new(),
            known_first: None,
        };
        for row in rows {
            if !row.perf.is_empty() {
                state.feedback.observe(&row.perf, selected);
                state.heldout.observe(&row.perf, holdout);
            }
            if let Some(key) = mismatch_feature(&row.fixed) {
                state.mismatches.insert(key);
            }
            if row.fixed["agree"] == true
                && row.baseline["mismatch"]["known_rule"] == observe::KNOWN_RULE
                && row
                    .known_replay
                    .as_ref()
                    .is_some_and(|replay| replay["mismatch"]["known_rule"] == observe::KNOWN_RULE)
            {
                state.known_first = Some(0);
            }
        }
        state
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn initial_corpus_is_case_zero_and_requires_confirmed_known_bug() {
        let rows = vec![
            Observation {
                perf: BTreeMap::from([("feedback".into(), 1), ("heldout".into(), 2)]),
                fixed: json!({"agree":true}),
                baseline: json!({"mismatch":{"known_rule":observe::KNOWN_RULE}}),
                known_replay: None,
                fixed_replay: None,
            },
            Observation {
                perf: BTreeMap::new(),
                fixed: json!({"agree":false,"bucket":"xs!=expected","reason":"test","isla_consistent_side":"nemu"}),
                baseline: Value::Null,
                known_replay: None,
                fixed_replay: None,
            },
        ];
        let mut rows = rows;
        let state = State::new(&rows, &["feedback".into()], &["heldout".into()]);
        assert_eq!(state.known_first, None, "观察到一次还不能算独立确认");
        assert_eq!(state.mismatches.len(), 1);
        assert_eq!(state.heldout.signatures, BTreeSet::from(["2".into()]));
        assert_eq!(state.feedback.signatures, BTreeSet::from(["1".into()]));
        rows[0].known_replay = Some(json!({"mismatch":{"known_rule":observe::KNOWN_RULE}}));
        assert_eq!(State::new(&rows, &["feedback".into()], &["heldout".into()]).known_first, Some(0));
        rows[0].fixed["agree"] = json!(false);
        assert_eq!(State::new(&rows, &["feedback".into()], &["heldout".into()]).known_first, None);
    }
}
