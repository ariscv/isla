//! 规则判定由 Python 原实现完成；这里保留三方结果、规则编号和去重维度。
use super::Oracle;
use serde_json::{json, Value};

pub struct ThreeWayOracle;
impl Oracle for ThreeWayOracle {
    fn compare(&self, expected: &Value, observed: &Value) -> Option<Value> {
        if observed["agree"] == true && observed["isla_consistent_side"] == "both" {
            assert_eq!(expected["isla_cause"], observed["xs_cause"]);
            assert_eq!(expected["isla_cause"], observed["nemu_cause"]);
            return None;
        }
        let infrastructure = matches!(
            observed["bucket"].as_str().unwrap(),
            "timeout" | "limit" | "framework-abort" | "other-failure" | "worker-error" | "cancelled"
        );
        let fields = if infrastructure {
            vec!["infrastructure"]
        } else if observed["xs_cause"] != expected["isla_cause"] || observed["nemu_cause"] != expected["isla_cause"] {
            vec!["cause"]
        } else {
            vec![observed["reason"].as_str().unwrap_or("state")]
        };
        let rule_id = match observed["mismatch"]["known_rule"].as_str() {
            None => None,
            Some("xs_leaf_ppn_af_over_permission_pf") => Some("R-XS-001"),
            Some(rule) => panic!("未登记编号的窄规则：{rule}"),
        };
        assert_eq!(observed["mismatch"]["filtered"] == true, rule_id.is_some(), "过滤结果必须对应登记的窄规则");
        Some(
            json!({"fields":fields,"phase":observed["phase"],"rule_id":rule_id,"filtered":rule_id.is_some(),"infrastructure":infrastructure,"isla_cause":expected["isla_cause"],"xs_cause":observed["xs_cause"],"nemu_cause":observed["nemu_cause"],"observation":observed}),
        )
    }
}
