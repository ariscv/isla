//! 使用确定性时长检查归属，避免依赖机器负载。
use super::merge_timing::*;
use serde_json::json;
use std::time::Duration;

fn sample(wall: u64, smt: u64, queries: u64) -> Measure {
    Measure { wall: Duration::from_millis(wall), smt: Duration::from_millis(smt), queries, ..Measure::default() }
}

#[test]
fn merge_timing_nested_costs_partition_without_double_counting() {
    let mut counts = Counts::default();
    let origin = json!({"function":"choose","pc":3});
    let child = Measure { model: Duration::from_millis(2), model_calls: 3, ..sample(40, 20, 2) };
    let parent = Measure { model: Duration::from_millis(5), model_calls: 7, ..sample(100, 50, 5) };
    counts.begin();
    counts.finish(&origin, "success", child, child, false);
    counts.begin();
    counts.finish(&origin, "SpeculativeRejectReason::StepBudget", parent, parent.subtract(child), true);
    let rows = counts.rows();
    let success = rows.iter().find(|r| r["outcome"] == "success").unwrap();
    let reject = rows.iter().find(|r| r["outcome"] == "SpeculativeRejectReason::StepBudget").unwrap();
    assert_eq!(success["exclusive"]["wall_seconds"]["sum"], 0.04);
    assert_eq!(reject["exclusive"]["wall_seconds"]["sum"], 0.06);
    assert_eq!(reject["inclusive"]["queries"]["sum"], 5);
    assert_eq!(reject["exclusive"]["queries"]["sum"], 3);
    assert_eq!(reject["root"]["wall_seconds"]["sum"], 0.1);
    assert_eq!(success["root"]["count"], 0);
    assert_eq!(reject["exclusive"]["model_seconds"]["sum"], 0.003);
    assert_eq!(reject["exclusive"]["model_calls"]["sum"], 4);
}

#[test]
fn merge_timing_totals_means_maxima_and_bounded_locations() {
    let mut counts = Counts::default();
    for n in [10, 30] {
        let m = sample(n, n / 2, 2);
        counts.begin();
        counts.finish(&json!({"function":"choose","pc":3}), "success", m, m, true);
    }
    let rows = counts.rows();
    let row = &rows[0];
    assert_eq!(row["inclusive"]["count"], 2);
    assert_eq!(row["inclusive"]["wall_seconds"], json!({"sum":0.04,"mean":0.02,"max":0.03}));
    for pc in 0..4200 {
        let m = sample(1, 0, 0);
        counts.begin();
        counts.finish(&json!({"function":"choose","pc":pc}), "success", m, m, true);
    }
    let sites = counts.site_rows();
    assert!(sites.len() <= 4096);
    let summary = counts.summary();
    assert!(summary["other_sites"]["inclusive"]["count"].as_u64().unwrap() > 0);
    assert_eq!(counts.rows()[0]["inclusive"]["count"], 4202);
}
