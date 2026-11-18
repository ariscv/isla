//! 保留最后一个完整清零后PERF向量；同名项按出现次序编号。
use regex::Regex;
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;

pub(super) fn parse(text: &str) -> BTreeMap<String, u64> {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    let pattern =
        PATTERN.get_or_init(|| Regex::new(r"(?m)\[PERF \]\[time=\s*(\d+)\]\s*(.*?):\s*(.*?),\s*(\d+)\s*$").unwrap());
    let mut dumps = BTreeMap::<u64, BTreeMap<String, u64>>::new();
    let mut occurrences = BTreeMap::new();
    for capture in pattern.captures_iter(text) {
        let stamp = capture[1].parse::<u64>().unwrap();
        let base = format!("{}: {}", capture[2].trim(), capture[3].trim());
        let count = occurrences.entry((stamp, base.clone())).or_insert(0usize);
        *count += 1;
        dumps.entry(stamp).or_default().insert(format!("{base} #{count}"), capture[4].parse().unwrap());
    }
    assert!(dumps.len() >= 2, "缺少预热及最终PERF dump");
    let expected = dumps.first_key_value().unwrap().1.len();
    let result = dumps.pop_last().unwrap().1;
    assert_eq!(result.len(), expected, "最终PERF dump不完整");
    result
}

pub(super) fn signature(perf: &BTreeMap<String, u64>, selected: &[String]) -> String {
    selected
        .iter()
        .map(|name| char::from(b'0' + (*perf.get(name).unwrap_or_else(|| panic!("缺少计数器 {name}"))).min(2) as u8))
        .collect()
}

#[derive(Default, Clone)]
pub(super) struct Coverage {
    pub signatures: BTreeSet<String>,
    pub bins: BTreeSet<(String, u8)>,
}
impl Coverage {
    pub fn observe(&mut self, perf: &BTreeMap<String, u64>, selected: &[String]) -> bool {
        let signature = signature(perf, selected);
        for (name, bin) in selected.iter().zip(signature.bytes()) {
            self.bins.insert((name.clone(), bin - b'0'));
        }
        self.signatures.insert(signature)
    }
    pub fn summary(&self) -> Value {
        json!({"signatures":self.signatures.len(),"signal_bins":self.bins.len()})
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn final_dump_and_duplicate_names_are_preserved() {
        let text = "[PERF ][time= 10] mod: pulse, 99\n[PERF ][time= 10] mod: pulse, 3\n[PERF ][time= 20] mod: pulse, 0\n[PERF ][time= 20] mod: pulse, 2\n";
        let result = parse(text);
        assert_eq!(signature(&result, &["mod: pulse #1".into(), "mod: pulse #2".into()]), "02");
        let mut coverage = Coverage::default();
        let selected = vec!["mod: pulse #1".into(), "mod: pulse #2".into()];
        assert!(coverage.observe(&result, &selected));
        assert!(!coverage.observe(&result, &selected));
        assert_eq!(coverage.bins.len(), 2);
    }
}
