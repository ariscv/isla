//! 只按字段名配置变异，不依赖指令集。
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Default, Deserialize, Serialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub enum Mode {
    #[default]
    Legacy,
    UniformSubset,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct FieldWeight {
    pub pattern: String,
    pub weight: f64,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(default, deny_unknown_fields)]
pub struct MutationConfig {
    pub mode: Mode,
    pub default_weight: f64,
    pub field_counts: Vec<usize>,
    pub fields: Vec<FieldWeight>,
}

impl Default for MutationConfig {
    fn default() -> Self {
        Self { mode: Mode::Legacy, default_weight: 1.0, field_counts: vec![1, 2, 3], fields: Vec::new() }
    }
}

impl MutationConfig {
    pub fn parse(text: &str) -> Result<Self, String> {
        let config: Self = toml::from_str(text).map_err(|e| format!("变异配置无效：{e}"))?;
        if !config.default_weight.is_finite()
            || config.default_weight < 0.0
            || config.fields.iter().any(|f| f.pattern.is_empty() || !f.weight.is_finite() || f.weight < 0.0)
        {
            return Err("字段模式不得为空，权重必须为有限非负数".into());
        }
        if config.field_counts.is_empty() || config.field_counts.contains(&0) {
            return Err("field_counts 必须为非空正整数数组".into());
        }
        if config.mode == Mode::Legacy
            && (!config.fields.is_empty() || config.default_weight != 1.0 || config.field_counts != [1, 2, 3])
        {
            return Err("legacy 不接受字段权重或数量覆盖；请使用 uniform-subset".into());
        }
        Ok(config)
    }

    pub fn is_legacy(&self) -> bool {
        self.mode == Mode::Legacy
    }

    // 后匹配规则覆盖前规则；零权重明确排除字段。
    fn weight(&self, name: &str) -> f64 {
        self.fields.iter().rev().find(|f| glob(&f.pattern, name)).map_or(self.default_weight, |f| f.weight)
    }

    pub(super) fn select<'a>(
        &self,
        names: impl Iterator<Item = &'a str>,
        random: &mut impl FnMut() -> u64,
    ) -> BTreeSet<String> {
        assert!(!self.is_legacy());
        let mut families = BTreeMap::<String, Vec<(&str, f64)>>::new();
        for name in names {
            let weight = self.weight(name);
            if weight > 0.0 {
                families.entry(family(name)).or_default().push((name, weight));
            }
        }
        let mut families = families.into_values().collect::<Vec<_>>();
        let count = self.field_counts[index(self.field_counts.len(), random)].min(families.len());
        let mut selected = BTreeSet::new();
        for _ in 0..count {
            // 族权重取最大叶权重，避免含32个字段的族自然获得32倍预算。
            let weights = families.iter().map(|f| f.iter().map(|(_, w)| *w).fold(0.0, f64::max)).collect::<Vec<_>>();
            let members = families.remove(weighted(&weights, random));
            let weights = members.iter().map(|(_, w)| *w).collect::<Vec<_>>();
            selected.insert(members[weighted(&weights, random)].0.to_owned());
        }
        selected
    }
}

// 无偏整数下标；固定初值和字段序下可复现。
fn index(length: usize, random: &mut impl FnMut() -> u64) -> usize {
    assert!(length > 0);
    let bound = length as u64;
    let threshold = bound.wrapping_neg() % bound;
    loop {
        let word = random();
        if word >= threshold {
            return (word % bound) as usize;
        }
    }
}

fn weighted(weights: &[f64], random: &mut impl FnMut() -> u64) -> usize {
    let max = weights.iter().copied().fold(0.0, f64::max);
    assert!(max > 0.0);
    // 先缩放，合法的大权重也不会把总和推成无穷。
    let total = weights.iter().map(|w| w / max).sum::<f64>();
    let mut position = (random() >> 11) as f64 * (1.0 / ((1u64 << 53) as f64)) * total;
    for (i, weight) in weights.iter().enumerate() {
        position -= weight / max;
        if position < 0.0 {
            return i;
        }
    }
    weights.len() - 1 // 浮点边界舍入。
}

fn family(name: &str) -> String {
    let mut result = String::new();
    let mut number = false;
    for c in name.chars() {
        if c.is_ascii_digit() {
            if !number {
                result.push('*');
            }
            number = true;
        } else {
            result.push(c);
            number = false;
        }
    }
    result
}

// '*' 为任意串，'?' 为一个字符；其余字符（包括方括号）按字面匹配。
fn glob(pattern: &str, name: &str) -> bool {
    let pattern = pattern.chars().collect::<Vec<_>>();
    let name = name.chars().collect::<Vec<_>>();
    let (mut p, mut n, mut star) = (0, 0, None);
    while n < name.len() {
        if p < pattern.len() && (pattern[p] == '?' || (pattern[p] != '*' && pattern[p] == name[n])) {
            p += 1;
            n += 1;
        } else if p < pattern.len() && pattern[p] == '*' {
            star = Some((p, n));
            p += 1;
        } else if let Some((s, matched)) = star {
            star = Some((s, matched + 1));
            p = s + 1;
            n = matched + 1;
        } else {
            return false;
        }
    }
    while p < pattern.len() && pattern[p] == '*' {
        p += 1;
    }
    p == pattern.len()
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{RngCore, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    #[test]
    fn mutator_config_parsing_rejects_invalid_policies() {
        assert!(MutationConfig::parse("mode = 'legacy'").unwrap().is_legacy());
        assert!(MutationConfig::parse("unknown = 1").is_err());
        for invalid in [
            "mode='unknown'",
            "mode='uniform-subset'\nfield_counts=[]",
            "mode='uniform-subset'\nfield_counts=[0]",
            "mode='uniform-subset'\ndefault_weight=-1.0",
            "mode='uniform-subset'\ndefault_weight=nan",
            "mode='legacy'\n[[fields]]\npattern='pre.flag'\nweight=10.0",
            "mode='uniform-subset'\n[[fields]]\npattern=''\nweight=1.0",
        ] {
            assert!(MutationConfig::parse(invalid).is_err(), "{invalid}");
        }
    }

    #[test]
    fn mutator_globs_and_families_are_generic() {
        assert!(glob("pre.*[?]", "pre.value[3]"));
        assert!(!glob("pre.*[?]", "pre.value[33]"));
        assert!(glob("*", "read.20"));
        assert!(glob("*a", "*bba"));
        assert!(!glob("pre.a", "pre.ab"));
        assert_eq!(family("pre.bank12[3].45"), "pre.bank*[*].*");
    }

    #[test]
    fn mutator_uniform_selects_families_instead_of_overweighting_large_arrays() {
        let config = MutationConfig::parse("mode='uniform-subset'\nfield_counts=[1]").unwrap();
        let mut names = (0..32).map(|i| format!("pre.bank{i}")).collect::<Vec<_>>();
        names.push("pre.flag".into());
        let mut rng = ChaCha8Rng::seed_from_u64(42);
        let mut flag = 0;
        for _ in 0..20000 {
            let selected = config.select(names.iter().map(String::as_str), &mut || rng.next_u64());
            assert_eq!(selected.len(), 1);
            flag += usize::from(selected.contains("pre.flag"));
        }
        assert!((0.48..0.52).contains(&(flag as f64 / 20000.0)));
    }

    #[test]
    fn mutator_weights_and_zero_exclusion_follow_fixed_seed_distribution() {
        let config = MutationConfig::parse("mode='uniform-subset'\nfield_counts=[1]\ndefault_weight=0.0\n[[fields]]\npattern='pre.*'\nweight=1.0\n[[fields]]\npattern='pre.flag'\nweight=9.0").unwrap();
        let mut rng = ChaCha8Rng::seed_from_u64(314159);
        let mut flag = 0;
        for _ in 0..20000 {
            let selected = config.select(["pre.value", "pre.flag", "read.1"].into_iter(), &mut || rng.next_u64());
            assert_eq!(selected.len(), 1);
            assert!(!selected.contains("read.1"));
            flag += usize::from(selected.contains("pre.flag"));
        }
        assert!((0.88..0.92).contains(&(flag as f64 / 20000.0)));
    }

    #[test]
    fn mutator_count_distribution_and_replay_are_deterministic() {
        let config = MutationConfig::parse("mode='uniform-subset'\nfield_counts=[1,2,2]").unwrap();
        let run = || {
            let mut rng = ChaCha8Rng::seed_from_u64(5);
            (0..12000).map(|_| config.select(["a", "b", "c"].into_iter(), &mut || rng.next_u64())).collect::<Vec<_>>()
        };
        let selected = run();
        assert_eq!(selected, run());
        let ones = selected.iter().filter(|s| s.len() == 1).count();
        assert!((0.31..0.35).contains(&(ones as f64 / selected.len() as f64)));
    }
}
