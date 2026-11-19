//! 路径合并的全局参数、局部规则与只读诊断。
use serde::{Deserialize, Deserializer};
use std::path::PathBuf;
use toml::Value;

use super::{
    allowed_table_keys, parse_merge_enumeration, parse_region_step_budget, required_u32, sample_bias,
    source_region_spec, validate_merge_policy_conflicts, zencode, BranchRegionLimitConfig, MergeEnumerationConfig,
    MergeMode, MergePolicyConfig, MergePolicySelectorConfig, RegionForkLimitConfig,
};
use crate::source_loc::SourceRegionSpec;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum SolverOnUnknown {
    #[default]
    Dead,
    Error,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct SolverConfig {
    pub on_unknown: SolverOnUnknown,
    /// 通用等价改写。缺省启用全部规则，可显式关闭或指定规则。
    pub bv_rewrite: crate::smt::rewrite::BvRewrite,
    /// 跳过分支可行性查询，保留完整候选守卫；默认关闭。
    pub skip_branch_checks: bool,
    /// 跳过可选布尔恒值证明；默认关闭。
    pub skip_bool_proofs: bool,
    /// 不调用 SMT check，仅构造未认证候选；默认关闭。
    pub no_smt: bool,
    /// 无 SMT 模式下只恢复可选布尔恒值证明；默认关闭。
    pub no_smt_keep_bool_proofs: bool,
    /// 0 表示不限，不限制路径判定。
    pub bool_proof_rlimit: u32,
    /// isarch 终值重解的单次时限（毫秒）。省略时沿用已有时限。
    pub model_timeout_ms: Option<std::num::NonZeroU64>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct PathMergeDiagnostics {
    pub witness_shadow: bool,
    pub witness_local_shadow: bool,
    pub bool_proof_profile: bool,
    pub progress: bool,
    pub native_snapshot: bool,
    pub call_census: bool,
    pub probe_round_cost: bool,
    pub probe_query_timings: bool,
    pub query_dump_sites: Vec<String>,
    pub same_context_sites: Vec<String>,
    pub query_dump_dir: Option<PathBuf>,
    pub obligation_dump_dir: Option<PathBuf>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct PathMergeConfig {
    pub strategy: Option<super::MergeStrategy>,
    /// 两种组织者共用。true 要求访问偏序，缺省 false。
    pub ordered_events: Option<bool>,
    /// 省略时沿用入口缺省值。完整符号 DAG 缺省开启。
    pub enabled: Option<bool>,
    /// 区域推演嵌套上限；缺省或-1不限。
    pub max_merge_depth: Option<i64>,
    /// 区域因局部汇合失败可保留的片段上限；缺省或 -1 不限。
    pub max_fragments: Option<i64>,
    /// 范围证明转为出口待证义务；默认关闭。
    pub defer_range_proofs: bool,
    /// 构造子解包标签转为出口待证义务；默认关闭。
    pub defer_ctor_checks: bool,
    /// 只消除已证明不可观察的未初始化槽位；默认关闭。
    pub merge_poison_slots: bool,
    /// None 沿用运行时关闭（-1）；-1关闭；其余合法值为正数。
    pub step_budget: Option<i64>,
    pub defer_exit_check: bool,
    /// 分支入口只用表达式结构识别布尔恒值；默认关闭。
    pub prune_constant_branches: bool,
    pub arm_error_leaf: bool,
    /// 用守卫保留不同的具体字符串和机器整数，缺省开启。
    pub merge_concrete_values: bool,
    /// 在实际到达指令时检查普通被调函数的传递效应。
    pub defer_call_effect_checks: bool,
    /// 仅在延迟出口检查内生效。
    pub lazy_z3_scope: bool,
    pub finite_domain_enumeration: bool,
    pub witness_eval: bool,
    pub prefix_compact: bool,
    pub diagnostics: PathMergeDiagnostics,
    pub regions: Option<Vec<PathMergeRegionConfig>>,
    #[serde(deserialize_with = "deserialize_enumeration")]
    pub enumeration: Option<MergeEnumerationConfig>,
}

impl Default for PathMergeConfig {
    fn default() -> Self {
        Self {
            strategy: None,
            ordered_events: None,
            enabled: None,
            max_merge_depth: None,
            max_fragments: None,
            defer_range_proofs: false,
            defer_ctor_checks: false,
            merge_poison_slots: false,
            step_budget: None,
            defer_exit_check: false,
            prune_constant_branches: false,
            arm_error_leaf: false,
            merge_concrete_values: true,
            defer_call_effect_checks: false,
            lazy_z3_scope: false,
            finite_domain_enumeration: false,
            witness_eval: false,
            prefix_compact: false,
            diagnostics: PathMergeDiagnostics::default(),
            regions: None,
            enumeration: None,
        }
    }
}

impl PathMergeConfig {
    pub fn policies(&self) -> Vec<MergePolicyConfig> {
        self.regions
            .iter()
            .flatten()
            .filter_map(|rule| match rule {
                PathMergeRegionConfig::MergePolicy(rule) => Some(rule.clone()),
                _ => None,
            })
            .collect()
    }

    pub fn fragment_limit(&self) -> Result<Option<usize>, String> {
        match self.max_fragments {
            None | Some(-1) => Ok(None),
            Some(value) if value > 0 => usize::try_from(value)
                .map(Some)
                .map_err(|_| "execution_limits.path_merge.max_fragments 超出 usize 范围".into()),
            _ => Err("execution_limits.path_merge.max_fragments 必须为正整数或 -1（不限）".into()),
        }
    }

    pub fn validate(&self) -> Result<(), String> {
        self.fragment_limit()?;
        if let Some(value) = self.step_budget {
            parse_region_step_budget(value)?;
        }
        if self.regions.as_ref().is_some_and(Vec::is_empty) {
            return Err("execution_limits.path_merge.regions 不能为空".into());
        }
        validate_merge_policy_conflicts(&self.policies())
    }
}

/// 显式 kind 保留四种旧规则的独立语义；不由缺失字段猜测类别。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathMergeRegionConfig {
    LimitFilter(SourceRegionSpec),
    BranchLimit(BranchRegionLimitConfig),
    ForkLimit(RegionForkLimitConfig),
    MergePolicy(MergePolicyConfig),
}

impl<'de> Deserialize<'de> for PathMergeRegionConfig {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = Value::deserialize(deserializer)?;
        parse_region(&value).map_err(serde::de::Error::custom)
    }
}

fn parse_region(value: &Value) -> Result<PathMergeRegionConfig, String> {
    let root = "execution_limits.path_merge.regions";
    let table = value.as_table().ok_or_else(|| format!("{root} 项必须是 TOML table"))?;
    let coordinates = ["file", "start_line", "start_column", "end_line", "end_column"];
    let mut allowed = vec!["kind"];
    let kind = table.get("kind").and_then(Value::as_str).ok_or_else(|| format!("{root}.kind 是必填字符串"))?;
    allowed.extend(coordinates);
    match kind {
        "limit_filter" => {}
        "branch_limit" => allowed.push("max_forks_per_branch"),
        "fork_limit" => allowed.extend(["max_forks_per_region", "sample_bias", "sample_bias_direction"]),
        "merge_policy" => allowed.extend(["mode", "function"]),
        _ => return Err(format!("{root}.kind 必须是 limit_filter、branch_limit、fork_limit 或 merge_policy")),
    }
    allowed_table_keys(table, root, &allowed)?;
    Ok(match kind {
        "limit_filter" => PathMergeRegionConfig::LimitFilter(source_region_spec(table, root)?),
        "branch_limit" => PathMergeRegionConfig::BranchLimit(BranchRegionLimitConfig {
            max_forks_per_branch: required_u32(table, "max_forks_per_branch", root)?,
            region: source_region_spec(table, root)?,
        }),
        "fork_limit" => PathMergeRegionConfig::ForkLimit(RegionForkLimitConfig {
            max_forks_per_region: required_u32(table, "max_forks_per_region", root)?,
            sample_bias: sample_bias(table, root)?,
            region: source_region_spec(table, root)?,
        }),
        "merge_policy" => {
            let mode = match table.get("mode").and_then(Value::as_str) {
                Some("force") => MergeMode::Force,
                Some("adaptive") => MergeMode::Adaptive,
                Some("off") => MergeMode::Off,
                _ => return Err(format!("{root}.mode 必须是 force、adaptive 或 off")),
            };
            let selector = if let Some(function) = table.get("function") {
                if coordinates.iter().any(|key| table.contains_key(*key)) {
                    return Err(format!("{root} 的 function 与源码区域必须二选一"));
                }
                let function = function
                    .as_str()
                    .filter(|name| !name.is_empty())
                    .ok_or_else(|| format!("{root}.function 必须是非空字符串"))?;
                MergePolicySelectorConfig::Function(zencode::encode(function))
            } else {
                MergePolicySelectorConfig::Region(source_region_spec(table, root)?)
            };
            PathMergeRegionConfig::MergePolicy(MergePolicyConfig { mode, selector })
        }
        _ => unreachable!("kind 已校验"),
    })
}

fn deserialize_enumeration<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Option<MergeEnumerationConfig>, D::Error> {
    let value = Value::deserialize(deserializer)?;
    let mut table = toml::value::Table::new();
    table.insert("enumeration".into(), value);
    parse_merge_enumeration(&table).map_err(serde::de::Error::custom)
}
