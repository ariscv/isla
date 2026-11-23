//! 分段合并候选与只读诊断；执行前确定，进程内保持不变。
use serde::Deserialize;
use std::path::PathBuf;
use std::sync::OnceLock;

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct RegionOptions {
    pub bv_rewrite: crate::smt::rewrite::BvRewrite,
    /// 区域推演嵌套上限；缺省或-1不限。
    pub max_merge_depth: Option<i64>,
    /// 延后推演时，范围证明转为出口待证义务；默认开启。
    pub defer_range_proofs: bool,
    /// 延后推演时，构造子解包标签转为出口待证义务；默认开启。
    pub defer_ctor_checks: bool,
    /// 跳过分支可行性查询，保留完整候选守卫；默认关闭。
    pub skip_branch_checks: bool,
    /// 跳过可选布尔恒值证明；默认关闭。
    pub skip_bool_proofs: bool,
    /// 不调用 SMT check，仅构造未认证候选；默认关闭。
    pub no_smt: bool,
    /// 无 SMT 模式下只恢复可选布尔恒值证明；默认关闭。
    pub no_smt_keep_bool_proofs: bool,
    /// 延迟区域出口检查；默认关闭。
    pub defer_exit_check: bool,
    /// 嵌套区域遇到 solver_unknown 时，保留外层区域并在其中退化为普通分叉；默认关闭。
    pub partial_commit_solver_unknown: bool,
    /// 分支入口识别布尔恒值；默认开启。
    pub prune_constant_branches: bool,
    pub arm_error_leaf: bool,
    pub arm_error_batch_size: std::num::NonZeroUsize,
    /// 延迟 Z3 条件作用域；默认关闭，仅在 defer 内生效，可能增加内存占用。
    pub lazy_z3_scope: bool,
    /// 完整前提见证求值；默认关闭。
    pub witness_eval: bool,
    /// 见证影子诊断；默认关闭。
    pub witness_shadow: bool,
    /// 局部见证补全影子诊断；默认关闭。
    pub witness_local_shadow: bool,
    /// 迭代边界前缀固化，并压缩已完成轮次的记录和逻辑臂；默认关闭。
    pub prefix_compact: bool,
    pub loop_fold_shapes: bool,
    /// 可选布尔证明资源统计；默认关闭。
    pub bool_proof_profile: bool,
    /// 区域步数和查询进度诊断；默认关闭。
    pub progress: bool,
    /// 原生查询快照；默认关闭。
    pub native_snapshot: bool,
    /// 有界函数调用统计；默认关闭。
    pub call_census: bool,
    /// 逐轮成本分账；默认关闭。
    pub probe_round_cost: bool,
    /// 有界逐查询计时；默认关闭。
    pub probe_query_timings: bool,
    /// 可选布尔证明的资源上限；0 表示不限，不限制路径判定。
    pub bool_proof_rlimit: u32,
    pub query_dump_sites: Vec<String>,
    pub same_context_sites: Vec<String>,
    pub query_dump_dir: Option<PathBuf>,
    pub obligation_dump_dir: Option<PathBuf>,
}

static OPTIONS: OnceLock<RegionOptions> = OnceLock::new();
static DEFAULT_OPTIONS: OnceLock<RegionOptions> = OnceLock::new();

impl Default for RegionOptions {
    fn default() -> Self {
        Self::from_config(&super::ExecutionLimitsConfig::default())
    }
}

impl RegionOptions {
    pub fn merge_depth_limit(&self) -> Option<usize> {
        match self.max_merge_depth {
            None => None,
            Some(-1) => None,
            Some(value) => Some(usize::try_from(value).expect("区域嵌套配置必须已校验")),
        }
    }
    /// 只保留执行前冻结的运行时快照；外部配置不再有 region_options 表。
    pub fn from_config(limits: &super::ExecutionLimitsConfig) -> Self {
        let merge = &limits.path_merge;
        let diagnostics = &merge.diagnostics;
        Self {
            bv_rewrite: limits.solver.bv_rewrite,
            max_merge_depth: merge.max_merge_depth,
            defer_range_proofs: merge.defer_range_proofs,
            defer_ctor_checks: merge.defer_ctor_checks,
            skip_branch_checks: limits.solver.skip_branch_checks,
            skip_bool_proofs: limits.solver.skip_bool_proofs,
            no_smt: limits.solver.no_smt,
            no_smt_keep_bool_proofs: limits.solver.no_smt_keep_bool_proofs,
            defer_exit_check: merge.defer_exit_check,
            partial_commit_solver_unknown: merge.partial_commit_solver_unknown,
            prune_constant_branches: merge.prune_constant_branches,
            arm_error_leaf: merge.arm_error_leaf,
            arm_error_batch_size: merge.solver.arm_error_batch_size,
            lazy_z3_scope: merge.lazy_z3_scope,
            witness_eval: merge.witness_eval,
            prefix_compact: merge.prefix_compact,
            loop_fold_shapes: merge.loop_fold_shapes,
            bool_proof_rlimit: limits.solver.bool_proof_rlimit,
            witness_shadow: diagnostics.witness_shadow,
            witness_local_shadow: diagnostics.witness_local_shadow,
            bool_proof_profile: diagnostics.bool_proof_profile,
            progress: diagnostics.progress,
            native_snapshot: diagnostics.native_snapshot,
            call_census: diagnostics.call_census,
            probe_round_cost: diagnostics.probe_round_cost,
            probe_query_timings: diagnostics.probe_query_timings,
            query_dump_sites: diagnostics.query_dump_sites.clone(),
            same_context_sites: diagnostics.same_context_sites.clone(),
            query_dump_dir: diagnostics.query_dump_dir.clone(),
            obligation_dump_dir: diagnostics.obligation_dump_dir.clone(),
        }
    }

    pub fn validate(&self) -> Result<(), String> {
        if let Some(value) = self.max_merge_depth {
            if value != -1 && (value <= 0 || usize::try_from(value).is_err()) {
                return Err("max_merge_depth 必须为正整数或 -1（不设区域上限）".into());
            }
        }
        if self.no_smt_keep_bool_proofs && (!self.no_smt || self.skip_bool_proofs) {
            return Err("no_smt_keep_bool_proofs 需要 no_smt=true 且 skip_bool_proofs=false".into());
        }
        if self.same_context_sites.len() > 2 {
            return Err("same_context_sites 最多选择两个位置".into());
        }
        for site in self.query_dump_sites.iter().chain(&self.same_context_sites) {
            if site.is_empty() || site.trim() != site {
                return Err("诊断位置必须非空且不含首尾空格".into());
            }
        }
        if !self.query_dump_sites.is_empty() && self.query_dump_dir.is_none() {
            return Err("query_dump_sites 需要 query_dump_dir".into());
        }
        for path in [&self.query_dump_dir, &self.obligation_dump_dir].into_iter().flatten() {
            if path.as_os_str().is_empty() {
                return Err("诊断导出目录不能为空".into());
            }
        }
        Ok(())
    }

    /// 沿用 SMT 配置的进程内冻结约定；重复传入相同值可用，更改配置直接终止。
    pub fn configure(&self) {
        self.validate().expect("区域配置必须在执行前通过校验");
        assert_eq!(OPTIONS.get_or_init(|| self.clone()), self, "不能更改已经初始化的区域配置");
    }

    pub fn current() -> &'static Self {
        OPTIONS.get().unwrap_or_else(|| DEFAULT_OPTIONS.get_or_init(Self::default))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn region_options_defaults_match_configuration() {
        assert_eq!(toml::from_str::<RegionOptions>("").unwrap(), RegionOptions::default());
        assert_eq!(RegionOptions::current(), &RegionOptions::default());
        assert_eq!(RegionOptions::default().bool_proof_rlimit, 0);
    }
}
