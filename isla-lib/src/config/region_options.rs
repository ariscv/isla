//! 分段合并候选与只读诊断；执行前确定，进程内保持不变。
use serde::Deserialize;
use std::path::PathBuf;
use std::sync::OnceLock;

#[derive(Debug, Clone, Default, PartialEq, Eq, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct RegionOptions {
    /// 延迟区域出口检查；默认关闭。
    pub defer_exit_check: bool,
    /// 延迟 Z3 条件作用域；默认关闭，仅在 defer 内生效，可能增加内存占用。
    pub lazy_z3_scope: bool,
    /// 完整前提见证求值；默认关闭。
    pub witness_eval: bool,
    /// 见证影子诊断；默认关闭。
    pub witness_shadow: bool,
    /// 局部见证补全影子诊断；默认关闭。
    pub witness_local_shadow: bool,
    /// 迭代边界前缀固化；默认关闭。
    pub prefix_compact: bool,
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

impl RegionOptions {
    pub fn validate(&self) -> Result<(), String> {
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
    fn region_options_defaults_preserve_disabled_behavior() {
        assert_eq!(toml::from_str::<RegionOptions>("").unwrap(), RegionOptions::default());
        assert_eq!(RegionOptions::current(), &RegionOptions::default());
        assert_eq!(RegionOptions::default().bool_proof_rlimit, 0);
    }
}
