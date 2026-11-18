//! 只控制导出选路和预算；不向缓存或求解器添加前态条件。
use isla_lib::executor::ExecutionLimits;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(default, deny_unknown_fields)]
pub(super) struct Sampling {
    pub path_stride: usize,
    pub path_offset: usize,
    pub exclude_model_errors: bool,
}
impl Default for Sampling {
    fn default() -> Self {
        Self { path_stride: 1, path_offset: 0, exclude_model_errors: false }
    }
}
impl Sampling {
    pub fn selected(&self, index: usize) -> bool {
        assert!(self.path_stride > 0 && self.path_offset < self.path_stride, "路径抽样参数越界");
        index % self.path_stride == self.path_offset
    }
}
pub(super) fn limits(source: &ExecutionLimits) -> ExecutionLimits {
    let mut limits = source.clone();
    limits.merge_enumeration.enabled = true;
    limits.merge_enumeration.mode = isla_lib::config::MergeEnumerationMode::Samples;
    limits.merge_enumeration.class_cap = 1;
    // 路径间并行；保留调用方的每路径上限和输出步长。
    limits.merge_enumeration.enumeration_threads = 1;
    limits.merge_enumeration.max_output_bytes = None;
    limits
}
