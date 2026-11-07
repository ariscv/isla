//! itrace、ftrace、btrace 为平级工具，共用路径状态、配置及 writer。
use std::path::PathBuf;

/// 共用一个输出文件，三种轨迹可以独立选择或组合。
#[derive(Clone, Default)]
pub struct TraceOptions {
    pub output: Option<PathBuf>,
    pub instructions: bool,
    pub functions: bool,
    pub branches: bool,
}

#[cfg(feature = "tracetool")]
pub mod btrace;
#[cfg(feature = "tracetool")]
mod common;
#[cfg(feature = "tracetool")]
pub mod ftrace;
#[cfg(feature = "tracetool")]
pub mod itrace;
#[cfg(feature = "tracetool")]
mod sequence;
#[cfg(feature = "tracetool")]
mod writer;
#[cfg(feature = "tracetool")]
pub use common::TraceHandler;
#[cfg(feature = "tracetool")]
pub(crate) use common::{TraceCompletedPath, TracePerPath};

#[cfg(all(test, feature = "tracetool"))]
mod hierarchy_regression {
    use super::{TraceCompletedPath, TraceHandler, TracePerPath};

    #[test]
    fn shared_path_and_handler_belong_to_tracetool() {
        let handler = TraceHandler::default();
        handler.set_traces(false, true, true);
        assert!(handler.ftrace_enabled());
        assert!(handler.btrace_enabled());
        let completed = TraceCompletedPath::without_diagnostics(TracePerPath::default());
        handler.submit_completed_path(&completed, &crate::ir::Symtab::new());
    }
}
