//! 通用探索快照。JSON 与 bincode 共用同一镜像，损坏即终止。
pub mod event;
pub mod expr;
mod names;
pub mod value;
pub use names::NameEnvironment;

use std::collections::HashSet;
use std::sync::{Mutex, OnceLock};

/// 同一个区域名只分配一次；查询、分配和插入持有同一把锁。
fn intern_region(name: String) -> &'static str {
    static REGIONS: OnceLock<Mutex<HashSet<&'static str>>> = OnceLock::new();
    let mut regions = REGIONS.get_or_init(|| Mutex::new(HashSet::new())).lock().unwrap();
    if let Some(found) = regions.get(name.as_str()) {
        return found;
    }
    let name = Box::leak(name.into_boxed_str());
    regions.insert(name);
    name
}

mod trace;
pub use trace::{CheckpointData, Segment, TraceReader, TraceWriter};
mod path;
pub use path::{Arm, CachedPath, Facts, GuardedRead, PathData, Record};
mod validate;
pub use validate::validate_paths;
