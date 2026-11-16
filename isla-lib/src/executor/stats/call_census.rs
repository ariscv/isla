//! 有界、只读的调用重复性诊断；不参与摘要复用或执行决策。
use crate::bitvector::BV;
use crate::ir::{Name, Symtab, Val};
use serde_json::json;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::OnceLock;

pub(crate) fn enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("ISLA_CALL_CENSUS").as_deref() == Ok("1"))
}
fn emit(value: serde_json::Value) {
    static ROWS: AtomicUsize = AtomicUsize::new(0);
    let row = ROWS.fetch_add(1, Ordering::Relaxed);
    if row < 100_000 {
        eprintln!("{value}");
    } else if row == 100_000 {
        eprintln!("{}", json!({"kind":"call_census_truncated","limit":100_000}));
    }
}
pub(crate) fn enter<B: BV>(id: usize, parent: usize, task: usize, f: Name, args: &[Val<B>], symtab: &Symtab) {
    if enabled() {
        emit(json!({"kind":"call_census_enter","call_instance":id,"parent_instance":parent,
            "task":task,"function":crate::zencode::decode(symtab.to_str(f)),"args":format!("{args:?}")}));
    }
}
pub(crate) fn read<B: BV>(id: usize, reg: Name, value: &Val<B>, symtab: &Symtab) {
    if enabled() {
        emit(json!({"kind":"call_census_read","call_instance":id,
            "register":crate::zencode::decode(symtab.to_str(reg)),"value":format!("{value:?}")}));
    }
}
pub(crate) fn returned(id: usize) {
    if enabled() {
        emit(json!({"kind":"call_census_return","call_instance":id}));
    }
}
