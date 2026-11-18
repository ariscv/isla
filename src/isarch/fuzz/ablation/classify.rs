//! 与历史重放器一致的日志分类，保留出口和基础设施失败的优先级；同一构建产物直接用于两版emu。
use regex::Regex;
use serde_json::{json, Value};
use std::collections::BTreeMap;

pub(super) fn classify_log(log: &str, returncode: Option<i64>, symbols: &BTreeMap<String, u64>) -> Value {
    let ansi = Regex::new(r"\x1b\[[0-9;]*m").unwrap();
    let text = ansi.replace_all(log, "");
    let l2 = Regex::new(r"L2TLB resp test[^\n]*failed").unwrap().is_match(&text);
    let hits = Regex::new(r"HIT (?:GOOD|BAD) TRAP").unwrap();
    let hit_count = hits.find_iter(&text).count();
    let good = text.contains("HIT GOOD TRAP");
    let bad = text.contains("HIT BAD TRAP");
    let trap = Regex::new(r"HIT (?:GOOD|BAD) TRAP at pc\s*=\s*(0x[0-9a-fA-F]+)").unwrap();
    let pc = trap.captures(&text).map(|capture| u64::from_str_radix(&capture[1][2..], 16).unwrap());
    let names: Vec<_> =
        symbols.iter().filter(|(_, address)| Some(**address) == pc).map(|(name, _)| name.as_str()).collect();
    let symbol = if names.len() == 1 { Some(names[0]) } else { None };
    let reason = symbol
        .and_then(|name| name.strip_prefix("fail_"))
        .and_then(|name| name.strip_suffix("_trap"))
        .filter(|name| !name.is_empty());
    let false_good = good && reason.is_some();
    let limit = Regex::new(r"EXCEEDING (?:CYCLE|INSTR|CYCLE/INSTR) LIMIT").unwrap().is_match(&text);
    let abort = text.contains("ABORT");
    let agree = returncode == Some(0)
        && hit_count == 1
        && good
        && !bad
        && pc.is_some()
        && pc == symbols.get("good_trap_ins").copied()
        && symbol == Some("good_trap_ins")
        && !l2
        && !abort
        && !limit;
    let bucket = if returncode.is_none() {
        "timeout"
    } else if limit {
        "limit"
    } else if hit_count == 1 && reason.is_some() {
        "xs!=expected"
    } else if l2 {
        "framework-abort"
    } else if abort {
        "xs!=nemu"
    } else if agree {
        "agree"
    } else {
        "other-failure"
    };
    json!({"agree":agree,"bucket":bucket,"good_trap":good,"bad_trap":bad,
        "abort":abort,"trap_pc":pc,"trap_symbol":symbol,"bad_pc":if bad {pc} else {None},
        "bad_symbol":if bad {symbol} else {None},"false_good":false_good,"l2tlb_failed":l2,
        "reason":reason,"hit_count":hit_count,"limit":limit})
}
