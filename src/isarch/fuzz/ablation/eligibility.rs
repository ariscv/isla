//! 硬件可执行域只在这里判定；原缓存和原样本不改变。
use super::super::testcase::{self, Generated, Platform};
use isla_lib::executor::samples::Sample;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

#[derive(Debug, Serialize, Deserialize)]
pub(super) struct Exclusion {
    pub reasons: BTreeSet<String>,
    pub detail: Option<String>,
}

fn value(sample: &Sample, name: &str, wrapped: bool) -> u64 {
    let field = &sample.pre_registers[name];
    let field = if wrapped { &field["struct"]["bits"] } else { field };
    u64::from_str_radix(field["bits"].as_str().expect("前态必须是具体64位位串"), 2).unwrap()
}

pub(super) fn precheck(sample: &Sample) -> Result<(), Exclusion> {
    let mut reasons = BTreeSet::new();
    if sample.result["ctor"].as_str().is_some_and(|name| name.starts_with("Error_"))
        || !matches!(sample.terminal, isla_lib::executor::samples::Terminal::Normal)
    {
        reasons.insert("sail_internal_error".into());
    }
    let mode = value(sample, "satp", false) >> 60;
    if !matches!(mode, 8 | 9) {
        reasons.insert(
            match mode {
                0 => "satp_bare",
                10 => "satp_sv57",
                _ => "satp_unsupported",
            }
            .into(),
        );
    }
    match sample.pre_registers["cur_privilege"]["enum"].as_str().expect("缺少特权级") {
        "User" | "Supervisor" => (),
        "Machine" => {
            reasons.insert("machine_privilege".into());
        }
        "VirtualUser" | "VirtualSupervisor" => {
            reasons.insert("virtual_privilege".into());
        }
        privilege => panic!("未知模型特权级 {privilege}"),
    }
    let status = value(sample, "mstatus", true);
    if status & (1 << 17) != 0 {
        reasons.insert("mprv_nonzero".into());
    }
    if status & (1u64 << 42) != 0 {
        reasons.insert("trap_observer_double_trap".into());
    }
    if value(sample, "menvcfg", true) != 0 {
        reasons.insert("menvcfg_nonzero".into());
    }
    let fields = sample.pre_registers["$instruction"]["value"]["struct"].as_object().unwrap();
    let is_load = sample.pre_registers["$instruction"]["ctor"] == "LOAD";
    let suffix = if is_load { "4" } else { "3" };
    let width = fields.iter().find(|(name, _)| name.ends_with(suffix)).unwrap().1;
    let width = if let Some(width) = width["i64"].as_str() {
        width.parse::<u64>().unwrap()
    } else {
        u64::from_str_radix(width["bits"].as_str().unwrap(), 2).unwrap()
    };
    if !matches!(width, 1 | 2 | 4 | 8) {
        reasons.insert("nonencoding_width".into());
    } else {
        let field = |suffix: &str| fields.iter().find(|(name, _)| name.ends_with(suffix)).unwrap().1;
        let register =
            u64::from_str_radix(field(if is_load { "1" } else { "2" })["bits"].as_str().unwrap(), 2).unwrap();
        let immediate = u64::from_str_radix(field("0")["bits"].as_str().unwrap(), 2).unwrap();
        let offset = ((immediate as i64) << 52) >> 52;
        let base = if register == 0 { 0 } else { value(sample, &format!("x{register}"), false) };
        if base.wrapping_add(offset as u64) & (width - 1) != 0 {
            // 本阶段保持Sail非对齐关闭；不把未对齐的平台行为差异记为DUT分歧。
            reasons.insert("misaligned_phase_two".into());
        }
    }
    if is_load && width == 8 && fields.iter().find(|(name, _)| name.ends_with('3')).unwrap().1["bool"] == true {
        reasons.insert("nonencoding_unsigned_doubleword".into());
    }
    if !reasons.is_empty() {
        return Err(Exclusion { reasons, detail: None });
    }
    Ok(())
}

pub(super) fn check(sample: &Sample, platform: &Platform) -> Result<Generated, Exclusion> {
    precheck(sample)?;
    testcase::generate(sample, platform, testcase::EntryMode::Mprv).map_err(|detail| {
        let reason = match detail.as_str() {
            "要求空 TLB" => "nonempty_tlb",
            "前后内存地址集合必须一致且全部位于可重放 DRAM，后态必须已知" => {
                "memory_not_replayable_dram"
            }
            _ if detail.starts_with("缺少已知的内存字节") => "missing_replay_bytes",
            _ => "testcase_unsupported",
        };
        Exclusion { reasons: [reason.into()].into_iter().collect(), detail: Some(detail) }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn candidate() -> Sample {
        let mut sample = crate::isarch::fuzz::tests::example_sample();
        let bits = |v: u64| json!({"bits":format!("{v:064b}")});
        sample.pre_registers.insert("satp".into(), bits(8 << 60));
        sample.pre_registers.insert("mstatus".into(), json!({"struct":{"bits":bits(0)}}));
        sample.pre_registers.insert("menvcfg".into(), json!({"struct":{"bits":bits(0)}}));
        sample.pre_registers.insert("cur_privilege".into(), json!({"enum":"User"}));
        sample.pre_registers.insert("x1".into(), bits(0));
        sample.pre_registers.insert(
            "$instruction".into(),
            json!({"ctor":"LOAD","value":{"struct":{
                "tuple#%bv12_%bv5_%bv5_%bool_%i640":{"bits":"000000000000"},
                "tuple#%bv12_%bv5_%bv5_%bool_%i641":{"bits":"00001"},
                "tuple#%bv12_%bv5_%bv5_%bool_%i642":{"bits":"00010"},
                "tuple#%bv12_%bv5_%bv5_%bool_%i643":{"bool":false},
                "tuple#%bv12_%bv5_%bv5_%bool_%i644":bits(1)
            }}}),
        );
        sample
    }

    #[test]
    fn every_exclusion_reason_is_retained_without_changing_the_sample() {
        let mut sample = candidate();
        assert!(precheck(&sample).is_ok());
        sample.pre_registers.insert("satp".into(), json!({"bits":format!("{:064b}",10u64<<60)}));
        sample.pre_registers.insert("mstatus".into(), json!({"struct":{"bits":{"bits":format!("{:064b}",1u64<<17)}}}));
        let before = serde_json::to_value(&sample).unwrap();
        let excluded = precheck(&sample).unwrap_err();
        assert!(excluded.reasons.contains("satp_sv57"));
        assert!(excluded.reasons.contains("mprv_nonzero"));
        assert_eq!(serde_json::to_value(&sample).unwrap(), before);
    }

    #[test]
    fn model_internal_errors_and_nonencoding_widths_never_reach_hardware() {
        let mut sample = candidate();
        sample.result = json!({"ctor":"Error_internal_error","value":{"string":"Hypervisor extension not supported"}});
        sample.pre_registers.get_mut("$instruction").unwrap()["value"]["struct"]["tuple#%bv12_%bv5_%bv5_%bool_%i644"] =
            json!({"bits":"0".repeat(64)});
        let excluded = precheck(&sample).unwrap_err();
        assert!(excluded.reasons.contains("sail_internal_error"));
        assert!(excluded.reasons.contains("nonencoding_width"));
    }

    #[test]
    fn ablation_double_trap_cannot_use_machine_trap_observer() {
        let mut sample = candidate();
        sample.pre_registers.insert("mstatus".into(), json!({"struct":{"bits":{"bits":format!("{:064b}",1u64<<42)}}}));
        let before = serde_json::to_value(&sample).unwrap();
        assert!(precheck(&sample).unwrap_err().reasons.contains("trap_observer_double_trap"));
        assert_eq!(serde_json::to_value(&sample).unwrap(), before);
    }

    #[test]
    fn misaligned_inputs_are_explicitly_reserved_for_phase_two() {
        let mut sample = candidate();
        sample.pre_registers.insert("x1".into(), json!({"bits":format!("{:064b}",3u64)}));
        sample.pre_registers.get_mut("$instruction").unwrap()["value"]["struct"]["tuple#%bv12_%bv5_%bv5_%bool_%i644"] =
            json!({"bits":format!("{:064b}",4u64)});
        assert!(precheck(&sample).unwrap_err().reasons.contains("misaligned_phase_two"));
    }
}
