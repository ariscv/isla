//! 独立 NEMU 观察、三方判定和精确输入分组；仅恢复窄规则需要的页表信息。
use super::super::testcase::{Access, Generated, Platform};
use crate::isarch::target::RiscvPte;
use isla_lib::executor::samples::Sample;
use regex::Regex;
use serde_json::{json, Value};
use std::collections::BTreeMap;

pub(super) const KNOWN_RULE: &str = "xs_leaf_ppn_af_over_permission_pf";

pub(super) fn known_mismatch_rules() -> Vec<Value> {
    vec![
        json!({"rule":KNOWN_RULE,"reason":"已上报的 XiangShan 真发现：规范按遍历顺序应报 PF；XiangShan TLB.scala 的 !af 掩码使第 6-9 步的权限/A/D PF 让位于叶 PPN 溢出 AF，已上报。"}),
    ]
}

fn mismatch_key(generated: &Generated, observation: &Value) -> Value {
    let levels = match generated.satp >> 60 {
        8 => 3,
        9 => 4,
        _ => panic!("不支持的分页模式"),
    };
    let ptes: Vec<_> = generated
        .pte_addresses
        .iter()
        .enumerate()
        .map(|(index, address)| {
            let word = generated.writes.iter().find(|word| word.address == *address).expect("实际 PTE 不在初始化表");
            json!({"level":levels - 1 - index,"address":address,"value":format!("0x{:016x}",word.value)})
        })
        .collect();
    json!({"ptes":ptes,"xs_cause":observation["xs_cause"],"nemu_cause":observation["nemu_cause"],"isla_consistent_side":observation["isla_consistent_side"]})
}

fn reported_xs_ppn_fault(sample: &Sample, generated: &Generated, platform: &Platform, observation: &Value) -> bool {
    let (af, pf) = match generated.instruction.access {
        Access::Load => (5, 13),
        Access::Store => (7, 15),
    };
    if observation["isla_consistent_side"] != "nemu"
        || observation["xs_cause"] != af
        || observation["nemu_cause"] != pf
        || generated.expected.cause != pf
    {
        return false;
    }
    let levels = match generated.satp >> 60 {
        8 => 3,
        9 => 4,
        _ => panic!("不支持的分页模式"),
    };
    let status = &sample.pre_registers["mstatus"]["struct"]["bits"]["bits"];
    let status = u64::from_str_radix(status.as_str().expect("mstatus 位串缺失"), 2).unwrap();
    let privilege = sample.pre_registers["cur_privilege"]["enum"].as_str().unwrap();
    for (index, address) in generated.pte_addresses.iter().enumerate() {
        let level = levels - 1 - index;
        let pte = RiscvPte { bits: generated.writes.iter().find(|word| word.address == *address).unwrap().value };
        let nonleaf = !(pte.has_read() || pte.has_write() || pte.has_execute());
        let n = pte.bits >> 63 != 0;
        let invalid = !pte.is_valid()
            || (pte.has_write() && !pte.has_read())
            || pte.bits & (0x1f << 54 | 3 << 61) != 0
            || (!platform.isa.svrsw60t59b && pte.bits & (3 << 59) != 0)
            || if platform.isa.standard_paging {
                (nonleaf && pte.bits & (0xd0 | 1 << 63) != 0) || (n && (level != 0 || pte.ppn() & 15 != 8))
            } else {
                n
            };
        if invalid || (nonleaf && level == 0) {
            return false;
        }
        if nonleaf {
            continue;
        }
        if index + 1 != generated.pte_addresses.len() || pte.ppn() & ((1 << (9 * level)) - 1) != 0 {
            return false;
        }
        let user = pte.bits & (1 << 4) != 0;
        let privilege_failure =
            (privilege == "User" && !user) || (privilege == "Supervisor" && user && status & (1 << 18) == 0);
        let permission = match generated.instruction.access {
            Access::Load => pte.has_read() || (pte.has_execute() && status & (1 << 19) != 0),
            Access::Store => pte.has_write(),
        };
        // 当前平台固定禁用硬件 A/D 更新；按规范顺序只接受第 6–9 步的 PF。
        let permission_failure = privilege_failure
            || !permission
            || pte.bits & (1 << 6) == 0
            || (generated.instruction.access == Access::Store && pte.bits & (1 << 7) == 0);
        return permission_failure && pte.bits & (0xff << 46) != 0;
    }
    false
}

pub(super) struct MismatchTable {
    known: BTreeMap<String, String>,
    rules: BTreeMap<String, String>,
    groups: BTreeMap<String, Value>,
    group_order: Vec<String>,
}

impl MismatchTable {
    pub(super) fn new(known: &[Value]) -> Self {
        let mut table =
            Self { known: BTreeMap::new(), rules: BTreeMap::new(), groups: BTreeMap::new(), group_order: Vec::new() };
        for item in known {
            let object = item.as_object().unwrap();
            assert_eq!(object.len(), 2);
            let reason = item["reason"].as_str().expect("已知问题缺少原因");
            assert!(!reason.is_empty());
            if let Some(rule) = object.get("rule") {
                let rule = rule.as_str().unwrap();
                assert_eq!(rule, KNOWN_RULE, "未登记的已知问题规则");
                assert!(table.rules.insert(rule.into(), reason.into()).is_none());
            } else {
                let key = item["key"].as_object().unwrap();
                assert_eq!(key.len(), 4);
                assert!(["ptes", "xs_cause", "nemu_cause", "isla_consistent_side"]
                    .iter()
                    .all(|name| key.contains_key(*name)));
                let ptes = item["key"]["ptes"].as_array().unwrap();
                assert!(!ptes.is_empty());
                assert!(item["key"]["xs_cause"].is_number() && item["key"]["nemu_cause"].is_number());
                assert!(matches!(
                    item["key"]["isla_consistent_side"].as_str().unwrap(),
                    "xs" | "nemu" | "both" | "neither"
                ));
                let hex = Regex::new(r"^0x[0-9a-f]{16}$").unwrap();
                for pte in ptes {
                    assert_eq!(pte.as_object().unwrap().len(), 3);
                    assert!(
                        pte["level"].is_u64()
                            && pte["address"].is_u64()
                            && hex.is_match(pte["value"].as_str().unwrap())
                    );
                }
                assert!(table.known.insert(super::io::canonical_json(&item["key"]), reason.into()).is_none());
            }
        }
        table
    }

    pub(super) fn record(
        &mut self,
        sample: &Sample,
        generated: &Generated,
        platform: &Platform,
        observation: &Value,
        sample_ref: &str,
    ) -> Value {
        let key = mismatch_key(generated, observation);
        let identity = super::io::canonical_json(&key);
        let rule =
            if self.rules.contains_key(KNOWN_RULE) && reported_xs_ppn_fault(sample, generated, platform, observation) {
                Some(KNOWN_RULE)
            } else {
                None
            };
        let reason = match rule {
            Some(rule) => self.rules.get(rule),
            None => self.known.get(&identity),
        };
        let filtered = reason.is_some();
        if !self.groups.contains_key(&identity) {
            self.group_order.push(identity.clone());
        }
        let group = self.groups.entry(identity).or_insert_with(|| {
            let mut group =
                json!({"key":key,"count":0,"filtered_samples":0,"representative":sample_ref,"known_reason":reason});
            if let Some(rule) = rule {
                group["known_rule"] = json!(rule);
            }
            group
        });
        group["count"] = json!(group["count"].as_u64().unwrap() + 1);
        group["filtered_samples"] = json!(group["filtered_samples"].as_u64().unwrap() + u64::from(filtered));
        json!({"filtered":filtered,"group_key":key,"known_rule":rule})
    }

    pub(super) fn summary(&self) -> Value {
        let groups: Vec<_> = self.group_order.iter().map(|identity| &self.groups[identity]).collect();
        json!({"groups":groups,"mismatch_samples":groups.iter().map(|g|g["count"].as_u64().unwrap()).sum::<u64>(),
            "filtered_samples":groups.iter().map(|g|g["filtered_samples"].as_u64().unwrap()).sum::<u64>(),"known_entries":self.known.len()+self.rules.len()})
    }
}

pub(super) fn observe_run(
    symbols: &BTreeMap<String, u64>,
    expected_cause: u64,
    result: &Value,
    trace: &[Value],
    log: &str,
) -> Value {
    assert!(Regex::new(r"ECFG3_NATIVE child_status=0\b").unwrap().is_match(log), "独立 NEMU 子进程未正常完成");
    let starts: Vec<_> = trace.iter().filter(|entry| entry["event"] == "start").collect();
    assert_eq!(starts.len(), 1, "NEMU 起点必须唯一");
    assert_eq!(starts[0]["pc"], symbols["payload_ins"]);
    assert_eq!(starts[0]["guided_exec"], false);
    let last = trace.last().expect("独立 NEMU 追踪为空");
    assert_eq!(last["event"], "step");
    let names: Vec<_> =
        symbols.iter().filter(|(_, pc)| Some(**pc) == last["pc"].as_u64()).map(|(name, _)| name.as_str()).collect();
    assert_eq!(names.len(), 1, "NEMU 出口必须唯一");
    let symbol = names[0];
    assert!(
        symbol == "good_trap_ins"
            || super::super::testcase::FAILURE_REASONS.iter().any(|reason| symbol == format!("fail_{reason}_trap")),
        "NEMU 未到登记出口"
    );
    let nemu_agrees = symbol == "good_trap_ins";
    let mut xs_agrees = if result["agree"] == true {
        Some(true)
    } else if result["bucket"] == "xs!=expected" {
        Some(false)
    } else {
        None
    };
    let mut xs_cause = if result["abort"] == true {
        Regex::new(r"mcause different at pc = 0x[0-9a-f]+, right = 0x[0-9a-f]+, wrong = 0x([0-9a-f]+)")
            .unwrap()
            .captures(log)
            .map(|c| u64::from_str_radix(&c[1], 16).unwrap())
    } else {
        let refs = Regex::new(r"ECFG3_REF pc=0x[0-9a-f]+ mcause=(\d+)").unwrap();
        let last_ref = refs.captures_iter(log).last().expect("缺少参考寄存器观测");
        Some(last_ref[1].parse::<u64>().unwrap())
    };
    let guides = Regex::new(r"ECFG3_GUIDE force=1 cause=(\d+)").unwrap();
    if let Some(guide) = guides.captures_iter(log).last() {
        xs_cause = Some(guide[1].parse().unwrap());
    }
    if xs_cause.is_some() && xs_cause != Some(expected_cause) {
        xs_agrees = Some(false);
    }
    let side = match (xs_agrees, nemu_agrees) {
        (None, _) => "unobserved",
        (Some(true), true) => "both",
        (Some(true), false) => "xs",
        (Some(false), true) => "nemu",
        (Some(false), false) => "neither",
    };
    json!({"xs_cause":xs_cause,"nemu_cause":last["mcause"],"isla_consistent_side":side,
        "native_exit_symbol":symbol,"native_guided_exec":false,"native_result":last,
        "xs_result_observed":matches!(result["bucket"].as_str().unwrap(),"agree"|"xs!=expected")})
}

/// 基础设施失败没有三方证据。参考侧引导所得的分歧也可以是完整观察。
pub(super) fn complete_probe(result: &Value) -> bool {
    let observation = &result["observation"];
    let side = result["isla_consistent_side"].as_str();
    super::complete_observation(result)
        && result["agree"].as_bool() == Some(side == Some("both"))
        && matches!(
            (result["bucket"].as_str(), side),
            (Some("agree"), Some("both"))
                | (
                    Some("xs!=nemu" | "xs!=expected" | "nemu!=expected" | "xs+nemu!=expected"),
                    Some("xs" | "nemu" | "neither")
                )
        )
        && observation["isla_consistent_side"] == result["isla_consistent_side"]
        && observation["native_guided_exec"] == false
        && observation["native_result"]["event"] == "step"
        && observation["native_result"]["mcause"] == result["nemu_cause"]
        && result["native_exit_symbol"].is_string()
        && result["nemu_cause"].is_u64()
        && (result["xs_cause"].is_u64() || observation["xs_result_observed"] == true)
}

/// 只有完整的主硬件观察才能进入有效预算和后续反馈。
pub(super) fn record_mutant(
    record: &Value,
    result: &Value,
    log: &mut std::fs::File,
    cases: &mut usize,
    infrastructure: &mut usize,
) -> Option<super::lineage::Observation> {
    if complete_probe(result) {
        *cases += 1;
        return Some(super::lineage::Observation::from_fixed(result));
    }
    *infrastructure += 1;
    let failure = match result["bucket"].as_str() {
        Some(bucket @ ("timeout" | "limit" | "framework-abort" | "other-failure")) => bucket,
        _ => "incomplete_observation",
    };
    super::append(
        log,
        &json!({"infrastructure_failure":{
            "mutant_sample_id":record["sample_id"],"parent_entry":record["parent_entry"],
            "parent_sample_id":record["parent_sample_id"],"operator":record["operator"],
            "failure":failure,"agree":result["agree"],"bucket":result["bucket"],"reason":result["reason"]
        }}),
    );
    None
}

fn update_agreement(result: &mut Value, observation: &Value) {
    let side = &observation["isla_consistent_side"];
    let agree = result["agree"] == true && side == "both";
    result["agree"] = json!(agree);
    if !agree && result["bucket"] == "agree" {
        let bucket = match side.as_str() {
            Some("xs") => {
                let reason = observation["native_exit_symbol"]
                    .as_str()
                    .and_then(|symbol| symbol.strip_prefix("fail_"))
                    .and_then(|symbol| symbol.strip_suffix("_trap"))
                    .expect("NEMU 分歧缺少已登记的失败出口");
                result["reason"] = json!(reason);
                "nemu!=expected"
            }
            Some("nemu") => "xs!=expected",
            Some("neither") => "xs+nemu!=expected",
            _ => unreachable!("初步一致结果缺少三方观察"),
        };
        result["bucket"] = json!(bucket);
    }
}

pub(super) fn finish_result(
    sample: &Sample,
    generated: &Generated,
    platform: &Platform,
    symbols: &BTreeMap<String, u64>,
    mut result: Value,
    trace: &[Value],
    log: &str,
    id: &str,
) -> Value {
    let status =
        u64::from_str_radix(sample.pre_registers["mstatus"]["struct"]["bits"]["bits"].as_str().unwrap(), 2).unwrap();
    let privilege = &sample.pre_registers["cur_privilege"]["enum"];
    let fields = json!({"sample_id":sample.sample_id,"isla_cause":generated.expected.cause,"xs_cause":null,"nemu_cause":null,
        "isla_consistent_side":"unobserved","mismatch":{"filtered":false,"known_rule":null,"group_key":null},
        "prestate_context":{"privilege":privilege,"effective_privilege":privilege,"sum":status&(1<<18)!=0,"mxr":status&(1<<19)!=0,"mprv":false,"mpp":(status>>11)&3}});
    result.as_object_mut().unwrap().extend(fields.as_object().unwrap().clone());
    if matches!(result["bucket"].as_str().unwrap(), "timeout" | "limit" | "framework-abort" | "other-failure") {
        return result;
    }
    let observation = observe_run(symbols, generated.expected.cause, &result, trace, log);
    result.as_object_mut().unwrap().extend(observation.as_object().unwrap().clone());
    update_agreement(&mut result, &observation);
    if result["agree"] != true {
        let mut table = MismatchTable::new(&known_mismatch_rules());
        result["mismatch"] = table.record(sample, generated, platform, &observation, id);
        result["mismatch_summary"] = table.summary();
    }
    result["observation"] = observation;
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_only_disagreement_updates_bucket_and_keeps_complete_observation() {
        let mut result = json!({"agree":true,"bucket":"agree","reason":null});
        let observation = json!({"isla_consistent_side":"xs","native_exit_symbol":"fail_unexpected_trap_trap"});
        update_agreement(&mut result, &observation);
        assert_eq!(result["agree"], false);
        assert_eq!(result["bucket"], "nemu!=expected");
        assert_eq!(result["reason"], "unexpected_trap");
        assert!(super::super::complete_observation(&result));
    }

    #[test]
    fn keeps_three_way_agreement_and_existing_disagreement_buckets() {
        for (agree, bucket, side) in [(true, "agree", "both"), (false, "xs!=expected", "nemu")] {
            let mut result = json!({"agree":agree,"bucket":bucket});
            update_agreement(&mut result, &json!({"isla_consistent_side":side}));
            assert_eq!(result["agree"], agree);
            assert_eq!(result["bucket"], bucket);
        }
    }
}
