//! 真实 IR 的 M0 测量入口；与执行器预检同层，直接复用静态效应摘要，不初始化架构。
use super::*;
use crate::ir::regions::{FunctionRegions, RegionOptions};
use serde_json::{json, Value};
use std::collections::BTreeMap;

#[test]
#[ignore = "需要 ISLA_REGIONS_IR、ISLA_M0_INPUT、ISLA_M0_OUTPUT 指定只读输入及输出"]
fn regions_loop_merge_real_ir_measurement() {
    let text = std::fs::read_to_string(std::env::var("ISLA_REGIONS_IR").unwrap()).unwrap();
    let mut symtab = Symtab::new();
    let mut definitions: Vec<crate::ir::Def<Name, B64>> =
        crate::ir_parser::IrParser::new().parse(&mut symtab, crate::ir_lexer::new_ir_lexer(&text)).unwrap();
    crate::ir::assertions_to_jumps(&mut definitions);
    crate::ir::insert_monomorphize(&mut definitions);
    let types = IRTypeInfo::new(&definitions);
    let mut clauses: Vec<Value> =
        serde_json::from_str(&std::fs::read_to_string(std::env::var("ISLA_M0_INPUT").unwrap()).unwrap()).unwrap();
    let config_text = std::fs::read_to_string(clauses[0]["config"].as_str().unwrap()).unwrap();
    let config = ISAConfig::<B64>::parse(&config_text, None, &symtab, &types).unwrap();
    crate::ir::insert_primops(&mut definitions, &symtab, AssertionMode::Optimistic, &config);
    let shared = SharedState::new(
        symtab,
        &definitions,
        types,
        HashSet::new(),
        HashSet::new(),
        HashSet::new(),
        vec![],
        vec![],
        vec![],
    );
    let execute = shared.symtab.lookup("zexecute");
    for pc in [28821, 29115] {
        let Instr::Jump(_, _, location) = &shared.functions[&execute].2[pc] else {
            panic!("FVFTYPE 日志中的 pc{pc} 必须对应 Jump")
        };
        assert_eq!(
            serde_json::to_value(location).unwrap()["line1"].as_u64().unwrap(),
            if pc == 28821 { 983 } else { 1002 }
        );
    }
    eprintln!("M0：已核对 FVFTYPE 的 pc28821、pc29115；开始静态效应摘要");
    let global_state = std::env::var_os("ISLA_M0_GLOBAL_STATE").is_some();
    let summaries = region_summary::function_effect_summaries(&shared, global_state);
    let terminals: Vec<_> =
        summaries.iter().filter_map(|(name, effect)| effect.non_returning.then_some(*name)).collect();
    eprintln!("M0：静态效应摘要已完成");
    let baseline_only = std::env::var_os("ISLA_M0_BASELINE_ONLY").is_some();
    let mut queries = HashMap::new();
    for clause in &mut clauses {
        assert_eq!(
            std::fs::read_to_string(clause["config"].as_str().unwrap()).unwrap(),
            config_text,
            "测量输入的加载期配置必须相同"
        );
        let mut weights = BTreeMap::<String, u64>::new();
        let mut preflight_weights = BTreeMap::<String, u64>::new();
        let mut new_preflight_weights = BTreeMap::<String, u64>::new();
        for branch in clause["branches"].as_array_mut().unwrap() {
            let function = shared.symtab.lookup(&crate::zencode::encode(branch["function"].as_str().unwrap()));
            let pc = branch["branch_pc"].as_u64().unwrap() as usize;
            let count = branch["count"].as_u64().unwrap();
            let body = shared.functions[&function].2;
            let mut baseline_acyclic = false;
            for filtered in [false, true] {
                if baseline_only && filtered {
                    continue;
                }
                let regions = queries.entry((function, filtered)).or_insert_with(|| {
                    FunctionRegions::with_options(
                        body,
                        RegionOptions {
                            bounded_loops: false,
                            filter_assertion_failures: filtered,
                            recreated_slot_liveness: filtered,
                            have_exception: Some(HAVE_EXCEPTION),
                            terminal_calls: &terminals,
                        },
                    )
                });
                let result = regions.region(pc);
                let category = match &result {
                    Ok(region) => {
                        let prefix = if filtered { "m1" } else { "baseline" };
                        branch[format!("{prefix}_join")] = json!(format!("{:?}", region.join));
                        branch[format!("{prefix}_nodes")] = json!(region.nodes.len());
                        if filtered && !baseline_acyclic {
                            "M1 后无环".to_owned()
                        } else {
                            "现状已无环".to_owned()
                        }
                    }
                    Err(reason) => format!("{reason:?}"),
                };
                if !filtered {
                    baseline_acyclic = result.is_ok();
                    if let Some(previous) = branch.get("baseline") {
                        assert_eq!(previous.as_str().unwrap(), category, "与 M1 实现前的静态区域结果必须一致");
                    }
                    branch["baseline"] = json!(category);
                    if baseline_only {
                        *weights.entry(category).or_default() += count;
                    }
                    continue;
                }
                branch["category"] = json!(category);
                *weights.entry(category).or_default() += count;
                let Ok(region) = result else { continue };
                let mut rejections = Vec::new();
                // 与 try_region 的静态预检完全相同，按原始 pc 顺序检查区域全部节点。
                for node in &region.nodes {
                    if let Some(rejection) =
                        region_summary::instruction_effect(function, *node, &body[*node], &shared, &summaries)
                    {
                        let callee = match &body[*node] {
                            Instr::Call(_, _, callee, _, _) => {
                                Some(crate::zencode::decode(shared.symtab.to_str(*callee)))
                            }
                            _ => None,
                        };
                        let mut evidence = json!({
                            "region_pc": node, "reason": rejection.reason,
                            "callee": callee,
                            "rejected_function": crate::zencode::decode(shared.symtab.to_str(rejection.function)),
                            "target_pc": rejection.pc,
                        });
                        let writer = &shared.functions[&rejection.function].2[rejection.pc];
                        let operation = match writer {
                            Instr::PrimopUnary(_, f, ..) => primop::unary_primops::<B64>()
                                .into_iter()
                                .find(|(_, candidate)| std::ptr::fn_addr_eq(*candidate, *f))
                                .unwrap()
                                .0
                                .to_owned(),
                            Instr::PrimopBinary(_, f, ..) => primop::binary_primops::<B64>()
                                .into_iter()
                                .find(|(_, candidate)| std::ptr::fn_addr_eq(*candidate, *f))
                                .unwrap()
                                .0
                                .to_owned(),
                            Instr::PrimopVariadic(_, f, ..) => primop::variadic_primops::<B64>()
                                .into_iter()
                                .find(|(_, candidate)| std::ptr::fn_addr_eq(*candidate, *f))
                                .unwrap()
                                .0
                                .to_owned(),
                            Instr::Call(_, _, callee, ..) => crate::zencode::decode(shared.symtab.to_str(*callee)),
                            Instr::PrimopReset(_, _, effect, _) => format!("配置原语：{effect:?}"),
                            _ => "赋值".to_owned(),
                        };
                        evidence["operation"] = json!(operation);
                        if rejection.reason == SpeculativeRejectReason::CalleeStateWrite {
                            let destination = match writer {
                                Instr::Copy(loc, ..)
                                | Instr::PrimopUnary(loc, ..)
                                | Instr::PrimopBinary(loc, ..)
                                | Instr::PrimopVariadic(loc, ..)
                                | Instr::PrimopReset(loc, ..)
                                | Instr::Call(loc, ..) => loc,
                                _ => panic!("callee_state_write 的证据必须指向写入指令"),
                            };
                            evidence["written_global"] =
                                json!(crate::zencode::decode(shared.symtab.to_str(destination.id())));
                            evidence["indirect_write"] = json!(
                                matches!(destination, Loc::Addr(_))
                                    || matches!(writer, Instr::Call(_, _, WRITE_REGISTER_FROM_VECTOR, _, _))
                            );
                        }
                        rejections.push(evidence);
                    }
                }
                let preflight = rejections
                    .first()
                    .map_or("可通过".to_owned(), |first| first["reason"].as_str().unwrap().to_owned());
                *preflight_weights.entry(preflight.clone()).or_default() += count;
                if !baseline_acyclic {
                    *new_preflight_weights.entry(preflight.clone()).or_default() += count;
                }
                branch["preflight"] = json!(preflight);
                branch["preflight_rejections"] = json!(rejections);
            }
        }
        if baseline_only {
            clause["baseline_weights"] = json!(weights);
        } else {
            clause["weights"] = json!(weights);
            clause["preflight_weights"] = json!(preflight_weights);
            clause["new_preflight_weights"] = json!(new_preflight_weights);
        }
        eprintln!(
            "M0：{} 分类={} 预检={}",
            clause["clause"],
            clause[if baseline_only { "baseline_weights" } else { "weights" }],
            clause["preflight_weights"]
        );
    }
    std::fs::write(std::env::var("ISLA_M0_OUTPUT").unwrap(), serde_json::to_string_pretty(&clauses).unwrap() + "\n")
        .unwrap();
}
