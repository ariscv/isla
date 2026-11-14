use super::*;
use crate::bitvector::b64::B64;

fn logging_program(value: Option<bool>) -> (SharedState<'static, B64>, Name) {
    let mut shared = SharedState::empty(Symtab::new());
    let getter = shared.symtab.intern("zconstant_candidate");
    let caller = shared.symtab.intern("zcaller_candidate");
    let flag = shared.symtab.intern("zflag_candidate");
    let unit = shared.symtab.intern("zunit_candidate");
    let source = SourceLoc::unknown();
    let getter_body = Box::leak(
        vec![Instr::Copy(Loc::Id(RETURN), value.map(Exp::Bool).unwrap_or(Exp::Id(flag)), source), Instr::End]
            .into_boxed_slice(),
    );
    shared.functions.insert(getter, (vec![(flag, &Ty::Bool)], &Ty::Bool, getter_body));
    let body = Box::leak(
        vec![
            Instr::Decl(flag, Ty::Bool, source),
            Instr::Decl(unit, Ty::Unit, source),
            Instr::Call(Loc::Id(flag), false, getter, vec![Exp::Id(flag)], source),
            Instr::Jump(Exp::Id(flag), 6, source),
            Instr::Copy(Loc::Id(RETURN), Exp::Unit, source),
            Instr::End,
            Instr::PrimopUnary(
                Loc::Id(unit),
                primop::unary_primops()["print"],
                Exp::String("真实副作用".into()),
                source,
            ),
            Instr::Copy(Loc::Id(RETURN), Exp::Unit, source),
            Instr::End,
        ]
        .into_boxed_slice(),
    );
    shared.functions.insert(caller, (vec![], &Ty::Unit, body));
    (shared, caller)
}

#[test]
fn constant_false_call_does_not_make_unreachable_io_a_static_rejection() {
    let (shared, caller) = logging_program(Some(false));
    let summary = function_effect_summaries(&shared, true)[&caller];
    assert!(summary.rejection.is_none(), "已证明不可能到达的打印不能阻止区域合并");
    assert_eq!(summary.effect, Effect::Pure);
    let actual_io = instruction_effect(caller, 6, &shared.functions[&caller].2[6], &shared, &HashMap::new()).unwrap();
    assert_eq!(actual_io.reason, SpeculativeRejectReason::StateEffect, "实际到达打印时仍须在执行前拒绝");
}

#[test]
fn constant_true_and_unknown_calls_keep_real_io_rejection() {
    for value in [Some(true), None] {
        let (shared, caller) = logging_program(value);
        let summary = function_effect_summaries(&shared, true)[&caller];
        assert_eq!(summary.rejection.unwrap().reason, SpeculativeRejectReason::StateEffect);
    }
}

#[test]
fn constant_function_assumption_does_not_reuse_the_original_literal_return() {
    let (mut shared, caller) = logging_program(Some(false));
    shared.function_assumptions.push(("zconstant_candidate".into(), vec![None], crate::smt::smtlib::Exp::Bool(true)));
    let summaries = function_effect_summaries(&shared, true);
    let getter = shared.symtab.lookup("zconstant_candidate");
    assert_eq!(summaries[&getter].constant_return, None, "函数假设可以替代原函数体的返回值");
    assert_eq!(summaries[&caller].rejection.unwrap().reason, SpeculativeRejectReason::StateEffect);
}

#[test]
fn constant_function_regions_exclude_dead_io_from_static_scan() {
    use crate::ir::regions::{FunctionRegions, RegionPoint};
    let (shared, caller) = logging_program(Some(false));
    let summaries = function_effect_summaries(&shared, true);
    let constants =
        summaries.iter().filter_map(|(name, summary)| summary.constant_return.map(|value| (*name, value))).collect();
    let mut analysis = FunctionRegions::with_options(shared.functions[&caller].2, RegionOptions::default())
        .with_constant_returns(constants);
    let successors: Vec<_> = analysis.cfg().successors(3).collect();
    assert_eq!(successors, vec![(RegionPoint::Instruction(4), crate::ir::regions::EdgeKind::Jump(false))]);
    let region = analysis.region(3).unwrap();
    assert!(!region.nodes.contains(&6), "不可达打印不能出现在候选区域扫描中");
}
