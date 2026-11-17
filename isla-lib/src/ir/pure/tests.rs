use super::*;
use crate::bitvector::b64::B64;
use crate::primop;
use crate::source_loc::SourceLoc;

fn program(body: impl FnOnce(Name, Name) -> Vec<Instr<Name, B64>>) -> (SharedState<'static, B64>, Name, Name) {
    let mut shared = SharedState::empty(Symtab::new());
    let function = shared.symtab.intern("zchoose");
    let register = shared.symtab.intern("zstate");
    let argument = shared.symtab.intern("zargument");
    shared.registers.insert(register, Ty::Bool);
    shared.functions.insert(
        function,
        (vec![(argument, &Ty::Bool)], &Ty::Bool, Box::leak(body(register, argument).into_boxed_slice())),
    );
    (shared, function, register)
}
fn classify(shared: &SharedState<B64>, function: Name) -> PureFunction {
    analyze(shared, &Bindings::default(), &HashSet::new()).remove(&function).unwrap()
}
fn site() -> SourceLoc {
    SourceLoc::unknown()
}
#[test]
fn pure_function_passes() {
    let (shared, f, _) = program(|_, arg| vec![Instr::Copy(Loc::Id(RETURN), Exp::Id(arg), site()), Instr::End]);
    let result = classify(&shared, f);
    assert!(result.accepted());
    assert!(result.terminates);
}
#[test]
fn register_write_is_rejected() {
    let (shared, f, reg) = program(|reg, arg| vec![Instr::Copy(Loc::Id(reg), Exp::Id(arg), site()), Instr::End]);
    let result = classify(&shared, f);
    assert!(!result.accepted());
    assert!(result.writes.contains(&reg));
}
#[test]
fn memory_read_is_rejected() {
    let (shared, f, _) = program(|_, _| {
        vec![Instr::PrimopVariadic(Loc::Id(RETURN), primop::variadic_primops()["read_mem"], vec![], site()), Instr::End]
    });
    assert!(!classify(&shared, f).accepted());
}
#[test]
fn symbolic_assertion_is_rejected() {
    let (shared, f, _) = program(|_, arg| {
        vec![
            Instr::Call(Loc::Id(RETURN), true, SAIL_ASSERT, vec![Exp::Id(arg), Exp::String("检查".into())], site()),
            Instr::End,
        ]
    });
    let result = classify(&shared, f);
    assert!(!result.accepted());
    assert_eq!(result.assertions[&(f, 0)], AssertionCondition::Symbolic);
}
#[test]
fn constant_false_assertion_is_a_recorded_dead_arm() {
    let (shared, f, _) = program(|_, _| {
        vec![
            Instr::Call(Loc::Id(RETURN), true, SAIL_ASSERT, vec![Exp::Bool(false), Exp::String("死臂".into())], site()),
            Instr::End,
        ]
    });
    let result = classify(&shared, f);
    assert!(result.accepted());
    assert_eq!(result.assertions[&(f, 0)], AssertionCondition::Concrete(false));
}

#[test]
fn transitive_reads_and_relaxed_state_are_classified() {
    let (mut shared, f, reg) = program(|reg, _| vec![Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), site()), Instr::End]);
    let caller = shared.symtab.intern("zcaller");
    shared.functions.insert(
        caller,
        (
            vec![],
            &Ty::Bool,
            Box::leak(
                vec![Instr::Call(Loc::Id(RETURN), false, f, vec![Exp::Bool(true)], site()), Instr::End]
                    .into_boxed_slice(),
            ),
        ),
    );
    let summaries = analyze(&shared, &Bindings::default(), &HashSet::new());
    assert!(summaries[&caller].accepted());
    assert_eq!(summaries[&caller].registers, BTreeSet::from([reg]));
    assert!(!analyze(&shared, &Bindings::default(), &HashSet::from([reg]))[&caller].accepted());
}

#[test]
fn configuration_can_make_an_assertion_concrete_without_call_site_facts() {
    let (mut shared, f, _) = program(|_, _| vec![Instr::End]);
    let config = shared.symtab.intern("zfixed_setting");
    let temp = shared.symtab.intern("ztemp");
    let flag = shared.symtab.intern("zflag");
    shared.functions.get_mut(&f).unwrap().2 = Box::leak(
        vec![
            Instr::Decl(temp, Ty::I128, site()),
            Instr::Decl(flag, Ty::Bool, site()),
            Instr::PrimopUnary(Loc::Id(temp), primop::unary_primops()["%i64->%i"], Exp::Id(config), site()),
            Instr::PrimopBinary(Loc::Id(flag), primop::binary_primops()["lt"], Exp::Id(temp), Exp::I128(1), site()),
            Instr::Call(Loc::Id(RETURN), true, SAIL_ASSERT, vec![Exp::Id(flag), Exp::String("配置".into())], site()),
            Instr::End,
        ]
        .into_boxed_slice(),
    );
    let lets = Bindings::from_iter([(config, UVal::Init(Val::I64(10)))]);
    let result = analyze(&shared, &lets, &HashSet::new()).remove(&f).unwrap();
    assert!(result.accepted(), "{:?}", result.rejections);
    assert_eq!(result.lets, BTreeSet::from([config]));
    assert_eq!(result.assertions[&(f, 4)], AssertionCondition::Concrete(false));
}

/// 外部输入只通过环境变量指定，测试代码不包含任何模型或函数特判。
#[test]
#[ignore = "需要 ISLA_PURE_IR、ISLA_PURE_CONFIG、ISLA_PURE_FUNCTION"]
fn analyze_external_ir() {
    use crate::config::ISAConfig;
    use crate::init::initialize_architecture;
    use crate::ir::AssertionMode;
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let text = std::fs::read_to_string(std::env::var("ISLA_PURE_IR").unwrap()).unwrap();
    let mut symbols = Symtab::new();
    let mut definitions =
        crate::ir_parser::IrParser::new().parse(&mut symbols, crate::ir_lexer::new_ir_lexer(&text)).unwrap();
    let raw_functions: HashMap<_, _> = definitions
        .iter()
        .filter_map(|d| match d {
            crate::ir::Def::Fn(n, _, b) => Some((*n, b)),
            _ => None,
        })
        .collect();
    let raw_target = symbols.lookup(&crate::zencode::encode(&std::env::var("ISLA_PURE_FUNCTION").unwrap()));
    let mut raw_closure = BTreeSet::new();
    let mut pending = vec![raw_target];
    while let Some(n) = pending.pop() {
        if raw_closure.insert(n) {
            for i in raw_functions[&n] {
                if let Instr::Call(_, _, f, _, _) = i {
                    if raw_functions.contains_key(f) {
                        pending.push(*f)
                    }
                }
            }
        }
    }
    let types = IRTypeInfo::new(&definitions);
    let config = ISAConfig::<B64>::from_file(
        &mut sha2::Sha256::default(),
        std::env::var("ISLA_PURE_CONFIG").unwrap(),
        None,
        &symbols,
        &types,
    )
    .unwrap();
    let initialized =
        initialize_architecture(&mut definitions, symbols, types, &config, AssertionMode::Optimistic, false);
    let shared = &initialized.shared_state;
    let target = shared.symtab.lookup(&crate::zencode::encode(&std::env::var("ISLA_PURE_FUNCTION").unwrap()));
    let summaries = analyze_from(shared, &initialized.lets, &config.relaxed_registers, &BTreeSet::from([target]));
    let removed: Vec<_> = raw_closure
        .iter()
        .filter(|n| !summaries.contains_key(n))
        .map(|n| crate::zencode::decode(shared.symtab.to_str(*n)))
        .collect();
    println!("原始函数闭包={}，加载后={}，改写后不再调用={:?}", raw_closure.len(), summaries.len(), removed);
    let config_values: Vec<_> = summaries[&target]
        .lets
        .iter()
        .map(|n| format!("{}={:?}", crate::zencode::decode(shared.symtab.to_str(*n)), initialized.lets[n]))
        .collect();
    println!("不可变配置读取={:?}", config_values);
    let names =
        |set: &BTreeSet<Name>| set.iter().map(|n| crate::zencode::decode(shared.symtab.to_str(*n))).collect::<Vec<_>>();
    let mut closure = BTreeSet::new();
    let mut pending = vec![target];
    while let Some(n) = pending.pop() {
        if closure.insert(n) {
            pending.extend(&summaries[&n].calls);
        }
    }
    for n in &closure {
        let s = &summaries[n];
        let assertions: Vec<_> = s
            .assertions
            .iter()
            .map(|((f, pc), c)| format!("{}@{}:{:?}", crate::zencode::decode(shared.symtab.to_str(*f)), pc, c))
            .collect();
        println!(
            "{}",
            serde_json::json!({"function": crate::zencode::decode(shared.symtab.to_str(*n)),
            "accepted": s.accepted(), "registers": names(&s.registers), "lets": names(&s.lets), "writes": names(&s.writes),
            "calls": names(&s.calls), "assertions": assertions, "external_sites": s.externals.len(), "external_primitives": s.externals,
            "back_edge": s.has_back_edge, "terminates": s.terminates, "rejections": s.rejections})
        );
    }
    let rejected = summaries.values().filter(|s| !s.accepted()).count();
    println!("已分析函数={}，拒绝={}，目标闭包={}", summaries.len(), rejected, closure.len());
    assert!(summaries[&target].accepted(), "{:?}", summaries[&target].rejections);
    if let Ok(expected) = std::env::var("ISLA_PURE_EXPECT_READS") {
        let actual: BTreeSet<_> =
            names(&summaries[&target].registers).into_iter().chain(names(&summaries[&target].lets)).collect();
        assert_eq!(actual, expected.split(',').map(str::to_owned).collect());
    }
}

#[test]
fn parameter_shadowing_a_let_does_not_make_a_symbolic_assertion_concrete() {
    let (shared, f, _) = program(|_, arg| {
        vec![
            Instr::Call(Loc::Id(RETURN), true, SAIL_ASSERT, vec![Exp::Id(arg), Exp::String("形参".into())], site()),
            Instr::End,
        ]
    });
    let argument = shared.functions[&f].0[0].0;
    let lets = Bindings::from_iter([(argument, UVal::Init(Val::Bool(false)))]);
    assert!(!analyze(&shared, &lets, &HashSet::new())[&f].accepted());
}
#[test]
fn assumed_functions_are_not_pure_body_summaries() {
    let (mut shared, f, _) = program(|_, _| vec![Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), site()), Instr::End]);
    shared.function_assumptions.push(("zchoose".into(), vec![None], crate::smt::smtlib::Exp::Bool(false)));
    assert!(!classify(&shared, f).accepted());
}

#[test]
fn dynamic_state_opaque_calls_references_and_pessimistic_asserts_are_rejected() {
    let source = SourceLoc::unknown();
    for kind in 0..4 {
        let (mut shared, f, _) = program(|reg, arg| {
            vec![
                match kind {
                    0 => Instr::PrimopUnary(
                        Loc::Id(RETURN),
                        primop::unary_primops()["get_cycle_count"],
                        Exp::Unit,
                        source,
                    ),
                    1 => Instr::Call(Loc::Id(RETURN), true, Name::from_u32(999), vec![], source),
                    2 => Instr::Copy(Loc::Id(RETURN), Exp::Ref(reg), source),
                    _ => Instr::PrimopBinary(
                        Loc::Id(RETURN),
                        primop::binary_primops()["pessimistic_assert"],
                        Exp::Id(arg),
                        Exp::String("悲观".into()),
                        source,
                    ),
                },
                Instr::End,
            ]
        });
        if kind == 1 {
            // 给未知调用合法符号，但不给它效应契约。
            let opaque = shared.symtab.intern("zopaque");
            let (_, _, body) = shared.functions.get_mut(&f).unwrap();
            *body = Box::leak(
                vec![Instr::Call(Loc::Id(RETURN), true, opaque, vec![], source), Instr::End].into_boxed_slice(),
            );
        }
        assert!(!classify(&shared, f).accepted(), "拒绝项 {}", kind);
    }
}
