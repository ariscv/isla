use super::*;
use crate::smt::{
    smtlib::{bits64, Ty},
    Config, Context,
};

#[test]
fn mutation_a_blocks_previous_values_and_keeps_the_class() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let x = solver.declare_bitvector(8, SourceLoc::unknown());
    let unused = solver.declare_bitvector(64, SourceLoc::unknown());
    let g = solver.define_const(
        Exp::Eq(Box::new(Exp::Extract(0, 0, Box::new(Exp::Var(x)))), Box::new(bits64(1, 1))),
        SourceLoc::unknown(),
    );
    let path = SamplePath {
        pre: BTreeMap::from([("x".into(), Val::Symbolic(x)), ("unused".into(), Val::Symbolic(unused))]),
        post: BTreeMap::new(),
        result: Val::Unit,
        memory: Vec::new(),
        memory_guards: BTreeMap::new(),
    };
    let shared = SharedState::empty(crate::ir::Symtab::new());
    assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
    let mut parent = path.materialize(&mut Model::new(&solver), &shared, "merge", 1, Some(0)).unwrap();
    parent.pre_registers.insert("x".into(), json!({"bits":"00000001"}));
    parent
        .pre_registers
        .insert("unused".into(), json!({"bits":"0000000000000000000000000000000000000000000000000000000000000000"}));
    let records = vec![super::tests::judge_record(4, g)];
    let mut mutator = mutation::PathMutator::new(&path, &solver, &records);
    let mut random = || 0x34567890abcdef12;
    let mut values = std::collections::BTreeSet::new();
    for _ in 0..20 {
        let changed = mutator.generate(&path, &mut solver, &shared, &parent, "1", false, &mut random).unwrap().unwrap();
        let bits = changed.sample.pre_registers["x"]["bits"].as_str().unwrap().to_owned();
        assert_ne!(bits, "00000001");
        assert!(bits.ends_with('1'));
        assert!(values.insert(bits));
        assert!(!changed.changes.is_empty());
        assert_eq!(
            changed.sample.pre_registers["unused"], parent.pre_registers["unused"],
            "不能用未使用寄存器制造取值多样性"
        );
        assert_eq!(solver.transaction_depth(), 0);
    }
}

#[test]
fn mutation_b_opens_only_bits_related_to_different_guards() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let x = solver.declare_bitvector(8, SourceLoc::unknown());
    let g = solver.define_const(
        Exp::Eq(Box::new(Exp::Extract(0, 0, Box::new(Exp::Var(x)))), Box::new(bits64(1, 1))),
        SourceLoc::unknown(),
    );
    let path = SamplePath {
        pre: BTreeMap::from([("x".into(), Val::Symbolic(x))]),
        post: BTreeMap::new(),
        result: Val::Unit,
        memory: Vec::new(),
        memory_guards: BTreeMap::new(),
    };
    let shared = SharedState::empty(crate::ir::Symtab::new());
    assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
    let mut parent = path.materialize(&mut Model::new(&solver), &shared, "merge", 1, Some(0)).unwrap();
    parent.pre_registers.insert("x".into(), json!({"bits":"10100101"}));
    let records = vec![super::tests::judge_record(4, g)];
    let mut mutator = mutation::PathMutator::new(&path, &solver, &records);
    let changed = mutator.generate(&path, &mut solver, &shared, &parent, "0", true, &mut || 0).unwrap().unwrap();
    assert_eq!(changed.sample.pre_registers["x"]["bits"], "10100100");
    assert_eq!(solver.transaction_depth(), 0);
    assert!(
        mutator.generate(&path, &mut solver, &shared, &parent, "0", true, &mut || 0).unwrap().is_none(),
        "有限邻类空间耗尽必须显式返回"
    );
}

#[test]
fn mutation_b_preserves_a_coupled_unchanged_guard() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let x = solver.declare_bitvector(8, SourceLoc::unknown());
    let y = solver.declare_bitvector(8, SourceLoc::unknown());
    let first = solver.define_const(
        Exp::Eq(Box::new(Exp::Extract(0, 0, Box::new(Exp::Var(x)))), Box::new(bits64(1, 1))),
        SourceLoc::unknown(),
    );
    let second = solver.define_const(Exp::Eq(Box::new(Exp::Var(x)), Box::new(Exp::Var(y))), SourceLoc::unknown());
    let path = SamplePath {
        pre: BTreeMap::from([("x".into(), Val::Symbolic(x)), ("y".into(), Val::Symbolic(y))]),
        post: BTreeMap::new(),
        result: Val::Unit,
        memory: Vec::new(),
        memory_guards: BTreeMap::new(),
    };
    let shared = SharedState::empty(crate::ir::Symtab::new());
    assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
    let mut parent = path.materialize(&mut Model::new(&solver), &shared, "merge", 1, Some(0)).unwrap();
    for name in ["x", "y"] {
        parent.pre_registers.insert(name.into(), json!({"bits":"00000001"}));
    }
    let records = vec![super::tests::judge_record(4, first), super::tests::judge_record(5, second)];
    let mut mutator = mutation::PathMutator::new(&path, &solver, &records);
    // 11 -> 01 只改变第一个守卫，但保持 x == y 也要求放开 y。
    let changed = mutator
        .generate(&path, &mut solver, &shared, &parent, "01", true, &mut || 0)
        .unwrap()
        .expect("不能把可行邻类误判为耗尽");
    assert_eq!(changed.sample.pre_registers["x"], json!({"bits":"00000000"}));
    assert_eq!(changed.sample.pre_registers["y"], json!({"bits":"00000000"}));
    let judged = path.judge(&mut solver, &shared, &changed.sample, &records, 1, |_, _| Ok(())).unwrap().unwrap();
    assert_eq!(judged.guard_vector, "01");
}

#[test]
fn dag_export_keeps_definition_order_guards_and_state_references() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let x = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let y = solver.define_const(Exp::Not(Box::new(Exp::Var(x))), SourceLoc::unknown());
    solver.assert(Exp::Var(y));
    let path = SamplePath {
        pre: BTreeMap::from([("flag".into(), Val::Symbolic(x))]),
        post: BTreeMap::from([("flag".into(), Val::Symbolic(y))]),
        result: Val::Bool(true),
        memory: Vec::new(),
        memory_guards: BTreeMap::new(),
    };
    let shared = SharedState::empty(crate::ir::Symtab::new());
    let records = vec![super::tests::judge_record(10, y)];
    let value = path.export_dag(&solver, &shared, &records, 42);
    let reread: Value = serde_json::from_slice(&serde_json::to_vec(&value).unwrap()).unwrap();
    assert_eq!(reread, value);
    assert_eq!(reread["guards"].as_array().unwrap().len(), 1);
    let definitions = reread["definitions"].as_array().unwrap();
    assert_eq!(
        definitions.iter().map(|d| d["kind"].as_str().unwrap()).collect::<Vec<_>>(),
        vec!["declare_const", "define_const", "assert"]
    );
    assert_eq!(reread["state"]["pre"]["flag"]["symbol"], format!("v{x}"));
    assert_eq!(reread["state"]["post"]["flag"]["symbol"], format!("v{y}"));
}
