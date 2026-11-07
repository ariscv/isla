//! 快档的证明边界：输入决定输出才跳过逐例查询。
use super::*;
use crate::smt::smtlib::Ty;
use crate::smt::{Config, Context};

#[test]
fn fast_facts_skip_only_proven_queries() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let input = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let free = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let mut path = SamplePath {
        pre: BTreeMap::from([("x".into(), Val::Symbolic(input))]),
        post: BTreeMap::from([("x".into(), Val::Symbolic(input))]),
        result: Val::Symbolic(input),
        memory: vec![],
        memory_guards: BTreeMap::new(),
    };
    let shared = SharedState::empty(crate::ir::Symtab::new());
    let facts = fast::FastFacts::analyze(&path, &mut solver, &[]).unwrap();
    assert!(facts.guard_unique && facts.post_unique);
    assert!(sat(&mut solver).unwrap());
    let sample = path.materialize(&mut Model::new(&solver), &shared, "fork", 1, None).unwrap();
    let trace_len = solver.trace().to_vec().len();
    profile::reset();
    let actual = path.classify(&mut solver, &shared, &sample, &[], 1, &facts, |_, _| Ok(())).unwrap().unwrap();
    let timing = profile::take();
    assert_eq!(solver.trace().to_vec().len(), trace_len, "快档查询不得改动原路径定义或断言");
    assert!(!timing.contains_key("guard_unique"));
    assert!(!timing.contains_key("recheck_bind"));
    let expected = path.judge(&mut solver, &shared, &sample, &[], 1, |_, _| Ok(())).unwrap().unwrap();
    assert_eq!(serde_json::to_value(actual).unwrap(), serde_json::to_value(expected).unwrap());
    path.result = Val::Symbolic(free);
    let facts = fast::FastFacts::analyze(&path, &mut solver, &[]).unwrap();
    assert!(!facts.post_unique);
    assert!(path.classify(&mut solver, &shared, &sample, &[], 1, &facts, |_, _| Ok(())).is_err());
    assert_eq!(solver.transaction_depth(), 0);
}

#[test]
fn fast_facts_guarded_reads_and_free_symbols() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let input = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let data = solver.declare_bitvector(8, SourceLoc::unknown());
    let result = solver.define_const(
        Exp::Ite(Box::new(Exp::Var(input)), Box::new(Exp::Var(data)), Box::new(Exp::Bits64(B64::new(7, 8)))),
        SourceLoc::unknown(),
    );
    let event = Event::ReadMem {
        value: Val::Symbolic(data),
        read_kind: Val::Unit,
        address: Val::Bits(B64::new(u64::MAX, 64)),
        bytes: 1,
        tag_value: None,
        opts: Default::default(),
        region: "test",
    };
    let mut path = SamplePath {
        pre: BTreeMap::from([("x".into(), Val::Symbolic(input))]),
        post: BTreeMap::new(),
        result: Val::Symbolic(result),
        memory: vec![event],
        memory_guards: BTreeMap::from([(0, Exp::Var(input))]),
    };
    let facts = fast::FastFacts::analyze(&path, &mut solver, &[]).unwrap();
    assert!(facts.guard_unique && facts.post_unique, "非活动读取不应污染结果");
    path.result = Val::Symbolic(data);
    let facts = fast::FastFacts::analyze(&path, &mut solver, &[]).unwrap();
    assert!(!facts.post_unique, "未活动的读取不能当成由输入决定");
}

#[test]
fn fast_binding_matches_byte_binding_including_wrap_and_missing_bytes() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let address = solver.declare_bitvector(64, SourceLoc::unknown());
    let data = solver.declare_bitvector(16, SourceLoc::unknown());
    let path = SamplePath {
        pre: BTreeMap::from([("address".into(), Val::Symbolic(address))]),
        post: BTreeMap::new(),
        result: Val::Symbolic(data),
        memory: vec![Event::ReadMem {
            value: Val::Symbolic(data),
            read_kind: Val::Unit,
            address: Val::Symbolic(address),
            bytes: 2,
            tag_value: None,
            opts: Default::default(),
            region: "test",
        }],
        memory_guards: BTreeMap::new(),
    };
    let shared = SharedState::empty(crate::ir::Symtab::new());
    solver.assert(Exp::Eq(Box::new(Exp::Var(address)), Box::new(Exp::Bits64(B64::new(u64::MAX, 64)))));
    assert!(sat(&mut solver).unwrap());
    let mut sample = path.materialize(&mut Model::new(&solver), &shared, "fork", 1, None).unwrap();
    sample.pre_memory[0].value = Some(0x34);
    sample.pre_memory[1].value = Some(0x12);
    let facts = fast::FastFacts::analyze(&path, &mut solver, &[]).unwrap();
    for cells in [sample.pre_memory.clone(), sample.pre_memory[..1].to_vec(), vec![]] {
        sample.pre_memory = cells;
        let fast = path.classify(&mut solver, &shared, &sample, &[], 1, &facts, |_, _| Ok(())).unwrap();
        let full = path.judge(&mut solver, &shared, &sample, &[], 1, |_, _| Ok(())).unwrap();
        assert_eq!(serde_json::to_value(fast).unwrap(), serde_json::to_value(full).unwrap());
    }
}

#[test]
fn fast_facts_normalize_inactive_free_guard_and_keep_active_one_slow() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let input = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let free = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let path = SamplePath {
        pre: BTreeMap::from([("x".into(), Val::Symbolic(input))]),
        post: BTreeMap::new(),
        result: Val::Unit,
        memory: vec![],
        memory_guards: BTreeMap::new(),
    };
    let record = super::tests::judge_record(12, free);
    assert!(!fast::FastFacts::analyze(&path, &mut solver, &[record]).unwrap().guard_unique);
    solver.assert(Exp::Not(Box::new(Exp::Var(input))));
    let mut child = super::tests::judge_record(13, free);
    child.parent_record = Some(12);
    child.arm = "then";
    let facts = fast::FastFacts::analyze(&path, &mut solver, &[child, super::tests::judge_record(12, input)]).unwrap();
    assert!(facts.guard_unique && facts.post_unique);
}
