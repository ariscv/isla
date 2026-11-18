use super::*;
use crate::smt::{
    smtlib::{bits64, Ty},
    Config, Context,
};

#[test]
fn mutation_enum_keeps_allowed_domain_and_selects_deterministically() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let mut shared = SharedState::empty(crate::ir::Symtab::new());
    let name = shared.symtab.intern("zPrivilege");
    let members = ["zUser", "zSupervisor", "zMachine"].map(|n| shared.symtab.intern(n));
    shared.type_info.enums.insert(name, members.to_vec());
    for (index, member) in members.iter().enumerate() {
        shared.type_info.enum_members.insert(*member, (index, members.len(), name));
    }
    for neighbor in [false, true] {
        let run = || {
            let context = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&context);
            let id = solver.get_enum(name, members.len());
            let privilege = solver.declare_const(Ty::Enum(id), SourceLoc::unknown());
            let machine = crate::smt::EnumMember { enum_id: id, member: 2 };
            let allowed = Exp::Neq(Box::new(Exp::Var(privilege)), Box::new(Exp::Enum(machine)));
            solver.assert(allowed.clone());
            let guard = if neighbor {
                Exp::Eq(Box::new(Exp::Var(privilege)), Box::new(Exp::Enum(id.first_member())))
            } else {
                allowed
            };
            let guard = solver.define_const(guard, SourceLoc::unknown());
            let records = vec![super::tests::judge_record(4, guard)];
            let path = SamplePath {
                terminal: Terminal::Normal,
                pre: BTreeMap::from([("cur_privilege".into(), Val::Symbolic(privilege))]),
                post: BTreeMap::new(),
                result: Val::Unit,
                memory: Vec::new(),
                memory_guards: BTreeMap::new(),
            };
            assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
            let mut parent = path.materialize(&mut Model::new(&solver), &shared, "merge", 1, Some(0)).unwrap();
            parent.pre_registers.insert("cur_privilege".into(), json!({"enum":"User"}));
            let mut mutator = mutation::PathMutator::new(&path, &mut solver, &records);
            let target = if neighbor { "0" } else { "1" };
            let changed = mutator
                .generate(&path, &mut solver, &shared, &parent, target, neighbor, &mut || 1)
                .unwrap()
                .expect("允许集合中的另一成员必须可生成");
            assert_eq!(changed.sample.pre_registers["cur_privilege"], json!({"enum":"Supervisor"}));
            let judged =
                path.judge(&mut solver, &shared, &changed.sample, &records, 1, |_, _| Ok(())).unwrap().unwrap();
            assert_eq!(judged.guard_vector, target);
            assert!(mutator
                .generate(&path, &mut solver, &shared, &parent, target, neighbor, &mut || 1)
                .unwrap()
                .is_none());
            serde_json::to_value(changed.sample).unwrap()
        };
        assert_eq!(run(), run());
    }
}

#[test]
fn mutation_a_blocks_whole_inputs_and_keeps_the_class() {
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
        terminal: Terminal::Normal,
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
    let mut mutator = mutation::PathMutator::new(&path, &mut solver, &records);
    let mut random = || 0x34567890abcdef12;
    let mut values = std::collections::BTreeSet::new();
    let mut varied_unused = false;
    for _ in 0..20 {
        let changed = mutator.generate(&path, &mut solver, &shared, &parent, "1", false, &mut random).unwrap().unwrap();
        let bits = changed.sample.pre_registers["x"]["bits"].as_str().unwrap().to_owned();
        assert!(bits.ends_with('1'));
        assert!(values.insert(serde_json::to_string(&changed.sample.pre_registers).unwrap()));
        assert!(!changed.changes.is_empty());
        varied_unused |= changed.sample.pre_registers["unused"] != parent.pre_registers["unused"];
        let judged = path.judge(&mut solver, &shared, &changed.sample, &records, 1, |_, _| Ok(())).unwrap().unwrap();
        assert_eq!(judged.guard_vector, "1");
        assert_eq!(solver.transaction_depth(), 0);
        assert!(mutator.profile.queries > 0);
        assert!(mutator.profile.query_seconds <= mutator.profile.total_seconds);
    }
    assert!(varied_unused, "完全无约束的输入应参与随机填值，不能钉父值");
}

#[test]
fn mutation_b_samples_the_entire_neighbor_class() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let x = solver.declare_bitvector(8, SourceLoc::unknown());
    let g = solver.define_const(
        Exp::Eq(Box::new(Exp::Extract(0, 0, Box::new(Exp::Var(x)))), Box::new(bits64(1, 1))),
        SourceLoc::unknown(),
    );
    let path = SamplePath {
        terminal: Terminal::Normal,
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
    let mut mutator = mutation::PathMutator::new(&path, &mut solver, &records);
    let changed = mutator.generate(&path, &mut solver, &shared, &parent, "0", true, &mut || u64::MAX).unwrap().unwrap();
    let mut values = std::collections::BTreeSet::from([changed.sample.pre_registers["x"].to_string()]);
    for _ in 1..128 {
        let changed =
            mutator.generate(&path, &mut solver, &shared, &parent, "0", true, &mut || u64::MAX).unwrap().unwrap();
        assert!(values.insert(changed.sample.pre_registers["x"].to_string()));
        let judged = path.judge(&mut solver, &shared, &changed.sample, &records, 1, |_, _| Ok(())).unwrap().unwrap();
        assert_eq!(judged.guard_vector, "0");
        assert_eq!(solver.transaction_depth(), 0);
    }
    assert!(mutator.generate(&path, &mut solver, &shared, &parent, "0", true, &mut || 0).unwrap().is_none());
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
        terminal: Terminal::Normal,
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
    let mut mutator = mutation::PathMutator::new(&path, &mut solver, &records);
    // 11 -> 01 只改变第一个守卫，但保持 x == y 也要求放开 y。
    let changed = mutator
        .generate(&path, &mut solver, &shared, &parent, "01", true, &mut || 0)
        .unwrap()
        .expect("不能把可行邻类误判为耗尽");
    assert_eq!(changed.sample.pre_registers["x"], changed.sample.pre_registers["y"]);
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
        terminal: Terminal::Normal,
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

#[test]
fn mutation_random_stream_repeats_whole_inputs_for_a_and_b() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let run = |seed: u64, neighbor| {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let x = solver.declare_bitvector(32, SourceLoc::unknown());
        let free = solver.declare_bitvector(64, SourceLoc::unknown());
        let alias = solver.define_const(Exp::Var(x), SourceLoc::unknown());
        let g = solver.define_const(
            Exp::Eq(Box::new(Exp::Extract(0, 0, Box::new(Exp::Var(x)))), Box::new(bits64(1, 1))),
            SourceLoc::unknown(),
        );
        let path = SamplePath {
            terminal: Terminal::Normal,
            pre: BTreeMap::from([("x".into(), Val::Symbolic(x)), ("free".into(), Val::Symbolic(free))]),
            post: BTreeMap::from([("alias".into(), Val::Symbolic(alias))]),
            result: Val::Symbolic(alias),
            memory: Vec::new(),
            memory_guards: BTreeMap::new(),
        };
        let shared = SharedState::empty(crate::ir::Symtab::new());
        assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
        let mut parent = path.materialize(&mut Model::new(&solver), &shared, "merge", 1, Some(0)).unwrap();
        parent.pre_registers.insert("x".into(), json!({"bits":format!("{:032b}",1)}));
        let records = vec![super::tests::judge_record(4, g)];
        let mut mutator = mutation::PathMutator::new(&path, &mut solver, &records);
        let mut state = seed;
        let mut random = || {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            state
        };
        let target = if neighbor { "0" } else { "1" };
        (0..4)
            .map(|_| {
                let changed = mutator
                    .generate(&path, &mut solver, &shared, &parent, target, neighbor, &mut random)
                    .unwrap()
                    .unwrap();
                assert_eq!(mutator.profile.queries, 2, "只求目标类的一点，再做填值后的最终检查");
                assert_eq!(changed.sample.pre_registers["x"], changed.sample.post_registers["alias"]);
                let judged =
                    path.judge(&mut solver, &shared, &changed.sample, &records, 1, |_, _| Ok(())).unwrap().unwrap();
                assert_eq!(judged.guard_vector, target);
                serde_json::to_value(changed.sample).unwrap()
            })
            .collect::<Vec<_>>()
    };
    for neighbor in [false, true] {
        assert_eq!(run(42, neighbor), run(42, neighbor));
        assert_ne!(run(42, neighbor), run(43, neighbor));
    }
}

#[test]
fn mutation_history_ignores_inactive_reads_and_exhausts_active_inputs() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let flag = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let data = solver.declare_bitvector(8, SourceLoc::unknown());
    solver.assert(Exp::Bvule(Box::new(Exp::Var(data)), Box::new(bits64(1, 8))));
    let path = SamplePath {
        terminal: Terminal::Normal,
        pre: BTreeMap::from([("flag".into(), Val::Symbolic(flag))]),
        post: BTreeMap::new(),
        result: Val::Unit,
        memory: vec![crate::smt::Event::ReadMem {
            value: Val::Symbolic(data),
            read_kind: Val::Unit,
            address: Val::Bits(B64::new(4096, 64)),
            bytes: 1,
            tag_value: None,
            opts: Default::default(),
            region: "mem",
        }],
        memory_guards: BTreeMap::from([(0, Exp::Var(flag))]),
    };
    let shared = SharedState::empty(crate::ir::Symtab::new());
    assert!(solver.check_sat_with(&Exp::Not(Box::new(Exp::Var(flag))), SourceLoc::unknown()).is_sat().unwrap());
    let parent = path.materialize(&mut Model::new(&solver), &shared, "merge", 1, Some(0)).unwrap();
    let records = vec![super::tests::judge_record(4, flag)];
    let mut mutator = mutation::PathMutator::new(&path, &mut solver, &records);
    assert!(mutator.generate(&path, &mut solver, &shared, &parent, "0", false, &mut || 42).unwrap().is_none());
    let mut values = std::collections::BTreeSet::new();
    for _ in 0..2 {
        let changed = mutator.generate(&path, &mut solver, &shared, &parent, "1", true, &mut || 42).unwrap().unwrap();
        assert!(values.insert(changed.sample.pre_memory[0].value));
        let judged = path.judge(&mut solver, &shared, &changed.sample, &records, 1, |_, _| Ok(())).unwrap().unwrap();
        assert_eq!(judged.guard_vector, "1");
    }
    assert!(mutator.generate(&path, &mut solver, &shared, &parent, "1", true, &mut || 42).unwrap().is_none());
}

// 只使用无架构含义的布尔量和位向量，域不能污染类定义或父绑定。
#[test]
fn mutation_input_domain_intersects_without_pinning_free_fields() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let run = || {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let restricted = solver.declare_bitvector(64, SourceLoc::unknown());
        let free = solver.declare_bitvector(64, SourceLoc::unknown());
        let flag = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        let path = SamplePath {
            terminal: Terminal::Normal,
            pre: BTreeMap::from([
                ("restricted".into(), Val::Symbolic(restricted)),
                ("free".into(), Val::Symbolic(free)),
                ("flag".into(), Val::Symbolic(flag)),
            ]),
            post: BTreeMap::new(),
            result: Val::Unit,
            memory: Vec::new(),
            memory_guards: BTreeMap::new(),
        };
        let shared = SharedState::empty(crate::ir::Symtab::new());
        solver.assert(Exp::Var(flag));
        assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
        let parent = path.materialize(&mut Model::new(&solver), &shared, "merge", 1, Some(0)).unwrap();
        let records = vec![super::tests::judge_record(4, flag)];
        let domain = Exp::Eq(Box::new(Exp::Var(restricted)), Box::new(bits64(0, 64)));
        let mut mutator = mutation::PathMutator::new(&path, &mut solver, &records).with_input_domain(domain);
        let mut seed = 42u64;
        let mut random = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            seed
        };
        (0..3)
            .map(|_| {
                let sample = mutator
                    .generate(&path, &mut solver, &shared, &parent, "1", false, &mut random)
                    .unwrap()
                    .unwrap()
                    .sample;
                assert_eq!(sample.pre_registers["restricted"], json!({"bits":"0".repeat(64)}));
                assert_eq!(
                    path.judge(&mut solver, &shared, &sample, &records, 1, |_, _| Ok(()))
                        .unwrap()
                        .unwrap()
                        .guard_vector,
                    "1"
                );
                sample.pre_registers["free"].clone()
            })
            .collect::<Vec<_>>()
    };
    let values = run();
    assert_eq!(values, run());
    assert_eq!(values.iter().map(|v| v.to_string()).collect::<std::collections::BTreeSet<_>>().len(), 3);
}

#[test]
fn mutation_input_domain_empty_intersection_and_finite_exhaustion() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let value = solver.declare_bitvector(2, SourceLoc::unknown());
    let flag = solver.define_const(Exp::Eq(Box::new(Exp::Var(value)), Box::new(bits64(0, 2))), SourceLoc::unknown());
    let path = SamplePath {
        terminal: Terminal::Normal,
        pre: BTreeMap::from([("value".into(), Val::Symbolic(value))]),
        post: BTreeMap::new(),
        result: Val::Unit,
        memory: Vec::new(),
        memory_guards: BTreeMap::new(),
    };
    let shared = SharedState::empty(crate::ir::Symtab::new());
    assert!(solver.check_sat_with(&Exp::Var(flag), SourceLoc::unknown()).is_sat().unwrap());
    let parent = path.materialize(&mut Model::new(&solver), &shared, "merge", 1, Some(0)).unwrap();
    let records = vec![super::tests::judge_record(4, flag)];
    let domain = Exp::Eq(Box::new(Exp::Var(value)), Box::new(bits64(1, 2)));
    let mut mutator = mutation::PathMutator::new(&path, &mut solver, &records).with_input_domain(domain);
    assert!(mutator.generate(&path, &mut solver, &shared, &parent, "1", false, &mut || 42).unwrap().is_none());
    let sample = mutator.generate(&path, &mut solver, &shared, &parent, "0", true, &mut || 42).unwrap().unwrap().sample;
    assert_eq!(sample.pre_registers["value"], json!({"bits":"01"}));
    assert!(mutator.generate(&path, &mut solver, &shared, &parent, "0", true, &mut || 42).unwrap().is_none());
    // 空交集返回不能破坏可供完整 judge 使用的原路径语义。
    assert!(path.judge(&mut solver, &shared, &parent, &records, 1, |_, _| Ok(())).unwrap().is_some());
}

#[test]
fn mutation_input_domain_is_shared_reproducible_and_leaves_other_inputs_free() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let run = || {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let fixed = solver.declare_bitvector(64, SourceLoc::unknown());
        let free = solver.declare_bitvector(8, SourceLoc::unknown());
        let guard = solver.define_const(
            Exp::Eq(Box::new(Exp::Extract(0, 0, Box::new(Exp::Var(free)))), Box::new(bits64(1, 1))),
            SourceLoc::unknown(),
        );
        let path = SamplePath {
            terminal: Terminal::Normal,
            pre: BTreeMap::from([("fixed".into(), Val::Symbolic(fixed)), ("free".into(), Val::Symbolic(free))]),
            post: BTreeMap::new(),
            result: Val::Unit,
            memory: Vec::new(),
            memory_guards: BTreeMap::new(),
        };
        let shared = SharedState::empty(crate::ir::Symtab::new());
        assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
        let mut parent = path.materialize(&mut Model::new(&solver), &shared, "merge", 1, Some(0)).unwrap();
        parent.pre_registers.insert("fixed".into(), json!({"bits":"0".repeat(64)}));
        parent.pre_registers.insert("free".into(), json!({"bits":"00000001"}));
        let records = vec![super::tests::judge_record(4, guard)];
        let domain = Exp::Eq(Box::new(Exp::Var(fixed)), Box::new(bits64(0, 64)));
        let mut mutator = mutation::PathMutator::new(&path, &mut solver, &records).with_input_domain(domain);
        let mut inputs = Vec::new();
        for _ in 0..4 {
            let changed =
                mutator.generate(&path, &mut solver, &shared, &parent, "1", false, &mut || 934875).unwrap().unwrap();
            assert_eq!(changed.sample.pre_registers["fixed"], parent.pre_registers["fixed"]);
            assert!(changed.sample.pre_registers["free"]["bits"].as_str().unwrap().ends_with('1'));
            assert!(!inputs.contains(&changed.sample.pre_registers));
            let judged =
                path.judge(&mut solver, &shared, &changed.sample, &records, 1, |_, _| Ok(())).unwrap().unwrap();
            assert_eq!(judged.guard_vector, "1");
            inputs.push(changed.sample.pre_registers);
        }
        inputs
    };
    assert_eq!(run(), run());
}

#[test]
fn mutation_empty_domain_and_finite_intersection_report_exhaustion() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    for empty in [true, false] {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let x = solver.declare_bitvector(2, SourceLoc::unknown());
        let guard = solver.define_const(
            Exp::Eq(Box::new(Exp::Extract(0, 0, Box::new(Exp::Var(x)))), Box::new(bits64(1, 1))),
            SourceLoc::unknown(),
        );
        let path = SamplePath {
            terminal: Terminal::Normal,
            pre: BTreeMap::from([("x".into(), Val::Symbolic(x))]),
            post: BTreeMap::new(),
            result: Val::Unit,
            memory: Vec::new(),
            memory_guards: BTreeMap::new(),
        };
        let shared = SharedState::empty(crate::ir::Symtab::new());
        assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
        let mut parent = path.materialize(&mut Model::new(&solver), &shared, "merge", 1, Some(0)).unwrap();
        parent.pre_registers.insert("x".into(), json!({"bits":"01"}));
        let records = vec![super::tests::judge_record(4, guard)];
        let domain = if empty {
            Exp::Eq(Box::new(Exp::Var(x)), Box::new(bits64(0, 2)))
        } else {
            Exp::Bvule(Box::new(Exp::Var(x)), Box::new(bits64(3, 2)))
        };
        let mut mutator = mutation::PathMutator::new(&path, &mut solver, &records).with_input_domain(domain);
        if !empty {
            let changed =
                mutator.generate(&path, &mut solver, &shared, &parent, "1", false, &mut || 0).unwrap().unwrap();
            assert_eq!(changed.sample.pre_registers["x"], json!({"bits":"11"}));
        }
        for _ in 0..2 {
            assert!(mutator.generate(&path, &mut solver, &shared, &parent, "1", false, &mut || 0).unwrap().is_none());
            assert_eq!(solver.transaction_depth(), 0);
        }
    }
}

// 在加入字段选择接口前，先冻结旧实现三个连续请求的具体输入。
#[test]
fn mutation_legacy_golden() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let a = solver.declare_bitvector(8, SourceLoc::unknown());
    let b = solver.declare_bitvector(8, SourceLoc::unknown());
    let path = SamplePath {
        terminal: Terminal::Normal,
        pre: BTreeMap::from([("a".into(), Val::Symbolic(a)), ("b".into(), Val::Symbolic(b))]),
        post: BTreeMap::new(),
        result: Val::Unit,
        memory: Vec::new(),
        memory_guards: BTreeMap::new(),
    };
    let shared = SharedState::empty(crate::ir::Symtab::new());
    assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
    let mut parent = path.materialize(&mut Model::new(&solver), &shared, "merge", 1, Some(0)).unwrap();
    parent.pre_registers.insert("a".into(), json!({"bits":"00000000"}));
    parent.pre_registers.insert("b".into(), json!({"bits":"00000000"}));
    let mut mutator = mutation::PathMutator::new(&path, &mut solver, &[]);
    let mut word = 42u64;
    let mut random = || {
        word ^= word << 13;
        word ^= word >> 7;
        word ^= word << 17;
        word
    };
    let mut snapshot = Vec::new();
    for _ in 0..3 {
        let changed = mutator.generate(&path, &mut solver, &shared, &parent, "", false, &mut random).unwrap().unwrap();
        snapshot.push(json!({"pre":changed.sample.pre_registers,"changes":changed.changes}));
    }
    let expected = [(255u64, 0u64), (43, 255), (139, 0)].into_iter().map(|(a, b)| {
        let changes = [("pre.a", a), ("pre.b", b)].into_iter().filter(|(_, value)| *value != 0).map(|(name, value)| {
            json!({"field":name,"before":format!("{:?}",bits64::<Sym>(0,8)),"after":format!("{:?}",bits64::<Sym>(value,8))})
        }).collect::<Vec<_>>();
        json!({"pre":{"a":{"bits":format!("{a:08b}")},"b":{"bits":format!("{b:08b}")}},"changes":changes})
    }).collect::<Vec<_>>();
    assert_eq!(json!(snapshot), json!(expected));
}

#[test]
fn mutation_selected_fields_pin_others_and_report_subset_exhaustion() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    for fixed in [false, true] {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let a = solver.declare_bitvector(2, SourceLoc::unknown());
        let b = solver.declare_bitvector(2, SourceLoc::unknown());
        let path = SamplePath {
            terminal: Terminal::Normal,
            pre: BTreeMap::from([("a".into(), Val::Symbolic(a)), ("b".into(), Val::Symbolic(b))]),
            post: BTreeMap::new(),
            result: Val::Unit,
            memory: Vec::new(),
            memory_guards: BTreeMap::new(),
        };
        let shared = SharedState::empty(crate::ir::Symtab::new());
        assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
        let mut parent = path.materialize(&mut Model::new(&solver), &shared, "merge", 1, Some(0)).unwrap();
        parent.pre_registers.insert("a".into(), json!({"bits":"00"}));
        parent.pre_registers.insert("b".into(), json!({"bits":"00"}));
        let mut mutator = mutation::PathMutator::new(&path, &mut solver, &[]).with_input_domain(if fixed {
            Exp::Eq(Box::new(Exp::Var(a)), Box::new(bits64(0, 2)))
        } else {
            Exp::Bool(true)
        });
        let selected = ["pre.a".to_string()].into_iter().collect();
        let mut seen = std::collections::BTreeSet::new();
        for _ in 0..if fixed { 0 } else { 3 } {
            let changed = mutator
                .generate_with_fields(&path, &mut solver, &shared, &parent, "", false, &selected, &mut || 42)
                .unwrap()
                .unwrap();
            assert_eq!(changed.sample.pre_registers["b"], parent.pre_registers["b"]);
            assert_ne!(changed.sample.pre_registers["a"], parent.pre_registers["a"]);
            assert_eq!(changed.changes.len(), 1);
            assert_eq!(changed.changes[0]["field"], "pre.a");
            assert!(seen.insert(changed.sample.pre_registers["a"].to_string()));
        }
        assert!(mutator
            .generate_with_fields(&path, &mut solver, &shared, &parent, "", false, &selected, &mut || 42)
            .unwrap()
            .is_none());
        // 此子集不可用不代表整类耗尽，另一个字段仍可变化。
        let selected = ["pre.b".to_string()].into_iter().collect();
        let changed = mutator
            .generate_with_fields(&path, &mut solver, &shared, &parent, "", false, &selected, &mut || 42)
            .unwrap()
            .unwrap();
        assert_eq!(changed.sample.pre_registers["a"], parent.pre_registers["a"]);
        assert_ne!(changed.sample.pre_registers["b"], parent.pre_registers["b"]);
    }
}

#[test]
fn mutation_selected_enum_must_change_instead_of_retaining_solver_default() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let mut shared = SharedState::empty(crate::ir::Symtab::new());
    let name = shared.symtab.intern("zChoice");
    let members = ["zFirst", "zSecond"].map(|n| shared.symtab.intern(n));
    shared.type_info.enums.insert(name, members.to_vec());
    for (index, member) in members.iter().enumerate() {
        shared.type_info.enum_members.insert(*member, (index, members.len(), name));
    }
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let sort = solver.get_enum(name, members.len());
    let choice = solver.declare_const(Ty::Enum(sort), SourceLoc::unknown());
    let other = solver.declare_bitvector(8, SourceLoc::unknown());
    let path = SamplePath {
        terminal: Terminal::Normal,
        pre: BTreeMap::from([("choice".into(), Val::Symbolic(choice)), ("other".into(), Val::Symbolic(other))]),
        post: BTreeMap::new(),
        result: Val::Unit,
        memory: Vec::new(),
        memory_guards: BTreeMap::new(),
    };
    assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
    let parent = path.materialize(&mut Model::new(&solver), &shared, "merge", 1, Some(0)).unwrap();
    let mut mutator = mutation::PathMutator::new(&path, &mut solver, &[]);
    let selected = ["pre.choice".to_string()].into_iter().collect();
    let changed = mutator
        .generate_with_fields(&path, &mut solver, &shared, &parent, "", false, &selected, &mut || 42)
        .unwrap()
        .unwrap();
    assert_ne!(changed.sample.pre_registers["choice"], parent.pre_registers["choice"]);
    assert_eq!(changed.sample.pre_registers["other"], parent.pre_registers["other"]);
    assert!(mutator
        .generate_with_fields(&path, &mut solver, &shared, &parent, "", false, &selected, &mut || 42)
        .unwrap()
        .is_none());
}
