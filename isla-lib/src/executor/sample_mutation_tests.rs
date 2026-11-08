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
                pre: BTreeMap::from([("cur_privilege".into(), Val::Symbolic(privilege))]),
                post: BTreeMap::new(),
                result: Val::Unit,
                memory: Vec::new(),
                memory_guards: BTreeMap::new(),
            };
            assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
            let mut parent = path.materialize(&mut Model::new(&solver), &shared, "merge", 1, Some(0)).unwrap();
            parent.pre_registers.insert("cur_privilege".into(), json!({"enum":"User"}));
            let mut mutator = mutation::PathMutator::new(&path, &solver, &records);
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
        assert!(mutator.profile.queries > 0);
        assert!(mutator.profile.query_seconds <= mutator.profile.total_seconds);
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
    let changed = mutator.generate(&path, &mut solver, &shared, &parent, "0", true, &mut || u64::MAX).unwrap().unwrap();
    assert!(mutator.profile.fixed_buckets > 0);
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

#[test]
fn mutation_ppn_preference_is_soft_and_only_changes_active_leaves() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    for neighbor in [false, true] {
        for required in [false, true] {
            for enabled in [false, true] {
                let run = || {
                    let context = Context::new(Config::new());
                    let mut solver = Solver::<B64>::new(&context);
                    let pte = solver.declare_bitvector(64, SourceLoc::unknown());
                    let data = solver.declare_bitvector(64, SourceLoc::unknown());
                    let inactive = solver.declare_bitvector(64, SourceLoc::unknown());
                    let pointer = solver.declare_bitvector(64, SourceLoc::unknown());
                    // 叶、非叶和未活动读取都依赖守卫；数据读取不依赖守卫。
                    let leaf = solver.define_const(
                        Exp::Eq(Box::new(Exp::Extract(3, 0, Box::new(Exp::Var(pte)))), Box::new(bits64(3, 4))),
                        SourceLoc::unknown(),
                    );
                    let nonleaf = solver.define_const(
                        Exp::Eq(Box::new(Exp::Extract(3, 0, Box::new(Exp::Var(pointer)))), Box::new(bits64(1, 4))),
                        SourceLoc::unknown(),
                    );
                    let unused = solver.define_const(
                        Exp::Eq(Box::new(Exp::Extract(0, 0, Box::new(Exp::Var(inactive)))), Box::new(bits64(1, 1))),
                        SourceLoc::unknown(),
                    );
                    let overflow = solver.define_const(
                        Exp::Neq(Box::new(Exp::Extract(53, 46, Box::new(Exp::Var(pte)))), Box::new(bits64(0, 8))),
                        SourceLoc::unknown(),
                    );
                    let mut records = vec![
                        super::tests::judge_record(0, leaf),
                        super::tests::judge_record(1, nonleaf),
                        super::tests::judge_record(2, unused),
                    ];
                    if required {
                        records.push(super::tests::judge_record(3, overflow));
                    }
                    let read = |value, address| Event::ReadMem {
                        value: Val::Symbolic(value),
                        read_kind: Val::Unit,
                        address: Val::Bits(B64::new(address, 64)),
                        bytes: 8,
                        tag_value: None,
                        opts: Default::default(),
                        region: "mem",
                    };
                    let path = SamplePath {
                        pre: BTreeMap::new(),
                        post: BTreeMap::new(),
                        result: Val::Unit,
                        memory: vec![read(pte, 4096), read(data, 8192), read(inactive, 12288), read(pointer, 16384)],
                        memory_guards: BTreeMap::from([(2, Exp::Bool(false))]),
                    };
                    let shared = SharedState::empty(crate::ir::Symtab::new());
                    let parent_leaf = if neighbor { 9 } else { 3 };
                    solver.assert(Exp::Eq(Box::new(Exp::Var(data)), Box::new(bits64(0xffffffffffffff03, 64))));
                    solver.assert(Exp::Eq(Box::new(Exp::Var(pointer)), Box::new(bits64(0xffffffffffffff01, 64))));
                    solver.assert(Exp::Eq(Box::new(Exp::Var(inactive)), Box::new(bits64((1u64 << 50) | 3, 64))));
                    let tx = solver.start_transaction_with_guard(Some(Exp::Bool(true)));
                    solver.assert(Exp::Eq(Box::new(Exp::Var(pte)), Box::new(bits64((1u64 << 50) | parent_leaf, 64))));
                    // 用事务生成父输入，再恢复原路径。
                    assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
                    let parent = path.materialize(&mut Model::new(&solver), &shared, "merge", 1, Some(0)).unwrap();
                    solver.rollback_transaction(tx);
                    let mut mutator = mutation::PathMutator::new(&path, &solver, &records);
                    mutator.avoid_known_ppn_overflow = enabled;
                    let target = if required { "1111" } else { "111" };
                    let changed = mutator
                        .generate(&path, &mut solver, &shared, &parent, target, neighbor, &mut || u64::MAX)
                        .unwrap()
                        .unwrap();
                    let value = |address| {
                        changed
                            .sample
                            .pre_memory
                            .iter()
                            .filter(|c| (address..address + 8).contains(&c.address))
                            .fold(0u64, |v, c| v | (c.value.unwrap() as u64) << (8 * (c.address - address)))
                    };
                    assert_eq!((value(4096) >> 46) & 255 == 0, enabled && !required);
                    assert_eq!(mutator.ppn_overflow_retained_for_class, enabled && required);
                    assert_eq!(value(8192), 0xffffffffffffff03, "数据读取不能被当作 PTE");
                    assert_eq!(value(16384), 0xffffffffffffff01, "非叶 PTE 的高位保持父值");
                    let judged =
                        path.judge(&mut solver, &shared, &changed.sample, &records, 1, |_, _| Ok(())).unwrap().unwrap();
                    assert_eq!(judged.guard_vector, target);
                    serde_json::to_value(changed.sample).unwrap()
                };
                assert_eq!(run(), run());
            }
        }
    }
}
