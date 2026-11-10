//! M2 的全局状态差分与事件检查；寄存器名称和结构均不依赖具体架构。
use super::*;

fn diamond(
    then_arm: Vec<Instr<Name, B64>>,
    else_arm: Vec<Instr<Name, B64>>,
    tail: Vec<Instr<Name, B64>>,
) -> Vec<Instr<Name, B64>> {
    let target = else_arm.len() + 2;
    let join = target + then_arm.len();
    let mut program = vec![Instr::Jump(input(0), target, info())];
    program.extend(else_arm);
    program.push(Instr::Goto(join));
    program.extend(then_arm);
    program.extend(tail);
    program
}

fn run(
    program: Vec<Instr<Name, B64>>,
    shared: &SharedState<'static, B64>,
    inputs: usize,
    merge: bool,
    configure: impl FnOnce(&mut LocalFrame<'static, B64>),
) -> Vec<Path> {
    paths_with_state(
        program,
        shared,
        inputs,
        ExecutionLimits::default().with_path_merging(merge).with_region_global_state(true),
        crate::memory::Memory::new(),
        |frame| {
            frame.vars_mut().insert(RETURN, UVal::Init(Val::Bool(false)));
            // 差分两侧使用同一个具体前态；符号前态由程序中的输入赋值覆盖。
            for (name, ty) in &shared.registers {
                if matches!(ty, Ty::Bool) {
                    frame.regs_mut().assign(*name, Val::Bool(false), shared);
                }
            }
            configure(frame);
        },
    )
}

fn check(program: Vec<Instr<Name, B64>>, shared: &SharedState<'static, B64>, inputs: usize) -> Vec<Path> {
    let forked = run(program.clone(), shared, inputs, false, |_| ());
    let merged = run(program, shared, inputs, true, |_| ());
    assert_eq!(equivalent_paths(&forked, &merged, inputs, true), (2, 1));
    assert!(!merged[0].records.is_empty());
    equivalent_register_paths(&forked, &merged, inputs);
    merged
}

fn finish() -> Vec<Instr<Name, B64>> {
    vec![Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()), Instr::End]
}

#[test]
fn region_m2_callee_register_and_global_let_writes() {
    let mut shared = empty_shared_state();
    let reg = shared.symtab.intern("zstate");
    let global = shared.symtab.intern("zglobal");
    shared.registers.insert(reg, Ty::Bool);
    let callee = helper(&mut shared);
    let argument = shared.functions[&callee].0[0].0;
    shared.functions.get_mut(&callee).unwrap().2 = Box::leak(
        vec![
            Instr::Copy(Loc::Id(reg), Exp::Id(argument), info()),
            Instr::Copy(Loc::Id(global), Exp::Id(argument), info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(global), info()),
            Instr::End,
        ]
        .into_boxed_slice(),
    );
    let program = diamond(
        vec![Instr::Call(Loc::Id(RETURN), false, callee, vec![input(1)], info())],
        vec![Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info())],
        vec![Instr::End],
    );
    let configure = |frame: &mut LocalFrame<'static, B64>| {
        frame.lets_mut().insert(global, UVal::Init(Val::Bool(false)));
    };
    let forked = run(program.clone(), &shared, 2, false, configure);
    let merged = run(program, &shared, 2, true, configure);
    assert_eq!(equivalent_paths(&forked, &merged, 2, true), (2, 1));
    equivalent_register_paths(&forked, &merged, 2);
    let path = &merged[0];
    assert!(matches!(path.value, Val::Symbolic(_)), "返回值必须保留臂条件");
    let UVal::Init(global_value) = &path.lets[&global] else { panic!("全局 let 必须初始化") };
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let inputs: Vec<_> = (0..2).map(|_| solver.declare_const(smtlib::Ty::Bool, info())).collect();
    let (_, values) = import_values(
        path,
        &inputs,
        &mut solver,
        &[
            smt_value(&path.value, info()).unwrap(),
            smt_value(path.registers.get_last_if_initialized(reg).unwrap(), info()).unwrap(),
            smt_value(global_value, info()).unwrap(),
        ],
    );
    for value in &values[1..] {
        assert!(solver
            .check_sat_with(&smtlib::Exp::Neq(Box::new(values[0].clone()), Box::new(value.clone())), info())
            .is_unsat()
            .unwrap());
    }
    assert!(!path.events.iter().any(|event| matches!(event, Event::ReadReg(..))));
    assert_eq!(path.events.iter().filter(|event| matches!(event, Event::WriteReg(..))).count(), 1);
}

#[test]
fn region_m2_repeated_write_and_internal_read() {
    let mut shared = empty_shared_state();
    let reg = shared.symtab.intern("zstate");
    shared.registers.insert(reg, Ty::Bool);
    let program = diamond(
        vec![
            Instr::Copy(Loc::Id(reg), Exp::Bool(false), info()),
            Instr::Copy(Loc::Id(reg), input(1), info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
        ],
        vec![Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info())],
        vec![Instr::End],
    );
    let paths = check(program, &shared, 2);
    assert!(!paths[0].events.iter().any(|event| matches!(event, Event::ReadReg(..))));
    assert_eq!(paths[0].events.iter().filter(|event| matches!(event, Event::WriteReg(..))).count(), 1);
}

#[test]
fn region_m2_unrelated_read_after_write_and_first_write_order() {
    let mut shared = empty_shared_state();
    let a = shared.symtab.intern("za");
    let b = shared.symtab.intern("zb");
    let c = shared.symtab.intern("zc");
    for reg in [a, b, c] {
        shared.registers.insert(reg, Ty::Bool);
    }
    let read = Instr::Copy(Loc::Id(RETURN), Exp::Id(c), info());
    let write = |reg, value| Instr::Copy(Loc::Id(reg), Exp::Bool(value), info());
    let paths = check(
        diamond(
            vec![write(a, false), read.clone(), write(b, true), write(a, true), read.clone()],
            vec![read.clone(), read],
            finish(),
        ),
        &shared,
        1,
    );
    assert_eq!(
        paths[0].events.iter().filter(|event| matches!(event, Event::ReadReg(reg, _, _) if *reg == c)).count(),
        1
    );
    let writes: Vec<_> = paths[0]
        .events
        .iter()
        .filter_map(|event| match event {
            Event::WriteReg(reg, _, _) => Some(*reg),
            _ => None,
        })
        .collect();
    assert_eq!(writes, vec![a, b]);
}

#[test]
fn region_m2_callee_address_and_other_write_effects_stay_in_summary() {
    let mut shared = empty_shared_state();
    let callee = helper(&mut shared);
    let argument = shared.functions[&callee].0[0].0;
    for (instruction, reason) in [
        (
            Instr::Copy(Loc::Addr(Box::new(Loc::Id(argument))), Exp::Bool(true), info()),
            SpeculativeRejectReason::CalleeStateWrite,
        ),
        (
            Instr::PrimopVariadic(Loc::Id(RETURN), primop::variadic_primops()["platform_write_mem"], vec![], info()),
            SpeculativeRejectReason::StateEffect,
        ),
    ] {
        shared.functions.get_mut(&callee).unwrap().2 = Box::leak(vec![instruction, Instr::End].into_boxed_slice());
        let summaries = region_summary::function_effect_summaries(&shared, true);
        assert_eq!(summaries[&callee].rejection.unwrap().reason, reason);
    }
}

#[test]
fn region_m2_read_write_read_and_repeated_pre_state_read() {
    let mut shared = empty_shared_state();
    let reg = shared.symtab.intern("zstate");
    shared.registers.insert(reg, Ty::Bool);
    let read = Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info());
    let mut program = diamond(
        vec![read.clone(), Instr::Copy(Loc::Id(reg), input(1), info()), read.clone()],
        vec![read.clone(), read],
        vec![Instr::End],
    );
    // 符号前态也必须在每条路径的最终寄存器映射中保持等价。
    program.insert(0, Instr::Copy(Loc::Id(reg), input(2), info()));
    for instr in &mut program[1..] {
        match instr {
            Instr::Jump(_, target, _) | Instr::Goto(target) => *target += 1,
            _ => (),
        }
    }
    let paths = check(program, &shared, 3);
    assert_eq!(paths[0].events.iter().filter(|event| matches!(event, Event::ReadReg(..))).count(), 1);
}

#[test]
fn region_m2_read_footprint_topology_and_write_cycle() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let regs: Vec<_> = ["za", "zb", "zc"].iter().map(|name| shared.symtab.intern(name)).collect();
    for reg in &regs {
        shared.registers.insert(*reg, Ty::Bool);
    }
    let read = |reg| Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info());
    // 共同读取只有 b；单臂读取分别位于共同读取的前后，不能按寄存器名排序。
    let paths =
        check(diamond(vec![read(regs[0]), read(regs[1])], vec![read(regs[1]), read(regs[2])], finish()), &shared, 1);
    assert_eq!(paths[0].records.last().unwrap().single_arm_reads.len(), 2);
    assert_eq!(paths[0].events.iter().filter(|event| matches!(event, Event::ReadReg(..))).count(), 3);
    // 相反的共同读取和相反的写入偏序分别形成环，都必须拒绝。
    for write in [false, true] {
        let access = |reg| if write { Instr::Copy(Loc::Id(reg), Exp::Bool(true), info()) } else { read(reg) };
        let program = diamond(vec![access(regs[0]), access(regs[1])], vec![access(regs[1]), access(regs[0])], finish());
        let forked = run(program.clone(), &shared, 1, false, |_| ());
        let merged = run(program, &shared, 1, true, |_| ());
        assert_eq!(equivalent_paths(&forked, &merged, 1, true), (2, 2));
        equivalent_register_paths(&forked, &merged, 1);
    }
    assert!(shared.execution_stats.merge_json()["failure_reasons"]["register_sequence"].as_u64().unwrap() >= 2);
}

#[test]
fn region_m2_nested_conditional_write_then_outer_read() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let reg = shared.symtab.intern("zstate");
    shared.registers.insert(reg, Ty::Bool);
    let program = vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(8),
        Instr::Jump(input(1), 6, info()),
        Instr::Copy(Loc::Id(reg), Exp::Bool(true), info()),
        Instr::Goto(7),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
        Instr::End,
    ];
    let forked = run(program.clone(), &shared, 2, false, |_| ());
    let merged = run(program, &shared, 2, true, |_| ());
    assert_eq!(equivalent_paths(&forked, &merged, 2, true), (3, 1), "{}", shared.execution_stats.merge_json());
    equivalent_register_paths(&forked, &merged, 2);
    assert_eq!(merged[0].records.len(), 2);
    assert!(!merged[0].events.iter().any(|event| matches!(event, Event::ReadReg(..))));
    assert_eq!(merged[0].events.iter().filter(|event| matches!(event, Event::WriteReg(..))).count(), 1);
    // 缺少内部读取足迹时，缓存和导出仍必须直接保留最终帧里的条件值。
    use crate::executor::path_cache::{CachedPath, TraceReader, TraceWriter};
    use crate::executor::samples::{fast::FastFacts, SamplePath};
    let path = &merged[0];
    let context = Context::new(Config::new());
    let mut solver = Solver::from_checkpoint(&context, path.checkpoint.clone());
    let sample_path = SamplePath {
        pre: (0..2)
            .map(|i| {
                let UVal::Init(value) = &path.variables[&test_name(900 + i)] else { panic!("输入必须初始化") };
                (format!("input{i}"), value.clone())
            })
            .chain([("state".into(), Val::Bool(false))])
            .collect(),
        post: BTreeMap::from([("state".into(), path.registers.get_last_if_initialized(reg).unwrap().clone())]),
        result: path.value.clone(),
        memory: vec![],
        memory_guards: BTreeMap::new(),
    };
    let facts = FastFacts::analyze(&sample_path, &mut solver, &path.records).unwrap();
    assert!(facts.is_complete(), "内部读的条件值只依赖初始输入");
    let dag = sample_path.export_dag(&solver, &shared, &path.records, 7);
    assert_eq!(dag["guards"].as_array().unwrap().len(), 2);
    assert!(matches!(path.registers.get_last_if_initialized(reg), Some(Val::Symbolic(_))));
    assert!(solver
        .check_sat_with(
            &smtlib::Exp::Neq(
                Box::new(smt_value(path.registers.get_last_if_initialized(reg).unwrap(), info()).unwrap()),
                Box::new(smt_value(&path.value, info()).unwrap()),
            ),
            info()
        )
        .is_unsat()
        .unwrap());
    assert!(dag["state"]["post"]["state"]["symbol"].is_string());
    assert!(dag["state"]["result"]["symbol"].is_string());
    assert!(dag["definitions"].as_array().unwrap().iter().any(|row| row["smtlib"].as_str().unwrap().contains("ite")));
    let mut writer = TraceWriter::default();
    let cached = CachedPath {
        signature: 7,
        checkpoint: writer.capture(&path.checkpoint),
        path: sample_path.into(),
        records: path.records.iter().cloned().map(Into::into).collect(),
        facts: facts.into(),
    };
    let json = serde_json::to_vec(&cached).unwrap();
    let decoded: CachedPath<B64> = serde_json::from_slice(&json).unwrap();
    assert_eq!(decoded, cached);
    let decoded: CachedPath<B64> = bincode::deserialize(&bincode::serialize(&cached).unwrap()).unwrap();
    assert_eq!(decoded, cached);
    let replay = TraceReader::new(&writer.segments).restore(&decoded.checkpoint);
    let mut replay = Solver::from_checkpoint(&context, replay);
    let restored: SamplePath<B64> = decoded.path.into();
    let records: Vec<_> = decoded.records.into_iter().map(Into::into).collect();
    assert!(FastFacts::analyze(&restored, &mut replay, &records).unwrap().is_complete());
    assert_eq!(restored.export_dag(&replay, &shared, &records, 7), dag);
}

#[test]
fn region_m2_relaxed_and_address_writes_remain_rejected() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let reg = shared.symtab.intern("zstate");
    let reference = shared.symtab.intern("zreference");
    shared.registers.insert(reg, Ty::Bool);
    for address in [false, true] {
        let program = diamond(
            vec![Instr::Copy(
                if address { Loc::Addr(Box::new(Loc::Id(reference))) } else { Loc::Id(reg) },
                Exp::Bool(true),
                info(),
            )],
            vec![],
            finish(),
        );
        let configure = |frame: &mut LocalFrame<'static, B64>| {
            frame.vars_mut().insert(reference, UVal::Init(Val::Ref(reg)));
            if !address {
                frame.regs_mut().insert(reg, true, UVal::Init(Val::Bool(false)));
            }
        };
        let forked = run(program.clone(), &shared, 1, false, configure);
        let merged = run(program, &shared, 1, true, configure);
        assert_eq!(equivalent_paths(&forked, &merged, 1, true), (2, 2));
        equivalent_register_paths(&forked, &merged, 1);
        assert!(merged.iter().all(|path| path.records.is_empty()));
    }
    assert!(shared.execution_stats.merge_json()["failure_reasons"]["relaxed_register"].as_u64().unwrap() > 0);
}

#[test]
fn region_m2_opposite_register_order_with_distinct_accessors() {
    let mut shared = empty_shared_state();
    let a = shared.symtab.intern("za");
    let b = shared.symtab.intern("zb");
    let pair = shared.symtab.intern("zpair");
    let x = shared.symtab.intern("zx");
    let y = shared.symtab.intern("zy");
    shared.type_info.structs.insert(pair, BTreeMap::from([(x, Ty::Bool), (y, Ty::Bool)]));
    for reg in [a, b] {
        shared.registers.insert(reg, Ty::Struct(pair));
    }
    let read = |reg, field| Instr::Copy(Loc::Id(RETURN), Exp::Field(Box::new(Exp::Id(reg)), field), info());
    let program = diamond(vec![read(a, x), read(b, x)], vec![read(b, y), read(a, y)], vec![Instr::End]);
    let configure = |frame: &mut LocalFrame<'static, B64>| {
        for reg in [a, b] {
            frame.regs_mut().assign(
                reg,
                Val::Struct([(x, Val::Bool(true)), (y, Val::Bool(false))].into_iter().collect()),
                &shared,
            );
        }
    };
    let forked = run(program.clone(), &shared, 1, false, configure);
    let merged = run(program, &shared, 1, true, configure);
    assert_eq!(equivalent_paths(&forked, &merged, 1, true), (2, 1));
    equivalent_register_paths(&forked, &merged, 1);
    assert_eq!(merged[0].records.last().unwrap().single_arm_reads.len(), 4);
    assert_eq!(merged[0].events.iter().filter(|event| matches!(event, Event::ReadReg(..))).count(), 4);
}

#[test]
fn region_m2_callee_vector_write_uses_register_merge() {
    let mut shared = empty_shared_state();
    let a = shared.symtab.intern("za");
    let b = shared.symtab.intern("zb");
    let refs = shared.symtab.intern("zrefs");
    for reg in [a, b] {
        shared.registers.insert(reg, Ty::Bool);
    }
    let callee = helper(&mut shared);
    shared.functions.get_mut(&callee).unwrap().2 = Box::leak(
        vec![
            Instr::Call(
                Loc::Id(RETURN),
                false,
                WRITE_REGISTER_FROM_VECTOR,
                vec![Exp::I128(0), Exp::Bool(true), Exp::Id(refs)],
                info(),
            ),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::End,
        ]
        .into_boxed_slice(),
    );
    let program = diamond(
        vec![Instr::Call(Loc::Id(RETURN), false, callee, vec![input(0)], info())],
        vec![Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info())],
        vec![Instr::End],
    );
    let configure = |frame: &mut LocalFrame<'static, B64>| {
        frame.lets_mut().insert(refs, UVal::Init(Val::Vector(vec![Val::Ref(a), Val::Ref(b)])));
    };
    let forked = run(program.clone(), &shared, 1, false, configure);
    let merged = run(program, &shared, 1, true, configure);
    assert_eq!(equivalent_paths(&forked, &merged, 1, true), (2, 1));
    equivalent_register_paths(&forked, &merged, 1);
    let writes: Vec<_> = merged[0]
        .events
        .iter()
        .filter_map(|event| match event {
            Event::WriteReg(reg, _, _) => Some(*reg),
            _ => None,
        })
        .collect();
    assert_eq!(writes, vec![a]);
}

#[test]
fn region_m2_status_callback_with_conditional_and_repeated_struct_writes() {
    let mut shared = empty_shared_state();
    let status = shared.symtab.intern("zstatus");
    let context_reg = shared.symtab.intern("zcontext");
    let structure = shared.symtab.intern("zpair");
    let x = shared.symtab.intern("zx");
    let y = shared.symtab.intern("zy");
    shared.type_info.structs.insert(structure, BTreeMap::from([(x, Ty::Bool), (y, Ty::Bool)]));
    for reg in [status, context_reg] {
        shared.registers.insert(reg, Ty::Struct(structure));
    }
    let callback = helper(&mut shared);
    let callback_arg = shared.functions[&callback].0[0].0;
    let local = shared.symtab.intern("zcallback_local");
    shared.functions.get_mut(&callback).unwrap().2 = Box::leak(
        vec![
            Instr::Init(local, Ty::Bool, Exp::Id(callback_arg), info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(local), info()),
            Instr::End,
        ]
        .into_boxed_slice(),
    );
    let accrue = shared.symtab.intern("zupdate_status");
    let flags = shared.symtab.intern("zflags");
    let old = shared.symtab.intern("zold");
    let field = |reg, name| Exp::Field(Box::new(Exp::Id(reg)), name);
    shared.functions.insert(
        accrue,
        (
            vec![(flags, &Ty::Bool)],
            &Ty::Bool,
            Box::leak(
                vec![
                    Instr::Init(old, Ty::Bool, field(status, x), info()),
                    Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(old), Exp::Id(flags)]), 5, info()),
                    Instr::Copy(Loc::Field(Box::new(Loc::Id(status)), x), Exp::Id(flags), info()),
                    Instr::Copy(Loc::Field(Box::new(Loc::Id(context_reg)), x), Exp::Bool(true), info()),
                    Instr::Copy(Loc::Field(Box::new(Loc::Id(context_reg)), y), Exp::Bool(true), info()),
                    Instr::Call(Loc::Id(RETURN), false, callback, vec![field(status, x)], info()),
                    Instr::End,
                ]
                .into_boxed_slice(),
            ),
        ),
    );
    let program = diamond(
        vec![Instr::Call(Loc::Id(RETURN), false, accrue, vec![input(1)], info())],
        vec![Instr::Copy(Loc::Id(RETURN), field(status, x), info())],
        vec![Instr::End],
    );
    let configure = |frame: &mut LocalFrame<'static, B64>| {
        for reg in [status, context_reg] {
            frame.regs_mut().assign(
                reg,
                Val::Struct([(x, Val::Bool(false)), (y, Val::Bool(false))].into_iter().collect()),
                &shared,
            );
        }
    };
    let forked = run(program.clone(), &shared, 2, false, configure);
    let merged = run(program, &shared, 2, true, configure);
    assert_eq!(equivalent_paths(&forked, &merged, 2, true), (3, 1), "{}", shared.execution_stats.merge_json());
    equivalent_register_paths(&forked, &merged, 2);
    assert_eq!(merged[0].records.len(), 2);
    assert_eq!(merged[0].events.iter().filter(|event| matches!(event, Event::ReadReg(..))).count(), 1);
    let writes: Vec<_> = merged[0]
        .events
        .iter()
        .filter_map(|event| match event {
            Event::WriteReg(reg, accessor, _) => {
                assert!(accessor.is_empty());
                Some(*reg)
            }
            _ => None,
        })
        .collect();
    assert_eq!(writes, vec![status, context_reg]);
}
