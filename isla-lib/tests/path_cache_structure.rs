//! 合成 IR 的完整快照与损坏检查；不含处理器专用名字。
use isla_lib::{
    bitvector::{b64::B64, BV},
    executor::{
        path_cache::{self as cache, *},
        samples::SamplePath,
    },
    ir::{SharedState, Symtab, Val},
    smt::{
        self, checkpoint,
        smtlib::{Def, Exp, Ty},
        Config, Context, EnumMember, Event, ReadOpts, Solver, WriteOpts,
    },
    source_loc::SourceLoc,
};
use std::collections::BTreeMap;

fn fixture() -> (Vec<Segment<B64>>, Vec<CachedPath<B64>>, SharedState<'static, B64>) {
    smt::configure_tastic(smt::Tactic::Qfaufbv);
    let mut symbols = Symtab::new();
    let kind = symbols.intern("kind");
    let first = symbols.intern("first");
    let second = symbols.intern("second");
    let constructor = symbols.intern("constructor");
    let register = symbols.intern("register");
    let function = symbols.intern("function");
    let mut shared = SharedState::empty(symbols);
    shared.type_info.enums.insert(kind, vec![first, second]);
    shared.type_info.enum_members.insert(first, (0, 2, kind));
    shared.type_info.enum_members.insert(second, (1, 2, kind));
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let enumeration = solver.get_enum(kind, 2);
    let input = solver.declare_const(Ty::BitVec(8), SourceLoc::unknown());
    let condition = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let fun = solver.fresh();
    solver.add(Def::DeclareFun(fun, vec![Ty::BitVec(8)], Ty::BitVec(8)));
    let result = solver.define_const(Exp::App(fun, vec![Exp::Var(input)]), SourceLoc::unknown());
    let enum_value = Val::Enum(EnumMember { enum_id: enumeration, member: 1 });
    let read = Event::ReadMem {
        value: Val::Symbolic(result),
        read_kind: Val::Unit,
        address: Val::Bits(B64::new(0, 64)),
        bytes: 1,
        tag_value: Some(Val::Bool(true)),
        opts: ReadOpts::exclusive(),
        region: "generic",
    };
    let write = Event::WriteMem {
        value: condition,
        write_kind: Val::Unit,
        address: Val::Bits(B64::new(0, 64)),
        data: Val::Symbolic(input),
        bytes: 1,
        tag_value: None,
        opts: WriteOpts::exclusive(),
        region: "generic",
    };
    let value = Val::Ctor(constructor, Box::new(enum_value));
    let events = vec![
        Event::Fork(13, condition, 1, SourceLoc::unknown()),
        Event::Merge(13, 2, SourceLoc::unknown()),
        Event::Function { name: function, call: true },
        Event::Abstract {
            name: function,
            primitive: true,
            args: vec![value.clone()],
            return_value: Val::Symbolic(result),
        },
        Event::ReadReg(register, vec![], value.clone()),
        Event::WriteReg(register, vec![], Val::Symbolic(result)),
        Event::AssumeReg(register, vec![], Val::Symbolic(input)),
        read.clone(),
        write.clone(),
        Event::MarkReg { regs: vec![register], mark: "mark".into() },
        Event::AddressAnnounce { address: Val::Bits(B64::new(0, 64)) },
        Event::Branch { address: Val::Bits(B64::new(0, 64)) },
        Event::Cycle,
        Event::Instr(value.clone()),
        Event::Assume(Exp::Bool(true)),
        Event::AssumeFun { name: function, args: vec![value.clone()], return_value: Val::Unit },
        Event::UseFunAssumption { name: function, args: vec![value.clone()], return_value: Val::Unit },
    ];
    for event in events {
        solver.add_event(event);
    }
    let checkpoint = checkpoint(&mut solver);
    let mut writer = TraceWriter::default();
    let checkpoint = writer.capture(&checkpoint);
    let path = SamplePath {
        pre: BTreeMap::from([("input".into(), Val::Symbolic(input))]),
        post: BTreeMap::from([("result".into(), Val::Symbolic(result))]),
        result: value,
        memory: vec![read.clone(), write],
        memory_guards: BTreeMap::from([(0, Exp::Var(condition))]),
    };
    let record = Record {
        record_id: 1009,
        parent_record: None,
        arm: Arm::Root,
        function,
        branch_pc: 3,
        join: cache::event::RegionPoint::FunctionExit,
        condition: condition.as_u32(),
        source_loc: SourceLoc::unknown(),
        depth: 0,
        dead: false,
        value_symbols: vec![],
        input_symbols: vec![],
        single_arm_reads: vec![GuardedRead {
            register,
            accessor: vec![],
            value: cache::value::Val::Symbolic(input.as_u32()),
            guard: cache::expr::Exp::Var(condition.as_u32()),
        }],
        memory_reads: vec![(0, cache::expr::Exp::Var(condition.as_u32()), read.into())],
    };
    (
        writer.segments,
        vec![CachedPath {
            signature: 109,
            checkpoint,
            path: path.into(),
            records: vec![record],
            facts: Facts { guard_unique: true, post_unique: true, simple_pre: false },
        }],
        shared,
    )
}

#[test]
fn 合成_ir_所有事件_枚举_构造子_函数应用及_dag_往返() {
    let (segments, paths, shared) = fixture();
    let names = NameEnvironment::capture(&shared.symtab, &shared.type_info);
    validate_paths(&segments, &paths, &names, &[], &[]);
    let json = serde_json::to_vec(&(segments.clone(), paths.clone())).unwrap();
    let bin = bincode::serialize(&(segments.clone(), paths.clone())).unwrap();
    let a: (Vec<Segment<B64>>, Vec<CachedPath<B64>>) = serde_json::from_slice(&json).unwrap();
    let b = bincode::deserialize(&bin).unwrap();
    assert_eq!(a, b);
    assert_eq!(a, (segments.clone(), paths.clone()));
    let reader = TraceReader::new(&segments);
    let restored = TraceReader::new(&a.0);
    let context = Context::new(Config::new());
    let export = |reader: &TraceReader<B64>, p: &CachedPath<B64>| {
        let solver = Solver::from_checkpoint(&context, reader.restore(&p.checkpoint));
        let path: SamplePath<B64> = p.path.clone().into();
        let records = p.records.iter().cloned().map(Into::into).collect::<Vec<_>>();
        serde_json::to_vec(&path.export_dag(&solver, &shared, &records, p.signature)).unwrap()
    };
    assert_eq!(export(&reader, &paths[0]), export(&restored, &a.1[0]));
}

#[test]
fn 损坏的符号空间_记录和访存索引逐项拒绝() {
    let (segments, paths, shared) = fixture();
    let names = NameEnvironment::capture(&shared.symtab, &shared.type_info);
    let reject = |segments: &[Segment<B64>], paths: &[CachedPath<B64>]| {
        assert!(std::panic::catch_unwind(|| validate_paths(segments, paths, &names, &[], &[])).is_err())
    };
    let mut changed = paths.clone();
    changed[0].checkpoint.next_var = 0;
    reject(&segments, &changed);
    let mut changed = paths.clone();
    let duplicate = changed[0].records[0].clone();
    changed[0].records.push(duplicate);
    reject(&segments, &changed);
    let mut changed = paths.clone();
    changed[0].records[0].parent_record = Some(1008);
    changed[0].records[0].arm = Arm::Then;
    reject(&segments, &changed);
    let mut changed = paths.clone();
    changed[0].records[0].parent_record = Some(1009);
    changed[0].records[0].arm = Arm::Then;
    reject(&segments, &changed);
    let mut changed = paths.clone();
    changed[0].path.memory_guards[0].0 = 3;
    reject(&segments, &changed);
    let mut changed = segments.clone();
    changed[0].events.push(cache::event::Event::Smt(
        cache::expr::Def::Assert(cache::expr::Exp::App(u32::MAX, vec![])),
        cache::event::DefAttrs { bits: 0 },
        SourceLoc::unknown(),
    ));
    reject(&changed, &paths);
    let mut changed = segments.clone();
    changed[0].events.push(cache::event::Event::Smt(
        cache::expr::Def::DefineEnum(shared.symtab.lookup("kind"), 3),
        cache::event::DefAttrs { bits: 0 },
        SourceLoc::unknown(),
    ));
    reject(&changed, &paths);
    let mut changed = paths.clone();
    changed[0].path.result =
        cache::value::Val::Enum(cache::expr::Member { enum_id: shared.symtab.lookup("kind"), member: 2 });
    reject(&segments, &changed);
    assert!(std::panic::catch_unwind(|| validate_paths(&segments, &paths, &names, &[], &[("size".into(), u32::MAX)]))
        .is_err());
}
