//! 缓存名字环境的契约测试；不依赖任何处理器名字。
use isla_lib::bitvector::b64::B64;
use isla_lib::executor::path_cache::NameEnvironment;
use isla_lib::ir::{Name, SharedState, Symtab};

fn environment() -> SharedState<'static, B64> {
    let mut symtab = Symtab::new();
    let kind = symtab.intern("kind");
    let first = symtab.intern("first");
    let second = symtab.intern("second");
    symtab.mangled_names.insert(first, "original");
    let mut shared = SharedState::empty(symtab);
    shared.type_info.enums.insert(kind, vec![first, second]);
    shared.type_info.enum_members.insert(first, (0, 2, kind));
    shared.type_info.enum_members.insert(second, (1, 2, kind));
    shared
}

#[test]
fn 名字环境双编码并允许尾部追加() {
    let mut shared = environment();
    let saved = NameEnvironment::capture(&shared.symtab, &shared.type_info);
    let json = serde_json::to_vec(&saved).unwrap();
    let bin = bincode::serialize(&saved).unwrap();
    assert_eq!(serde_json::from_slice::<NameEnvironment>(&json).unwrap(), bincode::deserialize(&bin).unwrap());
    shared.symtab.intern("appended");
    saved.validate(&shared.symtab, &shared.type_info);
}

#[test]
#[should_panic(expected = "符号表")]
fn 名字编号不一致必须拒绝() {
    let shared = environment();
    let mut saved = NameEnvironment::capture(&shared.symtab, &shared.type_info);
    saved.symbols[0] = "different".into();
    saved.validate(&shared.symtab, &shared.type_info);
}

#[test]
#[should_panic(expected = "枚举")]
fn 枚举换序必须拒绝() {
    let shared = environment();
    let mut saved = NameEnvironment::capture(&shared.symtab, &shared.type_info);
    saved.enums[0].1.swap(0, 1);
    saved.validate(&shared.symtab, &shared.type_info);
}

#[test]
#[should_panic(expected = "反混淆")]
fn 反混淆映射不一致必须拒绝() {
    let shared = environment();
    let mut saved = NameEnvironment::capture(&shared.symtab, &shared.type_info);
    saved.mangled_names[0].1 = "different".into();
    saved.validate(&shared.symtab, &shared.type_info);
}

#[test]
#[should_panic(expected = "源文件")]
fn 源文件不一致必须拒绝() {
    let shared = environment();
    let mut saved = NameEnvironment::capture(&shared.symtab, &shared.type_info);
    saved.files.push("missing.sail".into());
    saved.validate(&shared.symtab, &shared.type_info);
}

#[test]
#[should_panic(expected = "反向")]
fn 枚举反向表不一致必须拒绝() {
    let mut shared = environment();
    let saved = NameEnvironment::capture(&shared.symtab, &shared.type_info);
    shared.type_info.enum_members.get_mut(&Name::from_u32(saved.enums[0].1[0].0.as_u32())).unwrap().0 = 1;
    saved.validate(&shared.symtab, &shared.type_info);
}

use isla_lib::executor::path_cache::{CheckpointData, TraceReader, TraceWriter};
use isla_lib::smt::{checkpoint, Config, Context, Event, Solver};

#[test]
fn 空段和共享父节点必须原样恢复() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    solver.add_event(Event::Cycle);
    let parent = checkpoint(&mut solver);
    let empty = checkpoint(&mut solver);
    let mut writer = TraceWriter::default();
    let a = writer.capture(&parent);
    let b = writer.capture(&empty);
    assert_eq!(writer.segments.len(), 2);
    assert_eq!(writer.segments[1].parent, a.leaf);
    assert!(writer.segments[1].events.is_empty());
    let reader = TraceReader::new(&writer.segments);
    let restored_a = reader.restore(&a);
    let restored_b = reader.restore(&b);
    let mut again = TraceWriter::default();
    assert_eq!(a, again.capture(&restored_a));
    assert_eq!(b, again.capture(&restored_b));
    assert_eq!(writer.segments, again.segments);
    let replay = Solver::from_checkpoint(&context, restored_b);
    assert_eq!(replay.trace().to_vec().len(), 1);
}

#[test]
#[should_panic(expected = "父段")]
fn 父链成环必须拒绝() {
    use isla_lib::executor::path_cache::Segment;
    let segments = vec![Segment::<B64> { id: 0, parent: Some(0), checkpoints: 0, events: vec![] }];
    TraceReader::new(&segments);
}

#[test]
#[should_panic(expected = "段数")]
fn 检查点段数错误必须拒绝() {
    let reader = TraceReader::<B64>::new(&[]);
    reader.restore(&CheckpointData { num: 1, next_var: 0, leaf: None });
}

#[test]
fn 完整路径与非连续记录编号往返并重新导出() {
    use isla_lib::executor::path_cache::{event::RegionPoint, value::Val};
    use isla_lib::executor::path_cache::{CachedPath, Facts, PathData, Record};
    use std::collections::BTreeMap;
    let cached = CachedPath::<B64> {
        pure_definitions: vec![],
        signature: 999,
        checkpoint: CheckpointData { num: 0, next_var: 1, leaf: None },
        path: PathData {
            terminal: Default::default(),
            pre: BTreeMap::new(),
            post: BTreeMap::new(),
            result: Val::MixedBits(vec![]),
            memory: vec![],
            memory_guards: vec![],
        },
        records: vec![Record {
            record_id: 998,
            parent_record: None,
            arm: isla_lib::executor::path_cache::Arm::Root,
            function: Name::from_u32(9),
            branch_pc: 8,
            join: RegionPoint::FunctionExit,
            condition: 0,
            source_loc: isla_lib::source_loc::SourceLoc::unknown(),
            depth: 0,
            dead: false,
            value_symbols: vec![0],
            input_symbols: vec![0],
            single_arm_reads: vec![],
            memory_reads: vec![],
        }],
        facts: Facts { guard_unique: true, post_unique: false, simple_pre: true },
    };
    let json = serde_json::to_vec(&cached).unwrap();
    let bin = bincode::serialize(&cached).unwrap();
    assert_eq!(cached, serde_json::from_slice(&json).unwrap());
    assert_eq!(cached, bincode::deserialize(&bin).unwrap());
    let core: isla_lib::executor::samples::SamplePath<B64> = cached.path.clone().into();
    assert_eq!(cached.path, core.into());
    let core: isla_lib::executor::RegionMergeRecord<B64> = cached.records[0].clone().into();
    assert_eq!(cached.records[0], core.into());
    let core: isla_lib::executor::samples::fast::FastFacts = cached.facts.clone().into();
    assert_eq!(cached.facts, core.into());
}

#[test]
#[should_panic(expected = "未声明")]
fn 定义中的悬空引用必须拒绝() {
    use isla_lib::executor::path_cache::{
        event::{DefAttrs, Event},
        expr::{Def, Exp},
        validate_paths,
        value::Val,
        CachedPath, Facts, PathData, Segment,
    };
    let shared = environment();
    let names = NameEnvironment::capture(&shared.symtab, &shared.type_info);
    let segments = vec![Segment::<B64> {
        id: 0,
        parent: None,
        checkpoints: 0,
        events: vec![Event::Smt(
            Def::Assert(Exp::Var(8)),
            DefAttrs { bits: 0 },
            isla_lib::source_loc::SourceLoc::unknown(),
        )],
    }];
    let paths = vec![CachedPath {
        pure_definitions: vec![],
        signature: 1,
        checkpoint: CheckpointData { num: 1, next_var: 9, leaf: Some(0) },
        path: PathData {
            terminal: Default::default(),
            pre: Default::default(),
            post: Default::default(),
            result: Val::Unit,
            memory: vec![],
            memory_guards: vec![],
        },
        records: vec![],
        facts: Facts { guard_unique: true, post_unique: true, simple_pre: true },
    }];
    validate_paths(&segments, &paths, &names, &[], &[]);
}

#[test]
fn 导出器不能把已释放节点的地址复用当成共享() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut writer = TraceWriter::default();
    for iteration in 0..16 {
        let mut solver = Solver::<B64>::new(&context);
        solver.add_event(Event::Merge(iteration, 2, isla_lib::source_loc::SourceLoc::unknown()));
        writer.capture(&checkpoint(&mut solver));
    }
    assert_eq!(writer.segments.len(), 16);
}

#[test]
#[should_panic(expected = "枚举")]
fn 名字环境不能遗漏生产者编号范围内的枚举() {
    let shared = environment();
    let mut saved = NameEnvironment::capture(&shared.symtab, &shared.type_info);
    saved.enums.clear();
    saved.validate(&shared.symtab, &shared.type_info);
}
