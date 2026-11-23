//! 固定输入与人工核对的预期文件互为独立对照，不读取真实 IR。
mod path_cache_common;

use isla_lib::{
    bitvector::{b64::B64, BV},
    executor::{
        path_cache::{self as cache, CachedPath, Facts, Segment, TraceReader, TraceWriter},
        samples::{fast::FastFacts, SamplePath},
        GuardedRegisterRead, RegionMergeRecord, RegionRecordOutcome,
    },
    ir::{regions::RegionPoint, BitsSegment, SharedState, Symtab, Val},
    smt::{
        self, checkpoint,
        smtlib::{Def, Exp, Ty},
        Checkpoint, Config, Context, EnumMember, Event, ReadOpts, Solver, WriteOpts,
    },
    source_loc::SourceLoc,
};
use path_cache_common::validate_cache;
use serde::Serialize;
use std::{
    collections::{BTreeMap, HashSet},
    io::{self, Write},
    sync::Arc,
};

struct Path {
    signature: u64,
    checkpoint: Checkpoint<B64>,
    path: SamplePath<B64>,
    records: Vec<RegionMergeRecord<B64>>,
    facts: FastFacts,
}

fn fixture() -> (SharedState<'static, B64>, Vec<Path>) {
    smt::configure_tastic(smt::Tactic::Qfaufbv);
    let mut symtab = Symtab::new();
    // 内置名字占 0..25；这些断言把预期文件中的名字编号固定下来。
    let names = ["kind", "first", "second", "constructor", "field", "function", "register"].map(|n| symtab.intern(n));
    assert_eq!(names.map(|n| n.as_u32()), [25, 26, 27, 28, 29, 30, 31]);
    let [kind, first, second, constructor, field, function, register] = names;
    let mut shared = SharedState::empty(symtab);
    shared.type_info.enums.insert(kind, vec![first, second]);
    shared.type_info.enum_members.insert(first, (0, 2, kind));
    shared.type_info.enum_members.insert(second, (1, 2, kind));
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let loc = SourceLoc::unknown();
    // DefineEnum 为两个成员分配 v0/v1；后续自由符号从 v2 开始。
    let enumeration = solver.get_enum(kind, 2);
    let input = solver.declare_const(Ty::BitVec(8), loc); // v2
    let condition = solver.declare_const(Ty::Bool, loc); // v3
    let fun = solver.fresh(); // v4
    solver.add(Def::DeclareFun(fun, vec![Ty::BitVec(8)], Ty::BitVec(8)));
    solver.set_def_attrs(smt::DefAttrs::uninteresting());
    let result = solver.define_const(Exp::App(fun, vec![Exp::Var(input)]), loc); // v5，属性位为 1
    solver.clear_def_attrs();
    let member = EnumMember { enum_id: enumeration, member: 1 };
    let enum_symbol = solver.define_const(Exp::Enum(member), loc); // v6
    assert_eq!([input, condition, fun, result, enum_symbol].map(|v| v.as_u32()), [2, 3, 4, 5, 6]);
    solver.assert(Exp::Eq(Box::new(Exp::Var(input)), Box::new(Exp::Bits64(B64::new(7, 8)))));
    let read = Event::ReadMem {
        value: Val::Symbolic(result),
        read_kind: Val::Unit,
        address: Val::Bits(B64::new(16, 64)),
        bytes: 1,
        tag_value: Some(Val::Bool(true)),
        opts: ReadOpts::exclusive(),
        region: "golden",
    };
    let write = Event::WriteMem {
        value: condition,
        write_kind: Val::Unit,
        address: Val::Bits(B64::new(17, 64)),
        data: Val::Symbolic(input),
        bytes: 1,
        tag_value: None,
        opts: WriteOpts::exclusive(),
        region: "golden",
    };
    solver.add_event(Event::ReadReg(register, vec![], Val::Ctor(constructor, Box::new(Val::Enum(member)))));
    solver.add_event(read.clone());
    solver.add_event(write.clone());
    solver.add_event(Event::Cycle);
    let parent = checkpoint(&mut solver); // 段 0：上述 11 个事件。
    let empty = checkpoint(&mut solver); // 段 1：父段 0，事件为空。
    let mut branch = Solver::from_checkpoint(&context, parent);
    branch.assert(Exp::Var(condition));
    let branch = checkpoint(&mut branch); // 段 2：父段 0，仅 Assert(v3)。
    let path = SamplePath {
        terminal: Default::default(),
        pre: BTreeMap::from([
            ("bits".into(), Val::Bits(B64::new(7, 8))),
            ("bool".into(), Val::Bool(true)),
            ("ctor".into(), Val::Ctor(constructor, Box::new(Val::Enum(member)))),
            ("enum".into(), Val::Enum(member)),
            ("i128".into(), Val::I128(3)),
            ("i64".into(), Val::I64(-2)),
            ("list".into(), Val::List(vec![Val::Unit])),
            (
                "mixed".into(),
                Val::MixedBits(vec![BitsSegment::Concrete(B64::new(10, 4)), BitsSegment::Symbolic(input)]),
            ),
            ("string".into(), Val::String("字".into())),
            ("struct".into(), Val::Struct([(field, Val::Bool(false))].into_iter().collect())),
            ("symbolic".into(), Val::Symbolic(input)),
            ("symbolic_ctor".into(), Val::SymbolicCtor(input, [(constructor, Val::Unit)].into_iter().collect())),
            ("unit".into(), Val::Unit),
            ("vector".into(), Val::Vector(vec![Val::Unit])),
        ]),
        post: BTreeMap::from([("enum".into(), Val::Symbolic(enum_symbol)), ("result".into(), Val::Symbolic(result))]),
        result: Val::Ctor(constructor, Box::new(Val::Enum(member))),
        memory: vec![read.clone(), write],
        memory_guards: BTreeMap::from([(0, Exp::Var(condition)), (1, Exp::Not(Box::new(Exp::Var(condition))))]),
    };
    let records = [(10, None, "root"), (20, Some(10), "then"), (30, Some(10), "else")]
        .into_iter()
        .map(|(id, parent, arm)| RegionMergeRecord {
            record_id: id,
            parent_record: parent,
            arm,
            function,
            branch_pc: 4,
            join: RegionPoint::FunctionExit,
            condition,
            source_loc: loc,
            depth: usize::from(parent.is_some()),
            outcome: if arm == "else" { RegionRecordOutcome::Dead } else { RegionRecordOutcome::Merged },
            value_symbols: Arc::new(HashSet::from([result])),
            input_symbols: Arc::new(HashSet::from([input, condition])),
            single_arm_reads: if parent.is_none() {
                vec![GuardedRegisterRead {
                    register,
                    accessor: vec![],
                    value: Val::Symbolic(input),
                    guard: Exp::Var(condition),
                }]
                .into()
            } else {
                Arc::default()
            },
            memory_reads: if parent.is_none() {
                vec![(0, Exp::Var(condition), read.clone())].into()
            } else {
                Arc::default()
            },
        })
        .collect();
    let small = SamplePath {
        terminal: Default::default(),
        pre: BTreeMap::from([("input".into(), Val::Symbolic(input))]),
        post: BTreeMap::new(),
        result: Val::Bool(false),
        memory: vec![],
        memory_guards: BTreeMap::new(),
    };
    (
        shared,
        vec![
            Path {
                signature: 11,
                checkpoint: empty,
                path,
                records,
                facts: Facts { guard_unique: true, post_unique: false, simple_pre: false }.into(),
            },
            Path {
                signature: 22,
                checkpoint: branch,
                path: small,
                records: vec![],
                facts: Facts { guard_unique: false, post_unique: true, simple_pre: true }.into(),
            },
        ],
    )
}

fn capture(paths: &[Path]) -> (Vec<Segment<B64>>, Vec<CachedPath<B64>>) {
    let mut writer = TraceWriter::default();
    let paths = paths
        .iter()
        .map(|p| CachedPath {
            pure_definitions: vec![],
            signature: p.signature,
            checkpoint: writer.capture(&p.checkpoint),
            path: p.path.clone().into(),
            records: p.records.iter().cloned().map(Into::into).collect(),
            facts: p.facts.clone().into(),
        })
        .collect();
    (writer.segments, paths)
}

// 只控制测试文件的空白：前四层换行，深层事件和值紧凑排版，所有字段照常交给 serde。
#[derive(Default)]
struct Readable {
    filled: Vec<bool>,
}
impl Readable {
    fn line(&self, writer: &mut impl Write) -> io::Result<()> {
        if self.filled.len() <= 4 {
            writer.write_all(b"\n")?;
            for _ in 0..self.filled.len() {
                writer.write_all(b"  ")?;
            }
        }
        Ok(())
    }
}
impl serde_json::ser::Formatter for Readable {
    fn begin_array<W: ?Sized + Write>(&mut self, w: &mut W) -> io::Result<()> {
        self.filled.push(false);
        w.write_all(b"[")
    }
    fn end_array<W: ?Sized + Write>(&mut self, mut w: &mut W) -> io::Result<()> {
        if self.filled.pop().unwrap() && self.filled.len() < 4 {
            self.line(&mut w)?;
        }
        w.write_all(b"]")
    }
    fn begin_object<W: ?Sized + Write>(&mut self, w: &mut W) -> io::Result<()> {
        self.filled.push(false);
        w.write_all(b"{")
    }
    fn end_object<W: ?Sized + Write>(&mut self, mut w: &mut W) -> io::Result<()> {
        if self.filled.pop().unwrap() && self.filled.len() < 4 {
            self.line(&mut w)?;
        }
        w.write_all(b"}")
    }
    fn begin_array_value<W: ?Sized + Write>(&mut self, mut w: &mut W, first: bool) -> io::Result<()> {
        if !first {
            w.write_all(b",")?;
        }
        *self.filled.last_mut().unwrap() = true;
        self.line(&mut w)
    }
    fn begin_object_key<W: ?Sized + Write>(&mut self, mut w: &mut W, first: bool) -> io::Result<()> {
        if !first {
            w.write_all(b",")?;
        }
        *self.filled.last_mut().unwrap() = true;
        self.line(&mut w)
    }
    fn begin_object_value<W: ?Sized + Write>(&mut self, w: &mut W) -> io::Result<()> {
        w.write_all(b":")
    }
}
fn json_file(value: &impl Serialize) -> Vec<u8> {
    let mut bytes = Vec::new();
    value.serialize(&mut serde_json::Serializer::with_formatter(&mut bytes, Readable::default())).unwrap();
    bytes.push(b'\n');
    bytes
}

#[test]
fn 正向序列化逐字节符合预期文件() {
    let (shared, paths) = fixture();
    let (segments, paths) = capture(&paths);
    let names = cache::NameEnvironment::capture(&shared.symtab, &shared.type_info);
    validate_cache(&segments, &paths, &names, &[]);
    assert_eq!(json_file(&segments), include_bytes!("path_cache_golden/segments.json"));
    assert_eq!(json_file(&paths), include_bytes!("path_cache_golden/paths.json"));
}

fn assert_event(left: &Event<B64>, right: &Event<B64>) {
    match (left, right) {
        (Event::Smt(a, aa, al), Event::Smt(b, ba, bl)) => {
            assert_eq!(al, bl);
            assert_eq!(format!("{aa:?}"), format!("{ba:?}"));
            match (a, b) {
                (Def::DeclareConst(x, t), Def::DeclareConst(y, u)) => {
                    assert_eq!(x, y);
                    assert_eq!(format!("{t:?}"), format!("{u:?}"));
                }
                (Def::DeclareFun(x, a, t), Def::DeclareFun(y, b, u)) => {
                    assert_eq!(x, y);
                    assert_eq!(format!("{a:?}"), format!("{b:?}"));
                    assert_eq!(format!("{t:?}"), format!("{u:?}"));
                }
                (Def::DefineConst(x, e), Def::DefineConst(y, f)) => {
                    assert_eq!(x, y);
                    assert_eq!(e, f);
                }
                (Def::DefineEnum(x, n), Def::DefineEnum(y, m)) => {
                    assert_eq!(x, y);
                    assert_eq!(n, m);
                }
                (Def::Assert(e), Def::Assert(f)) => assert_eq!(e, f),
                _ => panic!("预期文件重建出了不同的 SMT 定义种类"),
            }
        }
        (Event::ReadReg(a, b, c), Event::ReadReg(d, e, f)) => {
            assert_eq!(a, d);
            assert_eq!(b, e);
            assert_eq!(c, f);
        }
        (
            Event::ReadMem { value: a, read_kind: b, address: c, bytes: d, tag_value: e, opts: f, region: g },
            Event::ReadMem { value: h, read_kind: i, address: j, bytes: k, tag_value: l, opts: m, region: n },
        ) => {
            assert_eq!((a, b, c, d, e, g), (h, i, j, k, l, n));
            assert_eq!(f.is_exclusive, m.is_exclusive);
            assert_eq!(f.is_ifetch, m.is_ifetch);
        }
        (
            Event::WriteMem {
                value: a,
                write_kind: b,
                address: c,
                data: d,
                bytes: e,
                tag_value: f,
                opts: g,
                region: h,
            },
            Event::WriteMem {
                value: i,
                write_kind: j,
                address: k,
                data: l,
                bytes: m,
                tag_value: n,
                opts: o,
                region: p,
            },
        ) => {
            assert_eq!((a, b, c, d, e, f, h), (i, j, k, l, m, n, p));
            assert_eq!(g.is_exclusive(), o.is_exclusive());
        }
        (Event::Cycle, Event::Cycle) => (),
        _ => panic!("预期文件重建出了不同的事件种类"),
    }
}

#[test]
fn 反向预期文件重建核心字段及_dag_一致() {
    let segments: Vec<Segment<B64>> =
        serde_json::from_slice(include_bytes!("path_cache_golden/segments.json")).unwrap();
    let paths: Vec<CachedPath<B64>> = serde_json::from_slice(include_bytes!("path_cache_golden/paths.json")).unwrap();
    // bin 只核对同一份预期 DTO 的往返，不维护二进制预期文件。
    assert_eq!(
        (segments.clone(), paths.clone()),
        bincode::deserialize(&bincode::serialize(&(segments.clone(), paths.clone())).unwrap()).unwrap()
    );
    let (shared, originals) = fixture();
    let names = cache::NameEnvironment::capture(&shared.symtab, &shared.type_info);
    validate_cache(&segments, &paths, &names, &[]);
    assert_eq!(originals.len(), paths.len());
    let reader = TraceReader::new(&segments);
    let restored = paths
        .into_iter()
        .map(|p| Path {
            signature: p.signature,
            checkpoint: reader.restore(&p.checkpoint),
            path: p.path.into(),
            records: p.records.into_iter().map(Into::into).collect(),
            facts: p.facts.into(),
        })
        .collect::<Vec<_>>();
    // 再导出仍为三个段，证明两条路径的父节点共享且空段没有丢失。
    let (again, points) = capture(&restored);
    assert_eq!(again, segments);
    assert_eq!(again.len(), 3);
    assert!(again[1].events.is_empty());
    assert_eq!((again[1].parent, again[2].parent), (Some(0), Some(0)));
    assert!(points.iter().all(|p| p.checkpoint.num == 2 && p.checkpoint.next_var == 7));
    let context = Context::new(Config::new());
    for (a, b) in originals.iter().zip(&restored) {
        assert_eq!(a.signature, b.signature);
        assert_eq!(
            (&a.path.pre, &a.path.post, &a.path.result, &a.path.memory_guards),
            (&b.path.pre, &b.path.post, &b.path.result, &b.path.memory_guards)
        );
        assert_eq!(a.path.memory.len(), b.path.memory.len());
        for (x, y) in a.path.memory.iter().zip(&b.path.memory) {
            assert_event(x, y);
        }
        assert_eq!(serde_json::to_value(&a.facts).unwrap(), serde_json::to_value(&b.facts).unwrap());
        assert_eq!(a.records.len(), b.records.len());
        for (x, y) in a.records.iter().zip(&b.records) {
            assert_eq!(
                (
                    x.record_id,
                    x.parent_record,
                    x.arm,
                    x.function,
                    x.branch_pc,
                    x.join,
                    x.condition,
                    x.source_loc,
                    x.depth,
                    x.outcome
                ),
                (
                    y.record_id,
                    y.parent_record,
                    y.arm,
                    y.function,
                    y.branch_pc,
                    y.join,
                    y.condition,
                    y.source_loc,
                    y.depth,
                    y.outcome
                )
            );
            assert_eq!((&x.value_symbols, &x.input_symbols), (&y.value_symbols, &y.input_symbols));
            assert_eq!(x.single_arm_reads.len(), y.single_arm_reads.len());
            for (u, v) in x.single_arm_reads.iter().zip(y.single_arm_reads.iter()) {
                assert_eq!(
                    (&u.register, &u.accessor, &u.value, &u.guard),
                    (&v.register, &v.accessor, &v.value, &v.guard)
                );
            }
            assert_eq!(x.memory_reads.len(), y.memory_reads.len());
            for ((i, g, e), (j, h, f)) in x.memory_reads.iter().zip(y.memory_reads.iter()) {
                assert_eq!((i, g), (j, h));
                assert_event(e, f);
            }
        }
        let left = Solver::from_checkpoint(&context, a.checkpoint.clone());
        let right = Solver::from_checkpoint(&context, b.checkpoint.clone());
        let left_events = left.trace().to_vec();
        let right_events = right.trace().to_vec();
        assert_eq!(left_events.len(), right_events.len());
        for (x, y) in left_events.iter().zip(right_events) {
            assert_event(x, y);
        }
        assert_eq!(
            serde_json::to_vec(&a.path.export_dag(&left, &shared, &a.records, a.signature)).unwrap(),
            serde_json::to_vec(&b.path.export_dag(&right, &shared, &b.records, b.signature)).unwrap()
        );
    }
}
