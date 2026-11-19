//! 结构检查只核对快照的可重建性，不复核当前 IR 语义。
use super::{event::*, expr::*, value::*, *};
use crate::{bitvector::BV, ir::Name};
use std::collections::{HashMap, HashSet};

struct Validator<'a> {
    names: &'a NameEnvironment,
    constants: HashSet<u32>,
    functions: HashSet<u32>,
    max_used: Option<u32>,
}
impl Validator<'_> {
    fn used(&mut self, symbol: u32) {
        self.max_used = Some(self.max_used.map_or(symbol, |m| m.max(symbol)));
    }
    fn constant(&mut self, symbol: u32) {
        assert!(self.constants.contains(&symbol), "缓存引用未声明的常量 v{symbol}");
        self.used(symbol);
    }
    fn function(&mut self, symbol: u32) {
        assert!(self.functions.contains(&symbol), "缓存引用未声明的函数 v{symbol}");
        self.used(symbol);
    }
    fn name(&self, name: Name) {
        assert!((name.as_u32() as usize) < self.names.symbols.len(), "缓存名字编号越界：{name}");
    }
    fn member(&self, member: &Member) {
        let (_, members) = self.names.enums.iter().find(|(n, _)| *n == member.enum_id).expect("缓存枚举类型缺失");
        assert!(member.member < members.len() as u64, "缓存枚举成员越界");
    }
    fn ty(&self, ty: &Ty) {
        match ty {
            Ty::Enum(n) => {
                assert!(self.names.enums.iter().any(|(name, _)| name == n), "缓存枚举类型缺失");
            }
            Ty::Array(a, b) => {
                self.ty(a);
                self.ty(b);
            }
            _ => (),
        }
    }
    fn exp(&mut self, exp: &Exp) {
        match exp {
            Exp::Var(field0) => {
                self.constant(*field0);
            }
            Exp::Bits(..) => {}
            Exp::Bits64(..) => {}
            Exp::Enum(field0) => {
                self.member(field0);
            }
            Exp::Bool(..) => {}
            Exp::Eq(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Neq(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::And(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Or(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Not(field0) => {
                self.exp(field0);
            }
            Exp::Bvnot(field0) => {
                self.exp(field0);
            }
            Exp::Bvand(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvor(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvxor(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvnand(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvnor(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvxnor(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvneg(field0) => {
                self.exp(field0);
            }
            Exp::Bvadd(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvsub(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvmul(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvudiv(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvsdiv(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvurem(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvsrem(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvsmod(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvult(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvslt(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvule(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvsle(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvuge(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvsge(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvugt(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvsgt(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Extract(_, _, field2) => {
                self.exp(field2);
            }
            Exp::ZeroExtend(_, field1) => {
                self.exp(field1);
            }
            Exp::SignExtend(_, field1) => {
                self.exp(field1);
            }
            Exp::Bvshl(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvlshr(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Bvashr(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Concat(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Ite(field0, field1, field2) => {
                self.exp(field0);
                self.exp(field1);
                self.exp(field2);
            }
            Exp::App(field0, field1) => {
                self.function(*field0);
                for item in field1 {
                    self.exp(item);
                }
            }
            Exp::Select(field0, field1) => {
                self.exp(field0);
                self.exp(field1);
            }
            Exp::Store(field0, field1, field2) => {
                self.exp(field0);
                self.exp(field1);
                self.exp(field2);
            }
            Exp::Distinct(field0) => {
                for item in field0 {
                    self.exp(item);
                }
            }
            Exp::FPConstant(..) => {}
            Exp::FPRoundingMode(..) => {}
            Exp::FPUnary(_, field1) => {
                self.exp(field1);
            }
            Exp::FPRoundingUnary(_, field1, field2) => {
                self.exp(field1);
                self.exp(field2);
            }
            Exp::FPBinary(_, field1, field2) => {
                self.exp(field1);
                self.exp(field2);
            }
            Exp::FPRoundingBinary(_, field1, field2, field3) => {
                self.exp(field1);
                self.exp(field2);
                self.exp(field3);
            }
            Exp::FPfma(field0, field1, field2, field3) => {
                self.exp(field0);
                self.exp(field1);
                self.exp(field2);
                self.exp(field3);
            }
        }
    }
    fn assumeexp(&mut self, exp: &AssumeExp) {
        match exp {
            AssumeExp::Var(..) => {}
            AssumeExp::Bits(..) => {}
            AssumeExp::Bits64(..) => {}
            AssumeExp::Enum(field0) => {
                self.member(field0);
            }
            AssumeExp::Bool(..) => {}
            AssumeExp::Eq(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Neq(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::And(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Or(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Not(field0) => {
                self.assumeexp(field0);
            }
            AssumeExp::Bvnot(field0) => {
                self.assumeexp(field0);
            }
            AssumeExp::Bvand(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvor(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvxor(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvnand(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvnor(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvxnor(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvneg(field0) => {
                self.assumeexp(field0);
            }
            AssumeExp::Bvadd(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvsub(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvmul(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvudiv(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvsdiv(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvurem(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvsrem(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvsmod(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvult(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvslt(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvule(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvsle(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvuge(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvsge(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvugt(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvsgt(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Extract(_, _, field2) => {
                self.assumeexp(field2);
            }
            AssumeExp::ZeroExtend(_, field1) => {
                self.assumeexp(field1);
            }
            AssumeExp::SignExtend(_, field1) => {
                self.assumeexp(field1);
            }
            AssumeExp::Bvshl(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvlshr(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Bvashr(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Concat(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Ite(field0, field1, field2) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
                self.assumeexp(field2);
            }
            AssumeExp::App(field0, field1) => {
                self.function(*field0);
                for item in field1 {
                    self.assumeexp(item);
                }
            }
            AssumeExp::Select(field0, field1) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
            }
            AssumeExp::Store(field0, field1, field2) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
                self.assumeexp(field2);
            }
            AssumeExp::Distinct(field0) => {
                for item in field0 {
                    self.assumeexp(item);
                }
            }
            AssumeExp::FPConstant(..) => {}
            AssumeExp::FPRoundingMode(..) => {}
            AssumeExp::FPUnary(_, field1) => {
                self.assumeexp(field1);
            }
            AssumeExp::FPRoundingUnary(_, field1, field2) => {
                self.assumeexp(field1);
                self.assumeexp(field2);
            }
            AssumeExp::FPBinary(_, field1, field2) => {
                self.assumeexp(field1);
                self.assumeexp(field2);
            }
            AssumeExp::FPRoundingBinary(_, field1, field2, field3) => {
                self.assumeexp(field1);
                self.assumeexp(field2);
                self.assumeexp(field3);
            }
            AssumeExp::FPfma(field0, field1, field2, field3) => {
                self.assumeexp(field0);
                self.assumeexp(field1);
                self.assumeexp(field2);
                self.assumeexp(field3);
            }
        }
    }

    fn value<B: BV>(&mut self, value: &Val<B>) {
        match value {
            Val::Guarded(guard, values) => {
                self.constant(*guard);
                self.value(&values.0);
                self.value(&values.1);
            }
            Val::Symbolic(s) => self.constant(*s),
            Val::MixedBits(parts) => {
                for p in parts {
                    match p {
                        BitsSegment::Symbolic(s) => self.constant(*s),
                        BitsSegment::Concrete(b) => assert!(b.len() <= B::MAX_WIDTH, "缓存位串长度越界"),
                    }
                }
            }
            Val::Bits(b) => assert!(b.len() <= B::MAX_WIDTH, "缓存位串长度越界"),
            Val::Enum(m) => self.member(m),
            Val::Vector(v) | Val::List(v) => {
                for item in v {
                    self.value(item);
                }
            }
            Val::Struct(fields) => {
                let mut seen = HashSet::new();
                for (n, v) in fields {
                    assert!(seen.insert(*n), "缓存结构体字段重复");
                    self.name(*n);
                    self.value(v);
                }
            }
            Val::Ctor(n, v) => {
                self.name(*n);
                self.value(v);
            }
            Val::SymbolicCtor(s, fields) => {
                self.constant(*s);
                let mut seen = HashSet::new();
                for (n, v) in fields {
                    assert!(seen.insert(*n), "缓存构造子重复");
                    self.name(*n);
                    self.value(v);
                }
            }
            Val::Ref(n) => self.name(*n),
            Val::I64(_) | Val::I128(_) | Val::Bool(_) | Val::String(_) | Val::Unit | Val::Poison => (),
        }
    }
    fn event<B: BV>(&mut self, event: &Event<B>) {
        match event {
            Event::Smt(def, attrs, _) => {
                assert_eq!(attrs.bits & !3, 0, "缓存定义属性包含未知位");
                match def {
                    Def::DeclareConst(s, t) => {
                        self.ty(t);
                        assert!(!self.functions.contains(s) && self.constants.insert(*s), "缓存符号重复定义");
                        self.used(*s);
                    }
                    Def::DeclareFun(s, args, result) => {
                        for ty in args {
                            self.ty(ty);
                        }
                        self.ty(result);
                        assert!(!self.constants.contains(s) && self.functions.insert(*s), "缓存函数重复声明");
                        self.used(*s);
                    }
                    Def::DefineConst(s, e) => {
                        self.exp(e);
                        assert!(!self.functions.contains(s) && self.constants.insert(*s), "缓存符号重复定义");
                        self.used(*s);
                    }
                    Def::DefineEnum(n, size) => {
                        let (_, members) =
                            self.names.enums.iter().find(|(name, _)| name == n).expect("缓存枚举类型缺失");
                        assert_eq!(*size, members.len() as u64, "缓存 DefineEnum 大小不一致");
                    }
                    Def::Assert(e) => self.exp(e),
                }
            }
            Event::Fork(_, s, _, _) => self.constant(*s),
            Event::Function { name, .. } => self.name(*name),
            Event::Abstract { name, args, return_value, .. }
            | Event::AssumeFun { name, args, return_value }
            | Event::UseFunAssumption { name, args, return_value } => {
                self.name(*name);
                for v in args {
                    self.value(v);
                }
                self.value(return_value);
            }
            Event::ReadReg(n, accessors, v) | Event::WriteReg(n, accessors, v) | Event::AssumeReg(n, accessors, v) => {
                self.name(*n);
                for a in accessors {
                    let crate::smt::Accessor::Field(n) = a;
                    self.name(*n);
                }
                self.value(v);
            }
            Event::ReadMem { value, read_kind, address, tag_value, .. } => {
                self.value(value);
                self.value(read_kind);
                self.value(address);
                if let Some(v) = tag_value {
                    self.value(v);
                }
            }
            Event::WriteMem { value, write_kind, address, data, tag_value, .. } => {
                self.constant(*value);
                self.value(write_kind);
                self.value(address);
                self.value(data);
                if let Some(v) = tag_value {
                    self.value(v);
                }
            }
            Event::MarkReg { regs, .. } => {
                for n in regs {
                    self.name(*n);
                }
            }
            Event::AddressAnnounce { address } | Event::Branch { address } | Event::Instr(address) => {
                self.value(address)
            }
            Event::Assume(e) => self.assumeexp(e),
            Event::Cycle | Event::Merge(..) => (),
        }
    }
}

pub fn validate_paths<B: BV>(
    segments: &[Segment<B>],
    paths: &[CachedPath<B>],
    names: &NameEnvironment,
    pre_state: &[(Name, Val<B>)],
    pma: &[(String, u32)],
) {
    // 先验证全部段，包括没有路径引用的段。
    let reader = TraceReader::new(segments);
    let mut signatures = HashSet::new();
    for path in paths {
        assert!(signatures.insert(path.signature), "缓存路径签名重复");
        for (start, end) in &path.pure_definitions {
            assert!(start < end && *end < path.checkpoint.next_var, "缓存纯计算定义区间无效");
        }
        let checkpoint = reader.restore(&path.checkpoint);
        drop(checkpoint);
        let mut chain = Vec::new();
        let mut next = path.checkpoint.leaf;
        while let Some(id) = next {
            let segment = &segments[id as usize];
            chain.push(segment);
            next = segment.parent;
        }
        let mut validator = Validator { names, constants: HashSet::new(), functions: HashSet::new(), max_used: None };
        for segment in chain.iter().rev() {
            for event in &segment.events {
                validator.event(event);
            }
        }
        for value in path.path.pre.values().chain(path.path.post.values()).chain(std::iter::once(&path.path.result)) {
            validator.value(value);
        }
        for event in &path.path.memory {
            assert!(matches!(event, Event::ReadMem { .. } | Event::WriteMem { .. }), "缓存路径包含非访存事件");
            validator.event(event);
        }
        let mut indices = HashSet::new();
        for (i, g) in &path.path.memory_guards {
            assert!(indices.insert(*i), "缓存访存条件索引重复");
            assert!(*i < path.path.memory.len() as u64, "缓存访存条件索引越界");
            validator.exp(g);
        }
        let records = path.records.iter().map(|r| (r.record_id, r)).collect::<HashMap<_, _>>();
        assert_eq!(records.len(), path.records.len(), "缓存记录编号重复");
        for record in &path.records {
            validator.name(record.function);
            validator.constant(record.condition);
            let mut seen = HashSet::new();
            let mut next = Some(record.record_id);
            while let Some(id) = next {
                assert!(seen.insert(id), "缓存父记录成环");
                next = records.get(&id).expect("缓存父记录不存在").parent_record;
            }
            assert_eq!(record.parent_record.is_none(), matches!(record.arm, Arm::Root), "缓存记录臂与父记录不一致");
            for s in record.value_symbols.iter().chain(&record.input_symbols) {
                validator.constant(*s);
            }
            for read in &record.single_arm_reads {
                validator.name(read.register);
                for accessor in &read.accessor {
                    let crate::smt::Accessor::Field(name) = accessor;
                    validator.name(*name);
                }
                validator.value(&read.value);
                validator.exp(&read.guard);
            }
            for (i, g, e) in &record.memory_reads {
                assert!(*i < path.path.memory.len() as u64, "缓存记录访存索引越界");
                assert!(matches!(e, Event::ReadMem { .. } | Event::WriteMem { .. }), "缓存记录不是访存事件");
                validator.exp(g);
                validator.event(e);
            }
        }
        let mut pre_names = HashSet::new();
        for (n, v) in pre_state {
            assert!(pre_names.insert(*n), "缓存前态名字重复");
            validator.name(*n);
            validator.value(v);
        }
        let mut pma_names = HashSet::new();
        for (n, s) in pma {
            assert!(pma_names.insert(n), "缓存 PMA 名字重复");
            validator.constant(*s);
        }
        if let Some(max) = validator.max_used {
            assert!(path.checkpoint.next_var > max, "缓存 next_var 未超过已用 Sym：{max}");
        }
    }
}
