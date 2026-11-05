//! 路径终态的具体样本与增量成员检查；不依赖 ISA 字段名。

use crate::bitvector::{b64::B64, BV};
use crate::error::ExecError;
use crate::ir::{SharedState, Val};
use crate::primop::eq_anything;
use crate::primop_util::smt_value;
use crate::smt::smtlib::Exp;
use crate::smt::{Event, Model, SmtResult, Solver, Sym};
use crate::source_loc::SourceLoc;
use crate::zencode;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::io::{BufRead, Write};
use std::sync::Mutex;

fn concrete_bits<B: BV>(value: B) -> Value {
    json!({"bits": (0..value.len()).rev().map(|i| if value.slice(i,1).unwrap().lower_u64()==1 {'1'} else {'0'}).collect::<String>()})
}

/// 使用解码后的名字传递复合值，禁止把跨路径 SMT 变量编号当成输入。
fn encode<B: BV>(value: &Val<B>, shared: &SharedState<B>) -> Value {
    let name = |id| zencode::decode(shared.symtab.to_str(id));
    match value {
        Val::Unit => json!({"unit":true}),
        Val::Bool(value) => json!({"bool":value}),
        Val::Bits(value) => concrete_bits(*value),
        Val::I64(value) => json!({"i64":value.to_string()}),
        Val::I128(value) => json!({"i128":value.to_string()}),
        Val::String(value) => json!({"string":value}),
        Val::Enum(value) => json!({"enum":name(value.to_name(shared))}),
        Val::Ctor(id, value) => json!({"ctor":name(*id),"value":encode(value,shared)}),
        Val::Struct(fields) => {
            json!({"struct":fields.iter().map(|(id,value)|(name(*id),encode(value,shared))).collect::<BTreeMap<_,_>>()})
        }
        Val::Vector(values) => json!({"vector":values.iter().map(|v|encode(v,shared)).collect::<Vec<_>>()}),
        Val::List(values) => json!({"list":values.iter().map(|v|encode(v,shared)).collect::<Vec<_>>()}),
        value => panic!("样本必须是完整具体值：{value:?}"),
    }
}

/// 直接物化 SMT 位串，保留超过 BV 容量的向量寄存器；不收窄或截位。
fn materialized<B: BV>(value: &Val<B>, model: &mut Model<B>, shared: &SharedState<B>) -> Result<Value, ExecError> {
    match value {
        Val::Symbolic(_) | Val::MixedBits(_) => {
            let value = model.get_exp(&smt_value(value, SourceLoc::unknown())?)?.unwrap_exp();
            Ok(match value {
                Exp::Bits(bits) => {
                    json!({"bits":bits.iter().rev().map(|bit|if *bit {'1'} else {'0'}).collect::<String>()})
                }
                Exp::Bits64(bits) => concrete_bits(bits),
                Exp::Bool(value) => json!({"bool":value}),
                Exp::Enum(value) => encode(&Val::<B>::Enum(value), shared),
                value => panic!("样本标量必须具体：{value:?}"),
            })
        }
        Val::Struct(fields) => Ok(
            json!({"struct":fields.iter().map(|(name,value)|Ok((zencode::decode(shared.symtab.to_str(*name)),materialized(value,model,shared)?))).collect::<Result<BTreeMap<_,_>,ExecError>>()?}),
        ),
        Val::Ctor(name, value) => {
            Ok(json!({"ctor":zencode::decode(shared.symtab.to_str(*name)),"value":materialized(value,model,shared)?}))
        }
        Val::Vector(values) | Val::List(values) => {
            let values =
                values.iter().map(|value| materialized(value, model, shared)).collect::<Result<Vec<_>, _>>()?;
            Ok(if matches!(value, Val::Vector(_)) { json!({"vector":values}) } else { json!({"list":values}) })
        }
        Val::SymbolicCtor(..) => materialized(&model.get_val(value)?, model, shared),
        _ => Ok(encode(value, shared)),
    }
}

fn decode<B: BV>(value: &Value, shared: &SharedState<B>) -> Val<B> {
    let object = value.as_object().expect("样本值必须为对象");
    let name = |text: &Value| shared.symtab.lookup(&zencode::encode(text.as_str().unwrap()));
    let (kind, payload) = object.iter().next().expect("样本值不得为空");
    match kind.as_str() {
        "unit" => Val::Unit,
        "bool" => Val::Bool(payload.as_bool().unwrap()),
        "bits" => {
            let text = payload.as_str().unwrap();
            assert!(!text.is_empty() && text.len() <= B::MAX_WIDTH as usize, "样本位宽超出执行器能力");
            Val::Bits(text.bytes().fold(B::zeros(text.len() as u32), |bits, bit| {
                assert!(bit == b'0' || bit == b'1');
                (bits << B::new(1, text.len() as u32)) | B::new(u64::from(bit == b'1'), text.len() as u32)
            }))
        }
        "i64" => Val::I64(payload.as_str().unwrap().parse().unwrap()),
        "i128" => Val::I128(payload.as_str().unwrap().parse().unwrap()),
        "string" => Val::String(payload.as_str().unwrap().into()),
        "enum" => {
            let member = name(payload);
            let (index, _, id) = shared.type_info.enum_members[&member];
            Val::Enum(crate::smt::EnumMember { enum_id: crate::smt::EnumId::from_name(id), member: index })
        }
        "ctor" => Val::Ctor(name(payload), Box::new(decode(&value["value"], shared))),
        "struct" => Val::Struct(
            payload
                .as_object()
                .unwrap()
                .iter()
                .map(|(key, value)| (name(&json!(key)), decode(value, shared)))
                .collect(),
        ),
        "vector" => Val::Vector(payload.as_array().unwrap().iter().map(|v| decode(v, shared)).collect()),
        "list" => Val::List(payload.as_array().unwrap().iter().map(|v| decode(v, shared)).collect()),
        kind => panic!("未知样本值类型：{kind}"),
    }
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Sample {
    pub schema_version: u32,
    pub sample_id: u64,
    pub mode: String,
    pub path_signature: u64,
    pub class_id: Option<usize>,
    pub truncated: bool,
    pub pre_registers: BTreeMap<String, Value>,
    pub post_registers: BTreeMap<String, Value>,
    /// 与 isa-state 同源的展示值，检查使用上面的保类型值。
    pub isa_state: BTreeMap<String, String>,
    pub pre_memory: Vec<MemoryCell>,
    pub post_memory: Vec<MemoryCell>,
    pub result: Value,
    pub ret_val: String,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MemoryCell {
    pub address: u64,
    pub value: Option<u8>,
    pub bytes: u32,
}

/// 每条访问拆成小端字节；前后内存与 isarch 既有重放规则一致。
pub struct SamplePath<B: BV> {
    pub pre: BTreeMap<String, Val<B>>,
    pub post: BTreeMap<String, Val<B>>,
    pub result: Val<B>,
    pub memory: Vec<Event<B>>,
    /// 主迹访存序号对应的读条件；主迹保留并集，导出/成员检查仅绑定实际臂。
    pub memory_guards: BTreeMap<usize, Exp<Sym>>,
}

fn sat<B: BV>(solver: &mut Solver<B>) -> Result<bool, ExecError> {
    match solver.check_sat(SourceLoc::unknown()) {
        SmtResult::Sat => Ok(true),
        SmtResult::Unsat => Ok(false),
        SmtResult::Unknown => Err(ExecError::Z3Unknown),
        SmtResult::Error(error) => Err(ExecError::Smt(error)),
    }
}

fn equal<B: BV>(
    left: &Val<B>,
    right: &Value,
    shared: &SharedState<B>,
    solver: &mut Solver<B>,
) -> Result<Exp<Sym>, ExecError> {
    if let Some(bits) = right.get("bits") {
        if let Val::Bits(value) = left {
            return Ok(Exp::Bool(concrete_bits(*value) == *right));
        }
        let bits =
            crate::bitvector::bit_vector_from_str(&format!("#b{}", bits.as_str().unwrap())).expect("样本位串无效");
        return Ok(Exp::Eq(Box::new(smt_value(left, SourceLoc::unknown())?), Box::new(Exp::Bits(bits))));
    }
    match left {
        Val::Struct(fields) if right.get("struct").is_some() => {
            let mut condition = Exp::Bool(true);
            let values = right["struct"].as_object().unwrap();
            assert_eq!(fields.len(), values.len(), "样本结构体字段必须完整");
            for (name, value) in fields {
                let key = zencode::decode(shared.symtab.to_str(*name));
                condition = Exp::And(Box::new(condition), Box::new(equal(value, &values[&key], shared, solver)?));
            }
            return Ok(condition);
        }
        Val::Vector(values) | Val::List(values) => {
            let key = if matches!(left, Val::Vector(_)) { "vector" } else { "list" };
            let right = right[key].as_array().unwrap();
            if values.len() != right.len() {
                return Ok(Exp::Bool(false));
            }
            let mut condition = Exp::Bool(true);
            for (left, right) in values.iter().zip(right) {
                condition = Exp::And(Box::new(condition), Box::new(equal(left, right, shared, solver)?));
            }
            return Ok(condition);
        }
        Val::Ctor(name, value) if right.get("ctor").is_some() => {
            if right["ctor"] != zencode::decode(shared.symtab.to_str(*name)) {
                return Ok(Exp::Bool(false));
            }
            return equal(value, &right["value"], shared, solver);
        }
        _ => (),
    }
    if let Val::String(value) = left {
        return Ok(Exp::Bool(right["string"].as_str().unwrap() == value));
    }
    let right = decode(right, shared);
    // eq_anything 沿用复合值、union 与混合位串的既有等式语义。
    if matches!((left, &right), (Val::Unit, Val::Unit)) {
        return Ok(Exp::Bool(true));
    }
    smt_value(&eq_anything(left.clone(), right, solver, SourceLoc::unknown())?, SourceLoc::unknown())
}

fn bytes<B: BV>(event: &Event<B>) -> Vec<(Exp<Sym>, Exp<Sym>, Exp<Sym>, bool)> {
    let info = SourceLoc::unknown();
    let (address, value, count, commit, read) = match event {
        Event::ReadMem { address, value, bytes, .. } => (address, value, *bytes, Exp::Bool(true), true),
        Event::WriteMem { address, data, bytes, value, opts, .. } => {
            (address, data, *bytes, if opts.is_exclusive() { Exp::Var(*value) } else { Exp::Bool(true) }, false)
        }
        _ => panic!("只允许访存事件"),
    };
    let address = smt_value(address, info).unwrap();
    let value = smt_value(value, info).unwrap();
    (0..count)
        .map(|i| {
            (
                Exp::Bvadd(Box::new(address.clone()), Box::new(Exp::Bits64(B64::new(i as u64, 64)))),
                Exp::Extract(8 * i + 7, 8 * i, Box::new(value.clone())),
                commit.clone(),
                read,
            )
        })
        .collect()
}

impl<B: BV> SamplePath<B> {
    fn accesses(&self) -> Vec<(Exp<Sym>, Exp<Sym>, Exp<Sym>, bool)> {
        for index in self.memory_guards.keys() {
            assert!(self.memory.get(*index).expect("读取条件的访存序号必须存在").is_memory_read());
        }
        self.memory
            .iter()
            .enumerate()
            .flat_map(|(index, event)| {
                bytes(event).into_iter().map(move |(address, value, commit, read)| {
                    let commit = match self.memory_guards.get(&index) {
                        Some(guard) => {
                            assert!(read, "带条件的访存必须是读取");
                            Exp::And(Box::new(guard.clone()), Box::new(commit))
                        }
                        None => commit,
                    };
                    (address, value, commit, read)
                })
            })
            .collect()
    }

    pub fn materialize(
        &self,
        model: &mut Model<B>,
        shared: &SharedState<B>,
        mode: &str,
        signature: u64,
        class_id: Option<usize>,
    ) -> Result<Sample, ExecError> {
        model.set_complete_model(true);
        let mut registers = |values: &BTreeMap<String, Val<B>>| -> Result<BTreeMap<String, Value>, ExecError> {
            values.iter().map(|(name, value)| Ok((name.clone(), materialized(value, model, shared)?))).collect()
        };
        let pre_registers = registers(&self.pre)?;
        let post_registers = registers(&self.post)?;
        let mut pre = BTreeMap::new();
        let mut post = BTreeMap::new();
        for (address, value, commit, read) in self.accesses() {
            if !matches!(model.get_exp(&commit)?.unwrap_exp(), Exp::Bool(true)) {
                continue;
            }
            let address = match model.get_exp(&address)?.unwrap_exp() {
                Exp::Bits64(value) => value.lower_u64(),
                value => panic!("地址必须为64位：{value:?}"),
            };
            let value = match model.get_exp(&value)?.unwrap_exp() {
                Exp::Bits64(value) => value.lower_u64() as u8,
                value => panic!("内存必须为字节：{value:?}"),
            };
            pre.entry(address).or_insert(if read { Some(value) } else { None });
            post.insert(address, Some(value));
        }
        let cells = |map: BTreeMap<u64, Option<u8>>| {
            map.into_iter().map(|(address, value)| MemoryCell { address, value, bytes: 1 }).collect()
        };
        let result = materialized(&self.result, model, shared)?;
        Ok(Sample {
            schema_version: 1,
            sample_id: 0,
            mode: mode.into(),
            path_signature: signature,
            class_id,
            truncated: false,
            pre_registers,
            post_registers,
            isa_state: BTreeMap::new(),
            pre_memory: cells(pre),
            post_memory: cells(post),
            result,
            ret_val: self.result.to_string(shared),
        })
    }

    pub fn check(
        &self,
        solver: &mut Solver<B>,
        shared: &SharedState<B>,
        sample: &Sample,
    ) -> Result<Option<bool>, ExecError> {
        assert_eq!(solver.transaction_depth(), 0, "成员检查必须在路径结束后运行");
        let tx = solver.start_transaction_with_guard(Some(Exp::Bool(true)));
        let outcome = (|| {
            for (name, value) in &sample.pre_registers {
                let expr = equal(self.pre.get(name).expect("路径缺少样本前置输入"), value, shared, solver)?;
                match expr {
                    Exp::Bool(true) => (),
                    Exp::Bool(false) => return Ok(None),
                    expr => solver.assert(expr),
                }
            }
            let accesses = self.accesses();
            for (address, value, commit, read) in &accesses {
                if !read {
                    continue;
                }
                let condition = sample.pre_memory.iter().filter_map(|cell| cell.value.map(|byte| (cell, byte))).fold(
                    Exp::Bool(false),
                    |condition, (cell, byte)| {
                        assert_eq!(cell.bytes, 1, "内部内存单元必须按字节规范化");
                        Exp::Or(
                            Box::new(condition),
                            Box::new(Exp::And(
                                Box::new(Exp::Eq(
                                    Box::new(address.clone()),
                                    Box::new(Exp::Bits64(B64::new(cell.address, 64))),
                                )),
                                Box::new(Exp::Eq(
                                    Box::new(value.clone()),
                                    Box::new(Exp::Bits64(B64::new(byte as u64, 8))),
                                )),
                            )),
                        )
                    },
                );
                solver.assert(Exp::Or(Box::new(Exp::Not(Box::new(commit.clone()))), Box::new(condition)));
            }
            if !sat(solver)? {
                return Ok(None);
            }
            let mut checks = Vec::new();
            checks.push(equal(&self.result, &sample.result, shared, solver)?);
            for (name, value) in &sample.post_registers {
                if self.pre.get(name) == self.post.get(name) && sample.pre_registers.get(name) == Some(value) {
                    continue;
                }
                checks.push(equal(self.post.get(name).expect("路径缺少样本后置寄存器"), value, shared, solver)?);
            }
            for cell in &sample.post_memory {
                let byte = cell.value.expect("后置内存必须具体");
                let mut seen = Exp::Bool(false);
                let mut final_value = Exp::Bits64(B64::new(0, 8));
                for (address, value, commit, _) in &accesses {
                    let hit = Exp::And(
                        Box::new(commit.clone()),
                        Box::new(Exp::Eq(Box::new(address.clone()), Box::new(Exp::Bits64(B64::new(cell.address, 64))))),
                    );
                    seen = Exp::Or(Box::new(seen), Box::new(hit.clone()));
                    final_value = Exp::Ite(Box::new(hit), Box::new(value.clone()), Box::new(final_value));
                }
                checks.push(Exp::And(
                    Box::new(seen),
                    Box::new(Exp::Eq(Box::new(final_value), Box::new(Exp::Bits64(B64::new(byte as u64, 8))))),
                ));
            }
            // 后置足迹也必须相等；额外触碰样本之外的字节不能被漏报为一致。
            for (address, _, commit, _) in &accesses {
                let covered = sample.post_memory.iter().fold(Exp::Bool(false), |covered, cell| {
                    Exp::Or(
                        Box::new(covered),
                        Box::new(Exp::Eq(Box::new(address.clone()), Box::new(Exp::Bits64(B64::new(cell.address, 64))))),
                    )
                });
                checks.push(Exp::Or(Box::new(Exp::Not(Box::new(commit.clone()))), Box::new(covered)));
            }
            for condition in checks {
                if let Exp::Bool(known) = condition {
                    if known {
                        continue;
                    } else {
                        return Ok(Some(false));
                    }
                }
                match solver.check_sat_with(&Exp::Not(Box::new(condition)), SourceLoc::unknown()) {
                    SmtResult::Unsat => (),
                    SmtResult::Sat => return Ok(Some(false)),
                    SmtResult::Unknown => return Err(ExecError::Z3Unknown),
                    SmtResult::Error(error) => return Err(ExecError::Smt(error)),
                }
            }
            Ok(Some(true))
        })();
        solver.rollback_transaction(tx);
        outcome
    }
}

pub struct SampleWriter {
    file: Mutex<std::fs::File>,
    next: std::sync::atomic::AtomicU64,
}
impl SampleWriter {
    pub fn open(path: &std::path::Path) -> Self {
        let file =
            std::fs::OpenOptions::new().create(true).read(true).append(true).open(path).expect("打开样本文件失败");
        let mut next = 0;
        for line in std::io::BufReader::new(file.try_clone().unwrap()).lines() {
            let sample: Sample = serde_json::from_str(&line.expect("读取已有样本失败")).expect("已有样本行损坏");
            next = next.max(sample.sample_id.checked_add(1).expect("样本编号溢出"));
        }
        Self { file: Mutex::new(file), next: std::sync::atomic::AtomicU64::new(next) }
    }
    pub fn append(&self, mut sample: Sample) {
        sample.sample_id = self.next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let mut line = serde_json::to_vec(&sample).expect("样本序列化失败");
        line.push(b'\n');
        self.file.lock().unwrap().write_all(&line).expect("追加样本失败");
    }
}

pub struct SampleChecker {
    pub samples: Vec<Sample>,
    counts: Mutex<Vec<(usize, usize, usize)>>,
    inconsistent: Mutex<Vec<(u64, u64)>>,
}
impl SampleChecker {
    pub fn new(samples: Vec<Sample>) -> Self {
        Self { counts: Mutex::new(vec![(0, 0, 0); samples.len()]), samples, inconsistent: Mutex::new(Vec::new()) }
    }
    pub fn load(path: &std::path::Path, limit: Option<usize>) -> Result<Self, String> {
        let file = std::fs::File::open(path).map_err(|error| format!("读取样本失败：{error}"))?;
        let samples = std::io::BufReader::new(file)
            .lines()
            .take(limit.unwrap_or(usize::MAX))
            .enumerate()
            .map(|(line, text)| {
                let sample: Sample = serde_json::from_str(&text.map_err(|error| error.to_string())?)
                    .map_err(|error| format!("样本第{}行：{error}", line + 1))?;
                if sample.schema_version != 1 {
                    return Err("不支持的样本版本".into());
                }
                Ok(sample)
            })
            .collect::<Result<Vec<_>, String>>()?;
        let mut ids = std::collections::HashSet::new();
        for sample in &samples {
            if !ids.insert(sample.sample_id) {
                return Err(format!("重复样本 id：{}", sample.sample_id));
            }
        }
        Ok(Self::new(samples))
    }
    pub fn check_path<B: BV>(
        &self,
        path: &SamplePath<B>,
        solver: &mut Solver<B>,
        shared: &SharedState<B>,
        signature: u64,
    ) -> Result<(), ExecError> {
        for (index, sample) in self.samples.iter().enumerate() {
            if let Some(consistent) = path.check(solver, shared, sample)? {
                let mut counts = self.counts.lock().unwrap();
                counts[index].0 += 1;
                if consistent {
                    counts[index].1 += 1;
                } else {
                    counts[index].2 += 1;
                    self.inconsistent.lock().unwrap().push((sample.sample_id, signature));
                }
            }
        }
        Ok(())
    }
    pub fn report(&self) -> Value {
        let counts = self.counts.lock().unwrap();
        let mut inconsistent = self.inconsistent.lock().unwrap().clone();
        inconsistent.sort();
        json!({"schema_version":1,"sample_total":self.samples.len(),"samples":self.samples.iter().zip(counts.iter()).map(|(sample,(accepted,consistent,inconsistent))|json!({"sample_id":sample.sample_id,"accepted_paths":accepted,"consistent_paths":consistent,"inconsistent_paths":inconsistent})).collect::<Vec<_>>(),"unaccepted_sample_ids":self.samples.iter().zip(counts.iter()).filter(|(_,count)|count.0==0).map(|(sample,_)|sample.sample_id).collect::<Vec<_>>(),"inconsistent":inconsistent})
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::smt::{Config, Context};

    #[test]
    fn samples_membership_and_wrong_result() {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let input = solver.declare_const(crate::smt::smtlib::Ty::Bool, SourceLoc::unknown());
        solver.assert(Exp::Var(input));
        let path = SamplePath {
            pre: BTreeMap::from([("x".into(), Val::Symbolic(input))]),
            post: BTreeMap::new(),
            result: Val::Symbolic(input),
            memory: Vec::new(),
            memory_guards: BTreeMap::new(),
        };
        let shared = crate::ir::SharedState::empty(crate::ir::Symtab::new());
        assert!(sat(&mut solver).unwrap());
        let mut model = Model::new(&mut solver);
        let good = path.materialize(&mut model, &shared, "fork", 1, None).unwrap();
        drop(model);
        assert_eq!(path.check(&mut solver, &shared, &good).unwrap(), Some(true));
        let mut bad = good.clone();
        bad.sample_id = 1;
        bad.pre_registers.insert("x".into(), serde_json::json!({"bool":false}));
        assert_eq!(path.check(&mut solver, &shared, &bad).unwrap(), None);
        let mut wrong = good.clone();
        wrong.sample_id = 2;
        wrong.result = serde_json::json!({"bool":false});
        assert_eq!(path.check(&mut solver, &shared, &wrong).unwrap(), Some(false));
        let checker = SampleChecker::new(vec![good, bad, wrong]);
        checker.check_path(&path, &mut solver, &shared, 9).unwrap();
        let report = checker.report();
        assert_eq!(report["unaccepted_sample_ids"], serde_json::json!([1]));
        assert_eq!(report["inconsistent"].as_array().unwrap().len(), 1);
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
    }
    #[test]
    fn samples_memory_membership_post_and_multithread_jsonl() {
        use std::sync::Arc;
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let value = solver.declare_const(crate::smt::smtlib::Ty::BitVec(16), SourceLoc::unknown());
        let write = solver.declare_const(crate::smt::smtlib::Ty::Bool, SourceLoc::unknown());
        let path = SamplePath {
            pre: BTreeMap::new(),
            post: BTreeMap::new(),
            result: Val::Unit,
            memory_guards: BTreeMap::new(),
            memory: vec![
                Event::ReadMem {
                    value: Val::Symbolic(value),
                    read_kind: Val::Unit,
                    address: Val::Bits(B64::new(4096, 64)),
                    bytes: 2,
                    tag_value: None,
                    opts: Default::default(),
                    region: "mem",
                },
                Event::WriteMem {
                    value: write,
                    write_kind: Val::Unit,
                    address: Val::Bits(B64::new(4097, 64)),
                    data: Val::Bits(B64::new(7, 8)),
                    bytes: 1,
                    tag_value: None,
                    opts: Default::default(),
                    region: "mem",
                },
            ],
        };
        let shared = SharedState::empty(crate::ir::Symtab::new());
        assert!(sat(&mut solver).unwrap());
        let sample = path.materialize(&mut Model::new(&mut solver), &shared, "fork", 1, None).unwrap();
        assert_eq!(path.check(&mut solver, &shared, &sample).unwrap(), Some(true));
        let mut wrong = sample.clone();
        wrong.post_memory[1].value = Some(8);
        assert_eq!(path.check(&mut solver, &shared, &wrong).unwrap(), Some(false));
        let mut absent = sample.clone();
        absent.pre_memory.clear();
        assert_eq!(path.check(&mut solver, &shared, &absent).unwrap(), None);
        let file = std::env::temp_dir().join(format!("e2-lines-{}.jsonl", std::process::id()));
        if file.exists() {
            std::fs::remove_file(&file).unwrap();
        }
        let writer = Arc::new(SampleWriter::open(&file));
        std::thread::scope(|scope| {
            for _ in 0..8 {
                let writer = writer.clone();
                let sample = sample.clone();
                scope.spawn(move || {
                    for _ in 0..32 {
                        writer.append(sample.clone());
                    }
                });
            }
        });
        drop(writer);
        assert_eq!(SampleChecker::load(&file, None).unwrap().samples.len(), 256);
        assert_eq!(SampleChecker::load(&file, Some(10)).unwrap().samples.len(), 10);
        SampleWriter::open(&file).append(sample);
        assert_eq!(SampleChecker::load(&file, None).unwrap().samples.len(), 257, "续写编号不得重复");
        std::fs::remove_file(file).unwrap();
    }

    /// 规格将每次读绑定初始内存；改写后的再次读取无法满足该协议，明确保留证据。
    #[test]
    fn samples_initial_memory_protocol_rejects_read_after_changed_write() {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let written = solver.declare_const(crate::smt::smtlib::Ty::Bool, SourceLoc::unknown());
        let read = |value| Event::ReadMem {
            value: Val::Bits(B64::new(value, 8)),
            read_kind: Val::Unit,
            address: Val::Bits(B64::new(4096, 64)),
            bytes: 1,
            tag_value: None,
            opts: Default::default(),
            region: "mem",
        };
        let path = SamplePath {
            pre: BTreeMap::new(),
            post: BTreeMap::new(),
            result: Val::Unit,
            memory_guards: BTreeMap::new(),
            memory: vec![
                read(0),
                Event::WriteMem {
                    value: written,
                    write_kind: Val::Unit,
                    address: Val::Bits(B64::new(4096, 64)),
                    data: Val::Bits(B64::new(1, 8)),
                    bytes: 1,
                    tag_value: None,
                    opts: Default::default(),
                    region: "mem",
                },
                read(1),
            ],
        };
        let shared = SharedState::empty(crate::ir::Symtab::new());
        assert!(sat(&mut solver).unwrap());
        let sample = path.materialize(&mut Model::new(&mut solver), &shared, "fork", 0, None).unwrap();
        assert_eq!(sample.pre_memory[0].value, Some(0));
        assert_eq!(sample.post_memory[0].value, Some(1));
        assert_eq!(path.check(&mut solver, &shared, &sample).unwrap(), None);
    }

    #[test]
    fn samples_guarded_memory_reads_bind_only_active_arm() {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let guard = solver.declare_const(crate::smt::smtlib::Ty::Bool, SourceLoc::unknown());
        let read = |address, value| Event::ReadMem {
            value: Val::Bits(B64::new(value, 8)),
            read_kind: Val::Unit,
            address: Val::Bits(B64::new(address, 64)),
            bytes: 1,
            tag_value: None,
            opts: Default::default(),
            region: "mem",
        };
        let path = SamplePath {
            pre: BTreeMap::from([("g".into(), Val::Symbolic(guard))]),
            post: BTreeMap::new(),
            result: Val::Bool(true),
            memory: vec![read(0x1000, 7), read(0x1008, 9)],
            memory_guards: BTreeMap::from([(0, Exp::Var(guard)), (1, Exp::Not(Box::new(Exp::Var(guard))))]),
        };
        let shared = crate::ir::SharedState::empty(crate::ir::Symtab::new());
        for direction in [false, true] {
            let tx = solver.start_transaction_with_guard(Some(Exp::Bool(true)));
            solver.assert(Exp::Eq(Box::new(Exp::Var(guard)), Box::new(Exp::Bool(direction))));
            assert!(sat(&mut solver).unwrap());
            let mut model = Model::new(&mut solver);
            let sample = path.materialize(&mut model, &shared, "merge", 1, None).unwrap();
            drop(model);
            assert_eq!(sample.pre_memory.len(), 1);
            assert_eq!(sample.pre_memory[0].address, if direction { 0x1000 } else { 0x1008 });
            solver.rollback_transaction(tx);
            assert_eq!(path.check(&mut solver, &shared, &sample).unwrap(), Some(true));
        }
    }
}
