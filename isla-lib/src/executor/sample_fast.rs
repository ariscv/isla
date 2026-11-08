//! 快档只使用当前路径的静态充分条件，不读取历史证明或输入期望。
use super::*;
use crate::smt::smtlib::Def;
use ahash::{HashMap, HashMapExt, HashSet, HashSetExt};

#[derive(Clone, Serialize)]
pub struct FastFacts {
    pub(super) guard_unique: bool,
    pub(super) post_unique: bool,
    simple_pre: bool,
}

/// 返回的布尔式表示：在该条件下，表达式由完整前态唯一决定。
/// 活动读取还要求地址和活动条件本身已确定；不把未活动的自由读值算作输入。
struct Dependencies {
    definitions: HashMap<Sym, Exp<Sym>>,
    inputs: HashSet<Sym>,
    reads: HashMap<Sym, Vec<(Exp<Sym>, Exp<Sym>)>>,
    cache: HashMap<Sym, Exp<Sym>>,
    visiting: HashSet<Sym>,
}

fn and(a: Exp<Sym>, b: Exp<Sym>) -> Exp<Sym> {
    Exp::And(Box::new(a), Box::new(b)).eval()
}
fn implies(a: Exp<Sym>, b: Exp<Sym>) -> Exp<Sym> {
    Exp::Or(Box::new(Exp::Not(Box::new(a))), Box::new(b)).eval()
}

impl Dependencies {
    fn symbol(&mut self, symbol: Sym) -> Exp<Sym> {
        if self.inputs.contains(&symbol) {
            return Exp::Bool(true);
        }
        if let Some(found) = self.cache.get(&symbol) {
            return found.clone();
        }
        // 读取绑定与原定义可能相互引用；循环不构成充分证明，保留认证查询。
        if !self.visiting.insert(symbol) {
            return Exp::Bool(false);
        }
        let mut determined =
            self.definitions.get(&symbol).cloned().map(|exp| self.exp(&exp)).unwrap_or(Exp::Bool(false));
        for (address, commit) in self.reads.get(&symbol).cloned().unwrap_or_default() {
            let condition = and(self.exp(&commit), and(commit.clone(), self.exp(&address)));
            determined = Exp::Or(Box::new(determined), Box::new(condition)).eval();
        }
        self.visiting.remove(&symbol);
        self.cache.insert(symbol, determined.clone());
        determined
    }

    fn exp(&mut self, exp: &Exp<Sym>) -> Exp<Sym> {
        match exp {
            Exp::Var(symbol) => self.symbol(*symbol),
            Exp::Ite(condition, yes, no) => {
                let arms = Exp::Ite(condition.clone(), Box::new(self.exp(yes)), Box::new(self.exp(no))).eval();
                and(self.exp(condition), arms)
            }
            Exp::And(a, b) => and(self.exp(a), implies((**a).clone(), self.exp(b))),
            Exp::Or(a, b) => and(self.exp(a), implies(Exp::Not(a.clone()), self.exp(b))),
            _ => {
                let mut unsupported = false;
                exp.clone().modify(&mut |part| {
                    // 未解释函数及浮点欠规定行为不能按普通纯函数放行。
                    if matches!(
                        part,
                        Exp::App(..)
                            | Exp::FPUnary(..)
                            | Exp::FPBinary(..)
                            | Exp::FPRoundingUnary(..)
                            | Exp::FPRoundingBinary(..)
                            | Exp::FPfma(..)
                    ) {
                        unsupported = true;
                    }
                });
                if unsupported {
                    return Exp::Bool(false);
                }
                exp.variables()
                    .into_iter()
                    .fold(Exp::Bool(true), |condition, symbol| and(condition, self.symbol(symbol)))
            }
        }
    }

    fn value<B: BV>(&mut self, value: &Val<B>) -> Exp<Sym> {
        match value {
            Val::Struct(fields) => fields.values().fold(Exp::Bool(true), |a, v| and(a, self.value(v))),
            Val::Ctor(_, value) => self.value(value),
            Val::Vector(values) | Val::List(values) => {
                values.iter().fold(Exp::Bool(true), |a, v| and(a, self.value(v)))
            }
            Val::SymbolicCtor(..) => Exp::Bool(false),
            _ => value.symbolic_variables().into_iter().fold(Exp::Bool(true), |a, symbol| and(a, self.symbol(symbol))),
        }
    }
}

fn simple<B: BV>(value: &Val<B>) -> bool {
    match value {
        Val::SymbolicCtor(..) | Val::Poison => false,
        Val::Struct(fields) => fields.values().all(simple),
        Val::Ctor(_, value) => simple(value),
        Val::Vector(values) | Val::List(values) => values.iter().all(simple),
        _ => true,
    }
}

impl FastFacts {
    pub fn is_complete(&self) -> bool {
        self.guard_unique && self.post_unique && self.simple_pre
    }

    pub fn analyze<B: BV>(
        path: &SamplePath<B>,
        solver: &mut Solver<B>,
        records: &[super::super::RegionMergeRecord<B>],
    ) -> Result<Self, ExecError> {
        assert_eq!(solver.transaction_depth(), 0);
        let simple_pre = path.pre.values().all(simple);
        let mut dependencies = Dependencies {
            definitions: HashMap::new(),
            inputs: HashSet::new(),
            reads: HashMap::new(),
            cache: HashMap::new(),
            visiting: HashSet::new(),
        };
        for event in solver.trace().to_vec().into_iter().rev() {
            if let Event::Smt(Def::DefineConst(symbol, exp), ..) = event {
                dependencies.definitions.insert(*symbol, exp.clone());
            }
        }
        if simple_pre {
            for value in path.pre.values() {
                dependencies.inputs.extend(value.symbolic_variables());
            }
        }
        for (index, event) in path.memory.iter().enumerate() {
            if let Event::ReadMem { address, value: Val::Symbolic(symbol), bytes, .. } = event {
                // 只有整个读取值都被绑定时，才能把整个符号作为已知量。
                if solver.length(*symbol) == Some(8 * bytes) && *bytes > 0 {
                    dependencies.reads.entry(*symbol).or_default().push((
                        smt_value(address, SourceLoc::unknown())?,
                        path.memory_guards.get(&index).cloned().unwrap_or(Exp::Bool(true)),
                    ));
                }
            }
        }
        let by_id = records.iter().map(|record| (record.record_id, record)).collect();
        let mut contexts = std::collections::HashMap::new();
        let mut visiting = std::collections::HashSet::new();
        let mut guard_condition = Exp::Bool(true);
        for record in records {
            let context = super::super::merge_record::context(record, &by_id, &mut visiting, &mut contexts);
            guard_condition = and(guard_condition, dependencies.exp(&and(context, Exp::Var(record.condition))));
        }
        let mut post_condition = dependencies.value(&path.result);
        for value in path.post.values() {
            post_condition = and(post_condition, dependencies.value(value));
        }
        // 地址、活动条件、数据全部确定，便确定完整触碰范围与按事件顺序覆盖后的内存。
        for (address, data, commit, _) in path.accesses() {
            let active = and(dependencies.exp(&address), dependencies.exp(&data));
            post_condition = and(post_condition, and(dependencies.exp(&commit), implies(commit, active)));
        }
        let mut prove = |condition: Exp<Sym>| -> Result<bool, ExecError> {
            match condition.eval() {
                Exp::Bool(value) => Ok(value),
                condition => match solver.check_sat_with(&Exp::Not(Box::new(condition)), SourceLoc::unknown()) {
                    SmtResult::Unsat => Ok(true),
                    SmtResult::Sat | SmtResult::Unknown => Ok(false),
                    SmtResult::Error(error) => Err(ExecError::Smt(error)),
                },
            }
        };
        Ok(Self { guard_unique: prove(guard_condition)?, post_unique: prove(post_condition)?, simple_pre })
    }
}

/// 同原 bind 的等式，但只构造表达式，不创建辅助符号或改动求解器。
fn input_equal<B: BV>(
    value: &Val<B>,
    input: &Value,
    shared: &SharedState<B>,
    solver: &mut Solver<B>,
) -> Result<Exp<Sym>, ExecError> {
    if value.is_concrete() {
        return equal(value, input, shared, solver);
    }
    let all = |conditions: Vec<Exp<Sym>>| conditions.into_iter().fold(Exp::Bool(true), and);
    Ok(match value {
        Val::Struct(fields) => {
            let values = input["struct"].as_object().expect("样本结构体必须完整");
            assert_eq!(fields.len(), values.len());
            all(fields
                .iter()
                .map(|(name, value)| {
                    input_equal(value, &values[&zencode::decode(shared.symtab.to_str(*name))], shared, solver)
                })
                .collect::<Result<Vec<_>, _>>()?)
        }
        Val::Vector(values) | Val::List(values) => {
            let name = if matches!(value, Val::Vector(_)) { "vector" } else { "list" };
            let inputs = input[name].as_array().unwrap();
            if inputs.len() != values.len() {
                return Ok(Exp::Bool(false));
            }
            all(values
                .iter()
                .zip(inputs)
                .map(|(v, i)| input_equal(v, i, shared, solver))
                .collect::<Result<Vec<_>, _>>()?)
        }
        Val::Ctor(name, value) => {
            if input["ctor"] != zencode::decode(shared.symtab.to_str(*name)) {
                return Ok(Exp::Bool(false));
            }
            input_equal(value, &input["value"], shared, solver)?
        }
        Val::Symbolic(_) | Val::MixedBits(_) => {
            let right = if let Some(bits) = input.get("bits") {
                Exp::Bits(
                    crate::bitvector::bit_vector_from_str(&format!("#b{}", bits.as_str().unwrap()))
                        .expect("样本位串无效"),
                )
            } else {
                smt_value(&decode::<B>(input, shared), SourceLoc::unknown())?
            };
            Exp::Eq(Box::new(smt_value(value, SourceLoc::unknown())?), Box::new(right))
        }
        _ => unreachable!("快档前态必须已通过形状检查"),
    })
}

impl<B: BV> SamplePath<B> {
    pub fn classify(
        &self,
        solver: &mut Solver<B>,
        shared: &SharedState<B>,
        input: &Sample,
        records: &[super::super::RegionMergeRecord<B>],
        signature: u64,
        facts: &FastFacts,
        consume: impl FnMut(&mut Sample, &mut Model<B>) -> Result<(), ExecError>,
    ) -> Result<Option<JudgedSample>, ExecError> {
        let mut memory = BTreeMap::new();
        let mut functional = true;
        for cell in &input.pre_memory {
            if let Some(byte) = cell.value {
                assert_eq!(cell.bytes, 1, "内部内存单元必须按字节规范化");
                if let Some(previous) = memory.insert(cell.address, byte) {
                    functional &= previous == byte;
                }
            }
        }
        if !facts.is_complete() || !functional {
            return self.judge(solver, shared, input, records, signature, consume);
        }
        for name in self.pre.keys() {
            if !input.pre_registers.contains_key(name) {
                return Err(ExecError::Type(format!("缺少前态寄存器：{name}"), SourceLoc::unknown()));
            }
        }
        assert_eq!(solver.transaction_depth(), 0, "快档必须在路径结束后运行");
        let timing = profile::Span::new("fast_bind");
        let mut condition = Exp::Bool(true);
        for (name, value) in &input.pre_registers {
            if let Some(reg) = self.pre.get(name) {
                condition = and(condition, input_equal(reg, value, shared, solver)?);
            }
        }
        // 一次绑定整次读取，等价于原来的逐字节析取；候选基址必须覆盖全部字节。
        for (index, event) in self.memory.iter().enumerate() {
            let Event::ReadMem { address, value, bytes, .. } = event else {
                continue;
            };
            if *bytes == 0 {
                continue;
            }
            let mut candidates = Exp::Bool(false);
            for base in memory.keys() {
                let data = (0..*bytes)
                    .map(|offset| memory.get(&base.wrapping_add(u64::from(offset))).copied())
                    .collect::<Option<Vec<_>>>();
                if let Some(data) = data {
                    let bits =
                        data.into_iter().flat_map(|byte| (0..8).map(move |bit| byte & (1 << bit) != 0)).collect();
                    let hit = and(
                        Exp::Eq(
                            Box::new(smt_value(address, SourceLoc::unknown())?),
                            Box::new(Exp::Bits64(B64::new(*base, 64))),
                        ),
                        Exp::Eq(
                            Box::new(Exp::Extract(8 * bytes - 1, 0, Box::new(smt_value(value, SourceLoc::unknown())?))),
                            Box::new(Exp::Bits(bits)),
                        ),
                    );
                    candidates = Exp::Or(Box::new(candidates), Box::new(hit)).eval();
                }
            }
            condition =
                and(condition, implies(self.memory_guards.get(&index).cloned().unwrap_or(Exp::Bool(true)), candidates));
        }
        let result = solver.check_sat_with(&condition, SourceLoc::unknown());
        drop(timing);
        match result {
            SmtResult::Sat => {
                Ok(Some(self.concretize_judged(solver, shared, input.sample_id, records, signature, consume)?.0))
            }
            SmtResult::Unsat => Ok(None),
            SmtResult::Unknown => Err(ExecError::Z3Unknown),
            SmtResult::Error(error) => Err(ExecError::Smt(error)),
        }
    }
}
