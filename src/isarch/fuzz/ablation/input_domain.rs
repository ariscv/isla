//! 硬件规则由fuzz配置提供，通用取点器只接收编译后的布尔表达式。
use isla_lib::{
    bitvector::BV,
    executor::samples::SamplePath,
    ir::{Loc, SharedState, Val},
    primop_util::smt_value,
    smt::{
        smtlib::{bits64, Exp},
        Event, Sym,
    },
    source_loc::SourceLoc,
    zencode,
};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default, deny_unknown_fields)]
pub(super) struct InputDomain {
    pub register_constraints: Vec<String>,
    pub privileges: Vec<String>,
    pub instruction_widths: Vec<u64>,
    pub exclude_unsigned_doubleword: bool,
    pub aligned: bool,
    /// 每个范围为允许的字节地址闭区间，由平台可重放DRAM求交后提供。
    pub memory_ranges: Vec<[u64; 2]>,
}
fn and(parts: impl IntoIterator<Item = Exp<Sym>>) -> Exp<Sym> {
    parts.into_iter().fold(Exp::Bool(true), |a, b| Exp::And(Box::new(a), Box::new(b)).eval())
}
fn or(parts: impl IntoIterator<Item = Exp<Sym>>) -> Exp<Sym> {
    parts.into_iter().fold(Exp::Bool(false), |a, b| Exp::Or(Box::new(a), Box::new(b)).eval())
}
fn equal(a: Exp<Sym>, b: Exp<Sym>) -> Exp<Sym> {
    Exp::Eq(Box::new(a), Box::new(b))
}
impl InputDomain {
    pub fn compile<B: BV>(&self, path: &SamplePath<B>, shared: &SharedState<B>) -> Result<Exp<Sym>, String> {
        let scalar = |value: &Val<B>| {
            smt_value(value, SourceLoc::unknown()).map_err(|e| format!("输入域字段不能转为SMT：{e:?}"))
        };
        let mut conditions = Vec::new();
        for text in &self.register_constraints {
            let parsed =
                isla_lib::smt_parser::ExpParser::new().parse(text).map_err(|e| format!("输入域表达式错误：{e}"))?;
            let expression = parsed.map_var(&mut |reference| {
                let mut fields = Vec::new();
                let mut root = reference;
                while let Loc::Field(parent, field) = root {
                    fields.push(field);
                    root = parent;
                }
                let Loc::Id(name) = root else { return Err("输入域不能使用地址位置".into()) };
                let decoded = zencode::decode(name);
                let mut value = path.pre.get(&decoded).ok_or_else(|| format!("输入域引用缺少的寄存器：{decoded}"))?;
                for field in fields.into_iter().rev() {
                    let Val::Struct(members) = value else { return Err("输入域字段不是结构体".into()) };
                    value = members
                        .iter()
                        .find(|(name, _)| shared.symtab.to_str(**name) == field)
                        .map(|(_, v)| v)
                        .ok_or_else(|| format!("输入域字段不存在：{field}"))?;
                }
                scalar(value)
            })?;
            conditions.push(expression);
        }
        if !self.privileges.is_empty() {
            let value = scalar(path.pre.get("cur_privilege").ok_or("缺少特权级")?)?;
            let mut allowed = Vec::new();
            for privilege in &self.privileges {
                let name = shared.symtab.get(&zencode::encode(privilege)).ok_or("输入域特权级不存在")?;
                let (index, _, id) = shared.type_info.enum_members.get(&name).ok_or("输入域特权级不是枚举成员")?;
                allowed.push(equal(
                    value.clone(),
                    Exp::Enum(isla_lib::smt::EnumMember {
                        enum_id: isla_lib::smt::EnumId::from_name(*id),
                        member: *index,
                    }),
                ));
            }
            conditions.push(or(allowed));
        }
        if !self.instruction_widths.is_empty() {
            if self.instruction_widths.iter().any(|w| !matches!(w, 1 | 2 | 4 | 8)) {
                return Err("输入域宽度必须为1/2/4/8".into());
            }
            let Val::Ctor(name, payload) = path.pre.get("$instruction").ok_or("输入域缺少指令")? else {
                return Err("输入域指令必须为构造子".into());
            };
            let load = match zencode::decode(shared.symtab.to_str(*name)).as_str() {
                "LOAD" => true,
                "STORE" => false,
                _ => return Err("硬件输入域只用于LOAD/STORE".into()),
            };
            let Val::Struct(fields) = &**payload else { return Err("指令载荷必须为结构体".into()) };
            let field = |suffix: char| {
                fields
                    .iter()
                    .find(|(n, _)| zencode::decode(shared.symtab.to_str(**n)).ends_with(suffix))
                    .map(|(_, v)| v)
                    .ok_or_else(|| format!("指令缺少字段{suffix}"))
            };
            let width = scalar(field(if load { '4' } else { '3' })?)?;
            conditions.push(or(self.instruction_widths.iter().map(|w| equal(width.clone(), bits64(*w, 64)))));
            if load && self.exclude_unsigned_doubleword {
                conditions.push(Exp::Not(Box::new(and([equal(width.clone(), bits64(8, 64)), scalar(field('3')?)?]))));
            }
            if self.aligned {
                let register = scalar(field(if load { '1' } else { '2' })?)?;
                let offset = Exp::SignExtend(52, Box::new(scalar(field('0')?)?));
                let mut aligned = Vec::new();
                for index in 0..32 {
                    let base = if index == 0 {
                        bits64(0, 64)
                    } else if let Some(v) = path.pre.get(&format!("x{index}")) {
                        scalar(v)?
                    } else {
                        continue;
                    };
                    let address = Exp::Bvadd(Box::new(base), Box::new(offset.clone()));
                    let mask = Exp::Bvsub(Box::new(width.clone()), Box::new(bits64(1, 64)));
                    aligned.push(and([
                        equal(register.clone(), bits64(index, 5)),
                        equal(Exp::Bvand(Box::new(address), Box::new(mask)), bits64(0, 64)),
                    ]));
                }
                conditions.push(or(aligned));
            }
        }
        if !self.memory_ranges.is_empty() {
            if self.memory_ranges.iter().any(|[low, high]| low > high) {
                return Err("输入域内存闭区间颠倒".into());
            }
            for (index, event) in path.memory.iter().enumerate() {
                let (address, bytes) = match event {
                    Event::ReadMem { address, bytes, .. } | Event::WriteMem { address, bytes, .. } => (address, *bytes),
                    _ => continue,
                };
                assert!(bytes > 0, "活动访存宽度必须非零");
                let address = scalar(address)?;
                let last = Exp::Bvadd(Box::new(address.clone()), Box::new(bits64(u64::from(bytes) - 1, 64)));
                let valid = or(self.memory_ranges.iter().map(|[low, high]| {
                    and([
                        Exp::Bvuge(Box::new(address.clone()), Box::new(bits64(*low, 64))),
                        Exp::Bvule(Box::new(last.clone()), Box::new(bits64(*high, 64))),
                        Exp::Bvuge(Box::new(last.clone()), Box::new(address.clone())),
                    ])
                }));
                let active = path.memory_guards.get(&index).cloned().unwrap_or(Exp::Bool(true));
                conditions.push(or([Exp::Not(Box::new(active)), valid]));
            }
        }
        Ok(and(conditions))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::{
        bitvector::b64::B64,
        executor::samples::Terminal,
        ir::{SharedState, Symtab, Val},
        smt::{Config, Context, Solver},
        source_loc::SourceLoc,
    };
    use std::collections::BTreeMap;
    #[test]
    fn input_domain_rejects_unknown_registers_and_keeps_masked_bits_free() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let x = solver.declare_bitvector(64, SourceLoc::unknown());
        let path: SamplePath<B64> = SamplePath {
            terminal: Terminal::Normal,
            pre: BTreeMap::from([("field".into(), Val::Symbolic(x))]),
            post: BTreeMap::new(),
            result: Val::Unit,
            memory: Vec::new(),
            memory_guards: BTreeMap::new(),
        };
        let shared = SharedState::empty(Symtab::new());
        let mut domain: InputDomain = serde_json::from_value(
            serde_json::json!({"register_constraints":["= (bvand field #x0000000000000001) #x0000000000000000"]}),
        )
        .unwrap();
        let condition = domain.compile(&path, &shared).unwrap();
        assert!(solver.check_sat_with(&condition, SourceLoc::unknown()).is_sat().unwrap());
        domain.register_constraints = vec!["= absent #x0000000000000000".into()];
        assert!(domain.compile(&path, &shared).is_err());
    }
    #[test]
    fn input_domain_memory_guards_and_last_byte_reject_wraparound() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let address = solver.declare_bitvector(64, SourceLoc::unknown());
        let active = solver.declare_const(isla_lib::smt::smtlib::Ty::Bool, SourceLoc::unknown());
        let path: SamplePath<B64> = SamplePath {
            terminal: Terminal::Normal,
            pre: BTreeMap::new(),
            post: BTreeMap::new(),
            result: Val::Unit,
            memory: vec![Event::ReadMem {
                value: Val::Bits(B64::new(0, 64)),
                read_kind: Val::Unit,
                address: Val::Symbolic(address),
                bytes: 8,
                tag_value: None,
                opts: Default::default(),
                region: "mem",
            }],
            memory_guards: BTreeMap::from([(0, Exp::Var(active))]),
        };
        let shared = SharedState::empty(Symtab::new());
        let domain = InputDomain { memory_ranges: vec![[0x1000, 0x1fff]], ..Default::default() };
        let condition = domain.compile(&path, &shared).unwrap();
        for (value, enabled, allowed) in [
            (0x1000, true, true),
            (0x1ff8, true, true),
            (0x1ff9, true, false),
            (u64::MAX, true, false),
            (u64::MAX, false, true),
        ] {
            let query = and([
                condition.clone(),
                equal(Exp::Var(address), bits64(value, 64)),
                equal(Exp::Var(active), Exp::Bool(enabled)),
            ]);
            assert_eq!(solver.check_sat_with(&query, SourceLoc::unknown()).is_sat().unwrap(), allowed);
        }
    }
}
