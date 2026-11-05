//! solve-state 的样本配置与终态适配；算法由 isla-lib 两种模式共用。
use super::target::Target;
use isla_lib::bitvector::BV;
use isla_lib::executor::samples::{SampleChecker, SamplePath, SampleWriter};
use isla_lib::executor::LocalFrame;
use isla_lib::ir::{SharedState, Val};
use isla_lib::register::RegisterBindings;
use std::collections::BTreeMap;
use std::path::PathBuf;

#[derive(Default)]
pub struct SampleOptions {
    pub check: Option<PathBuf>,
    pub limit: Option<usize>,
    pub report: Option<PathBuf>,
}

impl SampleOptions {
    pub fn validate(&self) -> Result<(), String> {
        if self.check.is_none() && (self.limit.is_some() || self.report.is_some()) {
            return Err("--check-samples-limit/--check-samples-report 需要 --check-samples".into());
        }
        if self.limit == Some(0) {
            return Err("--check-samples-limit 必须大于零".into());
        }
        if let Some(path) = &self.check {
            if self.report.as_ref() == Some(path) {
                return Err("检查报告不得覆盖样本输入".into());
            }
        }
        Ok(())
    }
}

pub struct SampleSession {
    pub writer: Option<SampleWriter>,
    pub checker: Option<SampleChecker>,
}
impl SampleSession {
    pub fn new(options: &SampleOptions) -> Result<Self, String> {
        options.validate()?;
        let checker = options.check.as_ref().map(|path| SampleChecker::load(path, options.limit)).transpose()?;
        let writer =
            std::env::var_os("ISLA_EXPORT_SAMPLES").map(|path| SampleWriter::open(std::path::Path::new(&path)));
        Ok(Self { writer, checker })
    }
    pub fn enabled(&self) -> bool {
        self.writer.is_some() || self.checker.is_some()
    }
    pub fn finish(&self, options: &SampleOptions, completed: bool) {
        if let Some(checker) = &self.checker {
            let mut report = checker.report();
            report["completed"] = serde_json::json!(completed);
            let text = serde_json::to_string_pretty(&report).expect("报告序列化失败");
            if let Some(path) = &options.report {
                std::fs::write(path, &text).expect("写入样本报告失败");
            }
            eprintln!("[SAMPLE_CHECK_REPORT] {}", serde_json::to_string(&report).unwrap());
        }
    }
}

pub fn path<B: BV>(
    target: &dyn Target<B>,
    initial: &RegisterBindings<B>,
    frame: &LocalFrame<B>,
    shared: &SharedState<B>,
    instruction: &Val<B>,
    result: &Val<B>,
    memory: Vec<isla_lib::smt::Event<B>>,
) -> SamplePath<B> {
    let mut pre: BTreeMap<_, _> = initial
        .iter()
        .filter_map(|(name, register)| {
            register
                .read_last_if_initialized()
                .map(|value| (isla_lib::zencode::decode(shared.symtab.to_str(*name)), value.clone()))
        })
        .collect();
    for (name, value) in target.pre_state().iter() {
        pre.insert(isla_lib::zencode::decode(shared.symtab.to_str(*name)), value.clone());
    }
    let post = frame
        .regs()
        .iter()
        .filter_map(|(name, register)| {
            register
                .read_last_if_initialized()
                .map(|value| (isla_lib::zencode::decode(shared.symtab.to_str(*name)), value.clone()))
        })
        .collect();
    pre.insert("$instruction".into(), instruction.clone());
    // 注意（ATTENTION）：合并路径的内存读取为并集语义；需要精确内存读序列时不可信。
    // 样本按保存的 guard 过滤未执行臂；实际发生的每次读仍绑定 pre_memory，
    // 沿用既有初始内存规则及“写后读不同值”限制。原始主迹本身仍是并集。
    let memory_guards = frame
        .region_merge_records()
        .iter()
        .flat_map(|record| record.memory_reads.iter().map(|(index, guard, _)| (*index, guard.clone())))
        .collect();
    SamplePath { pre, post, result: result.clone(), memory, memory_guards }
}

/// 样本已物化完整前态；复用其值格式化 ISA 状态，避免再抽取同一模型。
pub fn isa_state<B: BV>(
    target: &dyn Target<B>,
    sample: &isla_lib::executor::samples::Sample,
    model: &mut isla_lib::smt::Model<B>,
    shared: &SharedState<B>,
) -> Result<BTreeMap<String, String>, isla_lib::error::ExecError> {
    use isla_lib::error::ExecError;
    use isla_lib::fmtval::FmtVal;
    use isla_lib::smt::smtlib::Exp;
    use isla_lib::zencode;
    fn formatted<B: BV>(
        original: &Val<B>,
        value: &serde_json::Value,
        model: &mut isla_lib::smt::Model<B>,
        shared: &SharedState<B>,
    ) -> Result<Option<FmtVal>, ExecError> {
        match original {
            Val::Symbolic(_) => {
                let expression = if let Some(bits) = value.get("bits") {
                    Exp::Bits(bits.as_str().unwrap().bytes().rev().map(|bit| bit == b'1').collect())
                } else if let Some(value) = value.get("bool") {
                    Exp::Bool(value.as_bool().unwrap())
                } else if let Some(value) = value.get("enum") {
                    let name = shared.symtab.lookup(&zencode::encode(value.as_str().unwrap()));
                    let (member, _, enum_name) = shared.type_info.enum_members[&name];
                    Exp::Enum(isla_lib::smt::EnumMember {
                        enum_id: isla_lib::smt::EnumId::from_name(enum_name),
                        member,
                    })
                } else {
                    panic!("符号标量必须物化为位向量、布尔或枚举");
                };
                Ok(FmtVal::from_exp(&expression))
            }
            Val::Struct(fields) if fields.len() == 1 => {
                let (name, original) = fields.iter().next().unwrap();
                formatted(original, &value["struct"][zencode::decode(shared.symtab.to_str(*name))], model, shared)
            }
            Val::Ctor(_, original) => formatted(original, &value["value"], model, shared),
            // 具体值与混合位串沿用既有格式化，以保留原来的片段语义。
            Val::Bits(_) | Val::Bool(_) | Val::Enum(_) | Val::MixedBits(_) => {
                FmtVal::from_val(original, model).map(Some)
            }
            _ => Ok(None),
        }
    }
    let mut state = BTreeMap::new();
    for (name, original) in target.pre_state().iter() {
        let name = zencode::decode(shared.symtab.to_str(*name));
        let value = sample.pre_registers.get(&name).expect("完整样本必须包含前态寄存器");
        if let Some(value) = formatted(original, value, model, shared)? {
            state.insert(name, value.to_str(shared));
        }
    }
    // PMA 大小不在 pre_registers 中，仍按现有接口查询。
    for (name, symbol) in target.symbolic_pma_sizes() {
        let value = model.get_var(*symbol)?;
        if let Some(value) = FmtVal::from_model_val(&value) {
            if !value.is_arbitrary() {
                state.insert(format!("pma_regions.{name}.size"), value.to_str(shared));
            }
        }
    }
    Ok(state)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn samples_f5_复用前态格式化字节与模型查询一致() {
        use isla_lib::bitvector::b129::B129;
        use isla_lib::ir::Symtab;
        use isla_lib::smt::{smtlib, Config, Context, Model, Solver};
        use isla_lib::source_loc::SourceLoc;
        let context = Context::new(Config::new());
        let mut solver = Solver::<B129>::new(&context);
        let mut symtab = Symtab::new();
        let flag = symtab.intern("zflag");
        let wide = symtab.intern("zwide");
        let wrapped = symtab.intern("zwrapped");
        let field = symtab.intern("zbits");
        let list = symtab.intern("zlist");
        let mut target = super::super::target::RV64::<B129>::default();
        target
            .pre_state_mut()
            .insert(flag, Val::Symbolic(solver.declare_const(smtlib::Ty::Bool, SourceLoc::unknown())));
        target.pre_state_mut().insert(wide, Val::Symbolic(solver.declare_bitvector(256, SourceLoc::unknown())));
        target.pre_state_mut().insert(
            wrapped,
            Val::Struct(std::collections::HashMap::from_iter([(
                field,
                Val::Symbolic(solver.declare_bitvector(64, SourceLoc::unknown())),
            )])),
        );
        target.pre_state_mut().insert(list, Val::List(vec![Val::Unit]));
        // 非零高位与枚举覆盖格式化位序；符号 PMA 大小仍走模型接口。
        let Val::Symbolic(wide_symbol) = target.pre_state().get(&wide).unwrap() else {
            panic!("宽值必须符号化");
        };
        solver.assert(smtlib::Exp::Eq(
            Box::new(smtlib::Exp::Var(*wide_symbol)),
            Box::new(smtlib::Exp::Bits((0..256).map(|bit| bit % 7 == 0).collect())),
        ));
        let enum_name = symtab.intern("zF5Enum");
        let enum_member = symtab.intern("zF5Member");
        let enum_register = symtab.intern("zenum_reg");
        let mut shared = SharedState::empty(symtab);
        shared.type_info.enum_members.insert(enum_member, (0, 1, enum_name));
        shared.type_info.enums.insert(enum_name, vec![enum_member]);
        solver.add(smtlib::Def::DefineEnum(enum_name, 1));
        let enum_value =
            solver.declare_const(smtlib::Ty::Enum(isla_lib::smt::EnumId::from_name(enum_name)), SourceLoc::unknown());
        target.pre_state_mut().insert(enum_register, Val::Symbolic(enum_value));
        let pma_size = solver.declare_bitvector(64, SourceLoc::unknown());
        target.symbolic_pma_sizes_mut().push(("test".into(), pma_size));

        let pre = target
            .pre_state()
            .iter()
            .map(|(name, value)| (isla_lib::zencode::decode(shared.symtab.to_str(*name)), value.clone()))
            .collect();
        let path = SamplePath {
            pre,
            post: BTreeMap::new(),
            result: Val::Unit,
            memory: Vec::new(),
            memory_guards: BTreeMap::new(),
        };
        assert_eq!(solver.check_sat(SourceLoc::unknown()), isla_lib::smt::SmtResult::Sat);
        let mut model = Model::new(&solver);
        let sample = path.materialize(&mut model, &shared, "merge", 0, Some(0)).unwrap();
        let expected = target.solve_pre_state(&mut model, &shared).unwrap();
        let actual = isa_state(&target, &sample, &mut model, &shared).unwrap();
        assert_eq!(serde_json::to_vec(&actual).unwrap(), serde_json::to_vec(&expected).unwrap());
    }

    #[test]
    fn samples_options_validate_dependencies_and_limits() {
        assert!(SampleOptions::default().validate().is_ok());
        assert!(SampleOptions { limit: Some(10), ..Default::default() }.validate().is_err());
        assert!(SampleOptions { check: Some("samples.jsonl".into()), limit: Some(0), report: None }
            .validate()
            .is_err());
        assert!(SampleOptions {
            check: Some("samples.jsonl".into()),
            limit: Some(10),
            report: Some("samples.jsonl".into())
        }
        .validate()
        .is_err());
        assert!(SampleOptions {
            check: Some("samples.jsonl".into()),
            limit: Some(10),
            report: Some("report.json".into())
        }
        .validate()
        .is_ok());
    }
    #[test]
    fn samples_f4_array_reads_keep_constraints_under_arm_guard() {
        use isla_lib::bitvector::b64::B64;
        use isla_lib::memory::Memory;
        use isla_lib::primop_util::smt_value;
        use isla_lib::smt::smtlib::{bits64, Exp, Ty};
        use isla_lib::smt::{Config, Context, ReadOpts, Solver};
        use isla_lib::source_loc::SourceLoc;
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let mut memory = Memory::new();
        memory.add_symbolic_region(0x1000..0x1010);
        super::super::memory_model::install_seq_memory(&mut memory, 64, &mut solver);
        let g = solver.declare_const(Ty::Bool, info);
        solver.start_transaction();
        let mut values = Vec::new();
        for (guard, byte) in [(Exp::Var(g), 7), (Exp::Not(Box::new(Exp::Var(g))), 9)] {
            solver.start_transaction_with_guard(Some(guard));
            let value = memory
                .read(Val::Unit, Val::Bits(B64::new(0x1000, 64)), Val::I128(1), &mut solver, false, ReadOpts::default())
                .unwrap();
            solver.assert(Exp::Eq(Box::new(smt_value(&value, info).unwrap()), Box::new(bits64(byte, 8))));
            values.push(value);
            solver.commit_transaction();
        }
        solver.commit_transaction();
        // 同址两臂要求不同内容，只有各自 guard 生效；无条件提交会使整个路径 Unsat。
        for (direction, byte) in [(true, 7), (false, 9)] {
            let guard = Exp::Eq(Box::new(Exp::Var(g)), Box::new(Exp::Bool(direction)));
            assert!(solver.check_sat_with(&guard, info).is_sat().unwrap());
            let tx = solver.start_transaction_with_guard(Some(guard));
            let current = memory
                .read(Val::Unit, Val::Bits(B64::new(0x1000, 64)), Val::I128(1), &mut solver, false, ReadOpts::default())
                .unwrap();
            assert!(solver
                .check_sat_with(
                    &Exp::Neq(Box::new(smt_value(&current, info).unwrap()), Box::new(bits64(byte, 8))),
                    info
                )
                .is_unsat()
                .unwrap());
            solver.rollback_transaction(tx);
        }
        assert_ne!(values[0], values[1], "两次读取必须使用不同的新鲜符号");
    }
}
