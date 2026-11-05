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

#[cfg(test)]
mod tests {
    use super::*;
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
