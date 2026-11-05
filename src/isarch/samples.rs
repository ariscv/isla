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
    SamplePath { pre, post, result: result.clone(), memory }
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
}
