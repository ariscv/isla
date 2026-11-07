//! 公共路径状态、组合配置与提交；三种轨迹不相互隶属。
use super::btrace::BranchEdge;
use super::itrace::{IrFileCache, ItracePerInstr};
use super::sequence::SharedSequence;
use super::writer::TraceWriter;
use crate::ir::{Name, Symtab};
use crate::smt::{smtlib, Sym};
use crate::timeout::{PathTimeSnapshot, TimeoutDiagnostic};
use std::collections::BTreeSet;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Mutex;

#[derive(Clone, Default)]
pub(crate) struct TracePerPath {
    pub(super) itrace_records: SharedSequence<ItracePerInstr>,
    pub(super) branch_conditions: SharedSequence<smtlib::Exp<Sym>>,
    pub(super) branch_edges: SharedSequence<BranchEdge>,
    pub(crate) instruction_count: usize,
    pub(super) executed_functions: BTreeSet<Name>,
    pub(super) function_trace: Vec<(Name, bool)>,
}

#[derive(Clone)]
pub(crate) struct TraceCompletedPath {
    pub(super) execution_trace: TracePerPath,
    completion_diagnostics: Vec<TraceCompletionDiagnostic>,
    pub(super) path_timing: PathTimeSnapshot,
    pub(super) smtperf_summary: Option<String>,
    pub(super) path_signature: Option<u64>,
}

#[derive(Clone)]
struct TraceCompletionDiagnostic {
    pub(super) timeout: TimeoutDiagnostic,
    pub(super) include_smt_dump: bool,
}

impl TraceCompletedPath {
    pub(crate) fn new(execution_trace: TracePerPath, completion_diagnostics: Vec<TimeoutDiagnostic>) -> Self {
        TraceCompletedPath {
            execution_trace,
            completion_diagnostics: completion_diagnostics
                .into_iter()
                .map(|timeout| TraceCompletionDiagnostic { timeout, include_smt_dump: true })
                .collect(),
            path_timing: PathTimeSnapshot::default(),
            smtperf_summary: None,
            path_signature: None,
        }
    }

    pub(crate) fn with_timing(
        execution_trace: TracePerPath,
        completion_diagnostics: Vec<TimeoutDiagnostic>,
        path_timing: PathTimeSnapshot,
    ) -> Self {
        TraceCompletedPath {
            execution_trace,
            completion_diagnostics: completion_diagnostics
                .into_iter()
                .map(|timeout| TraceCompletionDiagnostic { timeout, include_smt_dump: true })
                .collect(),
            path_timing,
            smtperf_summary: None,
            path_signature: None,
        }
    }

    pub(crate) fn without_diagnostics(execution_trace: TracePerPath) -> Self {
        TraceCompletedPath::new(execution_trace, Vec::new())
    }

    pub(crate) fn push_diagnostic_with_dump(&mut self, diagnostic: TimeoutDiagnostic, include_smt_dump: bool) {
        self.completion_diagnostics.push(TraceCompletionDiagnostic { timeout: diagnostic, include_smt_dump });
    }

    pub(crate) fn set_timing(&mut self, path_timing: PathTimeSnapshot) {
        self.path_timing = path_timing;
    }

    pub(crate) fn set_smtperf_summary(&mut self, summary: Option<String>) {
        self.smtperf_summary = summary;
    }

    pub(crate) fn set_path_signature(&mut self, signature: u64) {
        self.path_signature = Some(signature);
    }
}

impl TracePerPath {
    #[cfg(test)]
    pub(crate) fn prefix_identity_for_test(&self) -> [*const (); 3] {
        [
            self.itrace_records.iter().next().map_or(std::ptr::null(), |item| item as *const _ as *const ()),
            self.branch_conditions.iter().next().map_or(std::ptr::null(), |item| item as *const _ as *const ()),
            self.branch_edges.iter().next().map_or(std::ptr::null(), |item| item as *const _ as *const ()),
        ]
    }
}

// ============ TraceHandler ============
// 一个 TraceHandler 对应一次完整的符号执行入口、一个组合轨迹输出文件和一个大标题。
// 在多 clause / --all 场景下，每个 clause 应拥有独立的 handler 生命周期，
// 以保证各 clause 的 轨迹输出互不干扰（独立文件、独立标题）。
// Handler 管理 三类轨迹的公共上下文，Writer 管理写入生命周期。

pub struct TraceHandler {
    pub(super) title: Mutex<String>,
    pub(super) ir_cache: Mutex<IrFileCache>,
    pub(super) instructions: AtomicBool,
    pub(super) functions: AtomicBool,
    pub(super) branches: AtomicBool,
    pub(super) writer: TraceWriter,
}

impl Default for TraceHandler {
    fn default() -> Self {
        Self {
            title: Mutex::new(String::new()),
            ir_cache: Mutex::new(IrFileCache::default()),
            instructions: AtomicBool::new(true),
            functions: AtomicBool::new(false),
            branches: AtomicBool::new(true),
            writer: TraceWriter::default(),
        }
    }
}

impl TraceHandler {
    /// Full initialization: read .ir file to build cache, set output path, spawn write thread
    pub fn init(title: &str, ir_file_path: PathBuf, output_path: Option<PathBuf>, symtab: &Symtab) -> Self {
        let ir_cache = IrFileCache::from_file(&ir_file_path, symtab);
        Self {
            title: Mutex::new(title.to_string()),
            ir_cache: Mutex::new(ir_cache),
            instructions: AtomicBool::new(true),
            functions: AtomicBool::new(false),
            branches: AtomicBool::new(true),
            writer: TraceWriter::with_output_path(output_path),
        }
    }

    pub fn configure(&self, title: &str, ir_file_path: PathBuf, output_path: Option<PathBuf>, symtab: &Symtab) {
        self.writer.dump();

        if let Ok(mut title_lock) = self.title.lock() {
            *title_lock = title.to_string();
        }

        let ir_cache = IrFileCache::from_file(&ir_file_path, symtab);
        if let Ok(mut cache_lock) = self.ir_cache.lock() {
            *cache_lock = ir_cache;
        }
        self.set_traces(true, false, true);

        self.writer.configure_path(output_path);
    }

    /// Set output path — compatible with &self call sites (interior mutability via Mutex)
    pub fn set_path(&self, output_path: Option<PathBuf>) {
        self.writer.set_path(output_path);
    }

    /// 三种轨迹独立组合；路径签名、统计和诊断属于公共路径信息。
    pub fn set_traces(&self, instructions: bool, functions: bool, branches: bool) {
        self.instructions.store(instructions, Ordering::Release);
        self.functions.store(functions, Ordering::Release);
        self.branches.store(branches, Ordering::Release);
    }

    pub fn ftrace_enabled(&self) -> bool {
        self.functions.load(Ordering::Acquire)
    }

    pub fn btrace_enabled(&self) -> bool {
        self.branches.load(Ordering::Acquire)
    }

    fn title(&self) -> String {
        self.title.lock().map(|title| title.clone()).unwrap_or_default()
    }

    /// Signal shutdown and join the write thread (flushes remaining data)
    pub fn dump(&self) {
        self.writer.dump();
    }
}

impl Drop for TraceHandler {
    fn drop(&mut self) {
        self.dump();
    }
}

/*
 * Post-processing and presentation
 *
 * 后处理路径负责 IR cache 查找、source location 清洗和标题格式化，优先保证输出整洁可读。
 */

impl TracePerPath {
    fn render_lines(&self, handler: &TraceHandler, symtab: &Symtab) -> Option<Vec<String>> {
        handler.writer.output_path()?;

        let mut lines = Vec::new();
        lines.push(self.render_title(&handler.title(), symtab));

        lines.push(format!("instruction_count: {}", self.instruction_count));
        let functions = self.executed_functions.iter().map(|name| symtab.to_str(*name)).collect::<BTreeSet<_>>();
        lines.push(format!(
            "executed_functions: {}",
            serde_json::to_string(&functions).expect("function names serialize")
        ));
        self.render_functions(handler, symtab, &mut lines);

        self.render_instructions(handler, symtab, &mut lines);

        Some(lines)
    }

    fn render_text(&self, handler: &TraceHandler, symtab: &Symtab) -> Option<String> {
        let mut lines = self.render_lines(handler, symtab)?;
        lines.push(String::new());
        lines.push("====".to_string());
        Some(lines.join("\n"))
    }
}

fn render_path_timing(lines: &mut Vec<String>, timing: crate::timeout::PathTimeSnapshot) {
    crate::timeout::append_path_timing_lines(lines, timing);
}

fn render_timeout_diagnostic(lines: &mut Vec<String>, diagnostic: &TraceCompletionDiagnostic) {
    lines.push(String::new());
    lines.push("---- completion diagnostic ----".to_string());
    lines.extend(diagnostic.timeout.metadata_lines());
    if !diagnostic.include_smt_dump {
        return;
    }
    let dump = diagnostic.timeout.dump();

    match dump.materialize() {
        Ok(smt2) => {
            lines.push("---- timeout smt2 begin ----".to_string());
            lines.push(smt2.to_string());
            lines.push("---- timeout smt2 end ----".to_string());
        }
        Err(error) => lines.push(format!("timeout_smt_dump_error: {}", error)),
    }
}

impl TraceCompletedPath {
    fn render_text(&self, handler: &TraceHandler, symtab: &Symtab) -> Option<String> {
        let mut lines = self.execution_trace.render_lines(handler, symtab)?;
        if let Some(signature) = self.path_signature {
            lines.push(format!("path_signature: {}", signature));
        }
        self.execution_trace.render_branches(handler, symtab, &mut lines);
        lines.push(String::new());
        lines.push("---- path timing ----".to_string());
        render_path_timing(&mut lines, self.path_timing);
        if let Some(summary) = &self.smtperf_summary {
            lines.push(String::new());
            lines.push("---- smt performance ----".to_string());
            lines.extend(summary.lines().map(str::to_string));
        }
        for diagnostic in &self.completion_diagnostics {
            render_timeout_diagnostic(&mut lines, diagnostic);
        }
        lines.push(String::new());
        lines.push("====".to_string());
        Some(lines.join("\n"))
    }
}

impl TraceHandler {
    /// 提交已完成路径；公共层组合输出并交给共享 writer。
    pub(crate) fn submit_path(&self, path: &TracePerPath, symtab: &Symtab) {
        self.submit_completed_path(&TraceCompletedPath::without_diagnostics(path.clone()), symtab);
    }

    pub(crate) fn submit_completed_path(&self, path: &TraceCompletedPath, symtab: &Symtab) {
        if let Some(text) = path.render_text(self, symtab) {
            self.writer.submit_text(text);
        }
    }
}

#[cfg(test)]
#[path = "tests.rs"]
mod tests;
