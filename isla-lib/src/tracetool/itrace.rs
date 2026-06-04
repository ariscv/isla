use crate::bitvector::BV;
use crate::executor::Backtrace;
use crate::ir::{Instr, Name, SharedState};
use crate::zencode;
use std::fs;
use std::io::Write;
use std::ops::Deref;
use std::path::{Path, PathBuf};

#[derive(Clone, Default)]
pub struct BacktraceString(Vec<(String, usize)>);

impl Deref for BacktraceString {
    type Target = [(String, usize)];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl BacktraceString {
    pub fn get_function_name(&self) -> Option<&String> {
        self.last().map(|(name, _)| name)
    }
}

pub trait ToBacktraceStringWithSharedState {
    fn to_backtrace_string<B: BV>(&self, shared_state: &SharedState<B>) -> BacktraceString;
}

impl ToBacktraceStringWithSharedState for Backtrace {
    fn to_backtrace_string<B: BV>(&self, shared_state: &SharedState<B>) -> BacktraceString {
        BacktraceString(self.iter().map(|(name, pc)| (shared_state.symtab.to_str(*name).to_string(), *pc)).collect())
    }
}

#[derive(Clone)]
pub struct ItracePerInstr {
    pub seq: u64,
    pub backtrace: BacktraceString,
    pub pc: u64,
    pub opcode: String,
    pub summary: Option<String>,
}
impl ItracePerInstr {
    fn backtrace_to_string(&self) -> String {
        if self.backtrace.is_empty() {
            "-".to_string()
        } else {
            self.backtrace.iter().map(|(name, pc)| format!("{}:{}", name, pc)).collect::<Vec<_>>().join(" -> ")
        }
    }

    pub fn dump(&self) -> String {
        format!(
            "{}\t{}\t{}\t{}\t{}",
            self.seq,
            self.pc,
            self.opcode,
            self.backtrace_to_string(),
            self.summary.clone().unwrap_or_else(|| "-".to_string())
        )
    }
}
#[derive(Default, Clone)]
struct ItracePerPath {
    title: String, // ItracePerPath.title=ItraceHandler.title+<path_condition>
    ir_file_path: PathBuf,
    records: Vec<ItracePerInstr>,
    output_path: Option<PathBuf>,
    next_seq: u64,
}

impl ItracePerPath {
    pub fn init(title: String, ir_file_path: PathBuf, output_path: Option<PathBuf>) -> Self {
        Self { title, ir_file_path, output_path, records: Vec::new(), next_seq: 0 }
    }
    pub fn record(&mut self, backtrace: BacktraceString, pc: u64, opcode: String, summary: Option<String>) {
        let seq = self.next_seq + 1;
        self.next_seq = seq;
        self.records.push(ItracePerInstr { seq, backtrace, pc, opcode, summary });
    }
    pub fn record_with_sharedstate<B: BV>(
        &mut self,
        shared_state: &SharedState<B>,
        backtrace: Backtrace,
        pc: u64,
        opcode: String,
        summary: Option<String>,
    ) {
        self.record(backtrace.to_backtrace_string(shared_state), pc, opcode, summary);
    }
    pub fn dump(&self) -> String {
        self.records.iter().map(ItracePerInstr::dump).collect::<Vec<_>>().join("\n")
    }
}

#[derive(Default)]
pub struct ItraceHandler {
    title: String,
    itrace_perpath: Vec<ItracePerPath>,
}

impl ItraceHandler {
    pub fn init(title: &str, ir_file_path: PathBuf, output_path: Option<PathBuf>) -> Self {
        let init_title = format!("{}_init", title);
        Self {
            title: title.to_string(),
            itrace_perpath: vec![ItracePerPath::init(init_title, ir_file_path, output_path)],
        }
    }

    pub fn create_path(&self) -> &ItracePerPath {
		// let itrace_per_path = ItracePerPath::init(self.title.clone(), PathBuf::new(), None);
		// self.itrace_perpath.push(itrace_per_path);
		// self.itrace_perpath.last().unwrap()
	}
	pub fn fork_path(&self, based_path: &ItracePerPath,path_condition: String) -> &ItracePerPath{
		// self.create_path(path_condition)
	}



    pub fn dump(&self) {}
}

