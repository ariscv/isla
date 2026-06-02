use crate::bitvector::BV;
use crate::ir::{Loc, Name, SharedState, Val};
use crate::source_loc::SourceLoc;
use crate::zencode;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

pub struct ItraceRecord {
    pub seq: u64,
	pub backtree: Vec<String>,
	pub pc: u64,
    pub opcode: String,
    pub summary: Option<String>,
}
impl ItraceRecord{

}
#[derive(Default)]
struct Itrace {
	ir_file_path: PathBuf,
    records: Vec<ItraceRecord>,
    output_path: Option<PathBuf>,
}

impl Itrace {
    pub fn new(ir_file_path: PathBuf, output_path: Option<PathBuf>) -> Self {
        Self { ir_file_path, output_path, records: Vec::new() }
    }
    pub fn record(&mut self, backtree: Vec<String>, pc: u64, opcode: String, summary: Option<String>) {
        let seq = self.records.last().map_or(1, |last| last.seq + 1);
        self.records.push(ItraceRecord { seq, backtree, pc, opcode, summary });
    }
}

#[derive(Default)]
pub struct ItraceHandler {
    sink: Mutex<Itrace>,
}

impl ItraceHandler {
    pub fn set_path(&self, path: Option<PathBuf>) {
        let mut sink = self.sink.lock().unwrap();
        sink.output_path = path;
        sink.enabled = sink.output_path.is_some();
        sink.next_seq = 0;
        sink.records.clear();
    }

    pub fn record<B: BV>(&self, opcode: &Val<B>, shared_state: &SharedState<B>, addr: &str, summary: Option<String>) {
        let mut sink = self.sink.lock().unwrap();
        if !sink.enabled {
            return;
        }

        sink.next_seq += 1;
        let seq = sink.next_seq;
        sink.records.push(ItraceRecord {
            seq,
            opcode: opcode.to_string(shared_state),
            addr: addr.to_string(),
            summary,
        });
    }

    pub fn record_at_loc<B: BV>(&self, opcode: &Val<B>, shared_state: &SharedState<B>, info: &SourceLoc) {
        let summary = match opcode {
            Val::Ctor(ctor, _) => Some(opcode_name(shared_state, *ctor)),
            _ => None,
        };
        self.record(opcode, shared_state, &info.location_string(shared_state.symtab.files()), summary)
    }

    pub fn dump(&self) -> std::io::Result<()> {
        let mut sink = self.sink.lock().unwrap();
        let path = match sink.output_path.as_deref() {
            Some(path) => path.to_path_buf(),
            None => return Ok(()),
        };

        if sink.records.is_empty() {
            return Ok(());
        }

        dump_records_to_path(&path, &sink.records)?;

        sink.enabled = false;
        sink.records.clear();
        sink.next_seq = 0;
        Ok(())
    }
}

fn dump_records_to_path(path: &Path, records: &[ItraceRecord]) -> std::io::Result<()> {
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent)?;
        }
    }

    let content = records
        .iter()
        .map(|record| {
            let summary = record.summary.as_deref().unwrap_or("-");
            format!("{}\t{}\t{}\t{}\n", record.seq, record.addr, summary, record.opcode)
        })
        .collect::<Vec<_>>()
        .join("");

    fs::write(path, content)
}

fn opcode_name<B: BV>(shared_state: &SharedState<B>, ctor: Name) -> String {
    zencode::decode(shared_state.symtab.to_str_demangled(ctor)).to_string()
}
