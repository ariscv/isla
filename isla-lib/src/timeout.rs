use std::collections::BTreeMap;
use std::fmt;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use crate::source_loc::SourceLoc;

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct PathTimeSnapshot {
    pub active_wall: Duration,
    pub executor_cpu: Duration,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SmtOperation {
    CheckSat,
    CheckSatAssuming,
    ModelEval,
}

/// Dump 时使用的 SMT symbol 名称快照。
#[derive(Clone, Debug, Default)]
pub struct SmtDumpNames {
    symbol_names: BTreeMap<u32, String>,
    ir_names: BTreeMap<u32, String>,
    enum_members: BTreeMap<u32, Vec<String>>,
}

impl SmtDumpNames {
    pub(crate) fn insert_ir_name(&mut self, name_id: u32, name: String) {
        self.ir_names.insert(name_id, name);
    }

    pub(crate) fn insert_enum_members(&mut self, enum_id: u32, members: Vec<String>) {
        self.enum_members.insert(enum_id, members);
    }

    pub(crate) fn bind_symbol_to_ir_name(&mut self, symbol_id: u32, name_id: u32) {
        let name = self.ir_names.get(&name_id).expect("SMT dump symbol references an unknown IR name");
        let candidate = format!("isla_{}__s{}", name, symbol_id);
        match self.symbol_names.get_mut(&symbol_id) {
            Some(existing) if candidate < *existing => *existing = candidate,
            Some(_) => (),
            None => {
                self.symbol_names.insert(symbol_id, candidate);
            }
        }
    }

    pub(crate) fn symbol_name(&self, symbol_id: u32) -> String {
        self.symbol_names.get(&symbol_id).cloned().unwrap_or_else(|| format!("isla_s{}", symbol_id))
    }

    pub(crate) fn enum_sort_name(&self, enum_id: u32) -> String {
        self.ir_names
            .get(&enum_id)
            .map(|name| format!("isla_{}__n{}", name, enum_id))
            .unwrap_or_else(|| format!("isla_s{}", enum_id))
    }

    pub(crate) fn enum_member_name(&self, enum_id: u32, member: usize, generated_symbol_id: u32) -> String {
        self.enum_members
            .get(&enum_id)
            .and_then(|members| members.get(member))
            .map(|name| format!("isla_{}__e{}_m{}", name, enum_id, member))
            .unwrap_or_else(|| format!("isla_s{}", generated_symbol_id))
    }

    fn merge(&mut self, other: Self) {
        for (name_id, name) in other.ir_names {
            self.ir_names.entry(name_id).or_insert(name);
        }
        for (enum_id, members) in other.enum_members {
            self.enum_members.entry(enum_id).or_insert(members);
        }
        for (symbol_id, name) in other.symbol_names {
            match self.symbol_names.get_mut(&symbol_id) {
                Some(existing) if name < *existing => *existing = name,
                Some(_) => (),
                None => {
                    self.symbol_names.insert(symbol_id, name);
                }
            }
        }
    }
}

pub trait SmtDumpSource: Send + Sync {
    fn materialize(&self) -> Result<String, String>;

    fn materialize_with_names(&self, _names: &SmtDumpNames) -> Result<String, String> {
        self.materialize()
    }
}

pub struct TimeoutSmtDump {
    source: Arc<dyn SmtDumpSource>,
    names: Mutex<SmtDumpNames>,
    materialized: Mutex<Option<Result<Arc<str>, Arc<str>>>>,
}

impl TimeoutSmtDump {
    pub fn new(source: Arc<dyn SmtDumpSource>) -> Self {
        TimeoutSmtDump { source, names: Mutex::new(SmtDumpNames::default()), materialized: Mutex::new(None) }
    }

    pub(crate) fn configure_names(&self, names: SmtDumpNames) {
        let materialized = self.materialized.lock().expect("timeout SMT dump cache poisoned");
        assert!(materialized.is_none(), "SMT dump names were configured after materialization");
        self.names.lock().expect("timeout SMT dump names poisoned").merge(names);
    }

    pub fn materialize(&self) -> Result<Arc<str>, Arc<str>> {
        let mut materialized = self.materialized.lock().expect("timeout SMT dump cache poisoned");
        if let Some(result) = materialized.as_ref() {
            return result.clone();
        }

        let names = self.names.lock().expect("timeout SMT dump names poisoned").clone();
        let result = self.source.materialize_with_names(&names).map(Arc::<str>::from).map_err(Arc::<str>::from);
        *materialized = Some(result.clone());
        result
    }

    pub fn is_materialized(&self) -> bool {
        self.materialized.lock().expect("timeout SMT dump cache poisoned").is_some()
    }
}

impl fmt::Debug for TimeoutSmtDump {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TimeoutSmtDump").field("materialized", &self.is_materialized()).finish()
    }
}

#[derive(Debug)]
pub struct SmtTimeout {
    pub source_loc: SourceLoc,
    pub operation: SmtOperation,
    pub limit: Duration,
    pub operation_wall: Duration,
    pub dump: Arc<TimeoutSmtDump>,
}

impl SmtTimeout {
    pub fn source_loc(&self) -> SourceLoc {
        self.source_loc
    }
}

#[derive(Clone, Debug)]
pub enum TimeoutDiagnostic {
    Smt(Arc<SmtTimeout>),
}

impl TimeoutDiagnostic {
    pub fn metadata_lines(&self) -> Vec<String> {
        let TimeoutDiagnostic::Smt(timeout) = self;
        let lines = vec![
            "timeout_kind: smt".to_string(),
            format!("operation: {:?}", timeout.operation),
            format!("limit: {:?}", timeout.limit),
            format!("operation_wall: {:?}", timeout.operation_wall),
        ];
        lines
    }

    pub fn dump(&self) -> Arc<TimeoutSmtDump> {
        match self {
            TimeoutDiagnostic::Smt(timeout) => timeout.dump.clone(),
        }
    }
}

pub fn append_path_timing_lines(lines: &mut Vec<String>, timing: PathTimeSnapshot) {
    lines.push(format!("active_wall: {:?}", timing.active_wall));
    lines.push(format!("executor_cpu: {:?}", timing.executor_cpu));
}
