//! 显式开启的通用合并诊断；不发查询，不初始化值，不参与事务或缓存。
use crate::bitvector::BV;
use crate::error::ExecError;
use crate::ir::{BitsSegment, Name, Symtab, Ty, UVal, Val};
use crate::smt::{smtlib, Solver};
use serde_json::{json, Value};
use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicI32, AtomicU8, AtomicUsize, Ordering};
use std::sync::{mpsc, Arc, Mutex, OnceLock};
use std::time::{Duration, Instant};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Off,
    Summary,
    Detail,
}
static MODE: AtomicU8 = AtomicU8::new(0);
static NEXT_ATTEMPT: AtomicUsize = AtomicUsize::new(0);
static COUNTS: OnceLock<Mutex<DiagnosticCounts>> = OnceLock::new();

pub fn configure(value: &str) -> Result<(), String> {
    let mode = match value {
        "off" => Mode::Off,
        "summary" => Mode::Summary,
        "detail" => Mode::Detail,
        _ => return Err("--merge-diagnostics 必须为 off、summary 或 detail".into()),
    };
    MODE.store(
        match mode {
            Mode::Off => 0,
            Mode::Summary => 1,
            Mode::Detail => 2,
        },
        Ordering::Relaxed,
    );
    if mode != Mode::Off {
        super::merge_timing::reset();
        *COUNTS.get_or_init(|| Mutex::new(DiagnosticCounts::new(mode))).lock().unwrap() = DiagnosticCounts::new(mode);
    }
    Ok(())
}

#[inline]
pub fn enabled() -> bool {
    MODE.load(Ordering::Relaxed) != 0
}

#[derive(Clone, Copy)]
pub(crate) enum PathPart {
    Field(Name),
    Index(usize),
    Ctor(Name),
}

pub(crate) struct Failure {
    path: Vec<PathPart>,
    pub difference: &'static str,
    pub left: Value,
    pub right: Value,
    pub error: String,
    path_truncated: bool,
}
impl Failure {
    pub fn path_string(&self, symtab: &Symtab) -> String {
        let mut result = String::new();
        for part in &self.path {
            match part {
                PathPart::Field(name) => result.push_str(&format!(".{}", name_string(*name, symtab))),
                PathPart::Index(index) => result.push_str(&format!("[{index}]")),
                PathPart::Ctor(name) => result.push_str(&format!("<{}>", name_string(*name, symtab))),
            }
        }
        result
    }
    pub fn json(&self, symtab: &Symtab) -> Value {
        json!({"path":self.path_string(symtab), "path_truncated":self.path_truncated,
            "left":decode_shape(self.left.clone(), symtab),"right":decode_shape(self.right.clone(),symtab),
            "difference":self.difference,"error":self.error})
    }
}
#[derive(Default)]
struct TraceState {
    path: Vec<PathPart>,
    depth: usize,
    failure: Option<Failure>,
    swapped: bool,
}
thread_local! {
    static TRACE: RefCell<Option<TraceState>> = const { RefCell::new(None) };
    static ATTEMPTS: RefCell<Vec<Attempt>> = const { RefCell::new(Vec::new()) };
    // 测试在当前线程开启递归观察，避免修改进程开关影响并行用例。
    static TEST_TRACE: Cell<bool> = const { Cell::new(false) };
}
#[inline]
fn trace_enabled() -> bool {
    #[cfg(test)]
    if TEST_TRACE.with(Cell::get) {
        return true;
    }
    enabled()
}

pub(crate) struct ValueTrace {
    previous: Option<TraceState>,
    finished: bool,
    previous_test: bool,
}
impl ValueTrace {
    pub fn start() -> Self {
        Self {
            previous: TRACE.with(|state| state.replace(Some(TraceState::default()))),
            finished: false,
            previous_test: TEST_TRACE.with(Cell::get),
        }
    }
    #[cfg(test)]
    pub fn start_for_test() -> Self {
        let trace = Self::start();
        TEST_TRACE.with(|flag| flag.set(true));
        trace
    }
    pub fn finish(mut self) -> Option<Failure> {
        let current = TRACE.with(|state| state.replace(self.previous.take()));
        self.finished = true;
        TEST_TRACE.with(|flag| flag.set(self.previous_test));
        current.and_then(|state| state.failure)
    }
}
impl Drop for ValueTrace {
    fn drop(&mut self) {
        if !self.finished {
            TRACE.with(|state| state.replace(self.previous.take()));
            TEST_TRACE.with(|flag| flag.set(self.previous_test));
        }
    }
}

pub(crate) fn with_path<T>(part: PathPart, action: impl FnOnce() -> T) -> T {
    if !trace_enabled() {
        return action();
    }
    let active = TRACE.with(|state| {
        let mut state = state.borrow_mut();
        if let Some(state) = state.as_mut() {
            if state.depth < 8 {
                state.path.push(part);
            }
            state.depth += 1;
            true
        } else {
            false
        }
    });
    let result = action();
    if active {
        TRACE.with(|state| {
            let mut state = state.borrow_mut();
            let state = state.as_mut().unwrap();
            state.depth -= 1;
            if state.depth < 8 {
                state.path.pop();
            }
        });
    }
    result
}

pub(crate) fn with_swapped<T>(action: impl FnOnce() -> T) -> T {
    if !trace_enabled() {
        return action();
    }
    TRACE.with(|state| {
        if let Some(state) = state.borrow_mut().as_mut() {
            state.swapped = !state.swapped;
        }
    });
    let result = action();
    TRACE.with(|state| {
        if let Some(state) = state.borrow_mut().as_mut() {
            state.swapped = !state.swapped;
        }
    });
    result
}

/// 首个错误在原递归返回处保存；外层错误映射不能覆盖叶子位置。
pub(crate) fn failed<B: BV>(left: &Val<B>, right: &Val<B>, solver: &Solver<B>, error: &ExecError) {
    if !trace_enabled() {
        return;
    }
    TRACE.with(|state| {
        let mut state = state.borrow_mut();
        if let Some(state) = state.as_mut().filter(|state| state.failure.is_none()) {
            let (left, right) = if state.swapped { (right, left) } else { (left, right) };
            let left = shape(left, solver);
            let right = shape(right, solver);
            state.failure = Some(Failure {
                path: state.path.clone(),
                path_truncated: state.depth > 8,
                difference: difference(&left, &right),
                left,
                right,
                error: bounded_debug(error, 256),
            });
        }
    });
}

/// 限制格式化本身的内存，而不是先生成完整值再截断。
fn bounded_debug(value: &impl std::fmt::Debug, limit: usize) -> String {
    use std::fmt::Write;
    struct Limited {
        text: String,
        limit: usize,
    }
    impl std::fmt::Write for Limited {
        fn write_str(&mut self, text: &str) -> std::fmt::Result {
            for ch in text.chars() {
                if self.text.len() + ch.len_utf8() > self.limit {
                    return Err(std::fmt::Error);
                }
                self.text.push(ch);
            }
            Ok(())
        }
    }
    let mut out = Limited { text: String::new(), limit };
    let result = write!(&mut out, "{value:?}");
    if result.is_err() {
        out.text.push('…');
    }
    out.text
}
pub(crate) fn describe_error(error: &ExecError) -> String {
    bounded_debug(error, 256)
}
fn short(text: &str) -> String {
    text.chars().take(96).collect()
}
pub(crate) fn name_string(name: Name, symtab: &Symtab) -> String {
    let raw = symtab.to_str(name);
    if raw.starts_with('z') {
        short(&crate::zencode::decode(raw))
    } else {
        short(raw)
    }
}
fn sort_name(sort: &smtlib::Ty) -> String {
    match sort {
        smtlib::Ty::BitVec(n) => format!("BV{n}"),
        _ => bounded_debug(sort, 64),
    }
}
fn shape<B: BV>(value: &Val<B>, solver: &Solver<B>) -> Value {
    let kind = match value {
        Val::Symbolic(_) => "Symbolic",
        Val::I64(_) => "I64",
        Val::I128(_) => "I128",
        Val::Bool(_) => "Bool",
        Val::Bits(_) => "Bits",
        Val::MixedBits(_) => "MixedBits",
        Val::String(_) => "String",
        Val::Unit => "Unit",
        Val::Vector(_) => "Vector",
        Val::List(_) => "List",
        Val::Enum(_) => "Enum",
        Val::Struct(_) => "Struct",
        Val::Ctor(..) => "Ctor",
        Val::SymbolicCtor(..) => "SymbolicCtor",
        Val::Ref(_) => "Ref",
        Val::Poison => "Poison",
    };
    let mut result = json!({"raw":"Init","shape":kind});
    match value {
        Val::Symbolic(sym) => {
            result["symbol"] = json!(sym.id);
            if let Some(sort) = solver.scalar_sort(*sym) {
                result["sort"] = json!(sort_name(&sort));
                if let smtlib::Ty::BitVec(n) = sort {
                    result["width"] = json!(n);
                }
            }
        }
        Val::Bits(bits) => {
            result["width"] = json!(bits.len());
            result["sort"] = json!(format!("BV{}", bits.len()));
        }
        Val::I64(_) => {
            result["width"] = json!(64);
            result["sort"] = json!("BV64");
        }
        Val::I128(_) => {
            result["width"] = json!(128);
            result["sort"] = json!("BV128");
        }
        Val::Bool(_) => result["sort"] = json!("Bool"),
        Val::MixedBits(parts) => {
            let mut width = Some(0u32);
            for part in parts {
                let n = match part {
                    BitsSegment::Concrete(bits) => Some(bits.len()),
                    BitsSegment::Symbolic(sym) => match solver.scalar_sort(*sym) {
                        Some(smtlib::Ty::BitVec(n)) => Some(n),
                        _ => None,
                    },
                };
                width = width.zip(n).and_then(|(a, b)| a.checked_add(b));
            }
            if let Some(width) = width {
                result["width"] = json!(width);
                result["sort"] = json!(format!("BV{width}"));
            }
        }
        Val::Ctor(name, _) => result["ctor_id"] = json!(name.as_u32()),
        Val::SymbolicCtor(sym, ctors) => {
            result["symbol"] = json!(sym.id);
            // 只保存有界的标签元数据，不展开载荷。
            let mut first = Vec::new();
            for name in ctors.keys() {
                let pos = first.binary_search(name).unwrap_or_else(|pos| pos);
                if pos < 8 {
                    first.insert(pos, *name);
                    first.truncate(8);
                }
            }
            result["ctor_ids"] = json!(first.iter().map(|n| n.as_u32()).collect::<Vec<_>>());
            result["ctor_count"] = json!(ctors.len());
        }
        Val::Vector(values) | Val::List(values) => result["length"] = json!(values.len()),
        Val::Struct(fields) => {
            let mut first = Vec::new();
            for name in fields.keys() {
                let pos = first.binary_search(name).unwrap_or_else(|pos| pos);
                if pos < 8 {
                    first.insert(pos, *name);
                    first.truncate(8);
                }
            }
            result["field_ids"] = json!(first.iter().map(|n| n.as_u32()).collect::<Vec<_>>());
            result["field_count"] = json!(fields.len());
        }
        _ => (),
    }
    result
}
fn decode_shape(mut value: Value, symtab: &Symtab) -> Value {
    if let Some(id) = value.as_object_mut().unwrap().remove("ctor_id") {
        value["ctor"] = json!(name_string(Name::from_u32(id.as_u64().unwrap() as u32), symtab));
    }
    for (key, target) in [("ctor_ids", "ctors"), ("field_ids", "fields")] {
        if let Some(ids) = value.as_object_mut().unwrap().remove(key) {
            value[target] = json!(ids
                .as_array()
                .unwrap()
                .iter()
                .map(|id| name_string(Name::from_u32(id.as_u64().unwrap() as u32), symtab))
                .collect::<Vec<_>>());
        }
    }
    value
}
pub(crate) fn type_string(ty: &Ty<Name>, symtab: &Symtab) -> String {
    fn render(ty: &Ty<Name>, symtab: &Symtab, depth: usize) -> String {
        if depth == 8 {
            return "…".into();
        }
        match ty {
            Ty::Union(name) => format!("union {}", name_string(*name, symtab)),
            Ty::Struct(name) => format!("struct {}", name_string(*name, symtab)),
            Ty::Enum(name) => format!("enum {}", name_string(*name, symtab)),
            Ty::Vector(inner) | Ty::List(inner) | Ty::Ref(inner) => format!(
                "{}<{}>",
                match ty {
                    Ty::Vector(_) => "Vector",
                    Ty::List(_) => "List",
                    _ => "Ref",
                },
                render(inner, symtab, depth + 1)
            ),
            Ty::FixedVector(n, inner) => format!("Vector[{n}]<{}>", render(inner, symtab, depth + 1)),
            _ => bounded_debug(ty, 96),
        }
    }
    short(&render(ty, symtab, 0))
}
#[derive(Clone, Copy)]
pub(crate) enum RawValue<'a, B> {
    Missing,
    Uninit(&'a Ty<Name>),
    Init(&'a Val<B>),
}
impl<'a, B> RawValue<'a, B> {
    pub fn from_uval(value: Option<&'a UVal<B>>) -> Self {
        match value {
            None => Self::Missing,
            Some(UVal::Uninit(ty)) => Self::Uninit(ty),
            Some(UVal::Init(value)) => Self::Init(value),
        }
    }
    pub fn ty(self) -> Option<&'a Ty<Name>> {
        match self {
            Self::Uninit(ty) => Some(ty),
            _ => None,
        }
    }
    pub fn is_missing(self) -> bool {
        matches!(self, Self::Missing)
    }
}
pub(crate) fn describe_raw<B: BV>(value: RawValue<B>, solver: &Solver<B>, symtab: &Symtab) -> Value {
    match value {
        RawValue::Missing => json!({"raw":"Missing"}),
        RawValue::Uninit(ty) => json!({"raw":"Uninit","decl_type":type_string(ty,symtab)}),
        RawValue::Init(value) => decode_shape(shape(value, solver), symtab),
    }
}
#[cfg(test)]
pub(crate) fn describe_uval<B: BV>(value: Option<&UVal<B>>, solver: &Solver<B>, symtab: &Symtab) -> Value {
    describe_raw(RawValue::from_uval(value), solver, symtab)
}
pub(crate) fn describe_value<B: BV>(value: Option<&Val<B>>, solver: &Solver<B>, symtab: &Symtab) -> Value {
    match value {
        Some(value) => decode_shape(shape(value, solver), symtab),
        None => Value::Null,
    }
}
fn difference(left: &Value, right: &Value) -> &'static str {
    if left["width"].is_number() && right["width"].is_number() && left["width"] != right["width"] {
        return "width_mismatch";
    }
    if left["sort"].is_string() && right["sort"].is_string() && left["sort"] != right["sort"] {
        return "type_mismatch";
    }
    if left["shape"] == "Vector" && right["shape"] == "Vector" && left["length"] != right["length"] {
        return "vector_length";
    }
    if left["shape"] == "Struct"
        && right["shape"] == "Struct"
        && (left["field_count"] != right["field_count"] || left["field_ids"] != right["field_ids"])
    {
        return "struct_fields";
    }
    if matches!(left["shape"].as_str(), Some("Ctor" | "SymbolicCtor"))
        && matches!(right["shape"].as_str(), Some("Ctor" | "SymbolicCtor"))
    {
        return if left["ctor_id"] != right["ctor_id"] || left["ctor_ids"] != right["ctor_ids"] {
            "ctor_set_difference"
        } else {
            "payload_shape"
        };
    }
    if left["shape"] != right["shape"] && left["shape"] != "Symbolic" && right["shape"] != "Symbolic" {
        return "type_mismatch";
    }
    if matches!(left["shape"].as_str(), Some("I64" | "I128" | "String" | "Ref" | "List"))
        && left["shape"] == right["shape"]
    {
        return "concrete_required";
    }
    "unsupported_value"
}

struct Attempt {
    id: usize,
    parent: Option<usize>,
    task: usize,
    origin: Value,
    root: Option<usize>,
}
pub(crate) struct AttemptGuard {
    timing: super::merge_timing::AttemptGuard,
}
impl AttemptGuard {
    pub fn start(task: usize, function: Name, pc: usize, symtab: &Symtab) -> Self {
        let origin = json!({"function":name_string(function,symtab),"function_id":function.as_u32(),"pc":pc});
        let timing = super::merge_timing::AttemptGuard::start(origin.clone());
        ATTEMPTS.with(|stack| {
            let mut stack = stack.borrow_mut();
            let parent = stack.last().map(|attempt| attempt.id);
            stack.push(Attempt { id: NEXT_ATTEMPT.fetch_add(1, Ordering::Relaxed), parent, task, origin, root: None });
        });
        Self { timing }
    }
    pub fn finish(&mut self, reason: Option<super::SpeculativeRejectReason>) {
        self.timing.finish(reason.map_or_else(|| "success".into(), |reason| reason.to_string()));
    }
}
impl Drop for AttemptGuard {
    fn drop(&mut self) {
        ATTEMPTS.with(|stack| {
            let mut stack = stack.borrow_mut();
            let attempt = stack.pop().unwrap();
            if let (Some(parent), Some(root)) = (stack.last_mut(), attempt.root) {
                parent.root = Some(root);
            }
        });
    }
}
pub(crate) fn emit(mut record: Value) {
    if !enabled() {
        return;
    }
    ATTEMPTS.with(|stack| {
        let mut stack = stack.borrow_mut();
        if let Some(attempt) = stack.last_mut() {
            record["attempt"] = json!(attempt.id);
            record["parent_attempt"] = json!(attempt.parent);
            record["task"] = json!(attempt.task);
            record["origin"] = attempt.origin.clone();
            attempt.root = Some(attempt.id);
        }
    });
    record["schema"] = json!(1);
    record["kind"] = json!("merge_value_reject");
    if let Some(line) = COUNTS.get().unwrap().lock().unwrap().record(&record) {
        eprintln!("{line}");
    }
}
pub(crate) fn unattributed_error(function: Name, pc: usize, error: &ExecError, symtab: &Symtab) {
    let recorded = ATTEMPTS.with(|stack| stack.borrow().last().is_some_and(|attempt| attempt.root.is_some()));
    if !recorded {
        emit(json!({"stage":"execute_arm","at":{"function":name_string(function,symtab),"pc":pc},
            "slot":null,"path":null,"left":null,"right":null,"difference":"unsupported_value",
            "error":bounded_debug(error,256),"reason":"incompatible_state"}));
    }
}

pub(crate) fn propagated() {
    if !enabled() {
        return;
    }
    let propagation = ATTEMPTS.with(|stack| {
        let stack = stack.borrow();
        let attempt = stack.last()?;
        attempt.root.filter(|root| *root != attempt.id).map(|root| (attempt.id, root))
    });
    if let Some((attempt, root)) = propagation {
        let mut counts = COUNTS.get().unwrap().lock().unwrap();
        counts.propagated += 1;
        if counts.mode == Mode::Detail && counts.details_emitted < 1000 {
            counts.details_emitted += 1;
            eprintln!(
                "{}",
                json!({"schema":1,"kind":"merge_value_propagated","attempt":attempt,"propagated_from":root})
            );
        } else if counts.mode == Mode::Detail {
            counts.details_suppressed += 1;
        }
    }
}
/// 执行臂内没有双臂槽时，明确留下空槽；只在原始错误映射处调用。
pub(crate) fn execute_arm_error(function: Name, pc: usize, error: &ExecError, symtab: &Symtab) {
    if !enabled()
        || matches!(
            error,
            ExecError::SpeculativeReject { .. } | ExecError::Smt(_) | ExecError::Timeout | ExecError::Z3Unknown
        )
    {
        return;
    }
    emit(json!({"stage":"execute_arm","at":{"function":name_string(function,symtab),"pc":pc},
        "slot":null,"path":null,"left":null,"right":null,"difference":"unsupported_value",
        "error":bounded_debug(error,256),"reason":"incompatible_state"}));
}

pub(super) struct DiagnosticCounts {
    mode: Mode,
    keys: BTreeMap<String, (u64, u8)>,
    differences: BTreeMap<String, u64>,
    total: u64,
    other: u64,
    details_emitted: u64,
    details_suppressed: u64,
    propagated: u64,
    oversized: u64,
}
impl DiagnosticCounts {
    pub fn new(mode: Mode) -> Self {
        Self {
            mode,
            keys: BTreeMap::new(),
            differences: BTreeMap::new(),
            total: 0,
            other: 0,
            details_emitted: 0,
            details_suppressed: 0,
            propagated: 0,
            oversized: 0,
        }
    }
    pub fn record(&mut self, record: &Value) -> Option<String> {
        if self.mode == Mode::Off {
            return None;
        }
        self.total += 1;
        *self.differences.entry(record["difference"].as_str().unwrap().to_string()).or_default() += 1;
        let key = json!({"stage":record["stage"],"origin":record["origin"],"at":record["at"],
            "reason":record["reason"],"slot":record["slot"],"path":record["path"],"left_shape":record["left"]["shape"],
            "right_shape":record["right"]["shape"],"left_sort":record["left"]["sort"],
            "right_sort":record["right"]["sort"],"left_raw":record["left"]["raw"],"right_raw":record["right"]["raw"],"difference":record["difference"]})
        .to_string();
        // 4096×1024 字节的键，加计数和树节点，保持在建议的 8 MiB 内。
        if key.len() > 1024 || (!self.keys.contains_key(&key) && self.keys.len() == 4096) {
            self.other += 1;
            if self.mode == Mode::Detail {
                self.details_suppressed += 1;
            }
            return None;
        }
        let entry = self.keys.entry(key).or_default();
        entry.0 += 1;
        if self.mode != Mode::Detail {
            return None;
        }
        if entry.1 >= 3 || self.details_emitted >= 1000 {
            self.details_suppressed += 1;
            return None;
        }
        let line = record.to_string();
        if line.len() > 4096 {
            self.oversized += 1;
            self.details_suppressed += 1;
            return None;
        }
        entry.1 += 1;
        self.details_emitted += 1;
        Some(line)
    }
    fn totals(&self) -> Value {
        json!({"schema":1,"kind":"merge_value_summary","total":self.total,
            "differences":self.differences,"propagated":self.propagated,"other":self.other,
            "details_emitted":self.details_emitted,"details_suppressed":self.details_suppressed,
            "oversized":self.oversized,"key_count":self.keys.len()})
    }
    #[cfg(test)]
    pub fn summary(&self) -> Option<Value> {
        if self.mode == Mode::Off {
            return None;
        }
        let mut result = self.totals();
        result["keys"] = json!(self
            .keys
            .iter()
            .map(|(key, (count, _))| json!({"key":serde_json::from_str::<Value>(key).unwrap(),"count":count}))
            .collect::<Vec<_>>());
        Some(result)
    }
}
/// 每组累计快照带编号；末行是完整组的标记，不清空计数。
fn print_with_trigger(trigger: &str) {
    if !enabled() {
        return;
    }
    use std::io::Write;
    static SNAPSHOT: AtomicUsize = AtomicUsize::new(0);
    let counts = COUNTS.get().unwrap().lock().unwrap();
    let snapshot = SNAPSHOT.fetch_add(1, Ordering::Relaxed);
    // 整组持有 stderr 锁，避免 worker 日志插入 JSON 行。
    let mut out = std::io::stderr().lock();
    for (key, (count, _)) in &counts.keys {
        writeln!(
            out,
            "{}",
            json!({"schema":1,"kind":"merge_value_summary_key","snapshot":snapshot,
            "key":serde_json::from_str::<Value>(key).unwrap(),"count":count})
        )
        .unwrap();
    }
    super::merge_timing::write_snapshot(&mut out, snapshot, trigger);
    let mut totals = counts.totals();
    totals["snapshot"] = json!(snapshot);
    totals["trigger"] = json!(trigger);
    writeln!(out, "{totals}").unwrap();
    out.flush().unwrap();
}
pub(crate) fn print() {
    print_with_trigger("final");
}

static TERMINATION: AtomicI32 = AtomicI32::new(0);
extern "C" fn request_termination(signal: libc::c_int) {
    // 与现有取消处理一样，信号处理器只置标志；禁止在此格式化或加锁。
    TERMINATION.store(signal, Ordering::Relaxed);
}

/// 复用统计快照线程与节奏；诊断开启时额外检查终止标志，退出作用域即回收线程。
pub struct SnapshotReporter {
    stop: Option<mpsc::Sender<()>>,
    worker: Option<std::thread::JoinHandle<()>>,
    handlers: Vec<(i32, libc::sigaction)>,
}
impl SnapshotReporter {
    pub fn start(stats: Arc<super::ExecutionStats>, interval: Duration) -> Self {
        let diagnostic = enabled();
        let mut reporter = Self { stop: None, worker: None, handlers: Vec::new() };
        if !diagnostic && !stats.enabled() && !super::memory_stats::enabled() {
            return reporter;
        }
        assert!(!interval.is_zero());
        if diagnostic {
            TERMINATION.store(0, Ordering::Relaxed);
            unsafe {
                for signal in [libc::SIGINT, libc::SIGTERM] {
                    let mut action: libc::sigaction = std::mem::zeroed();
                    let mut previous: libc::sigaction = std::mem::zeroed();
                    action.sa_sigaction = request_termination as *const () as usize;
                    libc::sigemptyset(&mut action.sa_mask);
                    assert_eq!(libc::sigaction(signal, &action, &mut previous), 0);
                    reporter.handlers.push((signal, previous));
                }
            }
        }
        let handlers = reporter.handlers.clone();
        let (stop, receiver) = mpsc::channel();
        reporter.stop = Some(stop);
        reporter.worker = Some(std::thread::spawn(move || {
            let mut deadline = Instant::now() + interval;
            loop {
                let remaining = deadline.saturating_duration_since(Instant::now());
                let wait = if diagnostic { remaining.min(Duration::from_millis(100)) } else { remaining };
                match receiver.recv_timeout(wait) {
                    Ok(()) | Err(mpsc::RecvTimeoutError::Disconnected) => return,
                    Err(mpsc::RecvTimeoutError::Timeout) => (),
                }
                if diagnostic {
                    let signal = TERMINATION.swap(0, Ordering::Relaxed);
                    if signal != 0 {
                        print_with_trigger("signal");
                        super::memory_stats::print();
                        // 恢复原动作后重新投递，保留默认的信号退出状态或原处理器行为。
                        let previous = &handlers.iter().find(|(number, _)| *number == signal).unwrap().1;
                        unsafe {
                            assert_eq!(libc::sigaction(signal, previous, std::ptr::null_mut()), 0);
                            assert_eq!(libc::raise(signal), 0);
                        }
                        return;
                    }
                }
                if Instant::now() >= deadline {
                    print_with_trigger("periodic");
                    super::memory_stats::print();
                    if stats.enabled() {
                        let (merge, forks, arms) = stats.snapshot_json();
                        eprintln!("[MERGE_STATS_SNAPSHOT] {}", merge);
                        eprintln!("[FORK_STATS_SNAPSHOT] {}", forks);
                        eprintln!("[ARM_UNSUPPORTED_SNAPSHOT] {}", arms);
                    }
                    deadline = Instant::now() + interval;
                }
            }
        }));
        reporter
    }
}
impl Drop for SnapshotReporter {
    fn drop(&mut self) {
        if let Some(stop) = self.stop.take() {
            // 接收端可已在重新投递信号后退出。
            match stop.send(()) {
                Ok(()) | Err(_) => (),
            }
        }
        if let Some(worker) = self.worker.take() {
            worker.join().unwrap();
        }
        super::memory_stats::print();
        unsafe {
            for (signal, previous) in &self.handlers {
                assert_eq!(libc::sigaction(*signal, previous, std::ptr::null_mut()), 0);
            }
        }
    }
}
#[cfg(test)]
pub(crate) fn summary_for_test() -> Value {
    COUNTS.get().unwrap().lock().unwrap().summary().unwrap()
}
