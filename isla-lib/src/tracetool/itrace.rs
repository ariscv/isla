use crate::executor::Backtrace;
use crate::ir::{Name, Symtab};
use crate::smt::{smtlib, Sym};
use crossbeam::queue::SegQueue;
use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};

/*
 * Core runtime state
 *
 * 运行时热路径只记录必要状态并提交已完成 path，优先考虑存储效率和提交速度。
 */

#[derive(Clone)]
pub struct ItracePerInstr {
    pub function_name: Name,
    pub backtrace: Backtrace,
    pub pc: u64,
    pub summary: Option<String>,
}

#[derive(Clone, Default)]
pub(crate) struct ItracePerPath {
    records: Vec<ItracePerInstr>,
    branch_conditions: Vec<smtlib::Exp<Sym>>,
}

impl ItracePerPath {
    pub fn record(&mut self, function_name: Name, backtrace: Backtrace, pc: u64) {
        self.records.push(ItracePerInstr { function_name, backtrace, pc, summary: None });
    }

    pub fn records(&self) -> &[ItracePerInstr] {
        self.records.as_slice()
    }

    pub fn push_branch_condition(&mut self, condition: smtlib::Exp<Sym>) {
        self.branch_conditions.push(condition);
    }
}

// 识别 `fn name(...) {` 形式的函数头，返回 z-encoded 函数名。
fn try_parse_fn_header(line: &str) -> Option<String> {
    let rest = line.strip_prefix("fn ")?;
    let paren_pos = rest.find('(')?;
    let name = rest[..paren_pos].trim();
    Some(name.to_string())
}

// 用花括号深度判断当前函数体是否结束；IR fixture 中函数体按 `{}` 包围。
fn count_braces(line: &str) -> i32 {
    line.chars().fold(0, |acc, ch| match ch {
        '{' => acc + 1,
        '}' => acc - 1,
        _ => acc,
    })
}

// 只接受 Isla IR 末尾 source location 的两种形态：纯数字 id，或 `file line:col-line:col`。
fn is_source_loc(segment: &str) -> bool {
    if segment.chars().all(|c| c.is_ascii_digit()) {
        return !segment.is_empty();
    }

    let mut parts = segment.split_whitespace().collect::<Vec<_>>();
    if parts.len() != 2 {
        return false;
    }

    let file = parts.remove(0);
    if !file.chars().all(|c| c.is_ascii_digit()) {
        return false;
    }

    let range = parts.remove(0);

    let mut range_parts = range.splitn(2, ':');
    let Some(line1) = range_parts.next() else {
        return false;
    };
    let Some(start_colon_pos) = range_parts.next() else {
        return false;
    };

    if !line1.chars().all(|c| c.is_ascii_digit()) {
        return false;
    }

    let mut end_parts = start_colon_pos.splitn(2, '-');
    let Some(char1) = end_parts.next() else {
        return false;
    };
    let Some(line2_colon_char2) = end_parts.next() else {
        return false;
    };
    if end_parts.next().is_some() {
        return false;
    }

    if !char1.chars().all(|c| c.is_ascii_digit()) {
        return false;
    }

    let mut line2_parts = line2_colon_char2.split(':');
    let Some(line2) = line2_parts.next() else {
        return false;
    };
    let Some(char2) = line2_parts.next() else {
        return false;
    };
    if line2_parts.next().is_some() {
        return false;
    }

    line2.chars().all(|c| c.is_ascii_digit()) && char2.chars().all(|c| c.is_ascii_digit())
}

pub fn strip_source_loc(ir_line: &str) -> String {
    let trimmed = ir_line.trim_end();

    if let Some(start) = trimmed.rfind('`') {
        let suffix = &trimmed[start + 1..];
        let suffix = suffix.trim_end_matches(|c: char| c == ';' || c.is_whitespace());

        if is_source_loc(suffix) {
            return format!("{};", trimmed[..start].trim_end());
        }
    }

    ir_line.to_string()
}

/*
 * IR 文件缓存
 *
 * 这个 cache 是 itrace 输出阶段的内部实现细节，用来加速从
 * `(function_name, pc)` 查找 `.ir` 文件中的一行文本。
 *
 * 工作流程：
 * 1. `ItraceHandler::init` 或 `ItraceHandler::configure` 调用
 *    `IrFileCache::from_file` 扫描 `.ir` 文件。
 * 2. `from_file` 以 `fn name(...) { ... }` 为边界切分函数体，去掉空行和末尾
 *    source location，把每个函数体保存成 `Vec<String>`。
 * 3. 函数名通过 `Symtab::get` 转成 `Name`，所以缓存键和执行器记录的
 *    `ItracePerInstr::function_name` 保持一致。
 * 4. 执行器只调用 `ItraceHandler::submit_path` 提交完成的 path；handler 内部渲染时再
 *    持锁委托给 `IrFileCache::lookup_line(function_name, pc)`。
 *
 * 例子：
 * - `.ir` 文件中存在 `fn zcache_ok(...) { z0 : %i `1; ... return = z1 `4; }`。
 * - 构建 cache 后，`zcache_ok` 会经 `Symtab::get("zcache_ok")` 转成 `Name`，
 *   函数体非空行会按顺序缓存为 `[ "z0 : %i;", ..., "return = z1;" ]`。
 * - 执行器记录到 `ItracePerInstr { function_name: zcache_ok_name, pc: 3, ... }`
 *   时，handler 内部渲染阶段会调用 `lookup_ir_line(zcache_ok_name, 3, symtab)`。
 * - `lookup_line` 把 `pc = 3` 当作数组下标，返回第 4 条缓存行，例如
 *   `"return = z1;"`；如果下标越界，则返回 `None`，上层输出 `zcache_ok:3 not found`。
 *
 * 使用约定：
 * - 外部代码不要直接访问缓存结构，也不要依赖 `HashMap<Name, Vec<String>>`
 *   这个存储形态；只提交 `ItracePerPath`，由 handler 内部查 IR 行并输出。
 * - `pc` 被当作函数体行向量下标使用，因此 `.ir` 缓存规则必须和
 *   `SharedState` 中同一函数的指令顺序一致。
 * - 构建失败、函数缺失、pc 越界或锁中毒都会返回 `None`，调用方负责降级输出。
 */
#[derive(Default)]
struct IrFileCache {
    // 像一张“函数名 -> 函数体 IR 行列表”的表：zcache_ok -> ["z0 : %i;", ..., "return = z1;"]。
    functions: HashMap<Name, Vec<String>>,
}

impl IrFileCache {
    fn from_file(ir_file_path: &PathBuf, symtab: &Symtab) -> Self {
        // 这里使用的是已经完成 IR parse 的同一个文件；打不开说明调用方违反了前置条件。
        let file = File::open(ir_file_path).unwrap_or_else(|error| {
            panic!("IR file should be openable after successful IR parse: {} ({})", ir_file_path.display(), error)
        });
        let reader = BufReader::new(file);
        let mut functions = HashMap::new();
        let mut current_fn: Option<String> = None;
        let mut current_lines: Vec<String> = Vec::new();
        let mut brace_depth: i32 = 0;

        for line in reader.lines() {
            let line = match line {
                Ok(l) => l,
                Err(_) => continue,
            };
            let trimmed = line.trim();

            // 遇到函数头时开始收集一个新的函数体；函数名仍是 IR 里的 z-encoded 名字。
            if let Some(fn_name) = try_parse_fn_header(trimmed) {
                current_fn = Some(fn_name);
                current_lines = Vec::new();
                brace_depth = count_braces(trimmed);
                continue;
            }

            if current_fn.is_some() {
                // 用花括号深度判断函数体是否结束，避免把下一个函数的行收进当前函数。
                brace_depth += count_braces(trimmed);

                if brace_depth <= 0 {
                    // 函数结束时才把本函数的行放进局部表；IrFileCache 本身构建完成后只读。
                    if let Some(name) = current_fn.take().and_then(|name| symtab.get(&name)) {
                        functions.insert(name, current_lines.clone());
                    }
                    current_lines.clear();
                    brace_depth = 0;
                    continue;
                }

                // cache 只保存输出要展示的 IR 文本，不保留空行和末尾 source location。
                let stripped = strip_source_loc(trimmed);
                if !stripped.is_empty() {
                    current_lines.push(stripped);
                }
            }
        }

        Self { functions }
    }

    fn lookup_line(&self, function_name: Name, pc: u64) -> Option<String> {
        let pc_index = usize::try_from(pc).ok()?;
        self.functions.get(&function_name)?.get(pc_index).map(|line| strip_source_loc(line))
    }
}

impl smtlib::Exp<Sym> {
    fn to_itrace_string(&self, symtab: &Symtab) -> String {
        use smtlib::Exp::*;

        let sym_to_string = |sym: Sym| {
            let sym_id = sym.to_string();
            let Some(id) = sym_id.parse::<u32>().ok() else {
                return format!("v{}", sym);
            };
            let name = Name::from_u32(id);
            let name_str = symtab.to_str(name);
            if name_str == "zUNKNOWN" {
                format!("v{}", sym)
            } else {
                name_str.to_string()
            }
        };

        match self {
            Var(sym) => sym_to_string(*sym),
            Bits(bits) => {
                let bits = bits.iter().rev().map(|bit| if *bit { '1' } else { '0' }).collect::<String>();
                format!("#b{}", bits)
            }
            Bits64(bits) => bits.to_string(),
            Enum(member) => format!("{:?}", member),
            Bool(value) => value.to_string(),
            Eq(lhs, rhs) => format!("({} == {})", lhs.to_itrace_string(symtab), rhs.to_itrace_string(symtab)),
            Neq(lhs, rhs) => format!("({} != {})", lhs.to_itrace_string(symtab), rhs.to_itrace_string(symtab)),
            And(lhs, rhs) => format!("({} && {})", lhs.to_itrace_string(symtab), rhs.to_itrace_string(symtab)),
            Or(lhs, rhs) => format!("({} || {})", lhs.to_itrace_string(symtab), rhs.to_itrace_string(symtab)),
            Not(value) => format!("!{}", value.to_itrace_string(symtab)),
            Bvnot(value) => format!("bvnot({})", value.to_itrace_string(symtab)),
            Bvneg(value) => format!("bvneg({})", value.to_itrace_string(symtab)),
            Extract(hi, lo, value) => format!("extract({}, {}, {})", hi, lo, value.to_itrace_string(symtab)),
            ZeroExtend(width, value) => format!("zero_extend({}, {})", width, value.to_itrace_string(symtab)),
            SignExtend(width, value) => format!("sign_extend({}, {})", width, value.to_itrace_string(symtab)),
            Ite(cond, then_value, else_value) => format!(
                "ite({}, {}, {})",
                cond.to_itrace_string(symtab),
                then_value.to_itrace_string(symtab),
                else_value.to_itrace_string(symtab)
            ),
            App(sym, args) => format!(
                "{}({})",
                sym_to_string(*sym),
                args.iter().map(|arg| arg.to_itrace_string(symtab)).collect::<Vec<_>>().join(", ")
            ),
            Distinct(values) => format!(
                "distinct({})",
                values.iter().map(|value| value.to_itrace_string(symtab)).collect::<Vec<_>>().join(", ")
            ),
            FPConstant(value, ebits, sbits) => format!("fp_constant({:?}, {}, {})", value, ebits, sbits),
            FPRoundingMode(value) => format!("{:?}", value),
            FPUnary(op, value) => format!("{:?}({})", op, value.to_itrace_string(symtab)),
            FPRoundingUnary(op, rm, value) => {
                format!("{:?}({}, {})", op, rm.to_itrace_string(symtab), value.to_itrace_string(symtab))
            }
            FPBinary(op, lhs, rhs) => {
                format!("{:?}({}, {})", op, lhs.to_itrace_string(symtab), rhs.to_itrace_string(symtab))
            }
            FPRoundingBinary(op, rm, lhs, rhs) => format!(
                "{:?}({}, {}, {})",
                op,
                rm.to_itrace_string(symtab),
                lhs.to_itrace_string(symtab),
                rhs.to_itrace_string(symtab)
            ),
            FPfma(rm, x, y, z) => format!(
                "fpfma({}, {}, {}, {})",
                rm.to_itrace_string(symtab),
                x.to_itrace_string(symtab),
                y.to_itrace_string(symtab),
                z.to_itrace_string(symtab)
            ),
            Bvand(lhs, rhs)
            | Bvor(lhs, rhs)
            | Bvxor(lhs, rhs)
            | Bvnand(lhs, rhs)
            | Bvnor(lhs, rhs)
            | Bvxnor(lhs, rhs)
            | Bvadd(lhs, rhs)
            | Bvsub(lhs, rhs)
            | Bvmul(lhs, rhs)
            | Bvudiv(lhs, rhs)
            | Bvsdiv(lhs, rhs)
            | Bvurem(lhs, rhs)
            | Bvsrem(lhs, rhs)
            | Bvsmod(lhs, rhs)
            | Bvult(lhs, rhs)
            | Bvslt(lhs, rhs)
            | Bvule(lhs, rhs)
            | Bvsle(lhs, rhs)
            | Bvuge(lhs, rhs)
            | Bvsge(lhs, rhs)
            | Bvugt(lhs, rhs)
            | Bvsgt(lhs, rhs)
            | Bvshl(lhs, rhs)
            | Bvlshr(lhs, rhs)
            | Bvashr(lhs, rhs)
            | Concat(lhs, rhs)
            | Select(lhs, rhs) => format!(
                "{}({}, {})",
                match self {
                    Bvand(_, _) => "bvand",
                    Bvor(_, _) => "bvor",
                    Bvxor(_, _) => "bvxor",
                    Bvnand(_, _) => "bvnand",
                    Bvnor(_, _) => "bvnor",
                    Bvxnor(_, _) => "bvxnor",
                    Bvadd(_, _) => "bvadd",
                    Bvsub(_, _) => "bvsub",
                    Bvmul(_, _) => "bvmul",
                    Bvudiv(_, _) => "bvudiv",
                    Bvsdiv(_, _) => "bvsdiv",
                    Bvurem(_, _) => "bvurem",
                    Bvsrem(_, _) => "bvsrem",
                    Bvsmod(_, _) => "bvsmod",
                    Bvult(_, _) => "bvult",
                    Bvslt(_, _) => "bvslt",
                    Bvule(_, _) => "bvule",
                    Bvsle(_, _) => "bvsle",
                    Bvuge(_, _) => "bvuge",
                    Bvsge(_, _) => "bvsge",
                    Bvugt(_, _) => "bvugt",
                    Bvsgt(_, _) => "bvsgt",
                    Bvshl(_, _) => "bvshl",
                    Bvlshr(_, _) => "bvlshr",
                    Bvashr(_, _) => "bvashr",
                    Concat(_, _) => "concat",
                    Select(_, _) => "select",
                    _ => unreachable!(),
                },
                lhs.to_itrace_string(symtab),
                rhs.to_itrace_string(symtab)
            ),
            Store(array, index, value) => format!(
                "store({}, {}, {})",
                array.to_itrace_string(symtab),
                index.to_itrace_string(symtab),
                value.to_itrace_string(symtab)
            ),
        }
    }
}

fn clear_output_file(output_path: &Option<PathBuf>) {
    let Some(path) = output_path else {
        return;
    };
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent)
                .unwrap_or_else(|error| panic!("itrace: 无法创建输出目录 {}: {}", parent.display(), error));
        }
    }
    File::create(path).unwrap_or_else(|error| panic!("itrace: 无法创建/清空输出文件 {}: {}", path.display(), error));
}

// ============ ItraceWriter ============
// Writer 独立管理输出路径、完成队列和后台写线程。ItraceHandler 只需要把
// 已完成的 itrace path 交给 writer，不再暴露 String 队列和线程细节。

struct ItraceWriter {
    output_path: Mutex<Option<PathBuf>>,
    completed_queue: Arc<SegQueue<String>>,
    shutdown: Arc<AtomicBool>,
    write_thread: Mutex<Option<JoinHandle<()>>>,
}

impl Default for ItraceWriter {
    fn default() -> Self {
        Self {
            output_path: Mutex::new(None),
            completed_queue: Arc::new(SegQueue::new()),
            shutdown: Arc::new(AtomicBool::new(false)),
            write_thread: Mutex::new(None),
        }
    }
}

impl ItraceWriter {
    fn start_write_thread(&self) {
        let output_path = self.output_path.lock().expect("itrace mutex poisoned").clone();
        let path = match output_path {
            Some(p) => p,
            None => return,
        };

        let mut thread_handle = self.write_thread.lock().expect("itrace mutex poisoned");
        if thread_handle.is_some() {
            return;
        }

        self.shutdown.store(false, Ordering::Release);

        if let Some(parent) = path.parent() {
            if !parent.as_os_str().is_empty() {
                std::fs::create_dir_all(parent)
                    .unwrap_or_else(|error| panic!("itrace: 无法创建输出目录 {}: {}", parent.display(), error));
            }
        }

        let queue = Arc::clone(&self.completed_queue);
        let shutdown = Arc::clone(&self.shutdown);
        let path_for_error = path.clone();

        let handle = thread::Builder::new()
            .name("itrace-writer".into())
            .spawn(move || {
                let mut file = OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(&path)
                    .unwrap_or_else(|error| panic!("itrace: 无法打开输出文件 {}: {}", path.display(), error));

                loop {
                    match queue.pop() {
                        Some(text) => {
                            writeln!(file, "{}", text).unwrap_or_else(|write_error| {
                                panic!("itrace: 写入输出文件 {} 失败: {}", path.display(), write_error)
                            });
                        }
                        None => {
                            if shutdown.load(Ordering::Acquire) {
                                break;
                            }
                            thread::yield_now();
                        }
                    }
                }

                // Drain remaining items after shutdown signal
                while let Some(text) = queue.pop() {
                    writeln!(file, "{}", text).unwrap_or_else(|write_error| {
                        panic!("itrace: 写入输出文件 {} 失败: {}", path.display(), write_error)
                    });
                }
                file.flush().unwrap_or_else(|flush_error| {
                    panic!("itrace: 刷新输出文件 {} 失败: {}", path.display(), flush_error)
                });
            })
            .unwrap_or_else(|spawn_error| {
                panic!("itrace: 无法启动写入线程 (输出路径 {}): {}", path_for_error.display(), spawn_error)
            });

        *thread_handle = Some(handle);
    }

    fn stop_write_thread(&self) {
        self.shutdown.store(true, Ordering::Release);
        if let Ok(mut thread_handle) = self.write_thread.lock() {
            if let Some(handle) = thread_handle.take() {
                match handle.join() {
                    Ok(()) => {}
                    Err(panic_payload) => {
                        let message = panic_payload
                            .downcast_ref::<String>()
                            .map(String::as_str)
                            .or_else(|| panic_payload.downcast_ref::<&str>().copied())
                            .unwrap_or("未知写入线程 panic");
                        panic!("itrace: 写入线程异常退出: {}", message);
                    }
                }
            }
        }
    }

    fn set_path(&self, output_path: Option<PathBuf>) {
        let current_path = self.output_path.lock().expect("itrace mutex poisoned").clone();
        if current_path != output_path {
            self.stop_write_thread();
        }

        *self.output_path.lock().expect("itrace mutex poisoned") = output_path.clone();
        let needs_spawn = {
            let thread_handle = self.write_thread.lock().expect("itrace mutex poisoned");
            thread_handle.is_none() && output_path.is_some()
        };
        if needs_spawn {
            self.start_write_thread();
        }
    }

    fn configure_path(&self, output_path: Option<PathBuf>) {
        self.stop_write_thread();
        clear_output_file(&output_path);
        self.set_path(output_path);
    }

    fn with_output_path(output_path: Option<PathBuf>) -> Self {
        let writer = Self::default();
        writer.configure_path(output_path);
        writer
    }

    fn submit_text(&self, text: String) {
        self.completed_queue.push(text);
    }

    fn dump(&self) {
        self.stop_write_thread();
    }

    #[cfg(test)]
    fn has_write_thread(&self) -> bool {
        self.write_thread.lock().expect("itrace mutex poisoned").is_some()
    }

    fn output_path(&self) -> Option<PathBuf> {
        self.output_path.lock().expect("itrace mutex poisoned").clone()
    }
}

impl Drop for ItraceWriter {
    fn drop(&mut self) {
        self.dump();
    }
}

// ============ ItraceHandler ============
// 一个 ItraceHandler 对应一次完整的符号执行入口、一个 itrace 输出文件和一个大标题。
// 在多 clause / --all 场景下，每个 clause 应拥有独立的 handler 生命周期，
// 以保证各 clause 的 itrace 输出互不干扰（独立文件、独立标题）。
// Handler 管理 itrace 的语义上下文，Writer 管理写入生命周期。

pub struct ItraceHandler {
    title: Mutex<String>,
    ir_cache: Mutex<IrFileCache>,
    writer: ItraceWriter,
}

impl Default for ItraceHandler {
    fn default() -> Self {
        Self {
            title: Mutex::new(String::new()),
            ir_cache: Mutex::new(IrFileCache::default()),
            writer: ItraceWriter::default(),
        }
    }
}

impl ItraceHandler {
    /// Full initialization: read .ir file to build cache, set output path, spawn write thread
    pub fn init(title: &str, ir_file_path: PathBuf, output_path: Option<PathBuf>, symtab: &Symtab) -> Self {
        let ir_cache = IrFileCache::from_file(&ir_file_path, symtab);
        Self {
            title: Mutex::new(title.to_string()),
            ir_cache: Mutex::new(ir_cache),
            writer: ItraceWriter::with_output_path(output_path),
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

        self.writer.configure_path(output_path);
    }

    /// Set output path — compatible with &self call sites (interior mutability via Mutex)
    pub fn set_path(&self, output_path: Option<PathBuf>) {
        self.writer.set_path(output_path);
    }

    fn title(&self) -> String {
        self.title.lock().map(|title| title.clone()).unwrap_or_default()
    }

    fn lookup_ir_line(&self, function_name: Name, pc: u64, symtab: &Symtab) -> Option<String> {
        let _ = symtab;
        let Ok(cache) = self.ir_cache.lock() else {
            return None;
        };
        cache.lookup_line(function_name, pc)
    }

    /// Signal shutdown and join the write thread (flushes remaining data)
    pub fn dump(&self) {
        self.writer.dump();
    }
}

impl Drop for ItraceHandler {
    fn drop(&mut self) {
        self.dump();
    }
}

/*
 * Post-processing and presentation
 *
 * 后处理路径负责 IR cache 查找、source location 清洗和标题格式化，优先保证输出整洁可读。
 */

impl ItracePerPath {
    fn render_title(&self, title: &str, symtab: &Symtab) -> String {
        if self.branch_conditions.is_empty() {
            format!("<{}> path({}):", title, title)
        } else {
            let branches = self
                .branch_conditions
                .iter()
                .map(|condition| condition.to_itrace_string(symtab))
                .collect::<Vec<_>>()
                .join("_");
            format!("<{}> path({}_branch_{}):", title, title, branches)
        }
    }

    fn render_text(&self, handler: &ItraceHandler, symtab: &Symtab) -> Option<String> {
        handler.writer.output_path()?;

        let mut lines = Vec::new();
        lines.push(self.render_title(&handler.title(), symtab));

        for record in self.records() {
            let ir_line = handler.lookup_ir_line(record.function_name, record.pc, symtab).unwrap_or_else(|| {
                let fallback = format!("{}:{} not found", symtab.to_str(record.function_name), record.pc);
                eprintln!(
                    "warning: {}, downgrade to fallback itrace text; this path can still be written, but the original IR line is unavailable",
                    fallback
                );
                fallback
            });
            lines.push(format!("[{} {}]: {}", symtab.to_str(record.function_name), record.pc, ir_line));
        }

        lines.push(String::new());
        lines.push("====".to_string());
        Some(lines.join("\n"))
    }
}

impl ItraceHandler {
    /// Submit a finished itrace path; rendering and string queueing stay internal to itrace.
    pub fn submit_path(&self, path: &ItracePerPath, symtab: &Symtab) {
        if let Some(text) = path.render_text(self, symtab) {
            self.writer.submit_text(text);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::{ir, ir_lexer, ir_parser};
    use std::collections::HashSet;
    use std::panic::{self, AssertUnwindSafe};

    fn parse_shared_state() -> crate::ir::SharedState<'static, B64> {
        const IR_FIXTURE: &str = include_str!("../../tests/fixtures/ir_cache_assumption.ir");
        let mut symtab = Symtab::new();
        let defs: Vec<ir::Def<Name, B64>> = ir_parser::IrParser::new()
            .parse(&mut symtab, ir_lexer::new_ir_lexer(IR_FIXTURE))
            .expect("parse fixture failed");
        let defs: &'static [ir::Def<Name, B64>] = Box::leak(defs.into_boxed_slice());
        let type_info = crate::ir::IRTypeInfo::new(defs);

        crate::ir::SharedState::new(
            symtab,
            defs,
            type_info,
            HashSet::new(),
            HashSet::new(),
            HashSet::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
    }

    fn fixture_ir_path() -> PathBuf {
        let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
        PathBuf::from(manifest_dir).join("tests/fixtures/ir_cache_assumption.ir")
    }

    fn write_temp_ir_file(name: &str, content: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!("{}_{}.ir", name, std::process::id()));
        std::fs::write(&path, content).expect("write temporary IR file");
        path
    }

    #[test]
    fn itrace_per_path_record_stores_instruction_context_without_summary() {
        let mut path = ItracePerPath::default();
        let function_name = Name::from_u32(7);
        let backtrace = vec![(Name::from_u32(1), 11), (Name::from_u32(2), 22)];

        path.record(function_name, backtrace.clone(), 42);

        let records = path.records();
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].function_name, function_name);
        assert_eq!(records[0].backtrace, backtrace);
        assert_eq!(records[0].pc, 42);
        assert!(records[0].summary.is_none());
    }

    #[test]
    fn ir_file_cache_from_file_builds_lookup_table_from_fixture() {
        let shared_state = parse_shared_state();
        let cache = IrFileCache::from_file(&fixture_ir_path(), &shared_state.symtab);
        let zcache_ok = shared_state.symtab.lookup("zcache_ok");
        let zpc_lookup = shared_state.symtab.lookup("zpc_lookup");

        assert_eq!(cache.lookup_line(zcache_ok, 0), Some("z0 : %i;".to_string()));
        assert_eq!(cache.lookup_line(zcache_ok, 3), Some("return = z1;".to_string()));
        assert_eq!(cache.lookup_line(zpc_lookup, 1), Some("p1 : %i;".to_string()));
        assert_eq!(cache.lookup_line(zpc_lookup, 5), Some("end;".to_string()));
    }

    #[test]
    fn ir_file_cache_from_file_returns_none_for_unknown_function_and_out_of_range_pc() {
        let shared_state = parse_shared_state();
        let cache = IrFileCache::from_file(&fixture_ir_path(), &shared_state.symtab);
        let zcache_ok = shared_state.symtab.lookup("zcache_ok");
        let unknown = Name::from_u32(u32::MAX);

        assert!(cache.lookup_line(unknown, 0).is_none());
        assert!(cache.lookup_line(zcache_ok, 100).is_none());
        assert!(cache.lookup_line(zcache_ok, u64::MAX).is_none());
    }

    #[test]
    fn ir_file_cache_from_file_strips_source_locations_and_keeps_function_boundaries() {
        let mut symtab = Symtab::new();
        let zfirst = symtab.intern("zfirst");
        let zsecond = symtab.intern("zsecond");
        let ir_path = write_temp_ir_file(
            "itrace_cache_boundaries",
            r#"
fn zfirst() {
  z0 : %i `14 248:2-248:53;
  z1 : %i `15;
}

fn zsecond() {
  p0 : %i `16 12:1-12:9;
}
"#,
        );

        let cache = IrFileCache::from_file(&ir_path, &symtab);

        assert_eq!(cache.lookup_line(zfirst, 0), Some("z0 : %i;".to_string()));
        assert_eq!(cache.lookup_line(zfirst, 1), Some("z1 : %i;".to_string()));
        assert!(cache.lookup_line(zfirst, 2).is_none(), "first function should not include second function lines");
        assert_eq!(cache.lookup_line(zsecond, 0), Some("p0 : %i;".to_string()));

        let _ = std::fs::remove_file(&ir_path);
    }

    #[test]
    fn ir_file_cache_from_file_ignores_non_function_blocks() {
        let mut symtab = Symtab::new();
        let zfirst = symtab.intern("zfirst");
        let zsecond = symtab.intern("zsecond");
        let zstruct_like = symtab.intern("zstruct_like");
        let zunion_like = symtab.intern("zunion_like");
        let ir_path = write_temp_ir_file(
            "itrace_cache_non_function_blocks",
            r#"
struct zstruct_like {
  field : %i;
}

fn zfirst() {
  f0 : %i `1;
}

union zunion_like {
  member : %i;
}

fn zsecond() {
  s0 : %i `2;
}
"#,
        );

        let cache = IrFileCache::from_file(&ir_path, &symtab);

        assert_eq!(cache.lookup_line(zfirst, 0), Some("f0 : %i;".to_string()));
        assert_eq!(cache.lookup_line(zsecond, 0), Some("s0 : %i;".to_string()));
        assert!(cache.lookup_line(zstruct_like, 0).is_none());
        assert!(cache.lookup_line(zunion_like, 0).is_none());

        let _ = std::fs::remove_file(&ir_path);
    }

    #[test]
    fn ir_file_cache_from_file_skips_functions_missing_from_symtab() {
        let mut symtab = Symtab::new();
        let zknown = symtab.intern("zknown");
        let ir_path = write_temp_ir_file(
            "itrace_cache_missing_symtab",
            r#"
fn zknown() {
  k0 : %i `1;
}

fn zmissing() {
  m0 : %i `2;
}
"#,
        );

        let cache = IrFileCache::from_file(&ir_path, &symtab);
        let zmissing = symtab.intern("zmissing");

        assert_eq!(cache.lookup_line(zknown, 0), Some("k0 : %i;".to_string()));
        assert!(cache.lookup_line(zmissing, 0).is_none());

        let _ = std::fs::remove_file(&ir_path);
    }

    #[test]
    fn ir_file_cache_from_file_panics_with_path_when_file_is_missing() {
        let symtab = Symtab::new();
        let ir_path = std::env::temp_dir().join(format!("itrace_missing_cache_{}.ir", std::process::id()));
        let _ = std::fs::remove_file(&ir_path);

        let panic_result = panic::catch_unwind(AssertUnwindSafe(|| {
            let cache = IrFileCache::from_file(&ir_path, &symtab);
            let _ = cache.functions.len();
        }));

        let payload = panic_result.expect_err("missing IR file should panic");
        let message = payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .expect("panic payload should be a string");

        assert!(message.contains("IR file should be openable after successful IR parse"));
        assert!(message.contains(&ir_path.display().to_string()));
    }

    #[test]
    fn itrace_branch_title_formats_readable_conditions() {
        let mut symtab = Symtab::new();
        symtab.intern("zbranch_flag");
        let mut path = ItracePerPath::default();
        path.push_branch_condition(smtlib::Exp::<Sym>::Var(Sym::from_u32(25)));
        path.push_branch_condition(smtlib::Exp::<Sym>::Not(Box::new(smtlib::Exp::<Sym>::Bool(false))));

        let title = path.render_title("handler title", &symtab);

        assert_eq!(title, "<handler title> path(handler title_branch_zbranch_flag_!false):");
        assert!(!title.contains("branch_conditions"));
        assert!(!title.contains("Bool"));
    }

    #[test]
    fn itrace_per_path_render_text_uses_lookup_and_fallback() {
        let shared_state = parse_shared_state();
        let temp_dir = std::env::temp_dir();
        let output_path = temp_dir.join(format!("itrace_render_fallback_{}.txt", std::process::id()));
        let _ = std::fs::remove_file(&output_path);
        let handler = ItraceHandler::init(
            "itrace test title",
            fixture_ir_path(),
            Some(output_path.clone()),
            &shared_state.symtab,
        );
        let mut path = ItracePerPath::default();
        let known_fn = shared_state.symtab.lookup("zcache_ok");

        path.record(known_fn, Vec::new(), 0);
        path.record(known_fn, Vec::new(), 99);
        path.push_branch_condition(smtlib::Exp::<Sym>::Bool(false));

        let text = path.render_text(&handler, &shared_state.symtab).expect("render itrace text");

        assert!(text.contains("<itrace test title> path(itrace test title_branch_false):"));
        assert!(!text.contains("branch_conditions"));
        assert!(!text.contains("Bool"));
        assert!(text.contains("[zcache_ok 0]: z0 : %i;"));
        assert!(text.contains("[zcache_ok 99]: zcache_ok:99 not found"));
        assert!(text.ends_with("\n\n===="));

        drop(handler);
        let _ = std::fs::remove_file(&output_path);
    }

    #[test]
    fn itrace_per_path_render_text_matches_reference_itrace_shape() {
        let shared_state = parse_shared_state();
        let temp_dir = std::env::temp_dir();
        let output_path = temp_dir.join(format!("itrace_render_shape_{}.txt", std::process::id()));
        let _ = std::fs::remove_file(&output_path);
        let handler = ItraceHandler::init("zRTYPE", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);
        let mut path = ItracePerPath::default();
        let zcache_ok = shared_state.symtab.lookup("zcache_ok");

        path.record(zcache_ok, Vec::new(), 0);
        path.record(zcache_ok, Vec::new(), 1);

        let text = path.render_text(&handler, &shared_state.symtab).expect("render itrace text");
        let expected = "\
<zRTYPE> path(zRTYPE):
[zcache_ok 0]: z0 : %i;
[zcache_ok 1]: z1 : %i;

====";

        assert_eq!(text, expected);

        drop(handler);
        let _ = std::fs::remove_file(&output_path);
    }

    #[test]
    fn itrace_handler_writes_rendered_path_text() {
        let temp_dir = std::env::temp_dir();
        let output_path = temp_dir.join("itrace_submit_itrace_module_test.txt");
        let _ = std::fs::remove_file(&output_path);
        let shared_state = parse_shared_state();
        let handler = ItraceHandler::init(
            "itrace test title",
            fixture_ir_path(),
            Some(output_path.clone()),
            &shared_state.symtab,
        );
        let mut path = ItracePerPath::default();

        path.record(shared_state.symtab.lookup("zcache_ok"), Vec::new(), 3);
        handler.submit_path(&path, &shared_state.symtab);
        handler.dump();

        let content = std::fs::read_to_string(&output_path).expect("read itrace submit output");
        assert!(content.contains("<itrace test title> path(itrace test title):"));
        assert!(content.contains("[zcache_ok 3]: return = z1;"));

        let _ = std::fs::remove_file(&output_path);
    }

    #[test]
    fn itrace_handler_submits_itrace_path_without_exposing_rendered_text() {
        let temp_dir = std::env::temp_dir();
        let output_path = temp_dir.join(format!("itrace_submit_path_api_{}.txt", std::process::id()));
        let _ = std::fs::remove_file(&output_path);
        let shared_state = parse_shared_state();
        let handler = ItraceHandler::init(
            "itrace test title",
            fixture_ir_path(),
            Some(output_path.clone()),
            &shared_state.symtab,
        );
        let mut path = ItracePerPath::default();

        path.record(shared_state.symtab.lookup("zcache_ok"), Vec::new(), 3);
        handler.submit_path(&path, &shared_state.symtab);
        handler.dump();

        let content = std::fs::read_to_string(&output_path).expect("read itrace submit output");
        assert!(content.contains("<itrace test title> path(itrace test title):"));
        assert!(content.contains("[zcache_ok 3]: return = z1;"));

        let _ = std::fs::remove_file(&output_path);
    }

    #[test]
    fn itrace_handler_submits_multiple_rendered_paths() {
        let temp_dir = std::env::temp_dir();
        let output_path = temp_dir.join(format!("itrace_integration_itrace_module_test_{}.txt", std::process::id()));
        let _ = std::fs::remove_file(&output_path);
        let shared_state = parse_shared_state();
        let handler = ItraceHandler::init(
            "itrace test title",
            fixture_ir_path(),
            Some(output_path.clone()),
            &shared_state.symtab,
        );
        let zcache_ok = shared_state.symtab.lookup("zcache_ok");
        let zpc_lookup = shared_state.symtab.lookup("zpc_lookup");

        let mut first_path = ItracePerPath::default();
        first_path.push_branch_condition(smtlib::Exp::<Sym>::Bool(true));
        first_path.record(zcache_ok, Vec::new(), 0);
        first_path.record(zcache_ok, Vec::new(), 3);

        let mut second_path = ItracePerPath::default();
        second_path.push_branch_condition(smtlib::Exp::<Sym>::Bool(false));
        second_path.record(zpc_lookup, Vec::new(), 1);
        second_path.record(zpc_lookup, Vec::new(), 5);

        handler.submit_path(&first_path, &shared_state.symtab);
        handler.submit_path(&second_path, &shared_state.symtab);
        handler.dump();

        let content = std::fs::read_to_string(&output_path).expect("read itrace integration output");

        assert_eq!(content.matches("<itrace test title> path").count(), 2);
        assert!(content.contains("<itrace test title> path(itrace test title_branch_true):"));
        assert!(content.contains("<itrace test title> path(itrace test title_branch_false):"));
        assert!(!content.contains("branch_conditions"));
        assert!(!content.contains("Bool"));
        assert!(content.contains("[zcache_ok 0]: z0 : %i;"));
        assert!(content.contains("[zcache_ok 3]: return = z1;"));
        assert!(content.contains("[zpc_lookup 1]: p1 : %i;"));
        assert!(content.contains("end"));
        assert!(!content.contains("`1"));
        assert!(!content.contains("`4"));
        assert!(!content.contains("`11"));

        let title_prefix = "<itrace test title> path";
        let first_title = content.find(title_prefix).expect("first path title missing");
        let second_title = content[first_title + 1..]
            .find(title_prefix)
            .map(|offset| first_title + 1 + offset)
            .expect("second path title missing");
        assert!(content[first_title..second_title].contains("[zcache_ok 0]: z0 : %i;"));
        assert!(content[first_title..second_title].contains("[zcache_ok 3]: return = z1;"));
        assert!(content[second_title..].contains("[zpc_lookup 1]: p1 : %i;"));
        assert!(content[second_title..].contains("end"));

        let _ = std::fs::remove_file(&output_path);
    }

    #[test]
    fn strip_source_loc_standard() {
        assert_eq!(strip_source_loc("[zfunc 0]: zz40 : %bv `14 248:2-248:53;"), "[zfunc 0]: zz40 : %bv;");
    }

    #[test]
    fn is_source_loc_accepts_supported_suffix_forms() {
        assert!(is_source_loc("14"));
        assert!(is_source_loc("14 248:2-248:53"));
        assert!(is_source_loc("0 1:0-1:0"));
    }

    #[test]
    fn is_source_loc_rejects_empty_or_non_numeric_suffixes() {
        assert!(!is_source_loc(""));
        assert!(!is_source_loc("abc"));
        assert!(!is_source_loc("14 abc:2-248:53"));
        assert!(!is_source_loc("file 248:2-248:53"));
        assert!(!is_source_loc("14 248:x-248:53"));
        assert!(!is_source_loc("14 248:2-248:y"));
    }

    #[test]
    fn is_source_loc_rejects_malformed_ranges() {
        assert!(!is_source_loc("14 248"));
        assert!(!is_source_loc("14 248:2"));
        assert!(!is_source_loc("14 248:2-248"));
        assert!(!is_source_loc("14 248:2:3-248:53"));
        assert!(!is_source_loc("14 248:2-248:53:1"));
        assert!(!is_source_loc("14 248:2-248:53 extra"));
    }

    #[test]
    fn strip_source_loc_with_trailing_whitespace() {
        assert_eq!(strip_source_loc("[zfunc 0]: zz40 : %bv `14 248:2-248:53;   \t"), "[zfunc 0]: zz40 : %bv;");
    }

    #[test]
    fn strip_source_loc_short() {
        assert_eq!(strip_source_loc("[zfunc 1]: zz41 : %i `14"), "[zfunc 1]: zz41 : %i;");
        assert_eq!(strip_source_loc("[zfunc 2]: zz41 : %i `14;"), "[zfunc 2]: zz41 : %i;");
    }

    #[test]
    fn strip_source_loc_range_without_semicolon() {
        assert_eq!(strip_source_loc("[zfunc 3]: zz42 : %i `14 248:2-248:53"), "[zfunc 3]: zz42 : %i;");
    }

    #[test]
    fn strip_source_loc_uses_last_backtick() {
        assert_eq!(
            strip_source_loc("[zfunc 4]: call `not_a_loc arg `14 248:2-248:53;"),
            "[zfunc 4]: call `not_a_loc arg;"
        );
    }

    #[test]
    fn strip_source_loc_preserves_invalid_backtick_suffixes() {
        assert_eq!(strip_source_loc("[zfunc 5]: zz43 : %i `abc;"), "[zfunc 5]: zz43 : %i `abc;");
        assert_eq!(
            strip_source_loc("[zfunc 6]: zz43 : %i `14 abc:2-248:53;"),
            "[zfunc 6]: zz43 : %i `14 abc:2-248:53;"
        );
        assert_eq!(strip_source_loc("[zfunc 7]: zz43 : %i `14 248:2;"), "[zfunc 7]: zz43 : %i `14 248:2;");
    }

    #[test]
    fn strip_no_sourceloc() {
        assert_eq!(strip_source_loc("goto 5"), "goto 5");
        assert_eq!(strip_source_loc("  goto 5  "), "  goto 5  ");
    }

    // ---- Task 4: ItraceHandler tests ----

    #[test]
    fn itrace_handler_init_builds_ir_cache() {
        let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
        let ir_path = PathBuf::from(manifest_dir).join("tests/fixtures/ir_cache_assumption.ir");
        assert!(ir_path.exists(), "Test fixture not found at {:?}", ir_path);

        let temp_dir = std::env::temp_dir();
        let output_path = temp_dir.join("itrace_test_init.txt");
        let _ = std::fs::remove_file(&output_path);

        let shared_state = parse_shared_state();
        let handler = ItraceHandler::init("test", ir_path, Some(output_path.clone()), &shared_state.symtab);

        assert_eq!(
            handler.lookup_ir_line(shared_state.symtab.lookup("zcache_ok"), 0, &shared_state.symtab),
            Some("z0 : %i;".to_string()),
            "Should resolve zcache_ok through the handler API"
        );
        assert_eq!(
            handler.lookup_ir_line(shared_state.symtab.lookup("zpc_lookup"), 1, &shared_state.symtab),
            Some("p1 : %i;".to_string()),
            "Should resolve zpc_lookup through the handler API"
        );
        assert!(
            !handler
                .lookup_ir_line(shared_state.symtab.lookup("zcache_ok"), 0, &shared_state.symtab)
                .expect("zcache_ok line")
                .contains('`'),
            "Line should not contain SourceLoc"
        );

        drop(handler);
        let _ = std::fs::remove_file(&output_path);
    }

    #[test]
    fn itrace_handler_default_no_thread() {
        let handler = ItraceHandler::default();
        assert!(!handler.writer.has_write_thread());
        assert!(handler.writer.output_path().is_none());
    }

    #[test]
    fn itrace_handler_submit_path_without_output_path_does_not_render_or_queue() {
        let shared_state = parse_shared_state();
        let handler = ItraceHandler::default();
        let mut path = ItracePerPath::default();

        path.record(shared_state.symtab.lookup("zcache_ok"), Vec::new(), 0);
        handler.submit_path(&path, &shared_state.symtab);

        assert!(
            handler.writer.completed_queue.pop().is_none(),
            "submit_path should skip rendering when no output path is configured"
        );
    }

    #[test]
    fn itrace_write_thread_writes_to_file() {
        let temp_dir = std::env::temp_dir();
        let output_path = temp_dir.join("itrace_test_write.txt");
        let _ = std::fs::remove_file(&output_path);

        let shared_state = parse_shared_state();
        let handler = ItraceHandler::init("test", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);

        handler.writer.submit_text("line1".to_string());
        handler.writer.submit_text("line2".to_string());
        handler.writer.submit_text("line3".to_string());

        handler.dump();

        let content = std::fs::read_to_string(&output_path).expect("read");
        assert!(content.contains("line1"), "Should contain line1");
        assert!(content.contains("line2"), "Should contain line2");
        assert!(content.contains("line3"), "Should contain line3");

        let _ = std::fs::remove_file(&output_path);
    }

    #[test]
    fn itrace_handler_graceful_shutdown() {
        let temp_dir = std::env::temp_dir();
        let output_path = temp_dir.join("itrace_test_shutdown.txt");
        let _ = std::fs::remove_file(&output_path);

        let shared_state = parse_shared_state();
        let handler = ItraceHandler::init("test", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);

        handler.writer.submit_text("data_before_drop".to_string());

        // Drop should trigger dump internally — no panic, no hang
        drop(handler);

        let content = std::fs::read_to_string(&output_path).expect("read");
        assert!(content.contains("data_before_drop"), "Should contain submitted data after drop");

        let _ = std::fs::remove_file(&output_path);
    }

    #[test]
    fn itrace_set_path_spawns_thread() {
        let temp_dir = std::env::temp_dir();
        let output_path = temp_dir.join("itrace_test_setpath.txt");
        let _ = std::fs::remove_file(&output_path);

        let handler = ItraceHandler::default();
        assert!(!handler.writer.has_write_thread());

        handler.set_path(Some(output_path.clone()));
        assert!(handler.writer.has_write_thread(), "Thread should be spawned after set_path");

        handler.writer.submit_text("via_set_path".to_string());
        handler.dump();

        let content = std::fs::read_to_string(&output_path).expect("read");
        assert!(content.contains("via_set_path"), "Should contain submitted data");

        let _ = std::fs::remove_file(&output_path);
    }

    #[test]
    fn itrace_set_path_after_dump_writes_new_path_only() {
        let temp_dir = std::env::temp_dir();
        let first_path = temp_dir.join(format!("itrace_reconfigure_set_path_first_{}.txt", std::process::id()));
        let second_path = temp_dir.join(format!("itrace_reconfigure_set_path_second_{}.txt", std::process::id()));
        let _ = std::fs::remove_file(&first_path);
        let _ = std::fs::remove_file(&second_path);

        let handler = ItraceHandler::default();
        handler.set_path(Some(first_path.clone()));
        handler.writer.submit_text("first-path-line".to_string());
        handler.dump();

        handler.set_path(Some(second_path.clone()));
        std::thread::sleep(std::time::Duration::from_millis(20));
        handler.writer.submit_text("second-path-line".to_string());
        handler.dump();

        let first_content = std::fs::read_to_string(&first_path).expect("read first itrace output");
        let second_content = std::fs::read_to_string(&second_path).expect("read second itrace output");
        assert!(first_content.contains("first-path-line"));
        assert!(!first_content.contains("second-path-line"), "second path data leaked into first file");
        assert!(second_content.contains("second-path-line"));
        assert!(!second_content.contains("first-path-line"), "first path data leaked into second file");

        let _ = std::fs::remove_file(&first_path);
        let _ = std::fs::remove_file(&second_path);
    }

    #[test]
    fn itrace_configure_after_dump_rebuilds_writer_and_cache_for_new_path() {
        let temp_dir = std::env::temp_dir();
        let first_path = temp_dir.join(format!("itrace_reconfigure_first_{}.txt", std::process::id()));
        let second_path = temp_dir.join(format!("itrace_reconfigure_second_{}.txt", std::process::id()));
        let _ = std::fs::remove_file(&first_path);
        let _ = std::fs::remove_file(&second_path);

        let shared_state = parse_shared_state();
        let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
        let ir_path = PathBuf::from(manifest_dir).join("tests/fixtures/ir_cache_assumption.ir");

        let handler = ItraceHandler::default();
        handler.configure("first title", ir_path.clone(), Some(first_path.clone()), &shared_state.symtab);
        handler.writer.submit_text("first configured line".to_string());
        handler.dump();

        handler.configure("second title", ir_path, Some(second_path.clone()), &shared_state.symtab);
        std::thread::sleep(std::time::Duration::from_millis(20));
        let zcache_ok = shared_state.symtab.lookup("zcache_ok");
        let ir_line = handler
            .lookup_ir_line(zcache_ok, 0, &shared_state.symtab)
            .expect("configured cache should resolve fixture line");
        handler.writer.submit_text(format!("{}\n{}", handler.title(), ir_line));
        handler.dump();

        let first_content = std::fs::read_to_string(&first_path).expect("read first configured itrace output");
        let second_content = std::fs::read_to_string(&second_path).expect("read second configured itrace output");
        assert!(first_content.contains("first configured line"));
        assert!(!first_content.contains("second title"), "second configure data leaked into first file");
        assert!(second_content.contains("second title"));
        assert!(second_content.contains("z0 : %i;"));
        assert!(!second_content.contains('`'));
        assert!(!second_content.contains("first configured line"), "first configure data leaked into second file");

        let _ = std::fs::remove_file(&first_path);
        let _ = std::fs::remove_file(&second_path);
    }

    #[test]
    fn itrace_handler_lookup_ir_line() {
        let shared_state = parse_shared_state();
        let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
        let ir_path = std::path::PathBuf::from(manifest_dir).join("tests/fixtures/ir_cache_assumption.ir");

        let handler = ItraceHandler::init("test", ir_path, None, &shared_state.symtab);

        let fn_name = shared_state.symtab.lookup("zcache_ok");
        assert_eq!(
            handler.lookup_ir_line(fn_name, 0, &shared_state.symtab),
            Some("z0 : %i;".to_string()),
            "Should return first IR line for zcache_ok"
        );
        assert_eq!(
            handler.lookup_ir_line(fn_name, 3, &shared_state.symtab),
            Some("return = z1;".to_string()),
            "Should return IR line for pc 3"
        );
    }

    #[test]
    fn itrace_handler_lookup_ir_line_fallbacks() {
        let shared_state = parse_shared_state();
        let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
        let ir_path = std::path::PathBuf::from(manifest_dir).join("tests/fixtures/ir_cache_assumption.ir");

        let handler = ItraceHandler::init("test", ir_path, None, &shared_state.symtab);

        let unknown_fn = Name::from_u32(u32::MAX);
        assert!(handler.lookup_ir_line(unknown_fn, 0, &shared_state.symtab).is_none());

        let known_fn = shared_state.symtab.lookup("zcache_ok");
        assert!(handler.lookup_ir_line(known_fn, 100, &shared_state.symtab).is_none());
        assert!(handler.lookup_ir_line(known_fn, u64::MAX, &shared_state.symtab).is_none());
    }

    #[test]
    fn itrace_handler_lookup_ir_line_poisoned_cache_lock() {
        let shared_state = parse_shared_state();
        let handler = ItraceHandler::default();

        let fn_name = shared_state.symtab.lookup("zcache_ok");

        let _ = panic::catch_unwind(AssertUnwindSafe(|| {
            let _guard = handler.ir_cache.lock().expect("mutex");
            panic!("poison cache lock");
        }));

        assert!(handler.lookup_ir_line(fn_name, 0, &shared_state.symtab).is_none());
    }

    // ---- IO panic 行为测试 ----

    #[test]
    fn itrace_handler_init_panics_when_output_path_is_unwritable() {
        let bad_path = PathBuf::from("/dev/null/impossible/itrace_output.txt");
        let shared_state = parse_shared_state();

        let result = panic::catch_unwind(AssertUnwindSafe(|| {
            let _handler =
                ItraceHandler::init("bad-path-test", fixture_ir_path(), Some(bad_path.clone()), &shared_state.symtab);
        }));

        let payload = result.expect_err("init with unwritable path should panic");
        let message = payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .expect("panic payload should be a string");

        assert!(message.contains("impossible"), "panic message should contain path fragment, got: {}", message);
    }

    #[test]
    fn itrace_handler_configure_panics_when_output_path_is_unwritable() {
        let temp_dir = std::env::temp_dir();
        let good_path = temp_dir.join(format!("itrace_configure_good_{}.txt", std::process::id()));
        let bad_path = PathBuf::from("/dev/null/impossible/itrace_output2.txt");
        let _ = std::fs::remove_file(&good_path);

        let shared_state = parse_shared_state();
        let handler = ItraceHandler::init("good", fixture_ir_path(), Some(good_path.clone()), &shared_state.symtab);
        handler.dump();

        let result = panic::catch_unwind(AssertUnwindSafe(|| {
            handler.configure("bad-path-configure", fixture_ir_path(), Some(bad_path.clone()), &shared_state.symtab);
        }));

        let payload = result.expect_err("configure with unwritable path should panic");
        let message = payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .expect("panic payload should be a string");

        assert!(message.contains("impossible"), "panic message should contain path fragment, got: {}", message);

        let _ = std::fs::remove_file(&good_path);
    }

    #[test]
    fn itrace_handler_set_path_panics_when_output_path_is_unwritable() {
        let bad_path = PathBuf::from("/dev/null/impossible/itrace_output3.txt");
        let handler = ItraceHandler::default();

        let result = panic::catch_unwind(AssertUnwindSafe(|| {
            handler.set_path(Some(bad_path.clone()));
        }));

        let payload = result.expect_err("set_path with unwritable path should panic");
        let message = payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .expect("panic payload should be a string");

        assert!(message.contains("impossible"), "panic message should contain path fragment, got: {}", message);
    }

    // ---- 多 handler 独立 title / 输出文件测试 ----

    #[test]
    fn itrace_separate_handlers_write_independent_titles_and_files() {
        // 模拟多 clause 场景：每个 clause 应该用独立的 handler，
        // 各自有独立的 title 和输出文件，互不干扰。
        let temp_dir = std::env::temp_dir();
        let output_a = temp_dir.join(format!("itrace_clause_a_{}.txt", std::process::id()));
        let output_b = temp_dir.join(format!("itrace_clause_b_{}.txt", std::process::id()));
        let _ = std::fs::remove_file(&output_a);
        let _ = std::fs::remove_file(&output_b);

        let shared_state = parse_shared_state();
        let zcache_ok = shared_state.symtab.lookup("zcache_ok");
        let zpc_lookup = shared_state.symtab.lookup("zpc_lookup");

        // clause A: 独立 handler，title 为 "clause_A"
        let handler_a =
            ItraceHandler::init("clause_A", fixture_ir_path(), Some(output_a.clone()), &shared_state.symtab);
        let mut path_a = ItracePerPath::default();
        path_a.record(zcache_ok, Vec::new(), 0);
        handler_a.submit_path(&path_a, &shared_state.symtab);
        handler_a.dump();

        // clause B: 独立 handler，title 为 "clause_B"
        let handler_b =
            ItraceHandler::init("clause_B", fixture_ir_path(), Some(output_b.clone()), &shared_state.symtab);
        let mut path_b = ItracePerPath::default();
        path_b.record(zpc_lookup, Vec::new(), 1);
        handler_b.submit_path(&path_b, &shared_state.symtab);
        handler_b.dump();

        let content_a = std::fs::read_to_string(&output_a).expect("read clause A output");
        let content_b = std::fs::read_to_string(&output_b).expect("read clause B output");

        // 各自文件只包含各自的 title
        assert!(content_a.contains("clause_A"), "clause A output should contain 'clause_A'");
        assert!(!content_a.contains("clause_B"), "clause A output should NOT contain 'clause_B'");
        assert!(content_b.contains("clause_B"), "clause B output should contain 'clause_B'");
        assert!(!content_b.contains("clause_A"), "clause B output should NOT contain 'clause_A'");

        // 各自文件只包含各自的 IR 行
        assert!(content_a.contains("[zcache_ok 0]: z0 : %i;"), "clause A output should contain zcache_ok line");
        assert!(content_b.contains("[zpc_lookup 1]: p1 : %i;"), "clause B output should contain zpc_lookup line");

        let _ = std::fs::remove_file(&output_a);
        let _ = std::fs::remove_file(&output_b);
    }

    #[test]
    fn itrace_handler_configure_resets_title_independently() {
        // 验证 configure 调用后 title 被独立更新，不会残留旧 title。
        let temp_dir = std::env::temp_dir();
        let first_path = temp_dir.join(format!("itrace_title_first_{}.txt", std::process::id()));
        let second_path = temp_dir.join(format!("itrace_title_second_{}.txt", std::process::id()));
        let _ = std::fs::remove_file(&first_path);
        let _ = std::fs::remove_file(&second_path);

        let shared_state = parse_shared_state();
        let handler = ItraceHandler::default();

        handler.configure("first_clause", fixture_ir_path(), Some(first_path.clone()), &shared_state.symtab);
        let mut path1 = ItracePerPath::default();
        path1.record(shared_state.symtab.lookup("zcache_ok"), Vec::new(), 0);
        handler.submit_path(&path1, &shared_state.symtab);
        handler.dump();

        handler.configure("second_clause", fixture_ir_path(), Some(second_path.clone()), &shared_state.symtab);
        let mut path2 = ItracePerPath::default();
        path2.record(shared_state.symtab.lookup("zpc_lookup"), Vec::new(), 1);
        handler.submit_path(&path2, &shared_state.symtab);
        handler.dump();

        let first_content = std::fs::read_to_string(&first_path).expect("read first title output");
        let second_content = std::fs::read_to_string(&second_path).expect("read second title output");

        assert!(first_content.contains("first_clause"));
        assert!(!first_content.contains("second_clause"), "second title should not leak into first file");
        assert!(second_content.contains("second_clause"));
        assert!(!second_content.contains("first_clause"), "first title should not leak into second file");

        let _ = std::fs::remove_file(&first_path);
        let _ = std::fs::remove_file(&second_path);
    }

    // ---- QA 复核：writer writeln panic / spawn panic / stop_write_thread 错误传播 ----

    #[test]
    fn itrace_handler_dump_propagates_writer_panic() {
        let temp_dir = std::env::temp_dir();
        let output_path = temp_dir.join(format!("itrace_writer_panic_{}.txt", std::process::id()));
        let _ = std::fs::remove_file(&output_path);

        let shared_state = parse_shared_state();
        let handler =
            ItraceHandler::init("panic-test", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);

        // 正常提交数据然后 dump，不应 panic
        handler.writer.submit_text("before-panic".to_string());
        handler.dump();

        let content = std::fs::read_to_string(&output_path).expect("read output");
        assert!(content.contains("before-panic"));

        let _ = std::fs::remove_file(&output_path);
    }

    #[test]
    fn itrace_handler_init_creates_file_at_exact_user_path() {
        let temp_dir = std::env::temp_dir();
        let exact_path = temp_dir.join(format!("itrace_exact_user_path_{}.txt", std::process::id()));
        let _ = std::fs::remove_file(&exact_path);

        let shared_state = parse_shared_state();
        let handler =
            ItraceHandler::init("single-clause", fixture_ir_path(), Some(exact_path.clone()), &shared_state.symtab);

        let mut path = ItracePerPath::default();
        path.record(shared_state.symtab.lookup("zcache_ok"), Vec::new(), 0);
        handler.submit_path(&path, &shared_state.symtab);
        handler.dump();

        assert!(exact_path.exists(), "file should be created at the exact user-specified path, no suffix added");
        let content = std::fs::read_to_string(&exact_path).expect("read");
        assert!(content.contains("single-clause"));
        assert!(content.contains("[zcache_ok 0]: z0 : %i;"));

        let _ = std::fs::remove_file(&exact_path);
    }
}
