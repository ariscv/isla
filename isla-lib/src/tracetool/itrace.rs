//! 逐指令记录、实际 IR 文本和既有源文件查询。
use super::{TraceHandler, TracePerPath};
use crate::bitvector::BV;
use crate::executor::Backtrace;
use crate::ir::{Instr, Name, Symtab};
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;
use std::sync::atomic::Ordering;

// itrace 的逐指令记录及其摘要；其他轨迹可以复用，但不改变数据归属。
#[derive(Clone)]
pub struct ItracePerInstr {
    pub function_name: Name,
    pub backtrace: Backtrace,
    pub pc: u64,
    pub summary: Option<String>,
    pub(super) instruction: Option<String>,
}

impl TracePerPath {
    pub fn record_summary(&mut self, function_name: Name, backtrace: Backtrace, pc: u64, summary: impl Into<String>) {
        self.itrace_records.push(ItracePerInstr {
            function_name,
            backtrace,
            pc,
            summary: Some(summary.into()),
            instruction: None,
        });
    }

    pub fn records(&self) -> impl ExactSizeIterator<Item = &ItracePerInstr> {
        self.itrace_records.iter()
    }

    pub fn record_count(&self) -> usize {
        self.itrace_records.len()
    }

    pub fn record(&mut self, function_name: Name, backtrace: Backtrace, pc: u64) {
        self.instruction_count += 1;
        self.executed_functions.insert(function_name);
        self.itrace_records.push(ItracePerInstr { function_name, backtrace, pc, summary: None, instruction: None });
    }
    pub fn record_instruction<B: BV>(
        &mut self,
        function_name: Name,
        backtrace: Backtrace,
        pc: u64,
        instruction: &Instr<Name, B>,
        handler: &TraceHandler,
    ) {
        self.instruction_count += 1;
        self.executed_functions.insert(function_name);
        if handler.instructions.load(Ordering::Acquire) {
            self.itrace_records.push(ItracePerInstr {
                function_name,
                backtrace,
                pc,
                summary: None,
                instruction: Some(format!("{:?}", instruction)),
            });
        }
    }
    pub(super) fn render_instructions(&self, handler: &TraceHandler, symtab: &Symtab, lines: &mut Vec<String>) {
        for record in self.records() {
            if let Some(summary) = &record.summary {
                lines.push(format!("[{} {}]: {}", symtab.to_str(record.function_name), record.pc, summary));
                continue;
            }
            if !handler.instructions.load(Ordering::Acquire) {
                continue;
            }
            let ir_line = record.instruction.clone().or_else(|| handler.lookup_ir_line(record.function_name, record.pc, symtab)).unwrap_or_else(|| {
                let fallback = format!("{}:{} not found", symtab.to_str(record.function_name), record.pc);
                eprintln!(
                    "warning: {}, downgrade to fallback itrace text; this path can still be written, but the original IR line is unavailable",
                    fallback
                );
                fallback
            });
            lines.push(format!("[{} {}]: {}", symtab.to_str(record.function_name), record.pc, ir_line));
        }
    }
}

impl TraceHandler {
    pub(super) fn lookup_ir_line(&self, function_name: Name, pc: u64, symtab: &Symtab) -> Option<String> {
        let _ = symtab;
        let Ok(cache) = self.ir_cache.lock() else {
            return None;
        };
        cache.lookup_line(function_name, pc)
    }
}

// 识别 `fn name(...) {` 形式的函数头，返回 z-encoded 函数名。
pub(super) fn try_parse_fn_header(line: &str) -> Option<String> {
    let rest = line.strip_prefix("fn ")?;
    let paren_pos = rest.find('(')?;
    let name = rest[..paren_pos].trim();
    Some(name.to_string())
}

// 用花括号深度判断当前函数体是否结束；IR fixture 中函数体按 `{}` 包围。
pub(super) fn count_braces(line: &str) -> i32 {
    line.chars().fold(0, |acc, ch| match ch {
        '{' => acc + 1,
        '}' => acc - 1,
        _ => acc,
    })
}

// 只接受 Isla IR 末尾 source location 的两种形态：纯数字 id，或 `file line:col-line:col`。
pub(super) fn is_source_loc(segment: &str) -> bool {
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
 * 1. `TraceHandler::init` 或 `TraceHandler::configure` 调用
 *    `IrFileCache::from_file` 扫描 `.ir` 文件。
 * 2. `from_file` 以 `fn name(...) { ... }` 为边界切分函数体，去掉空行和末尾
 *    source location，把每个函数体保存成 `Vec<String>`。
 * 3. 函数名通过 `Symtab::get` 转成 `Name`，所以缓存键和执行器记录的
 *    `ItracePerInstr::function_name` 保持一致。
 * 4. 执行器只调用 `TraceHandler::submit_path` 提交完成的 path；handler 内部渲染时再
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
 *   这个存储形态；只提交 `TracePerPath`，由 handler 内部查 IR 行并输出。
 * - `pc` 被当作函数体行向量下标使用，因此 `.ir` 缓存规则必须和
 *   `SharedState` 中同一函数的指令顺序一致。
 * - 构建失败、函数缺失、pc 越界或锁中毒都会返回 `None`，调用方负责降级输出。
 */
#[derive(Default)]
pub(super) struct IrFileCache {
    // 像一张“函数名 -> 函数体 IR 行列表”的表：zcache_ok -> ["z0 : %i;", ..., "return = z1;"]。
    pub(super) functions: HashMap<Name, Vec<String>>,
}

impl IrFileCache {
    pub(super) fn from_file(ir_file_path: &PathBuf, symtab: &Symtab) -> Self {
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

    pub(super) fn lookup_line(&self, function_name: Name, pc: u64) -> Option<String> {
        let pc_index = usize::try_from(pc).ok()?;
        self.functions.get(&function_name)?.get(pc_index).map(|line| strip_source_loc(line))
    }
}
