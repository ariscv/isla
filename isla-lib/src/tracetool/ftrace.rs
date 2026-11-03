//! 从已有 SMT Function 事件投影函数调用与返回。
use super::{TraceHandler, TracePerPath};
use crate::bitvector::BV;
use crate::ir::Symtab;
use crate::smt::{Event, Trace};

impl TracePerPath {
    pub(crate) fn capture_function_trace<B: BV>(&mut self, trace: &Trace<B>) {
        // SMT trace 已经保存共享的调用/返回事件；仅在路径交付时按执行顺序投影。
        self.function_trace = trace
            .to_vec()
            .into_iter()
            .rev()
            .filter_map(|event| match event {
                Event::Function { name, call } => Some((*name, *call)),
                _ => None,
            })
            .collect();
    }
    pub(super) fn render_functions(&self, handler: &TraceHandler, symtab: &Symtab, lines: &mut Vec<String>) {
        if handler.ftrace_enabled() {
            for (name, call) in &self.function_trace {
                lines.push(format!(
                    "function_{} function={}",
                    if *call { "call" } else { "return" },
                    symtab.to_str(*name)
                ));
            }
        }
    }
}
