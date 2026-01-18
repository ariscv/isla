// BSD 2-Clause License
//
// Copyright (c) 2025
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// 1. Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

//! Instruction architecture exploration module for symbolic execution of RISC-V instructions.

use crate::bitvector::BV;
use crate::config::ISAConfig;
use crate::error::ExecError;
use crate::executor::{backtrace_string, start_single, LocalFrame, Run, TaskId, TaskState};
use crate::ir::*;
use crate::register::RegisterBindings;
use crate::smt::{Solver, Sym};
use crate::zencode;
use std::collections::HashMap;
use std::str::FromStr;
use std::sync::{Arc, Mutex};

/**
 * instruction list gen
  */

/* ==重构start== */

/// 通用的IR函数执行API
/// 执行指定的IR函数并返回结果
pub fn execute_ir_function<B: BV>(
    function_name: &str,
    args: &[Val<B>],
    shared_state: &&SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Option<Val<B>> {
    let result: Arc<Mutex<Option<Val<B>>>> = Arc::new(Mutex::new(None));

    // 获取函数信息
    let function_id = shared_state.symtab.lookup(function_name);
    let (func_args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();

    // 创建初始帧
    let mut initial_frame = LocalFrame::new(function_id, func_args, ret_ty, Some(args), instrs);
    initial_frame.add_regs(regs);
    initial_frame.add_lets(lets);

    // 创建任务
    let task_state = TaskState::new();
    let task_id = TaskId::fresh();
    let task = initial_frame.task(task_id, &task_state);

    // 执行任务
    let collected: Vec<Val<B>> = Vec::new();
    let collected = Arc::new(collected);

    start_single(task, shared_state, &collected, &|_thread, _task_id, exec_result, shared_state, _solver, _collected| {
        match exec_result {
            Ok((run, _frame)) => {
                match run {
                    Run::Finished(ret_val) => {
                        *result.lock().unwrap() = Some(ret_val);
                    }
                    _ => {}
                }
            }
            Err((error, backtrace)) => {
                // MatchFailure 可能由于以下原因发生：
                // 1. IR 文件包含了特定架构的指令（如 RV32 指令在 RV64 IR 中）
                // 2. 这些指令存在于 zinstruction union 中，但在 zassembly_forwards 中没有处理
                // 这是 IR 文件的设计特性，不是代码错误
                match &error {
                    ExecError::MatchFailure(_) => {
                        // 静默处理 - 指令没有汇编名称映射
                    }
                    _ => {
                        eprintln!("执行错误: {:?}", error);
                        eprintln!("调用栈: {:?}", backtrace_string(&backtrace, &shared_state.symtab));
                    }
                }
            }
        }
    });

    let res = result.lock().unwrap().as_ref().cloned();
    res
}

/// 根据类型生成默认值
pub fn generate_default_value<B: BV>(ty: &Ty<Name>, shared_state: &SharedState<B>) -> Val<B> {
    match ty {
        Ty::Unit => Val::Unit,
        Ty::I64 => Val::I64(0),
        Ty::I128 => Val::I128(0),
        Ty::Bool => Val::Bool(false),
        Ty::Bits(n) => Val::Bits(B::zeros(*n)),
        Ty::String => Val::String(String::new()),
        Ty::Vector(elem_ty) => Val::Vector(vec![generate_default_value(elem_ty, shared_state)]),
        Ty::List(elem_ty) => Val::List(vec![generate_default_value(elem_ty, shared_state)]),
        Ty::Enum(enum_name) => {
            // 获取枚举的第一个成员作为默认值
            if let Some(_members) = shared_state.type_info.enums.get(enum_name) {
                Val::Enum(crate::smt::EnumId::from_name(*enum_name).first_member())
            } else {
                Val::Poison
            }
        }
        Ty::Struct(struct_name) => {
            // 为结构体的每个字段生成默认值
            let mut fields: std::collections::HashMap<Name, Val<B>> = std::collections::HashMap::new();
            if let Some(struct_def) = shared_state.type_info.structs.get(struct_name) {
                for (field_name, field_ty) in struct_def {
                    fields.insert(*field_name, generate_default_value(field_ty, shared_state));
                }
            }
            // 转换为 ahash::HashMap 类型以匹配 Val::Struct 的要求
            let ahash_fields: ahash::HashMap<Name, Val<B>> =
                fields.into_iter().collect();
            Val::Struct(ahash_fields)
        }
        _ => Val::Unit, // 对于其他类型，使用 Unit 作为默认值
    }
}

/// 获取zassembly_forwards函数的执行结果
/// 传入指令名称，返回对应的汇编名称
pub fn get_assembly_name<B: BV>(
    instruction_name: &str,
    shared_state: &&SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Option<String> {
    // 查找指令的构造函数名称
    let encoded_name = format!("{}", instruction_name);
    let ctor_name = shared_state.symtab.lookup(&encoded_name);

    // 从 union 类型信息中获取构造函数的参数类型
    let instruction_union = shared_state.type_info.unions.get(
        &shared_state.symtab.lookup("zinstruction")
    );

    let Some(union_members) = instruction_union else {
        // zinstruction union 不存在
		panic!("get_assembly_name: 在symtab中没找到符号'zinstruction'");
    };

    // 查找当前构造函数的类型
    let Some((_, ctor_ty)) = union_members.iter().find(|(n, _ty)| *n == ctor_name) else {
        // 指令不在 zinstruction union 中（可能是其他架构的指令）
        return None;
    };

    // 根据构造函数的参数类型生成默认值
    let arg_value = match ctor_ty {
        Ty::Unit => Val::Unit,
        ty => generate_default_value(ty, *shared_state),
    };

    // 构造指令值
    let instr_value = Val::<B>::Ctor(ctor_name, Box::new(arg_value));

    // 执行 zassembly_forwards 函数
    // MatchFailure 错误会被 execute_ir_function 静默处理
    match execute_ir_function("zassembly_forwards", &[instr_value], shared_state, regs, lets) {
        Some(Val::String(s)) => Some(s),
        _ => None,
    }
}
pub fn get_instruction_list<B: BV>(
    shared_state: &&SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
)  -> HashMap<String, (Name, Ty<Name>, String)> {
		let results: Vec<_> = shared_state.type_info.unions.get(  &shared_state.symtab.lookup("zinstruction")  ).unwrap()
            .iter().map(
                |(n,ty)| {

					let inst_union_name_str=String::from_str(shared_state.symtab.to_str(*n)).unwrap();
					let s=&inst_union_name_str;
					//直接执行zassembly_forwards函数，执行zMRET、zADD这样的CTOR（构造函数），得到具体的汇编，比如add x1,x2,x3
					let inst_assembly=get_assembly_name::<B>(s, shared_state, regs, lets);
					(inst_assembly.clone(),(*n,ty.clone(),inst_union_name_str.clone()))
				}
            )
            .collect::<Vec<_>>();

	// 找出没有汇编名称的指令
	let no_assembly:Vec<_> = results.iter().filter(|(asm,_)| asm.is_none()).map(|(inst_assembly,(n,ty,inst_union_name_str))| inst_union_name_str.clone()).collect();
	if !no_assembly.is_empty() {
		eprintln!("警告: 以下 {} 个指令没有汇编名称映射:", no_assembly.len());
		for name in &no_assembly {
			// 调试：检查指令类型
			if let Some(union_members) = shared_state.type_info.unions.get(&shared_state.symtab.lookup("zinstruction")) {
				if let Some((_, ty)) = union_members.iter().find(|(n, _)| shared_state.symtab.to_str(*n) == *name) {
					eprintln!("  - {} (类型: {:?})", name, ty);
				} else {
					eprintln!("  - {} (不在 union 中)", name);
				}
			}
		}
	}

	let instruction_list=results.iter().filter_map(
			|(k,v)| 
				k.as_ref().map(|key|
					 (key.clone(), v.clone())
					)
		).collect::<HashMap<_,_>>();
	// println!("{:?}", instruction_list);

	// instruction_list
	instruction_list
}

/* ==重构end== */


/**
 * 符号执行部分
  */
/// Information about an instruction extracted from the IR
#[derive(Clone, Debug)]
pub struct InstructionInfo {
    /// The encoded name in the IR (e.g., "zMRET")
    pub encoded_name: String,
    /// The assembly name (e.g., "mret")
    pub assembly_name: String,
    /// The function ID in the IR
    pub function_id: Name,
}

/// A condition on an execution path
#[derive(Clone, Debug)]
pub enum PathCondition {
    /// Initial entry point (no condition)
    Initial,
    /// Branch condition
    Branch {
        variable: Sym,
        is_true: bool,
        description: String,
    },
}

/// ISA state snapshot
#[derive(Clone, Debug)]
pub struct ISAState<B> {
    /// General purpose registers
    pub registers: HashMap<Name, Val<B>>,
    /// Control and status registers
    pub csrs: HashMap<String, Val<B>>,
    /// Special registers (PC, privilege level, etc.)
    pub special_regs: HashMap<String, Val<B>>,
}

/// An execution path with conditions and state
#[derive(Clone, Debug)]
pub struct ExecutionPath<B> {
    /// Path identifier
    pub path_id: usize,
    /// Conditions on this path
    pub conditions: Vec<PathCondition>,
    /// ISA state at the end of the path
    pub isa_state: ISAState<B>,
    /// Whether the path is satisfiable
    pub satisfiable: bool,
}

/// Result of solving a path
#[derive(Debug)]
pub enum SolveResult<B> {
    /// Satisfiable with concrete values
    Sat {
        /// Symbolic variable to concrete value mapping
        values: HashMap<String, Val<B>>,
    },
    /// Unsatifiable
    Unsat,
    /// Unknown (solver timeout or other issue)
    Unknown,
}

/// Error during instruction dictionary building
#[derive(Debug)]
pub enum BuildError {
    /// Function not found
    FunctionNotFound(String),
    /// Invalid IR structure
    InvalidIR(String),
}

impl std::fmt::Display for BuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            BuildError::FunctionNotFound(name) => write!(f, "Function not found: {}", name),
            BuildError::InvalidIR(msg) => write!(f, "Invalid IR structure: {}", msg),
        }
    }
}

impl std::error::Error for BuildError {}


/// Execute an instruction symbolically and collect execution paths
pub fn execute_instruction<B: BV>(
    instruction: &str,
    shared_state: &SharedState<B>,
    options: &ExecOptions,
) -> Result<Vec<ExecutionPath<B>>, ExecError> {
    // TODO: Implement symbolic execution
    // This will:
    // 1. Find the instruction in the IR
    // 2. Create a task for execution
    // 3. Use executor::start_multi to explore paths
    // 4. Collect paths using a custom collector
    Ok(Vec::new())
}

/// Execution options
pub struct ExecOptions {
    /// Use config defaults for unconstrained fields
    pub init_isa_with_config: bool,
    /// Timeout in seconds
    pub timeout: Option<u64>,
    /// Number of threads
    pub num_threads: usize,
}

/**
 * 数据依赖追踪
 */

/// Solve a path's constraints to get concrete values
pub fn solve_path<B: BV>(
    path: &ExecutionPath<B>,
    solver: &mut Solver<B>,
    isa_config: &ISAConfig<B>,
    init_with_config: bool,
) -> SolveResult<B> {
    // TODO: Implement constraint solving
    // This will:
    // 1. Build SMT constraints from path conditions
    // 2. Check satisfiability
    // 3. If sat, extract model values
    // 4. Fill unconstrained variables with defaults or random values
    SolveResult::Unknown
}

/// Format an execution tree as ASCII art
pub fn format_tree_ascii<B: BV>(paths: &[ExecutionPath<B>]) -> String {
    let mut output = String::new();

    if paths.is_empty() {
        output.push_str("(no paths)\n");
        return output;
    }

    // Simple tree rendering
    output.push_str(&format!("Instruction execution tree ({} paths):\n", paths.len()));
    output.push_str("\n");

    for (i, path) in paths.iter().enumerate() {
        output.push_str(&format!("Path {}:\n", i));
        for (j, cond) in path.conditions.iter().enumerate() {
            match cond {
                PathCondition::Initial => {
                    output.push_str(&format!("  [{}]: Entry point\n", j));
                }
                PathCondition::Branch { is_true, description, .. } => {
                    output.push_str(&format!("  [{}]: {} ({})\n", j, description, if *is_true { "true" } else { "false" }));
                }
            }
        }
        output.push_str(&format!("  -> Satisfiable: {}\n", path.satisfiable));
        output.push_str("\n");
    }

    output
}

/// Format an execution tree as Graphviz DOT format
pub fn format_tree_graphviz<B: BV>(paths: &[ExecutionPath<B>]) -> String {
    let mut output = String::new();

    output.push_str("digraph ExecutionTree {\n");
    output.push_str("  node [shape=box];\n");
    output.push_str("\n");

    // Create entry node
    output.push_str("  entry [label=\"Entry\"];\n");

    for (i, path) in paths.iter().enumerate() {
        let node_id = format!("path{}", i);
        let mut label = format!("Path {}\\n", i);

        for cond in &path.conditions {
            match cond {
                PathCondition::Initial => {
                    label.push_str("Entry point\\n");
                }
                PathCondition::Branch { is_true, description, .. } => {
                    label.push_str(&format!("{} ({})\\n", description, if *is_true { "T" } else { "F" }));
                }
            }
        }

        label.push_str(&format!("Sat: {}", path.satisfiable));
        output.push_str(&format!("  {} [label=\"{}\"];\n", node_id, label));
        output.push_str(&format!("  entry -> {};\n", node_id));
    }

    output.push_str("}\n");
    output
}
