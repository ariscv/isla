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
use crate::smt::{Event, Solver, Sym};
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
    // 3. Use executor::start_single to explore paths
    // 4. Collect paths using a custom collector
    Ok(Vec::new())
}

/// A node in the execution tree
#[derive(Clone, Debug)]
pub struct TreeNode<B> {
    /// Unique identifier for this node
    pub node_id: usize,
    /// Type of node
    pub node_type: NodeType<B>,
    /// Child nodes
    pub children: Vec<TreeNode<B>>,
}

/// The type of tree node
#[derive(Clone, Debug)]
pub enum NodeType<B> {
    /// Root entry node
    Root {
        /// Instruction name being executed
        instruction: String,
    },
    /// Path node - carries constraints and tracks data
    Path {
        /// Constraints accumulated on this path
        constraints: Vec<PathConstraint>,
        /// Symbolic variables encountered
        variables: Vec<String>,
        /// Source location
        location: String,
    },
    /// Branch node - represents a fork in execution
    Branch {
        /// Fork ID from the executor
        fork_id: u32,
        /// The symbolic variable being branched on
        variable: String,
        /// Source location of the branch
        location: String,
    },
    /// Leaf node - execution complete, may need to unfold (zexecute returns a ctor)
    Leaf {
        /// Whether this path is satisfiable
        satisfiable: bool,
        /// Return value from zexecute (a constructor that may need further execution)
        return_value: Option<Val<B>>,
        /// Constructor name if return value is a Ctor
        constructor_name: Option<String>,
        /// Unfolded value representation (for display)
        unfolded_value: Option<String>,
    },
}

/// A constraint on a path
#[derive(Clone, Debug)]
pub struct PathConstraint {
    /// Symbolic variable
    pub variable: String,
    /// Constraint (e.g., "x = true" or "x = false")
    pub constraint: String,
    /// Branch number (0 for true, 1 for false)
    pub branch_num: u32,
}

/// Result of symbolic execution with execution tree
#[derive(Clone, Debug)]
pub struct ExecutionResult<B> {
    /// The execution tree
    pub tree: TreeNode<B>,
    /// Number of execution paths explored
    pub num_paths: usize,
    /// All leaf nodes (execution endpoints)
    pub leaves: Vec<LeafInfo<B>>,
}

/// Information about a leaf node
#[derive(Clone, Debug)]
pub struct LeafInfo<B> {
    /// Path to this leaf (node IDs)
    pub path: Vec<usize>,
    /// Whether satisfiable
    pub satisfiable: bool,
    /// Return value
    pub return_value: Option<Val<B>>,
}

/// Execute an instruction symbolically and collect execution tree
/// Returns an execution tree showing all branches explored
pub fn execute_instruction_tree<B: BV>(
    instruction_name: &str,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Result<ExecutionResult<B>, ExecError> {
    use std::sync::{Arc, Mutex};

    // Find the instruction function (zexecute function dispatches to instruction handlers)
    let zexecute_id = shared_state.symtab.lookup("zexecute");

    // Create an instruction value by calling the constructor
    let encoded_name = format!("z{}", instruction_name);
    let ctor_id = shared_state.symtab.lookup(&encoded_name);

    // Get the constructor type and create a default argument
    let instruction_value = if let Some(union_members) = shared_state.type_info.unions.get(&shared_state.symtab.lookup("zinstruction")) {
        if let Some((_, ctor_ty)) = union_members.iter().find(|(n, _)| *n == ctor_id) {
            let arg_value = generate_default_value(ctor_ty, shared_state);
            Val::Ctor(ctor_id, Box::new(arg_value))
        } else {
            return Err(ExecError::Unreachable(format!("Instruction '{}' not found in zinstruction union", instruction_name)));
        }
    } else {
        return Err(ExecError::Unreachable("zinstruction union not found".to_string()));
    };

    // Get the zexecute function
    let (func_args, ret_ty, instrs) = shared_state.functions.get(&zexecute_id)
        .ok_or_else(|| ExecError::Unreachable("zexecute function not found".to_string()))?;

    // Create initial frame for zexecute
    let mut initial_frame = LocalFrame::new(zexecute_id, func_args, ret_ty, Some(&[instruction_value]), instrs);
    initial_frame.add_regs(regs);
    initial_frame.add_lets(lets);

    // Create task
    let task_state = TaskState::new();
    let task_id = TaskId::fresh();
    let task = initial_frame.task(task_id, &task_state);

    // Track nodes and forks - these must be declared before the closure and live long enough
    let result = Arc::new(Mutex::new(ExecutionResult {
        tree: TreeNode {
            node_id: 0,
            node_type: NodeType::Root {
                instruction: instruction_name.to_string(),
            },
            children: Vec::new(),
        },
        num_paths: 0,
        leaves: Vec::new(),
    }));
    let node_counter = Arc::new(Mutex::new(1usize));
    let current_path = Arc::new(Mutex::new(Vec::new()));

    // Execute with custom collector
    let collected: Vec<Val<B>> = Vec::new();
    let collected = Arc::new(collected);

    // Clone Arcs for closure - use move to transfer ownership into the closure
    let result_clone = Arc::clone(&result);
    let node_counter_clone = Arc::clone(&node_counter);
    let current_path_clone = Arc::clone(&current_path);

    let collector = move |_thread: usize, _task_id: TaskId, exec_result: Result<(Run<B>, LocalFrame<B>), (ExecError, Vec<(Name, usize)>)>, shared_state: &SharedState<B>, solver: Solver<B>, _collected: &Arc<Vec<Val<B>>>| {
        match exec_result {
            Ok((run, _frame)) => {
                // Extract events from solver trace to build the tree
                let events = solver.trace().to_vec();

                let mut result_guard = result_clone.lock().unwrap();
                let mut counter_guard = node_counter_clone.lock().unwrap();
                let mut path_guard = current_path_clone.lock().unwrap();

                // Process events to build the tree structure
                for event in events {
                    if let Event::Fork(fork_id, sym, _branch_num, loc) = event {
                        let var_name = sym.to_string();
                        let location = loc.location_string(shared_state.symtab.files());

                        // Create branch node
                        let node_id = *counter_guard;
                        *counter_guard += 1;

                        let branch_node = TreeNode {
                            node_id,
                            node_type: NodeType::Branch {
                                fork_id: *fork_id,
                                variable: var_name.clone(),
                                location: location.clone(),
                            },
                            children: Vec::new(),
                        };

                        // Track current path
                        path_guard.push(node_id);

                        // Add to tree (simplified: add to root for now)
                        result_guard.tree.children.push(branch_node);
                    }
                }

                match run {
                    Run::Finished(ret_val) => {
                        result_guard.num_paths += 1;

                        // Extract constructor name if return value is a Ctor
                        let constructor_name = if let Val::Ctor(name, _) = &ret_val {
                            Some(shared_state.symtab.to_str(*name).to_string())
                        } else {
                            None
                        };

                        // Add leaf node
                        let node_id = *counter_guard;
                        *counter_guard += 1;

                        // Unfold the return value for better display
                        let unfolded_value = Some(unfold_return_value(&ret_val, shared_state, regs, lets).0);

                        let leaf_node = TreeNode {
                            node_id,
                            node_type: NodeType::Leaf {
                                satisfiable: true,
                                return_value: Some(ret_val.clone()),
                                constructor_name: constructor_name.clone(),
                                unfolded_value,
                            },
                            children: Vec::new(),
                        };

                        // Record leaf info
                        result_guard.leaves.push(LeafInfo {
                            path: path_guard.clone(),
                            satisfiable: true,
                            return_value: Some(ret_val.clone()),
                        });

                        // Add to tree
                        if !result_guard.tree.children.is_empty() {
                            if let Some(last_branch) = result_guard.tree.children.last_mut() {
                                last_branch.children.push(leaf_node);
                            }
                        } else {
                            result_guard.tree.children.push(leaf_node);
                        }

                        path_guard.clear();
                    }
                    Run::Dead => {
                        // Path is unsatisfiable
                        result_guard.num_paths += 1;

                        let node_id = *counter_guard;
                        *counter_guard += 1;

                        let leaf_node = TreeNode {
                            node_id,
                            node_type: NodeType::Leaf {
                                satisfiable: false,
                                return_value: None,
                                constructor_name: None,
                                unfolded_value: None,
                            },
                            children: Vec::new(),
                        };

                        result_guard.leaves.push(LeafInfo {
                            path: path_guard.clone(),
                            satisfiable: false,
                            return_value: None,
                        });

                        if !result_guard.tree.children.is_empty() {
                            if let Some(last_branch) = result_guard.tree.children.last_mut() {
                                last_branch.children.push(leaf_node);
                            }
                        } else {
                            result_guard.tree.children.push(leaf_node);
                        }

                        path_guard.clear();
                    }
                    _ => {}
                }
            }
            Err((error, backtrace)) => {
                eprintln!("执行错误: {:?}", error);
                eprintln!("调用栈: {:?}", backtrace_string(&backtrace, &shared_state.symtab));
            }
        }
    };

    start_single(task, shared_state, &collected, &collector);

    let result_guard = result.lock().unwrap();
    Ok(result_guard.clone())
}

/// Unfold a return value by recursively executing constructor functions
/// Returns a string representation of the unfolded value
pub fn unfold_return_value<B: BV>(
    val: &Val<B>,
    shared_state: &SharedState<B>,
    _regs: &RegisterBindings<B>,
    _lets: &Bindings<B>,
) -> (String, Option<Val<B>>) {
    use std::sync::{Arc, Mutex};

    match val {
        Val::Ctor(name, args) => {
            let ctor_name = shared_state.symtab.to_str(*name);

            // First, try to get the string representation directly
            let args_str = match &**args {
                Val::Unit => "Unit".to_string(),
                Val::I64(n) => format!("i64({})", n),
                Val::I128(n) => format!("i128({})", n),
                Val::Bool(b) => format!("bool({})", b),
                Val::Bits(bv) => format!("bits({})", bv),
                Val::String(s) => format!("\"{}\"", s),
                Val::Symbolic(sym) => format!("sym({})", sym),
                Val::Vector(v) => format!("vector[{}]", v.len()),
                Val::List(l) => format!("list[{}]", l.len()),
                Val::Enum(e) => format!("enum({:?})", e),
                Val::Struct(_s) => "struct{..}".to_string(),
                Val::Ctor(n, _) => {
                    let inner_name = shared_state.symtab.to_str(*n);
                    format!("{}(...)", inner_name)
                }
                Val::Poison => "Poison".to_string(),
                Val::Ref(r) => format!("ref({})", shared_state.symtab.to_str(*r)),
                _ => "<other>".to_string(),
            };

            (format!("{}({})", ctor_name, args_str), Some(val.clone()))
        }
        _ => {
            // For non-ctor values, just return the string representation
            let val_str = match val {
                Val::Unit => "Unit".to_string(),
                Val::I64(n) => format!("{}", n),
                Val::I128(n) => format!("{}", n),
                Val::Bool(b) => format!("{}", b),
                Val::Bits(bv) => format!("{}", bv),
                Val::String(s) => s.clone(),
                Val::Symbolic(sym) => format!("<sym:{}>", sym),
                Val::Poison => "Poison".to_string(),
                Val::Ref(r) => format!("<ref:{}>", shared_state.symtab.to_str(*r)),
                _ => "<complex>".to_string(),
            };
            (val_str, Some(val.clone()))
        }
    }
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
pub fn format_tree_ascii<B: BV>(result: &ExecutionResult<B>) -> String {
    let mut output = String::new();

    output.push_str(&format!("指令执行树 ({} 条路径):\n", result.num_paths));
    output.push_str("\n");

    // Helper function to recursively print tree
    fn print_tree<B: BV>(node: &TreeNode<B>, output: &mut String, prefix: &str, is_last: bool) {
        match &node.node_type {
            NodeType::Root { instruction } => {
                output.push_str(&format!("{}�指令: {}\n", prefix, instruction));
            }
            NodeType::Branch { fork_id, variable, location } => {
                output.push_str(&format!("{}🔀 分岔 #{}: {} @ {}\n", prefix, fork_id, variable, location));
            }
            NodeType::Leaf { satisfiable, return_value, constructor_name, unfolded_value } => {
                let sat_str = if *satisfiable { "✓ 可满足" } else { "✗ 不可满足" };
                output.push_str(&format!("{}🍁 {} ", prefix, sat_str));
                if let Some(name) = constructor_name {
                    output.push_str(&format!("(返回: {})", name));
                }
                if let Some(unfolded) = unfolded_value {
                    output.push_str(&format!(" => {}", unfolded));
                } else if let Some(_) = return_value {
                    output.push_str(" [有返回值]");
                }
                output.push_str("\n");
            }
            NodeType::Path { constraints, variables, location } => {
                output.push_str(&format!("{}📍 路径 @ {}\n", prefix, location));
                for (i, constraint) in constraints.iter().enumerate() {
                    output.push_str(&format!("{}   约束 {}: {} = {}\n", prefix, i, constraint.variable, constraint.constraint));
                }
            }
        }

        let child_count = node.children.len();
        for (i, child) in node.children.iter().enumerate() {
            let is_last_child = i == child_count - 1;
            let new_prefix = if is_last {
                format!("{}    ", prefix)
            } else {
                format!("{}│   ", prefix)
            };
            let connector = if is_last { "└── " } else { "├── " };
            output.push_str(&format!("{}{}", prefix, connector));
            print_tree(child, output, &new_prefix, is_last_child);
        }
    }

    print_tree(&result.tree, &mut output, "", result.tree.children.len() <= 1);

    output
}

/// Format an execution tree as Graphviz DOT format
pub fn format_tree_graphviz<B: BV>(result: &ExecutionResult<B>) -> String {
    let mut output = String::new();

    output.push_str("digraph ExecutionTree {\n");
    output.push_str("  rankdir=TB;\n");
    output.push_str("  node [shape=box, fontname=\"Courier\"];\n");
    output.push_str("  edge [fontname=\"Courier\"];\n");
    output.push_str("\n");

    // Helper function to recursively generate graphviz nodes and edges
    fn generate_graphviz<B: BV>(
        node: &TreeNode<B>,
        output: &mut String,
        parent_id: Option<usize>,
        node_counter: &mut usize,
    ) {
        let current_id = *node_counter;
        *node_counter += 1;

        // Generate node label
        let label = match &node.node_type {
            NodeType::Root { instruction } => {
                format!("指令:\\n{}", instruction)
            }
            NodeType::Branch { fork_id, variable, location } => {
                // Shorten location for readability
                let loc_short = location.lines().next().unwrap_or("");
                format!("分岔 #{}:\\n{} @ {}", fork_id, variable, loc_short)
            }
            NodeType::Leaf { satisfiable, return_value, constructor_name, unfolded_value } => {
                let sat_str = if *satisfiable { "✓" } else { "✗" };
                let mut label = format!("{} ", sat_str);
                if let Some(name) = constructor_name {
                    label.push_str(&format!("返回:\\n{}", name));
                }
                if let Some(unfolded) = unfolded_value {
                    label.push_str(&format!("\\n=> {}", unfolded));
                }
                label
            }
            NodeType::Path { constraints, .. } => {
                format!("路径\\n({} 个约束)", constraints.len())
            }
        };

        // Escape label for graphviz
        let label_escaped = label.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n");

        output.push_str(&format!("  node{} [label=\"{}\"];\n", current_id, label_escaped));

        // Generate edge from parent
        if let Some(pid) = parent_id {
            output.push_str(&format!("  node{} -> node{};\n", pid, current_id));
        }

        // Recursively process children
        for child in &node.children {
            generate_graphviz(child, output, Some(current_id), node_counter);
        }
    }

    let mut node_counter = 0;
    generate_graphviz(&result.tree, &mut output, None, &mut node_counter);

    output.push_str("}\n");
    output
}
