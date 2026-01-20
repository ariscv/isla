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
use crate::smt::smtlib::Exp;
use petgraph::graph::{Graph, NodeIndex};
use petgraph::Direction;
use std::collections::HashMap;
use std::fmt;
use std::io::Write;
use std::str::FromStr;
use std::sync::{Arc, Mutex};

/// 追踪符号变量约束到寄存器约束
///
/// 递归地追踪符号变量通过依赖链到寄存器，并将约束传播到寄存器。
///
/// # 参数
/// * `sym_id` - 当前符号变量 ID
/// * `constraint_value` - 约束值（true/false）
/// * `sym_to_reg` - 符号变量到寄存器的映射
/// * `sym_dependencies` - 符号变量依赖图
/// * `sym_to_value` - 符号变量到布尔值的映射（用于简单常量）
/// * `register_constraints` - 输出的寄存器约束
fn trace_symbol_to_register(
    sym_id: u32,
    constraint_value: bool,
    sym_to_reg: &std::collections::HashMap<u32, String>,
    sym_dependencies: &std::collections::HashMap<u32, Vec<u32>>,
    sym_to_value: &std::collections::HashMap<u32, bool>,
    register_constraints: &mut std::collections::HashMap<String, bool>,
) {
    // 如果这个符号变量直接对应一个寄存器，添加约束
    if let Some(reg_name) = sym_to_reg.get(&sym_id) {
        register_constraints.insert(reg_name.clone(), constraint_value);
        return;
    }

    // 如果这个符号变量有依赖，递归追踪依赖
    if let Some(deps) = sym_dependencies.get(&sym_id) {
        // 如果只有一个依赖，传播约束
        if deps.len() == 1 {
            let dep_id = deps[0];
            trace_symbol_to_register(
                dep_id,
                constraint_value,
                sym_to_reg,
                sym_dependencies,
                sym_to_value,
                register_constraints,
            );
        }
        // 如果有多个依赖，说明这是复合表达式（如 And、Or）
        // 这种情况比较复杂，暂时跳过
    }
}

/// 从表达式中提取依赖的符号变量
fn extract_exp_dependencies(exp: &Exp<crate::smt::Sym>, deps: &mut Vec<u32>) {
    match exp {
        Exp::Var(sym) => {
            deps.push(sym.id);
        }
        Exp::Not(e) => {
            extract_exp_dependencies(e, deps);
        }
        Exp::And(l, r) => {
            extract_exp_dependencies(l, deps);
            extract_exp_dependencies(r, deps);
        }
        Exp::Or(l, r) => {
            extract_exp_dependencies(l, deps);
            extract_exp_dependencies(r, deps);
        }
        Exp::Eq(l, r) => {
            extract_exp_dependencies(l, deps);
            extract_exp_dependencies(r, deps);
        }
        Exp::Neq(l, r) => {
            extract_exp_dependencies(l, deps);
            extract_exp_dependencies(r, deps);
        }
        Exp::Bits(_) | Exp::Bits64(_) | Exp::Bool(_) | Exp::Enum(_) => {}
        _ => {}
    }
}

/// 从值中递归提取符号变量
fn extract_symbolic_from_val<B>(val: &Val<B>, found: &mut Vec<Sym>)
where
    Val<B>: Clone,
{
    match val {
        Val::Symbolic(sym) => {
            found.push(*sym);
        }
        Val::Vector(v) => {
            for item in v {
                extract_symbolic_from_val(item, found);
            }
        }
        Val::List(l) => {
            for item in l {
                extract_symbolic_from_val(item, found);
            }
        }
        Val::Struct(fields) => {
            for (_name, val) in fields {
                extract_symbolic_from_val(val, found);
            }
        }
        Val::Ctor(_name, val) => {
            extract_symbolic_from_val(val, found);
        }
        Val::SymbolicCtor(_sym, fields) => {
            for (_name, val) in fields {
                extract_symbolic_from_val(val, found);
            }
        }
        _ => {
            // 其他类型不包含符号变量
        }
    }
}

/**
 * instruction list gen
  */

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

/// 执行图边数据
///
/// 表示执行图中节点之间的连接关系。
#[derive(Clone, Debug)]
pub enum EdgeData {
    /// 无条件边（顺序执行）
    Unconditional,
    /// 条件边（分支）
    Conditional {
        /// 分支编号（0 = 真, 1 = 假）
        branch_num: u32,
    },
}

impl fmt::Display for EdgeData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EdgeData::Unconditional => write!(f, ""),
            EdgeData::Conditional { branch_num } => {
                write!(f, "{}", if *branch_num == 0 { "T" } else { "F" })
            }
        }
    }
}

/// 执行图节点数据
///
/// 表示指令符号执行过程中的一个状态点。
#[derive(Clone, Debug)]
pub struct ExecutionNode<B> {
    /// 节点类型
    pub node_type: NodeType<B>,
}

impl<B> fmt::Display for ExecutionNode<B>
where
    NodeType<B>: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.node_type)
    }
}

/// 执行图
///
/// 使用 petgraph 的图结构来表示控制流图（CFG）。
pub struct ExecutionGraph<B> {
    /// petgraph 图结构
    pub graph: Graph<ExecutionNode<B>, EdgeData>,
    /// 根节点索引
    pub root: NodeIndex,
}

impl<B> ExecutionGraph<B>
where
    NodeType<B>: Clone,
{
    /// 创建一个新的执行图
    ///
    /// # 参数
    /// * `root_type` - 根节点类型
    pub fn new(root_type: NodeType<B>) -> Self {
        let mut graph = Graph::new();
        let root = graph.add_node(ExecutionNode { node_type: root_type });
        ExecutionGraph { graph, root }
    }

    /// 获取根节点索引
    pub fn root(&self) -> NodeIndex {
        self.root
    }

    /// 添加一个节点
    ///
    /// # 参数
    /// * `node_type` - 节点类型
    /// # 返回
    /// 新节点的索引
    pub fn add_node(&mut self, node_type: NodeType<B>) -> NodeIndex {
        self.graph.add_node(ExecutionNode { node_type })
    }

    /// 添加一条边
    ///
    /// # 参数
    /// * `source` - 源节点索引
    /// * `target` - 目标节点索引
    /// * `edge_data` - 边数据
    pub fn add_edge(&mut self, source: NodeIndex, target: NodeIndex, edge_data: EdgeData) {
        self.graph.add_edge(source, target, edge_data);
    }

    /// 深度优先遍历（DFS）
    ///
    /// # 参数
    /// * `visitor` - 访问者函数，对每个节点调用，返回 true 继续遍历，false 停止
    pub fn dfs<F>(&self, mut visitor: F)
    where
        F: FnMut(NodeIndex, &NodeType<B>) -> bool,
    {
        let mut visited = std::collections::HashSet::new();
        self.dfs_recursive(self.root, &mut visitor, &mut visited);
    }

    fn dfs_recursive<F>(
        &self,
        node: NodeIndex,
        visitor: &mut F,
        visited: &mut std::collections::HashSet<NodeIndex>,
    ) where
        F: FnMut(NodeIndex, &NodeType<B>) -> bool,
    {
        if !visited.insert(node) {
            return;
        }

        let node_data = &self.graph[node];
        if !visitor(node, &node_data.node_type) {
            return;
        }

        for neighbor in self.graph.neighbors_directed(node, Direction::Outgoing) {
            self.dfs_recursive(neighbor, visitor, visited);
        }
    }

    /// 广度优先遍历（BFS）
    ///
    /// # 参数
    /// * `visitor` - 访问者函数，对每个节点调用，返回 true 继续遍历，false 停止
    pub fn bfs<F>(&self, mut visitor: F)
    where
        F: FnMut(NodeIndex, &NodeType<B>) -> bool,
    {
        use std::collections::VecDeque;
        let mut visited = std::collections::HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(self.root);

        while let Some(node) = queue.pop_front() {
            if !visited.insert(node) {
                continue;
            }

            let node_data = &self.graph[node];
            if !visitor(node, &node_data.node_type) {
                break;
            }

            for neighbor in self.graph.neighbors_directed(node, Direction::Outgoing) {
                if !visited.contains(&neighbor) {
                    queue.push_back(neighbor);
                }
            }
        }
    }

    /// 根据条件查找节点
    ///
    /// # 参数
    /// * `predicate` - 谓词函数，返回 true 表示匹配
    /// # 返回
    /// 第一个匹配的节点索引
    pub fn find<F>(&self, predicate: F) -> Option<NodeIndex>
    where
        F: Fn(&NodeType<B>) -> bool,
    {
        let mut result = None;
        self.dfs(|_idx, node_type| {
            if predicate(node_type) {
                result = Some(_idx);
                false
            } else {
                true
            }
        });
        result
    }

    /// 统计图的总节点数
    pub fn node_count(&self) -> usize {
        self.graph.node_count()
    }

    /// 统计叶子节点数
    pub fn leaf_count(&self) -> usize {
        let mut count = 0;
        for node in self.graph.node_indices() {
            if self.graph.neighbors_directed(node, Direction::Outgoing).count() == 0 {
                count += 1;
            }
        }
        count
    }

    /// 获取图的最大深度
    pub fn max_depth(&self) -> usize {
        self.max_depth_recursive(self.root, &mut std::collections::HashSet::new())
    }

    fn max_depth_recursive(
        &self,
        node: NodeIndex,
        visited: &mut std::collections::HashSet<NodeIndex>,
    ) -> usize {
        if !visited.insert(node) {
            return 0;
        }

        let children: Vec<_> = self
            .graph
            .neighbors_directed(node, Direction::Outgoing)
            .collect();
        if children.is_empty() {
            return 1;
        }
        1 + children
            .iter()
            .map(|child| self.max_depth_recursive(*child, visited))
            .max()
            .unwrap_or(0)
    }

    /// 获取所有叶子节点
    pub fn leaves(&self) -> Vec<NodeIndex> {
        let mut leaves = Vec::new();
        for node in self.graph.node_indices() {
            if self.graph.neighbors_directed(node, Direction::Outgoing).count() == 0 {
                leaves.push(node);
            }
        }
        leaves
    }

    /// 将图格式化为 ASCII 艺术
    ///
    /// # 参数
    /// * `num_paths` - 执行路径数量（用于显示）
    pub fn format_ascii(&self, num_paths: usize) -> String {
        let mut output = String::new();

        output.push_str(&format!("指令执行图 ({} 条路径):\n", num_paths));
        output.push_str("\n");

        // 递归打印图的辅助函数
        fn print_graph<B>(
            graph: &Graph<ExecutionNode<B>, EdgeData>,
            node: NodeIndex,
            output: &mut String,
            prefix: &str,
            is_last: bool,
            visited: &mut std::collections::HashSet<NodeIndex>,
        ) where
            NodeType<B>: Clone,
        {
            if !visited.insert(node) {
                return;
            }

            let node_data = &graph[node];
            match &node_data.node_type {
                NodeType::Root { instruction } => {
                    output.push_str(&format!("{}📋 指令: {}\n", prefix, instruction));
                }
                NodeType::Branch { fork_id, variable, location } => {
                    output.push_str(&format!(
                        "{}🔀 分岔 #{}: {} @ {}\n",
                        prefix, fork_id, variable, location
                    ));
                }
                NodeType::Leaf {
                    satisfiable,
                    constructor_name,
                    unfolded_value,
                    ..
                } => {
                    let sat_str = if *satisfiable { "✓ 可满足" } else { "✗ 不可满足" };
                    output.push_str(&format!("{}🍁 {} ", prefix, sat_str));
                    if let Some(name) = constructor_name {
                        output.push_str(&format!("(返回: {})", name));
                    }
                    if let Some(unfolded) = unfolded_value {
                        output.push_str(&format!(" => {}", unfolded));
                    }
                    output.push_str("\n");
                }
                NodeType::Path {
                    constraints,
                    location,
                    ..
                } => {
                    output.push_str(&format!("{}📍 路径 @ {}\n", prefix, location));
                    for (i, constraint) in constraints.iter().enumerate() {
                        output
                            .push_str(&format!("{}   约束 {}: {}\n", prefix, i, constraint.format()));
                    }
                }
            }

            let mut children: Vec<_> =
                graph.neighbors_directed(node, Direction::Outgoing).collect();
            // 为了稳定性，按索引排序
            children.sort_by_key(|n| n.index());

            let child_count = children.len();
            for (i, child) in children.iter().enumerate() {
                let is_last_child = i == child_count - 1;
                let new_prefix = if is_last_child {
                    format!("{}    ", prefix)
                } else {
                    format!("{}│   ", prefix)
                };
                let connector = if is_last_child { "└── " } else { "├── " };
                output.push_str(&format!("{}{}", prefix, connector));
                print_graph(graph, *child, output, &new_prefix, is_last_child, visited);
            }
        }

        print_graph(&self.graph, self.root, &mut output, "", true, &mut std::collections::HashSet::new());

        output
    }

    /// 将图格式化为 Graphviz DOT 格式
    pub fn format_graphviz(&self) -> String
    where
        NodeType<B>: fmt::Display,
    {
        let mut buf = Vec::new();

        // 手动构建 DOT 输出
        writeln!(&mut buf, "digraph ExecutionGraph {{").unwrap();
        writeln!(&mut buf, "  rankdir=TB;").unwrap();
        writeln!(&mut buf, "  node [shape=box, fontname=\"Courier\"];").unwrap();
        writeln!(&mut buf, "  edge [fontname=\"Courier\"];").unwrap();
        writeln!(&mut buf).unwrap();

        // 输出节点
        for node in self.graph.node_indices() {
            let node_data = &self.graph[node];
            writeln!(
                &mut buf,
                "  \"{}\" [label=\"{}\"];",
                node.index(),
                Self::escape_label(&node_data.to_string())
            )
            .unwrap();
        }

        // 输出边
        for edge in self.graph.edge_indices() {
            if let Some((source, target)) = self.graph.edge_endpoints(edge) {
                let edge_data = &self.graph[edge];
                let label = edge_data.to_string();
                if label.is_empty() {
                    writeln!(
                        &mut buf,
                        "  \"{}\" -> \"{}\";",
                        source.index(),
                        target.index()
                    )
                    .unwrap();
                } else {
                    writeln!(
                        &mut buf,
                        "  \"{}\" -> \"{}\" [label=\"{}\"];",
                        source.index(),
                        target.index(),
                        label
                    )
                    .unwrap();
                }
            }
        }

        writeln!(&mut buf, "}}").unwrap();

        String::from_utf8(buf).unwrap()
    }

    /// 转义 DOT 标签中的特殊字符
    fn escape_label(s: &str) -> String {
        s.replace('\\', "\\\\")
            .replace('"', "\\\"")
            .replace('\n', "\\n")
    }

    /// 获取节点类型
    pub fn node_type(&self, node: NodeIndex) -> Option<&NodeType<B>> {
        self.graph.node_weight(node).map(|n| &n.node_type)
    }

    /// 判断节点是否为叶子节点
    pub fn is_leaf(&self, node: NodeIndex) -> bool {
        self.graph.neighbors_directed(node, Direction::Outgoing).count() == 0
    }
}

/// 树节点类型
///
/// 定义了执行树中可能出现的各种节点类型。
#[derive(Clone, Debug)]
pub enum NodeType<B> {
    /// 根节点 - 执行树的入口
    Root {
        /// 正在执行的指令名称
        instruction: String,
    },
    /// 路径节点 - 携带约束条件并追踪数据
    Path {
        /// 此路径上累积的约束条件
        constraints: Vec<PathConstraint>,
        /// 遇到的符号变量
        variables: Vec<String>,
        /// 源代码位置
        location: String,
    },
    /// 分支节点 - 表示执行中的分岔点
    Branch {
        /// 来自执行器的分支 ID
        fork_id: u32,
        /// 被分支的符号变量
        variable: String,
        /// 分支的源代码位置
        location: String,
    },
    /// 叶子节点 - 执行完成，可能需要展开（zexecute 返回构造函数）
    Leaf {
        /// 此路径是否可满足
        satisfiable: bool,
        /// zexecute 的返回值（可能需要进一步执行的构造函数）
        return_value: Option<Val<B>>,
        /// 如果返回值是 Ctor，则为构造函数名称
        constructor_name: Option<String>,
        /// 展开后的值表示（用于显示）
        unfolded_value: Option<String>,
    },
}

impl<B> fmt::Display for NodeType<B>
where
    Val<B>: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeType::Root { instruction } => {
                write!(f, "{}", instruction)
            }
            NodeType::Branch { fork_id, variable, location } => {
                let loc_short = location.lines().next().unwrap_or("");
                write!(f, "分岔 #{}, {}", fork_id, variable)
            }
            NodeType::Leaf {
                satisfiable,
                constructor_name,
                unfolded_value,
                ..
            } => {
                let sat_str = if *satisfiable { "✓" } else { "✗" };
                write!(f, "{} ", sat_str)?;
                if let Some(name) = constructor_name {
                    write!(f, "返回: {}", name)?;
                }
                if let Some(unfolded) = unfolded_value {
                    write!(f, " => {}", unfolded)?;
                }
                Ok(())
            }
            NodeType::Path { constraints, .. } => {
                write!(f, "路径 ({} 个约束)", constraints.len())
            }
        }
    }
}

impl<B> NodeType<B> {
    /// 获取节点的显示名称
    pub fn display_name(&self) -> &str {
        match self {
            NodeType::Root { .. } => "根节点",
            NodeType::Path { .. } => "路径节点",
            NodeType::Branch { .. } => "分支节点",
            NodeType::Leaf { .. } => "叶子节点",
        }
    }

    /// 判断是否为根节点
    pub fn is_root(&self) -> bool {
        matches!(self, NodeType::Root { .. })
    }

    /// 判断是否为路径节点
    pub fn is_path(&self) -> bool {
        matches!(self, NodeType::Path { .. })
    }

    /// 判断是否为分支节点
    pub fn is_branch(&self) -> bool {
        matches!(self, NodeType::Branch { .. })
    }

    /// 判断是否为叶子节点
    pub fn is_leaf(&self) -> bool {
        matches!(self, NodeType::Leaf { .. })
    }

    /// 获取指令名称（仅对根节点有效）
    pub fn as_root(&self) -> Option<&str> {
        match self {
            NodeType::Root { instruction } => Some(instruction),
            _ => None,
        }
    }

    /// 获取路径节点信息（仅对路径节点有效）
    pub fn as_path(&self) -> Option<(&[PathConstraint], &[String], &str)> {
        match self {
            NodeType::Path {
                constraints,
                variables,
                location,
            } => Some((constraints, variables, location)),
            _ => None,
        }
    }

    /// 获取分支节点信息（仅对分支节点有效）
    pub fn as_branch(&self) -> Option<(u32, &str, &str)> {
        match self {
            NodeType::Branch {
                fork_id,
                variable,
                location,
            } => Some((*fork_id, variable, location)),
            _ => None,
        }
    }

    /// 获取叶子节点信息（仅对叶子节点有效）
    pub fn as_leaf(&self) -> Option<LeafNodeInfo<B>> {
        match self {
            NodeType::Leaf {
                satisfiable,
                return_value,
                constructor_name,
                unfolded_value,
            } => Some(LeafNodeInfo {
                satisfiable: *satisfiable,
                return_value: return_value.as_ref(),
                constructor_name: constructor_name.as_deref(),
                unfolded_value: unfolded_value.as_deref(),
            }),
            _ => None,
        }
    }
}

/// 叶子节点信息的视图
///
/// 提供对叶子节点相关数据的只读访问，避免直接匹配枚举。
pub struct LeafNodeInfo<'a, B> {
    /// 此路径是否可满足
    pub satisfiable: bool,
    /// zexecute 的返回值
    pub return_value: Option<&'a Val<B>>,
    /// 构造函数名称（如果返回值是构造函数）
    pub constructor_name: Option<&'a str>,
    /// 展开后的值表示（用于显示）
    pub unfolded_value: Option<&'a str>,
}

/// 路径约束条件
///
/// 表示在符号执行过程中，对某个符号变量施加的约束。
#[derive(Clone, Debug)]
pub struct PathConstraint {
    /// 符号变量 ID（用于追踪到寄存器）
    pub sym_id: Option<u32>,
    /// 符号变量名称（用于显示）
    pub variable: String,
    /// 约束条件（例如 "x = true" 或 "x = false"）
    pub constraint: String,
    /// 分支编号（0 表示真，1 表示假）
    pub branch_num: u32,
}

impl PathConstraint {
    /// 创建一个新的路径约束
    ///
    /// # 参数
    /// * `sym_id` - 符号变量 ID（可选）
    /// * `variable` - 符号变量名称
    /// * `constraint` - 约束条件的字符串表示
    /// * `branch_num` - 分支编号（0 表示真分支，1 表示假分支）
    pub fn new(sym_id: Option<u32>, variable: String, constraint: String, branch_num: u32) -> Self {
        PathConstraint {
            sym_id,
            variable,
            constraint,
            branch_num,
        }
    }

    /// 创建一个真值约束（变量为 true）
    ///
    /// # 参数
    /// * `sym_id` - 符号变量 ID（可选）
    /// * `variable` - 符号变量名称
    pub fn true_constraint(sym_id: Option<u32>, variable: String) -> Self {
        PathConstraint {
            sym_id,
            variable,
            constraint: "true".to_string(),
            branch_num: 0,
        }
    }

    /// 创建一个假值约束（变量为 false）
    ///
    /// # 参数
    /// * `sym_id` - 符号变量 ID（可选）
    /// * `variable` - 符号变量名称
    pub fn false_constraint(sym_id: Option<u32>, variable: String) -> Self {
        PathConstraint {
            sym_id,
            variable,
            constraint: "false".to_string(),
            branch_num: 1,
        }
    }

    /// 判断是否为真分支
    pub fn is_true_branch(&self) -> bool {
        self.branch_num == 0
    }

    /// 判断是否为假分支
    pub fn is_false_branch(&self) -> bool {
        self.branch_num == 1
    }

    /// 获取分支方向的描述
    pub fn branch_direction(&self) -> &str {
        if self.is_true_branch() {
            "真"
        } else {
            "假"
        }
    }

    /// 格式化约束为可读字符串
    pub fn format(&self) -> String {
        format!("{} = {}", self.variable, self.constraint)
    }
}

/// 符号执行结果（包含执行图）
///
/// 封装了符号执行的完整结果，包括执行图、路径统计和叶子节点信息。
pub struct ExecutionResult<B> {
    /// 执行图
    pub graph: ExecutionGraph<B>,
    /// 探索的执行路径数量
    pub num_paths: usize,
    /// 所有叶子节点（执行终点）的信息
    pub leaves: Vec<LeafInfo<B>>,
}

impl<B: std::fmt::Debug> std::fmt::Debug for ExecutionResult<B>
where
    NodeType<B>: Clone,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExecutionResult")
            .field("num_paths", &self.num_paths)
            .field("leaf_count", &self.leaves.len())
            .field("graph_depth", &self.graph.max_depth())
            .finish()
    }
}

/// 叶子节点信息
///
/// 记录执行路径终点的相关信息。
#[derive(Clone, Debug)]
pub struct LeafInfo<B> {
    /// 通往此叶子节点的路径（节点索引列表）
    pub path: Vec<NodeIndex>,
    /// 是否可满足
    pub satisfiable: bool,
    /// 返回值
    pub return_value: Option<Val<B>>,
    /// 路径上的约束条件（符号变量）
    pub constraints: Vec<PathConstraint>,
    /// 寄存器约束条件（寄存器名到值的映射）
    pub register_constraints: std::collections::HashMap<String, bool>,
}

/// 路径约束的详细信息
///
/// 记录从符号变量到具体约束的映射关系。
#[derive(Clone, Debug)]
pub struct PathConstraintDetail {
    /// 符号变量
    pub symbol: Sym,
    /// 约束值（true/false）
    pub value: bool,
    /// 源代码位置
    pub location: String,
    /// 分支 ID
    pub fork_id: u32,
}

/// 符号执行指令并收集执行图
///
/// 返回显示所有探索分支的执行图。
pub fn execute_instruction_tree<B: BV>(
    instruction_name: &str,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Result<ExecutionResult<B>, ExecError> {
    // 查找指令函数（zexecute 函数分派到指令处理器）
    let zexecute_id = shared_state.symtab.lookup("zexecute");

    // 通过调用构造函数创建指令值
    let encoded_name = format!("z{}", instruction_name);
    let ctor_id = shared_state.symtab.lookup(&encoded_name);

    // 获取构造函数类型并创建默认参数
    let instruction_value = if let Some(union_members) = shared_state.type_info.unions.get(&shared_state.symtab.lookup("zinstruction")) {
        if let Some((_, ctor_ty)) = union_members.iter().find(|(n, _)| *n == ctor_id) {
            let arg_value = generate_default_value(ctor_ty, shared_state);
            Val::Ctor(ctor_id, Box::new(arg_value))
        } else {
            return Err(ExecError::Unreachable(format!("指令 '{}' 在 zinstruction union 中未找到", instruction_name)));
        }
    } else {
        return Err(ExecError::Unreachable("zinstruction union 未找到".to_string()));
    };

    // 获取 zexecute 函数
    let (func_args, ret_ty, instrs) = shared_state.functions.get(&zexecute_id)
        .ok_or_else(|| ExecError::Unreachable("zexecute 函数未找到".to_string()))?;

    // 为 zexecute 创建初始帧
    let mut initial_frame = LocalFrame::new(zexecute_id, func_args, ret_ty, Some(&[instruction_value]), instrs);
    initial_frame.add_regs(regs);
    initial_frame.add_lets(lets);

    // 创建任务
    let task_state = TaskState::new();
    let task_id = TaskId::fresh();
    let task = initial_frame.task(task_id, &task_state);

    // 创建执行图
    let graph = Arc::new(Mutex::new(ExecutionGraph::new(NodeType::Root {
        instruction: instruction_name.to_string(),
    })));

    // 使用 Arc<Mutex<>> 包装结果以便在闭包中共享
    let result = Arc::new(Mutex::new(ExecutionResult {
        graph: ExecutionGraph::new(NodeType::Root {
            instruction: instruction_name.to_string(),
        }),
        num_paths: 0,
        leaves: Vec::new(),
    }));
    let current_path = Arc::new(Mutex::new(Vec::new()));
    let current_constraints = Arc::new(Mutex::new(Vec::new()));
    let sym_to_reg = Arc::new(Mutex::new(std::collections::HashMap::<u32, String>::new()));
    let sym_dependencies = Arc::new(Mutex::new(std::collections::HashMap::<u32, Vec<u32>>::new()));
    let sym_to_value = Arc::new(Mutex::new(std::collections::HashMap::<u32, bool>::new()));
    let sym_names = Arc::new(Mutex::new(std::collections::HashMap::<u32, String>::new()));

    // 使用自定义收集器执行
    let collected: Vec<Val<B>> = Vec::new();
    let collected = Arc::new(collected);

    // 克隆 Arc 以便在闭包中使用
    let result_clone = Arc::clone(&result);
    let current_path_clone = Arc::clone(&current_path);
    let current_constraints_clone = Arc::clone(&current_constraints);
    let sym_to_reg_clone = Arc::clone(&sym_to_reg);
    let sym_dependencies_clone = Arc::clone(&sym_dependencies);
    let sym_to_value_clone = Arc::clone(&sym_to_value);
    let sym_names_clone = Arc::clone(&sym_names);
    let graph_clone = Arc::clone(&graph);

    let collector = move |_thread: usize, _task_id: TaskId, exec_result: Result<(Run<B>, LocalFrame<B>), (ExecError, Vec<(Name, usize)>)>, shared_state: &SharedState<B>, solver: Solver<B>, _collected: &Arc<Vec<Val<B>>>| {
        match exec_result {
            Ok((run, _frame)) => {
                // 从求解器跟踪中提取事件以构建图
                let events = solver.trace().to_vec();

                let mut result_guard = result_clone.lock().unwrap();
                let mut graph_guard = graph_clone.lock().unwrap();
                let mut path_guard = current_path_clone.lock().unwrap();
                let mut constraints_guard = current_constraints_clone.lock().unwrap();
                let mut sym_to_reg_guard = sym_to_reg_clone.lock().unwrap();
                let mut sym_dependencies_guard = sym_dependencies_clone.lock().unwrap();
                let mut sym_to_value_guard = sym_to_value_clone.lock().unwrap();
                let mut sym_names_guard = sym_names_clone.lock().unwrap();

                // 第一遍：处理所有事件以建立符号变量依赖图
                for event in &events {
                    match event {
                        Event::ReadReg(reg_name, _accessor, value) => {
                            // 追踪从寄存器读取的符号变量
                            if let Val::Symbolic(sym) = value {
                                let reg_str = shared_state.symtab.to_str(*reg_name).to_string();
                                sym_to_reg_guard.insert(sym.id, reg_str);
                            }
                        }
                        Event::Smt(def, _attrs, _loc) => {
                            // 解析 SMT 定义以建立符号变量依赖
                            use crate::smt::smtlib::{Def, Exp};
                            match def {
                                Def::DefineConst(sym, exp) => {
                                    // 记录符号变量依赖
                                    let mut deps = Vec::new();
                                    extract_exp_dependencies(exp, &mut deps);
                                    sym_dependencies_guard.insert(sym.id, deps);

                                    // 检查是否是简单的布尔常量
                                    if let Exp::Bool(b) = exp {
                                        sym_to_value_guard.insert(sym.id, *b);
                                    } else if let Exp::Not(e) = exp {
                                        // 处理 Not 表达式
                                        if let Exp::Var(v) = &**e {
                                            // sym = Not(v)，所以 sym=true 当 v=false
                                            sym_to_value_guard.insert(v.id, false);
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                        _ => {}
                    }
                }

                // 为符号变量生成有意义的名称
                for event in &events {
                    match event {
                        Event::ReadReg(reg_name, _accessor, value) => {
                            if let Val::Symbolic(sym) = value {
                                let reg_str = shared_state.symtab.to_str(*reg_name).to_string();
                                // 如果还没有名称，使用寄存器名称
                                sym_names_guard.entry(sym.id).or_insert_with(|| reg_str.clone());
                            }
                        }
                        _ => {}
                    }
                }

                // 迭代地为依赖链中的所有符号变量生成名称
                // 因为可能有多个层次的依赖，需要多次迭代才能传播完整
                let mut changed = true;
                let mut max_iterations = 10; // 防止无限循环
                while changed && max_iterations > 0 {
                    changed = false;
                    max_iterations -= 1;

                    for (sym_id, deps) in sym_dependencies_guard.iter() {
                        // 如果这个符号变量已经有名称，跳过
                        if sym_names_guard.contains_key(sym_id) {
                            continue;
                        }

                        // 如果这个符号变量依赖另一个符号变量
                        if deps.len() == 1 {
                            let dep_id = deps[0];
                            // 如果依赖的符号变量有名称（通常是寄存器），则使用该名称
                            if let Some(dep_name) = sym_names_guard.get(&dep_id).cloned() {
                                sym_names_guard.insert(*sym_id, dep_name);
                                changed = true;
                            }
                        }
                    }
                }

                // 第二遍：处理事件以构建图结构
                for event in events {
                    match event {
                        Event::AssumeReg(reg_name, _accessor, value) => {
                            // 追踪符号变量到寄存器的映射
                            let mut found_syms = Vec::new();
                            extract_symbolic_from_val(&value, &mut found_syms);
                            for sym in found_syms {
                                let reg_str = shared_state.symtab.to_str(*reg_name).to_string();
                                sym_to_reg_guard.insert(sym.id, reg_str);
                            }
                        }
                        Event::Fork(fork_id, sym, branch_num, loc) => {
                            // 尝试使用符号变量的有意义名称，否则使用 ID
                            let var_name = sym_names_guard.get(&sym.id)
                                .cloned()
                                .unwrap_or_else(|| sym.to_string());
                            let location = loc.location_string(shared_state.symtab.files());

                            // 创建路径约束
                            let constraint = PathConstraint::new(
                                Some(sym.id),
                                var_name.clone(),
                                if *branch_num == 0 { "true" } else { "false" }.to_string(),
                                *branch_num,
                            );

                            // 记录约束
                            constraints_guard.push(constraint.clone());

                            // 创建分支节点
                            let branch_node = graph_guard.add_node(
                                NodeType::Branch {
                                    fork_id: *fork_id,
                                    variable: var_name.clone(),
                                    location: location.clone(),
                                },
                            );

                            // 连接到路径中的最后一个节点
                            let parent = if !path_guard.is_empty() {
                                *path_guard.last().unwrap()
                            } else {
                                graph_guard.root
                            };

                            // 添加带条件的边
                            graph_guard.add_edge(
                                parent,
                                branch_node,
                                EdgeData::Conditional { branch_num: *branch_num },
                            );

                            // 跟踪当前路径
                            path_guard.push(branch_node);
                        }
                        _ => {}
                    }
                }

                match run {
                    Run::Finished(ret_val) => {
                        result_guard.num_paths += 1;

                        // 如果返回值是 Ctor，提取构造函数名称
                        let constructor_name = if let Val::Ctor(name, _) = &ret_val {
                            Some(shared_state.symtab.to_str(*name).to_string())
                        } else {
                            None
                        };

                        // 展开返回值以便更好地显示
                        let unfolded_value = Some(unfold_return_value(&ret_val, shared_state, regs, lets).0);

                        // 创建叶子节点
                        let leaf_node = graph_guard.add_node(
                            NodeType::Leaf {
                                satisfiable: true,
                                return_value: Some(ret_val.clone()),
                                constructor_name: constructor_name.clone(),
                                unfolded_value,
                            },
                        );

                        // 连接到路径中的最后一个节点
                        let parent = if !path_guard.is_empty() {
                            *path_guard.last().unwrap()
                        } else {
                            graph_guard.root
                        };

                        graph_guard.add_edge(parent, leaf_node, EdgeData::Unconditional);

                        // 将符号变量约束转换为寄存器约束
                        // 需要通过依赖链追踪符号变量到寄存器
                        let mut register_constraints = std::collections::HashMap::new();
                        for constraint in constraints_guard.iter() {
                            if let Some(sym_id) = constraint.sym_id {
                                // 递归追踪符号变量到寄存器
                                let constraint_value = constraint.is_true_branch();
                                trace_symbol_to_register(
                                    sym_id,
                                    constraint_value,
                                    &sym_to_reg_guard,
                                    &sym_dependencies_guard,
                                    &sym_to_value_guard,
                                    &mut register_constraints,
                                );
                            }
                        }

                        // 记录叶子信息（包含完整路径和约束）
                        let mut full_path = path_guard.clone();
                        full_path.push(leaf_node);
                        result_guard.leaves.push(LeafInfo {
                            path: full_path,
                            satisfiable: true,
                            return_value: Some(ret_val.clone()),
                            constraints: constraints_guard.clone(),
                            register_constraints,
                        });

                        path_guard.clear();
                        constraints_guard.clear();
                        sym_to_reg_guard.clear();
                    }
                    Run::Dead => {
                        // 路径不可满足
                        result_guard.num_paths += 1;

                        // 创建不可满足的叶子节点
                        let leaf_node = graph_guard.add_node(
                            NodeType::Leaf {
                                satisfiable: false,
                                return_value: None,
                                constructor_name: None,
                                unfolded_value: None,
                            },
                        );

                        // 连接到路径中的最后一个节点
                        let parent = if !path_guard.is_empty() {
                            *path_guard.last().unwrap()
                        } else {
                            graph_guard.root
                        };

                        graph_guard.add_edge(parent, leaf_node, EdgeData::Unconditional);

                        // 将符号变量约束转换为寄存器约束
                        // 需要通过依赖链追踪符号变量到寄存器
                        let mut register_constraints = std::collections::HashMap::new();
                        for constraint in constraints_guard.iter() {
                            if let Some(sym_id) = constraint.sym_id {
                                // 递归追踪符号变量到寄存器
                                let constraint_value = constraint.is_true_branch();
                                trace_symbol_to_register(
                                    sym_id,
                                    constraint_value,
                                    &sym_to_reg_guard,
                                    &sym_dependencies_guard,
                                    &sym_to_value_guard,
                                    &mut register_constraints,
                                );
                            }
                        }

                        // 记录叶子信息（包含完整路径和约束）
                        let mut full_path = path_guard.clone();
                        full_path.push(leaf_node);
                        result_guard.leaves.push(LeafInfo {
                            path: full_path,
                            satisfiable: false,
                            return_value: None,
                            constraints: constraints_guard.clone(),
                            register_constraints,
                        });

                        path_guard.clear();
                        constraints_guard.clear();
                        sym_to_reg_guard.clear();
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

    // 返回结果的克隆版本
    let result_guard = result.lock().unwrap();
    let graph_guard = graph.lock().unwrap();

    // 克隆执行图（由于 ExecutionGraph 现在包含 Graph，我们需要手动克隆）
    // Graph 不实现 Clone，所以我们创建一个新的 ExecutionGraph
    // 这里简化处理：直接使用 Arc 中的图
    Ok(ExecutionResult {
        graph: ExecutionGraph {
            graph: graph_guard.graph.clone(),
            root: graph_guard.root,
        },
        num_paths: result_guard.num_paths,
        leaves: result_guard.leaves.clone(),
    })
}

/// Unfold a return value by recursively executing constructor functions
/// Returns a string representation of the unfolded value
pub fn unfold_return_value<B: BV>(
    val: &Val<B>,
    shared_state: &SharedState<B>,
    _regs: &RegisterBindings<B>,
    _lets: &Bindings<B>,
) -> (String, Option<Val<B>>) {
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

/// 求解路径约束的结果
///
/// 表示对路径约束进行求解后的结果。
#[derive(Debug, Clone)]
pub enum ConstraintSolveResult {
    /// 可满足 - 包含变量到值的映射
    Sat {
        /// 符号变量到具体值的映射
        values: std::collections::HashMap<String, bool>,
    },
    /// 不可满足
    Unsat,
    /// 未知（求解器超时或其他错误）
    Unknown,
}

/// 求解路径的约束条件
///
/// 根据路径上的约束条件，确定变量值。
///
/// # 参数
/// * `constraints` - 路径上的约束条件列表
///
/// # 返回
/// 求解结果，包含变量的具体值（如果可满足）
pub fn solve_path_constraints<B: BV>(
    constraints: &[PathConstraint],
    _shared_state: &SharedState<B>,
) -> ConstraintSolveResult {
    use std::collections::HashMap;

    // 简单的约束求解：直接从约束中提取值
    // 注意：这是一个简化版本，实际的符号执行需要更复杂的处理
    let mut values = HashMap::new();

    for constraint in constraints {
        // 根据分支编号确定值
        let value = constraint.is_true_branch();
        values.insert(constraint.variable.clone(), value);
    }

    if values.is_empty() {
        ConstraintSolveResult::Unknown
    } else {
        ConstraintSolveResult::Sat { values }
    }
}

/// 格式化约束求解结果
///
/// 将求解结果转换为可读的字符串格式。
pub fn format_solve_result(result: &ConstraintSolveResult) -> String {
    match result {
        ConstraintSolveResult::Sat { values } => {
            let mut output = String::from("可满足:\n");
            for (var, val) in values {
                output.push_str(&format!("  {} = {}\n", var, val));
            }
            output
        }
        ConstraintSolveResult::Unsat => "不可满足".to_string(),
        ConstraintSolveResult::Unknown => "未知".to_string(),
    }
}

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

/// 将执行图格式化为 ASCII 艺术
pub fn format_tree_ascii<B: BV>(result: &ExecutionResult<B>) -> String {
    result.graph.format_ascii(result.num_paths)
}

/// 将执行图格式化为 ASCII 艺术（包含约束信息）
pub fn format_tree_ascii_with_constraints<B: BV>(result: &ExecutionResult<B>) -> String {
    let mut output = result.graph.format_ascii(result.num_paths);

    output.push_str("\n=== 路径约束信息 ===\n\n");

    for (i, leaf) in result.leaves.iter().enumerate() {
        output.push_str(&format!("路径 {}:\n", i + 1));
        output.push_str(&format!("  可满足: {}\n", leaf.satisfiable));

        // 显示寄存器约束
        if !leaf.register_constraints.is_empty() {
            output.push_str("  寄存器约束:\n");
            let mut reg_names: Vec<_> = leaf.register_constraints.keys().collect();
            reg_names.sort();
            for reg_name in reg_names {
                let value = leaf.register_constraints.get(reg_name).unwrap();
                output.push_str(&format!("    {} = {}\n", reg_name, value));
            }
        } else {
            output.push_str("  无寄存器约束\n");
        }

        // 也显示符号变量约束（用于调试）
        if !leaf.constraints.is_empty() {
            output.push_str("  符号变量约束:\n");
            for (j, constraint) in leaf.constraints.iter().enumerate() {
                output.push_str(&format!("    {}. {}\n", j + 1, constraint.format()));
            }
        }

        output.push_str("\n");
    }

    output
}

/// 将执行图格式化为 Graphviz DOT 格式
pub fn format_tree_graphviz<B: BV>(result: &ExecutionResult<B>) -> String {
    result.graph.format_graphviz()
}
