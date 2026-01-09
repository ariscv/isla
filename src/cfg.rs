

use std::collections::{HashMap, HashSet};
use isla_lib::ir::*;
use isla_lib::executor::*;
use isla_lib::smt::Event;

// CFG 节点：代表一个指令执行点
#[derive(Debug, Clone)]
struct CFGNode {
    pc: usize,                    // 指令索引
    instr: Instr<Name, B>,        // 指令内容
    path_id: TaskId,              // 路径标识
    parent_path: Option<TaskId>,  // 父路径（用于构建树）
    fork_condition: Option<ForkCondition>, // 分叉条件
    state_snapshot: Option<StateSnapshot>, // 状态快照（可选）
}

// 分叉条件
#[derive(Debug, Clone)]
struct ForkCondition {
    symbolic_var: Sym,           // 符号变量
    branch: ForkBranch,          // 分支（true/false）
    constraint: Exp<Sym>,         // SMT 约束
}

#[derive(Debug, Clone)]
enum ForkBranch {
    True,
    False,
}

// CFG 边：代表控制流转移
#[derive(Debug, Clone)]
struct CFGEdge {
    from: usize,                 // 源节点 PC
    to: usize,                   // 目标节点 PC
    path_id: TaskId,             // 路径标识
    condition: Option<ForkCondition>, // 条件（如果是条件跳转）
}

// CFG 树：整个函数的控制流图
struct CFGTree {
    nodes: HashMap<(usize, TaskId), CFGNode>,  // (pc, path_id) -> Node
    edges: Vec<CFGEdge>,
    entry_point: usize,           // 入口 PC
    path_tree: HashMap<TaskId, Vec<TaskId>>,  // 路径树：path_id -> 子路径列表
}