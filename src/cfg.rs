use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use isla_lib::ir::*;
use isla_lib::executor::*;
use isla_lib::executor::Backtrace;
use isla_lib::smt::{Event, Sym};
use isla_lib::smt::smtlib::Exp;
use isla_lib::bitvector::BV;


// CFG 节点：代表一个指令执行点
#[derive(Debug, Clone)]
pub struct CFGNode<B: BV> {
    pub pc: usize,                    // 指令索引
    pub instr: Instr<Name, B>,        // 指令内容
    pub path_id: TaskId,              // 路径标识
    pub parent_path: Option<TaskId>,  // 父路径（用于构建树）
    pub fork_condition: Option<ForkCondition>, // 分叉条件
    pub execution_order: usize,       // 在路径中的执行顺序
}

// 分叉条件
#[derive(Debug, Clone)]
pub struct ForkCondition {
    pub symbolic_var: Sym,           // 符号变量
    pub branch: ForkBranch,          // 分支（true/false）
    pub constraint: Exp<Sym>,         // SMT 约束（简化表示）
}

#[derive(Debug, Clone)]
pub enum ForkBranch {
    True,
    False,
}

// CFG 边：代表控制流转移
#[derive(Debug, Clone)]
pub struct CFGEdge {
    pub from: usize,                 // 源节点 PC
    pub to: usize,                   // 目标节点 PC
    pub from_path: TaskId,           // 源路径标识
    pub to_path: TaskId,             // 目标路径标识
    pub condition: Option<ForkCondition>, // 条件（如果是条件跳转）
}

// CFG 树：整个函数的控制流图
#[derive(Clone)]
pub struct CFGTree<B: BV> {
    pub nodes: HashMap<(usize, TaskId), CFGNode<B>>,  // (pc, path_id) -> Node
    pub edges: Vec<CFGEdge>,
    pub entry_point: usize,           // 入口 PC
    pub path_tree: HashMap<TaskId, Vec<TaskId>>,  // 路径树：path_id -> 子路径列表
    pub instructions: Vec<Instr<Name, B>>,  // 所有指令（用于索引）
}

impl<B: BV> CFGTree<B> {
    pub fn new(entry_point: usize, instructions: &[Instr<Name, B>]) -> Self {
        CFGTree {
            nodes: HashMap::new(),
            edges: Vec::new(),
            entry_point,
            path_tree: HashMap::new(),
            instructions: instructions.to_vec(),
        }
    }

    // 添加节点
    pub fn add_node(&mut self, pc: usize, path_id: TaskId, parent_path: Option<TaskId>, 
                    fork_condition: Option<ForkCondition>, execution_order: usize) {
        if pc < self.instructions.len() {
            let instr = self.instructions[pc].clone();
            let node = CFGNode {
                pc,
                instr,
                path_id,
                parent_path,
                fork_condition: fork_condition.clone(),
                execution_order,
            };
            self.nodes.insert((pc, path_id), node);
            
            // 更新路径树
            if let Some(parent) = parent_path {
                self.path_tree.entry(parent).or_insert_with(Vec::new).push(path_id);
            }
        }
    }

    // 添加边
    pub fn add_edge(&mut self, from: usize, to: usize, from_path: TaskId, to_path: TaskId, 
                    condition: Option<ForkCondition>) {
        self.edges.push(CFGEdge {
            from,
            to,
            from_path,
            to_path,
            condition,
        });
    }

    // 打印 CFG 树
    pub fn print(&self, _shared_state: &SharedState<B>) {
        println!("=== CFG Tree ===");
        println!("Entry point: PC={}", self.entry_point);
        println!("Total nodes: {}", self.nodes.len());
        println!("Total edges: {}", self.edges.len());
        println!();

        // 按路径组织节点
        let mut paths: HashMap<TaskId, Vec<((usize, TaskId), usize)>> = HashMap::new();
        for ((pc, path_id), node) in &self.nodes {
            paths.entry(*path_id).or_insert_with(Vec::new).push(((*pc, *path_id), node.execution_order));
        }

        // 按执行顺序排序每个路径的节点
        for (_, nodes) in &mut paths {
            nodes.sort_by_key(|(_, order)| *order);
        }

        // 打印每个路径
        for (path_id, nodes) in paths.iter() {
            println!("Path {}: ", path_id.as_usize());
            for ((pc, _), _) in nodes {
                if *pc < self.instructions.len() {
                    let node = &self.nodes.get(&(*pc, *path_id)).unwrap();
                    print!("  PC {} (order {}): ", pc, node.execution_order);
                    match &node.fork_condition {
                        Some(fc) => {
                            match fc.branch {
                                ForkBranch::True => print!("[TRUE] "),
                                ForkBranch::False => print!("[FALSE] "),
                            }
                        }
                        None => {}
                    }
                    println!("{:?}", &node.instr);
                }
            }
            println!();
        }

        // 打印边
        println!("Edges:");
        for edge in &self.edges {
            match &edge.condition {
                Some(fc) => {
                    match fc.branch {
                        ForkBranch::True => println!("  PC {} [Path {}] --[TRUE]--> PC {} [Path {}]", 
                                                     edge.from, edge.from_path.as_usize(), 
                                                     edge.to, edge.to_path.as_usize()),
                        ForkBranch::False => println!("  PC {} [Path {}] --[FALSE]--> PC {} [Path {}]", 
                                                      edge.from, edge.from_path.as_usize(), 
                                                      edge.to, edge.to_path.as_usize()),
                    }
                }
                None => println!("  PC {} [Path {}] --> PC {} [Path {}]", 
                                edge.from, edge.from_path.as_usize(), 
                                edge.to, edge.to_path.as_usize()),
            }
        }
    }
}

// 路径执行结果数据结构
struct PathResultData<B: BV> {
    task_id: TaskId,
    run_result: Run<B>,
    events: Vec<Event<B>>,
    backtrace: Vec<(Name, usize)>,  // 函数名和PC的序列
    final_pc: usize,
}

// 路径信息：用于跟踪执行路径和分叉关系
struct PathInfo {
    task_id: TaskId,
    executed_pcs: Vec<usize>,      // 按执行顺序的PC序列（包含重复，因为可能循环）
    fork_events: Vec<(usize, Sym, ForkBranch)>, // (pc位置, 符号变量, 分支)
    parent_path: Option<TaskId>,
}

// 符号执行引擎
pub struct SymbolicExecutor<B: BV> {
    pub cfg_tree: CFGTree<B>,
    path_infos: HashMap<TaskId, PathInfo>,
}

impl<B: BV> SymbolicExecutor<B> {
    pub fn new(instructions: &[Instr<Name, B>]) -> Self {
        SymbolicExecutor {
            cfg_tree: CFGTree::new(0, instructions),
            path_infos: HashMap::new(),
        }
    }

    // 处理路径执行结果
    pub fn process_path(&mut self, path_data: &PathResultData<B>) {
        // 提取所有执行的PC（保持顺序，包括重复）
        let mut executed_pcs: Vec<usize> = Vec::new();
        for (_name, pc) in &path_data.backtrace {
            executed_pcs.push(*pc);
        }
        // 添加最终PC（如果还在范围内）
        if path_data.final_pc < self.cfg_tree.instructions.len() {
            executed_pcs.push(path_data.final_pc);
        }

        // 从events中提取Fork信息，并关联到对应的PC
        // 注意：Fork事件通常发生在条件分支处
        let mut fork_events: Vec<(usize, Sym, ForkBranch)> = Vec::new();
        let mut fork_index = 0;
        for event in &path_data.events {
            if let Event::Fork(_fork_num, sym, branch_idx, _info) = event {
                // 尝试将fork事件关联到最近的PC
                // 这是一个简化处理，实际中可能需要更精确的关联
                let associated_pc = if fork_index < executed_pcs.len() {
                    executed_pcs[fork_index.max(1) - 1] // 关联到前一个PC（分支指令）
                } else if !executed_pcs.is_empty() {
                    executed_pcs[executed_pcs.len() - 1]
                } else {
                    0
                };
                fork_events.push((
                    associated_pc,
                    *sym,
                    if *branch_idx == 0 { ForkBranch::True } else { ForkBranch::False }
                ));
                fork_index += 1;
            }
        }

        // 确定父路径：查找最长公共前缀的路径
        let mut parent_path: Option<TaskId> = None;
        let mut max_common_prefix = 0;
        for (other_id, other_info) in &self.path_infos {
            let common_prefix_len = executed_pcs.iter()
                .zip(other_info.executed_pcs.iter())
                .take_while(|(a, b)| a == b)
                .count();
            if common_prefix_len > max_common_prefix && common_prefix_len < executed_pcs.len() {
                max_common_prefix = common_prefix_len;
                parent_path = Some(*other_id);
            }
        }

        // 存储路径信息
        self.path_infos.insert(path_data.task_id, PathInfo {
            task_id: path_data.task_id,
            executed_pcs: executed_pcs.clone(),
            fork_events,
            parent_path,
        });
    }

    // 构建CFG树：为每条指令创建节点和边
    pub fn build_cfg(&mut self) {
        // 清除现有节点和边（保留指令列表）
        self.cfg_tree.nodes.clear();
        self.cfg_tree.edges.clear();
        self.cfg_tree.path_tree.clear();

        // 为每条路径处理
        for (path_id, path_info) in &self.path_infos {
            // 获取该路径的fork事件映射
            let fork_map: HashMap<usize, (Sym, ForkBranch)> = path_info.fork_events
                .iter()
                .map(|(pc, sym, branch)| (*pc, (*sym, branch.clone())))
                .collect();

            // 为路径中的每条指令创建节点
            for (execution_order, &pc) in path_info.executed_pcs.iter().enumerate() {
                if pc >= self.cfg_tree.instructions.len() {
                    continue;
                }

                // 检查这个PC是否有fork条件
                let fork_condition = fork_map.get(&pc).map(|(sym, branch)| {
                    ForkCondition {
                        symbolic_var: *sym,
                        branch: branch.clone(),
                        constraint: Exp::Var(*sym), // 简化：实际应该从solver获取完整约束
                    }
                });

                // 确定parent_path：只有在路径开始处才设置
                let parent_path = if execution_order == 0 {
                    path_info.parent_path
                } else {
                    None
                };

                self.cfg_tree.add_node(pc, *path_id, parent_path, fork_condition, execution_order);
            }

            // 为路径中的连续指令创建边
            for i in 0..path_info.executed_pcs.len().saturating_sub(1) {
                let from_pc = path_info.executed_pcs[i];
                let to_pc = path_info.executed_pcs[i + 1];
                
                if from_pc >= self.cfg_tree.instructions.len() || 
                   to_pc >= self.cfg_tree.instructions.len() {
                    continue;
                }

                // 检查from_pc是否有fork条件
                let condition = fork_map.get(&from_pc).map(|(sym, branch)| {
                    ForkCondition {
                        symbolic_var: *sym,
                        branch: branch.clone(),
                        constraint: Exp::Var(*sym),
                    }
                });

                self.cfg_tree.add_edge(from_pc, to_pc, *path_id, *path_id, condition);
            }

            // 更新路径树：建立父子关系
            if let Some(parent) = path_info.parent_path {
                self.cfg_tree.path_tree.entry(parent).or_insert_with(Vec::new).push(*path_id);
            }
        }
    }
}

// 符号执行并构建CFG的主函数
pub fn symbolic_execute_and_build_cfg<'ir, B: BV>(
    task: Task<'ir, '_, B>,
    shared_state: &'ir SharedState<B>,
    instructions: &'ir [Instr<Name, B>],
) -> CFGTree<B> {
    // 创建符号执行引擎
    let executor = Arc::new(Mutex::new(SymbolicExecutor::new(instructions)));
    let executor_clone = executor.clone();

    // 执行符号执行，使用多线程并行执行
    // 使用 num_cpus::get() 获取逻辑核心数，对于有超线程的 CPU 可以适当调整
    let num_threads = num_cpus::get(); // 获取逻辑 CPU 核心数
    eprintln!("使用 {} 个线程进行符号执行", num_threads);

    start_multi(
        num_threads,
        None, // 无超时限制
        vec![task], // 将单个 task 包装成 Vec
        shared_state,
        executor_clone, // 需要 Arc<R>，不是引用
        &move |_tid, task_id, result, _shared_state, solver, executor| {
            // 从solver中提取所有事件（trace().to_vec()返回Vec<&Event<B>>，需要克隆）
            let mut events_vec = solver.trace().to_vec();
            let events: Vec<Event<B>> = events_vec.drain(..).cloned().collect();

            // 创建路径结果数据（需要立即提取数据以避免生命周期问题）
            let path_data = match result {
                Ok((run_result, frame)) => {
                    // 使用公共访问器方法获取backtrace和pc
                    let backtrace = frame.backtrace().clone();
                    let final_pc = frame.pc();
                    PathResultData {
                        task_id,
                        run_result,
                        events,
                        backtrace,
                        final_pc,
                    }
                }
                Err((_err, backtrace)) => {
                    // 即使出错也记录，以便查看部分执行路径
                    PathResultData {
                        task_id,
                        run_result: Run::Dead,
                        events: vec![],
                        backtrace,
                        final_pc: 0,
                    }
                }
            };

            // 处理路径数据
            let mut exec = executor.lock().unwrap();
            exec.process_path(&path_data);
        },
    );

    // 构建CFG树
    let mut exec = executor.lock().unwrap();
    exec.build_cfg();
    
    // 返回CFG树（通过克隆）
    // 注意：这里我们需要实际克隆整个树，因为executor被Arc包裹
    // 为了简化，我们直接返回executor中的cfg_tree
    // 但更好的做法是让build_cfg返回CFGTree
    let cfg_tree = exec.cfg_tree.clone();
    drop(exec); // 显式释放锁
    
    cfg_tree
}