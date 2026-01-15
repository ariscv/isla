use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use isla_lib::ir::*;
use isla_lib::executor::*;
use isla_lib::executor::Backtrace;
use isla_lib::smt::{Event, Sym};
use isla_lib::smt::smtlib::Exp as SmtExp;
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
    pub constraint: SmtExp<Sym>,     // SMT 约束（简化表示）
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

    // 打印 CFG 树（树状图格式）
    pub fn print(&self, shared_state: &SharedState<B>) {
        println!("╔═══════════════════════════════════════════════════════════════╗");
        println!("║                   Control Flow Tree (树状图)                  ║");
        println!("╚═══════════════════════════════════════════════════════════════╝");
        println!();

        // 统计信息
        println!("📊 Statistics:");
        println!("   • Entry point: PC {}", self.entry_point);
        println!("   • Total nodes: {}", self.nodes.len());
        println!("   • Total edges: {}", self.edges.len());
        println!();

        // 构建从根开始的树结构
        // 找到根路径（没有父路径的路径）
        let mut path_to_parent: HashMap<TaskId, Option<TaskId>> = HashMap::new();
        for ((_pc, path_id), node) in &self.nodes {
            if !path_to_parent.contains_key(path_id) {
                path_to_parent.insert(*path_id, node.parent_path);
            }
        }

        // 找到根路径（TaskId最小的）
        let root_path = path_to_parent.iter()
            .filter(|(_, parent)| parent.is_none())
            .min_by_key(|(id, _)| id.as_usize())
            .map(|(id, _)| *id)
            .or_else(|| path_to_parent.keys().copied().min_by_key(|id| id.as_usize()));

        println!("🌲 CFG Tree Structure:");
        println!();

        if let Some(root) = root_path {
            self.print_tree_recursive(root, "", shared_state, &mut HashSet::new());
        } else {
            // 如果没有明确的根，直接打印所有路径
            let mut all_path_ids: Vec<TaskId> = self.nodes.values()
                .map(|n| n.path_id)
                .collect::<HashSet<_>>()
                .into_iter()
                .collect();
            all_path_ids.sort_by_key(|id| id.as_usize());
            for path_id in all_path_ids {
                self.print_tree_recursive(path_id, "", shared_state, &mut HashSet::new());
            }
        }
    }

    // 递归打印树状结构
    fn print_tree_recursive(&self, path_id: TaskId, prefix: &str, shared_state: &SharedState<B>, printed: &mut HashSet<TaskId>) {
        // 防止重复打印
        if !printed.insert(path_id) {
            return;
        }

        // 收集该路径的所有节点
        let nodes: Vec<&CFGNode<B>> = self.nodes.values()
            .filter(|n| n.path_id == path_id)
            .collect();

        if nodes.is_empty() {
            return;
        }

        // 按执行顺序反向排序（从入口到出口）
        let mut sorted_nodes: Vec<_> = nodes.iter().collect();
        sorted_nodes.sort_by_key(|n| n.execution_order);
        sorted_nodes.reverse(); // 反转，使入口在顶部

        // 打印该路径的节点
        for (idx, node) in sorted_nodes.iter().enumerate() {
            let is_last = idx == sorted_nodes.len() - 1;
            let (line_prefix, child_prefix) = if is_last {
                ("└── ", format!("{}    ", prefix))
            } else {
                ("├── ", format!("{}│   ", prefix))
            };

            // 打印分支条件
            if let Some(fc) = &node.fork_condition {
                let branch_symbol = match fc.branch {
                    ForkBranch::True => "✓ TRUE",
                    ForkBranch::False => "✗ FALSE",
                };
                let condition_str = self.format_smt_condition(&fc.constraint);
                println!("{}{}{} [{}] v{}", prefix, line_prefix, branch_symbol, condition_str, fc.symbolic_var);
            } else {
                println!("{}{}PC {}", prefix, line_prefix, node.pc);
            }

            // 打印指令内容（带缩进）
            let instr_str = self.instr_to_string(&node.instr, shared_state);
            for line in instr_str.lines() {
                println!("{}{}    {}", child_prefix, line_prefix, line);
            }
        }

        // 递归打印子路径
        if let Some(children) = self.path_tree.get(&path_id) {
            let mut sorted_children: Vec<_> = children.iter().collect();
            sorted_children.sort_by_key(|id| id.as_usize());

            for (idx, &child_path) in sorted_children.iter().enumerate() {
                let is_last = idx == sorted_children.len() - 1;
                let new_prefix = if is_last {
                    format!("{}    ", prefix)
                } else {
                    format!("{}│   ", prefix)
                };

                // 打印子路径标题
                println!("{}{}┌── Path {} (子路径)", prefix, if is_last { " " } else { "│" }, child_path.as_usize());

                self.print_tree_recursive(*child_path, &new_prefix, shared_state, printed);

                // 打印子路径结束标记
                if idx < sorted_children.len() - 1 {
                    println!("{}{}│", prefix, if is_last { " " } else { "│" });
                }
            }
        }
    }

    // 将指令转换为多行字符串
    fn instr_to_string(&self, instr: &Instr<Name, B>, shared_state: &SharedState<B>) -> String {
        match instr {
            Instr::Init(var, _ty, exp, _info) => {
                format!("{} = {}", shared_state.symtab.to_str(*var), self.exp_to_string(exp, shared_state))
            }
            Instr::Copy(loc, exp, _info) => {
                format!("{} = {}", self.loc_to_string(loc, shared_state), self.exp_to_string(exp, shared_state))
            }
            Instr::Jump(exp, target, _info) => {
                format!("jump if {} -> PC {}", self.exp_to_string(exp, shared_state), target)
            }
            Instr::Goto(target) => {
                format!("goto -> PC {}", target)
            }
            Instr::Call(_loc, _ext, name, args, _info) => {
                let args_str: Vec<String> = args.iter()
                    .map(|a| self.exp_to_string(a, shared_state))
                    .collect();
                format!("call {}({})", shared_state.symtab.to_str(*name), args_str.join(", "))
            }
            Instr::End => {
                "end".to_string()
            }
            Instr::Decl(var, ty, _info) => {
                format!("decl {}: {:?}", shared_state.symtab.to_str(*var), ty)
            }
            Instr::Exit(cause, _info) => {
                format!("exit {:?}", cause)
            }
            Instr::Arbitrary => {
                "arbitrary".to_string()
            }
            _ => {
                format!("{:?}", instr)
            }
        }
    }

    // 将 Op 转换为字符串
    fn op_to_string(op: &Op) -> String {
        match op {
            Op::Not => "not".to_string(),
            Op::Or => "or".to_string(),
            Op::And => "and".to_string(),
            Op::Eq => "==".to_string(),
            Op::Neq => "!=".to_string(),
            Op::Lteq => "<=".to_string(),
            Op::Lt => "<".to_string(),
            Op::Gteq => ">=".to_string(),
            Op::Gt => ">".to_string(),
            Op::Add => "+".to_string(),
            Op::Sub => "-".to_string(),
            Op::Slice(n) => format!("slice[{}]", n),
            Op::SetSlice => "set_slice".to_string(),
            Op::Signed(n) => format!("signed[{}]", n),
            Op::Unsigned(n) => format!("unsigned[{}]", n),
            Op::ZeroExtend(n) => format!("zext[{}]", n),
            Op::Bvnot => "bvnot".to_string(),
            Op::Bvor => "bvor".to_string(),
            Op::Bvxor => "bvxor".to_string(),
            Op::Bvand => "bvand".to_string(),
            Op::Bvadd => "bvadd".to_string(),
            Op::Bvsub => "bvsub".to_string(),
            Op::Bvaccess => "bvaccess".to_string(),
            Op::Concat => "++".to_string(),
            Op::Head => "head".to_string(),
            Op::Tail => "tail".to_string(),
            Op::IsEmpty => "is_empty".to_string(),
        }
    }

    // 将表达式转换为字符串
    fn exp_to_string(&self, exp: &Exp<Name>, shared_state: &SharedState<B>) -> String {
        match exp {
            Exp::Id(name) => shared_state.symtab.to_str(*name).to_string(),
            Exp::Ref(name) => format!("&{}", shared_state.symtab.to_str(*name)),
            Exp::Bool(b) => format!("{}", b),
            Exp::Bits(bv) => format!("{}", bv),
            Exp::String(s) => format!("\"{}\"", s),
            Exp::Unit => "()".to_string(),
            Exp::I64(i) => format!("{}", i),
            Exp::I128(i) => format!("{}", i),
            Exp::Undefined(_ty) => "undefined".to_string(),
            Exp::Call(op, args) => {
                let op_str = Self::op_to_string(op);
                let args_str: Vec<String> = args.iter()
                    .map(|a| self.exp_to_string(a, shared_state))
                    .collect();
                match args.len() {
                    0 => op_str,
                    1 => format!("{}({})", op_str, args_str.join(", ")),
                    2 => {
                        // 对于二元操作，使用中缀表示法
                        format!("({} {} {})", args_str[0], op_str, args_str[1])
                    }
                    _ => format!("{}({})", op_str, args_str.join(", ")),
                }
            }
            Exp::Struct(name, fields) => {
                let struct_name = shared_state.symtab.to_str(*name);
                let fields_str: Vec<String> = fields.iter()
                    .map(|(f, e)| format!("{}: {}", shared_state.symtab.to_str(*f), self.exp_to_string(e, shared_state)))
                    .collect();
                format!("{}.struct({{{})}}", struct_name, fields_str.join(", "))
            }
            Exp::Kind(name, exp) => {
                format!("{}({})", shared_state.symtab.to_str(*name), self.exp_to_string(exp, shared_state))
            }
            Exp::Unwrap(name, exp) => {
                format!("unwrap({}, {})", shared_state.symtab.to_str(*name), self.exp_to_string(exp, shared_state))
            }
            Exp::Field(exp, name) => {
                format!("{}.{}", self.exp_to_string(exp, shared_state), shared_state.symtab.to_str(*name))
            }
        }
    }

    // 将位置转换为字符串
    fn loc_to_string(&self, loc: &Loc<Name>, shared_state: &SharedState<B>) -> String {
        match loc {
            Loc::Id(name) => shared_state.symtab.to_str(*name).to_string(),
            Loc::Field(loc, field) => format!("{}.{}", self.loc_to_string(loc, shared_state), shared_state.symtab.to_str(*field)),
            Loc::Addr(loc) => format!("&{}", self.loc_to_string(loc, shared_state)),
        }
    }

    // 格式化 SMT 表达式条件
    fn format_smt_condition(&self, exp: &SmtExp<Sym>) -> String {
        match exp {
            SmtExp::Var(sym) => format!("v{}", sym),
            SmtExp::Not(boxed) => match boxed.as_ref() {
                SmtExp::Var(sym) => format!("!v{}", sym),
                _ => format!("!({:?})", boxed),
            },
            _ => format!("{:?}", exp),
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
                        constraint: SmtExp::Var(*sym), // 简化：实际应该从solver获取完整约束
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
                        constraint: SmtExp::Var(*sym),
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

    eprintln!("使用 start_single 进行符号执行（单线程）");

    // 暂时使用 start_single，因为 start_multi 存在 bug：
    // 分叉任务使用相同的 task_id，导致 Fraction 永远不会达到 1，造成无限循环
    start_single(
        task,
        shared_state,
        &executor_clone,
        &move |_tid, task_id, result, _shared_state, solver, executor| {
            // 从solver中提取所有事件（trace().to_vec()返回Vec<&Event<B>>，需要克隆）
            let mut events_vec = solver.trace().to_vec();
            let events: Vec<Event<B>> = events_vec.drain(..).cloned().collect();

            // 创建路径结果数据（需要立即提取数据以避免生命周期问题）
            let path_data = match result {
                Ok((_run_result, frame)) => {
                    // 使用公共访问器方法获取backtrace和pc
                    let backtrace = frame.backtrace().clone();
                    let final_pc = frame.pc();
                    PathResultData {
                        task_id,
                        run_result: Run::Finished(Val::Unit), // 占位值
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
            let path_count = exec.path_infos.len();
            exec.process_path(&path_data);

            // 每10条路径打印一次进度
            if path_count > 0 && path_count % 10 == 0 {
                eprintln!("已处理 {} 条路径", path_count);
            }
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