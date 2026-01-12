use std::collections::{HashMap, HashSet};
use std::collections::HashSet as StdHashSet;
use isla_lib::ir::*;
use isla_lib::bitvector::BV;
use isla_lib::primop;

/// 符号变量映射：IR 变量 -> 符号表达式
#[derive(Debug, Clone)]
pub struct SymbolicMapping {
    /// IR 变量名到符号表达式的映射
    pub var_to_exp: HashMap<Name, String>,
    /// 变量定义映射：记录每个变量是如何定义的
    pub definitions: HashMap<Name, DefInfo>,
    /// IR 定义的函数集合（不是 primop）
    ir_functions: StdHashSet<String>,
    /// 函数调用映射：函数名 -> (形参列表, 返回值变量, 函数体指令)
    function_bodies: HashMap<String, (Vec<Name>, Name, Vec<Instr<Name, ()>>)>,
}

impl SymbolicMapping {
    pub fn new() -> Self {
        SymbolicMapping {
            var_to_exp: HashMap::new(),
            definitions: HashMap::new(),
            ir_functions: StdHashSet::new(),
            function_bodies: HashMap::new(),
        }
    }

    /// 添加 IR 定义的函数
    pub fn add_ir_function(&mut self, func_name: String, params: Vec<Name>, return_var: Name, body: Vec<Instr<Name, ()>>) {
        self.ir_functions.insert(func_name.clone());
        self.function_bodies.insert(func_name, (params, return_var, body));
    }

    /// 检查是否是 IR 定义的函数（不是 primop）
    pub fn is_ir_function(&self, func_name: &str) -> bool {
        self.ir_functions.contains(func_name)
    }

    /// 获取函数体
    pub fn get_function_body(&self, func_name: &str) -> Option<&(Vec<Name>, Name, Vec<Instr<Name, ()>>)> {
        self.function_bodies.get(func_name)
    }
}

/// 变量定义信息
#[derive(Debug, Clone)]
pub enum DefInfo {
    /// 从符号变量定义
    FromSymbolic(String),
    /// 从另一个 IR 变量定义（别名）
    FromAlias(Name),
    /// 从操作定义（需要分析操作数）
    FromOp(String, Vec<Name>),
    /// 从函数调用定义（函数名，参数变量列表）
    FromCall(String, Vec<Name>),
    /// 未定义
    Unknown,
}

impl SymbolicMapping {
    /// 添加映射：IR 变量 -> 符号表达式
    pub fn add_mapping(&mut self, ir_var: Name, symbolic_expr: String) {
        self.var_to_exp.insert(ir_var, symbolic_expr);
    }

    /// 添加定义信息
    pub fn add_definition(&mut self, var: Name, info: DefInfo) {
        self.definitions.insert(var, info);
    }

    /// 获取变量的符号表达式，递归解析别名链
    pub fn get_symbolic(&self, ir_var: Name) -> Option<String> {
        if let Some(expr) = self.var_to_exp.get(&ir_var) {
            Some(expr.clone())
        } else {
            // 尝试通过定义信息递归解析
            self.resolve_symbolic(ir_var)
        }
    }

    /// 递归解析变量的符号表达式
    fn resolve_symbolic(&self, var: Name) -> Option<String> {
        if let Some(def) = self.definitions.get(&var) {
            match def {
                DefInfo::FromSymbolic(s) => Some(s.clone()),
                DefInfo::FromAlias(target) => self.resolve_symbolic(*target),
                DefInfo::FromOp(op, args) => {
                    // 递归解析操作数的符号表达式
                    let arg_exprs: Vec<String> = args.iter()
                        .filter_map(|a| self.resolve_symbolic(*a))
                        .collect();

                    if arg_exprs.len() == args.len() {
                        // 所有操作数都能解析为符号表达式
                        Some(format!("{}({})", op, arg_exprs.join(", ")))
                    } else {
                        // 无法完全解析，尝试至少显示部分信息
                        let arg_names: Vec<String> = args.iter()
                            .map(|a| format!("zz{}", a))
                            .collect();
                        Some(format!("{}({})", op, arg_names.join(", ")))
                    }
                }
                DefInfo::FromCall(func, args) => {
                    // 检查是否是 IR 定义的函数，如果是则返回 None 让 format_condition 处理展开
                    if self.is_ir_function(func) {
                        None
                    } else {
                        // 递归解析函数参数的符号表达式
                        let arg_exprs: Vec<String> = args.iter()
                            .filter_map(|a| self.resolve_symbolic(*a))
                            .collect();

                        if arg_exprs.len() == args.len() {
                            // 所有参数都能解析为符号表达式
                            Some(format!("{}({})", func, arg_exprs.join(", ")))
                        } else if arg_exprs.is_empty() && args.len() == 1 {
                            // 单参数无法解析，尝试显示参数名
                            Some(format!("{}(zz{})", func, args[0]))
                        } else {
                            // 无法完全解析
                            None
                        }
                    }
                }
                DefInfo::Unknown => None,
            }
        } else {
            None
        }
    }

    /// 从值中提取符号表达式
    pub fn from_value<B: BV>(val: &Val<B>) -> Option<String> {
        match val {
            Val::Symbolic(sym) => Some(format!("v{}", sym)),
            _ => None,
        }
    }
}

/// CFG 边类型
#[derive(Debug, Clone)]
pub enum EdgeType {
    Unconditional,
    Conditional(Exp<Name>, bool),
    Call(Name),
    Return,
}

/// CFG 节点：代表一条指令
#[derive(Debug, Clone)]
pub struct CFGNode<B: BV> {
    pub pc: usize,
    pub instr: Instr<Name, B>,
    pub function: Name,
}

/// CFG 边：代表控制流转移
#[derive(Debug, Clone)]
pub struct CFGEdge {
    pub from: usize,
    pub to: usize,
    pub edge_type: EdgeType,
}

/// 代码段：表示一段顺序执行的指令
struct CodeSegment {
    start_pc: usize,
    end_pc: usize,
}

impl CodeSegment {
    fn len(&self) -> usize {
        self.end_pc - self.start_pc + 1
    }
}

/// 静态 CFG
#[derive(Clone)]
pub struct StaticCFG<B: BV> {
    pub nodes: Vec<CFGNode<B>>,
    pub edges: Vec<CFGEdge>,
    pub entry_point: usize,
    pub symbolic_mapping: SymbolicMapping,
}

impl<B: BV> StaticCFG<B> {
    pub fn new(entry_point: usize) -> Self {
        StaticCFG {
            nodes: Vec::new(),
            edges: Vec::new(),
            entry_point,
            symbolic_mapping: SymbolicMapping::new(),
        }
    }

    pub fn from_instructions(function_name: Name, instructions: &[Instr<Name, B>]) -> Self {
        let mut cfg = StaticCFG::new(0);
        let n = instructions.len();

        for (pc, instr) in instructions.iter().enumerate() {
            cfg.nodes.push(CFGNode {
                pc,
                instr: instr.clone(),
                function: function_name,
            });
        }

        let mut is_jump_target: HashSet<usize> = HashSet::new();

        for (pc, instr) in instructions.iter().enumerate() {
            match instr {
                Instr::Goto(target) => {
                    if *target < n {
                        is_jump_target.insert(*target);
                    }
                }
                Instr::Jump(_exp, target, _info) => {
                    if *target < n {
                        is_jump_target.insert(*target);
                    }
                }
                _ => {}
            }
        }

        for (pc, instr) in instructions.iter().enumerate() {
            match instr {
                Instr::End => {}
                Instr::Goto(target) => {
                    if *target < n {
                        cfg.edges.push(CFGEdge {
                            from: pc,
                            to: *target,
                            edge_type: EdgeType::Unconditional,
                        });
                    }
                }
                Instr::Jump(exp, target, _info) => {
                    if *target < n {
                        cfg.edges.push(CFGEdge {
                            from: pc,
                            to: *target,
                            edge_type: EdgeType::Conditional(exp.clone(), true),
                        });
                    }
                    if pc + 1 < n {
                        cfg.edges.push(CFGEdge {
                            from: pc,
                            to: pc + 1,
                            edge_type: EdgeType::Conditional(exp.clone(), false),
                        });
                    }
                }
                Instr::Call(_loc, _ext, name, _args, _info) => {
                    cfg.edges.push(CFGEdge {
                        from: pc,
                        to: pc,
                        edge_type: EdgeType::Call(*name),
                    });
                    if pc + 1 < n {
                        cfg.edges.push(CFGEdge {
                            from: pc,
                            to: pc + 1,
                            edge_type: EdgeType::Return,
                        });
                    }
                }
                _ => {
                    if pc + 1 < n && !is_jump_target.contains(&(pc + 1)) {
                        cfg.edges.push(CFGEdge {
                            from: pc,
                            to: pc + 1,
                            edge_type: EdgeType::Unconditional,
                        });
                    }
                }
            }
        }

        cfg
    }

    /// 分析数据流，建立变量定义映射
    pub fn analyze_dataflow(&mut self, symtab: &Symtab, args: &[(Name, &Ty<Name>)]) {
        // 参数已经在 set_symbolic_mapping 中设置好了，这里不需要重复设置
        // 只需要分析指令建立数据流

        // 分析每条指令，建立变量定义映射
        let instrs: Vec<_> = self.nodes.iter().map(|n| n.instr.clone()).collect();
        for instr in &instrs {
            match instr {
                Instr::Init(var, _ty, exp, _info) => {
                    self.analyze_exp(*var, exp, symtab);
                }
                Instr::Copy(loc, exp, _info) => {
                    if let Loc::Id(name) = loc {
                        self.analyze_exp(*name, exp, symtab);
                    }
                }
                Instr::PrimopUnary(loc, _op, exp, _info) => {
                    if let Loc::Id(name) = loc {
                        self.analyze_primop_unary(*name, exp, symtab);
                    }
                }
                Instr::PrimopBinary(loc, _op, exp1, _exp2, _info) => {
                    if let Loc::Id(name) = loc {
                        self.analyze_exp(*name, exp1, symtab);
                    }
                }
                Instr::PrimopVariadic(loc, _op, exps, _info) => {
                    if let Loc::Id(name) = loc {
                        if exps.len() == 1 {
                            self.analyze_exp(*name, &exps[0], symtab);
                        }
                    }
                }
                Instr::Call(loc, _ext, func_name, args_exp, _info) => {
                    if let Loc::Id(name) = loc {
                        let mut arg_vars = Vec::new();
                        for arg in args_exp {
                            if let Exp::Id(arg_name) = arg {
                                arg_vars.push(*arg_name);
                            }
                        }
                        self.symbolic_mapping.add_definition(*name, DefInfo::FromCall(symtab.to_str(*func_name).to_string(), arg_vars));
                    }
                }
                _ => {}
            }
        }
    }

    /// 分析表达式，建立变量定义
    fn analyze_exp(&mut self, target: Name, exp: &Exp<Name>, symtab: &Symtab) {
        match exp {
            Exp::Id(src_var) => {
                // 简单别名：如果源变量有符号映射，则复制该映射
                if let Some(symbolic) = self.symbolic_mapping.get_symbolic(*src_var) {
                    self.symbolic_mapping.add_definition(target, DefInfo::FromSymbolic(symbolic));
                } else {
                    self.symbolic_mapping.add_definition(target, DefInfo::FromAlias(*src_var));
                }
            }
            Exp::Call(op, args) => {
                // 函数调用：如果是单参数函数且参数有符号映射，则尝试传播
                let mut arg_vars = Vec::new();
                for arg in args {
                    if let Exp::Id(name) = arg {
                        arg_vars.push(*name);
                    }
                }

                // 特殊情况：对于单参数函数，如果参数有符号映射，则传播
                if arg_vars.len() == 1 {
                    if let Some(symbolic) = self.symbolic_mapping.get_symbolic(arg_vars[0]) {
                        self.symbolic_mapping.add_definition(target, DefInfo::FromSymbolic(symbolic));
                        return;
                    }
                }

                let op_name = format!("{:?}", op);
                self.symbolic_mapping.add_definition(target, DefInfo::FromOp(op_name, arg_vars));
            }
            Exp::I64(_) | Exp::I128(_) | Exp::Bits(_) | Exp::Bool(_) | Exp::Undefined(_) => {
                // 常量值
                let const_str = format!("{:?}", exp);
                self.symbolic_mapping.add_definition(target, DefInfo::FromSymbolic(const_str));
            }
            Exp::Ref(inner_name) => {
                // Ref takes a Name directly, treat it as an alias
                if let Some(symbolic) = self.symbolic_mapping.get_symbolic(*inner_name) {
                    self.symbolic_mapping.add_definition(target, DefInfo::FromSymbolic(symbolic));
                } else {
                    self.symbolic_mapping.add_definition(target, DefInfo::FromAlias(*inner_name));
                }
            }
            Exp::Field(base_exp, _field_name) => {
                // 结构体字段访问：尝试从基表达式中获取符号映射
                if let Exp::Id(base_var) = &**base_exp {
                    if let Some(symbolic) = self.symbolic_mapping.get_symbolic(*base_var) {
                        self.symbolic_mapping.add_definition(target, DefInfo::FromSymbolic(symbolic));
                    } else {
                        self.symbolic_mapping.add_definition(target, DefInfo::FromAlias(*base_var));
                    }
                } else {
                    self.symbolic_mapping.add_definition(target, DefInfo::Unknown);
                }
            }
            _ => {
                self.symbolic_mapping.add_definition(target, DefInfo::Unknown);
            }
        }
    }

    /// 设置符号映射
    pub fn set_symbolic_mapping(&mut self, mapping: SymbolicMapping) {
        self.symbolic_mapping = mapping;
    }

    /// 分析原始操作（函数指针），记录为函数调用
    /// 由于 Unary/Binary/Variadic 是函数指针，无法直接获取函数名
    /// 我们使用特殊的标记来表示这是一个原始操作
    fn analyze_primop_unary(&mut self, target: Name, exp: &Exp<Name>, _symtab: &Symtab) {
        // 尝试从表达式中提取函数调用信息
        match exp {
            Exp::Id(src_var) => {
                // 如果操作数是一个变量，记录为原始操作
                if let Some(symbolic) = self.symbolic_mapping.get_symbolic(*src_var) {
                    // 使用原始操作名称（从 symtab 获取函数名如果可能）
                    self.symbolic_mapping.add_definition(target, DefInfo::FromSymbolic(symbolic));
                } else {
                    // 记录为别名
                    self.symbolic_mapping.add_definition(target, DefInfo::FromAlias(*src_var));
                }
            }
            _ => {
                self.symbolic_mapping.add_definition(target, DefInfo::Unknown);
            }
        }
    }

    pub fn print(&self, symtab: &Symtab) {
        println!("╔═══════════════════════════════════════════════════════════════╗");
        println!("║                 Control Flow Branching                       ║");
        println!("╚═══════════════════════════════════════════════════════════════╝");
        println!();

        if !self.nodes.is_empty() {
            println!("📊 Statistics:");
            println!("   • Function: {}", symtab.to_str(self.nodes[0].function));
            println!("   • Total instructions: {}", self.nodes.len());

            let branch_points: Vec<usize> = self.nodes.iter()
                .filter(|n| matches!(n.instr, Instr::Jump(_, _, _)))
                .map(|n| n.pc)
                .collect();

            println!("   • Branch points: {}", branch_points.len());
            println!();

            println!("🌿 Branch Structure:");
            println!("┌─────────────────────────────────────────────────────────────────");

            let branch_pcs: HashSet<usize> = branch_points.into_iter().collect();

            let mut adj: HashMap<usize, Vec<&CFGEdge>> = HashMap::new();
            for edge in &self.edges {
                if !matches!(edge.edge_type, EdgeType::Call(_)) {
                    adj.entry(edge.from).or_insert_with(Vec::new).push(edge);
                }
            }

            self.print_branch_structure(symtab, 0, &adj, &branch_pcs, "", true);

            println!("└─────────────────────────────────────────────────────────────────");
            println!();
        }
    }

    fn print_branch_structure(
        &self,
        symtab: &Symtab,
        pc: usize,
        adj: &HashMap<usize, Vec<&CFGEdge>>,
        branch_pcs: &HashSet<usize>,
        prefix: &str,
        is_last: bool,
    ) {
        if pc >= self.nodes.len() {
            return;
        }

        let segment = self.collect_segment(pc, adj, branch_pcs);
        self.print_segment(symtab, &segment, prefix, is_last);

        let last_instr = &self.nodes[segment.end_pc].instr;
        let is_branch = branch_pcs.contains(&segment.end_pc);
        let is_goto = matches!(last_instr, Instr::Goto(_));

        if is_branch {
            if let Some(edges) = adj.get(&segment.end_pc) {
                for (i, edge) in edges.iter().enumerate() {
                    let is_last_child = i == edges.len() - 1;

                    let condition_str = if let EdgeType::Conditional(exp, is_true) = &edge.edge_type {
                        self.format_condition(exp, *is_true, symtab)
                    } else {
                        "?".to_string()
                    };

                    let new_prefix = format!("{}{}", prefix, if is_last { "   " } else { "│  " });
                    let branch_prefix = format!("{}{} ", new_prefix, if is_last_child { "└─" } else { "├─" });

                    println!("{}{} {}", branch_prefix, condition_str, "→");

                    let deeper_prefix = format!("{}{}", new_prefix, if is_last_child { "   " } else { "│  " });
                    self.print_branch_structure(symtab, edge.to, adj, branch_pcs, &deeper_prefix, is_last_child);
                }
            }
        } else if is_goto {
            // Goto 不创建新层级，直接跳到目标继续
            if let Some(edges) = adj.get(&segment.end_pc) {
                if !edges.is_empty() {
                    let target_pc = edges[0].to;
                    self.print_branch_structure(symtab, target_pc, adj, branch_pcs, prefix, is_last);
                }
            }
        }
    }

    /// 格式化条件表达式，使用符号映射
    fn format_condition(&self, exp: &Exp<Name>, is_true: bool, symtab: &Symtab) -> String {
        match exp {
            Exp::Bool(b) => {
                if *b == is_true {
                    "true".to_string()
                } else {
                    "false".to_string()
                }
            }
            Exp::Id(name) => {
                // 首先检查是否有符号映射
                if let Some(symbolic) = self.symbolic_mapping.get_symbolic(*name) {
                    if is_true {
                        format!("when {}", symbolic)
                    } else {
                        format!("when !{}", symbolic)
                    }
                } else {
                    // 没有符号映射，检查定义信息
                    let name_str = symtab.to_str(*name);
                    if let Some(def) = self.symbolic_mapping.definitions.get(name) {
                        match def {
                            DefInfo::FromCall(func, args) if !args.is_empty() => {
                                // 检查是否是 IR 定义的函数，如果是则展开
                                let call_str = if self.symbolic_mapping.is_ir_function(func) {
                                    self.expand_function_call(func, args, symtab)
                                } else {
                                    // Primop 或其他函数，不展开
                                    let arg_strs: Vec<String> = args.iter()
                                        .map(|a| self.format_exp(&Exp::Id(*a), symtab))
                                        .collect();
                                    format!("{}({})", func, arg_strs.join(", "))
                                };
                                if is_true {
                                    format!("when {}", call_str)
                                } else {
                                    format!("when !{}", call_str)
                                }
                            }
                            _ => {
                                // 其他情况，显示变量名
                                if is_true {
                                    format!("when {}", name_str)
                                } else {
                                    format!("when !{}", name_str)
                                }
                            }
                        }
                    } else {
                        // 没有定义信息，显示变量名
                        if is_true {
                            format!("when {}", name_str)
                        } else {
                            format!("when !{}", name_str)
                        }
                    }
                }
            }
            Exp::I64(n) => {
                if (*n != 0) == is_true {
                    format!("when {}", n)
                } else {
                    format!("when !({})", n)
                }
            }
            Exp::I128(n) => {
                if (*n != 0) == is_true {
                    format!("when {}", n)
                } else {
                    format!("when !({})", n)
                }
            }
            Exp::Undefined(ty) => {
                format!("when undefined:{:?}", ty)
            }
            Exp::Call(op, args) => {
                let op_name = format!("{:?}", op);
                let args_str: Vec<String> = args.iter().map(|a| self.format_exp(a, symtab)).collect();
                let full_call = format!("{}({})", op_name, args_str.join(", "));
                if is_true {
                    format!("when {}", full_call)
                } else {
                    format!("when !{}", full_call)
                }
            }
            _ => format!("when {:?}", exp),
        }
    }

    fn format_exp(&self, exp: &Exp<Name>, symtab: &Symtab) -> String {
        match exp {
            Exp::Id(name) => {
                if let Some(symbolic) = self.symbolic_mapping.get_symbolic(*name) {
                    symbolic
                } else {
                    symtab.to_str(*name).to_string()
                }
            }
            Exp::Bool(b) => format!("{}", b),
            Exp::I64(n) => format!("{}", n),
            Exp::I128(n) => format!("{}", n),
            Exp::Bits(b) => format!("{}", b),
            Exp::String(s) => format!("\"{}\"", s),
            Exp::Undefined(ty) => format!("undefined:{:?}", ty),
            Exp::Unit => "unit".to_string(),
            Exp::Ref(name) => {
                if let Some(symbolic) = self.symbolic_mapping.get_symbolic(*name) {
                    format!("&{}", symbolic)
                } else {
                    format!("&{}", symtab.to_str(*name))
                }
            }
            Exp::Call(op, args) => {
                let op_name = format!("{:?}", op);
                let args_str: Vec<String> = args.iter().map(|a| self.format_exp(a, symtab)).collect();
                format!("{}({})", op_name, args_str.join(", "))
            }
            Exp::Struct(name, fields) => {
                let name_str = symtab.to_str(*name);
                let fields_str: Vec<String> = fields.iter()
                    .map(|(fname, fexp)| format!("{}: {}", symtab.to_str(*fname), self.format_exp(fexp, symtab)))
                    .collect();
                format!("{} {{ {} }}", name_str, fields_str.join(", "))
            }
            Exp::Field(e, name) => format!("{}.{}", self.format_exp(e, symtab), symtab.to_str(*name)),
            Exp::Kind(_, e) => format!("kind({})", self.format_exp(e, symtab)),
            Exp::Unwrap(_, e) => format!("unwrap({})", self.format_exp(e, symtab)),
        }
    }

    /// 展开 IR 定义的函数调用，递归分析函数体直到遇到 primop
    fn expand_function_call(&self, func_name: &str, args: &[Name], symtab: &Symtab) -> String {
        // 获取函数体
        if let Some((params, return_var, func_body)) = self.symbolic_mapping.get_function_body(func_name) {
            // 首先构建函数内部的变量定义映射
            let mut local_defs: HashMap<Name, Exp<Name>> = HashMap::new();
            let mut local_calls: HashMap<Name, (Name, Vec<Name>)> = HashMap::new(); // 变量 -> (函数名, 参数)
            let mut primops: HashMap<Name, (Vec<Exp<Name>>, String)> = HashMap::new(); // 变量 -> (参数, 操作名)

            for instr in func_body.iter() {
                match instr {
                    Instr::Copy(Loc::Id(target), exp, _) => {
                        local_defs.insert(*target, exp.clone());
                    }
                    Instr::Init(target, _, exp, _) => {
                        local_defs.insert(*target, exp.clone());
                    }
                    Instr::Call(Loc::Id(target), _, func_name_id, call_args, _) => {
                        let mut arg_names = Vec::new();
                        for arg in call_args {
                            if let Exp::Id(arg_name) = arg {
                                arg_names.push(*arg_name);
                            }
                        }
                        local_calls.insert(*target, (*func_name_id, arg_names));
                    }
                    Instr::PrimopUnary(Loc::Id(target), _op, exp, _) => {
                        primops.insert(*target, (vec![exp.clone()], "primop".to_string()));
                    }
                    Instr::PrimopBinary(Loc::Id(target), _op, exp1, exp2, _) => {
                        primops.insert(*target, (vec![exp1.clone(), exp2.clone()], "primop".to_string()));
                    }
                    _ => {}
                }
            }

            // 递归展开返回值
            return self.expand_variable(*return_var, &params, args, &local_defs, &local_calls, &primops, symtab);
        }
        // 无法展开，返回函数调用形式
        let arg_strs: Vec<String> = args.iter()
            .map(|a| self.format_exp(&Exp::Id(*a), symtab))
            .collect();
        format!("{}({})", func_name, arg_strs.join(", "))
    }

    /// 递归展开变量定义
    fn expand_variable(
        &self,
        var: Name,
        params: &[Name],
        args: &[Name],
        local_defs: &HashMap<Name, Exp<Name>>,
        local_calls: &HashMap<Name, (Name, Vec<Name>)>,
        primops: &HashMap<Name, (Vec<Exp<Name>>, String)>,
        symtab: &Symtab
    ) -> String {
        // 如果是函数参数，返回对应的实参
        if let Some(idx) = params.iter().position(|&p| p == var) {
            return self.format_exp(&Exp::Id(args[idx]), symtab);
        }

        // 检查是否是 primop
        if let Some((op_args, op_name)) = primops.get(&var) {
            let expanded_args: Vec<String> = op_args.iter()
                .map(|arg| self.expand_exp_in_function_with_locals(arg, params, args, local_defs, local_calls, primops, symtab))
                .collect();
            return format!("{}({})", op_name, expanded_args.join(", "));
        }

        // 检查是否是函数调用
        if let Some((func_name, call_args)) = local_calls.get(&var) {
            let func_name_str = symtab.to_str(*func_name);
            // 映射参数
            let mut mapped_args = Vec::new();
            for arg in call_args {
                mapped_args.push(self.expand_variable(*arg, params, args, local_defs, local_calls, primops, symtab));
            }
            // 检查是否是 IR 函数
            if self.symbolic_mapping.is_ir_function(func_name_str) {
                return self.expand_function_call(func_name_str, call_args, symtab);
            } else {
                return format!("{}({})", func_name_str, mapped_args.join(", "));
            }
        }

        // 检查是否是局部变量定义
        if let Some(exp) = local_defs.get(&var) {
            return self.expand_exp_in_function_with_locals(exp, params, args, local_defs, local_calls, primops, symtab);
        }

        // 检查全局符号映射
        if let Some(symbolic) = self.symbolic_mapping.get_symbolic(var) {
            return symbolic;
        }

        // 无法展开，返回变量名
        symtab.to_str(var).to_string()
    }

    /// 在函数上下文中展开表达式（带局部变量映射）
    fn expand_exp_in_function_with_locals(
        &self,
        exp: &Exp<Name>,
        params: &[Name],
        args: &[Name],
        local_defs: &HashMap<Name, Exp<Name>>,
        local_calls: &HashMap<Name, (Name, Vec<Name>)>,
        primops: &HashMap<Name, (Vec<Exp<Name>>, String)>,
        symtab: &Symtab
    ) -> String {
        match exp {
            Exp::Id(name) => {
                self.expand_variable(*name, params, args, local_defs, local_calls, primops, symtab)
            }
            Exp::Call(op, call_args) => {
                let op_name = format!("{:?}", op);
                let args_str: Vec<String> = call_args.iter()
                    .map(|a| self.expand_exp_in_function_with_locals(a, params, args, local_defs, local_calls, primops, symtab))
                    .collect();
                format!("{}({})", op_name, args_str.join(", "))
            }
            Exp::Bool(b) => format!("{}", b),
            Exp::I64(n) => format!("{}", n),
            Exp::I128(n) => format!("{}", n),
            Exp::Bits(b) => format!("{}", b),
            Exp::String(s) => format!("\"{}\"", s),
            Exp::Undefined(ty) => format!("undefined:{:?}", ty),
            Exp::Unit => "unit".to_string(),
            Exp::Ref(name) => {
                format!("&{}", self.expand_variable(*name, params, args, local_defs, local_calls, primops, symtab))
            }
            Exp::Field(e, name) => {
                format!("{}.{}", self.expand_exp_in_function_with_locals(e, params, args, local_defs, local_calls, primops, symtab), symtab.to_str(*name))
            }
            Exp::Kind(_, e) => {
                format!("kind({})", self.expand_exp_in_function_with_locals(e, params, args, local_defs, local_calls, primops, symtab))
            }
            Exp::Unwrap(_, e) => {
                format!("unwrap({})", self.expand_exp_in_function_with_locals(e, params, args, local_defs, local_calls, primops, symtab))
            }
            _ => format!("{:?}", exp),
        }
    }

    fn collect_segment(
        &self,
        start_pc: usize,
        adj: &HashMap<usize, Vec<&CFGEdge>>,
        branch_pcs: &HashSet<usize>,
    ) -> CodeSegment {
        let mut current_pc = start_pc;

        while current_pc < self.nodes.len() {
            let instr = &self.nodes[current_pc].instr;

            // 在分支点或 end 处停止（不在 goto 处停止，因为 goto 会被合并）
            if branch_pcs.contains(&current_pc) || matches!(instr, Instr::End) {
                break;
            }

            // 检查控制流：如果不是简单的顺序执行，则停止
            if let Some(edges) = adj.get(&current_pc) {
                if edges.len() == 1 {
                    let next_pc = edges[0].to;
                    // 如果下一条不是 pc+1（即不是顺序执行），则停止
                    if next_pc != current_pc + 1 {
                        // 但如果是 goto，则包含它并继续
                        if !matches!(instr, Instr::Goto(_)) {
                            break;
                        }
                    }
                } else {
                    // 多条出边，这是分支点，应该在前面就停止了
                    break;
                }
            }

            current_pc += 1;
        }

        CodeSegment { start_pc, end_pc: current_pc }
    }

    fn print_segment(&self, symtab: &Symtab, segment: &CodeSegment, prefix: &str, is_last: bool) {
        // 对于 goto 指令，不显示（它会被合并到段中）
        let instr = &self.nodes[segment.start_pc].instr;
        if matches!(instr, Instr::Goto(_)) && segment.start_pc == segment.end_pc {
            return;
        }

        let icon = if segment.start_pc == segment.end_pc {
            let instr = &self.nodes[segment.start_pc].instr;
            if matches!(instr, Instr::Jump(_, _, _)) {
                "🔀"
            } else if matches!(instr, Instr::Goto(_)) {
                "➡️"
            } else if matches!(instr, Instr::End) {
                "🏁"
            } else {
                "•"
            }
        } else {
            "│"
        };

        print!("{}{}", prefix, if is_last { "└─" } else { "├─" });

        if segment.start_pc == segment.end_pc {
            let instr = &self.nodes[segment.start_pc].instr;
            print!("{} [PC {:3}] ", icon, segment.start_pc);
            self.print_instr_short(instr, symtab);
            println!();
        } else {
            print!("{} [PC {}-{:3}] ", icon, segment.start_pc, segment.end_pc);
            self.print_instr_short(&self.nodes[segment.start_pc].instr, symtab);
            print!(" → ... → ");
            self.print_instr_short(&self.nodes[segment.end_pc].instr, symtab);
            println!();
        }
    }

    fn print_instr_short(&self, instr: &Instr<Name, B>, symtab: &Symtab) {
        match instr {
            Instr::Init(var, _ty, _exp, _info) => {
                print!("{} = ...", symtab.to_str(*var));
            }
            Instr::Copy(loc, _exp, _info) => {
                print!("{} = ...", self.loc_to_string(loc, symtab));
            }
            Instr::Jump(exp, target, _info) => {
                print!("jump if {} → {}", self.format_exp(exp, symtab), target);
            }
            Instr::Goto(target) => {
                print!("goto → {}", target);
            }
            Instr::Call(_loc, _ext, name, _args, _info) => {
                print!("call {}", symtab.to_str(*name));
            }
            Instr::End => {
                print!("end");
            }
            Instr::Decl(var, _ty, _info) => {
                print!("decl {}", symtab.to_str(*var));
            }
            _ => {
                print!("...");
            }
        }
    }

    fn loc_to_string(&self, loc: &Loc<Name>, symtab: &Symtab) -> String {
        match loc {
            Loc::Id(name) => symtab.to_str(*name).to_string(),
            Loc::Field(loc, field) => format!("{}.{}", self.loc_to_string(loc, symtab), symtab.to_str(*field)),
            Loc::Addr(loc) => format!("&{}", self.loc_to_string(loc, symtab)),
        }
    }
}

pub fn build_static_cfg<B: BV>(
    function_name: Name,
    instructions: &[Instr<Name, B>],
) -> StaticCFG<B> {
    eprintln!("构建静态 CFG...");
    StaticCFG::from_instructions(function_name, instructions)
}
