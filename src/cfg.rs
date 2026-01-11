use std::collections::{HashMap, HashSet};
use isla_lib::ir::*;
use isla_lib::smt::Sym;
use isla_lib::smt::smtlib::Exp;
use isla_lib::bitvector::BV;

/// CFG 边类型
#[derive(Debug, Clone, PartialEq)]
pub enum EdgeType {
    Unconditional,
    Conditional(Exp<Sym>, bool), // (条件, is_true_branch)
    Call(Name),
    Return,
}

/// CFG 节点：代表一条指令
#[derive(Debug, Clone)]
pub struct CFGNode<B: BV> {
    pub pc: usize,                // 指令索引
    pub instr: Instr<Name, B>,    // 指令内容
    pub function: Name,           // 所属函数
}

/// CFG 边：代表控制流转移
#[derive(Debug, Clone)]
pub struct CFGEdge {
    pub from: usize,      // 源节点 PC
    pub to: usize,        // 目标节点 PC
    pub edge_type: EdgeType,
}

/// 静态 CFG：基于指令列表构建的控制流图
#[derive(Clone)]
pub struct StaticCFG<B: BV> {
    pub nodes: Vec<CFGNode<B>>,
    pub edges: Vec<CFGEdge>,
    pub entry_point: usize,
}

impl<B: BV> StaticCFG<B> {
    pub fn new(entry_point: usize) -> Self {
        StaticCFG {
            nodes: Vec::new(),
            edges: Vec::new(),
            entry_point,
        }
    }

    /// 从指令列表构建静态 CFG
    pub fn from_instructions(function_name: Name, instructions: &[Instr<Name, B>]) -> Self {
        let mut cfg = StaticCFG::new(0);
        let n = instructions.len();

        // 创建节点
        for (pc, instr) in instructions.iter().enumerate() {
            cfg.nodes.push(CFGNode {
                pc,
                instr: instr.clone(),
                function: function_name,
            });
        }

        // 分析每条指令，创建边
        for (pc, instr) in instructions.iter().enumerate() {
            match instr {
                // 无条件跳转
                Instr::Goto(target) => {
                    // target 是 usize 类型
                    if *target < n {
                        cfg.edges.push(CFGEdge {
                            from: pc,
                            to: *target,
                            edge_type: EdgeType::Unconditional,
                        });
                    }
                }

                // 条件跳转
                Instr::Jump(_exp, target, _info) => {
                    // target 是 usize 类型
                    if *target < n {
                        cfg.edges.push(CFGEdge {
                            from: pc,
                            to: *target,
                            edge_type: EdgeType::Conditional(Exp::Var(Sym::from_u32(0)), true), // 占位
                        });
                    }
                    // 条件为 false 时默认跳到下一条指令
                    if pc + 1 < n {
                        cfg.edges.push(CFGEdge {
                            from: pc,
                            to: pc + 1,
                            edge_type: EdgeType::Conditional(Exp::Var(Sym::from_u32(0)), false),
                        });
                    }
                }

                // 函数调用 - 调用后返回到下一条指令
                Instr::Call(_loc, _ext, name, _args, _info) => {
                    cfg.edges.push(CFGEdge {
                        from: pc,
                        to: pc,
                        edge_type: EdgeType::Call(*name),
                    });
                    // 调用后返回到下一条
                    if pc + 1 < n {
                        cfg.edges.push(CFGEdge {
                            from: pc,
                            to: pc + 1,
                            edge_type: EdgeType::Return,
                        });
                    }
                }

                // 其他指令：顺序执行到下一条
                _ => {
                    if pc + 1 < n {
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

    /// 打印 CFG
    pub fn print(&self, symtab: &Symtab) {
        println!("╔═══════════════════════════════════════════════════════════════╗");
        println!("║                 Static Control Flow Graph                    ║");
        println!("╚═══════════════════════════════════════════════════════════════╝");
        println!();

        if !self.nodes.is_empty() {
            println!("📊 Statistics:");
            println!("   • Function: {}", symtab.to_str(self.nodes[0].function));
            println!("   • Total instructions: {}", self.nodes.len());
            println!("   • Total edges: {}", self.edges.len());
            println!();

            println!("📝 Instructions:");
            println!("┌─────────────────────────────────────────────────────────────────");
            for node in &self.nodes {
                print!("│ [{:3}] ", node.pc);
                self.print_instr_short(&node.instr, symtab);
                println!();
            }
            println!("└─────────────────────────────────────────────────────────────────");
            println!();

            println!("🔗 Control Flow:");
            if self.edges.is_empty() {
                println!("   (no edges)");
            } else {
                // 按源 PC 分组
                let mut edges_by_from: HashMap<usize, Vec<&CFGEdge>> = HashMap::new();
                for edge in &self.edges {
                    edges_by_from.entry(edge.from).or_insert_with(Vec::new).push(edge);
                }

                let mut sorted_from_pcs: Vec<_> = edges_by_from.keys().cloned().collect();
                sorted_from_pcs.sort();

                for from_pc in sorted_from_pcs {
                    println!("   From PC {}:", from_pc);
                    if let Some(edges) = edges_by_from.get(&from_pc) {
                        for edge in edges {
                            match &edge.edge_type {
                                EdgeType::Unconditional => {
                                    println!("     └──→ PC {}", edge.to);
                                }
                                EdgeType::Conditional(_cond, is_true) => {
                                    if *is_true {
                                        println!("     ├──[TRUE  ] → PC {}", edge.to);
                                    } else {
                                        println!("     ├──[FALSE] → PC {}", edge.to);
                                    }
                                }
                                EdgeType::Call(name) => {
                                    println!("     └──call {} → PC {}", symtab.to_str(*name), edge.to);
                                }
                                EdgeType::Return => {
                                    println!("     └──return → PC {}", edge.to);
                                }
                            }
                        }
                    }
                }
            }
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
            Instr::Jump(_exp, target, _info) => {
                print!("jump if ... → {}", target);
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
                print!("decl {}: ...", symtab.to_str(*var));
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

/// 符号执行并构建静态 CFG
pub fn build_static_cfg<B: BV>(
    function_name: Name,
    instructions: &[Instr<Name, B>],
) -> StaticCFG<B> {
    eprintln!("构建静态 CFG...");
    StaticCFG::from_instructions(function_name, instructions)
}
