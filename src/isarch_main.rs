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

//! CLI tool for exploring RISC-V instruction execution through symbolic execution.
//!
//! This tool provides commands:
//! - `list-instructions`: List all available instructions in the architecture
//! - `tree <instruction>`: Show the execution path tree for an instruction
//! - `solve-state [--clause|--extension|--instruction-name|--all]`: Solve for concrete ISA state values

use sha2::{Digest, Sha256};
use std::process::exit;

use isla_lib::bitvector::b129::B129;
use isla_lib::bitvector::BV;
use isla_lib::init::{initialize_architecture, InitArchWithConfig};
use isla_lib::ir::{set_global_shared_state, AssertionMode, Bindings, SharedState};
use isla_lib::log;
mod opts;
use isla::isarch;
use isla::isarch::target::{RISCV, RV32, RV64};
use opts::CommonOpts;

use isla::isarch::args::test_clause_args_main;
use isla::isarch::args_yaml::test_clause_args_yaml_main;

/// isarch 支持的子命令
#[derive(Debug, PartialEq)]
enum Subcommand {
    /// 列出所有可用指令
    ListInstructions,
    /// 显示指令执行路径树
    Tree { instruction: String },
    /// 求解具体 ISA 状态值，支持通过 clause/扩展/指令名筛选
    SolveState { clauses: Vec<String>, extensions: Vec<String>, instruction_names: Vec<String>, run_all: bool },
    /// 调试指令汇编名称列举（替代 debug_instruction feature）
    DebugInstruction { clause: Option<String> },
    /// 调试 clause 参数提取（替代 debug_clause_args feature）
    DebugClauseArgs { clause: Option<String> },
    /// 导出 clause 参数为 YAML（替代 debug_clause_args_yaml feature）
    DebugClauseArgsYaml,
}

/// 从命令行参数解析子命令
fn parse_subcommand(matches: &getopts::Matches) -> Result<Subcommand, String> {
    if matches.free.is_empty() {
        return Err("未指定子命令".to_string());
    }
    match matches.free[0].as_str() {
        "list-instructions" => Ok(Subcommand::ListInstructions),
        "tree" => {
            if matches.free.len() < 2 {
                return Err("'tree' 命令需要指定指令参数".to_string());
            }
            Ok(Subcommand::Tree { instruction: matches.free[1].clone() })
        }
        "solve-state" => {
            let clauses = matches.opt_strs("clause");
            let extensions = matches.opt_strs("extension");
            let instruction_names = matches.opt_strs("instruction-name");
            let run_all = matches.opt_present("all");
            Ok(Subcommand::SolveState { clauses, extensions, instruction_names, run_all })
        }
        "debug-instruction" => Ok(Subcommand::DebugInstruction { clause: matches.free.get(1).cloned() }),
        "debug-clause-args" => Ok(Subcommand::DebugClauseArgs { clause: matches.free.get(1).cloned() }),
        "debug-clause-args-yaml" => Ok(Subcommand::DebugClauseArgsYaml),
        other => Err(format!("未知命令 '{}'", other)),
    }
}

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

fn print_usage(opts: &getopts::Options) -> ! {
    let brief = "Usage: isarch [options] <command> [args]\n\
                 Commands:\n\
                   list-instructions                    List all available instructions\n\
                   tree <instruction>                   Show execution path tree\n\
                   solve-state [--clause|--extension|--instruction-name|--all]\n\
                                                        Solve for concrete ISA state values\n\
                   debug-instruction [<clause>]         Debug instruction assembly name listing\n\
                   debug-clause-args [<clause>]         Debug clause argument extraction\n\
                   debug-clause-args-yaml               Export clause args to YAML files\n\
                 \n\
                 solve-state filters:\n\
                   --clause <name>                      Specify clause(s) to execute (repeatable)\n\
                   --extension <ext>                    Specify extension (i, m, c, etc.) (repeatable)\n\
                   --instruction-name <name>            Specify assembly instruction name (repeatable)\n\
                   --all                                Execute all clauses\n\
                 \n\
                 Options:\n";
    eprint!("{}", opts.usage(brief));
    exit(1)
}

/* fn cmd_list_instructions<B: isla_lib::bitvector::BV>(
    matches: getopts::Matches,
    shared_state: &&isla_lib::ir::SharedState<B>,
    regs: &isla_lib::register::RegisterBindings<B>,
    lets: &Bindings<B>,
    iarch_config: isla_lib::init::InitArchWithConfig<B>,
    source_path: Option<std::path::PathBuf>,
) -> i32 {
    use isarch;

    log!(log::VERBOSE, &format!("Building instruction dictionary..."));

    match isarch::build_instruction_dict::<B129>(&[], &shared_state.symtab) {
        Ok(instructions) => {
            if instructions.is_empty() {
                eprintln!("警告: 未找到任何指令");
                eprintln!("这可能是由于 IR 文件格式不匹配或解析逻辑需要调整");
                return 1;
            }

            println!("可用指令 ({} 条):", instructions.len());
            println!();

            let mut names: Vec<_> = instructions.keys().collect();
            names.sort();

            for name in names {
                let info = &instructions[name];
                println!("  {} ({})", name, info.encoded_name);
            }

            0
        }
        Err(e) => {
            eprintln!("错误: 构建指令字典失败: {}", e);
            1
        }
    }
} */

#[allow(dead_code)]
fn cmd_tree<B: isla_lib::bitvector::BV>(
    matches: getopts::Matches,
    shared_state: &&isla_lib::ir::SharedState<B>,
    regs: &isla_lib::register::RegisterBindings<B>,
    lets: &Bindings<B>,
    iarch_config: isla_lib::init::InitArchWithConfig<B>,
    source_path: Option<std::path::PathBuf>,
) -> i32 {
    let instruction = &matches.free[1];
    let graphviz = matches.opt_present("graphviz");

    log!(log::VERBOSE, &format!("Analyzing instruction: {}", instruction));

    // Execute symbolic execution to build execution tree
    /* match isarch::execute_instruction_tree::<B>(instruction, shared_state, regs, lets) {
           Ok(result) => {
               if graphviz {
                   // Generate Graphviz DOT output
                   let dot_output = isarch::format_tree_graphviz(&result);

                   // Create output directory
                   if let Err(e) = create_dir_all("out") {
                       eprintln!("错误: 无法创建 out 目录: {}", e);
                       return 1;
                   }

                   // Write DOT file
                   let dot_filename = format!("out/{}.dot", instruction);
                   if let Err(e) = std::fs::File::create(&dot_filename)
                       .and_then(|mut f| f.write_all(dot_output.as_bytes()))
                   {
                       eprintln!("错误: 无法写入 DOT 文件 {}: {}", dot_filename, e);
                       return 1;
                   }
                   println!("DOT 文件已保存到: {}", dot_filename);

                   // Generate PNG using dot command
                   let png_filename = format!("out/{}.png", instruction);
                   match Command::new("dot")
                       .arg("-Tpng")
                       .arg(&dot_filename)
                       .arg("-o")
                       .arg(&png_filename)
                       .output()
                   {
                       Ok(output) => {
                           if output.status.success() {
                               println!("图片已保存到: {}", png_filename);
                           } else {
                               eprintln!("警告: dot 命令执行失败: {}", String::from_utf8_lossy(&output.stderr));
                           }
                       }
                       Err(e) => {
                           eprintln!("警告: 无法执行 dot 命令生成图片: {}", e);
                           eprintln!("请安装 graphviz: apt install graphviz");
                       }
                   }

                   // Also print DOT to stdout
                   println!("\n--- DOT 输出 ---\n");
                   println!("{}", dot_output);
               } else {
                   println!("{}", isarch::format_tree_ascii(&result));
               }
               0
           }
           Err(e) => {
               eprintln!("错误: 符号执行失败: {:?}", e);
               1
           }
       }
    */
    0
}

#[allow(dead_code)]
fn cmd_solve_state<B: isla_lib::bitvector::BV>(
    matches: getopts::Matches,
    iarch: &isla_lib::init::Initialized<B>,
    arch: Vec<isla_lib::ir::Def<isla_lib::ir::Name, B>>,
    isa_config: isla_lib::config::ISAConfig<B>,
    source_path: Option<std::path::PathBuf>,
) -> i32 {
    let instruction = &matches.free[1];
    let init_isa_with_config = matches.opt_present("init-isa-with-config");

    log!(log::VERBOSE, &format!("Solving state for instruction: {}", instruction));

    // TODO: Implement symbolic execution and solving
    eprintln!("警告: 'solve-state' 命令尚未实现");
    eprintln!("这需要实现符号执行引擎和 Z3 约束求解");

    0
}

fn detect_xlen<B: BV>(shared_state: &SharedState<B>, lets: &Bindings<B>) -> u32 {
    let xlen_name = shared_state.symtab.lookup("zxlen");
    match lets.get(&xlen_name) {
        Some(isla_lib::ir::UVal::Init(isla_lib::ir::Val::I64(n))) => *n as u32,
        Some(isla_lib::ir::UVal::Init(isla_lib::ir::Val::I128(n))) => *n as u32,
        _ => panic!("unexpected xlen in lets: {:?}", lets.get(&xlen_name)),
    }
}

fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.optflag("", "init-isa-with-config", "使用配置默认值初始化ISA");
    opts.optflag("g", "graphviz", "输出 Graphviz 格式");
    opts.optopt("", "timeout", "超时时间（秒）", "<n>");
    opts.optmulti("", "clause", "指定要符号执行的clause名", "<name>");
    opts.optmulti("", "extension", "指定扩展名（如 i, m, c）", "<ext>");
    opts.optmulti("", "instruction-name", "指定指令汇编名称", "<name>");
    opts.optflag("", "all", "执行所有clause");
    opts.optopt("", "itrace", "把指令执行轨迹写入文件", "<path>");

    let mut hasher = Sha256::new();
    let (matches, arch) = opts::parse::<B129>(&mut hasher, &opts);
    let itrace_path = matches.opt_str("itrace").map(std::path::PathBuf::from);
    let arch_path = matches.opt_str("arch").map(std::path::PathBuf::from);

    if matches.free.is_empty() {
        print_usage(&opts);
    }

    let subcommand = match parse_subcommand(&matches) {
        Ok(cmd) => cmd,
        Err(e) => {
            eprintln!("Error: {}", e);
            print_usage(&opts);
        }
    };

    let CommonOpts { num_threads: _, mut arch, symtab, type_info, mut isa_config, source_path } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);

    let assertion_mode = AssertionMode::Optimistic;
    let use_model_reg_init = !matches.opt_present("no-model-reg-init");

    let pmp_symbolic = isa_config.pmp.as_ref().map(|pmp| pmp.symbolic).unwrap_or(false);

    if let Some(pmp_config) = &isa_config.pmp {
        if !pmp_config.symbolic {
            RV64::default()
                .apply_pmp_rules_to_config(pmp_config, &symtab, &type_info, &mut isa_config.default_registers)
                .unwrap();
        }
    }

    let iarch = initialize_architecture(&mut arch, symtab, type_info, &isa_config, assertion_mode, use_model_reg_init);
    let iarch_config = InitArchWithConfig::from_initialized(&iarch, &isa_config);
    let regs = &iarch.regs;
    let lets = &iarch.lets;
    let shared_state = &&iarch.shared_state;

    set_global_shared_state(*shared_state);

    match subcommand {
        Subcommand::ListInstructions => {
            let instructions = isarch::list_instructions(*shared_state, regs, lets);
            let total_inst: usize = instructions.iter().map(|(_, names)| names.len()).sum();
            let total_clause = instructions.len();
            println!("共 {} 个 clause，{} 条指令：", total_clause, total_inst);
            println!();
            for (clause, names) in &instructions {
                if names.is_empty() {
                    println!("  [{}] (无汇编名称)", clause);
                } else {
                    println!("  [{}] {}", clause, names.join(", "));
                }
            }
            0
        }
        Subcommand::Tree { .. } => cmd_tree(matches, shared_state, regs, lets, iarch_config, source_path),
        Subcommand::SolveState { clauses, extensions, instruction_names, run_all } => {
            let xlen = detect_xlen(*shared_state, lets);
            let success = match xlen {
                32 => {
                    let target = RV32 { pmp_symbolic };
                    let initial_memory = isla::isarch::memory_builder::MemoryBuilder::from_config(&target, &isa_config)
                        .and_then(|builder| builder.build())
                        .map_err(|e| eprintln!("Warning: MemoryBuilder error: {}", e))
                        .ok();
                    isarch::exec::solve_state_main(
                        shared_state,
                        regs,
                        lets,
                        initial_memory,
                        &target,
                        &clauses,
                        &extensions,
                        &instruction_names,
                        run_all,
                        itrace_path.clone(),
                        arch_path.clone(),
                    )
                }
                _ => {
                    let target = RV64 { pmp_symbolic };
                    let initial_memory = isla::isarch::memory_builder::MemoryBuilder::from_config(&target, &isa_config)
                        .and_then(|builder| builder.build())
                        .map_err(|e| eprintln!("Warning: MemoryBuilder error: {}", e))
                        .ok();
                    isarch::exec::solve_state_main(
                        shared_state,
                        regs,
                        lets,
                        initial_memory,
                        &target,
                        &clauses,
                        &extensions,
                        &instruction_names,
                        run_all,
                        itrace_path.clone(),
                        arch_path.clone(),
                    )
                }
            };
            if success {
                0
            } else {
                1
            }
        }
        Subcommand::DebugInstruction { clause } => {
            let clause_name = clause.as_deref().unwrap_or("zRTYPE");
            isarch::test_instruction_list_main(shared_state, regs, lets, clause_name);
            0
        }
        Subcommand::DebugClauseArgs { clause: _ } => {
            test_clause_args_main(shared_state, regs, lets);
            0
        }
        Subcommand::DebugClauseArgsYaml => {
            test_clause_args_yaml_main(shared_state, regs, lets);
            0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_matches(args: &[&str]) -> getopts::Matches {
        let mut opts = getopts::Options::new();
        opts.optflag("g", "graphviz", "");
        opts.optopt("A", "arch", "", "");
        opts.optopt("C", "config", "", "");
        opts.optmulti("", "clause", "", "<name>");
        opts.optmulti("", "extension", "", "<ext>");
        opts.optmulti("", "instruction-name", "", "<name>");
        opts.optflag("", "all", "");
        opts.parse(args).unwrap()
    }

    #[test]
    fn test_no_subcommand() {
        let matches = make_matches(&[]);
        let result = parse_subcommand(&matches);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("未指定子命令"));
    }

    #[test]
    fn test_unknown_command() {
        let matches = make_matches(&["foobar"]);
        let result = parse_subcommand(&matches);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("foobar"));
    }

    #[test]
    fn test_list_instructions() {
        let matches = make_matches(&["list-instructions"]);
        assert_eq!(parse_subcommand(&matches).unwrap(), Subcommand::ListInstructions);
    }

    #[test]
    fn test_tree_with_instruction() {
        let matches = make_matches(&["tree", "mret"]);
        assert_eq!(parse_subcommand(&matches).unwrap(), Subcommand::Tree { instruction: "mret".to_string() });
    }

    #[test]
    fn test_tree_missing_instruction() {
        let matches = make_matches(&["tree"]);
        let result = parse_subcommand(&matches);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("tree"));
    }

    #[test]
    fn test_solve_state_no_filter() {
        let matches = make_matches(&["solve-state"]);
        assert_eq!(
            parse_subcommand(&matches).unwrap(),
            Subcommand::SolveState { clauses: vec![], extensions: vec![], instruction_names: vec![], run_all: false }
        );
    }

    #[test]
    fn test_solve_state_with_clause() {
        let matches = make_matches(&["solve-state", "--clause", "zADD"]);
        assert_eq!(
            parse_subcommand(&matches).unwrap(),
            Subcommand::SolveState {
                clauses: vec!["zADD".to_string()],
                extensions: vec![],
                instruction_names: vec![],
                run_all: false,
            }
        );
    }

    #[test]
    fn test_solve_state_with_extension() {
        let matches = make_matches(&["solve-state", "--extension", "i"]);
        assert_eq!(
            parse_subcommand(&matches).unwrap(),
            Subcommand::SolveState {
                clauses: vec![],
                extensions: vec!["i".to_string()],
                instruction_names: vec![],
                run_all: false,
            }
        );
    }

    #[test]
    fn test_solve_state_with_instruction_name() {
        let matches = make_matches(&["solve-state", "--instruction-name", "add"]);
        assert_eq!(
            parse_subcommand(&matches).unwrap(),
            Subcommand::SolveState {
                clauses: vec![],
                extensions: vec![],
                instruction_names: vec!["add".to_string()],
                run_all: false,
            }
        );
    }

    #[test]
    fn test_solve_state_with_all() {
        let matches = make_matches(&["solve-state", "--all"]);
        assert_eq!(
            parse_subcommand(&matches).unwrap(),
            Subcommand::SolveState { clauses: vec![], extensions: vec![], instruction_names: vec![], run_all: true }
        );
    }

    #[test]
    fn test_solve_state_with_multiple_filters() {
        let matches =
            make_matches(&["solve-state", "--clause", "zSTORE", "--extension", "i", "--instruction-name", "add"]);
        assert_eq!(
            parse_subcommand(&matches).unwrap(),
            Subcommand::SolveState {
                clauses: vec!["zSTORE".to_string()],
                extensions: vec!["i".to_string()],
                instruction_names: vec!["add".to_string()],
                run_all: false,
            }
        );
    }

    #[test]
    fn test_debug_instruction_no_clause() {
        let matches = make_matches(&["debug-instruction"]);
        assert_eq!(parse_subcommand(&matches).unwrap(), Subcommand::DebugInstruction { clause: None });
    }

    #[test]
    fn test_debug_instruction_with_clause() {
        let matches = make_matches(&["debug-instruction", "zRTYPE"]);
        assert_eq!(
            parse_subcommand(&matches).unwrap(),
            Subcommand::DebugInstruction { clause: Some("zRTYPE".to_string()) }
        );
    }

    #[test]
    fn test_debug_clause_args_no_clause() {
        let matches = make_matches(&["debug-clause-args"]);
        assert_eq!(parse_subcommand(&matches).unwrap(), Subcommand::DebugClauseArgs { clause: None });
    }

    #[test]
    fn test_debug_clause_args_with_clause() {
        let matches = make_matches(&["debug-clause-args", "zSTORE"]);
        assert_eq!(
            parse_subcommand(&matches).unwrap(),
            Subcommand::DebugClauseArgs { clause: Some("zSTORE".to_string()) }
        );
    }

    #[test]
    fn test_debug_clause_args_yaml() {
        let matches = make_matches(&["debug-clause-args-yaml"]);
        assert_eq!(parse_subcommand(&matches).unwrap(), Subcommand::DebugClauseArgsYaml);
    }
}
