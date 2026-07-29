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
use std::time::Duration;

use isla_lib::bitvector::b129::B129;
use isla_lib::bitvector::BV;
use isla_lib::init::{initialize_architecture, InitArchWithConfig};
use isla_lib::ir::{set_global_shared_state, AssertionMode, Bindings, SharedState};
use isla_lib::log;
mod opts;
use isla::isarch;
use isla::isarch::target::{RISCV, RV32, RV64};
use opts::CommonOpts;

/// isarch 支持的子命令
#[derive(Debug, PartialEq)]
enum Subcommand {
    /// 列出所有可用指令
    ListInstructions,
    /// 显示指令执行路径树
    Tree { instruction: String },
    /// 求解具体 ISA 状态值，支持通过 clause/扩展/指令名筛选
    SolveState { clauses: Vec<String>, extensions: Vec<String>, instruction_names: Vec<String>, run_all: bool },
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

fn parse_timeout_seconds(value: Option<&str>) -> Result<Option<u64>, String> {
    let Some(value) = value else {
        return Ok(None);
    };
    let value = value.trim();
    if value.is_empty() {
        return Err("--timeout 不能为空".to_string());
    }

    let (number, multiplier): (&str, u64) = match value.as_bytes().last().unwrap() {
        b's' | b'S' => (&value[..value.len() - 1], 1),
        b'm' | b'M' => (&value[..value.len() - 1], 60),
        b'h' | b'H' => (&value[..value.len() - 1], 60 * 60),
        b'0'..=b'9' => (value, 1),
        unit => return Err(format!("--timeout 不支持单位 '{}': 使用纯数字秒数，或后缀 s/m/h", *unit as char)),
    };

    if number.is_empty() {
        return Err("--timeout 缺少数值".to_string());
    }
    if !number.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(format!("--timeout 数值必须是非负整数: {}", value));
    }

    let seconds = number.parse::<u64>().map_err(|error| format!("Failed to parse --timeout: {}", error))?;
    seconds.checked_mul(multiplier).map(Some).ok_or_else(|| format!("--timeout 超出 u64 秒范围: {}", value))
}

fn parse_duration_arg(flag: &str, value: Option<&str>, allow_milliseconds: bool) -> Result<Option<Duration>, String> {
    let Some(value) = value else {
        return Ok(None);
    };
    let value = value.trim();
    if value.is_empty() {
        return Err(format!("{} 不能为空", flag));
    }

    let (number, unit) = if let Some(number) = value.strip_suffix("ms").or_else(|| value.strip_suffix("MS")) {
        if !allow_milliseconds {
            return Err(format!("{} 不支持 ms 单位", flag));
        }
        (number, "ms")
    } else if let Some(number) = value.strip_suffix('s').or_else(|| value.strip_suffix('S')) {
        (number, "s")
    } else if let Some(number) = value.strip_suffix('m').or_else(|| value.strip_suffix('M')) {
        (number, "m")
    } else if let Some(number) = value.strip_suffix('h').or_else(|| value.strip_suffix('H')) {
        (number, "h")
    } else {
        (value, "s")
    };

    if number.is_empty() || !number.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(format!("{} 数值必须是非负整数: {}", flag, value));
    }
    let value = number.parse::<u64>().map_err(|error| format!("Failed to parse {}: {}", flag, error))?;
    let duration = match unit {
        "ms" => Duration::from_millis(value),
        "s" => Duration::from_secs(value),
        "m" => Duration::from_secs(value.checked_mul(60).ok_or_else(|| format!("{} 超出范围", flag))?),
        "h" => Duration::from_secs(value.checked_mul(60 * 60).ok_or_else(|| format!("{} 超出范围", flag))?),
        _ => unreachable!(),
    };
    if duration.as_millis() > u64::MAX as u128 {
        return Err(format!("{} 超出 u64 毫秒范围", flag));
    }
    Ok(Some(duration))
}

fn parse_timeout_smt_output(
    value: Option<&str>,
    itrace_enabled: bool,
) -> Result<isarch::exec::TimeoutSmtOutput, String> {
    let Some(value) = value else {
        return Ok(isarch::exec::TimeoutSmtOutput::new(true, false, itrace_enabled));
    };
    if value.trim().is_empty() {
        return Err("--timeout-smt-output 不能为空".to_string());
    }

    let mut file = false;
    let mut stdout = false;
    let mut itrace = false;
    for destination in value.split(',').map(str::trim) {
        match destination {
            "file" => file = true,
            "stdout" => stdout = true,
            "itrace" => itrace = true,
            "" => return Err("--timeout-smt-output 包含空输出目标".to_string()),
            destination => {
                return Err(format!("--timeout-smt-output 不支持 '{}': 只能使用 file,stdout,itrace", destination))
            }
        }
    }
    if itrace && !itrace_enabled {
        return Err("--timeout-smt-output 请求 itrace，但没有配置 --itrace".to_string());
    }
    if !file && !stdout && !itrace {
        return Err("--timeout-smt-output 至少需要一个输出目标".to_string());
    }
    Ok(isarch::exec::TimeoutSmtOutput::new(file, stdout, itrace))
}

fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.optflag("", "init-isa-with-config", "使用配置默认值初始化ISA");
    opts.optflag("g", "graphviz", "输出 Graphviz 格式");
    opts.optopt("", "timeout", "超时时间，默认秒；支持 s/m/h 后缀", "<n[s|m|h]>");
    opts.optopt("", "smt-timeout", "单次 Z3 operation 的 soft interrupt 超时时间", "<n[s|m|h]>");
    opts.optopt("", "timeout-smt-output", "timeout SMT2 输出目标，逗号分隔：file,stdout,itrace", "<destinations>");
    opts.optopt("", "timeout-smt-dir", "timeout SMT2 文件输出目录", "<path>");
    opts.optmulti("", "clause", "指定要符号执行的clause名", "<name>");
    opts.optmulti("", "extension", "指定扩展名（如 i, m, c）", "<ext>");
    opts.optmulti("", "instruction-name", "指定指令汇编名称", "<name>");
    opts.optflag("", "all", "执行所有clause");
    opts.optopt("", "itrace", "把指令执行轨迹写入文件", "<path>");

    let mut hasher = Sha256::new();
    let (matches, arch) = opts::parse::<B129>(&mut hasher, &opts);
    let itrace_path = matches.opt_str("itrace").map(std::path::PathBuf::from);
    let arch_path = matches.opt_str("arch").map(std::path::PathBuf::from);
    let timeout_arg = matches.opt_str("timeout");
    let timeout: Option<u64> = match parse_timeout_seconds(timeout_arg.as_deref()) {
        Ok(timeout) => timeout,
        Err(e) => {
            eprintln!("{}", e);
            return 1;
        }
    };
    let smt_timeout = match parse_duration_arg("--smt-timeout", matches.opt_str("smt-timeout").as_deref(), false) {
        Ok(Some(timeout)) if timeout.is_zero() => {
            eprintln!("--smt-timeout 必须大于 0");
            return 1;
        }
        Ok(timeout) => timeout,
        Err(e) => {
            eprintln!("{}", e);
            return 1;
        }
    };
    let timeout_smt_output =
        match parse_timeout_smt_output(matches.opt_str("timeout-smt-output").as_deref(), itrace_path.is_some()) {
            Ok(output) => output,
            Err(e) => {
                eprintln!("{}", e);
                return 1;
            }
        };
    let timeout_smt_dir = matches
        .opt_str("timeout-smt-dir")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| std::path::PathBuf::from("output/timeout-smt"));

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

    isla_lib::smt::configure_z3_timeout(smt_timeout);

    let CommonOpts { num_threads, mut arch, symtab, type_info, mut isa_config, source_path } =
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
            let timeout_report_config =
                isarch::exec::TimeoutReportConfig { output: timeout_smt_output, directory: timeout_smt_dir };
            let xlen = detect_xlen(*shared_state, lets);
            let success = match xlen {
                32 => {
                    let mut target = RV32::default();
                    target.pmp_symbolic = pmp_symbolic;
                    let initial_memory = isla::isarch::memory_builder::MemoryBuilder::from_config(&target, &isa_config)
                        .and_then(|builder| builder.build())
                        .map_err(|e| eprintln!("Warning: MemoryBuilder error: {}", e))
                        .ok();
                    isarch::exec::solve_state_main(
                        shared_state,
                        regs,
                        lets,
                        initial_memory,
                        &mut target,
                        &clauses,
                        &extensions,
                        &instruction_names,
                        run_all,
                        itrace_path.clone(),
                        arch_path.clone(),
                        num_threads,
                        timeout,
                        isa_config.execution_limits.as_ref(),
                        timeout_report_config.clone(),
                    )
                }
                _ => {
                    let mut target = RV64::default();
                    target.pmp_symbolic = pmp_symbolic;
                    let initial_memory = isla::isarch::memory_builder::MemoryBuilder::from_config(&target, &isa_config)
                        .and_then(|builder| builder.build())
                        .map_err(|e| eprintln!("Warning: MemoryBuilder error: {}", e))
                        .ok();
                    isarch::exec::solve_state_main(
                        shared_state,
                        regs,
                        lets,
                        initial_memory,
                        &mut target,
                        &clauses,
                        &extensions,
                        &instruction_names,
                        run_all,
                        itrace_path.clone(),
                        arch_path.clone(),
                        num_threads,
                        timeout,
                        isa_config.execution_limits.as_ref(),
                        timeout_report_config,
                    )
                }
            };
            if success {
                0
            } else {
                1
            }
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
    fn parse_timeout_defaults_to_seconds() {
        assert_eq!(parse_timeout_seconds(None).unwrap(), None);
        assert_eq!(parse_timeout_seconds(Some("360")).unwrap(), Some(360));
        assert_eq!(parse_timeout_seconds(Some("360s")).unwrap(), Some(360));
        assert_eq!(parse_timeout_seconds(Some("360S")).unwrap(), Some(360));
    }

    #[test]
    fn parse_timeout_accepts_minutes_and_hours() {
        assert_eq!(parse_timeout_seconds(Some("6m")).unwrap(), Some(360));
        assert_eq!(parse_timeout_seconds(Some("6M")).unwrap(), Some(360));
        assert_eq!(parse_timeout_seconds(Some("1h")).unwrap(), Some(3600));
        assert_eq!(parse_timeout_seconds(Some("1H")).unwrap(), Some(3600));
    }

    #[test]
    fn parse_timeout_rejects_invalid_values() {
        assert!(parse_timeout_seconds(Some("")).is_err());
        assert!(parse_timeout_seconds(Some("m")).is_err());
        assert!(parse_timeout_seconds(Some("1d")).is_err());
        assert!(parse_timeout_seconds(Some("1.5h")).is_err());
        assert!(parse_timeout_seconds(Some("18446744073709551615h")).is_err());
    }

    #[test]
    fn parse_smt_duration_supports_query_units() {
        assert_eq!(parse_duration_arg("--smt-timeout", Some("10m"), false).unwrap(), Some(Duration::from_secs(600)));
        assert!(parse_duration_arg("--smt-timeout", Some("250ms"), false).is_err());
    }

    #[test]
    fn parse_smt_timeout_rejects_values_outside_u64_milliseconds() {
        let largest_whole_seconds = u64::MAX / 1000;
        let accepted = format!("{}s", largest_whole_seconds);
        let rejected = format!("{}s", largest_whole_seconds + 1);

        assert!(parse_duration_arg("--smt-timeout", Some(&accepted), false).is_ok());
        assert!(parse_duration_arg("--smt-timeout", Some(&rejected), false).is_err());
    }

    #[test]
    fn parse_timeout_smt_output_accepts_combinations_and_rejects_unknown_values() {
        let output = parse_timeout_smt_output(Some("file,stdout,itrace"), true).unwrap();
        assert!(output.file);
        assert!(output.stdout);
        assert!(output.itrace);

        assert!(parse_timeout_smt_output(Some("itrace"), false).is_err());
        assert!(parse_timeout_smt_output(Some("file,network"), true).is_err());
        assert!(parse_timeout_smt_output(Some(""), true).is_err());
    }

    #[test]
    fn timeout_smt_output_defaults_to_file_and_enabled_itrace() {
        let with_itrace = parse_timeout_smt_output(None, true).unwrap();
        assert!(with_itrace.file);
        assert!(!with_itrace.stdout);
        assert!(with_itrace.itrace);

        let without_itrace = parse_timeout_smt_output(None, false).unwrap();
        assert!(without_itrace.file);
        assert!(!without_itrace.stdout);
        assert!(!without_itrace.itrace);
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
    fn test_debug_instruction_removed() {
        let matches = make_matches(&["debug-instruction"]);
        let result = parse_subcommand(&matches);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("debug-instruction"));
    }

    #[test]
    fn test_debug_clause_args_removed() {
        let matches = make_matches(&["debug-clause-args"]);
        let result = parse_subcommand(&matches);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("debug-clause-args"));
    }

    #[test]
    fn test_debug_clause_args_yaml_removed() {
        let matches = make_matches(&["debug-clause-args-yaml"]);
        let result = parse_subcommand(&matches);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("debug-clause-args-yaml"));
    }
}
