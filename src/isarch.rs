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
//! This tool provides three main commands:
//! - `list-instructions`: List all available instructions in the architecture
//! - `tree <instruction>`: Show the execution path tree for an instruction
//! - `solve-state <instruction>`: Solve for concrete ISA state values

use sha2::{Digest, Sha256};
use std::process::exit;
use std::sync::{Arc, Mutex};

use isla_lib::bitvector::b129::B129;
use isla_lib::executor::{backtrace_string, start_single, LocalFrame, TaskId, TaskState};
use isla_lib::init::{initialize_architecture, InitArchWithConfig};
use isla_lib::ir::{AssertionMode, Bindings, Name};
use isla_lib::log;

mod opts;
use opts::CommonOpts;

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

fn print_usage(opts: &getopts::Options) -> ! {
    let brief = "Usage: isarch [options] <command> [args]\n\
                 Commands:\n\
                   list-instructions    List all available instructions\n\
                   tree <instruction>    Show execution path tree\n\
                   solve-state <instruction>  Solve for concrete ISA state values\n\
                 \n\
                 Options:\n";
    eprint!("{}", opts.usage(brief));
    exit(1)
}

fn cmd_list_instructions<B: isla_lib::bitvector::BV>(
    matches: getopts::Matches,
    shared_state: &&isla_lib::ir::SharedState<B>,
    regs: &isla_lib::register::RegisterBindings<B>,
    lets: &Bindings<B>,
    iarch_config: isla_lib::init::InitArchWithConfig<B>,
    source_path: Option<std::path::PathBuf>,
) -> i32 {
    use isla_lib::isarch;

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
}

fn cmd_tree<B: isla_lib::bitvector::BV>(
    matches: getopts::Matches,
    iarch: &isla_lib::init::Initialized<B>,
    arch: Vec<isla_lib::ir::Def<isla_lib::ir::Name, B>>,
    isa_config: isla_lib::config::ISAConfig<B>,
    source_path: Option<std::path::PathBuf>,
) -> i32 {
    use isla_lib::isarch;

    let instruction = &matches.free[1];
    let graphviz = matches.opt_present("graphviz");

    log!(log::VERBOSE, &format!("Analyzing instruction: {}", instruction));

    // TODO: Implement symbolic execution
    eprintln!("警告: 'tree' 命令尚未实现");
    eprintln!("这需要实现符号执行引擎来探索执行路径");

    // Placeholder output
    if graphviz {
        println!("{}", isarch::format_tree_graphviz::<B129>(&[]));
    } else {
        println!("{}", isarch::format_tree_ascii::<B129>(&[]));
    }

    0
}

fn cmd_solve_state<B: isla_lib::bitvector::BV>(
    matches: getopts::Matches,
    iarch: &isla_lib::init::Initialized<B>,
    arch: Vec<isla_lib::ir::Def<isla_lib::ir::Name, B>>,
    isa_config: isla_lib::config::ISAConfig<B>,
    source_path: Option<std::path::PathBuf>,
) -> i32 {
    use isla_lib::isarch;

    let instruction = &matches.free[1];
    let init_isa_with_config = matches.opt_present("init-isa-with-config");

    log!(log::VERBOSE, &format!("Solving state for instruction: {}", instruction));

    // TODO: Implement symbolic execution and solving
    eprintln!("警告: 'solve-state' 命令尚未实现");
    eprintln!("这需要实现符号执行引擎和 Z3 约束求解");

    0
}

fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.optflag("", "init-isa-with-config", "使用配置默认值初始化ISA");
    opts.optflag("g", "graphviz", "输出 Graphviz 格式");
    opts.optopt("", "timeout", "超时时间（秒）", "<n>");

    let mut hasher = Sha256::new();
    let (matches, arch) = opts::parse::<B129>(&mut hasher, &opts);

    if matches.free.is_empty() {
        print_usage(&opts);
    }

    let CommonOpts { num_threads, mut arch, symtab, type_info, isa_config, source_path } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);

    let assertion_mode = AssertionMode::Optimistic;
    let use_model_reg_init = !matches.opt_present("no-model-reg-init");

    let iarch = initialize_architecture(&mut arch, symtab, type_info, &isa_config, assertion_mode, use_model_reg_init);
    let iarch_config = InitArchWithConfig::from_initialized(&iarch, &isa_config);
    let regs = &iarch.regs;
    let lets = &iarch.lets;
    let shared_state = &&iarch.shared_state;

    let subcommand = matches.free[0].as_str();

	/* 提取功能start */
    // 用于存储执行结果
    let assembly_result: Arc<Mutex<Option<String>>> = Arc::new(Mutex::new(None));

	//add code here: 1.获得zassembly_forwards函数
    let function_id = shared_state.symtab.lookup("zassembly_forwards");
    let (args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();
    // 打印函数签名信息
    println!("zassembly_forwards 函数信息:");
    println!("  参数: {:?}", args.iter().map(|(n, _)| shared_state.symtab.to_str(*n)).collect::<Vec<_>>());
    println!("  返回类型: {:?}", ret_ty);
	// println!("{:?},{:?}",shared_state.symtab.to_str(args[0].0), shared_state.symtab.to_str(Name::from_u32(1666)) );

	//add code here: 2.将mret函数作为参数传入zassembly_forwards执行
    // 查找 zMRET 的 Name
    let zmret_name = shared_state.symtab.lookup("zMRET");

    // 构造 MRET 指令值 (zMRET 是一个 unit 类型的构造函数)
    let mret_value = isla_lib::ir::Val::<B129>::Ctor(zmret_name, Box::new(isla_lib::ir::Val::Unit));

	//add code here: 3.获取执行的字符串结果，打印出来
    println!("zMRET Name: {:?}", shared_state.symtab.to_str(zmret_name));
    println!("MRET value constructed: {:?}", mret_value);
    println!("\n开始执行 zassembly_forwards 函数...");

    // 获取 zassembly_forwards 函数信息
    let (args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();

    // 创建初始帧，将 mret_value 作为参数传入
    let mut initial_frame = LocalFrame::new(function_id, args, ret_ty, Some(&[mret_value]), instrs);
    initial_frame.add_regs(regs);

    // 创建任务状态
    let task_state = TaskState::new();

    // 创建任务
    let task_id = TaskId::fresh();
    let task = initial_frame.task(task_id, &task_state);

    // 使用单线程执行器执行任务
    let collected: Vec<isla_lib::ir::Val<B129>> = Vec::new();
    let collected = Arc::new(collected);

    start_single(task, shared_state, &collected, &|_thread, _task_id, result, shared_state, _solver, _collected| {
        match result {
            Ok((run, _frame)) => {
                println!("执行完成！");
                // 检查执行状态
                use isla_lib::executor::Run;
                match run {
                    Run::Finished(ret_val) => {
                        println!("函数返回值: {:?}", ret_val);
                        // 如果是字符串值，存储到外部变量
                        if let isla_lib::ir::Val::String(s) = ret_val {
                            println!("Assembly string: {}", s);
                            *assembly_result.lock().unwrap() = Some(s);
                        }
                    }
                    Run::Exit => {
                        println!("函数提前退出");
                    }
                    Run::Dead => {
                        println!("执行进入不一致状态");
                    }
                    Run::Suspended => {
                        println!("执行被挂起");
                    }
                }
            }
            Err((error, backtrace)) => {
                eprintln!("执行错误: {:?}", error);
                eprintln!("调用栈: {:?}", backtrace_string(&backtrace, &shared_state.symtab));
            }
        }
    });

    // 在 isla_main 作用域中获取执行结果
    if let Some(result) = assembly_result.lock().unwrap().as_ref() {
        println!("\n===== isla_main 作用域中获取到的结果 =====");
        println!("Assembly result: {}", result);
        println!("==========================================");
    }

	/* 提取功能end */

    match subcommand {
        "list-instructions" => cmd_list_instructions(matches, shared_state,regs,lets, iarch_config, source_path),
        /* "tree" => {
            if matches.free.len() < 2 {
                eprintln!("Error: 'tree' command requires an instruction argument");
                println!("\nUsage: isarch [options] tree <instruction>");
                println!("\nExample: isarch -A ./rv32d.ir -C configs/riscv32.toml tree mret");
                1
            } else {
                cmd_tree(matches, &iarch, arch, isa_config, source_path)
            }
        } */
        /* "solve-state" => {
            if matches.free.len() < 2 {
                eprintln!("Error: 'solve-state' command requires an instruction argument");
                println!("\nUsage: isarch [options] solve-state <instruction>");
                println!("\nExample: isarch -A ./rv32d.ir -C configs/riscv32.toml solve-state mret");
                1
            } else {
                cmd_solve_state(matches, &iarch, arch, isa_config, source_path)
            }
        } */
        _ => {
            eprintln!("Error: Unknown command '{}'", subcommand);
            print_usage(&opts);
        }
    }
}
