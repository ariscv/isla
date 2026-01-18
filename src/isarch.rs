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

use std::any::type_name;
use std::collections::HashMap;
use sha2::{Digest, Sha256};
use std::process::exit;
use std::sync::{Arc, Mutex};

use isla_lib::bitvector::b129::B129;
use isla_lib::bitvector::BV;
use isla_lib::executor::{backtrace_string, start_single, LocalFrame, Run, TaskId, TaskState};
use isla_lib::init::{initialize_architecture, InitArchWithConfig};
use isla_lib::ir::{AssertionMode, Bindings, FPTy, Name, SharedState, Ty, Val};
use isla_lib::log;
use isla_lib::register::RegisterBindings;

mod opts;
use opts::CommonOpts;

/// 通用的IR函数执行API
/// 执行指定的IR函数并返回结果
fn execute_ir_function<B: BV>(
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
                eprintln!("执行错误: {:?}", error);
                eprintln!("调用栈: {:?}", backtrace_string(&backtrace, &shared_state.symtab));
            }
        }
    });

    let res = result.lock().unwrap().as_ref().cloned();
    res
}

/// 根据类型生成默认值
fn generate_default_value<B: BV>(ty: &Ty<Name>, shared_state: &SharedState<B>) -> Val<B> {
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
                Val::Enum(isla_lib::smt::EnumId::from_name(*enum_name).first_member())
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
fn get_assembly_name<B: BV>(
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

    let arg_value = if let Some(union_members) = instruction_union {
        // 查找当前构造函数的类型
        let ctor_ty = union_members.iter()
            .find(|(n, _ty)| *n == ctor_name)
            .map(|(_, ty)| ty);

        match ctor_ty {
            Some(Ty::Unit) => Val::Unit,
            Some(ty) => generate_default_value(ty, *shared_state),
            None => Val::Unit,
        }
    } else {
        Val::Unit
    };

    // 构造指令值
    let instr_value = Val::<B>::Ctor(ctor_name, Box::new(arg_value));

    // 执行 zassembly_forwards 函数
    match execute_ir_function("zassembly_forwards", &[instr_value], shared_state, regs, lets) {
        Some(Val::String(s)) => Some(s),
        _ => None,
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

    // 测试 get_assembly_name
    /* if let Some(assembly_name) = get_assembly_name::<B129>("zMRET", shared_state, regs) {
        println!("MRET 的汇编名称: {}", assembly_name);
    } */

    //
    let instruction_list = &shared_state.type_info;
    let instruction_id=shared_state.symtab.lookup("zinstruction");
    let MRET_id=shared_state.symtab.lookup("zMRET");
    // println!("ins_id={:?},MRET_id={:?}",instruction_id,MRET_id);
    // let instructions_union=shared_state.type_info.unions.get(  &shared_state.symtab.lookup("zinstruction")  ).unwrap();
    //let instruction_union_ctors=&shared_state.type_info.union_ctors;
    /* println!("{:?}",instructions_union.iter()
        .map(
            |(n,ty)| {
                (shared_state.symtab.to_str(*n), match ty {

                    isla_lib::ir::Ty::Enum(  ty_name) => isla_lib::ir::Ty::Enum(  shared_state.symtab.to_str(*ty_name)),
                    isla_lib::ir::Ty::Struct(ty_name) => isla_lib::ir::Ty::Struct(shared_state.symtab.to_str(*ty_name)),
                    isla_lib::ir::Ty::Union( ty_name) => isla_lib::ir::Ty::Union( shared_state.symtab.to_str(*ty_name)),
                    _ => isla_lib::ir::Ty::RoundingMode
                })
            }
        ).collect::<HashMap<_,_>>()
    ); */
    //println!("{:?}",instruction_union_ctors.iter().map(|e|{shared_state.symtab.to_str(*e)}).collect::<Vec<_>>() );

	//======

	println!("{:?}",
		shared_state.type_info.unions.get(  &shared_state.symtab.lookup("zinstruction")  ).unwrap()
            .iter().map(
                |(n,ty)| shared_state.symtab.to_str(*n)
            )
            .map(
                |s| get_assembly_name::<B129>(s, shared_state, regs, lets)
            )
            .collect::<Vec<_>>()
	);

    match subcommand {
        "list-instructions" => 0 /* cmd_list_instructions(matches, shared_state,regs,lets, iarch_config, source_path) */,
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
