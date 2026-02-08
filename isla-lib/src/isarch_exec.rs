use crate::bitvector::BV;
use crate::dprint::colors;
use crate::error::ExecError;
use crate::executor::{backtrace_string, LocalFrame, Run};
use crate::ir::UVal;
use crate::isarch::{self, get_assembly_name};
use crate::log;
use crate::primop_util::symbolic;
use crate::register::RegisterBindings;
use crate::smt::Solver;
use crate::smt::{checkpoint, Config, Context, Event, Model, ModelVal};
use crate::source_loc::SourceLoc;
use crate::zencode;
use crate::{ir::*, smt};
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

pub fn run_symbolic_execute<B: BV>(
    instruction_name: &str,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Option<String> {
    use crate::smt::checkpoint;

    // 查找指令的构造函数名称
    let ctor_name = shared_state.symtab.lookup(instruction_name);

    // 从 union 类型信息中获取构造函数的参数类型
    let instruction_union = shared_state.type_info.unions.get(&shared_state.symtab.lookup("zinstruction"));

    let Some(union_members) = instruction_union else {
        // zinstruction union 不存在
        panic!("run_symbolic_execute: 在symtab中没找到符号'zinstruction'");
    };

    // 查找当前构造函数的类型
    let Some((_, ctor_ty)) = union_members.iter().find(|(n, _ty)| *n == ctor_name) else {
        // 指令不在 zinstruction union 中（可能是其他架构的指令）
        return None;
    };

    let mut cfg = Config::new();
    cfg.set_param_value("model", "true");
    let ctx = Context::new(cfg);
    let mut solver = Solver::new(&ctx);

    let fun_args = vec![Val::<B>::Ctor(
        ctor_name,
        Box::new(symbolic(ctor_ty, shared_state, &mut solver, SourceLoc::unknown()).unwrap()),
    )];
    println!("fun_args:{:?}", fun_args);

    // 生成参数（暂时使用默认值，测试checkpoint机制）

    // 构造指令值

    // 创建checkpoint，包含符号化变量
    let cp = checkpoint(&mut solver);

    // 使用checkpoint执行函数
    let result: Arc<Mutex<Option<Val<B>>>> = Arc::new(Mutex::new(None));

    crate::executor::execute_ir_function_with_checkpoint_multi_thread(
        "zexecute",
        &fun_args,
        shared_state,
        regs,
        lets,
        &result,
        &|thread, _task_id, exec_result, shared_state, mut solver, collected| {
            match exec_result {
                Ok((run, frame)) => match run {
                    Run::Finished(ret_val) => {
                        println!(
                            "tid:{} 执行好一条路径，fork={}，ret_val={}",
                            thread,
                            frame.forks,
                            ret_val.to_str(shared_state)
                        );
                        /* let assembly = {
                            // 获取 zexecute 函数的参数信息
                            let execute_fn_id = shared_state.symtab.lookup("zexecute");
                            let (fn_args, _, _) = shared_state.functions.get(&execute_fn_id).unwrap();

                            // 提取第一个参数（指令）的值
                            match fn_args.first() {
                                Some((arg_name, _)) => {
                                    match frame.vars().get(arg_name) {
                                        // arg_val 就是指令的参数值
                                        Some(UVal::Init(arg_val)) => {
                                            println!("{:#?}", arg_val);
                                            isarch::get_assembly_name(arg_val.clone(), &shared_state, regs, lets)
                                        }
                                        _ => panic!(""),
                                    }
                                }
                                _ => panic!(""),
                            }
                        };
                        println!("assembly:{:#?}", assembly); */
                        // isarch::get_assembly_name(Val::Unit /* ??? */, &shared_state, regs, lets);

                        // 获取ISA状态（寄存器、lets变量等）
                        // 首先检查solver是否可满足
                        if solver.check_sat(SourceLoc::unknown()) == crate::smt::SmtResult::Sat {
                            if let Ok(mut model) =
                                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| Model::new(&solver)))
                            {
                                println!("=== ISA State (Thread {}) ===", thread);

                                // 遍历所有寄存器
                                for (reg_name, reg) in frame.regs().iter() {
                                    let reg_name_str = shared_state.symtab.to_str(*reg_name);
                                    if let Some(val) = reg.read_last_if_initialized() {
                                        match val {
                                            Val::Symbolic(sym) => match model.get_var(*sym) {
                                                Ok(crate::smt::ModelVal::Exp(crate::smt::smtlib::Exp::Bits64(bv))) => {
                                                    println!(
                                                        "  {} = 0x{:x} ({} bits)",
                                                        reg_name_str,
                                                        bv.lower_u64(),
                                                        bv.len()
                                                    );
                                                }
                                                Ok(crate::smt::ModelVal::Exp(crate::smt::smtlib::Exp::Bits(bv))) => {
                                                    let hex_str: String = bv
                                                        .chunks(4)
                                                        .rev()
                                                        .map(|chunk: &[bool]| {
                                                            let mut n = 0u8;
                                                            for (i, bit) in chunk.iter().enumerate() {
                                                                if *bit {
                                                                    n |= 1 << i;
                                                                }
                                                            }
                                                            format!("{:x}", n)
                                                        })
                                                        .collect();
                                                    println!("  {} = 0b{} ({} bits)", reg_name_str, hex_str, bv.len());
                                                }
                                                Ok(crate::smt::ModelVal::Exp(crate::smt::smtlib::Exp::Bool(b))) => {
                                                    println!("  {} = {}", reg_name_str, b);
                                                }
                                                Ok(crate::smt::ModelVal::Exp(crate::smt::smtlib::Exp::Enum(
                                                    member,
                                                ))) => {
                                                    let name = member.to_name(shared_state);
                                                    println!(
                                                        "  [enum]{} = {} | {:?}",
                                                        reg_name_str,
                                                        shared_state.symtab.to_str(name),
                                                        member
                                                    );
                                                }
                                                Ok(crate::smt::ModelVal::Arbitrary(ty)) => {
                                                    println!("  {} = <arbitrary: {:?}>", reg_name_str, ty);
                                                }
                                                Err(e) => {
                                                    println!("  {} = <error: {:?}>", reg_name_str, e);
                                                }
                                                _ => {
                                                    println!("  {} = {:?}", reg_name_str, val);
                                                }
                                            },
                                            Val::Bits(bv) => {
                                                println!("  {} = 0x{:x}", reg_name_str, bv.lower_u64());
                                            }
                                            Val::Bool(b) => {
                                                println!("  {} = {}", reg_name_str, b);
                                            }
                                            _ => {
                                                println!(
                                                    "  {} = {} | {:?}",
                                                    reg_name_str,
                                                    val.to_str(shared_state),
                                                    val
                                                );
                                            }
                                        }
                                    }
                                }

                                // 遍历lets中的特殊变量（如current_privilege等）
                                for (let_name, let_val) in frame.lets().iter() {
                                    let let_name_str = shared_state.symtab.to_str(*let_name);
                                    // 过滤掉一些内部变量
                                    if !let_name_str.starts_with("__") && let_name_str != "NULL" {
                                        match let_val {
                                            UVal::Init(Val::Symbolic(sym)) => match model.get_var(*sym) {
                                                Ok(crate::smt::ModelVal::Exp(crate::smt::smtlib::Exp::Bits64(bv))) => {
                                                    println!("  let {} = 0x{:x}", let_name_str, bv.lower_u64());
                                                }
                                                Ok(crate::smt::ModelVal::Exp(crate::smt::smtlib::Exp::Bits(bv))) => {
                                                    let hex_str: String = bv
                                                        .chunks(4)
                                                        .rev()
                                                        .map(|chunk: &[bool]| {
                                                            let mut n = 0u8;
                                                            for (i, bit) in chunk.iter().enumerate() {
                                                                if *bit {
                                                                    n |= 1 << i;
                                                                }
                                                            }
                                                            format!("{:x}", n)
                                                        })
                                                        .collect();
                                                    println!("  let {} = 0b{}", let_name_str, hex_str);
                                                }
                                                Ok(crate::smt::ModelVal::Exp(crate::smt::smtlib::Exp::Bool(b))) => {
                                                    println!("  let {} = {}", let_name_str, b);
                                                }
                                                Ok(crate::smt::ModelVal::Exp(crate::smt::smtlib::Exp::Enum(
                                                    member,
                                                ))) => {
                                                    let name = member.to_name(shared_state);
                                                    println!(
                                                        "  let {} = {}",
                                                        let_name_str,
                                                        shared_state.symtab.to_str(name)
                                                    );
                                                }
                                                _ => {}
                                            },
                                            UVal::Init(Val::Bits(bv)) => {
                                                println!("  let {} = 0x{:x}", let_name_str, bv.lower_u64());
                                            }
                                            UVal::Init(Val::Bool(b)) => {
                                                println!("  let {} = {}", let_name_str, b);
                                            }
                                            _ => {}
                                        }
                                    }
                                }

                                let mut events_vec = solver.trace().to_vec();
                                let events: Vec<Event<B>> = events_vec.drain(..).cloned().collect();
                                for event in events {
                                    match event {
                                        Event::Fork(fork_id, sym, branch_number, _) => {
                                            println!(" [event] Fork({}, {:?}, {}, _ )", fork_id, sym, branch_number)
                                        }
                                        _ => println!(" [event] {:?}", event),
                                    }
                                }
                                println!("==============================\n");
                            }
                            solver.dump_solver("solver.dump");
                        }

                        *collected.lock().unwrap() = Some(ret_val);
                    }
                    Run::Exit => println!("tid:{} 执行好一条路径，fork={}", thread, frame.forks),
                    Run::Dead => println!("tid:{} 执行好一条路径，fork={}", thread, frame.forks),

                    Run::Suspended => println!("tid:{} 执行好一条路径，fork={}", thread, frame.forks),
                },
                Err((error, backtrace)) => {
                    match &error {
                        ExecError::MatchFailure(_) => {
                            // 静默处理
                        }
                        _ => {
                            eprintln!("执行错误: {:?}", error);
                            eprintln!("调用栈: {:?}", backtrace_string(&backtrace, &shared_state.symtab));
                        }
                    }
                }
            }
        },
        cp,
    );

    // 提取字符串结果
    let res = match result.lock().unwrap().as_ref() {
        Some(Val::String(s)) => Some(s.clone()),
        Some(v) => {
            eprintln!("警告: zexecute 返回非字符串值: {:?}", v);
            None
        }
        None => None,
    };
    res
}

#[cfg(feature = "debug_exec")]
pub fn test_exec_main<B: BV>(shared_state: &SharedState<B>, regs: &RegisterBindings<B>, lets: &Bindings<B>) {
    println!("test_exec_main");

    run_symbolic_execute("zMRET", &shared_state, regs, lets);
}
