use crate::bitvector::BV;
use crate::config::ISAConfig;
use crate::dprint::colors;
use crate::error::ExecError;
use crate::executor::{
    backtrace_string, execute_ir_function, start_single, Collector, LocalFrame, Run, TaskId, TaskState,
};
use crate::ir::UVal;
use crate::isarch_args::{ArgStruct, InstructionMap};
use crate::log;
use crate::primop_util::symbolic;
use crate::register::RegisterBindings;
use crate::smt::{checkpoint, Config, Context, EnumMember, Model};
use crate::smt::{Checkpoint, Event, Solver, Sym};
use crate::source_loc::SourceLoc;
use crate::{d2, dlog, zencode};
use crate::{ir::*, smt};
use sha2::digest::generic_array::functional::FunctionalSequence;
use std::collections::{HashMap, HashSet};
use std::str::FromStr;
use std::sync::{Arc, Mutex, Weak};

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
        panic!("get_assembly_name: 在symtab中没找到符号'zinstruction'");
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
        &|thread, _task_id, exec_result, shared_state, solver, collected| {
            match exec_result {
                Ok((run, frame)) => match run {
                    Run::Finished(ret_val) => {
                        println!(
                            "tid:{} 执行好一条路径，fork={}，ret_val={}",
                            thread,
                            frame.forks,
                            ret_val.to_str(shared_state)
                        );
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
            eprintln!("警告: zassembly_forwards 返回非字符串值: {:?}", v);
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
