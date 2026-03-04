use crate::bitvector::BV;
use crate::dprint::{self, colors};
use crate::error::ExecError;
use crate::executor::{backtrace_string, LocalFrame, Run};
use crate::ir::UVal;
use crate::isarch::{self, get_assembly_name};
use crate::primop_util::symbolic;
use crate::register::RegisterBindings;
use crate::smt::{checkpoint, Config, Context, Event, Model, ModelVal};
use crate::smt::{Solver, Sym};
use crate::source_loc::SourceLoc;
use crate::zencode;
use crate::{dlog, log};
use crate::{ir::*, smt};
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

pub trait Target
where
    Self: Sync + Default,
{
    fn isa_state(&self) -> Vec<String> {
        vec![String::new()]
    }
}

// Marker trait 表示这是 RISC-V 架构
pub trait RISCV: Target {}

#[derive(Default)]
pub struct RISCV32 {}
#[derive(Default)]
pub struct RISCV64 {}

// 为所有 RISCV 类型提供默认实现
impl<T: RISCV> Target for T {
    fn isa_state(&self) -> Vec<String> {
        let mut regs: Vec<String> = (1..31).map(|r| format!("x{}", r)).collect();
        regs.extend((1..31).map(|r| format!("f{}", r)));
        regs.push("cur_privilege".to_string());
        regs
    }
}

// 标记为 RISCV 类型
impl RISCV for RISCV32 {}
impl RISCV for RISCV64 {}

pub fn run_symbolic_execute<B: BV>(
    instruction_name: &str,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Result<Option<String>, ExecError> {
    use crate::smt::checkpoint;

    let target = RISCV32::default();
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
        return Ok(None);
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
    println!("{:?}", target.isa_state());

    // 生成参数（暂时使用默认值，测试checkpoint机制）

    // 构造指令值

    // 创建checkpoint，包含符号化变量
    let cp = checkpoint(&mut solver);

    // 使用checkpoint执行函数，支持错误传播
    let result: Arc<Mutex<Result<Option<Val<B>>, ExecError>>> = Arc::new(Mutex::new(Ok(None)));

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
                                let test = Sym::from_u32(6);
                                // dlog!("model.get_var({:?})={:?}", test, model.get_var(test));
                                // dlog!("fun_args={:#?}", model.get_val(&fun_args[0]));
                                match model.get_val(&fun_args[0]) {
                                    Ok(arg_val) => {
                                        println!(
                                            "当前汇编：{:?}",
                                            isarch::get_assembly_name(arg_val, shared_state, regs, lets,),
                                        );
                                    }
                                    Err(e) => {
                                        *collected.lock().unwrap() = Err(e);
                                        return;
                                    }
                                }

                                // 遍历所有寄存器
                                for (reg_name, reg) in frame.regs().iter() {
                                    let reg_name_str: &str = shared_state.symtab.to_str(*reg_name);
                                    let reg_name_str: &str = &zencode::decode(reg_name_str);
                                    /* dlog!(
                                        "{}:(read_init_value_if_initialized){:?},(read_old_if_initialized){:?},(read_last_if_initialized){:?}",
                                        reg_name_str,
                                        reg.read_init_value_if_initialized(),
                                        reg.read_old_if_initialized(),
                                        reg.read_last_if_initialized()
                                    ); */

                                    // print reg
                                    /* if let Some(val) = reg.read_init_value_if_initialized() {
                                        match val {
                                            Val::Symbolic(sym) => {
                                                println!("  {} = {:?}", reg_name_str, model.get_var(*sym).unwrap());
                                            }
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
                                    } */
                                }

                                // 遍历lets中的特殊变量（如current_privilege等）
                                /* for (let_name, let_val) in frame.lets().iter() {
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
                                } */

                                // events
                                /* let mut events_vec = solver.trace().to_vec();
                                let events: Vec<Event<B>> = events_vec.drain(..).cloned().collect();
                                for event in events {
                                    match event {
                                        Event::Fork(fork_id, sym, branch_number, _) => {
                                            println!(
                                                " [event] Fork({}, {:?}, {}, _ )",
                                                fork_id,
                                                model.get_var(sym).unwrap(),
                                                branch_number
                                            )
                                        }
                                        _ => println!(" [event] {:?}", event),
                                    }
                                } */
                                println!("==============================\n");
                            }
                            solver.dump_solver("solver.dump");
                        }

                        *collected.lock().unwrap() = Ok(Some(ret_val));
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
                            eprintln!("调用栈: {}", backtrace_string(&backtrace, &shared_state.symtab));
                        }
                    }
                }
            }
        },
        cp,
    );

    // 提取字符串结果
    match Arc::try_unwrap(result).expect("result has multiple owners").into_inner().unwrap() {
        Ok(Some(Val::String(s))) => Ok(Some(s)),
        Ok(Some(v)) => {
            eprintln!("警告: zexecute 返回非字符串值: {:?}", v);
            Ok(None)
        }
        Ok(None) => Ok(None),
        Err(e) => Err(e),
    }
}

#[cfg(feature = "debug_exec")]
pub fn test_exec_main<B: BV>(shared_state: &SharedState<B>, regs: &RegisterBindings<B>, lets: &Bindings<B>) {
    use std::process::exit;

    println!("test_exec_main");
    /* match run_symbolic_execute("zLOAD", &shared_state, regs, lets) {
        Ok(_) => {}
        Err(e) => {
            eprintln!("test_exec_main: 运行错误 {}", e)
        }
    }; */
    // exit(0);

    let mut instruction_table = Vec::new();
    //能全部执行结束的
    let excute_through_instruction_table = [
        "zADDIW",
        "zAES32DSI",
        "zAES32DSMI",
        "zAES32ESI",
        "zAES32ESMI",
        "zAES64DS",
        "zAES64DSM",
        "zAES64ES",
        "zAES64ESM",
        "zAES64IM",
        "zAES64KS1I",
        "zAES64KS2",
        "zAMO",
        "zBITYPE",
        "zBREV8",
        "zBTYPE",
    ];
    // instruction_table.extend( excute_through_instruction_table.to_vec());

    //运行过程有问题的
    let failed_instruction_table = [
        /*
        zCLMUL的问题在于carryless_mul函数，这个函数用循环做了个无进位乘法。

        */
        "zCLMUL",
    ];
    instruction_table.extend(failed_instruction_table.to_vec());

    //待测试的
    let todo_instruction_table = [
        "zCLMULH",
        "zCLMULR",
        "zCLZ",
        "zCLZW",
        "zCPOP",
        "zCPOPW",
        "zCSRImm",
        "zCSRReg",
        "zCTZ",
        "zCTZW",
        "zC_ADD",
        "zC_ADDI",
        "zC_ADDI16SP",
        "zC_ADDI4SPN",
        "zC_ADDIW",
        "zC_ADDW",
        "zC_AND",
        "zC_ANDI",
        "zC_BEQZ",
        "zC_BNEZ",
        "zC_EBREAK",
        "zC_FLD",
        "zC_FLDSP",
        "zC_FLW",
        "zC_FLWSP",
        "zC_FSD",
        "zC_FSDSP",
        "zC_FSW",
        "zC_FSWSP",
        "zC_ILLEGAL",
        "zC_J",
        "zC_JAL",
        "zC_JALR",
        "zC_JR",
        "zC_LBU",
        "zC_LD",
        "zC_LDSP",
        "zC_LH",
        "zC_LHU",
        "zC_LI",
        "zC_LUI",
        "zC_LW",
        "zC_LWSP",
        "zC_MUL",
        "zC_MV",
        "zC_NOP",
        "zC_NOT",
        "zC_NTL",
        "zC_OR",
        "zC_SB",
        "zC_SD",
        "zC_SDSP",
        "zC_SEXT_B",
        "zC_SEXT_H",
        "zC_SH",
        "zC_SLLI",
        "zC_SRAI",
        "zC_SRLI",
        "zC_SUB",
        "zC_SUBW",
        "zC_SW",
        "zC_SWSP",
        "zC_XOR",
        "zC_ZEXT_B",
        "zC_ZEXT_H",
        "zC_ZEXT_W",
        "zDIV",
        "zDIVW",
        "zEBREAK",
        "zECALL",
        "zFCVTMOD_W_D",
        "zFCVT_BF16_S",
        "zFCVT_S_BF16",
        "zFENCE",
        "zFENCEI",
        "zFENCE_TSO",
        "zFLEQ_D",
        "zFLEQ_H",
        "zFLEQ_S",
        "zFLI_D",
        "zFLI_H",
        "zFLI_S",
        "zFLTQ_D",
        "zFLTQ_H",
        "zFLTQ_S",
        "zFMAXM_D",
        "zFMAXM_H",
        "zFMAXM_S",
        "zFMINM_D",
        "zFMINM_H",
        "zFMINM_S",
        "zFMVH_X_D",
        "zFMVP_D_X",
        "zFROUNDNX_D",
        "zFROUNDNX_H",
        "zFROUNDNX_S",
        "zFROUND_D",
        "zFROUND_H",
        "zFROUND_S",
        "zFVFMATYPE",
        "zFVFMTYPE",
        "zFVFTYPE",
        "zFVVMATYPE",
        "zFVVMTYPE",
        "zFVVTYPE",
        "zFWFTYPE",
        "zFWVFMATYPE",
        "zFWVFTYPE",
        "zFWVTYPE",
        "zFWVVMATYPE",
        "zFWVVTYPE",
        "zF_BIN_F_TYPE_D",
        "zF_BIN_F_TYPE_H",
        "zF_BIN_RM_TYPE_D",
        "zF_BIN_RM_TYPE_H",
        "zF_BIN_RM_TYPE_S",
        "zF_BIN_TYPE_F_S",
        "zF_BIN_TYPE_X_S",
        "zF_BIN_X_TYPE_D",
        "zF_BIN_X_TYPE_H",
        "zF_MADD_TYPE_D",
        "zF_MADD_TYPE_H",
        "zF_MADD_TYPE_S",
        "zF_UN_F_TYPE_D",
        "zF_UN_F_TYPE_H",
        "zF_UN_RM_FF_TYPE_D",
        "zF_UN_RM_FF_TYPE_H",
        "zF_UN_RM_FF_TYPE_S",
        "zF_UN_RM_FX_TYPE_D",
        "zF_UN_RM_FX_TYPE_H",
        "zF_UN_RM_FX_TYPE_S",
        "zF_UN_RM_XF_TYPE_D",
        "zF_UN_RM_XF_TYPE_H",
        "zF_UN_RM_XF_TYPE_S",
        "zF_UN_TYPE_F_S",
        "zF_UN_TYPE_X_S",
        "zF_UN_X_TYPE_D",
        "zF_UN_X_TYPE_H",
        "zILLEGAL",
        "zITYPE",
        "zJAL",
        "zJALR",
        "zLOAD",
        "zLOADRES",
        "zLOAD_FP",
        "zLPAD",
        "zMASKTYPEI",
        "zMASKTYPEV",
        "zMASKTYPEX",
        "zMMTYPE",
        "zMOVETYPEI",
        "zMOVETYPEV",
        "zMOVETYPEX",
        "zMRET",
        "zMUL",
        "zMULW",
        "zMVVCOMPRESS",
        "zMVVMATYPE",
        "zMVVTYPE",
        "zMVXMATYPE",
        "zMVXTYPE",
        "zNISTYPE",
        "zNITYPE",
        "zNTL",
        "zNVSTYPE",
        "zNVTYPE",
        "zNXSTYPE",
        "zNXTYPE",
        "zORCB",
        "zPAUSE",
        "zREM",
        "zREMW",
        "zREV8",
        "zRFVVTYPE",
        "zRFWVVTYPE",
        "zRIVVTYPE",
        "zRMVVTYPE",
        "zRORI",
        "zRORIW",
        "zRTYPE",
        "zRTYPEW",
        "zSFENCE_INVAL_IR",
        "zSFENCE_VMA",
        "zSFENCE_W_INVAL",
        "zSHA256SIG0",
        "zSHA256SIG1",
        "zSHA256SUM0",
        "zSHA256SUM1",
        "zSHA512SIG0",
        "zSHA512SIG0H",
        "zSHA512SIG0L",
        "zSHA512SIG1",
        "zSHA512SIG1H",
        "zSHA512SIG1L",
        "zSHA512SUM0",
        "zSHA512SUM0R",
        "zSHA512SUM1",
        "zSHA512SUM1R",
        "zSHIFTIOP",
        "zSHIFTIWOP",
        "zSINVAL_VMA",
        "zSLLIUW",
        "zSM3P0",
        "zSM3P1",
        "zSM4ED",
        "zSM4KS",
        "zSRET",
        "zSTORE",
        "zSTORECON",
        "zSTORE_FP",
        "zUNZIP",
        "zUTYPE",
        "zVABS_V",
        "zVAESDF",
        "zVAESDM",
        "zVAESEF",
        "zVAESEM",
        "zVAESKF1_VI",
        "zVAESKF2_VI",
        "zVAESZ_VS",
        "zVANDN_VV",
        "zVANDN_VX",
        "zVBREV8_V",
        "zVBREV_V",
        "zVCLMULH_VV",
        "zVCLMULH_VX",
        "zVCLMUL_VV",
        "zVCLMUL_VX",
        "zVCLZ_V",
        "zVCPOP_M",
        "zVCPOP_V",
        "zVCTZ_V",
        "zVEXTTYPE",
        "zVFIRST_M",
        "zVFMERGE",
        "zVFMV",
        "zVFMVFS",
        "zVFMVSF",
        "zVFNCVTBF16_F_F_W",
        "zVFNUNARY0",
        "zVFUNARY0",
        "zVFUNARY1",
        "zVFWCVTBF16_F_F_V",
        "zVFWMACCBF16_VF",
        "zVFWMACCBF16_VV",
        "zVFWUNARY0",
        "zVGHSH_VV",
        "zVGMUL_VV",
        "zVICMPTYPE",
        "zVID_V",
        "zVIMCTYPE",
        "zVIMSTYPE",
        "zVIMTYPE",
        "zVIOTA_M",
        "zVISG",
        "zVITYPE",
        "zVLRETYPE",
        "zVLSEGFFTYPE",
        "zVLSEGTYPE",
        "zVLSSEGTYPE",
        "zVLXSEGTYPE",
        "zVMSBF_M",
        "zVMSIF_M",
        "zVMSOF_M",
        "zVMTYPE",
        "zVMVRTYPE",
        "zVMVSX",
        "zVMVXS",
        "zVREV8_V",
        "zVROL_VV",
        "zVROL_VX",
        "zVROR_VI",
        "zVROR_VV",
        "zVROR_VX",
        "zVSETIVLI",
        "zVSETVL",
        "zVSETVLI",
        "zVSHA2MS_VV",
        "zVSM3C_VI",
        "zVSM3ME_VV",
        "zVSM4K_VI",
        "zVSRETYPE",
        "zVSSEGTYPE",
        "zVSSSEGTYPE",
        "zVSXSEGTYPE",
        "zVVCMPTYPE",
        "zVVMCTYPE",
        "zVVMSTYPE",
        "zVVMTYPE",
        "zVVTYPE",
        "zVWSLL_VI",
        "zVWSLL_VV",
        "zVWSLL_VX",
        "zVXCMPTYPE",
        "zVXMCTYPE",
        "zVXMSTYPE",
        "zVXMTYPE",
        "zVXSG",
        "zVXTYPE",
        "zWFI",
        "zWMVVTYPE",
        "zWMVXTYPE",
        "zWRS",
        "zWVTYPE",
        "zWVVTYPE",
        "zWVXTYPE",
        "zWXTYPE",
        "zXPERM4",
        "zXPERM8",
        "zZBA_RTYPE",
        "zZBA_RTYPEUW",
        "zZBB_EXTOP",
        "zZBB_RTYPE",
        "zZBB_RTYPEW",
        "zZBKB_PACKW",
        "zZBKB_RTYPE",
        "zZBS_IOP",
        "zZBS_RTYPE",
        "zZCMOP",
        "zZICBOM",
        "zZICBOP",
        "zZICBOZ",
        "zZICOND_RTYPE",
        "zZIMOP_MOP_R",
        "zZIMOP_MOP_RR",
        "zZIP",
        "zZVABDTYPE",
        "zZVKSHA2TYPE",
        "zZVKSM4RTYPE",
        "zZVWABDATYPE",
    ];
    // instruction_table.extend( todo_instruction_table.to_vec());

    for ins_name in instruction_table {
        match run_symbolic_execute(ins_name, &shared_state, regs, lets) {
            Ok(_) => {}
            Err(e) => {
                eprintln!("test_exec_main: 运行错误 {}", e)
            }
        };
    }
}
