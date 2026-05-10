use crate::isarch::{self as isarch};
use isla_lib::bitvector::BV;
use isla_lib::error::ExecError;
use isla_lib::error::IslaError;
use isla_lib::executor::{backtrace_string, Run};
use isla_lib::executor::{ExecutionLimits, LimitBehavior, TaskState};
use isla_lib::fmtval::FmtVal;
use isla_lib::ir::UVal;
use isla_lib::ir::*;
use isla_lib::primop_util::symbolic;
use isla_lib::register::RegisterBindings;
use isla_lib::smt::{Config, Context, Model};
use isla_lib::smt::{Solver, Sym};
use isla_lib::source_loc::SourceLoc;
use isla_lib::zencode;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use std::sync::{Arc, Mutex};

#[macro_export]
macro_rules! hashmap {
    // 空 map
    () => {
        ::std::collections::HashMap::new()
    };

    // 单个键值对，无尾随逗号
    ($key:tt: $value:expr) => {{
        let mut _map = ::std::collections::HashMap::new();
        _map.insert($key, $value);
        _map
    }};

    // 多个键值对，支持尾随逗号
    ($($key:tt: $value:expr),+ $(,)?) => {{
        let mut _map = ::std::collections::HashMap::new();
        $(
            _map.insert($key, $value);
        )+
        _map
    }};
}

pub trait Target
where
    Self: Sync,
{
    fn arch_name(&self) -> &'static str;
    fn arch_pretty_name(&self) -> &'static str;
    fn xlen(&self) -> &'static str;
    fn isa_state_list(&self) -> Vec<String>;
}

// Marker trait 表示这是 RISC-V 架构
pub trait RISCV: Target {
    fn xlen_bits(&self) -> &'static str;
    fn xlen_name(&self) -> &'static str;
}

// 为所有 RISCV 类型提供默认实现
impl<T: RISCV> Target for T {
    fn arch_name(&self) -> &'static str {
        "riscv"
    }

    fn arch_pretty_name(&self) -> &'static str {
        self.xlen_name()
    }

    fn xlen(&self) -> &'static str {
        self.xlen_bits()
    }

    fn isa_state_list(&self) -> Vec<String> {
        let mut regs: Vec<String> = (0..32).map(|r| format!("x{}", r)).collect();
        regs.extend((0..32).map(|r| format!("f{}", r)));
        regs.push("PC".to_string());
        regs.push("cur_privilege".to_string());
        regs.extend(["mstatus".to_string()]);
        regs
    }
}

/// 根据 xlen 值动态选择 RISC-V target
pub enum RISCVTarget {
    RV32,
    RV64,
}

impl RISCVTarget {
    pub fn from_xlen(xlen: u32) -> Self {
        match xlen {
            32 => RISCVTarget::RV32,
            64 => RISCVTarget::RV64,
            _ => panic!("from_xlen(xlen={xlen})的值不是64或者32的其中一个，你是不是IR文件选错了或者配置给错了?"),
        }
    }
}

impl RISCV for RISCVTarget {
    fn xlen_bits(&self) -> &'static str {
        match self {
            RISCVTarget::RV32 => "32",
            RISCVTarget::RV64 => "64",
        }
    }

    fn xlen_name(&self) -> &'static str {
        match self {
            RISCVTarget::RV32 => "rv32d",
            RISCVTarget::RV64 => "rv64d",
        }
    }
}

#[allow(non_camel_case_types)]
#[derive(Serialize, Deserialize)]
struct AssemGen_Json_Item {
    arch: BTreeMap<String, String>,
    #[serde(rename = "test-ins")]
    test_ins: String,
    #[serde(rename = "test-ins-encdec")]
    test_ins_encdec: String,
    #[serde(rename = "isa-state")]
    isa_state: BTreeMap<String, String>,
    ret_val: String,
}
impl AssemGen_Json_Item {
    pub fn new<T: Target>(
        target: &T,
        test_ins: String,
        test_ins_encdec: String,
        isa_state: BTreeMap<String, String>,
        ret_val: String,
    ) -> Self {
        let mut arch = BTreeMap::new();
        arch.insert("pretty-name".to_string(), target.arch_pretty_name().to_string());
        arch.insert("name".to_string(), target.arch_name().to_string());
        arch.insert("xlen".to_string(), target.xlen().to_string());
        arch.insert("ext".to_string(), "IMACFD".to_string());
        AssemGen_Json_Item { arch, test_ins, test_ins_encdec, isa_state, ret_val }
    }
}
trait ToJSON: Serialize {
    #[allow(dead_code)]
    fn to_json_str(&self) -> String {
        serde_json::to_string_pretty(self).unwrap()
    }
    fn to_json(&self, file_path: Option<String>) {
        let json = serde_json::to_string_pretty(self).unwrap();
        // 若未指定输出路径，则默认写到当前目录下的 assem_gen.json
        let path = file_path.unwrap_or_else(|| "assem_gen.json".to_string());
        // 支持类似 "output/a/b.json" 的路径：先提取父目录并递归创建（等价 mkdir -p）
        if let Some(parent) = Path::new(&path).parent() {
            // parent 可能为空（例如仅文件名 "a.json"），空路径时无需创建目录
            if !parent.as_os_str().is_empty() {
                fs::create_dir_all(parent).unwrap();
            }
        }
        // 目录准备好之后再写文件
        fs::write(path, json).unwrap();
    }
}
#[allow(non_camel_case_types)]
#[derive(Serialize, Deserialize)]
struct AssemGen_Json {
    gen: Vec<AssemGen_Json_Item>,
}
impl ToJSON for AssemGen_Json {}
impl ToJSON for AssemGen_Json_Item {}
impl AssemGen_Json {
    fn new(gen: Vec<AssemGen_Json_Item>) -> Self {
        AssemGen_Json { gen }
    }
}

#[allow(non_snake_case)]
fn symbolic_args_from_TYPEs<B: BV>(
    instruction_name: &str,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
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
        return Err(ExecError::Type(
            format!("指令 '{}' 不在 zinstruction union 中", instruction_name),
            SourceLoc::unknown(),
        ));
    };

    //hook: zSTORE
    if instruction_name == "zSTORE" {
        eprintln!("hook(zSTORE):ctor_ty={:#?}", ctor_ty);
    }

    let mut ret_val = symbolic(ctor_ty, shared_state, solver, SourceLoc::unknown())?;

    //hook: zSTORE

    let hook_overwrite_map = hashmap! {
        "zSTORE":hashmap!{
            "tuple#%bv12_%bv5_%bv5_%i643":"I64(4)"
        },
        "zLOAD":hashmap!{
            "tuple#%bv12_%bv5_%bv5_%bool_%i644":"I64(4)"
        }
    };
    // 当在hook_overwrite_map表中发现了要hook的名字，并获取要覆写的参数字段，比如zSTORE.keys()
    if let Some(zTYPE_name_map) = hook_overwrite_map.get(instruction_name) {
        for (&target_arg_type, &target_arg_value) in zTYPE_name_map {
            //hook: 检查类型名 ztuplez3z5bv12_z5bv5_z5bv5_z5i643
            let target_arg_ztype = zencode::encode(target_arg_type);
            match &mut ret_val {
                Val::Struct(name) => {
                    name.iter_mut().for_each(|(n, v)| {
                        let field_name = shared_state.symtab.to_str(*n);

                        if field_name == target_arg_ztype {
                            *v = Val::from_str(target_arg_value, shared_state).unwrap();
                            eprintln!("hook(field_name={target_arg_ztype}): value={:#?}", v);
                        }
                    });
                }
                _ => panic!("未预期类型的ret_val: {:?}", ret_val),
            }
            eprintln!("hook:ret_val={:#?}", ret_val);
        }
    }

    Ok(ret_val)
}
pub fn run_symbolic_execute<B: BV>(
    instruction_name: &str,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Result<Option<String>, ExecError> {
    use isla_lib::smt::checkpoint;

    // 从 lets 绑定中读取 zxlen 值
    let xlen = shared_state
        .symtab
        .get("zxlen")
        .and_then(|name| lets.get(&name))
        .and_then(|uval| match uval {
            UVal::Init(Val::I64(n)) => Some(*n as u32),
            _ => None,
        })
        .unwrap();
    let target = RISCVTarget::from_xlen(xlen);
    let mut cfg = Config::new();
    cfg.set_param_value("model", "true");
    let ctx = Context::new(cfg);
    let mut solver = Solver::new(&ctx);

    // 使用 symbolic_args_from_TYPEs 生成符号化参数
    let ctor_name = shared_state.symtab.lookup(instruction_name);

    let fun_args = vec![Val::<B>::Ctor(
        ctor_name,
        Box::new(symbolic_args_from_TYPEs(instruction_name, shared_state, regs, lets, &mut solver)?),
    )];
    println!("fun_args:{:?}", fun_args);
    println!("{:?}", target.isa_state_list());

    // 生成参数（暂时使用默认值，测试checkpoint机制）

    // 构造指令值

    // 创建checkpoint，包含符号化变量
    let cp = checkpoint(&mut solver);

    // 执行限制配置（三道防线，OR 关系，任一触发即执行 on_limit_reached）：
    //
    // 1) max_total_forks=8       — 硬上限：全局 fork 总数，防止状态爆炸
    // 2) max_forks_per_branch=2  — 硬上限：单个分支点最多 fork 2 次
    // 3) max_fork_pct_per_branch=0.1 — 自适应：单个分支点的 fork 数不得超过全局的 10%
    //    与 KLEE 的 MaxStaticForkPct 一致，自动抑制占比过高的"热点"分支。
    //    max_fork_pct_check_delay=100：前 100 次 fork 跳过百分比检查（热身期），
    //    避免初始阶段 total_forks 过小导致任何分支点占比都接近 100% 而误杀。
    //
    // 其他限制：
    // - max_backjumps_per_loop=10 — 循环回边次数上限，超过即视为无限循环
    // - max_path_depth=10000     — IR 指令步数上限，防止单条路径过长
    // - on_limit_reached=Concretize — 触发限制时具体化符号条件继续执行，而非截断路径
    let limits = ExecutionLimits::default()
        .with_max_forks_per_branch(2)
        .with_max_total_forks(8)
        .with_max_backjumps_per_loop(10)
        .with_max_path_depth(10000)
        .with_max_fork_pct_per_branch(0.1)
        .with_max_fork_pct_check_delay(100)
        .with_limit_behavior(LimitBehavior::Concretize);
    let task_state = TaskState::new().with_execution_limits(limits);

    // 使用checkpoint执行函数，支持错误传播
    let result: Arc<Mutex<AssemGen_Json>> = Arc::new(Mutex::new(AssemGen_Json::new(Vec::new())));

    isla_lib::executor::execute_ir_function_with_checkpoint_and_limits(
        "zexecute",
        &fun_args,
        shared_state,
        regs,
        lets,
        &result,
        &|thread, _task_id, exec_result, shared_state, mut solver, collected| {
            match exec_result {
                Ok((run, frame)) => match run {
                    Run::Finished(Val::Poison) => {
                        eprintln!("警告: {}这个Ctor返回值是Poison，可能是相关扩展（如H扩展）造成的，因此产生了sail的_inner_error_",instruction_name)
                    }
                    Run::Finished(ret_val) => {
                        println!(
                            "1. tid:{} 执行好一条路径，fork={}，ret_val={}",
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

                        let mut test_ins = String::new();
                        let mut test_ins_encdec = String::new();
                        let mut isa_state: BTreeMap<String, String> = BTreeMap::new();
                        // 获取ISA状态（寄存器、lets变量等）
                        // 首先检查solver是否可满足
                        if solver.check_sat(SourceLoc::unknown()) == isla_lib::smt::SmtResult::Sat {
                            if let Ok(mut model) =
                                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| Model::new(&solver)))
                            {
                                println!("2. === ISA State (Thread {}) ===", thread);
                                let test = Sym::from_u32(6);
                                // dlog!("model.get_var({:?})={:?}", test, model.get_var(test));
                                // dlog!("fun_args={:#?}", model.get_val(&fun_args[0]));
                                match model.get_val(&fun_args[0]) {
                                    Ok(arg_val) => {
                                        let asm_opt =
                                            isarch::get_assembly_name(arg_val.clone(), shared_state, regs, lets);
                                        println!("当前汇编：{:?}", asm_opt);
                                        match asm_opt {
                                            Some(asm) => test_ins = asm,
                                            None => return,
                                        }
                                        let asm_encdec_opt =
                                            isarch::get_assembly_encdec(arg_val.clone(), shared_state, regs, lets);
                                        let asm_encdec_opt = asm_encdec_opt.map(|val| {
                                            FmtVal::from_val(&val, &mut model).unwrap().to_str(shared_state)
                                        });
                                        println!("当前汇编encdec：{:?}", asm_encdec_opt);
                                        match asm_encdec_opt {
                                            Some(encdec) => test_ins_encdec = encdec,
                                            None => return,
                                        }
                                    }
                                    Err(e) => {
                                        eprintln!("警告: {}没有汇编 {:?}", instruction_name, e);
                                        //*collected.lock().unwrap() = Err(e);
                                        return;
                                    }
                                }

                                // 遍历所有寄存器
                                for (reg_name, reg) in frame.regs().iter() {
                                    let reg_name_str: &str = shared_state.symtab.to_str(*reg_name);
                                    let reg_name_decoded = zencode::decode(reg_name_str);
                                    /* dlog!(
                                        "{}:(read_init_value_if_initialized){:?},(read_old_if_initialized){:?},(read_last_if_initialized){:?}",
                                        reg_name_str,
                                        reg.read_init_value_if_initialized(),
                                        reg.read_old_if_initialized(),
                                        reg.read_last_if_initialized()
                                    ); */

                                    // print reg
                                    let filter_list = ["pma_regions", "tlb"];
                                    if filter_list.contains(&reg_name_decoded.as_str())
                                        || reg_name_decoded.starts_with("__")
                                        || reg_name_decoded.starts_with("htif_")
                                    {
                                        continue;
                                    };
                                    if let Some(val) = reg.read_init_value_if_initialized() {
                                        let formatted = model
                                            .get_fmtval(val)
                                            .map(|fmt_val| fmt_val.to_str(shared_state))
                                            .unwrap_or_else(|_| val.to_str(shared_state));
                                        let fv = model.get_fmtval(val);
                                        match fv {
                                            Err(exec_error) => continue,
                                            Ok(fmt_val) => {
                                                // println!("  {} = {}", reg_name_decoded, formatted);
                                                if fmt_val.is_arbitrary() {
                                                    continue;
                                                }

                                                if target.isa_state_list().contains(&reg_name_decoded.to_string()) {
                                                    let formatted = fmt_val.to_str(shared_state);
                                                    isa_state.insert(reg_name_decoded.to_string(), formatted.clone());
                                                }
                                            }
                                        }
                                    }
                                }

                                println!("isa_state={}", serde_json::to_string_pretty(&isa_state).unwrap());
                                // 遍历lets中的特殊变量（如current_privilege等）
                                /* for (let_name, let_val) in frame.lets().iter() {
                                    let let_name_str = shared_state.symtab.to_str(*let_name);
                                    // 过滤掉一些内部变量
                                    if !let_name_str.starts_with("__") && let_name_str != "NULL" {
                                        match let_val {
                                            UVal::Init(Val::Symbolic(sym)) => match model.get_var(*sym) {
                                                Ok(isla_lib::smt::ModelVal::Exp(isla_lib::smt::smtlib::Exp::Bits64(bv))) => {
                                                    println!("  let {} = 0x{:x}", let_name_str, bv.lower_u64());
                                                }
                                                Ok(isla_lib::smt::ModelVal::Exp(isla_lib::smt::smtlib::Exp::Bits(bv))) => {
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
                                                Ok(isla_lib::smt::ModelVal::Exp(isla_lib::smt::smtlib::Exp::Bool(b))) => {
                                                    println!("  let {} = {}", let_name_str, b);
                                                }
                                                Ok(isla_lib::smt::ModelVal::Exp(isla_lib::smt::smtlib::Exp::Enum(
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
                                println!("3. ==============================\n");
                            }
                            solver.dump_solver("solver.dump");
                        }
                        let single_instruction_json = AssemGen_Json_Item::new(
                            &target,
                            test_ins,
                            test_ins_encdec,
                            isa_state,
                            ret_val.to_str(shared_state).to_string(),
                        );
                        let mut instruction_json = collected.lock().unwrap();
                        instruction_json.gen.push(single_instruction_json);
                    }
                    Run::Exit => println!("tid:{} 执行好一条路径(Exit)，fork={}", thread, frame.forks),
                    Run::Dead => println!("tid:{} 执行好一条路径(Dead)，fork={}", thread, frame.forks),

                    Run::Suspended => println!("tid:{} 执行好一条路径(Suspended)，fork={}", thread, frame.forks),
                },
                Err((error, backtrace)) => {
                    match &error {
                        ExecError::MatchFailure(_) => {
                            // 静默处理
                        }
                        _ => {
                            eprintln!(
                                "执行错误: {}({:?})[{}]",
                                error,
                                error,
                                error.source_loc().location_string(shared_state.symtab.files())
                            );
                            eprintln!("调用栈: {}", backtrace_string(&backtrace, &shared_state.symtab));
                        }
                    }
                }
            }
        },
        cp,
        task_state,
    );

    // 提取字符串结果
    if let Ok(result_mutex) = Arc::try_unwrap(result) {
        let xlen_name = target.xlen_name();
        result_mutex.lock().unwrap().to_json(Some(format!("output/{}_{}.json", xlen_name, instruction_name)));
        Ok(None)
    } else {
        eprintln!("警告: {}无法获取 result 收集器", instruction_name);
        Ok(None)
    }
}

#[cfg(feature = "debug_exec")]
pub fn test_exec_main<B: BV>(shared_state: &SharedState<B>, regs: &RegisterBindings<B>, lets: &Bindings<B>) {
    println!("test_exec_main");
    /* match run_symbolic_execute("zLOAD", &shared_state, regs, lets) {
        Ok(_) => {}
        Err(e) => {
            eprintln!("test_exec_main: 运行错误 {}", e)
        }
    }; */
    // exit(0);

    let mut instruction_table: Vec<&str> = Vec::new();
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
    // instruction_table.extend(failed_instruction_table.to_vec());

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

    let ext_i_instruction_table = [
        "zADDIW",
        "zBTYPE",
        "zEBREAK",
        "zECALL",
        "zFENCE",
        "zFENCE_TSO",
        "zITYPE",
        "zJAL",
        "zJALR",
        // "zLOAD",
        "zMRET",
        "zRTYPE",
        "zRTYPEW",
        "zSFENCE_VMA",
        "zSHIFTIOP",
        "zSHIFTIWOP",
        "zSRET",
        // "zSTORE",
        "zUTYPE",
        "zWFI",
    ];
    // instruction_table.extend(ext_i_instruction_table.to_vec());

    let ext_m_instruction_table = ["MUL", "DIV", "REM", "MULW", "DIVW", "REMW"]
        .into_iter()
        .map(|name| zencode::encode(name))
        .collect::<Vec<String>>();
    // instruction_table.extend(ext_m_instruction_table.iter().map(|name| name.as_str()).collect::<Vec<&str>>());

    /*     let ext_a_instruction_table =
        ["AMO", "LOADRES", "STORECON"].into_iter().map(|name| zencode::encode(name)).collect::<Vec<String>>();
    instruction_table.extend(ext_a_instruction_table.iter().map(|name| name.as_str()).collect::<Vec<&str>>()); */

    let ext_c_instruction_table = [
        "C_NOP",
        "C_ADDI4SPN",
        "C_LW",
        "C_LD",
        "C_SW",
        "C_SD",
        "C_ADDI",
        "C_JAL",
        "C_ADDIW",
        "C_LI",
        "C_ADDI16SP",
        "C_LUI",
        "C_SRLI",
        "C_SRAI",
        "C_ANDI",
        "C_SUB",
        "C_XOR",
        "C_OR",
        "C_AND",
        "C_SUBW",
        "C_ADDW",
        "C_J",
        "C_BEQZ",
        "C_BNEZ",
        "C_SLLI",
        "C_LWSP",
        "C_LDSP",
        "C_SWSP",
        "C_SDSP",
        "C_JR",
        "C_JALR",
        "C_MV",
        "C_EBREAK",
        "C_ADD",
        "C_LBU",
        "C_LHU",
        "C_LH",
        "C_SB",
        "C_SH",
        "C_ZEXT_B",
        "C_SEXT_B",
        "C_ZEXT_H",
        "C_SEXT_H",
        "C_ZEXT_W",
        "C_NOT",
        "C_MUL",
    ]
    .into_iter()
    .map(|name| zencode::encode(name))
    .collect::<Vec<String>>();
    // instruction_table.extend(ext_c_instruction_table.iter().map(|name| name.as_str()).collect::<Vec<&str>>());

    // instruction_table.extend(vec!["zLOAD"]);

    let excute_through_instruction_table = ["zSTORE", "zLOAD"];
    instruction_table.extend(excute_through_instruction_table.to_vec());

    for ins_name in instruction_table {
        match run_symbolic_execute(ins_name, &shared_state, regs, lets) {
            Ok(_) => {}
            Err(e) => {
                eprintln!("test_exec_main: {}运行错误 {}", ins_name, e)
            }
        };
    }
}
