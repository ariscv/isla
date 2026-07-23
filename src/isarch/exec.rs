use super::clause::{get_extension_clauses, normalize_clause_name};
use super::target::{Target, RISCV};
use super::{get_all_clause_names, get_assembly_encdec, get_assembly_name, list_instructions};
use isla_lib::bitvector::BV;
use isla_lib::config::ExecutionLimitsConfig;
use isla_lib::error::ExecError;
use isla_lib::error::IslaError;
use isla_lib::executor::{backtrace_string, Run};
use isla_lib::executor::{ExecutionLimits, LimitBehavior, TaskState};
use isla_lib::fmtval::FmtVal;
use isla_lib::ir::*;
use isla_lib::log;
use isla_lib::primop_util::symbolic;
use isla_lib::register::RegisterBindings;
use isla_lib::smt::{Config, Context, Model};
use isla_lib::smt::{Solver, Sym};
use isla_lib::source_loc::{SourceLoc, SourceRegionSpec};
use isla_lib::zencode;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

#[allow(non_camel_case_types)]
#[derive(Serialize, Deserialize)]
struct AssemGenJsonItem {
    arch: BTreeMap<String, String>,
    #[serde(rename = "test-ins")]
    test_ins: String,
    #[serde(rename = "test-ins-encdec")]
    test_ins_encdec: String,
    #[serde(rename = "isa-state")]
    isa_state: BTreeMap<String, String>,
    ret_val: String,
}
impl AssemGenJsonItem {
    pub fn new<B: BV>(
        target: &dyn Target<B>,
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
        AssemGenJsonItem { arch, test_ins, test_ins_encdec, isa_state, ret_val }
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
struct AssemGenJson {
    gen: Vec<AssemGenJsonItem>,
}
impl ToJSON for AssemGenJson {}
impl ToJSON for AssemGenJsonItem {}
impl AssemGenJson {
    fn new(gen: Vec<AssemGenJsonItem>) -> Self {
        AssemGenJson { gen }
    }
}

fn should_collect_unfinished_path<B: BV>(run: &Run<B>) -> bool {
    !matches!(run, Run::Dead)
}

fn solve_execution_limits(symtab: &Symtab, config: Option<&ExecutionLimitsConfig>) -> ExecutionLimits {
    const GATHER_SOURCE_FILE: &str = "extensions/V/vext_arith_insts.sail";

    // 执行限制配置：局部 branch/loop 预算负责压制路径规模；达到预算后按固定 seed
    // 可复现抽样一侧继续执行，而不是固定选择 true 或直接丢弃整条路径。
    //
    // - max_forks_per_branch=2：每个 (函数, IR PC, 最近两层调用点, SourceLoc) 最多实际 fork 2 次；
    //   后续访问成对均衡地抽样 true/false，避免循环热点吃光深层分支预算。
    // - max_forks_per_path=None：不设置全局 path fork 上限，避免在 SourceLoc region 之外裁剪路径。
    // - max_backjumps_per_loop=None：当前只限制下面四个 gather 条件分支，不提前退出有界 vector 循环。
    // - max_path_depth=None：不使用全局路径深度限制，区域外控制流保持完整遍历。
    // - regions：只选择两个 gather 指令的 mask 和 idx < VLMAX 逐元素热点；constructor、编码 guard、
    //   合法性检查与主 match 保持完整展开，避免影响 VVTYPE 指令种类覆盖。
    let default_region_specs = [
        // VV_VRGATHER：逐元素 mask 分支。
        SourceRegionSpec::new(GATHER_SOURCE_FILE, (186, 6), (192, 7)),
        // VV_VRGATHER：逐元素 idx < VLMAX 分支。
        SourceRegionSpec::new(GATHER_SOURCE_FILE, (191, 20), (191, 65)),
        // VV_VRGATHEREI16：逐元素 mask 分支。
        SourceRegionSpec::new(GATHER_SOURCE_FILE, (195, 6), (201, 7)),
        // VV_VRGATHEREI16：逐元素 idx < VLMAX 分支。
        SourceRegionSpec::new(GATHER_SOURCE_FILE, (200, 20), (200, 65)),
    ];
    let limits = ExecutionLimits::default()
        .with_max_forks_per_branch(2)
        .with_limit_behavior(LimitBehavior::Concretize)
        .with_region_specs(&default_region_specs, symtab);

    // TOML 中出现的字段逐项覆盖代码默认策略；regions 出现时整体替换默认 SourceRegion 集合。
    match config {
        Some(config) => limits.with_config(config, symtab),
        None => limits,
    }
}

/// 基于用户指定的 itrace 基路径和 clause 名，生成每个 clause 独立的输出文件路径。
/// 规则：`output/itrace.txt` + clause `zadd` → `output/itrace_zadd.txt`
#[cfg(feature = "itrace")]
fn clause_itrace_output_path(base_path: &Path, clause: &str) -> PathBuf {
    let stem = base_path.file_stem().and_then(|s| s.to_str()).unwrap_or("itrace");
    let extension = base_path.extension().and_then(|s| s.to_str()).unwrap_or("txt");
    let new_name = format!("{}_{}.{}", stem, clause, extension);
    base_path.with_file_name(new_name)
}

/// solve-state 子命令的主入口函数
/// 支持通过 clause 名、扩展名、汇编指令名或 --all 来筛选需要符号执行的 clause
pub fn solve_state_main<'ir, B: BV>(
    shared_state: &SharedState<'ir, B>,
    regs: &'ir RegisterBindings<'ir, B>,
    lets: &'ir Bindings<'ir, B>,
    initial_memory: Option<isla_lib::memory::Memory<B>>,
    target: &mut dyn RISCV<B>,
    clauses: &[String],
    extensions: &[String],
    instruction_names: &[String],
    run_all: bool,
    itrace_path: Option<PathBuf>,
    ir_file_path: Option<PathBuf>,
    num_threads: usize,
    timeout: Option<u64>,
    execution_limits_config: Option<&ExecutionLimitsConfig>,
) -> bool {
    let mut clause_set: HashSet<String> = HashSet::new();
    let mut success = true;

    // 添加显式指定的 clause
    clause_set.extend(clauses.iter().map(|clause| normalize_clause_name(clause)));

    // 添加扩展对应的 clause
    for ext in extensions {
        let ext_clauses = get_extension_clauses(ext);
        if ext_clauses.is_empty() {
            log!(log::SYM_EXEC, &format!("警告: 未知扩展 '{}'", ext));
            success = false;
        }
        clause_set.extend(ext_clauses);
    }

    // 根据汇编指令名查找对应的 clause
    if !instruction_names.is_empty() {
        let instruction_map = list_instructions(shared_state, regs, lets);
        for inst_name in instruction_names {
            let mut found = false;
            for (clause_display_name, names) in &instruction_map {
                if names.iter().any(|n| n == inst_name) {
                    clause_set.insert(zencode::encode(clause_display_name));
                    found = true;
                }
            }
            if !found {
                log!(log::SYM_EXEC, &format!("警告: 未找到指令 '{}' 对应的 clause", inst_name));
                success = false;
            }
        }
    }

    // --all 模式：执行所有 clause
    if run_all {
        clause_set.extend(get_all_clause_names(shared_state));
    }

    #[cfg(not(feature = "itrace"))]
    let _ = (&itrace_path, &ir_file_path);

    #[cfg(feature = "itrace")]
    if itrace_path.is_some() && ir_file_path.is_none() {
        panic!("itrace: 使用 --itrace 时必须同时指定 --arch/-A 提供 IR 文件路径");
    }

    if clause_set.is_empty() {
        eprintln!("错误: 未指定任何要符号执行的 clause");
        eprintln!("请使用 --clause, --extension, --instruction-name 或 --all 指定");
        return false;
    }

    let num_clauses = clause_set.len();
    log!(log::SYM_EXEC, &format!("solve_state: 共 {} 个 clause 待执行", num_clauses));
    let execution_limits = solve_execution_limits(&shared_state.symtab, execution_limits_config);

    for clause in clause_set {
        #[cfg(feature = "itrace")]
        if let Some(base_path) = &itrace_path {
            // 多个 clause 同时执行时，为每个 clause 生成独立 itrace 输出文件，避免互相覆盖。
            let output_path =
                if num_clauses > 1 { clause_itrace_output_path(base_path, &clause) } else { base_path.clone() };
            if let Some(ir) = ir_file_path.as_ref() {
                // 每次执行前用当前 clause、IR 文件和输出路径配置 itrace 追踪器。
                shared_state.itrace.configure(clause.as_str(), ir.clone(), Some(output_path), &shared_state.symtab);
            }
        }

        match run_symbolic_execute_with_target(
            target,
            &clause,
            shared_state,
            regs,
            lets,
            initial_memory.clone(),
            num_threads,
            timeout,
            &execution_limits,
        ) {
            Ok(_) => {}
            Err(e) => {
                eprintln!("错误: clause '{}' 符号执行失败: {}", clause, e);
                log!(log::SYM_EXEC, &format!("solve_state: {}运行错误 {}", clause, e));
                success = false;
            }
        }

        #[cfg(feature = "itrace")]
        if itrace_path.is_some() {
            shared_state.itrace.dump();
        }
    }

    success
}

#[allow(non_snake_case)]
fn symbolic_args_from_types<B: BV>(
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

    symbolic(ctor_ty, shared_state, solver, SourceLoc::unknown())
}
fn run_symbolic_execute_with_target<'ir, B: BV>(
    target: &mut dyn RISCV<B>,
    instruction_name: &str,
    shared_state: &SharedState<'ir, B>,
    regs: &'ir RegisterBindings<'ir, B>,
    lets: &'ir Bindings<'ir, B>,
    initial_memory: Option<isla_lib::memory::Memory<B>>,
    num_threads: usize,
    timeout: Option<u64>,
    execution_limits: &ExecutionLimits,
) -> Result<Option<String>, ExecError> {
    use isla_lib::smt::checkpoint;

    let state_regs = target.reg_list();

    let mut cfg = Config::new();
    cfg.set_param_value("model", "true");
    let ctx = Context::new(cfg);
    let mut solver = Solver::new(&ctx);
    let mut symbolic_regs = regs.clone();

    // pre-state 主动符号化：遍历 target 提供的寄存器、按类型符号化并覆盖，返回 PreStateCtx 供求解后取 pre-state。
    target.setup_pre_state(&mut symbolic_regs, lets, shared_state, &mut solver)?;

    //不要删掉这个注释！！！留着以后改pmp的时候用
    /* if target.pmp_symbolic() {
        target.apply_symbolic_pmp_to_registers(&shared_state.symtab, &mut symbolic_regs, shared_state, &mut solver)?;
    } */

    // 使用 symbolic_args_from_types 生成符号化参数
    let ctor_name = shared_state.symtab.lookup(instruction_name);

    let fun_args = vec![Val::<B>::Ctor(
        ctor_name,
        Box::new(symbolic_args_from_types(instruction_name, shared_state, &symbolic_regs, lets, &mut solver)?),
    )];
    log!(log::SYM_EXEC, &format!("fun_args:{:?}", fun_args));
    log!(log::ARCH_INFO, &format!("{:?}", state_regs));

    // 生成参数（暂时使用默认值，测试checkpoint机制）

    // 构造指令值

    // 创建checkpoint，包含符号化变量
    let cp = checkpoint(&mut solver);

    // 使用checkpoint执行函数，支持错误传播
    let result: Arc<Mutex<AssemGenJson>> = Arc::new(Mutex::new(AssemGenJson::new(Vec::new())));

    let task_state = TaskState::new().with_execution_limits(execution_limits.clone());

    //isla_lib::executor::execute_ir_function_with_checkpoint_and_limits(
    isla_lib::executor::execute_ir_function_with_checkpoint_multi_thread(
        "zexecute",
        &fun_args,
        shared_state,
        &symbolic_regs,
        lets,
        &result,
        &|thread, _task_id, exec_result, shared_state, mut solver, collected| {
            match &exec_result {
                Ok((Run::Finished(_), frame)) => {
                    isla_lib::executor::submit_itrace_for_local_frame(frame, shared_state);
                }
                Ok((run, frame)) => {
                    if should_collect_unfinished_path(run) {
                        isla_lib::executor::submit_itrace_for_local_frame(frame, shared_state);
                    }
                }
                Err((ExecError::AssertionFailure(_, _), _)) => {}
                Err((_, frame)) => isla_lib::executor::submit_itrace_for_local_frame(frame, shared_state),
            }

            match exec_result {
                Ok((run, frame)) => match run {
                    Run::Finished(Val::Poison) => {
                        log!(log::SYM_EXEC, &format!("警告: {}这个Ctor返回值是Poison，可能是相关扩展（如H扩展）造成的，因此产生了sail的_inner_error_", instruction_name))
                    }
                    Run::Finished(ret_val) => {
                        let ret_val_str = ret_val.to_str(shared_state).to_string();
                        log!(
                            log::PATH_RESULT,
                            &format!(
                                "1. tid:{} 执行好一条路径，fork={}，ret_val={}",
                                thread,
                                frame.forks(),
                                ret_val_str
                            )
                        );
                        // Illegal_Instruction is a valid Sail ExecutionResult; JSON keeps every finished ret_val.
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
                                            get_assembly_name(arg_val.clone(), &shared_state, regs, lets)
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
                                // 开启 model completion：未被约束的 pre-state 符号变量也会得到一个具体值，
                                // 这样所有主动符号化的 pre-state 寄存器都能输出（与 testgen 一致）。
                                // model.set_complete_model(true);
                                log!(log::PATH_RESULT, &format!("2. === ISA State (Thread {}) ===", thread));
                                let test = Sym::from_u32(6);
                                // dlog!("model.get_var({:?})={:?}", test, model.get_var(test));
                                // dlog!("fun_args={:#?}", model.get_val(&fun_args[0]));
                                match model.get_val(&fun_args[0]) {
                                    Ok(arg_val) => {
                                        let asm_opt = get_assembly_name(arg_val.clone(), shared_state, regs, lets);
                                        log!(log::PATH_RESULT, &format!("当前汇编：{:?}", asm_opt));
                                        match asm_opt {
                                            Some(asm) => test_ins = asm,
                                            None => return,
                                        }
                                        let asm_encdec_opt =
                                            match get_assembly_encdec(arg_val.clone(), shared_state, regs, lets) {
                                                Some(val) => match FmtVal::from_val(&val, &mut model) {
                                                    Ok(fmt_val) => Some(fmt_val.to_str(shared_state)),
                                                    Err(err) => {
                                                        log!(
                                                            log::PATH_RESULT,
                                                            &format!(
                                                                "警告: {}汇编编码不可格式化 {:?}",
                                                                instruction_name, err
                                                            )
                                                        );
                                                        None
                                                    }
                                                },
                                                None => None,
                                            };
                                        log!(log::PATH_RESULT, &format!("当前汇编encdec：{:?}", asm_encdec_opt));
                                        match asm_encdec_opt {
                                            Some(encdec) => test_ins_encdec = encdec,
                                            None => return,
                                        }
                                    }
                                    Err(e) => {
                                        log!(
                                            log::PATH_RESULT,
                                            &format!("警告: clause{} model.get_val失败 {:?}", instruction_name, e)
                                        );
                                        //*collected.lock().unwrap() = Err(e);
                                        return;
                                    }
                                }

                                // pre-state 取值：通过 target 和 setup 阶段生成的 PreStateCtx 查询具体解。
                                isa_state.extend(target.solve_pre_state(&mut model, shared_state));

                                log!(
                                    log::PATH_RESULT,
                                    &format!("isa_state={}", serde_json::to_string_pretty(&isa_state).unwrap())
                                );
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
                                log!(log::PATH_RESULT, "3. ==============================");
                            }
                        }
                        let single_instruction_json =
                            AssemGenJsonItem::new(target, test_ins, test_ins_encdec, isa_state, ret_val_str);
                        let mut instruction_json = collected.lock().unwrap();
                        instruction_json.gen.push(single_instruction_json);
                    }
                    Run::Exit => {
                        log!(log::PATH_RESULT, &format!("tid:{} 执行好一条路径(Exit)，fork={}", thread, frame.forks()))
                    }
                    Run::Dead => {}

                    Run::Suspended => log!(
                        log::PATH_RESULT,
                        &format!("tid:{} 执行好一条路径(Suspended)，fork={}", thread, frame.forks())
                    ),
                },
                Err((error, frame)) => {
                    match &error {
                        ExecError::MatchFailure(_) => {
                            // 静默处理
                        }
                        ExecError::AssertionFailure(_, _) => {
                            // assert 失败表示当前路径不满足模型前置条件，丢弃该路径。
                        }
                        _ => {
                            log!(
                                log::SYM_EXEC,
                                &format!(
                                    "执行错误: {}({:?})[{}]",
                                    error,
                                    error,
                                    error.source_loc().location_string(shared_state.symtab.files())
                                )
                            );
                            log!(
                                log::SYM_EXEC,
                                &format!("调用栈: {}", backtrace_string(frame.backtrace(), &shared_state.symtab))
                            );
                        }
                    }
                }
            }
        },
        cp,
        num_threads,
        timeout,
        &task_state,
    );

    // 提取字符串结果
    if let Ok(result_mutex) = Arc::try_unwrap(result) {
        let xlen_name_str = target.arch_pretty_name().to_string();
        result_mutex.lock().unwrap().to_json(Some(format!("output/{}_{}.json", xlen_name_str, instruction_name)));
        Ok(None)
    } else {
        log!(log::SYM_EXEC, &format!("警告: {}无法获取 result 收集器", instruction_name));
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::bitvector::b64::B64;
    use isla_lib::config::LimitBehaviorConfig;
    use isla_lib::source_loc::SourceRegion;

    #[test]
    fn solve_execution_limits_use_local_sampling_as_primary_path_bound() {
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["extensions/V/vext_arith_insts.sail"]);
        let limits = solve_execution_limits(&symtab, None);

        assert_eq!(limits.max_forks_per_branch, Some(2));
        assert_eq!(limits.max_forks_per_path, None);
        assert_eq!(limits.max_backjumps_per_loop, None);
        assert_eq!(limits.max_path_depth, None);
        assert_eq!(limits.call_context_depth, None);
        assert_eq!(limits.on_limit_reached, LimitBehavior::Concretize);
        assert_eq!(limits.regions.as_ref().unwrap().len(), 4);

        assert_eq!(
            limits.regions,
            Some(vec![
                SourceRegion::from_source_loc(SourceLoc::new(0, 186, 6, 192, 7)),
                SourceRegion::from_source_loc(SourceLoc::new(0, 191, 20, 191, 65)),
                SourceRegion::from_source_loc(SourceLoc::new(0, 195, 6, 201, 7)),
                SourceRegion::from_source_loc(SourceLoc::new(0, 200, 20, 200, 65)),
            ])
        );
    }

    #[test]
    fn solve_execution_limits_applies_toml_override_after_defaults() {
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["extensions/V/vext_arith_insts.sail"]);
        let config = ExecutionLimitsConfig {
            max_forks_per_branch: Some(7),
            max_forks_per_path: Some(11),
            call_context_depth: Some(3),
            on_limit_reached: Some(LimitBehaviorConfig::Truncate),
            ..ExecutionLimitsConfig::default()
        };

        let limits = solve_execution_limits(&symtab, Some(&config));

        assert_eq!(limits.max_forks_per_branch, Some(7));
        assert_eq!(limits.max_forks_per_path, Some(11));
        assert_eq!(limits.call_context_depth, Some(3));
        assert_eq!(limits.on_limit_reached, LimitBehavior::Truncate);
        assert_eq!(limits.regions.as_ref().unwrap().len(), 4);
    }

    #[test]
    fn solve_execution_limits_can_be_disabled_by_toml() {
        let symtab = Symtab::new();
        let config = ExecutionLimitsConfig { enabled: Some(false), ..ExecutionLimitsConfig::default() };

        let limits = solve_execution_limits(&symtab, Some(&config));

        assert_eq!(limits.max_forks_per_branch, None);
        assert_eq!(limits.max_forks_per_path, None);
        assert!(limits.regions.is_none());
    }

    #[test]
    fn solve_execution_limits_missing_default_region_file_matches_nothing_without_panicking() {
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["core/types.sail"]);

        let limits = solve_execution_limits(&symtab, None);

        assert_eq!(limits.max_forks_per_branch, Some(2));
        assert_eq!(limits.max_fork_pct_per_branch, None);
        assert_eq!(limits.max_backjumps_per_loop, None);
        assert_eq!(limits.regions, Some(Vec::new()));
    }

    #[test]
    fn solve_execution_limits_missing_configured_region_keeps_path_limits_only() {
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["core/types.sail"]);
        let config = ExecutionLimitsConfig {
            max_forks_per_branch: Some(7),
            max_forks_per_path: Some(11),
            regions: Some(vec![SourceRegionSpec::new("extensions/V/vext_arith_insts.sail", (186, 6), (192, 7))]),
            ..ExecutionLimitsConfig::default()
        };

        let limits = solve_execution_limits(&symtab, Some(&config));

        assert_eq!(limits.max_forks_per_branch, Some(7));
        assert_eq!(limits.max_forks_per_path, Some(11));
        assert_eq!(limits.regions, Some(Vec::new()));
    }

    #[test]
    fn unfinished_path_collection_skips_dead_paths() {
        assert!(!should_collect_unfinished_path::<B64>(&Run::Dead));
        assert!(should_collect_unfinished_path::<B64>(&Run::Exit));
        assert!(should_collect_unfinished_path::<B64>(&Run::Suspended));
    }

    #[cfg(feature = "itrace")]
    #[test]
    fn clause_itrace_output_path_appends_clause_suffix() {
        let base = PathBuf::from("output/itrace.txt");
        let result = clause_itrace_output_path(&base, "zadd");
        assert_eq!(result, PathBuf::from("output/itrace_zadd.txt"));
    }

    #[cfg(feature = "itrace")]
    #[test]
    fn clause_itrace_output_path_preserves_directory() {
        let base = PathBuf::from("/tmp/deep/dir/trace.log");
        let result = clause_itrace_output_path(&base, "zlw");
        assert_eq!(result, PathBuf::from("/tmp/deep/dir/trace_zlw.log"));
    }

    #[cfg(feature = "itrace")]
    #[test]
    fn clause_itrace_output_path_handles_no_extension() {
        let base = PathBuf::from("output/itrace");
        let result = clause_itrace_output_path(&base, "zsub");
        assert_eq!(result, PathBuf::from("output/itrace_zsub.txt"));
    }
}
