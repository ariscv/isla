use super::clause::get_extension_clauses;
use super::context_execution::{init_model, run_model_instruction, setup_init_regs, setup_opcode};
use super::context_state::{interrogate_model, GVAccessor, GroundVal, PrePostStates};
use super::target::{Target, RISCV};
use super::{
    enumerate_concrete_values, get_all_clause_names, get_assembly_encdec, get_assembly_name, list_instructions,
};
use isla_axiomatic::litmus::assemble_instruction;
use isla_lib::bitvector::BV;
use isla_lib::config::ISAConfig;
use isla_lib::error::ExecError;
use isla_lib::error::IslaError;
use isla_lib::executor::{backtrace_string, Frame, Run, StopAction, StopConditions};
use isla_lib::executor::{ExecutionLimits, LimitBehavior, TaskState};
use isla_lib::fmtval::FmtVal;
use isla_lib::ir::*;
use isla_lib::log;
use isla_lib::memory::{Address, Memory};
use isla_lib::primop_util::symbolic;
use isla_lib::register::RegisterBindings;
use isla_lib::smt::{Checkpoint, Config, Context, Model};
use isla_lib::smt::{Solver, Sym};
use isla_lib::source_loc::SourceLoc;
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
    #[serde(skip_serializing_if = "Option::is_none")]
    context: Option<ExecutionContextJson>,
}
impl AssemGenJsonItem {
    pub fn new<T: Target>(
        target: &T,
        test_ins: String,
        test_ins_encdec: String,
        isa_state: BTreeMap<String, String>,
        ret_val: String,
    ) -> Self {
        Self::with_context(target, test_ins, test_ins_encdec, isa_state, ret_val, None)
    }

    pub fn with_context<T: Target>(
        target: &T,
        test_ins: String,
        test_ins_encdec: String,
        isa_state: BTreeMap<String, String>,
        ret_val: String,
        context: Option<ExecutionContextJson>,
    ) -> Self {
        let mut arch = BTreeMap::new();
        arch.insert("pretty-name".to_string(), target.arch_pretty_name().to_string());
        arch.insert("name".to_string(), target.arch_name().to_string());
        arch.insert("xlen".to_string(), target.xlen().to_string());
        arch.insert("ext".to_string(), "IMACFD".to_string());
        AssemGenJsonItem { arch, test_ins, test_ins_encdec, isa_state, ret_val, context }
    }
}

#[derive(Serialize, Deserialize)]
struct MemoryBytesJson {
    start: u64,
    end: u64,
    bytes: Vec<String>,
}

#[derive(Serialize, Deserialize)]
struct MemoryTagsJson {
    start: u64,
    end: u64,
    tags: Vec<bool>,
}

#[derive(Serialize, Deserialize)]
struct TagWriteJson {
    address: u64,
    tag: bool,
}

#[derive(Serialize, Deserialize)]
struct ExecutionContextJson {
    code: Vec<MemoryBytesJson>,
    #[serde(rename = "pre-memory")]
    pre_memory: Vec<MemoryBytesJson>,
    #[serde(rename = "pre-tag-memory")]
    pre_tag_memory: Vec<MemoryTagsJson>,
    #[serde(rename = "pre-registers")]
    pre_registers: BTreeMap<String, String>,
    #[serde(rename = "post-memory")]
    post_memory: Vec<MemoryBytesJson>,
    #[serde(rename = "post-tag-memory")]
    post_tag_memory: Vec<TagWriteJson>,
    #[serde(rename = "post-registers")]
    post_registers: BTreeMap<String, String>,
    #[serde(rename = "instruction-locations")]
    instruction_locations: BTreeMap<String, String>,
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
    /// 创建 solve-state 输出 JSON 的顶层结构。
    fn new(gen: Vec<AssemGenJsonItem>) -> Self {
        // 这里只包装 gen 列表，具体字段由 AssemGenJsonItem 承载。
        AssemGenJson { gen }
    }
}

/// 把寄存器名和 accessor 路径拼成 JSON 中使用的键。
fn regacc_key(reg: &str, acc: &[GVAccessor<&str>]) -> String {
    // 先解码寄存器名，再追加字段或元素下标。
    let mut parts = vec![zencode::decode(reg)];
    parts.extend(acc.iter().map(|acc| match acc {
        GVAccessor::Field(field) => zencode::decode(field),
        GVAccessor::Element(index) => index.to_string(),
    }));
    parts.join(".")
}

/// 把内部字节内存区间转换为 JSON 结构。
fn memory_bytes_json(ranges: Vec<(std::ops::Range<Address>, Vec<u8>)>) -> Vec<MemoryBytesJson> {
    // 字节使用十六进制字符串，便于外部模块直接消费。
    ranges
        .into_iter()
        .map(|(range, bytes)| MemoryBytesJson {
            start: range.start,
            end: range.end,
            bytes: bytes.into_iter().map(|byte| format!("0x{:02x}", byte)).collect(),
        })
        .collect()
}

/// 把内部 tag 内存区间转换为 JSON 结构。
fn memory_tags_json(ranges: Vec<(std::ops::Range<Address>, Vec<bool>)>) -> Vec<MemoryTagsJson> {
    // tag 本身就是 bool，保持原样输出。
    ranges.into_iter().map(|(range, tags)| MemoryTagsJson { start: range.start, end: range.end, tags }).collect()
}

/// 把内部寄存器具体值转换为 JSON 键值表。
fn registers_json<B: BV>(
    registers: std::collections::HashMap<(&str, Vec<GVAccessor<&str>>), GroundVal<B>>,
) -> BTreeMap<String, String> {
    // 使用 BTreeMap 保证输出稳定排序。
    registers.into_iter().map(|((reg, acc), value)| (regacc_key(reg, &acc), value.to_string())).collect()
}

/// 把 testgen 风格的 pre/post 状态转换为当前 JSON 的 context 字段。
fn context_json<B: BV>(states: PrePostStates<B>) -> ExecutionContextJson {
    // 这里仅做结构转换，不再参与求解。
    ExecutionContextJson {
        code: memory_bytes_json(states.code),
        pre_memory: memory_bytes_json(states.pre_memory),
        pre_tag_memory: memory_tags_json(states.pre_tag_memory),
        pre_registers: registers_json(states.pre_registers),
        post_memory: memory_bytes_json(states.post_memory),
        post_tag_memory: states
            .post_tag_memory
            .into_iter()
            .map(|(address, tag)| TagWriteJson { address, tag })
            .collect(),
        post_registers: registers_json(states.post_registers),
        instruction_locations: states
            .instruction_locations
            .into_iter()
            .map(|(address, description)| (format!("0x{:x}", address), description))
            .collect(),
    }
}

/// 规范化 Sail 输出的 RISC-V 汇编字符串，使其能被外部 assembler 接受。
fn normalize_riscv_assembly_for_assembler(instruction: &str) -> String {
    // GNU assembler 不接受 fence 0,0 形式，等价改写成 fence。
    let trimmed = instruction.trim();
    if trimmed == "fence 0, 0" || trimmed == "fence 0,0" {
        "fence".to_string()
    } else {
        trimmed.to_string()
    }
}

/// 把汇编字符串或十六进制 opcode 字符串转换为 Isla bitvector opcode。
fn instruction_opcode_from_asm<B: BV>(instruction: &str, isa_config: &ISAConfig<B>) -> Result<B, ExecError> {
    // 0x 前缀直接解析；其他字符串交给 RISC-V assembler。
    if let Some(hex) = instruction.strip_prefix("0x") {
        B::from_str(&format!("0x{}", hex.split_whitespace().next().unwrap_or(hex)))
            .ok_or_else(|| ExecError::Type(format!("无法解析指令 opcode: {}", instruction), SourceLoc::unknown()))
    } else {
        let normalized_instruction = normalize_riscv_assembly_for_assembler(instruction);
        let mut bytes = assemble_instruction(&normalized_instruction, isa_config)
            .map_err(|msg| ExecError::Type(format!("无法汇编指令 '{}': {}", instruction, msg), SourceLoc::unknown()))?;
        bytes.reverse();
        Ok(B::from_bytes(&bytes))
    }
}

#[allow(clippy::too_many_arguments)]
/// 对单条具体汇编指令执行“放入内存、跑模型、提取上下文”的完整流程。
fn solve_assembly_context<'ir, B, T>(
    target: &'ir T,
    shared_state: &'ir SharedState<'ir, B>,
    initial_frame: &Frame<'ir, B>,
    initial_checkpoint: Checkpoint<B>,
    register_map: &std::collections::HashMap<(String, Vec<GVAccessor<String>>), Sym>,
    register_types: &std::collections::HashMap<Name, Ty<Name>>,
    isa_config: &ISAConfig<B>,
    symbolic_regions: &[std::ops::Range<Address>],
    symbolic_code_regions: &[std::ops::Range<Address>],
    instruction: &str,
    num_threads: usize,
) -> Result<Vec<AssemGenJsonItem>, ExecError>
where
    B: BV,
    T: RISCV,
{
    // 先把汇编转 opcode，再把 opcode 约束到当前 PC 的指令内存读取上。
    let opcode = instruction_opcode_from_asm(instruction, isa_config)?;
    let (opcode_pc, opcode_var, opcode_checkpoint, opcode_ok) =
        setup_opcode(target, shared_state, initial_frame, opcode, None, initial_checkpoint);
    if !opcode_ok {
        return Err(ExecError::Z3Error(format!("指令 '{}' 放入内存后约束不可满足", instruction)));
    }

    let stop_conditions = StopConditions::new();
    let exception_stop_conditions =
        StopConditions::parse(T::exception_stop_functions(), shared_state, StopAction::Kill);
    let all_stop_conditions = stop_conditions.union(&exception_stop_conditions);
    let continuations = run_model_instruction(
        target,
        &T::run_instruction_function(),
        num_threads,
        shared_state,
        initial_frame,
        opcode_checkpoint,
        opcode_var,
        &all_stop_conditions,
        false,
        &None,
    );

    if continuations.is_empty() {
        return Err(ExecError::Unreachable(format!("指令 '{}' 没有可行执行路径", instruction)));
    }

    let (frame, checkpoint) = continuations.into_iter().next().unwrap();
    let states = interrogate_model(
        target,
        isa_config,
        checkpoint,
        shared_state,
        initial_frame,
        &frame,
        register_types,
        symbolic_regions,
        symbolic_code_regions,
        true,
        register_map,
        &[(opcode_pc.clone(), instruction.to_string())],
    )?;

    Ok(vec![AssemGenJsonItem::with_context(
        target,
        instruction.to_string(),
        instruction.to_string(),
        BTreeMap::new(),
        "unit".to_string(),
        Some(context_json(states)),
    )])
}

/// 基于用户指定的 itrace 基路径和 clause 名，生成每个 clause 独立的输出文件路径。
/// 规则：`output/itrace.txt` + clause `zadd` → `output/itrace_zadd.txt`
#[cfg(feature = "tracetool")]
fn clause_itrace_output_path(base_path: &Path, clause: &str) -> PathBuf {
    let stem = base_path.file_stem().and_then(|s| s.to_str()).unwrap_or("itrace");
    let extension = base_path.extension().and_then(|s| s.to_str()).unwrap_or("txt");
    let new_name = format!("{}_{}.{}", stem, clause, extension);
    base_path.with_file_name(new_name)
}

/// solve-state 子命令的主入口函数，枚举目标 clause 并输出带 context 的 JSON。
/// 支持通过 clause 名、扩展名、汇编指令名或 --all 来筛选需要符号执行的 clause。
pub fn solve_state_main<B, T>(
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
    initial_memory: Option<isla_lib::memory::Memory<B>>,
    isa_config: &ISAConfig<B>,
    register_types: &std::collections::HashMap<Name, Ty<Name>>,
    num_threads: usize,
    target: &T,
    clauses: &[String],
    extensions: &[String],
    instruction_names: &[String],
    run_all: bool,
    itrace_path: Option<PathBuf>,
    ir_file_path: Option<PathBuf>,
) -> bool
where
    B: BV,
    T: RISCV,
{
    // 先汇总用户指定的筛选条件，得到最终要处理的 clause 集合。
    let mut clause_set: HashSet<String> = HashSet::new();
    let mut success = true;

    // 添加显式指定的 clause
    clause_set.extend(clauses.iter().cloned());

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

    #[cfg(not(feature = "tracetool"))]
    let _ = (&itrace_path, &ir_file_path);

    #[cfg(feature = "tracetool")]
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

    // 当前 testgen 路径自行构造符号内存，因此丢弃旧入口传入的初始内存。
    drop(initial_memory);

    // 数据内存和代码内存分开建模，代码区从目标默认 PC 开始。
    let symbolic_regions = vec![0x8031_0000..0x8041_0000];
    let symbolic_code_regions = vec![target.default_init_pc()..target.default_init_pc() + 0x10000];
    let mut memory = Memory::new();
    for region in &symbolic_regions {
        memory.add_symbolic_region(region.clone());
    }
    for region in &symbolic_code_regions {
        memory.add_symbolic_code_region(region.clone());
    }

    // 初始化 Sail 模型，并把需要观察的寄存器符号化。
    let mut init_lets = lets.clone();
    init_lets.insert(ELF_ENTRY, UVal::Init(Val::I128(target.default_init_pc() as i128)));
    let (initial_frame, initial_checkpoint) =
        init_model(shared_state, init_lets, regs.clone(), &memory, &target.init_function());
    let (initial_frame, initial_checkpoint, register_map) = setup_init_regs(
        shared_state,
        initial_frame,
        initial_checkpoint,
        register_types,
        target.default_init_pc(),
        target,
        &[],
    );

    for clause in clause_set {
        #[cfg(feature = "tracetool")]
        if let Some(base_path) = &itrace_path {
            // 多个 clause 同时执行时，为每个 clause 生成独立 itrace 输出文件，避免互相覆盖。
            let output_path =
                if num_clauses > 1 { clause_itrace_output_path(base_path, &clause) } else { base_path.clone() };
            if let Some(ir) = ir_file_path.as_ref() {
                // 每次执行前用当前 clause、IR 文件和输出路径配置 itrace 追踪器。
                shared_state.itrace.configure(clause.as_str(), ir.clone(), Some(output_path), &shared_state.symtab);
            }
        }

        let instructions = full_assembly_candidates_for_clause(&clause, shared_state, regs, lets);
        if instructions.is_empty() {
            eprintln!("错误: clause '{}' 没有可汇编的候选指令", clause);
            success = false;
            continue;
        }

        let mut gen = Vec::new();
        for instruction in instructions {
            match solve_assembly_context(
                target,
                shared_state,
                &initial_frame,
                initial_checkpoint.clone(),
                &register_map,
                register_types,
                isa_config,
                &symbolic_regions,
                &symbolic_code_regions,
                &instruction,
                num_threads,
            ) {
                Ok(mut items) => gen.append(&mut items),
                Err(e) => {
                    eprintln!("错误: clause '{}' 指令 '{}' 上下文提取失败: {}", clause, instruction, e);
                    log!(log::SYM_EXEC, &format!("solve_state: {} {} 上下文提取错误 {}", clause, instruction, e));
                    success = false;
                }
            }
        }
        AssemGenJson::new(gen).to_json(Some(format!("output/{}_{}.json", target.arch_pretty_name(), clause)));

        #[cfg(feature = "tracetool")]
        if itrace_path.is_some() {
            shared_state.itrace.dump();
        }
    }

    success
}

/// 枚举某个 clause 能生成的完整汇编候选字符串。
fn full_assembly_candidates_for_clause<B: BV>(
    clause: &str,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Vec<String> {
    // 先在 zinstruction union 中找到 clause 的构造器类型。
    let instruction_union = shared_state.type_info.unions.get(&shared_state.symtab.lookup("zinstruction"));
    let Some(union_members) = instruction_union else {
        return vec![];
    };
    let ctor_name = shared_state.symtab.lookup(clause);
    let Some((_, ctor_ty)) = union_members.iter().find(|(name, _)| *name == ctor_name) else {
        return vec![];
    };

    let mut instructions = HashSet::new();
    for arg_value in enumerate_concrete_values(ctor_ty, shared_state) {
        let instr_value = Val::Ctor(ctor_name, Box::new(arg_value));
        if let Some(asm) = get_assembly_name(instr_value, shared_state, regs, lets) {
            instructions.insert(asm);
        }
    }
    let mut instructions: Vec<_> = instructions.into_iter().collect();
    instructions.sort();
    instructions
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
fn run_symbolic_execute_with_target<T: RISCV, B: BV>(
    target: &T,
    instruction_name: &str,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
    initial_memory: Option<isla_lib::memory::Memory<B>>,
) -> Result<Option<String>, ExecError> {
    use isla_lib::smt::checkpoint;

    let mut cfg = Config::new();
    cfg.set_param_value("model", "true");
    let ctx = Context::new(cfg);
    let mut solver = Solver::new(&ctx);
    let mut symbolic_regs = regs.clone();

    if target.pmp_symbolic() {
        target.apply_symbolic_pmp_to_registers(&shared_state.symtab, &mut symbolic_regs, shared_state, &mut solver)?;
    }

    // 使用 symbolic_args_from_types 生成符号化参数
    let ctor_name = shared_state.symtab.lookup(instruction_name);

    let fun_args = vec![Val::<B>::Ctor(
        ctor_name,
        Box::new(symbolic_args_from_types(instruction_name, shared_state, &symbolic_regs, lets, &mut solver)?),
    )];
    log!(log::SYM_EXEC, &format!("fun_args:{:?}", fun_args));
    log!(log::ARCH_INFO, &format!("{:?}", target.isa_state_list()));

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
    let result: Arc<Mutex<AssemGenJson>> = Arc::new(Mutex::new(AssemGenJson::new(Vec::new())));

    isla_lib::executor::execute_ir_function_with_checkpoint_and_limits(
        "zexecute",
        &fun_args,
        shared_state,
        &symbolic_regs,
        lets,
        &result,
        &|thread, _task_id, exec_result, shared_state, mut solver, collected| {
            match &exec_result {
                Ok((_, frame)) => isla_lib::executor::submit_itrace_for_local_frame(frame, shared_state),
                Err((_, frame)) => isla_lib::executor::submit_itrace_for_local_frame(frame, shared_state),
            }

            match exec_result {
                Ok((run, frame)) => match run {
                    Run::Finished(Val::Poison) => {
                        log!(log::SYM_EXEC, &format!("警告: {}这个Ctor返回值是Poison，可能是相关扩展（如H扩展）造成的，因此产生了sail的_inner_error_", instruction_name))
                    }
                    Run::Finished(ret_val) => {
                        log!(
                            log::PATH_RESULT,
                            &format!(
                                "1. tid:{} 执行好一条路径，fork={}，ret_val={}",
                                thread,
                                frame.forks,
                                ret_val.to_str(shared_state)
                            )
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
                                            get_assembly_encdec(arg_val.clone(), shared_state, regs, lets);
                                        let asm_encdec_opt = asm_encdec_opt.map(|val| {
                                            FmtVal::from_val(&val, &mut model).unwrap().to_str(shared_state)
                                        });
                                        log!(log::PATH_RESULT, &format!("当前汇编encdec：{:?}", asm_encdec_opt));
                                        match asm_encdec_opt {
                                            Some(encdec) => test_ins_encdec = encdec,
                                            None => return,
                                        }
                                    }
                                    Err(e) => {
                                        log!(log::PATH_RESULT, &format!("警告: {}没有汇编 {:?}", instruction_name, e));
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
                        let single_instruction_json = AssemGenJsonItem::new(
                            target,
                            test_ins,
                            test_ins_encdec,
                            isa_state,
                            ret_val.to_str(shared_state).to_string(),
                        );
                        let mut instruction_json = collected.lock().unwrap();
                        instruction_json.gen.push(single_instruction_json);
                    }
                    Run::Exit => {
                        log!(log::PATH_RESULT, &format!("tid:{} 执行好一条路径(Exit)，fork={}", thread, frame.forks))
                    }
                    Run::Dead => {
                        log!(log::PATH_RESULT, &format!("tid:{} 执行好一条路径(Dead)，fork={}", thread, frame.forks))
                    }

                    Run::Suspended => log!(
                        log::PATH_RESULT,
                        &format!("tid:{} 执行好一条路径(Suspended)，fork={}", thread, frame.forks)
                    ),
                },
                Err((error, frame)) => {
                    match &error {
                        ExecError::MatchFailure(_) => {
                            // 静默处理
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
        initial_memory,
        task_state,
    );

    // 提取字符串结果
    if let Ok(result_mutex) = Arc::try_unwrap(result) {
        let xlen_name_str = target.arch_pretty_name();
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

    #[test]
    fn clause_itrace_output_path_appends_clause_suffix() {
        let base = PathBuf::from("output/itrace.txt");
        let result = clause_itrace_output_path(&base, "zadd");
        assert_eq!(result, PathBuf::from("output/itrace_zadd.txt"));
    }

    #[test]
    fn clause_itrace_output_path_preserves_directory() {
        let base = PathBuf::from("/tmp/deep/dir/trace.log");
        let result = clause_itrace_output_path(&base, "zlw");
        assert_eq!(result, PathBuf::from("/tmp/deep/dir/trace_zlw.log"));
    }

    #[test]
    fn clause_itrace_output_path_handles_no_extension() {
        let base = PathBuf::from("output/itrace");
        let result = clause_itrace_output_path(&base, "zsub");
        assert_eq!(result, PathBuf::from("output/itrace_zsub.txt"));
    }

    #[test]
    fn normalize_riscv_assembly_accepts_numeric_fence_zero_masks() {
        assert_eq!(normalize_riscv_assembly_for_assembler("fence 0, 0"), "fence");
        assert_eq!(normalize_riscv_assembly_for_assembler("fence 0,0"), "fence");
    }

    #[test]
    fn normalize_riscv_assembly_preserves_other_instructions() {
        assert_eq!(normalize_riscv_assembly_for_assembler(" add x1, x2, x3 "), "add x1, x2, x3");
    }
}
