use crate::bitvector::BV;
use crate::config::ISAConfig;
use crate::error::{ExecError, IslaError};
use crate::executor::{backtrace_string, Run};
use crate::fmtval::FmtVal;
use crate::ir::UVal;
use crate::ir::*;
use crate::isarch::{self};
use crate::memory::Memory;
use crate::primop_util::symbolic;
use crate::primop_util::{length_bits, smt_sbits, smt_value};
use crate::register::RegisterBindings;
use crate::smt::{Config, Context, Event, Model, Solver};
use crate::source_loc::SourceLoc;
use crate::zencode;
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

#[derive(Serialize, Deserialize)]
struct AssemGenMemoryEvent {
    kind: String,
    region: String,
    bytes: u32,
    address: String,
    address_model: Option<String>,
    value: Option<String>,
    data: Option<String>,
    is_ifetch: bool,
    is_exclusive: bool,
}

#[derive(Serialize, Deserialize)]
struct AssemGen_Json_Item {
    arch: BTreeMap<String, String>,
    #[serde(rename = "test-ins")]
    test_ins: String,
    #[serde(rename = "test-ins-encdec")]
    test_ins_encdec: String,
    #[serde(rename = "isa-state")]
    isa_state: BTreeMap<String, String>,
    #[serde(rename = "memory-events")]
    memory_events: Vec<AssemGenMemoryEvent>,
    ret_val: String,
}
impl AssemGen_Json_Item {
    pub fn new<T: Target>(
        target: &T,
        test_ins: String,
        test_ins_encdec: String,
        isa_state: BTreeMap<String, String>,
        memory_events: Vec<AssemGenMemoryEvent>,
        ret_val: String,
    ) -> Self {
        let mut arch = BTreeMap::new();
        arch.insert("pretty-name".to_string(), target.arch_pretty_name().to_string());
        arch.insert("name".to_string(), target.arch_name().to_string());
        arch.insert("xlen".to_string(), target.xlen().to_string());
        arch.insert("ext".to_string(), "IMACFD".to_string());
        AssemGen_Json_Item { arch, test_ins, test_ins_encdec, isa_state, memory_events, ret_val }
    }
}
trait ToJSON: Serialize {
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

#[derive(Serialize)]
struct ForkProfileSite {
    location: String,
    innermost_function: String,
    stack: String,
    hits: usize,
}

#[derive(Serialize)]
struct ForkProfilePath {
    asm: String,
    ret_val: String,
    fork_events: usize,
    unique_sites: usize,
    trace_len: usize,
    top_sites: Vec<ForkProfileSite>,
}

fn profile_forks_enabled() -> bool {
    matches!(
        std::env::var("ISLA_RISCV_PROFILE_FORKS"),
        Ok(value) if matches!(value.as_str(), "1" | "true" | "True" | "TRUE" | "on" | "On" | "ON")
    )
}

fn decoded_symbol<B: BV>(name: Name, shared_state: &SharedState<B>) -> String {
    zencode::decode(shared_state.symtab.to_str(name))
}

fn fork_profile_for_trace<B: BV>(
    solver: &Solver<B>,
    shared_state: &SharedState<B>,
    asm: &str,
    ret_val: &str,
) -> ForkProfilePath {
    let events = solver.trace().to_vec();
    let mut stack = Vec::new();
    let mut sites: BTreeMap<(String, String, String), usize> = BTreeMap::new();
    let mut fork_events = 0;

    for event in events.iter().rev() {
        match event {
            Event::Function { name, call: true } => stack.push(*name),
            Event::Function { name, call: false } => {
                if let Some(pos) = stack.iter().rposition(|stack_name| stack_name == name) {
                    stack.truncate(pos);
                }
            }
            Event::Fork(_, _, _, info) => {
                fork_events += 1;
                let stack_names = stack
                    .iter()
                    .map(|name| decoded_symbol(*name, shared_state))
                    .collect::<Vec<_>>();
                let innermost_function = stack_names.last().cloned().unwrap_or_else(|| "<unknown>".to_string());
                let stack_string = stack_names.join(" -> ");
                let location = info.location_string(shared_state.symtab.files());
                *sites.entry((location, innermost_function, stack_string)).or_insert(0) += 1;
            }
            _ => {}
        }
    }

    let unique_sites = sites.len();
    let mut top_sites = sites
        .into_iter()
        .map(|((location, innermost_function, stack), hits)| ForkProfileSite {
            location,
            innermost_function,
            stack,
            hits,
        })
        .collect::<Vec<_>>();
    top_sites.sort_by(|a, b| b.hits.cmp(&a.hits).then_with(|| a.stack.cmp(&b.stack)).then_with(|| a.location.cmp(&b.location)));
    top_sites.truncate(20);

    ForkProfilePath {
        asm: asm.to_string(),
        ret_val: ret_val.to_string(),
        fork_events,
        unique_sites,
        trace_len: events.len(),
        top_sites,
    }
}

fn constrain_symbolic_address<B: BV>(
    solver: &mut Solver<B>,
    address: &Val<B>,
    isa_config: &ISAConfig<B>,
) -> Result<(), ExecError> {
    use crate::smt::smtlib::Exp::{Bvsub, Bvuge, Bvult, Bvurem, Eq};

    if isa_config.symbolic_addr_top <= isa_config.symbolic_addr_base {
        return Ok(());
    }

    let info = SourceLoc::unknown();
    let address_len = length_bits(address, solver, info)?;
    let address_exp = smt_value(address, info)?;
    let base_exp = smt_sbits(B::new(isa_config.symbolic_addr_base, address_len));
    let top_exp = smt_sbits(B::new(isa_config.symbolic_addr_top, address_len));

    solver.assert(Bvuge(Box::new(address_exp.clone()), Box::new(base_exp.clone())));
    solver.assert(Bvult(Box::new(address_exp.clone()), Box::new(top_exp)));

    if isa_config.symbolic_addr_stride > 1 {
        let stride_exp = smt_sbits(B::new(isa_config.symbolic_addr_stride, address_len));
        let zero_exp = smt_sbits(B::zeros(address_len));
        solver.assert(Eq(
            Box::new(Bvurem(Box::new(Bvsub(Box::new(address_exp), Box::new(base_exp))), Box::new(stride_exp))),
            Box::new(zero_exp),
        ));
    }

    Ok(())
}

fn constrain_trace_memory_addresses<B: BV>(
    solver: &mut Solver<B>,
    isa_config: &ISAConfig<B>,
) -> Result<usize, ExecError> {
    let addresses: Vec<_> = solver
        .trace()
        .to_vec()
        .into_iter()
        .filter_map(|event| match event {
            Event::ReadMem { address, opts, .. } if !opts.is_ifetch => Some(address.clone()),
            Event::WriteMem { address, .. } => Some(address.clone()),
            _ => None,
        })
        .collect();

    for address in &addresses {
        constrain_symbolic_address(solver, address, isa_config)?;
    }

    Ok(addresses.len())
}

fn collect_memory_events<B: BV>(
    solver: &Solver<B>,
    model: &mut Model<B>,
    shared_state: &SharedState<B>,
) -> Vec<AssemGenMemoryEvent> {
    solver
        .trace()
        .to_vec()
        .into_iter()
        .rev()
        .filter_map(|event| {
            let is_exclusive = event.is_exclusive();
            match event {
                Event::ReadMem { value, address, bytes, opts, region, .. } => Some(AssemGenMemoryEvent {
                    kind: "read".to_string(),
                    region: (*region).to_string(),
                    bytes: *bytes,
                    address: address.to_string(shared_state),
                    address_model: model.get_val(address).ok().map(|v| v.to_string(shared_state)),
                    value: model.get_val(value).ok().map(|v| v.to_string(shared_state)),
                    data: None,
                    is_ifetch: opts.is_ifetch,
                    is_exclusive: opts.is_exclusive,
                }),
                Event::WriteMem { value, address, data, bytes, opts: _, region, .. } => Some(AssemGenMemoryEvent {
                    kind: "write".to_string(),
                    region: (*region).to_string(),
                    bytes: *bytes,
                    address: address.to_string(shared_state),
                    address_model: model.get_val(address).ok().map(|v| v.to_string(shared_state)),
                    value: model.get_var(*value).ok().map(|v| v.to_str()),
                    data: model.get_val(data).ok().map(|v| v.to_string(shared_state)),
                    is_ifetch: false,
                    is_exclusive,
                }),
                _ => None,
            }
        })
        .collect()
}

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

    let mut ret_val = symbolic(ctor_ty, shared_state, solver, SourceLoc::unknown())?;

    apply_instruction_arg_overrides(instruction_name, &mut ret_val, shared_state)?;

    Ok(ret_val)
}

#[derive(Copy, Clone)]
enum FixedInstructionFieldKind {
    Bits(u32),
    I64,
    Bool,
}

fn apply_instruction_arg_overrides<B: BV>(
    instruction_name: &str,
    instruction_arg: &mut Val<B>,
    shared_state: &SharedState<B>,
) -> Result<(), ExecError> {
    let overrides = match instruction_name {
        "zSTORE" => &[
            (
                "tuple#%bv12_%bv5_%bv5_%i640",
                Some("ISLA_RISCV_TEST_ZSTORE_IMM"),
                FixedInstructionFieldKind::Bits(12),
                "",
            ),
            ("tuple#%bv12_%bv5_%bv5_%i641", Some("ISLA_RISCV_TEST_ZSTORE_RS2"), FixedInstructionFieldKind::Bits(5), ""),
            ("tuple#%bv12_%bv5_%bv5_%i642", Some("ISLA_RISCV_TEST_ZSTORE_RS1"), FixedInstructionFieldKind::Bits(5), ""),
            ("tuple#%bv12_%bv5_%bv5_%i643", Some("ISLA_RISCV_TEST_ZSTORE_WIDTH"), FixedInstructionFieldKind::I64, ""),
        ][..],
        "zLOAD" => &[
            (
                "tuple#%bv12_%bv5_%bv5_%bool_%i640",
                Some("ISLA_RISCV_TEST_ZLOAD_IMM"),
                FixedInstructionFieldKind::Bits(12),
                "",
            ),
            (
                "tuple#%bv12_%bv5_%bv5_%bool_%i641",
                Some("ISLA_RISCV_TEST_ZLOAD_RS1"),
                FixedInstructionFieldKind::Bits(5),
                "",
            ),
            (
                "tuple#%bv12_%bv5_%bv5_%bool_%i642",
                Some("ISLA_RISCV_TEST_ZLOAD_RD"),
                FixedInstructionFieldKind::Bits(5),
                "",
            ),
            (
                "tuple#%bv12_%bv5_%bv5_%bool_%i643",
                Some("ISLA_RISCV_TEST_ZLOAD_IS_UNSIGNED"),
                FixedInstructionFieldKind::Bool,
                "",
            ),
            (
                "tuple#%bv12_%bv5_%bv5_%bool_%i644",
                Some("ISLA_RISCV_TEST_ZLOAD_WIDTH"),
                FixedInstructionFieldKind::I64,
                "",
            ),
        ][..],
        _ => &[][..],
    };

    for (field_name, env_name, field_kind, default_value) in overrides {
        let value = match env_name {
            Some(env_name) => match std::env::var(env_name) {
                Ok(value) => value,
                Err(_) => continue,
            },
            None => default_value.to_string(),
        };
        let parsed = parse_fixed_instruction_field_value(&value, *field_kind, shared_state)?;
        set_instruction_struct_field(instruction_arg, field_name, parsed, shared_state)?;
    }

    Ok(())
}

fn parse_fixed_instruction_field_value<B: BV>(
    value: &str,
    field_kind: FixedInstructionFieldKind,
    shared_state: &SharedState<B>,
) -> Result<Val<B>, ExecError> {
    match field_kind {
        FixedInstructionFieldKind::Bits(width) => parse_fixed_bits(value, width),
        FixedInstructionFieldKind::I64 => value.parse::<i64>().map(Val::I64).map_err(|err| {
            ExecError::Type(format!("invalid fixed instruction i64 value '{}': {}", value, err), SourceLoc::unknown())
        }),
        FixedInstructionFieldKind::Bool => match value {
            "1" | "true" | "True" | "TRUE" => Ok(Val::Bool(true)),
            "0" | "false" | "False" | "FALSE" => Ok(Val::Bool(false)),
            _ => Val::from_str(value, shared_state).map_err(|err| {
                ExecError::Type(
                    format!("invalid fixed instruction bool value '{}': {}", value, err),
                    SourceLoc::unknown(),
                )
            }),
        },
    }
}

fn parse_fixed_bits<B: BV>(value: &str, width: u32) -> Result<Val<B>, ExecError> {
    if width > B::MAX_WIDTH {
        return Err(ExecError::Type(
            format!("fixed instruction bitvector width {} exceeds BV max width {}", width, B::MAX_WIDTH),
            SourceLoc::unknown(),
        ));
    }

    if value.starts_with("0x") || value.starts_with("#x") || value.starts_with("0b") || value.starts_with("#b") {
        let bits = B::from_str(value).ok_or_else(|| {
            ExecError::Type(format!("invalid fixed instruction bitvector value '{}'", value), SourceLoc::unknown())
        })?;
        if bits.len() != width {
            return Err(ExecError::Type(
                format!("fixed instruction bitvector value '{}' has width {}, expected {}", value, bits.len(), width),
                SourceLoc::unknown(),
            ));
        }
        return Ok(Val::Bits(bits));
    }

    let raw = value.parse::<u64>().map_err(|err| {
        ExecError::Type(format!("invalid fixed instruction bitvector value '{}': {}", value, err), SourceLoc::unknown())
    })?;
    if width < 64 && raw >= (1_u64 << width) {
        return Err(ExecError::Type(
            format!("fixed instruction bitvector value {} does not fit in {} bits", raw, width),
            SourceLoc::unknown(),
        ));
    }
    Ok(Val::Bits(B::new(raw, width)))
}

fn set_instruction_struct_field<B: BV>(
    instruction_arg: &mut Val<B>,
    field_name: &str,
    value: Val<B>,
    shared_state: &SharedState<B>,
) -> Result<(), ExecError> {
    let encoded_field_name = zencode::encode(field_name);
    let Val::Struct(fields) = instruction_arg else {
        return Err(ExecError::Type(
            format!("fixed instruction override expected struct argument, got {:?}", instruction_arg),
            SourceLoc::unknown(),
        ));
    };

    let Some((_, field_value)) =
        fields.iter_mut().find(|(name, _)| shared_state.symtab.to_str(**name) == encoded_field_name)
    else {
        return Err(ExecError::Type(
            format!("fixed instruction override field {} not found", encoded_field_name),
            SourceLoc::unknown(),
        ));
    };

    *field_value = value;
    Ok(())
}
pub fn run_symbolic_execute<B: BV>(
    instruction_name: &str,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
    isa_config: &ISAConfig<B>,
) -> Result<Option<String>, ExecError> {
    use crate::smt::checkpoint;

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
    let isa_state_list = target.isa_state_list();
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
    println!("{:?}", isa_state_list);

    // 生成参数（暂时使用默认值，测试checkpoint机制）

    // 构造指令值

    let mut memory = Memory::new();
    if isa_config.symbolic_addr_top > isa_config.symbolic_addr_base {
        memory.add_symbolic_region(isa_config.symbolic_addr_base..isa_config.symbolic_addr_top);
    }

    // 创建checkpoint，包含符号化变量
    let cp = checkpoint(&mut solver);

    // 使用checkpoint执行函数，支持错误传播
    let result: Arc<Mutex<AssemGen_Json>> = Arc::new(Mutex::new(AssemGen_Json::new(Vec::new())));

    crate::executor::execute_ir_function_with_checkpoint_and_memory_multi_thread(
        "zexecute",
        &fun_args,
        shared_state,
        regs,
        lets,
        memory,
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
                        let mut memory_events = Vec::new();
                        // 获取ISA状态（寄存器、lets变量等）
                        // 首先检查solver是否可满足
                        if let Err(err) = constrain_trace_memory_addresses(&mut solver, isa_config) {
                            eprintln!("警告: {}添加 symbolic memory 约束失败: {:?}", instruction_name, err);
                            return;
                        }
                        if solver.check_sat(SourceLoc::unknown()) == crate::smt::SmtResult::Sat {
                            if let Ok(mut model) =
                                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| Model::new(&solver)))
                            {
                                println!("2. === ISA State (Thread {}) ===", thread);
                                // dlog!("fun_args={:#?}", model.get_val(&fun_args[0]));
                                let arg_val = match model.get_val(&fun_args[0]) {
                                    Ok(arg_val) => arg_val,
                                    Err(e) => {
                                        eprintln!("警告: {}没有汇编 {:?}", instruction_name, e);
                                        return;
                                    }
                                };
                                let Some(asm) = isarch::get_assembly_name(arg_val.clone(), shared_state, regs, lets)
                                else {
                                    return;
                                };
                                println!("当前汇编：{:?}", asm);
                                test_ins = asm;

                                let asm_encdec_opt = isarch::get_assembly_encdec(arg_val, shared_state, regs, lets)
                                    .map(|val| FmtVal::from_val(&val, &mut model).unwrap().to_str(shared_state));
                                println!("当前汇编encdec：{:?}", asm_encdec_opt);
                                let Some(encdec) = asm_encdec_opt else {
                                    return;
                                };
                                test_ins_encdec = encdec;

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
                                        let fmt_val = match model.get_fmtval(val) {
                                            Err(_exec_error) => continue,
                                            Ok(fmt_val) => fmt_val,
                                        };
                                        if fmt_val.is_arbitrary() {
                                            continue;
                                        }

                                        if isa_state_list.contains(&reg_name_decoded) {
                                            let formatted = fmt_val.to_str(shared_state);
                                            isa_state.insert(reg_name_decoded, formatted);
                                        }
                                    }
                                }

                                println!("isa_state={}", serde_json::to_string_pretty(&isa_state).unwrap());
                                let trace_len = solver.trace().to_vec().len();
                                memory_events = collect_memory_events(&solver, &mut model, shared_state);
                                println!("trace_len={}, memory_event_count={}", trace_len, memory_events.len());
                                println!("memory_events={}", serde_json::to_string_pretty(&memory_events).unwrap());
                                if profile_forks_enabled() {
                                    let ret_val_str = ret_val.to_str(shared_state).to_string();
                                    let profile = fork_profile_for_trace(&solver, shared_state, &test_ins, &ret_val_str);
                                    println!("fork_profile={}", serde_json::to_string(&profile).unwrap());
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
                                println!("3. ==============================\n");
                            }
                            solver.dump_solver("solver.dump");
                        }
                        let single_instruction_json = AssemGen_Json_Item::new(
                            &target,
                            test_ins,
                            test_ins_encdec,
                            isa_state,
                            memory_events,
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
    );

    // 提取字符串结果
    match Arc::try_unwrap(result) {
        Ok(result_mutex) => {
            let xlen_name = target.xlen_name();
            result_mutex.lock().unwrap().to_json(Some(format!("output/{}_{}.json", xlen_name, instruction_name)));
        }
        Err(_) => eprintln!("警告: {}无法获取 result 收集器", instruction_name),
    }
    Ok(None)
}

#[cfg(feature = "debug_exec")]
pub fn test_exec_main<B: BV>(
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
    isa_config: &ISAConfig<B>,
) {
    use std::{process::exit, vec};

    println!("test_exec_main");
    /* match run_symbolic_execute("zLOAD", shared_state, regs, lets, isa_config) {
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

    /*     let ext_i_instruction_table = [
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
    instruction_table.extend(ext_i_instruction_table.to_vec()); */

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

    let execute_through_instruction_table = ["zSTORE", "zLOAD"];
    instruction_table.extend(execute_through_instruction_table.to_vec());

    for ins_name in instruction_table {
        match run_symbolic_execute(ins_name, shared_state, regs, lets, isa_config) {
            Ok(_) => {}
            Err(e) => {
                eprintln!("test_exec_main: {}运行错误 {}", ins_name, e)
            }
        };
    }
}
