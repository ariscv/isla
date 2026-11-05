use super::clause::{get_extension_clauses, normalize_clause_name};
use super::memory_builder;
use super::memory_model;
use super::solve_summary::SolveSummary;
use super::target::{validate_fixed_prestate_value, Target, RISCV};
use super::timeout_report::TimeoutReporter;
pub use super::timeout_report::{TimeoutReportConfig, TimeoutSmtOutput};
use super::{get_all_clause_names, list_instructions, try_get_assembly_encdec, try_get_assembly_name};
use isla_lib::bitvector::BV;
use isla_lib::config::ExecutionLimitsConfig;
use isla_lib::error::IslaError;
use isla_lib::error::{ExecError, SmtError};
use isla_lib::executor::{backtrace_string, execute_ir_function, LocalFrame, Run};
use isla_lib::executor::{ExecutionLimits, TaskId, TaskState};
use isla_lib::fmtval::FmtVal;
use isla_lib::ir::*;
use isla_lib::ir_lexer::new_ir_lexer;
use isla_lib::log;
use isla_lib::primop_util::symbolic;
use isla_lib::register::RegisterBindings;
use isla_lib::smt::smtlib::Exp;
use isla_lib::smt::{Config, Context, Event, Model, ModelVal, Trace};
use isla_lib::smt::{Solver, Sym};
use isla_lib::source_loc::SourceLoc;
use isla_lib::value_parser;
use isla_lib::zencode;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::Duration;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FixedInstruction {
    pub bits: u64,
    pub width: u32,
}

pub struct FixedSolveInputs<B: BV> {
    pub instruction: Option<FixedInstruction>,
    pub prestate: HashMap<Name, Val<B>>,
}

impl<B: BV> Default for FixedSolveInputs<B> {
    fn default() -> Self {
        FixedSolveInputs { instruction: None, prestate: HashMap::new() }
    }
}

pub fn parse_fixed_instruction_bits(text: &str) -> Result<FixedInstruction, String> {
    let digits = text.strip_prefix("0x").ok_or_else(|| "--instruction-bits 需要 0x 前缀".to_string())?;
    let width = match digits.len() {
        4 => 16,
        8 => 32,
        _ => return Err("--instruction-bits 只接受四位或八位十六进制编码".to_string()),
    };
    if !digits.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err("--instruction-bits 含非十六进制字符".to_string());
    }
    let bits = u64::from_str_radix(digits, 16).expect("已验证的十六进制编码应可解析");
    if (width == 16 && bits & 3 == 3) || (width == 32 && bits & 3 != 3) {
        return Err("--instruction-bits 的编码长度与低两位不符".to_string());
    }
    Ok(FixedInstruction { bits, width })
}

pub fn parse_fixed_prestate<B: BV>(
    args: &[String],
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Result<HashMap<Name, Val<B>>, String> {
    let mut fixed = HashMap::new();
    for arg in args {
        let (loc, value) = value_parser::AssignParser::new()
            .parse(&shared_state.symtab, &shared_state.type_info, new_ir_lexer(arg))
            .map_err(|error| format!("--prestate '{}' 无法解析: {}", arg, error))?;
        let Loc::Id(reg_text) = loc else {
            return Err(format!("--prestate 只支持完整顶层寄存器赋值: {}", arg));
        };
        let reg_name = zencode::decode(&reg_text);
        let reg_id =
            shared_state.symtab.get(&reg_text).ok_or_else(|| format!("--prestate 未知寄存器: {}", reg_name))?;
        let ty = shared_state.registers.get(&reg_id).ok_or_else(|| format!("--prestate {} 不是寄存器", reg_name))?;
        if fixed.contains_key(&reg_id) {
            return Err(format!("--prestate 重复指定寄存器 {}", reg_name));
        }
        validate_fixed_prestate_value(&reg_name, reg_id, &value, ty, shared_state, lets, regs)?;
        fixed.insert(reg_id, value);
    }
    Ok(fixed)
}

fn fixed_value_is_concrete<B: BV>(value: &Val<B>) -> bool {
    match value {
        Val::Symbolic(_) | Val::SymbolicCtor(..) | Val::Poison => false,
        Val::MixedBits(segments) => segments.iter().all(|segment| matches!(segment, BitsSegment::Concrete(_))),
        Val::Vector(values) | Val::List(values) => values.iter().all(fixed_value_is_concrete),
        Val::Struct(fields) => fields.values().all(fixed_value_is_concrete),
        Val::Ctor(_, payload) => fixed_value_is_concrete(payload),
        _ => true,
    }
}

pub(crate) fn concrete_function_result<'ir, B: BV + Send + Sync>(
    function: &str,
    arg: Val<B>,
    shared_state: &'ir SharedState<'ir, B>,
    regs: &RegisterBindings<'ir, B>,
    lets: &Bindings<'ir, B>,
) -> Result<Val<B>, String> {
    let outcomes: Mutex<Vec<Result<Val<B>, String>>> = Mutex::new(Vec::new());
    execute_ir_function(
        function,
        &[arg],
        shared_state,
        regs,
        lets,
        &outcomes,
        &|_, _, result, _, mut solver, outcomes| match result {
            Ok((Run::Finished(value), _)) => match solver.check_sat(SourceLoc::unknown()) {
                isla_lib::smt::SmtResult::Sat => {
                    outcomes.lock().expect("decode outcomes mutex poisoned").push(Ok(value))
                }
                isla_lib::smt::SmtResult::Unsat => (),
                other => outcomes
                    .lock()
                    .expect("decode outcomes mutex poisoned")
                    .push(Err(format!("{} SMT 未得到 Sat/Unsat: {:?}", function, other))),
            },
            Ok((_, _)) => {
                outcomes.lock().expect("decode outcomes mutex poisoned").push(Err(format!("{} 未完成", function)))
            }
            Err((error, _)) => outcomes
                .lock()
                .expect("decode outcomes mutex poisoned")
                .push(Err(format!("{} 执行失败: {}", function, error))),
        },
    );
    let outcomes = outcomes.into_inner().expect("decode outcomes mutex poisoned");
    if outcomes.is_empty() {
        return Err(format!("{} 没有可满足路径", function));
    }
    let mut values = Vec::with_capacity(outcomes.len());
    for outcome in outcomes {
        values.push(outcome?);
    }
    if values.iter().any(|value| !fixed_value_is_concrete(value)) {
        return Err(format!("{} 返回依赖符号状态的值，不能跨solver复用", function));
    }
    if !values.iter().all(|value| *value == values[0]) {
        return Err(format!("{} 的多个可满足路径返回不同值", function));
    }
    Ok(values.remove(0))
}

/// `--instruction-bits` 译码（concrete_function_result → zext_decode）使用的
/// 寄存器环境：初始具体寄存器表 + `--prestate`/分片钉值覆盖。
///
/// 根因修复（G6/E/P1 三次撞到的 smt.rs:2168 "Could not get Z3 func_decl" 启动期
/// panic）：译码在独立 solver 中执行，而 setup_pre_state 之后的 symbolic_regs
/// 携带的是主 solver 声明的符号值；向量 clause 的译码守卫
/// （zencdec_backwards 分支经 zcurrentlyEnabled 读 zmstatus/zmisa）对这些符号
/// 做 neq 时，符号从未在译码 solver 里声明，translate_exp 直接 panic。译码
/// 语义只依赖固定编码位与用户钉定的架构状态，因此改用初始具体表加钉值：
/// 未钉值寄存器取 IR/config 初始化的具体默认值（如 mstatus.VS=Off，向量
/// 编码需按 E 线先例用 --prestate 钉 mstatus/cur_privilege 打开扩展域）。
pub(crate) fn decode_register_bindings<'ir, B: BV>(
    regs: &RegisterBindings<'ir, B>,
    prestate: &HashMap<Name, Val<B>>,
    shared_state: &SharedState<'ir, B>,
) -> RegisterBindings<'ir, B> {
    let mut decode_regs = regs.clone();
    for (&name, value) in prestate {
        decode_regs.assign(name, value.clone(), shared_state);
    }
    decode_regs
}

fn decode_fixed_instruction<'ir, B: BV + Send + Sync>(
    fixed: FixedInstruction,
    instruction_name: &str,
    shared_state: &'ir SharedState<'ir, B>,
    regs: &RegisterBindings<'ir, B>,
    lets: &Bindings<'ir, B>,
) -> Result<Val<B>, String> {
    let compressed = fixed.width == 16;
    let decoded = concrete_function_result(
        if compressed { "zext_decode_compressed" } else { "zext_decode" },
        Val::Bits(B::new(fixed.bits, fixed.width)),
        shared_state,
        regs,
        lets,
    )?;
    let Val::Ctor(ctor, _) = &decoded else {
        return Err("固定编码没有译码为指令构造子".to_string());
    };
    let expected = shared_state.symtab.lookup(instruction_name);
    if *ctor != expected {
        return Err(format!(
            "固定编码译码为 {}，与 --clause {} 不符",
            zencode::decode(shared_state.symtab.to_str_demangled(*ctor)),
            zencode::decode(shared_state.symtab.to_str_demangled(expected))
        ));
    }
    let encoded = concrete_function_result(
        if compressed { "zencdec_compressed_forwards" } else { "zencdec_forwards" },
        decoded.clone(),
        shared_state,
        regs,
        lets,
    )?;
    if encoded != Val::Bits(B::new(fixed.bits, fixed.width)) {
        return Err(format!("固定编码译码后重新编码不一致: {:?}", encoded));
    }
    Ok(decoded)
}

/// P3（plan-bughunt）encdec 守卫过滤：`zencdec_forwards` 产出的编码用
/// `zext_decode`（encdec 映射的 backwards 方向——`when` 守卫在译码侧
/// 生效）译回，构造子与原指令一致才放行。
///
/// 根因（B2 的 ldu 变体）：solve-state 对 union 载荷的自由求解选中了
/// execute 域内合法但 encdec 域外的参数组合（`LOAD(is_unsigned=true,
/// width=8)`，RV64 无 ldu，`valid_load_encdec` 对其返回 false）。物化门
/// 信任的 `zencdec_forwards` 在真实物化环境（载荷的 %i64 字段以 64 位
/// Bits 形态从 model 取回，实跑观察值为 0x8000_0000_0000_0009 一类的
/// 未约束垃圾值）下越过 when 守卫产出了 funct3=111 的编码；而
/// `zencdec_backwards` 对同一编码正确译出 ILLEGAL。encdec 守卫一致性
/// 因此以"译码回环"为准——这也是 DUT 侧的真实接受度。
///
/// 返回 `Ok(false)` 表示编码被守卫拒绝（调用方丢弃该路径并计数
/// `encdec-guard-reject`）；`Err` 表示译码器本身执行出错（内部错误按
/// "查不到不编造"丢弃路径并记诊断，不静默放行）。
pub(crate) fn encdec_guard_roundtrip_ok<B: BV>(
    instruction_ctor: Name,
    encdec_bits: &Val<B>,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Result<bool, String> {
    let bits_len = match encdec_bits {
        Val::Bits(bits) => bits.len(),
        other => return Err(format!("zencdec_forwards 返回非位向量编码: {:?}", other)),
    };
    let function = match bits_len {
        16 => "zext_decode_compressed",
        32 => "zext_decode",
        other => return Err(format!("zencdec_forwards 产出 {} 位编码，只支持 16/32 位译码回环", other)),
    };
    let collected: Arc<Mutex<Option<Result<Val<B>, ExecError>>>> = Arc::new(Mutex::new(None));
    {
        let sink = Arc::clone(&collected);
        execute_ir_function(
            function,
            &[encdec_bits.clone()],
            shared_state,
            regs,
            lets,
            &sink,
            &move |_, _, exec_result, _, _, sink| match exec_result {
                // MatchFailure 是"该编码在译码器里无可走分支"（守卫拒绝的
                // 正常形态），静默保持 None——与 try_get_assembly_* 的处理
                // 一致。
                Err((ExecError::MatchFailure(_), _)) => (),
                Err((error, _)) => {
                    *sink.lock().expect("回环译码收集器 mutex poisoned") = Some(Err(error));
                }
                Ok((Run::Finished(ret), _)) => {
                    *sink.lock().expect("回环译码收集器 mutex poisoned") = Some(Ok(ret));
                }
                Ok((_, _)) => (),
            },
        );
    }
    let outcome = collected.lock().expect("回环译码收集器 mutex poisoned").take();
    match outcome {
        // 无 Finished 路径：编码不可译（含守卫拒绝）。
        None => Ok(false),
        Some(Err(error)) => Err(format!("{} 译码回环执行失败: {}", function, error)),
        Some(Ok(Val::Ctor(decoded_ctor, _))) => Ok(decoded_ctor == instruction_ctor),
        Some(Ok(other)) => Err(format!("{} 译码结果不是指令构造子: {:?}", function, other)),
    }
}

/// P3：是否保留 encdec 守卫外的编码变体（默认过滤）。故意测试保留编码
/// 的场景（非法编码的译码/trap 行为）设 `ISLA_RISCV_ALLOW_RESERVED_ENCODINGS=1`。
pub(crate) fn parse_allow_reserved_encodings(raw: Option<&str>) -> bool {
    match raw {
        None => false,
        Some("1") => true,
        Some("0") => false,
        Some(other) => panic!("ISLA_RISCV_ALLOW_RESERVED_ENCODINGS 仅支持 0 或 1，实际为 '{}'", other),
    }
}

fn allow_reserved_encodings() -> bool {
    match std::env::var("ISLA_RISCV_ALLOW_RESERVED_ENCODINGS") {
        Ok(value) => parse_allow_reserved_encodings(Some(&value)),
        Err(std::env::VarError::NotPresent) => parse_allow_reserved_encodings(None),
        Err(err) => panic!("读取环境变量 ISLA_RISCV_ALLOW_RESERVED_ENCODINGS 失败: {}", err),
    }
}

/// 执行轨迹中访存事件（Event::ReadMem/WriteMem）的物化结果。
/// value/data 等 model 中查不到取值的分量序列化为 null（外部数据边界，不编造也不 panic）。
/// 同一事件可能跨路径重复，按 trace 顺序原样输出，不去重。
#[derive(Serialize, Deserialize, Clone)]
struct MemoryEventJson {
    kind: String,
    /// exclusive/CAS 写的 Bool 决定是否提交；普通写的 Bool 不表示提交成败。
    exclusive: bool,
    region: String,
    address: Option<String>,
    bytes: u32,
    /// read：读出的值；write：返回 Bool（仅独占写用作提交条件）
    value: Option<String>,
    /// write：写入的数据
    data: Option<String>,
}

/// 经 model 把 Val 物化为 FmtVal 输出风格的字符串；物化失败返回 None。
fn fmt_val_str<B: BV>(val: &Val<B>, model: &mut Model<'_, B>, shared_state: &SharedState<B>) -> Option<String> {
    FmtVal::from_val(val, model).ok().map(|fmt_val| fmt_val.to_str(shared_state))
}

/// pre/post 内存输出的稀疏记录：address 是连续段起始地址，bytes 是段长（不超过 8），
/// value 是把段内字节按小端拼成位向量后的 FmtVal 十六进制（如 `32'h1122_3344`）；
/// 段内任一字节内容未知时 value 为 null。
#[derive(Serialize, Deserialize, Clone)]
struct MemorySpanJson {
    address: String,
    bytes: u32,
    value: Option<String>,
}

/// 轨迹按真实执行顺序返回的访存事件（ReadMem/WriteMem）。
///
/// `smt.rs` 的 `Trace::to_vec` 先访问最新段、段内反向遍历，整体是逆时间序
/// （事件 push 在段 head 末尾）；这里先取出再整体反转，恢复事件发生的先后顺序。
fn memory_events_chronological<B: BV>(trace: &Trace<B>) -> Vec<&Event<B>> {
    let mut events = trace.to_vec();
    events.reverse();
    events.into_iter().filter(|event| event.is_memory_read_or_write()).collect()
}

/// 单条访存事件物化后的重放输入。
///
/// payload 是读事件的读值或写事件的写数据按小端拆出的字节序列，长度等于事件
/// 的 bytes；地址或数值分量查不到模型具体值时对应字段为 None（不编造）。
struct ReplayAccess {
    is_read: bool,
    is_exclusive: bool,
    /// 仅 exclusive 写事件使用；None 表示 model 无法判定是否提交。
    write_success: Option<bool>,
    address: Option<u64>,
    bytes: u32,
    payload: Option<Vec<u8>>,
}

/// pre/post 内存重放结果（字节 → 内容稀疏映射）。
struct ReplayMemory {
    /// 每个触碰字节在首次被触碰时的内容：首触是读则取该读值的对应字节；
    /// 首触是已提交写则该字节初值自由，记 None（输出 null）。
    pre: BTreeMap<u64, Option<u8>>,
    /// 重放结束后的最终字节内容：只读未写的字节取最后一次读值（数组模型下同址
    /// 读值一致，与写数据一致）；最后一次触碰的分量未知时记 None。
    post: BTreeMap<u64, Option<u8>>,
    /// 地址或数值分量查不到模型值的事件分量计数（物化失败的诊断计数）。
    unknown_components: usize,
}

/// 按真实执行顺序重放访存事件，维护"字节 → 当前内容"映射。
///
/// 读事件把读值按小端拆到 `addr..addr+bytes`，写事件把写数据拆进去（覆盖），
/// 小端字节序与 W2 数组内存模型（`memory_model.rs` 的 Select/Store 链）一致。
/// 地址未知的事件整体跳过并计数。
fn replay_memory(accesses: &[ReplayAccess]) -> ReplayMemory {
    let mut replay = ReplayMemory { pre: BTreeMap::new(), post: BTreeMap::new(), unknown_components: 0 };
    for access in accesses {
        if !access.is_read && access.is_exclusive {
            match access.write_success {
                Some(false) => continue,
                None => {
                    replay.unknown_components += 1;
                    if let Some(address) = access.address {
                        for index in 0..access.bytes {
                            let byte_address = address.wrapping_add(u64::from(index));
                            replay.pre.entry(byte_address).or_insert(None);
                            replay.post.insert(byte_address, None);
                        }
                    } else {
                        replay.unknown_components += 1;
                    }
                    continue;
                }
                Some(true) => (),
            }
        }
        let Some(address) = access.address else {
            replay.unknown_components += 1;
            continue;
        };
        let payload = match &access.payload {
            Some(payload) => payload.as_slice(),
            None => {
                replay.unknown_components += 1;
                &[]
            }
        };
        for index in 0..access.bytes as usize {
            let byte_address = address.wrapping_add(index as u64);
            let byte = payload.get(index).copied();
            // 首触是读：pre 取读值对应字节；首触是写：初值自由记 None，
            // 不拿写数据编造初值；首触分量查不到模型值（byte 为 None）同样记 None
            replay.pre.entry(byte_address).or_insert_with(|| if access.is_read { byte } else { None });
            replay.post.insert(byte_address, byte);
        }
    }
    replay
}

/// 小端字节序列（不超过 8 字节）转 u64；超长返回 None（RV64 地址恒 64 位）。
fn le_bytes_to_u64(bytes: &[u8]) -> Option<u64> {
    if bytes.len() > 8 {
        return None;
    }
    let mut buffer = [0u8; 8];
    buffer[..bytes.len()].copy_from_slice(bytes);
    Some(u64::from_le_bytes(buffer))
}

/// 位序列（下标 0 是最低位）按小端拼成字节序列。
fn le_bytes_from_bits(bits: &[bool]) -> Vec<u8> {
    bits.chunks(8)
        .map(|chunk| chunk.iter().enumerate().fold(0u8, |acc, (i, bit)| acc | (u8::from(*bit) << i)))
        .collect()
}

/// 经 model 把位向量 Val 物化为小端字节序列。
///
/// 支持 Symbolic / Bits / MixedBits；模型未给出具体值（Arbitrary 等）或类型不是
/// 位向量时返回 None（外部数据边界，不编造）。
fn materialize_le_bytes<B: BV>(val: &Val<B>, model: &mut Model<'_, B>) -> Option<Vec<u8>> {
    match val {
        Val::Symbolic(sym) => match model.get_var(*sym).ok()? {
            ModelVal::Exp(Exp::Bits64(bv)) => Some(bv.to_le_bytes()),
            ModelVal::Exp(Exp::Bits(bits)) => Some(le_bytes_from_bits(&bits)),
            ModelVal::Exp(_) | ModelVal::Arbitrary(_) => None,
        },
        Val::Bits(bv) => Some(bv.to_le_bytes()),
        Val::MixedBits(segments) => {
            let mut bits = Vec::new();
            for segment in segments {
                match segment {
                    BitsSegment::Concrete(bv) => {
                        for index in 0..bv.len() {
                            bits.push(bv.slice(index, 1).expect("混合位串索引必须有效").lower_u64() == 1);
                        }
                    }
                    BitsSegment::Symbolic(sym) => match model.get_var(*sym).ok()? {
                        ModelVal::Exp(Exp::Bits64(bv)) => {
                            for index in 0..bv.len() {
                                bits.push(bv.slice(index, 1).expect("模型位串索引必须有效").lower_u64() == 1);
                            }
                        }
                        ModelVal::Exp(Exp::Bits(part)) => bits.extend(part.iter().copied()),
                        ModelVal::Exp(_) | ModelVal::Arbitrary(_) => return None,
                    },
                }
            }
            Some(le_bytes_from_bits(&bits))
        }
        _ => None,
    }
}

/// 经 model 物化单条访存事件为重放输入：读事件传读值、写事件传写数据，
/// 地址经 `le_bytes_to_u64` 收窄为 u64；分量查不到模型值时对应字段为 None。
fn materialize_replay_access<B: BV>(
    is_read: bool,
    is_exclusive: bool,
    write_success: Option<bool>,
    payload: &Val<B>,
    address: &Val<B>,
    bytes: u32,
    model: &mut Model<'_, B>,
) -> ReplayAccess {
    let address = materialize_le_bytes(address, model).and_then(|bytes| le_bytes_to_u64(&bytes));
    let payload = match materialize_le_bytes(payload, model) {
        Some(payload) => {
            assert_eq!(payload.len(), bytes as usize, "访存事件的载荷位宽必须与 bytes 一致");
            Some(payload)
        }
        None => None,
    };
    ReplayAccess { is_read, is_exclusive, write_success, address, bytes, payload }
}

/// 把重放得到的字节映射序列化为稀疏连续段：相邻字节且已知性一致时合并为一段，
/// 段长封顶 8 字节（FmtVal 位向量以 64 位为限）。
fn memory_spans_json<B: BV>(bytes: &BTreeMap<u64, Option<u8>>, shared_state: &SharedState<B>) -> Vec<MemorySpanJson> {
    let fmt_bits = |value: u64, len: u32| -> String {
        FmtVal::from_exp(&Exp::Bits64(isla_lib::bitvector::b64::B64::new(value, len)))
            .expect("FmtVal 必须能格式化 64 位以内的具体位向量")
            .to_str(shared_state)
    };

    let mut spans = Vec::new();
    let mut entries = bytes.iter().peekable();
    while let Some((&address, &first)) = entries.next() {
        let mut run = vec![first];
        while let Some((&next_address, &next_value)) = entries.peek() {
            if address.checked_add(run.len() as u64) == Some(next_address)
                && next_value.is_some() == first.is_some()
                && run.len() < 8
            {
                run.push(next_value);
                entries.next();
            } else {
                break;
            }
        }
        let value = if first.is_some() {
            let mut value = 0u64;
            for (index, byte) in run.iter().enumerate() {
                value |= u64::from(byte.expect("已知段内的字节内容必须存在")) << (8 * index);
            }
            Some(fmt_bits(value, (run.len() * 8) as u32))
        } else {
            None
        };
        spans.push(MemorySpanJson { address: fmt_bits(address, 64), bytes: run.len() as u32, value });
    }
    spans
}

/// 若 `zexecute` 的返回值是 `ExecuteAs(转换后的指令)`，返回转换后的指令。
///
/// 参照 sail 模型外层模式（sail-riscv `postlude/step.sail`：
/// `ExecuteAs(other_inst) => execute(other_inst)`），solve-state 收集到该返回值
/// 时应继续执行转换后的指令。载荷不是指令构造子属于模型不变量违反，直接 panic。
fn execute_as_instruction<'a, B: BV>(ret_val: &'a Val<B>, shared_state: &SharedState<B>) -> Option<&'a Val<B>> {
    match ret_val {
        Val::Ctor(ctor, payload) if zencode::decode(shared_state.symtab.to_str_demangled(*ctor)) == "ExecuteAs" => {
            match &**payload {
                Val::Ctor(..) => Some(payload),
                other => panic!("ExecuteAs 载荷应是指令构造子，实际 {:?}", other),
            }
        }
        _ => None,
    }
}

#[allow(non_camel_case_types)]
#[derive(Serialize, Deserialize, Clone)]
struct AssemGenJsonItem {
    #[serde(rename = "path-signature")]
    path_signature: u64,
    arch: BTreeMap<String, String>,
    #[serde(rename = "test-ins")]
    test_ins: String,
    #[serde(rename = "test-ins-encdec")]
    test_ins_encdec: String,
    #[serde(rename = "isa-state")]
    isa_state: BTreeMap<String, String>,
    ret_val: String,
    /// 按真实执行顺序排列的访存事件（地址/数值经 model 物化，查不到输出 null）
    #[serde(rename = "memory-events")]
    memory_events: Vec<MemoryEventJson>,
    /// 指令执行前每个被触碰字节的初始内容（稀疏连续段；首触是写的字节初值自由，输出 null）
    #[serde(rename = "pre-memory")]
    pre_memory: Vec<MemorySpanJson>,
    /// 指令执行后每个被触碰字节的最终内容（稀疏连续段；只读未写的字节取最后一次读值）
    #[serde(rename = "post-memory")]
    post_memory: Vec<MemorySpanJson>,
    /// P1 值域 signposting：产出该用例的 hint 批标签（自由批为 None，不序列化，
    /// 保证无 hints 配置的 JSON 输出与既有逐项一致）
    #[serde(rename = "value-hint", skip_serializing_if = "Option::is_none")]
    value_hint: Option<String>,
    /// P2 编码维度预分片：产出该用例的分片标签（自由批为 None，不序列化，
    /// 保证无分片配置的 JSON 输出与既有逐项一致）
    #[serde(rename = "encoding-slice", skip_serializing_if = "Option::is_none")]
    encoding_slice: Option<String>,
}
impl AssemGenJsonItem {
    pub fn new<B: BV>(
        target: &dyn Target<B>,
        test_ins: String,
        test_ins_encdec: String,
        isa_state: BTreeMap<String, String>,
        ret_val: String,
        memory_events: Vec<MemoryEventJson>,
        pre_memory: Vec<MemorySpanJson>,
        post_memory: Vec<MemorySpanJson>,
    ) -> Self {
        let mut arch = BTreeMap::new();
        arch.insert("pretty-name".to_string(), target.arch_pretty_name().to_string());
        arch.insert("name".to_string(), target.arch_name().to_string());
        arch.insert("xlen".to_string(), target.xlen().to_string());
        arch.insert("ext".to_string(), "IMACFD".to_string());
        AssemGenJsonItem {
            path_signature: 0,
            arch,
            test_ins,
            test_ins_encdec,
            isa_state,
            ret_val,
            memory_events,
            pre_memory,
            post_memory,
            value_hint: None,
            encoding_slice: None,
        }
    }

    /// P1 值域 signposting：批调度层为 hint 批的产出打上批标签。
    fn with_hint_label(mut self, label: Option<&str>) -> Self {
        self.value_hint = label.map(str::to_string);
        self
    }

    /// P2 编码维度预分片：批调度层为分片批的产出打上批标签。
    fn with_slice_label(mut self, label: Option<&str>) -> Self {
        self.encoding_slice = label.map(str::to_string);
        self
    }
}
trait ToJSON: Serialize {
    #[allow(dead_code)]
    fn to_json_str(&self) -> String {
        serde_json::to_string_pretty(self).unwrap()
    }
    fn to_json(&self, file_path: Option<String>) {
        let mut value = serde_json::to_value(self).unwrap();
        if value.get("gen").is_some() {
            value["provenance"] = super::solve_summary::input_manifest();
        }
        let json = serde_json::to_string_pretty(&value).unwrap();
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
    summary: serde_json::Value,
    diagnostics: Vec<serde_json::Value>,
    gen: Vec<AssemGenJsonItem>,
    /// P3 encdec 守卫过滤：被丢弃的非法编码变体计数（reason → 条数）。
    /// 为空时不序列化，保证零拒绝时 JSON 输出与既有逐字节一致。
    #[serde(skip_serializing_if = "BTreeMap::is_empty", default)]
    skip: BTreeMap<String, u64>,
}
impl ToJSON for AssemGenJson {}
impl ToJSON for AssemGenJsonItem {}
impl AssemGenJson {
    fn new(gen: Vec<AssemGenJsonItem>) -> Self {
        AssemGenJson { gen, skip: BTreeMap::new(), summary: SolveSummary::default().json(), diagnostics: Vec::new() }
    }
}

/// 一条完成的用例 + 它的路径签名。签名用于收尾阶段的稳定排序与配额取样，让多线程下
/// 的产出顺序不影响最终落盘的用例集合（按 codex 评审意见的"路径局部指纹 + 全量 canonical sort"）。
#[derive(Clone)]
struct CollectedCase {
    path_signature: u64,
    item: AssemGenJsonItem,
    /// 终值查询超时的路径仅供diagnostics使用，不进入gen。
    materialization_timed_out: bool,
}

struct SolveCollectorState {
    summary: SolveSummary,
    cases: Vec<CollectedCase>,
    case_quota: Option<CaseQuota>,
    first_error: Option<ExecError>,
    /// 终值查询（最终 check_sat + 取模型）超过时间盒而降级输出的路径数。
    model_query_timeouts: usize,
    /// P3 encdec 守卫过滤：编码未被译码器认回（execute 域越过 encdec 守卫
    /// 的非法变体，如 RV64 的 ldu）而被丢弃的路径数。
    encdec_guard_rejects: usize,
}

impl SolveCollectorState {
    fn new() -> Self {
        Self::with_case_quota(None)
    }

    fn with_case_quota(case_quota: Option<CaseQuota>) -> Self {
        SolveCollectorState {
            summary: SolveSummary::default(),
            first_error: None,
            cases: Vec::new(),
            case_quota,
            model_query_timeouts: 0,
            encdec_guard_rejects: 0,
        }
    }

    fn record_error(&mut self, error: &ExecError) -> bool {
        self.summary.errors += 1;
        self.summary.execution_timeouts += usize::from(matches!(error, ExecError::Timeout));
        self.summary.smt_timeouts += usize::from(matches!(error, ExecError::Smt(SmtError::Timeout(_))));
        let error = match error {
            ExecError::Timeout => ExecError::Timeout,
            ExecError::Smt(error) => ExecError::Smt(error.clone()),
            ExecError::Z3Unknown => ExecError::Z3Unknown,
            _ => return false,
        };
        if self.first_error.is_none() {
            self.first_error = Some(error);
        }
        true
    }

    fn record_model_query_timeout(&mut self) {
        self.model_query_timeouts += 1;
    }

    /// P3：encdec 守卫回环拒绝一条非法编码变体路径。
    fn record_encdec_guard_reject(&mut self) {
        self.encdec_guard_rejects += 1;
    }
}

/// solve-state 路径终值物化（最终 `check_sat` + 取模型）的时间盒。
///
/// 环境变量 `ISLA_RISCV_MODEL_TIMEOUT_MS`（毫秒，默认 30000）。数组内存模型
/// （W2）在路径尾部累积的 Select/Store + 区域约束可能让终值重解远慢于执行期
/// 查询；超时路径按 W3"查不到输出 null 不编造"规则降级输出而不是卡死整个
/// clause。真正中断 Z3 需 `smt-thread-interrupt` feature（`make solve-%` 默认
/// 开启），否则 deadline 不生效、行为与普通 `check_sat` 一致。
fn parse_model_timeout_ms(raw: Option<&str>) -> Duration {
    const DEFAULT_MODEL_TIMEOUT_MS: u64 = 30_000;
    match raw {
        None => Duration::from_millis(DEFAULT_MODEL_TIMEOUT_MS),
        Some(raw) => match raw.trim().parse::<u64>() {
            Ok(ms) if ms > 0 => Duration::from_millis(ms),
            _ => panic!("ISLA_RISCV_MODEL_TIMEOUT_MS 必须是正整数毫秒，实际 '{}'", raw),
        },
    }
}

fn model_query_deadline() -> Duration {
    match std::env::var("ISLA_RISCV_MODEL_TIMEOUT_MS") {
        Ok(value) => parse_model_timeout_ms(Some(&value)),
        Err(std::env::VarError::NotPresent) => parse_model_timeout_ms(None),
        Err(err) => panic!("读取环境变量 ISLA_RISCV_MODEL_TIMEOUT_MS 失败: {}", err),
    }
}

struct ErrorRecorder<'a> {
    collected: &'a Mutex<SolveCollectorState>,
    reporter: &'a TimeoutReporter,
    clause: &'a str,
}

impl ErrorRecorder<'_> {
    fn record_error_diagnostic<'ir, B: BV>(
        &self,
        error: &ExecError,
        frame: &LocalFrame<'ir, B>,
        shared_state: &SharedState<'ir, B>,
    ) -> Vec<(isla_lib::timeout::TimeoutDiagnostic, bool)> {
        frame.configure_timeout_smt_dump(error, shared_state);
        self.record_configured_error_diagnostic(error)
    }

    fn record_configured_error_diagnostic(
        &self,
        error: &ExecError,
    ) -> Vec<(isla_lib::timeout::TimeoutDiagnostic, bool)> {
        if !self.collected.lock().expect("solve collector mutex poisoned").record_error(error) {
            return Vec::new();
        }
        let diagnostics = match error {
            ExecError::Smt(SmtError::Timeout(timeout)) => {
                let diagnostic = isla_lib::timeout::TimeoutDiagnostic::Smt(timeout.clone());
                drop(diagnostic.dump().materialize());
                vec![(diagnostic, self.reporter.itrace_enabled())]
            }
            _ => Vec::new(),
        };
        self.reporter.report_error(self.clause, error);
        diagnostics
    }
}

fn should_collect_unfinished_path<B: BV>(run: &Run<B>) -> bool {
    !matches!(run, Run::Dead)
}

/// 收集一个值里出现的全部符号变量，按出现顺序去重。
///
/// 结构体字段按 `Name`（符号 ID）排序，避免随机哈希表迭代顺序影响候选的字段序号。
fn collect_symbolic_vars<B: BV>(value: &Val<B>, symbols: &mut Vec<Sym>) {
    match value {
        Val::Symbolic(sym) => {
            if !symbols.contains(sym) {
                symbols.push(*sym)
            }
        }
        Val::Vector(values) | Val::List(values) => {
            for value in values {
                collect_symbolic_vars(value, symbols)
            }
        }
        Val::Struct(fields) => {
            let mut fields: Vec<_> = fields.iter().collect();
            fields.sort_unstable_by_key(|(name, _)| name.as_u32());
            for (_, value) in fields {
                collect_symbolic_vars(value, symbols)
            }
        }
        Val::Ctor(_, value) => collect_symbolic_vars(value, symbols),
        Val::SymbolicCtor(sym, fields) => {
            if !symbols.contains(sym) {
                symbols.push(*sym)
            }
            let mut fields: Vec<_> = fields.iter().collect();
            fields.sort_unstable_by_key(|(name, _)| name.as_u32());
            for (_, value) in fields {
                collect_symbolic_vars(value, symbols)
            }
        }
        _ => (),
    }
}

/// SplitMix64 的单轮混合；同一路径和字段序号始终得到同一候选值。
fn splitmix64(mut value: u64) -> u64 {
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

/// 生成给定宽度位向量的一个确定性候选值。
///
/// 位宽超过 64 时仍是有限域，但不能只复用一个 64 位随机数；这里每 64 位独立混合一次，
/// 并保持 `Exp::Bits` 所要求的低位在前的位序。
fn bitvector_candidate(seed: u64, width: u32) -> isla_lib::smt::smtlib::Exp<Sym> {
    if width <= 64 {
        let value = if width == 64 { splitmix64(seed) } else { splitmix64(seed) & ((1u64 << width) - 1) };
        return isla_lib::smt::smtlib::Exp::Bits64(isla_lib::bitvector::b64::B64::new(value, width));
    }

    let mut bits = Vec::with_capacity(width as usize);
    for word_index in 0..((width + 63) / 64) {
        let word = splitmix64(seed.wrapping_add(word_index as u64));
        let word_width = (width - word_index * 64).min(64);
        for bit_index in 0..word_width {
            bits.push((word >> bit_index) & 1 == 1);
        }
    }
    isla_lib::smt::smtlib::Exp::Bits(bits)
}

/// 为路径未约束到的有限域字段选择不同的代表值。
///
/// `funct6` 等枚举字段若在 dispatch 前就走到 `Illegal_Instruction()`，Z3 会在每条这样的
/// 非法路径上都返回同一个默认成员，致使全部非法用例集中标到同一条子指令。布尔值和位向量也有同样
/// 问题，例如未约束的寄存器号会反复取 `v0`。这里按路径签名和字段序号为 enum、bool、
/// bitvector 各生成一个确定性候选；位向量虽可能很宽，但每条非法路径只尝试一个候选，绝不
/// 枚举指数大小的完整取值空间。bool/bitvector 只处理模型明确标为 `Arbitrary` 的字段，并把
/// 全部候选合并成一次 `check_sat_with`；成功路径不会调用本函数，避免不必要地增加高路径数
/// 指令的 SMT 查询。
///
/// 每个候选必须先经 `check_sat_with` 验证才能 `Assert`。路径已约束到其它值时验证为
/// `Unsat`，不会被改动；可满足时钉住的值本来就是该路径的模型，因此只影响原先的
/// "任意值"如何实例化，不改变路径语义。
fn diversify_unconstrained_finite_domains<'ir, B: BV>(
    args: &[Val<B>],
    signature: u64,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<(), ExecError> {
    let mut symbols = Vec::new();
    for arg in args {
        collect_symbolic_vars(arg, &mut symbols)
    }
    if symbols.is_empty() {
        return Ok(());
    }

    // 先用一个模型识别各符号的有限域类型。bool/bitvector 只有在模型明确标为 Arbitrary
    // 时才多样化；有具体模型值说明路径至少部分依赖它，不能为每个这样的字段额外做 SMT 查询。
    let mut finite_domain_symbols = Vec::new();
    match solver.check_sat(SourceLoc::unknown()) {
        isla_lib::smt::SmtResult::Sat => (),
        isla_lib::smt::SmtResult::Unsat | isla_lib::smt::SmtResult::Unknown => return Ok(()),
        isla_lib::smt::SmtResult::Error(error) => return Err(ExecError::Smt(error)),
    }
    {
        let mut model = Model::new(solver);
        for sym in symbols {
            match model.get_finite_domain_var(sym)? {
                Some(isla_lib::smt::ModelVal::Exp(isla_lib::smt::smtlib::Exp::Enum(member))) => {
                    finite_domain_symbols.push((sym, FiniteDomain::Enum(member)))
                }
                Some(isla_lib::smt::ModelVal::Arbitrary(isla_lib::smt::smtlib::Ty::Bool)) => {
                    finite_domain_symbols.push((sym, FiniteDomain::ArbitraryBool))
                }
                Some(isla_lib::smt::ModelVal::Arbitrary(isla_lib::smt::smtlib::Ty::BitVec(width))) => {
                    finite_domain_symbols.push((sym, FiniteDomain::ArbitraryBitVec(width)))
                }
                Some(_) | None => (),
            }
        }
    }

    // 枚举保留旧实现的成员轮转顺序，避免无关 bool/bitvector 字段的加入改变既有 enum 用例。
    let mut enum_index = 0;
    let mut arbitrary_preferred = None;
    for (index, (sym, domain)) in finite_domain_symbols.into_iter().enumerate() {
        let seed = signature ^ index as u64;
        match domain {
            FiniteDomain::Enum(member) => {
                let member_index = enum_index;
                enum_index += 1;
                let members = match shared_state.type_info.enums.get(&member.enum_id.to_name()) {
                    Some(members) if members.len() > 1 => members.len(),
                    _ => continue,
                };
                let candidate = (signature.wrapping_add(member_index) % members as u64) as usize;
                if candidate == member.member {
                    continue;
                }
                let candidate = isla_lib::smt::smtlib::Exp::Enum(isla_lib::smt::EnumMember {
                    enum_id: member.enum_id,
                    member: candidate,
                });
                let preferred =
                    isla_lib::smt::smtlib::Exp::Eq(Box::new(isla_lib::smt::smtlib::Exp::Var(sym)), Box::new(candidate));
                // Unsat 说明这条路径已经把该字段约束成别的值了，保持原样。
                match solver.check_sat_with(&preferred, SourceLoc::unknown()) {
                    isla_lib::smt::SmtResult::Sat => solver.add(isla_lib::smt::smtlib::Def::Assert(preferred)),
                    isla_lib::smt::SmtResult::Unsat | isla_lib::smt::SmtResult::Unknown => (),
                    isla_lib::smt::SmtResult::Error(error) => return Err(ExecError::Smt(error)),
                }
            }
            FiniteDomain::ArbitraryBool | FiniteDomain::ArbitraryBitVec(_) => {
                let candidate = match domain {
                    FiniteDomain::ArbitraryBool => isla_lib::smt::smtlib::Exp::Bool(splitmix64(seed) & 1 == 1),
                    FiniteDomain::ArbitraryBitVec(width) => bitvector_candidate(seed, width),
                    FiniteDomain::Enum(_) => unreachable!(),
                };
                let preferred =
                    isla_lib::smt::smtlib::Exp::Eq(Box::new(isla_lib::smt::smtlib::Exp::Var(sym)), Box::new(candidate));
                arbitrary_preferred = Some(match arbitrary_preferred {
                    Some(previous) => isla_lib::smt::smtlib::Exp::And(Box::new(previous), Box::new(preferred)),
                    None => preferred,
                });
            }
        }
    }
    // 同一条路径的全部无解释 bool/bitvector 候选一起验证，避免字段数线性放大 SMT 查询数。
    if let Some(preferred) = arbitrary_preferred {
        match solver.check_sat_with(&preferred, SourceLoc::unknown()) {
            isla_lib::smt::SmtResult::Sat => solver.add(isla_lib::smt::smtlib::Def::Assert(preferred)),
            isla_lib::smt::SmtResult::Unsat | isla_lib::smt::SmtResult::Unknown => (),
            isla_lib::smt::SmtResult::Error(error) => return Err(ExecError::Smt(error)),
        }
    }
    Ok(())
}

enum FiniteDomain {
    Enum(isla_lib::smt::EnumMember),
    ArbitraryBool,
    ArbitraryBitVec(u32),
}

/// 输出层配额：按 `(助记符, 完整 test-ins, ret_val 类别)` 分组，每组最多保留 N 条。
///
/// 这是 KLEE `emittedErrors` 的可复现改写——把"限流只作用在输出层、执行路径一条不少"
/// 的设计原样保留，把全局 static 集合换成"所有 worker join 后做一次确定性归并"。
/// 成功用例（`Retire_Success`）默认不限量，配额只压非法用例。
///
/// 分组键带了完整 `test-ins`：同一个非法编码配不同 vtype 各算一条是主要冗余形态，
/// 按 `(助记符, test-ins)` 分组能让这些落在同一个桶里被均匀取样。
#[derive(Clone, Debug, Default)]
pub struct CaseQuota {
    /// 按 `ret_val` 类别名做前缀过滤的配额。key 是 ret_val 字符串里的构造子名
    /// （例如 `Illegal_Instruction`、`Retire_Success`），value 是每组上限。
    /// 未列出的类别不限量。
    pub per_class: BTreeMap<String, u32>,
}

impl CaseQuota {
    fn from_config(map: &BTreeMap<String, u32>) -> Self {
        CaseQuota { per_class: map.clone() }
    }

    fn limit_for(&self, ret_val: &str) -> Option<u32> {
        // ret_val 形如 "Illegal_Instruction(())" / "Retire_Success(())"，取构造子名做匹配。
        let name = ret_val.split('(').next().unwrap_or(ret_val);
        self.per_class.get(name).copied()
    }
}

/// 收尾阶段的确定性归并：分组配额 + 全量 canonical sort。
///
/// 顺序由 `path_signature` + 序列化文本（tie-breaker）决定，与 worker 调度无关，
/// 因此 THREADS=1/4/64 跑出来的 JSON 逐字节一致。
fn finalize_cases(mut cases: Vec<CollectedCase>, quota: &Option<CaseQuota>) -> Vec<AssemGenJsonItem> {
    // gen只保留已具体化的可重放见证，超时终态由批次层单独写入diagnostics。
    cases.retain(|case| {
        !case.materialization_timed_out && !case.item.test_ins.is_empty() && !case.item.test_ins_encdec.is_empty()
    });
    // 1. 组内配额：按 (助记符, 完整 test-ins, ret_val 类别) 分桶，每组按签名均匀取样。
    if let Some(quota) = quota {
        cases = apply_case_quota(cases, quota);
    }
    // 2. 全量稳定排序：签名 + 序列化文本做 tie-breaker，杜绝签名碰撞时的调度依赖。
    cases.sort_by(|a, b| {
        let a_text = serde_json::to_string(&a.item).expect("AssemGenJsonItem 序列化失败");
        let b_text = serde_json::to_string(&b.item).expect("AssemGenJsonItem 序列化失败");
        a.path_signature.cmp(&b.path_signature).then_with(|| a_text.cmp(&b_text))
    });
    cases
        .into_iter()
        .map(|mut case| {
            case.item.path_signature = case.path_signature;
            case.item
        })
        .collect()
}

fn apply_case_quota(cases: Vec<CollectedCase>, quota: &CaseQuota) -> Vec<CollectedCase> {
    use std::collections::HashMap;
    // 先按分组键装桶。
    let mut buckets: HashMap<(String, String, String), Vec<CollectedCase>> = HashMap::new();
    for case in cases {
        let mnemonic = case.item.test_ins.split_whitespace().next().unwrap_or("").to_string();
        let ret_class = case.item.ret_val.split('(').next().unwrap_or("").to_string();
        let key = (mnemonic, case.item.test_ins.clone(), ret_class);
        buckets.entry(key).or_default().push(case);
    }
    // 每个桶按 ret_val 类别查配额；超过配额的按签名均匀取样。
    let mut kept = Vec::with_capacity(buckets.values().map(|v| v.len()).sum());
    for (_, mut bucket) in buckets {
        let limit = bucket.first().and_then(|c| quota.limit_for(&c.item.ret_val));
        match limit {
            Some(0) => {}
            Some(n) if (n as usize) < bucket.len() => {
                bucket.sort_by(|a, b| {
                    let a_text = serde_json::to_string(&a.item).expect("AssemGenJsonItem 序列化失败");
                    let b_text = serde_json::to_string(&b.item).expect("AssemGenJsonItem 序列化失败");
                    a.path_signature.cmp(&b.path_signature).then_with(|| a_text.cmp(&b_text))
                });
                let k = bucket.len();
                for i in 0..n as usize {
                    // 均匀取样：在排序后的桶里等间距取 n 个，比取前 n 更能让 vtype/操作数分散。
                    let idx = if n == 1 { 0 } else { i * (k - 1) / (n as usize - 1) };
                    kept.push(bucket[idx].clone());
                }
            }
            _ => kept.extend(bucket),
        }
    }
    kept
}

fn solve_execution_limits(symtab: &Symtab, config: Option<&ExecutionLimitsConfig>) -> ExecutionLimits {
    match config {
        Some(config) => ExecutionLimits::default().with_config(config, symtab),
        None => ExecutionLimits::default(),
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
    timeout_report_config: TimeoutReportConfig,
    fixed_inputs: &FixedSolveInputs<B>,
    value_hints: &[isla_lib::config::ValueHintConfig],
    region_configs: super::value_hints::RegionConfigInput<'_>,
    encoding_slices: &[isla_lib::config::EncodingSliceConfig],
) -> bool {
    let case_quota = execution_limits_config.and_then(|cfg| cfg.case_quota.as_ref().map(CaseQuota::from_config));
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

    shared_state.execution_stats.reset();
    if shared_state.execution_stats.enabled() {
        // 限时场景下进程可能被外层强杀，收尾打印不会执行；ISLA_STATS=1 时周期性输出快照。
        let stats = shared_state.execution_stats.clone();
        // 仅用于实验：快照线程只读符号表，且不会在 shared_state 释放后被唤醒再访问到有意义的数据；
        // 进程退出前线程随之终止。
        let symtab: &'static isla_lib::ir::Symtab<'static> = unsafe { std::mem::transmute(&shared_state.symtab) };
        std::thread::spawn(move || loop {
            std::thread::sleep(std::time::Duration::from_secs(15));
            eprintln!("[MERGE_STATS_SNAPSHOT] {}", stats.merge_json());
            eprintln!("[FORK_STATS_SNAPSHOT] {}", stats.fork_json(symtab));
            eprintln!("[ARM_UNSUPPORTED_SNAPSHOT] {}", stats.arm_unsupported_json(symtab));
        });
    }
    let num_clauses = clause_set.len();
    log!(log::SYM_EXEC, &format!("solve_state: 共 {} 个 clause 待执行", num_clauses));
    let execution_limits = solve_execution_limits(&shared_state.symtab, execution_limits_config);
    let timeout_reporter = TimeoutReporter::new(timeout_report_config);

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

        // P2 编码维度预分片：配置声明了该 clause 的分片时接管批计划（自由
        // 对照批 + 每片钉死编码的求解批）。两套钉值通道（编码分片 × 值域
        // hint）组合是配置级爆炸面，分片激活时该 clause 的 value_hints 批
        // 让位并记日志；无分片声明时维持 P1 的 hint 批计划。
        let slice_batches = match super::encoding_slices::plan_slice_batches(
            encoding_slices,
            &clause,
            shared_state,
            regs,
            lets,
            &fixed_inputs.prestate,
            fixed_inputs.instruction,
        ) {
            Ok(batches) => batches,
            Err(error) => {
                eprintln!("错误: clause '{}' 编码分片批计划失败: {}", clause, error);
                log!(log::SYM_EXEC, &format!("solve_state: {} 编码分片批计划错误 {}", clause, error));
                success = false;
                continue;
            }
        };
        if slice_batches.is_some() {
            // W21 同名冲突在计划期拦下（分片 prestate 与 [symbolic_registers] 的
            // 矛盾不该等到执行期防御 panic）
            let csr_conflict = target.symbolic_csrs().iter().find_map(|csr| {
                let conflict = encoding_slices
                    .iter()
                    .filter(|slice| normalize_clause_name(&slice.clause) == clause)
                    .any(|slice| slice.prestate.contains_key(&csr.name));
                conflict.then(|| {
                    format!(
                        "编码分片 prestate 钉值 {} 与 [symbolic_registers] 同名冲突（符号化 CSR 不能再钉具体值）",
                        csr.name
                    )
                })
            });
            if let Some(error) = csr_conflict {
                eprintln!("错误: clause '{}' {}", clause, error);
                log!(log::SYM_EXEC, &format!("solve_state: {} {}", clause, error));
                success = false;
                continue;
            }
            let has_hints = value_hints.iter().any(|hint| super::value_hints::hint_matches_clause(hint, &clause));
            if has_hints {
                log!(
                    log::SYM_EXEC,
                    &format!(
                        "solve_state: {} 编码分片激活，value_hints 批让位（分片批已钉编码，避免两套钉值笛卡尔积）",
                        clause
                    )
                );
            }
        }
        // P1 值域 signposting：批调度——首批恒为自由批（无提示档对照，保证
        // signposting 不压缩纯符号路径），其后为作用域内 hint 候选批。批间不
        // 共享假设：每批独立重置 checkpoint 求解，产出合并写入同一 JSON。
        let batches = match slice_batches {
            Some(batches) => batches,
            None => match super::value_hints::plan_solve_batches(
                value_hints,
                &clause,
                region_configs,
                shared_state,
                regs,
                lets,
                &fixed_inputs.prestate,
            ) {
                Ok(batches) => batches,
                Err(error) => {
                    eprintln!("错误: clause '{}' 值域 hint 批计划失败: {}", clause, error);
                    log!(log::SYM_EXEC, &format!("solve_state: {} hint 计划错误 {}", clause, error));
                    success = false;
                    continue;
                }
            },
        };
        if batches.len() > 1 {
            log!(
                log::SYM_EXEC,
                &format!(
                    "solve_state: {} 共 {} 个求解批（1 自由批 + {} 个钉值批）",
                    clause,
                    batches.len(),
                    batches.len() - 1
                )
            );
        }

        let mut merged_summary = SolveSummary::default();
        let mut merged_diagnostics = Vec::new();
        let mut merged_items: Vec<AssemGenJsonItem> = Vec::new();
        // P3 encdec 守卫过滤：跨批累计被拒条数，随 JSON 落盘（reason 固定
        // encdec-guard-reject），下游 build/summary 与重放侧可见。
        let mut merged_encdec_guard_rejects: u64 = 0;
        for (batch_index, batch) in batches.iter().enumerate() {
            let batch_label = batch.label.as_deref();
            log!(
                log::SYM_EXEC,
                &format!(
                    "solve_state: {} 求解批 {}/{}: {}",
                    clause,
                    batch_index + 1,
                    batches.len(),
                    batch_label.unwrap_or("自由批（无 hint）")
                )
            );
            let batch_inputs = FixedSolveInputs {
                instruction: batch.instruction.or(fixed_inputs.instruction),
                prestate: batch.prestate.clone(),
            };
            // P2 分片预算：时间盒取分片覆写与全局 --timeout 的较小值
            let batch_timeout = match batch.timeout {
                Some(timebox) => Some(timeout.map(|global| global.min(timebox)).unwrap_or(timebox)),
                None => timeout,
            };
            match run_symbolic_execute_with_target(
                target,
                &clause,
                shared_state,
                regs,
                lets,
                initial_memory.clone(),
                num_threads,
                batch_timeout,
                &execution_limits,
                &timeout_reporter,
                case_quota.clone(),
                &batch_inputs,
                batch_label,
                batch.label.as_deref().filter(|label| label.starts_with("enc-slice:")),
                batch.case_limit,
            ) {
                Ok(outcome) => {
                    log!(
                        log::SYM_EXEC,
                        &format!(
                            "solve_state: {} 批 {}/{} 完成，产出 {} 条用例{}",
                            clause,
                            batch_index + 1,
                            batches.len(),
                            outcome.items.len(),
                            if outcome.error.is_some() { "（含执行错误，已保留部分产出）" } else { "" }
                        )
                    );
                    // 出错批已物化的部分用例仍保留（与既有"错误路径也落盘"语义
                    // 一致）；执行期错误只终止本批，继续跑剩余批——单批超时不
                    // 应吞掉其他批的产出
                    if let Some(error) = outcome.error {
                        eprintln!(
                            "错误: clause '{}' 符号执行失败（批 {}/{} {}）: {}",
                            clause,
                            batch_index + 1,
                            batches.len(),
                            batch_label.unwrap_or("自由批"),
                            error
                        );
                        log!(
                            log::SYM_EXEC,
                            &format!(
                                "solve_state: {}运行错误 {} (批 {})",
                                clause,
                                error,
                                batch_label.unwrap_or("自由批")
                            )
                        );
                        success = false;
                    }
                    merged_summary.merge(&outcome.summary);
                    merged_diagnostics.extend(outcome.diagnostics);
                    merged_items.extend(outcome.items);
                    merged_encdec_guard_rejects += outcome.encdec_guard_rejects as u64;
                }
                Err(error) => {
                    eprintln!(
                        "错误: clause '{}' 符号执行启动失败（批 {}/{} {}）: {}",
                        clause,
                        batch_index + 1,
                        batches.len(),
                        batch_label.unwrap_or("自由批"),
                        error
                    );
                    log!(
                        log::SYM_EXEC,
                        &format!("solve_state: {}启动错误 {} (批 {})", clause, error, batch_label.unwrap_or("自由批"))
                    );
                    success = false;
                    merged_summary.errors += 1;
                }
            }
            // 每批后增量落盘（覆写为已合并全集）：外层时间盒硬杀时，已完成批的
            // 产出不随进程丢失
            let mut json = AssemGenJson::new(merged_items.clone());
            merged_summary.pending_batches = batches.len() - batch_index - 1;
            json.summary = merged_summary.json();
            json.summary["target-clause"] = serde_json::json!(clause);
            json.diagnostics = merged_diagnostics.clone();
            if merged_encdec_guard_rejects > 0 {
                json.skip.insert("encdec-guard-reject".to_string(), merged_encdec_guard_rejects);
            }
            json.to_json(Some(format!("output/{}_{}.json", target.arch_pretty_name(), clause)));
        }

        #[cfg(feature = "itrace")]
        if itrace_path.is_some() {
            shared_state.itrace.dump();
        }
    }

    super::solve_summary::print_execution_stats(shared_state);
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

/// ExecuteAs 续执行快照（不携带 'ir，避免 Vec 不变性把收集闭包的生命周期钉死在
/// 外层 'ir 上）：转换后的指令 + 本路径 solver 的 checkpoint。
///
/// 模型中 ExecuteAs 仅由压缩指令解码 clause 产生（sail-riscv extensions/C/*），
/// 返回前没有访存或寄存器写入副作用，因此续执行轮次直接用初始符号寄存器/初始
/// 内存重建 zexecute 调用帧：数组内存模型的状态链（DefineConst 序列）随
/// checkpoint 重放延续，语义等价于在外层重新执行解码出的指令。
struct ExecuteAsContinuation<B: BV> {
    instruction: Val<B>,
    checkpoint: isla_lib::smt::Checkpoint<B>,
}

/// solve-state 路径收集的共享只读环境：首段闭包与续执行轮次的转发闭包共用，
/// 保证续执行路径与首段路径走同一套收集逻辑（同一 JSON 项结构、同一配额桶）。
struct SolvePathCtx<'a, 'ir, B: BV> {
    target: &'a dyn Target<B>,
    instruction_name: &'a str,
    fun_args: &'a [Val<B>],
    regs: &'a RegisterBindings<'ir, B>,
    lets: &'a Bindings<'ir, B>,
    timeout_reporter: &'a TimeoutReporter,
    task_state: &'a TaskState<B>,
    continuations: &'a Mutex<Vec<ExecuteAsContinuation<B>>>,
    /// P1 值域 signposting：当前批的 hint 标签（自由批为 None），随每条产出
    /// 用例写入 JSON 的 value-hint 字段
    hint_label: Option<&'a str>,
    /// P2 编码维度预分片：当前批的分片标签（自由批为 None），随每条产出
    /// 用例写入 JSON 的 encoding-slice 字段
    slice_label: Option<&'a str>,
}

/// solve-state 单条完成路径的收集逻辑（自 collector 闭包迁出）：Sat 路径物化 JSON 项；
/// ExecuteAs 返回值入队续执行快照，由外层循环统一多线程执行。
fn solve_collect_path<'ir, B: BV>(
    ctx: &SolvePathCtx<'_, 'ir, B>,
    thread: usize,
    _task_id: TaskId,
    exec_result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, LocalFrame<'ir, B>)>,
    shared_state: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    collected: &Mutex<SolveCollectorState>,
) {
    {
        let frame = match &exec_result {
            Ok((_, frame)) | Err((_, frame)) => frame,
        };
        let mut state = collected.lock().expect("solve collector mutex poisoned");
        state.summary.sampled_paths += usize::from(frame.has_sampled_branch());
        match &exec_result {
            Ok((Run::Finished(Val::Poison) | Run::Exit | Run::Suspended, _)) => state.summary.unfinished_paths += 1,
            Err((ExecError::AssertionFailure(_, _), _)) => state.summary.assertion_filtered_paths += 1,
            _ => (),
        }
    }
    let mut itrace_diagnostics = Vec::new();
    let submit_itrace = |frame, diagnostics: &mut Vec<(isla_lib::timeout::TimeoutDiagnostic, bool)>| {
        isla_lib::executor::submit_itrace_for_local_frame_with_diagnostics(
            frame,
            shared_state,
            std::mem::take(diagnostics),
        );
    };
    let error_recorder = ErrorRecorder { collected, reporter: ctx.timeout_reporter, clause: ctx.instruction_name };
    let should_submit_itrace = match &exec_result {
        Ok((Run::Finished(_), _)) => true,
        Ok((run, _)) => should_collect_unfinished_path(run),
        Err((ExecError::AssertionFailure(_, _), _)) => false,
        Err((error, frame)) => {
            itrace_diagnostics = error_recorder.record_error_diagnostic(error, frame, shared_state);
            true
        }
    };

    match &exec_result {
        Ok((run, frame)) => match run {
            Run::Finished(Val::Poison) => {
                log!(log::SYM_EXEC, &format!("警告: {}这个Ctor返回值是Poison，可能是相关扩展（如H扩展）造成的，因此产生了sail的_inner_error_", ctx.instruction_name))
            }
            Run::Finished(ret_val) => {
                // 压缩指令（如 C_LD/C_SD）的 clause 解码后直接返回 ExecuteAs(转换后的指令)，
                // 不产生访存；参照模型外层模式（sail-riscv postlude/step.sail：
                // `ExecuteAs(other_inst) => execute(other_inst)`）继续执行转换后的指令。
                // 这里入队（转换后的指令、本路径 solver 的 checkpoint），外层轮次循环统一
                // 重建调用帧执行：checkpoint 重放含前段全部事件，W2 数组内存模型的状态链
                // （DefineConst 序列）随之延续，续执行产生的访存事件进入同一条路径轨迹。
                if let Some(instruction) = execute_as_instruction(ret_val, shared_state) {
                    log!(log::SYM_EXEC, &format!("{} 返回 ExecuteAs，入队续执行转换后的指令", ctx.instruction_name));
                    if should_submit_itrace {
                        submit_itrace(frame, &mut itrace_diagnostics);
                    }
                    // 只入队不执行：外层循环在本轮全部首段路径完成后统一排空队列并
                    // 用多线程池跑续执行（转换后的指令如 LOAD 自身会大量 fork，
                    // 串行执行会把整棵子树压在单个 worker 上）。
                    ctx.continuations.lock().expect("ExecuteAs 续执行队列 mutex poisoned").push(
                        ExecuteAsContinuation {
                            instruction: instruction.clone(),
                            checkpoint: isla_lib::smt::checkpoint(&mut solver),
                        },
                    );
                    return;
                }
                let ret_val_str = ret_val.to_str(shared_state).to_string();
                log!(
                    log::PATH_RESULT,
                    &format!("1. tid:{} 执行好一条路径，fork={}，ret_val={}", thread, frame.forks(), ret_val_str)
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
                                    get_assembly_name(arg_val.clone(), &shared_state, ctx.regs, ctx.lets)
                                }
                                _ => panic!(""),
                            }
                        }
                        _ => panic!(""),
                    }
                };
                println!("assembly:{:#?}", assembly); */
                // isarch::get_assembly_name(Val::Unit /* ??? */, &shared_state, ctx.regs, ctx.lets);

                let mut test_ins = String::new();
                let mut test_ins_encdec = String::new();
                let mut isa_state: BTreeMap<String, String> = BTreeMap::new();
                let mut memory_events: Vec<MemoryEventJson> = Vec::new();
                let mut pre_memory: Vec<MemorySpanJson> = Vec::new();
                let mut post_memory: Vec<MemorySpanJson> = Vec::new();
                if matches!(
                    ret_val,
                    Val::Ctor(ctor, _)
                        if zencode::decode(shared_state.symtab.to_str_demangled(*ctor))
                            == "Illegal_Instruction"
                ) {
                    // 未被这条非法路径约束的有限域字段（典型是提前返回 Illegal 的路径上的
                    // funct6）先按路径签名挑一个代表值钉住，否则所有这类用例都会被标注
                    // 成同一条子指令，寄存器号等位向量字段也会反复取 Z3 默认值。
                    match diversify_unconstrained_finite_domains(
                        &ctx.fun_args,
                        frame.path_signature(),
                        shared_state,
                        &mut solver,
                    ) {
                        Ok(()) => (),
                        Err(error @ (ExecError::Timeout | ExecError::Smt(_))) => {
                            itrace_diagnostics = error_recorder.record_error_diagnostic(&error, frame, shared_state);
                            log!(log::SYM_EXEC, &format!("finite-domain diversification failed: {}", error));
                            submit_itrace(frame, &mut itrace_diagnostics);
                            return;
                        }
                        Err(error) => {
                            panic!("finite-domain diversification invariant violated: {}", error)
                        }
                    }
                }
                // 获取ISA状态（寄存器、lets变量等）
                // 首先检查solver是否可满足。
                // 终值查询策略（W6）：真实访存路径的最后一次 SMT 操作通常是
                // `__monomorphize` 的唯一性探测（Unsat 的 check_sat_with），Z3 随后
                // 丢弃自己的"最后模型"，旧实现此处重解整条路径（数组模型的
                // Select/Store + 区域约束累积后极慢，W5 观测 202/310 条卡死）。因此：
                // 1) 优先取 solver 缓存的"最近一次 Sat check"模型——自那次 check 后
                //    没有新增 Assert（探测不改变断言集）时它与当前断言集一致，
                //    直接取值跳过重解（零成本）；
                // 2) 无缓存（缓存后被新增 Assert 失效，或从未 Sat 过）时带时间盒
                //    重解（ISLA_RISCV_MODEL_TIMEOUT_MS，默认 30s），超时按 W3
                //    "查不到输出 null 不编造"规则降级输出：ret_val 照常，其余模型
                //    物化字段置空并计数，保证真实访存 clause 一定能出完整 JSON。
                if solver.has_stashed_model() {
                    log!(
                        log::PATH_RESULT,
                        &format!("2. tid:{} 终值复用缓存的 Sat 模型（断言集未变，跳过重解）", thread)
                    );
                } else {
                    log!(
                        log::PATH_RESULT,
                        &format!(
                            "2. tid:{} 终值重解（最后一次 check 是否 Sat：{}，其后新增 Assert {} 条）",
                            thread,
                            solver.last_check_was_sat(),
                            solver.asserts_since_check()
                        )
                    );
                    match solver.check_sat_deadline(SourceLoc::unknown(), model_query_deadline()) {
                        // Sat 的重解会刷新 solver 的模型缓存，与复用路径统一从缓存取
                        isla_lib::smt::SmtResult::Sat => (),
                        isla_lib::smt::SmtResult::Unsat => {
                            log!(log::SYM_EXEC, "collector 丢弃 Unsat 完成路径");
                            if let Ok(dir) = std::env::var("ISLA_RISCV_DUMP_UNSAT_DIR") {
                                // 目录不存在时先创建：W7 复跑曾因 dump 目录缺失让
                                // File::create panic 杀掉整个进程（rc=134），诊断
                                // 开关不应有杀死主流程的能力。
                                std::fs::create_dir_all(&dir)
                                    .unwrap_or_else(|err| panic!("创建 Unsat dump 目录 {} 失败: {}", dir, err));
                                let path = format!("{}/unsat_{}_t{}.smt2", dir, ctx.instruction_name, thread);
                                solver.dump_solver(&path);
                                log!(log::SYM_EXEC, &format!("已导出 Unsat 路径求解器: {}", path));
                            }
                            submit_itrace(frame, &mut itrace_diagnostics);
                            return;
                        }
                        isla_lib::smt::SmtResult::Unknown => {
                            let error = ExecError::Z3Unknown;
                            itrace_diagnostics = error_recorder.record_error_diagnostic(&error, frame, shared_state);
                            log!(log::SYM_EXEC, &format!("collector final SMT query failed: {}", error));
                            submit_itrace(frame, &mut itrace_diagnostics);
                            return;
                        }
                        isla_lib::smt::SmtResult::Error(error)
                            if matches!(error, isla_lib::error::SmtError::Timeout(_)) =>
                        {
                            // 整路径超时降级：与"单分量查不到输出 null"同一规则（W3），
                            // 只是范围扩大到整条路径的模型物化字段。
                            collected.lock().expect("solve collector mutex poisoned").record_model_query_timeout();
                            log!(
                                log::PATH_RESULT,
                                &format!(
                                    "警告: clause{} 路径终值查询超过时间盒 {:?}，降级输出（ret_val 照常，访存与 pre-state 分量置空）",
                                    ctx.instruction_name,
                                    model_query_deadline()
                                )
                            );
                            let single_instruction_json = AssemGenJsonItem::new(
                                ctx.target,
                                String::new(),
                                String::new(),
                                BTreeMap::new(),
                                ret_val_str.clone(),
                                Vec::new(),
                                Vec::new(),
                                Vec::new(),
                            );
                            collected.lock().expect("solve collector mutex poisoned").cases.push(CollectedCase {
                                path_signature: frame.path_signature(),
                                item: single_instruction_json,
                                materialization_timed_out: true,
                            });
                            submit_itrace(frame, &mut itrace_diagnostics);
                            return;
                        }
                        isla_lib::smt::SmtResult::Error(error) => {
                            let error = ExecError::Smt(error);
                            itrace_diagnostics = error_recorder.record_error_diagnostic(&error, frame, shared_state);
                            log!(log::SYM_EXEC, &format!("collector final SMT query failed: {}", error));
                            submit_itrace(frame, &mut itrace_diagnostics);
                            return;
                        }
                    }
                }
                // 先取 trace（模型借用存活期间不再访问 solver）：复用与重解两条
                // 路径的事件序列都来自路径终态轨迹，与取模型顺序无关。clone 成
                // 所有值，避免事件引用延续对 solver 的不可变借用。
                let trace_events: Vec<Event<B>> =
                    memory_events_chronological(solver.trace()).into_iter().cloned().collect();
                // 统一取模型：复用路径取既有缓存，重解路径取刚刷新的缓存。
                let mut model = match solver.take_stashed_model() {
                    Some(model) => model,
                    None => panic!("collector 在 SAT 完成路径上无法取得 SMT model"),
                };
                {
                    // 开启 model completion：未被约束的 pre-state 符号变量也会得到一个具体值，
                    // 这样所有主动符号化的 pre-state 寄存器都能输出（与 testgen 一致）。
                    // model.set_complete_model(true);
                    log!(log::PATH_RESULT, &format!("2. === ISA State (Thread {}) ===", thread));
                    let test = Sym::from_u32(6);
                    // dlog!("model.get_var({:?})={:?}", test, model.get_var(test));
                    // dlog!("ctx.fun_args={:#?}", model.get_val(&ctx.fun_args[0]));
                    // W21：encdec/assembly 门（下方 try_get_assembly_*）以独立 solver +
                    // ctx.regs 执行 zencdec/zassembly，读 CSR 时按具体值评估守卫
                    //（如 currentlyEnabled(Ext_Zcd) 的 mstatus[FS]）。声明了符号 CSR
                    // 时必须换成按当前路径模型具象化的克隆——否则门一直看到 defaults
                    // 的旧具体值（FS=Off 令 Zcd 物化全灭，即 G8 根因）。具象化失败
                    // 的路径按"查不到不编造"丢弃，不落假用例。
                    let concretized_gate_regs;
                    let gate_regs = if ctx.target.symbolic_csrs().is_empty() {
                        ctx.regs
                    } else {
                        match ctx.target.concretize_symbolic_csrs(ctx.regs, &mut model, shared_state) {
                            Ok(regs) => {
                                concretized_gate_regs = regs;
                                &concretized_gate_regs
                            }
                            Err(error) => {
                                itrace_diagnostics =
                                    error_recorder.record_error_diagnostic(&error, frame, shared_state);
                                log!(
                                    log::PATH_RESULT,
                                    &format!("警告: clause{} 符号 CSR 门具象化失败 {:?}", ctx.instruction_name, error)
                                );
                                submit_itrace(frame, &mut itrace_diagnostics);
                                return;
                            }
                        }
                    };
                    match model.get_val(&ctx.fun_args[0]) {
                        Ok(arg_val) => {
                            let asm_opt =
                                match try_get_assembly_name(arg_val.clone(), shared_state, gate_regs, ctx.lets) {
                                    Ok(assembly) => assembly,
                                    Err(error) => {
                                        itrace_diagnostics = error_recorder.record_configured_error_diagnostic(&error);
                                        log!(
                                            log::PATH_RESULT,
                                            &format!(
                                                "警告: clause{} 汇编名称求解失败 {:?}",
                                                ctx.instruction_name, error
                                            )
                                        );
                                        submit_itrace(frame, &mut itrace_diagnostics);
                                        return;
                                    }
                                };
                            log!(log::PATH_RESULT, &format!("当前汇编：{:?}", asm_opt));
                            match asm_opt {
                                Some(asm) => test_ins = asm,
                                None => {
                                    submit_itrace(frame, &mut itrace_diagnostics);
                                    return;
                                }
                            }
                            let asm_encdec_opt =
                                match try_get_assembly_encdec(arg_val.clone(), shared_state, gate_regs, ctx.lets) {
                                    Ok(encoded) => match encoded {
                                        Some(val) => {
                                            // P3 encdec 守卫过滤：forwards 产出的编码必须能被
                                            // 译码器认回同一构造子（when 守卫在 backwards 方向
                                            // 生效），否则丢弃并计数 encdec-guard-reject。
                                            // ISLA_RISCV_ALLOW_RESERVED_ENCODINGS=1 显式保留
                                            // （故意测试保留编码的场景）。
                                            if !allow_reserved_encodings() {
                                                let expected_ctor = match &arg_val {
                                                    Val::Ctor(ctor, _) => *ctor,
                                                    other => panic!("指令参数应是构造子值，实际 {:?}", other),
                                                };
                                                match encdec_guard_roundtrip_ok(
                                                    expected_ctor,
                                                    &val,
                                                    shared_state,
                                                    gate_regs,
                                                    ctx.lets,
                                                ) {
                                                    Ok(true) => (),
                                                    Ok(false) => {
                                                        collected
                                                            .lock()
                                                            .expect("solve collector mutex poisoned")
                                                            .record_encdec_guard_reject();
                                                        log!(
                                                            log::PATH_RESULT,
                                                            &format!(
                                                                "clause{} encdec 守卫拒绝非法编码变体（test-ins={}）",
                                                                ctx.instruction_name, test_ins
                                                            )
                                                        );
                                                        submit_itrace(frame, &mut itrace_diagnostics);
                                                        return;
                                                    }
                                                    Err(error) => {
                                                        log!(
                                                            log::PATH_RESULT,
                                                            &format!(
                                                                "警告: clause{} encdec 守卫回环译码失败，丢弃路径: {}",
                                                                ctx.instruction_name, error
                                                            )
                                                        );
                                                        submit_itrace(frame, &mut itrace_diagnostics);
                                                        return;
                                                    }
                                                }
                                            }
                                            match FmtVal::from_val(&val, &mut model) {
                                                Ok(fmt_val) => Some(fmt_val.to_str(shared_state)),
                                                Err(err) => {
                                                    itrace_diagnostics = error_recorder.record_error_diagnostic(
                                                        &err,
                                                        frame,
                                                        shared_state,
                                                    );
                                                    log!(
                                                        log::PATH_RESULT,
                                                        &format!(
                                                            "警告: {}汇编编码不可格式化 {:?}",
                                                            ctx.instruction_name, err
                                                        )
                                                    );
                                                    None
                                                }
                                            }
                                        }
                                        None => None,
                                    },
                                    Err(error) => {
                                        itrace_diagnostics = error_recorder.record_configured_error_diagnostic(&error);
                                        log!(
                                            log::PATH_RESULT,
                                            &format!(
                                                "警告: clause{} 汇编编码求解失败 {:?}",
                                                ctx.instruction_name, error
                                            )
                                        );
                                        submit_itrace(frame, &mut itrace_diagnostics);
                                        return;
                                    }
                                };
                            log!(log::PATH_RESULT, &format!("当前汇编encdec：{:?}", asm_encdec_opt));
                            match asm_encdec_opt {
                                Some(encdec) => test_ins_encdec = encdec,
                                None => {
                                    submit_itrace(frame, &mut itrace_diagnostics);
                                    return;
                                }
                            }
                        }
                        Err(e) => {
                            itrace_diagnostics = error_recorder.record_error_diagnostic(&e, frame, shared_state);
                            log!(
                                log::PATH_RESULT,
                                &format!("警告: clause{} model.get_val失败 {:?}", ctx.instruction_name, e)
                            );
                            submit_itrace(frame, &mut itrace_diagnostics);
                            return;
                        }
                    }

                    // pre-state 取值：通过 ctx.target 和 setup 阶段生成的 PreStateCtx 查询具体解。
                    match ctx.target.solve_pre_state(&mut model, shared_state) {
                        Ok(state) => isa_state.extend(state),
                        Err(error) => {
                            itrace_diagnostics = error_recorder.record_error_diagnostic(&error, frame, shared_state);
                            log!(
                                log::PATH_RESULT,
                                &format!("警告: clause{} pre-state求解失败 {:?}", ctx.instruction_name, error)
                            );
                            submit_itrace(frame, &mut itrace_diagnostics);
                            return;
                        }
                    }

                    log!(log::PATH_RESULT, &format!("isa_state={}", serde_json::to_string_pretty(&isa_state).unwrap()));
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
                    // 物化执行轨迹中的访存事件：smt.rs Trace::to_vec 是逆时间序，
                    // memory_events_chronological 整体反转恢复真实执行顺序；
                    // ReadMem/WriteMem 逐个经 model 取具体值，
                    // model 中查不到的分量输出 null（外部数据边界，不编造）。
                    let mut replay_accesses = Vec::with_capacity(trace_events.len());
                    for event in &trace_events {
                        match event {
                            Event::ReadMem { value, address, bytes, region, opts, .. } => {
                                memory_events.push(MemoryEventJson {
                                    kind: "read".to_string(),
                                    exclusive: opts.is_exclusive,
                                    region: region.to_string(),
                                    address: fmt_val_str(address, &mut model, shared_state),
                                    bytes: *bytes,
                                    value: fmt_val_str(value, &mut model, shared_state),
                                    data: None,
                                });
                                replay_accesses.push(materialize_replay_access(
                                    true, false, None, value, address, *bytes, &mut model,
                                ));
                            }
                            Event::WriteMem { value, address, data, bytes, region, opts, .. } => {
                                memory_events.push(MemoryEventJson {
                                    kind: "write".to_string(),
                                    exclusive: opts.is_exclusive(),
                                    region: region.to_string(),
                                    address: fmt_val_str(address, &mut model, shared_state),
                                    bytes: *bytes,
                                    value: model
                                        .get_var(*value)
                                        .ok()
                                        .and_then(|model_val| FmtVal::from_model_val(&model_val))
                                        .map(|fmt_val| fmt_val.to_str(shared_state)),
                                    data: fmt_val_str(data, &mut model, shared_state),
                                });
                                let write_success = if opts.is_exclusive() {
                                    match model.get_var(*value) {
                                        Ok(ModelVal::Exp(Exp::Bool(success))) => Some(success),
                                        _ => None,
                                    }
                                } else {
                                    None
                                };
                                replay_accesses.push(materialize_replay_access(
                                    false,
                                    opts.is_exclusive(),
                                    write_success,
                                    data,
                                    address,
                                    *bytes,
                                    &mut model,
                                ));
                            }
                            _ => panic!("memory_events_chronological 只返回访存事件，实际 {:?}", event),
                        }
                    }
                    // 按真实执行顺序重放 pre/post 内存（与 memory-events 同一事件序列）。
                    // pre：首触是读取读值字节，首触是写初值自由输出 null；
                    // post：最终字节内容，只读未写的字节取最后一次读值。
                    // 分量查不到模型值时输出 null 并计数（不编造）。
                    let replay = replay_memory(&replay_accesses);
                    if replay.unknown_components > 0 {
                        log!(
                            log::PATH_RESULT,
                            &format!(
                                "警告: clause{} pre/post 内存物化有 {} 个分量查不到模型值",
                                ctx.instruction_name, replay.unknown_components
                            )
                        );
                    }
                    pre_memory = memory_spans_json(&replay.pre, shared_state);
                    post_memory = memory_spans_json(&replay.post, shared_state);
                    log!(
                        log::PATH_RESULT,
                        &format!(
                            "memory_events={}\npre_memory={}\npost_memory={}",
                            serde_json::to_string_pretty(&memory_events).unwrap(),
                            serde_json::to_string_pretty(&pre_memory).unwrap(),
                            serde_json::to_string_pretty(&post_memory).unwrap()
                        )
                    );
                    log!(log::PATH_RESULT, "3. ==============================");
                }
                let single_instruction_json = AssemGenJsonItem::new(
                    ctx.target,
                    test_ins,
                    test_ins_encdec,
                    isa_state,
                    ret_val_str,
                    memory_events,
                    pre_memory,
                    post_memory,
                )
                .with_hint_label(ctx.hint_label)
                .with_slice_label(ctx.slice_label);
                collected.lock().expect("solve collector mutex poisoned").cases.push(CollectedCase {
                    path_signature: frame.path_signature(),
                    item: single_instruction_json,
                    materialization_timed_out: false,
                });
            }
            Run::Exit => {
                log!(log::PATH_RESULT, &format!("tid:{} 执行好一条路径(Exit)，fork={}", thread, frame.forks()))
            }
            Run::Dead => {}

            Run::Suspended => {
                log!(log::PATH_RESULT, &format!("tid:{} 执行好一条路径(Suspended)，fork={}", thread, frame.forks()))
            }
        },
        Err((error, frame)) => {
            match error {
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
    if should_submit_itrace {
        let frame = match &exec_result {
            Ok((_, frame)) | Err((_, frame)) => frame,
        };
        submit_itrace(frame, &mut itrace_diagnostics);
    }
}

/// 单批求解结果：已物化用例 + 可选的首个错误（错误批的已物化部分仍随
/// items 保留——与既有"错误路径也落盘"语义一致，由批调度层合并）。
struct BatchOutcome {
    items: Vec<AssemGenJsonItem>,
    summary: SolveSummary,
    diagnostics: Vec<serde_json::Value>,
    error: Option<ExecError>,
    /// P3 encdec 守卫过滤：本批被拒绝的非法编码变体路径数。
    encdec_guard_rejects: usize,
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
    timeout_reporter: &TimeoutReporter,
    case_quota: Option<CaseQuota>,
    fixed_inputs: &FixedSolveInputs<B>,
    hint_label: Option<&str>,
    slice_label: Option<&str>,
    case_limit: Option<u32>,
) -> Result<BatchOutcome, ExecError> {
    use isla_lib::smt::checkpoint;

    let state_regs = target.reg_list();

    let mut cfg = Config::new();
    cfg.set_param_value("model", "true");
    let ctx = Context::new(cfg);
    let mut solver = Solver::new(&ctx);
    let mut symbolic_regs = regs.clone();

    // W2 数组内存模型装配：同址读写一致。数组常量必须在下方生成 checkpoint
    // 之前声明，使所有执行路径共享初始数组定义；每个 clause 的内存克隆通过
    // Clone 快照保留回调，各路径独立持有数组状态。
    // ISLA_RISCV_MEMORY_MODEL=array（默认）启用，fresh 退回旧的独立变量行为。
    // W9 语义：默认全符号化——符号读写地址全域自由、内容来自字节数组，
    // 可访问性/trap 交给模型自身 PMA/PMP，成功与 fault 路径并存；
    // [[memory_regions]] 的 excluded（判死）区域把"落到这段就 Unsat"的语义
    // 下推到内存层（符号地址 NOT 链 + W7 立即判死，具体地址直接 Err）。
    // 零配置（未声明 [[memory_regions]]）语义：地址与数组内容全部符号化，
    // 不再依赖默认区域救活（W6 修复了写侧空 OR 链折叠成 false 的 bug）；
    // ISLA_RISCV_DEFAULT_SYM_RAM=1 可显式要求补默认符号 RAM（对齐
    // riscv64_difftest_mem.toml 的 sym_ram，供 difftest 重放兜底）。
    let initial_memory = if memory_model::array_model_enabled() {
        initial_memory.map(|mut memory| {
            // Sail 的 Mem_read_request/Mem_write_request 地址固定为 bits(64)。
            // RV32 的物理地址先从 34 位零扩到 64 位，不能用 XLEN 声明数组索引。
            memory = memory_builder::ensure_solve_state_memory(memory, memory_builder::default_sym_ram_enabled());
            memory_model::install_seq_memory(&mut memory, 64, &mut solver);
            memory
        })
    } else {
        initial_memory
    };

    // pre-state 主动符号化：遍历 target 提供的寄存器、按类型符号化并覆盖，返回 PreStateCtx 供求解后取 pre-state。
    target.setup_pre_state(&mut symbolic_regs, lets, shared_state, &mut solver, &fixed_inputs.prestate)?;

    // W21：[symbolic_registers] 声明的 CSR 在这里注入——必须在 setup_pre_state
    // 之后（覆盖 reg_list 全量符号化产生的"整寄存器一个符号"，换成带位约束的
    // 声明并同步 pre_state 记录）、checkpoint 之前（所有路径共享同一组符号
    // 声明与位约束断言）。CLI --prestate 与符号化声明同名是配置矛盾
    // （isarch_main 已给出用户友好报错，此处是防御兜底）。
    if !target.symbolic_csrs().is_empty() {
        for csr in target.symbolic_csrs() {
            let Some(name) = shared_state.symtab.get(&zencode::encode(&csr.name)) else {
                panic!("防御性编程：符号化 CSR {} 不在当前 IR symtab", csr.name);
            };
            if fixed_inputs.prestate.contains_key(&name) {
                panic!("防御性编程：--prestate {} 与 [symbolic_registers] 同名冲突", csr.name);
            }
        }
        target.apply_symbolic_csrs_to_registers(&mut symbolic_regs, shared_state, &mut solver)?;
    }

    // S2（W17）：[[pma_regions]] 含符号边界时的执行期注入（镜像符号 PMP 的
    // 装配时机）。符号 zsizze 必须声明在本次求解的 solver 里，且必须在下方
    // checkpoint 之前完成——所有路径共享同一组符号声明与取值域约束，
    // zpmaCheck/zmatching_pma 的符号比较在各路径上独立分叉。
    if !target.symbolic_pma_regions().is_empty() {
        let records = super::target::apply_symbolic_pma_regions_to_registers(
            target.symbolic_pma_regions(),
            &shared_state.symtab,
            &shared_state.type_info,
            &mut symbolic_regs,
            shared_state,
            &mut solver,
        )
        .map_err(|error| ExecError::Type(error, SourceLoc::command_line()))?;
        target.symbolic_pma_sizes_mut().extend(records);
    }

    //不要删掉这个注释！！！留着以后改pmp的时候用
    /* if target.pmp_symbolic() {
        target.apply_symbolic_pmp_to_registers(&shared_state.symtab, &mut symbolic_regs, shared_state, &mut solver)?;
    } */

    let instruction = if let Some(fixed) = fixed_inputs.instruction {
        decode_fixed_instruction(
            fixed,
            instruction_name,
            shared_state,
            // 译码环境用初始具体表 + 钉值（见 decode_register_bindings 的根因说明），
            // 不传主求解的 symbolic_regs——其中的符号声明只存在于主 solver。
            &decode_register_bindings(regs, &fixed_inputs.prestate, shared_state),
            lets,
        )
        .map_err(|error| ExecError::Type(error, SourceLoc::command_line()))?
    } else {
        let ctor_name = shared_state.symtab.lookup(instruction_name);
        Val::<B>::Ctor(
            ctor_name,
            Box::new(symbolic_args_from_types(instruction_name, shared_state, &symbolic_regs, lets, &mut solver)?),
        )
    };
    let fun_args = vec![instruction];
    log!(log::SYM_EXEC, &format!("fun_args:{:?}", fun_args));
    log!(log::ARCH_INFO, &format!("{:?}", state_regs));

    // 生成参数（暂时使用默认值，测试checkpoint机制）

    // 构造指令值

    // 创建checkpoint，包含符号化变量
    let cp = checkpoint(&mut solver);

    // 使用checkpoint执行函数，支持错误传播
    let result: Arc<Mutex<SolveCollectorState>> =
        Arc::new(Mutex::new(SolveCollectorState::with_case_quota(case_quota)));

    let task_state = TaskState::new().with_execution_limits(execution_limits.clone());

    // ExecuteAs 续执行任务队列：collector 阶段入队，每轮执行后排空再跑下一轮。
    // 首轮执行 clause 本体（如 C_LD 解码），其后每轮执行一轮 ExecuteAs 续执行
    // 任务（如转换出的 LOAD/STORE），直到队列不再增长（模型里 ExecuteAs 不链式
    // 嵌套，正常一轮即收敛）。
    let continuations: Mutex<Vec<ExecuteAsContinuation<B>>> = Mutex::new(Vec::new());
    // 续执行轮次重建调用帧用的初始内存（首轮传 clone，此份留给轮次循环）。
    let round_memory = initial_memory.clone();

    // solve-state 路径收集环境：首段闭包与续执行轮次的转发闭包共用。
    let solve_ctx = SolvePathCtx {
        target: &*target,
        instruction_name,
        fun_args: &fun_args,
        regs,
        lets,
        timeout_reporter: &timeout_reporter,
        task_state: &task_state,
        continuations: &continuations,
        hint_label,
        slice_label,
    };

    //isla_lib::executor::execute_ir_function_with_checkpoint_and_limits(
    isla_lib::executor::execute_ir_function_with_checkpoint_multi_thread(
        "zexecute",
        &fun_args,
        shared_state,
        &symbolic_regs,
        lets,
        &result,
        &|thread, task_id, exec_result, shared_state, solver, collected| {
            solve_collect_path(&solve_ctx, thread, task_id, exec_result, shared_state, solver, collected)
        },
        cp,
        initial_memory.clone(),
        num_threads,
        timeout,
        &task_state,
    );

    // ExecuteAs 续执行轮次：排空 collector 入队的续执行任务，多线程并行执行；
    // 续执行路径里再次出现 ExecuteAs 时由下一轮继续处理。
    loop {
        let next_continuations: Vec<ExecuteAsContinuation<B>> =
            std::mem::take(&mut *continuations.lock().expect("ExecuteAs 续执行队列 mutex poisoned"));
        if next_continuations.is_empty() {
            break;
        }
        log!(
            log::SYM_EXEC,
            &format!("{} 第 {} 个 ExecuteAs 续执行任务开始执行", instruction_name, next_continuations.len())
        );
        let execute_fn_id = shared_state.symtab.lookup("zexecute");
        let (func_args, ret_ty, instrs) = shared_state.functions.get(&execute_fn_id).unwrap();
        let mut next_tasks = Vec::with_capacity(next_continuations.len());
        for continuation in next_continuations {
            // 用初始符号寄存器/初始内存重建 zexecute 调用帧（ExecuteAs 返回前无副作用，
            // 等价于外层重新执行解码出的指令），checkpoint 携带前段全部 SMT 状态。
            let mut frame =
                LocalFrame::new(execute_fn_id, func_args, ret_ty, Some(&[continuation.instruction]), instrs);
            frame.add_regs(&symbolic_regs);
            frame.add_lets(lets);
            if let Some(memory) = round_memory.clone() {
                frame.set_memory(memory);
            }
            next_tasks.push(frame.task_with_checkpoint(TaskId::fresh(), &task_state, continuation.checkpoint));
        }
        isla_lib::executor::start_multi(
            num_threads,
            timeout,
            next_tasks,
            shared_state,
            result.clone(),
            &|thread, task_id, exec_result, shared_state, solver, collected| {
                solve_collect_path(&solve_ctx, thread, task_id, exec_result, shared_state, solver, collected)
            },
        );
    }

    // 提取字符串结果
    let result_mutex = match Arc::try_unwrap(result) {
        Ok(result_mutex) => result_mutex,
        Err(_) => panic!("{} 执行结束后 result 收集器仍有共享引用", instruction_name),
    };
    let mut state = result_mutex.into_inner().expect("solve collector mutex poisoned");
    let quota = state.case_quota;
    if state.model_query_timeouts > 0 {
        log!(
            log::SYM_EXEC,
            &format!(
                "{} 有 {} 条完成路径的终值查询超过时间盒，已写入不完整诊断，不进入gen",
                instruction_name, state.model_query_timeouts
            )
        );
    }
    let mut diagnostics: Vec<serde_json::Value> = state
        .cases
        .iter()
        .filter(|case| case.materialization_timed_out)
        .map(|case| {
            serde_json::json!({"status":"incomplete", "reason":"final-model-query-timeout",
            "path-signature":case.path_signature, "symbolic-return-value":case.item.ret_val})
        })
        .collect();
    diagnostics.sort_by_cached_key(|diagnostic| serde_json::to_string(diagnostic).unwrap());
    let collected_count = state.cases.iter().filter(|case| !case.materialization_timed_out).count();
    let mut items = finalize_cases(state.cases, &quota);
    // P2 分片预算：case_limit 是每片产出条数硬上限（在确定性归并之后截断，
    // 保证截断结果与配额取样后的排序一致）
    if let Some(limit) = case_limit {
        items.truncate(limit as usize);
    }
    if state.encdec_guard_rejects > 0 {
        log!(
            log::SYM_EXEC,
            &format!(
                "{} encdec 守卫过滤拒绝 {} 条非法编码变体（execute 域越过 encdec 守卫，ISLA_RISCV_ALLOW_RESERVED_ENCODINGS=1 可保留）",
                instruction_name, state.encdec_guard_rejects
            )
        );
    }
    state.summary.omitted_cases = collected_count - items.len();
    state.summary.model_query_timeouts = state.model_query_timeouts;
    state.summary.encoding_filtered_paths = state.encdec_guard_rejects;
    Ok(BatchOutcome {
        items,
        summary: state.summary,
        diagnostics,
        error: state.first_error,
        encdec_guard_rejects: state.encdec_guard_rejects,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::bitvector::b129::B129;
    use isla_lib::bitvector::b64::B64;
    use isla_lib::config::{LimitBehaviorConfig, RegionForkLimitConfig};
    use isla_lib::executor::{LimitBehavior, SampleBias};
    use isla_lib::smt::{ReadOpts, WriteOpts};
    use isla_lib::source_loc::SourceRegionSpec;
    use isla_lib::timeout::{SmtDumpNames, SmtDumpSource, SmtOperation, SmtTimeout, TimeoutSmtDump};
    use std::time::Duration;

    #[test]
    fn fixed_instruction_bits保留压缩和普通编码宽度() {
        assert_eq!(parse_fixed_instruction_bits("0x6008").unwrap(), FixedInstruction { bits: 0x6008, width: 16 });
        assert_eq!(
            parse_fixed_instruction_bits("0x0000b183").unwrap(),
            FixedInstruction { bits: 0x0000b183, width: 32 }
        );
        assert!(parse_fixed_instruction_bits("0x6").is_err());
        assert!(parse_fixed_instruction_bits("0x00006008").is_err());
        assert!(parse_fixed_instruction_bits("6008").is_err());
    }

    /// 译码守卫读寄存器的最小 IR 函数：`return = (mstatus != 0x600)`。
    /// 模拟真实 rv64d IR 中 zencdec_backwards 向量分支经 zcurrentlyEnabled
    /// 读取 zmstatus 的形态（Exp::Id 直接引用寄存器名 + neq primop）。
    /// 返回（shared_state，mstatus 寄存器名），并把函数注册进 shared_state。
    fn decode_probe_shared_state() -> (SharedState<'static, B64>, Name) {
        use isla_lib::ir::Exp as IrExp;
        let mut symtab = Symtab::new();
        let mstatus_text: &'static str = Box::leak(zencode::encode("mstatus").into_boxed_str());
        // 函数名用 IR 原文（z 前缀形式），symtab.lookup 按原文匹配
        let probe_text: &'static str = "zdecode_probe";
        let mstatus_name = symtab.intern(mstatus_text);
        let probe_name = symtab.intern(probe_text);
        let mut shared_state: SharedState<B64> = SharedState::empty(symtab);
        shared_state.registers.insert(mstatus_name, Ty::Bits(64));
        let result_text: &'static str = Box::leak(zencode::encode("zz_result").into_boxed_str());
        let result = shared_state.symtab.intern(result_text);
        let instrs: &'static [Instr<Name, B64>] = Box::leak(
            vec![
                Instr::Decl(result, Ty::Bool, SourceLoc::unknown()),
                Instr::Copy(
                    Loc::Id(result),
                    IrExp::Call(Op::Neq, vec![IrExp::Id(mstatus_name), IrExp::Bits(B64::new(0x600, 64))]),
                    SourceLoc::unknown(),
                ),
                Instr::Copy(Loc::Id(RETURN), IrExp::Id(result), SourceLoc::unknown()),
                Instr::End,
            ]
            .into_boxed_slice(),
        );
        let ret_ty: &'static Ty<Name> = Box::leak(Box::new(Ty::Bool));
        shared_state.functions.insert(probe_name, (Vec::new(), ret_ty, instrs));
        (shared_state, mstatus_name)
    }

    /// 根因回归（G6/E/P1 三次撞到的 smt.rs:2168 "Could not get Z3 func_decl"
    /// 启动期 panic）：concrete_function_result 在独立 solver 中执行译码函数，
    /// 寄存器表若携带主 solver 声明的符号值（setup_pre_state 之后的
    /// symbolic_regs），译码守卫的 neq 把该符号送进从未声明它的 solver，
    /// translate_exp 直接 panic。这是不变量违反，必须硬失败而非静默绕过；
    /// 调用侧（decode_fixed_instruction）必须传 decode_register_bindings
    /// 产出的全具体环境。
    #[test]
    #[should_panic(expected = "Could not get Z3 func_decl")]
    fn concrete_function_result外部solver符号寄存器硬失败() {
        let (shared_state, mstatus_name) = decode_probe_shared_state();
        let context = Context::new(Config::new());
        let mut main_solver = Solver::<B64>::new(&context);
        // 模拟 setup_pre_state：在主 solver 里符号化 mstatus
        let symbolic_mstatus = symbolic(&Ty::Bits(64), &shared_state, &mut main_solver, SourceLoc::unknown()).unwrap();
        let mut symbolic_regs = RegisterBindings::new();
        let ty = Ty::<Name>::Bits(64);
        symbolic_regs.insert(mstatus_name, false, UVal::Init(symbolic_mstatus));

        // 在 fresh solver（concrete_function_result 内部自建）里执行：符号未声明 → panic
        let outcome =
            concrete_function_result("zdecode_probe", Val::Unit, &shared_state, &symbolic_regs, &Bindings::default());
        panic!("防御性编程：外部 solver 符号应在上游 panic，不应返回 {:?}", outcome);
    }

    /// 具体寄存器环境下译码函数正常返回具体值——decode_register_bindings 的
    /// 语义约束：初始具体值 + --prestate 钉值即可安全跨 solver 复用。
    #[test]
    fn concrete_function_result具体寄存器环境成功() {
        let (shared_state, mstatus_name) = decode_probe_shared_state();
        let mut regs = RegisterBindings::new();
        let ty = Ty::<Name>::Bits(64);
        regs.insert(mstatus_name, false, UVal::Init(Val::Bits(B64::new(0x600, 64))));
        let outcome =
            concrete_function_result("zdecode_probe", Val::Unit, &shared_state, &regs, &Bindings::default()).unwrap();
        assert_eq!(outcome, Val::Bool(false), "0x600 != 0x600 为假");
    }

    /// --instruction-bits 的译码环境构造：初始寄存器表 + --prestate 钉值覆盖。
    /// 未钉值寄存器保留初始具体值（不被主求解的符号化污染），钉值寄存器按
    /// CLI/分片注入的具体值覆盖。
    #[test]
    fn decode_register_bindings初始值加钉值() {
        let (mut shared_state, mstatus_name) = decode_probe_shared_state();
        let x6_text = zencode::encode("x6");
        let x6_name = shared_state.symtab.intern(&x6_text);
        let mut regs = RegisterBindings::new();
        let ty = Ty::<Name>::Bits(64);
        regs.insert(mstatus_name, false, UVal::Init(Val::Bits(B64::new(0x600, 64))));
        regs.insert(x6_name, false, UVal::Uninit(&ty));

        let pinned = Val::Bits(B64::new(0x8000_1000, 64));
        let prestate = HashMap::from([(x6_name, pinned.clone())]);
        let decode_regs = decode_register_bindings(&regs, &prestate, &shared_state);
        assert_eq!(decode_regs.get_last_if_initialized(x6_name), Some(&pinned), "钉值寄存器被覆盖");
        assert_eq!(
            decode_regs.get_last_if_initialized(mstatus_name),
            Some(&Val::Bits(B64::new(0x600, 64))),
            "未钉值寄存器保留初始具体值"
        );
        // 原表不被修改（批间复用同一初始表）
        assert_eq!(regs.get_last_if_initialized(x6_name), None, "原表保持 Uninit");
    }

    /// 构造一个内联的 `ExecutionLimitsConfig`，用来测 `solve_execution_limits` 这个函数本身的
    /// 行为（region 解析、文件名匹配、偏置/预算传递）。不读任何真实配置文件 / IR / Sail 源码，
    /// 避免测试随 workaround TOML 漂移。
    fn inline_config(max_forks_per_branch: u32, region_limits: Vec<RegionForkLimitConfig>) -> ExecutionLimitsConfig {
        ExecutionLimitsConfig {
            max_forks_per_branch: Some(max_forks_per_branch),
            on_limit_reached: Some(LimitBehaviorConfig::Concretize),
            region_fork_limits: Some(region_limits),
            ..ExecutionLimitsConfig::default()
        }
    }

    fn vext_arith_region(start: (u32, u16), end: (u32, u16)) -> SourceRegionSpec {
        SourceRegionSpec::new("extensions/V/vext_arith_insts.sail", start, end)
    }

    /// 含 vext_arith / vext_utils / vext_control 三个文件的 symtab，方便测试里构造 SourceLoc。
    fn vext_symtab() -> Symtab<'static> {
        let mut symtab = Symtab::new();
        symtab.set_files(vec![
            "extensions/V/vext_arith_insts.sail",
            "extensions/V/vext_utils_insts.sail",
            "extensions/V/vext_control.sail",
        ]);
        symtab
    }

    struct NamesDump;

    impl SmtDumpSource for NamesDump {
        fn materialize(&self) -> Result<String, String> {
            panic!("timeout dump test must materialize with configured names")
        }

        fn materialize_with_names(&self, names: &SmtDumpNames) -> Result<String, String> {
            Ok(format!("{:?}", names))
        }
    }

    #[test]
    fn error_diagnostic_records_timeout_with_frame_names() {
        let argument_text = zencode::encode("test_argument");
        let function_text = zencode::encode("test_function");
        let mut symtab = Symtab::new();
        let argument = symtab.intern(&argument_text);
        let function_name = symtab.intern(&function_text);
        let shared_state: SharedState<B64> = SharedState::empty(symtab);
        let instrs: Vec<Instr<Name, B64>> = Vec::new();
        let mut frame = LocalFrame::new(function_name, &[], &Ty::Unit, None, &instrs);
        frame.vars_mut().insert(argument, UVal::Init(Val::Symbolic(Sym::from_u32(17))));
        let timeout = Arc::new(SmtTimeout {
            source_loc: SourceLoc::unknown(),
            operation: SmtOperation::CheckSat,
            limit: Duration::from_secs(1),
            operation_wall: Duration::from_secs(1),
            dump: Arc::new(TimeoutSmtDump::new(Arc::new(NamesDump))),
        });
        let error = ExecError::Smt(SmtError::Timeout(timeout.clone()));
        let collected = Mutex::new(SolveCollectorState::new());
        let reporter = TimeoutReporter::new(TimeoutReportConfig {
            output: TimeoutSmtOutput::new(false, false, true),
            directory: PathBuf::new(),
        });

        let recorder = ErrorRecorder { collected: &collected, reporter: &reporter, clause: "zTEST" };
        let diagnostics = recorder.record_error_diagnostic(&error, &frame, &shared_state);

        let state = collected.into_inner().unwrap();
        let Some(ExecError::Smt(SmtError::Timeout(recorded))) = state.first_error else {
            panic!("SMT timeout was not recorded")
        };
        assert!(Arc::ptr_eq(&recorded, &timeout));
        assert_eq!(diagnostics.len(), 1);
        assert!(timeout.dump.materialize().unwrap().contains("isla_test_argument__s17"));
    }

    #[test]
    fn collect_symbolic_vars_sorts_struct_fields_by_name() {
        let mut fields: ahash::HashMap<Name, Val<B64>> =
            ahash::HashMap::with_hasher(ahash::RandomState::with_seeds(0, 0, 0, 0));
        fields.insert(Name::from_u32(3), Val::Symbolic(Sym::from_u32(30)));
        fields.insert(Name::from_u32(1), Val::Symbolic(Sym::from_u32(10)));
        fields.insert(Name::from_u32(2), Val::Symbolic(Sym::from_u32(20)));
        let value = Val::Struct(fields);
        let mut symbols = Vec::new();

        collect_symbolic_vars(&value, &mut symbols);

        assert_eq!(
            symbols,
            vec![Sym::from_u32(10), Sym::from_u32(20), Sym::from_u32(30)],
            "结构体字段的哈希表迭代顺序不得影响有限域候选的序号"
        );
    }

    #[test]
    fn diversify_unconstrained_finite_domains_diversifies_bool_and_bitvectors() {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let boolean = solver.declare_const(isla_lib::smt::smtlib::Ty::Bool, SourceLoc::unknown());
        let bits = solver.declare_const(isla_lib::smt::smtlib::Ty::BitVec(5), SourceLoc::unknown());
        let args = [Val::Symbolic(boolean), Val::Symbolic(bits)];
        let shared_state = SharedState::empty(Symtab::new());
        let signature = 0x5a31_7c9d_f024_6be8;

        diversify_unconstrained_finite_domains(&args, signature, &shared_state, &mut solver)
            .expect("有限域候选必须能钉住未约束的布尔值和位向量");

        assert_eq!(solver.check_sat(SourceLoc::unknown()), isla_lib::smt::SmtResult::Sat);
        let mut model = Model::new(&solver);
        assert_eq!(
            model.get_var(boolean).unwrap().unwrap_exp(),
            isla_lib::smt::smtlib::Exp::Bool(splitmix64(signature) & 1 == 1)
        );
        assert_eq!(model.get_var(bits).unwrap().unwrap_exp(), bitvector_candidate(signature ^ 1, 5));
    }

    #[test]
    fn diversify_unconstrained_finite_domains_diversifies_wide_bitvectors() {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B129>::new(&context);
        let bits = solver.declare_const(isla_lib::smt::smtlib::Ty::BitVec(65), SourceLoc::unknown());
        let args = [Val::Symbolic(bits)];
        let shared_state = SharedState::empty(Symtab::new());
        let signature = 0xf126_dab7_0c49_5e83;

        diversify_unconstrained_finite_domains(&args, signature, &shared_state, &mut solver)
            .expect("有限域候选必须支持超过 B64 的位向量");

        assert_eq!(solver.check_sat(SourceLoc::unknown()), isla_lib::smt::SmtResult::Sat);
        let mut model = Model::new(&solver);
        let candidate = bitvector_candidate(signature, 65);
        assert_eq!(model.get_var(bits).unwrap().unwrap_exp(), candidate);

        let isla_lib::smt::smtlib::Exp::Bits(candidate_bits) = candidate else {
            panic!("65 位候选必须使用 Exp::Bits 表示")
        };
        let mut expected = B129::zeros(65);
        for (index, bit) in candidate_bits.into_iter().enumerate() {
            if bit {
                expected = expected.set_slice(index as u32, B129::BIT_ONE);
            }
        }
        assert_eq!(
            model.get_val(&args[0]).expect("可由 B129 表示的宽位候选必须能物化为 Val::Bits"),
            Val::Bits(expected)
        );
    }

    #[test]
    fn diversify_unconstrained_finite_domains_skips_non_target_smt_types() {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let floating = solver.declare_const(isla_lib::smt::smtlib::Ty::Float(8, 24), SourceLoc::unknown());
        let rounding = solver.declare_const(isla_lib::smt::smtlib::Ty::RoundingMode, SourceLoc::unknown());
        let args = [Val::Symbolic(floating), Val::Symbolic(rounding)];
        let shared_state = SharedState::empty(Symtab::new());

        diversify_unconstrained_finite_domains(&args, 0, &shared_state, &mut solver)
            .expect("Float 和 RoundingMode 不属于目标有限域，必须按声明类型跳过");

        assert_eq!(solver.check_sat(SourceLoc::unknown()), isla_lib::smt::SmtResult::Sat);
    }

    #[test]
    fn diversify_unconstrained_finite_domains_preserves_constrained_fields() {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let bits = solver.declare_const(isla_lib::smt::smtlib::Ty::BitVec(4), SourceLoc::unknown());
        let constrained_value = B64::new(3, 4);
        solver.assert_eq(isla_lib::smt::smtlib::Exp::Var(bits), isla_lib::smt::smtlib::Exp::Bits64(constrained_value));
        let args = [Val::Symbolic(bits)];
        let shared_state = SharedState::empty(Symtab::new());
        let signature = (0..u64::MAX)
            .find(|signature| B64::new(splitmix64(*signature) & 0xf, 4) != constrained_value)
            .expect("必须存在不等于已约束值的候选");

        diversify_unconstrained_finite_domains(&args, signature, &shared_state, &mut solver)
            .expect("候选不可满足时必须保留已有约束");

        assert_eq!(solver.check_sat(SourceLoc::unknown()), isla_lib::smt::SmtResult::Sat);
        let mut model = Model::new(&solver);
        assert_eq!(model.get_var(bits).unwrap().unwrap_exp(), isla_lib::smt::smtlib::Exp::Bits64(constrained_value));
    }

    #[test]
    fn diversify_unconstrained_finite_domains_propagates_model_errors() {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let shared_state = SharedState::empty(Symtab::new());
        let args = [Val::Symbolic(Sym::from_u32(999))];

        let error = diversify_unconstrained_finite_domains(&args, 0, &shared_state, &mut solver)
            .expect_err("读取枚举模型失败必须向调用方传播");

        assert!(matches!(error, ExecError::Type(_, _)));
    }

    #[test]
    fn solve_execution_limits_passes_through_inline_region_limits() {
        let symtab = vext_symtab();
        let config = inline_config(
            1,
            vec![
                RegionForkLimitConfig {
                    max_forks_per_region: 0,
                    sample_bias: None,
                    region: vext_arith_region((65, 36), (65, 57)),
                },
                RegionForkLimitConfig {
                    max_forks_per_region: 0,
                    sample_bias: Some((16, true)),
                    region: vext_arith_region((181, 6), (187, 7)),
                },
            ],
        );
        let limits = solve_execution_limits(&symtab, Some(&config));

        assert_eq!(limits.max_forks_per_branch, Some(1));
        assert_eq!(limits.on_limit_reached, LimitBehavior::Concretize);
        // 不配 `regions`：per-scope 预算必须全局生效，否则选不中没有 Sail 源码位置的分支点。
        assert_eq!(limits.regions, None);
        assert!(limits.branch_region_limits.is_empty());
        assert_eq!(limits.region_fork_limits.len(), 2);
        // 解析出的 region 坐标 + 偏置都按配置原样传递。
        let biased = limits
            .region_fork_limits
            .iter()
            .find(|limit| limit.sample_bias.is_some())
            .expect("应该有一条带偏置的 region");
        assert_eq!(biased.sample_bias, Some(SampleBias { denominator: 16, direction: true }));
        assert!(biased.region.selects_ir_location(SourceLoc::new(0, 181, 6, 187, 7)));
    }

    /// `regions` 过滤器不开启时，没有 Sail 源码位置（`SourceLoc::unknown`）的分支点也必须
    /// 受 per-scope 预算约束——这是 `bool_bit_forwards` 那类 IR 内部编号 jump 能被压住的前提。
    #[test]
    fn solve_execution_limits_keeps_branch_budget_when_regions_filter_is_absent() {
        let symtab = vext_symtab();
        let config = inline_config(1, Vec::new());
        let limits = solve_execution_limits(&symtab, Some(&config));

        assert_eq!(limits.max_forks_per_branch, Some(1));
        assert!(limits.regions.is_none());
        // 不应该因为某条 region 配置选不中 unknown 位置就 panic。
        assert!(limits.region_fork_limits.iter().all(|limit| !limit.region.selects_ir_location(SourceLoc::unknown())));
    }

    /// `region_fork_limits` 解析时按文件名匹配到运行时 file 编号；坐标在配置给的范围内才命中。
    /// 这条测试用一个内联配置覆盖"命中、不命中、文件不存在"三种情况。
    #[test]
    fn solve_execution_limits_region_fork_limits_match_by_source_location() {
        let symtab = vext_symtab();
        let config = inline_config(
            1,
            vec![
                RegionForkLimitConfig {
                    max_forks_per_region: 0,
                    sample_bias: None,
                    region: vext_arith_region((181, 6), (187, 7)),
                },
                RegionForkLimitConfig {
                    max_forks_per_region: 0,
                    sample_bias: None,
                    // 故意写一个 symtab 里没有的文件，解析时应该整体落空、不 panic。
                    region: SourceRegionSpec::new("not/a/real/file.sail", (1, 1), (2, 2)),
                },
            ],
        );
        let limits = solve_execution_limits(&symtab, Some(&config));
        let budgeted =
            |location| limits.region_fork_limits.iter().any(|limit| limit.region.selects_ir_location(location));

        // 文件名能匹配、坐标在区间内 => 命中。
        assert!(budgeted(SourceLoc::new(0, 181, 6, 187, 7)));
        assert!(budgeted(SourceLoc::new(0, 185, 10, 186, 20)));
        // 坐标在区间外 => 不命中。
        assert!(!budgeted(SourceLoc::new(0, 180, 1, 180, 5)));
        assert!(!budgeted(SourceLoc::new(0, 188, 1, 188, 5)));
        // 别的文件 => 不命中。
        assert!(!budgeted(SourceLoc::new(1, 181, 6, 187, 7)));
        // 配置里那条不存在的文件应该被滤掉，不进 region_fork_limits。
        assert_eq!(limits.region_fork_limits.len(), 1);
    }

    #[test]
    fn solve_execution_limits_uses_only_the_supplied_toml_config() {
        let mut symtab = Symtab::new();
        symtab.set_files(vec![
            "extensions/V/vext_arith_insts.sail",
            "extensions/V/vext_utils_insts.sail",
            "extensions/V/vext_control.sail",
        ]);
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
        assert!(limits.regions.is_none());
        assert!(limits.branch_region_limits.is_empty());
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
    fn solve_execution_limits_without_toml_is_inactive() {
        let limits = solve_execution_limits(&Symtab::new(), None);

        assert_eq!(limits.max_forks_per_branch, None);
        assert_eq!(limits.max_forks_per_path, None);
        assert_eq!(limits.max_backjumps_per_loop, None);
        assert_eq!(limits.max_path_depth, None);
        assert_eq!(limits.regions, None);
        assert!(limits.branch_region_limits.is_empty());
    }

    /// region 预算配置里的文件名在 symtab 中找不到时，那条 region 整体落空、不 panic；
    /// per-scope 预算不受影响。
    #[test]
    fn solve_execution_limits_drops_region_limits_whose_file_is_unknown() {
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["core/types.sail"]);
        let config = inline_config(
            7,
            vec![RegionForkLimitConfig {
                max_forks_per_region: 0,
                sample_bias: None,
                region: SourceRegionSpec::new("extensions/V/vext_arith_insts.sail", (181, 6), (187, 7)),
            }],
        );
        let limits = solve_execution_limits(&symtab, Some(&config));

        // per-scope 预算照常生效。
        assert_eq!(limits.max_forks_per_branch, Some(7));
        // region 预算因文件名解析不到而落空。
        assert!(limits.region_fork_limits.is_empty());
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

    // ===== W3：memory-events 执行顺序、pre/post 内存物化、ExecuteAs 识别 =====

    fn read_mem_event(address: u64, bytes: u32, value: u64) -> Event<B64> {
        Event::ReadMem {
            value: Val::Bits(B64::new(value, 8 * bytes)),
            read_kind: Val::Unit,
            address: Val::Bits(B64::new(address, 64)),
            bytes,
            tag_value: None,
            opts: ReadOpts::default(),
            region: "default",
        }
    }

    fn write_mem_event(address: u64, bytes: u32, data: u64) -> Event<B64> {
        Event::WriteMem {
            value: Sym::from_u32(4242),
            write_kind: Val::Unit,
            address: Val::Bits(B64::new(address, 64)),
            data: Val::Bits(B64::new(data, 8 * bytes)),
            bytes,
            tag_value: None,
            opts: WriteOpts::default(),
            region: "default",
        }
    }

    /// 轨迹是逆时间序（smt.rs Trace::to_vec 先最新段、段内反向），
    /// 收集层必须整体反转恢复真实执行顺序；本用例跨两个轨迹段（中间夹 checkpoint）。
    #[test]
    fn memory_events_chronological_跨段恢复执行顺序() {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        solver.add_event(read_mem_event(0x100, 4, 0xAABBCCDD));
        // 模拟一次 fork 产生的 checkpoint：当前 head 段化进 tail，轨迹跨两段
        let _ = isla_lib::smt::checkpoint(&mut solver);
        solver.add_event(write_mem_event(0x200, 4, 0x11223344));

        let events = memory_events_chronological(solver.trace());

        assert_eq!(events.len(), 2, "只应返回访存事件");
        assert!(matches!(events[0], Event::ReadMem { .. }), "先发生的读应排在最前");
        assert!(matches!(events[1], Event::WriteMem { .. }), "后发生的写应排在最后");
    }

    #[test]
    fn memory_events_chronological_段内恢复执行顺序() {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        solver.add_event(read_mem_event(0x100, 4, 0xAABBCCDD));
        solver.add_event(write_mem_event(0x100, 4, 0x11223344));

        let events = memory_events_chronological(solver.trace());

        assert_eq!(events.len(), 2);
        assert!(matches!(events[0], Event::ReadMem { .. }), "同一 head 段内也要按发生顺序");
        assert!(matches!(events[1], Event::WriteMem { .. }));
    }

    #[test]
    fn 真实memory回调事件可物化普通假返回写的前后态() {
        use isla_lib::memory::Memory;
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut memory = Memory::<B64>::new();
        memory_model::install_seq_memory(&mut memory, 64, &mut solver);
        let address = Val::Bits(B64::new(0x8000_1000, 64));
        let before =
            memory.read(Val::Unit, address.clone(), Val::I128(1), &mut solver, false, ReadOpts::default()).unwrap();
        let Val::Symbolic(before_sym) = before else { panic!("初始读应为符号值") };
        solver.assert_eq(Exp::Var(before_sym), Exp::Bits64(B64::new(0x11, 8)));
        let write = memory
            .write(Val::Unit, address.clone(), Val::Bits(B64::new(0xA5, 8)), &mut solver, None, WriteOpts::default())
            .unwrap();
        let Val::Symbolic(write_sym) = write else { panic!("写结果应为符号Bool") };
        solver.add(isla_lib::smt::smtlib::Def::Assert(Exp::Not(Box::new(Exp::Var(write_sym)))));
        let after = memory.read(Val::Unit, address, Val::I128(1), &mut solver, false, ReadOpts::default()).unwrap();
        let Val::Symbolic(after_sym) = after else { panic!("写后读应为符号值") };
        assert_eq!(solver.check_sat(SourceLoc::unknown()), isla_lib::smt::SmtResult::Sat);
        assert_eq!(
            solver.check_sat_with(
                &Exp::Neq(Box::new(Exp::Var(after_sym)), Box::new(Exp::Bits64(B64::new(0xA5, 8)))),
                SourceLoc::unknown(),
            ),
            isla_lib::smt::SmtResult::Unsat,
        );

        assert_eq!(solver.check_sat(SourceLoc::unknown()), isla_lib::smt::SmtResult::Sat);
        let trace = memory_events_chronological(solver.trace());
        assert_eq!(trace.len(), 3);
        assert!(matches!(trace[0], Event::ReadMem { .. }));
        assert!(matches!(trace[1], Event::WriteMem { .. }));
        assert!(matches!(trace[2], Event::ReadMem { .. }));
        let mut model = Model::new(&solver);
        let accesses: Vec<_> = trace
            .into_iter()
            .map(|event| match event {
                Event::ReadMem { value, address, bytes, .. } => {
                    materialize_replay_access(true, false, None, value, address, *bytes, &mut model)
                }
                Event::WriteMem { address, data, bytes, opts, .. } => {
                    materialize_replay_access(false, opts.is_exclusive(), None, data, address, *bytes, &mut model)
                }
                other => panic!("非访存事件: {:?}", other),
            })
            .collect();
        let replay = replay_memory(&accesses);
        assert_eq!(replay.pre, BTreeMap::from([(0x8000_1000, Some(0x11))]));
        assert_eq!(replay.post, BTreeMap::from([(0x8000_1000, Some(0xA5))]));
        assert_eq!(replay.unknown_components, 0);
        let shared_state: SharedState<B64> = SharedState::empty(Symtab::new());
        let spans = memory_spans_json(&replay.post, &shared_state);
        assert_eq!(spans.len(), 1);
        assert_eq!(spans[0].value.as_deref(), Some("8'ha5"));
    }

    fn replay_access(is_read: bool, address: Option<u64>, bytes: u32, payload: Option<Vec<u8>>) -> ReplayAccess {
        ReplayAccess { is_read, is_exclusive: false, write_success: None, address, bytes, payload }
    }

    #[test]
    fn replay_memory_先读后写() {
        let replay = replay_memory(&[
            replay_access(true, Some(0x100), 4, Some(vec![0xDD, 0xCC, 0xBB, 0xAA])),
            replay_access(false, Some(0x100), 4, Some(vec![0x44, 0x33, 0x22, 0x11])),
        ]);

        // 首触是读：pre 取读值对应字节（小端拆分）
        assert_eq!(
            replay.pre,
            BTreeMap::from([(0x100, Some(0xDD)), (0x101, Some(0xCC)), (0x102, Some(0xBB)), (0x103, Some(0xAA))])
        );
        // 写覆盖后 post 取写数据字节
        assert_eq!(
            replay.post,
            BTreeMap::from([(0x100, Some(0x44)), (0x101, Some(0x33)), (0x102, Some(0x22)), (0x103, Some(0x11))])
        );
        assert_eq!(replay.unknown_components, 0);
    }

    #[test]
    fn replay_memory_写后再读同地址() {
        let replay = replay_memory(&[
            replay_access(false, Some(0x100), 4, Some(vec![0x44, 0x33, 0x22, 0x11])),
            replay_access(true, Some(0x100), 4, Some(vec![0x44, 0x33, 0x22, 0x11])),
        ]);

        // 首触是写：该字节初值自由，pre 输出 null，不拿写数据编造初值
        assert_eq!(replay.pre, BTreeMap::from([(0x100, None), (0x101, None), (0x102, None), (0x103, None)]));
        // 数组模型下写后读值等于写数据，post 为最后一次触碰（读）的字节
        assert_eq!(
            replay.post,
            BTreeMap::from([(0x100, Some(0x44)), (0x101, Some(0x33)), (0x102, Some(0x22)), (0x103, Some(0x11))])
        );
    }

    #[test]
    fn replay_memory_四字节写后读中间一字节() {
        let replay = replay_memory(&[
            replay_access(false, Some(0x100), 4, Some(vec![0xDD, 0xCC, 0xBB, 0xAA])),
            replay_access(true, Some(0x102), 1, Some(vec![0xBB])),
        ]);

        // 0x102 首触是写：pre 为 null；读回值等于写数据第 2 字节（小端）
        assert_eq!(replay.pre, BTreeMap::from([(0x100, None), (0x101, None), (0x102, None), (0x103, None)]));
        assert_eq!(
            replay.post,
            BTreeMap::from([(0x100, Some(0xDD)), (0x101, Some(0xCC)), (0x102, Some(0xBB)), (0x103, Some(0xAA))])
        );
    }

    #[test]
    fn replay_memory_独占失败写保留先前读取的字节() {
        let mut failed_write = replay_access(false, Some(0x100), 1, Some(vec![0xA5]));
        failed_write.is_exclusive = true;
        failed_write.write_success = Some(false);
        let replay = replay_memory(&[replay_access(true, Some(0x100), 1, Some(vec![0x11])), failed_write]);
        assert_eq!(replay.pre, BTreeMap::from([(0x100, Some(0x11))]));
        assert_eq!(replay.post, BTreeMap::from([(0x100, Some(0x11))]));
    }

    #[test]
    fn replay_memory_普通写返回假仍提交() {
        let mut ordinary_write = replay_access(false, Some(0x100), 1, Some(vec![0xA5]));
        ordinary_write.write_success = Some(false);
        let replay = replay_memory(&[replay_access(true, Some(0x100), 1, Some(vec![0x11])), ordinary_write]);
        assert_eq!(replay.pre, BTreeMap::from([(0x100, Some(0x11))]));
        assert_eq!(replay.post, BTreeMap::from([(0x100, Some(0xA5))]));
    }

    #[test]
    fn replay_memory_未知写结果不声称已提交() {
        let mut unknown_write = replay_access(false, Some(0x100), 1, Some(vec![0xA5]));
        unknown_write.is_exclusive = true;
        unknown_write.write_success = None;
        let replay = replay_memory(&[replay_access(true, Some(0x100), 1, Some(vec![0x11])), unknown_write]);
        assert_eq!(replay.pre, BTreeMap::from([(0x100, Some(0x11))]));
        assert_eq!(replay.post, BTreeMap::from([(0x100, None)]));
        assert_eq!(replay.unknown_components, 1);
    }

    #[test]
    fn replay_memory_未知分量计数() {
        let replay = replay_memory(&[
            replay_access(true, None, 4, Some(vec![0, 0, 0, 0])),
            replay_access(false, Some(0x100), 2, None),
        ]);

        // 地址未知：整条事件无法定位字节；数据未知：字节计入触碰但内容为 null
        assert_eq!(replay.unknown_components, 2);
        assert_eq!(replay.pre, BTreeMap::from([(0x100, None), (0x101, None)]));
        assert_eq!(replay.post, BTreeMap::from([(0x100, None), (0x101, None)]));
    }

    #[test]
    fn replay_memory_无区域时地址按位向量回绕() {
        let replay = replay_memory(&[replay_access(true, Some(u64::MAX), 2, Some(vec![0x11, 0x22]))]);
        assert_eq!(replay.pre, BTreeMap::from([(0, Some(0x22)), (u64::MAX, Some(0x11))]));
        assert_eq!(replay.post, replay.pre);
    }

    #[test]
    fn memory_spans_合并连续字节并按已知性分段() {
        let shared_state: SharedState<B64> = SharedState::empty(Symtab::new());
        let mut bytes = BTreeMap::new();
        bytes.insert(0x100, Some(0x44));
        bytes.insert(0x101, Some(0x33));
        bytes.insert(0x102, None);
        bytes.insert(0x103, None);
        bytes.insert(0x110, Some(0xAB));

        let spans = memory_spans_json(&bytes, &shared_state);

        assert_eq!(spans.len(), 3, "已知/未知混排时按已知性切分连续段");
        assert_eq!(
            (spans[0].address.as_str(), spans[0].bytes, spans[0].value.as_deref()),
            ("64'h0000_0000_0000_0100", 2, Some("16'h3344"))
        );
        assert_eq!(
            (spans[1].address.as_str(), spans[1].bytes, spans[1].value.as_deref()),
            ("64'h0000_0000_0000_0102", 2, None)
        );
        assert_eq!(
            (spans[2].address.as_str(), spans[2].bytes, spans[2].value.as_deref()),
            ("64'h0000_0000_0000_0110", 1, Some("8'hab"))
        );
    }

    #[test]
    fn materialize_le_bytes_物化符号与具体值() {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let sym = solver.declare_const(isla_lib::smt::smtlib::Ty::BitVec(32), SourceLoc::unknown());
        solver.assert_eq(
            isla_lib::smt::smtlib::Exp::Var(sym),
            isla_lib::smt::smtlib::Exp::Bits64(B64::new(0xAABBCCDD, 32)),
        );
        assert_eq!(solver.check_sat(SourceLoc::unknown()), isla_lib::smt::SmtResult::Sat);

        let mut model = Model::new(&solver);
        assert_eq!(
            materialize_le_bytes(&Val::Bits(B64::new(0x11223344, 32)), &mut model),
            Some(vec![0x44, 0x33, 0x22, 0x11])
        );
        assert_eq!(materialize_le_bytes(&Val::Symbolic(sym), &mut model), Some(vec![0xDD, 0xCC, 0xBB, 0xAA]));
    }

    #[test]
    fn materialize_le_bytes_宽混合位串不截断高位() {
        use isla_lib::bitvector::b129::B129;
        let context = Context::new(Config::new());
        let mut solver = Solver::<B129>::new(&context);
        assert_eq!(solver.check_sat(SourceLoc::unknown()), isla_lib::smt::SmtResult::Sat);
        let mut model = Model::new(&solver);
        let value = Val::MixedBits(vec![BitsSegment::Concrete(B129::ones(80))]);
        assert_eq!(materialize_le_bytes(&value, &mut model), Some(vec![0xff; 10]));
    }

    #[test]
    fn execute_as_instruction_识别转换指令() {
        let execute_as_text = zencode::encode("ExecuteAs");
        let load_text = zencode::encode("LOAD");
        let illegal_text = zencode::encode("Illegal_Instruction");
        let mut symtab = Symtab::new();
        let execute_as = symtab.intern(&execute_as_text);
        let load = symtab.intern(&load_text);
        let illegal = symtab.intern(&illegal_text);
        let shared_state: SharedState<B64> = SharedState::empty(symtab);

        let ret = Val::Ctor(execute_as, Box::new(Val::Ctor(load, Box::new(Val::Unit))));
        assert!(matches!(execute_as_instruction(&ret, &shared_state), Some(Val::Ctor(name, _)) if *name == load));

        let illegal_ret = Val::Ctor(illegal, Box::new(Val::Unit));
        assert!(execute_as_instruction(&illegal_ret, &shared_state).is_none(), "其它 ExecutionResult 不触发续执行");
        assert!(execute_as_instruction(&Val::Unit, &shared_state).is_none(), "非构造子返回值不触发续执行");
    }

    #[test]
    #[should_panic(expected = "ExecuteAs 载荷")]
    fn execute_as_instruction_载荷不是指令构造子时panic() {
        let execute_as_text = zencode::encode("ExecuteAs");
        let mut symtab = Symtab::new();
        let execute_as = symtab.intern(&execute_as_text);
        let shared_state: SharedState<B64> = SharedState::empty(symtab);

        let _ = execute_as_instruction(&Val::Ctor(execute_as, Box::new(Val::Unit)), &shared_state);
    }

    #[test]
    fn json_summary_marks_sampling_and_quota_as_partial() {
        let mut summary = SolveSummary::default();
        assert_eq!(summary.status(), "finished");
        summary.sampled_paths = 1;
        assert_eq!(summary.status(), "partial");
        let json = summary.json();
        assert_eq!(json["sampled-paths"], 1);
        assert_eq!(json["model-coverage"], "not-measured");
        summary.sampled_paths = 0;
        summary.omitted_cases = 1;
        assert_eq!(summary.status(), "partial");
    }

    fn collected_case(signature: u64, test_ins: &str, ret_val: &str) -> CollectedCase {
        CollectedCase {
            path_signature: signature,
            materialization_timed_out: false,
            item: AssemGenJsonItem {
                path_signature: signature,
                arch: BTreeMap::new(),
                test_ins: test_ins.to_string(),
                test_ins_encdec: "32'h0000_0000".to_string(),
                isa_state: BTreeMap::new(),
                ret_val: ret_val.to_string(),
                memory_events: Vec::new(),
                pre_memory: Vec::new(),
                post_memory: Vec::new(),
                value_hint: None,
                encoding_slice: None,
            },
        }
    }

    #[test]
    fn finalize_cases_不输出无指令的完成路径空壳() {
        let cases =
            vec![collected_case(1, "", "Retire_Success(())"), collected_case(2, "sd x1, 0(x2)", "Retire_Success(())")];
        let finalized = finalize_cases(cases, &None);
        assert_eq!(finalized.len(), 1);
        assert_eq!(finalized[0].test_ins, "sd x1, 0(x2)");
    }

    /// 终值查询超时只保留诊断，不能当作已具体化的见证。
    #[test]
    fn finalize_cases_终值超时不能进入可重放gen() {
        let mut degraded = collected_case(1, "", "Retire_Success(())");
        degraded.materialization_timed_out = true;
        let cases = vec![degraded, collected_case(2, "sd x1, 0(x2)", "Retire_Success(())")];
        let finalized = finalize_cases(cases, &None);
        assert_eq!(finalized.len(), 1, "超时路径不能冒充可重放见证");
        assert_eq!(finalized[0].test_ins, "sd x1, 0(x2)");
    }

    #[test]
    fn parse_model_timeout_ms_默认与显式值() {
        assert_eq!(parse_model_timeout_ms(None), Duration::from_millis(30_000));
        assert_eq!(parse_model_timeout_ms(Some("5000")), Duration::from_millis(5000));
        assert_eq!(parse_model_timeout_ms(Some(" 5000 ")), Duration::from_millis(5000));
    }

    #[test]
    #[should_panic(expected = "ISLA_RISCV_MODEL_TIMEOUT_MS")]
    fn parse_model_timeout_ms_拒绝零与非数字() {
        let _ = parse_model_timeout_ms(Some("0"));
    }

    #[test]
    fn case_quota_zero_discards_every_case_in_the_bucket() {
        let quota = CaseQuota { per_class: BTreeMap::from([(String::from("Illegal_Instruction"), 0)]) };
        let cases = vec![
            collected_case(1, "vadd.vv v0, v1, v2", "Illegal_Instruction(())"),
            collected_case(2, "vadd.vv v0, v1, v2", "Illegal_Instruction(())"),
            collected_case(3, "vadd.vv v0, v1, v2", "Retire_Success(())"),
        ];

        let finalized = finalize_cases(cases, &Some(quota));

        assert_eq!(finalized.len(), 1);
        assert_eq!(finalized[0].ret_val, "Retire_Success(())");
    }

    #[test]
    fn case_quota_same_signature_uses_canonical_json_tie_breaker() {
        let quota = CaseQuota { per_class: BTreeMap::from([(String::from("Illegal_Instruction"), 1)]) };
        let first = vec![
            collected_case(9, "vadd.vv v0, v1, v2", "Illegal_Instruction(())"),
            collected_case(9, "vadd.vv v0, v1, v3", "Illegal_Instruction(())"),
        ];
        let second = first.iter().cloned().rev().collect();

        let first = serde_json::to_string(&finalize_cases(first, &Some(quota.clone()))).unwrap();
        let second = serde_json::to_string(&finalize_cases(second, &Some(quota))).unwrap();

        assert_eq!(first, second);
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

    /// 真 rv64d.ir 的初始化环境（P3 集成测试共用）：加载 IR + difftest pma
    /// 配置，返回 (shared_state, regs, lets)。加载约 4-5 秒，两个用例各自
    /// 重建，避免测试间共享可变状态。
    fn real_ir_env() -> (SharedState<'static, B129>, RegisterBindings<'static, B129>, Bindings<'static, B129>) {
        let contents: &'static str = Box::leak(
            std::fs::read_to_string("rv64d.ir").expect("测试需要从仓库根目录运行，读 rv64d.ir").into_boxed_str(),
        );
        let mut symtab = Symtab::new();
        let mut arch: &'static mut [Def<Name, B129>] = Box::leak(
            isla_lib::ir_parser::IrParser::new()
                .parse(&mut symtab, isla_lib::ir_lexer::new_ir_lexer(contents))
                .expect("解析 rv64d.ir 失败")
                .into_boxed_slice(),
        );
        let type_info = IRTypeInfo::new(&arch);
        let config_contents = std::fs::read_to_string("configs/riscv64_difftest_mem_excluded_pma.toml")
            .expect("测试需要从仓库根目录运行，读 configs/riscv64_difftest_mem_excluded_pma.toml");
        let isa_config =
            isla_lib::config::ISAConfig::parse(&config_contents, None, &symtab, &type_info).expect("ISA 配置解析失败");
        let isla_lib::init::Initialized { regs, lets, shared_state } = isla_lib::init::initialize_architecture(
            arch,
            symtab,
            type_info,
            &isa_config,
            isla_lib::ir::AssertionMode::Pessimistic,
            false,
        );
        (shared_state, regs, lets)
    }

    /// P3 集成：ldu 编码（funct3=111，RV64 非法变体——zencdec_forwards 在
    /// 物化环境越过 valid_load_encdec 守卫产出的形态）必须被译码回环拒绝：
    /// zext_decode 对它译出 ILLEGAL，与 zLOAD 构造子不一致。
    #[test]
    fn encdec_guard_回环拒绝ldu非法编码() {
        let (shared_state, regs, lets) = real_ir_env();
        let load_ctor = shared_state.symtab.lookup("zLOAD");
        // 32'h7e8e_7003：imm=0x7e8, rs1=x28, funct3=111, rd=x0, opcode=0000011
        let ldu_bits = Val::Bits(B129::new(0x7e8e_7003, 32));
        assert_eq!(
            encdec_guard_roundtrip_ok(load_ctor, &ldu_bits, &shared_state, &regs, &lets),
            Ok(false),
            "ldu 编码（funct3=111）应被 encdec 守卫回环拒绝"
        );
    }

    /// P3 集成：AMO 的非法 op×width 组合（amoswap.q——RVA/Zabha 无 16 字节
    /// swap，decode 译出 ILLEGAL）也必须被回环拒绝。
    #[test]
    fn encdec_guard_回环拒绝amoswapq非法编码() {
        let (shared_state, regs, lets) = real_ir_env();
        let amo_ctor = shared_state.symtab.lookup("zAMO");
        // 32'h0900_402f：funct5=amoswap, funct3=100（16 字节 q），实跑产物形态
        let swap_q = Val::Bits(B129::new(0x0900_402f, 32));
        assert_eq!(
            encdec_guard_roundtrip_ok(amo_ctor, &swap_q, &shared_state, &regs, &lets),
            Ok(false),
            "amoswap.q 编码（无 16 字节 swap）应被回环拒绝"
        );
        // amoswap.h（Zabha）译回 zAMO，放行
        let swap_h = Val::Bits(B129::new(0x09ff_902f, 32));
        assert_eq!(
            encdec_guard_roundtrip_ok(amo_ctor, &swap_h, &shared_state, &regs, &lets),
            Ok(true),
            "Zabha amoswap.h 编码应译回 zAMO 并通过回环"
        );
    }

    /// P3 集成：向量段 store 构造子（zVSSEGTYPE）的合法编码（vse8.v，
    /// P2 验收产物 32'h0000_0027）译回同构造子放行；跨构造子（拿 zLOAD
    /// 校验）拒绝。VSSEG 全量求解超出本测时间盒，产物级扫描由验收战役
    /// 覆盖（见议题状态文档）。
    #[test]
    fn encdec_guard_向量段store编码回环() {
        let (shared_state, regs, lets) = real_ir_env();
        let vsseg_ctor = shared_state.symtab.lookup("zVSSEGTYPE");
        let vse8 = Val::Bits(B129::new(0x0000_0027, 32));
        assert_eq!(
            encdec_guard_roundtrip_ok(vsseg_ctor, &vse8, &shared_state, &regs, &lets),
            Ok(true),
            "vse8.v 编码应译回 zVSSEGTYPE 并通过回环"
        );
        let load_ctor = shared_state.symtab.lookup("zLOAD");
        assert_eq!(
            encdec_guard_roundtrip_ok(load_ctor, &vse8, &shared_state, &regs, &lets),
            Ok(false),
            "向量 store 编码对 zLOAD 构造子应拒绝"
        );
    }

    /// P3 集成：合法 load 编码（lb，funct3=000）译回仍是 zLOAD，回环放行。
    #[test]
    fn encdec_guard_回环放行合法load编码() {
        let (shared_state, regs, lets) = real_ir_env();
        let load_ctor = shared_state.symtab.lookup("zLOAD");
        // 32'h4000_0003：imm=0x400, rs1=x0, funct3=000, rd=x0, opcode=0000011（lb）
        let lb_bits = Val::Bits(B129::new(0x4000_0003, 32));
        assert_eq!(
            encdec_guard_roundtrip_ok(load_ctor, &lb_bits, &shared_state, &regs, &lets),
            Ok(true),
            "合法 lb 编码应通过 encdec 守卫回环"
        );
    }

    /// P3 集成：16 位压缩编码走 zext_decode_compressed 回环；c.nop（0x0001）
    /// 译回 zC_NOP。构造子不一致（拿 zLOAD 对 0x0001 校验）时拒绝。
    #[test]
    fn encdec_guard_压缩编码回环与构造子校验() {
        let (shared_state, regs, lets) = real_ir_env();
        let nop_bits = Val::Bits(B129::new(0x0001, 16));
        let c_nop_ctor = shared_state.symtab.lookup("zC_NOP");
        assert_eq!(
            encdec_guard_roundtrip_ok(c_nop_ctor, &nop_bits, &shared_state, &regs, &lets),
            Ok(true),
            "c.nop 编码应译回 zC_NOP 并通过回环"
        );
        let load_ctor = shared_state.symtab.lookup("zLOAD");
        assert_eq!(
            encdec_guard_roundtrip_ok(load_ctor, &nop_bits, &shared_state, &regs, &lets),
            Ok(false),
            "编码译回的构造子与原指令不一致时应拒绝"
        );
    }

    /// P3：非位向量编码是内部不变量违反（防御式，不允许静默放行）。
    #[test]
    fn encdec_guard_非位向量编码报错() {
        let (shared_state, regs, lets) = real_ir_env();
        let load_ctor = shared_state.symtab.lookup("zLOAD");
        let err = encdec_guard_roundtrip_ok(load_ctor, &Val::Bool(true), &shared_state, &regs, &lets)
            .expect_err("非位向量编码必须报错");
        assert!(err.contains("非位向量"), "实际: {}", err);
    }

    /// P3：保留编码开关默认关（过滤启用），"1" 开，"0" 关，非法值硬失败。
    #[test]
    fn parse_allow_reserved_encodings_三态解析() {
        assert!(!parse_allow_reserved_encodings(None));
        assert!(!parse_allow_reserved_encodings(Some("0")));
        assert!(parse_allow_reserved_encodings(Some("1")));
    }

    #[test]
    #[should_panic(expected = "仅支持 0 或 1")]
    fn parse_allow_reserved_encodings_非法值硬失败() {
        parse_allow_reserved_encodings(Some("yes"));
    }
}
