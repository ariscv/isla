use super::clause::{get_extension_clauses, normalize_clause_name};
use super::target::{Target, RISCV};
use super::timeout_report::TimeoutReporter;
pub use super::timeout_report::{TimeoutReportConfig, TimeoutSmtOutput};
use super::{get_all_clause_names, list_instructions, try_get_assembly_encdec, try_get_assembly_name};
use isla_lib::bitvector::BV;
use isla_lib::config::ExecutionLimitsConfig;
use isla_lib::error::IslaError;
use isla_lib::error::{ExecError, SmtError};
use isla_lib::executor::{backtrace_string, LocalFrame, Run};
use isla_lib::executor::{ExecutionLimits, TaskState};
use isla_lib::fmtval::FmtVal;
use isla_lib::ir::*;
use isla_lib::log;
use isla_lib::primop_util::symbolic;
use isla_lib::register::RegisterBindings;
use isla_lib::smt::{Config, Context, Model};
use isla_lib::smt::{Solver, Sym};
use isla_lib::source_loc::SourceLoc;
use isla_lib::zencode;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

const SOLVE_WRAPPER: &str = "zisarch_solve_wrapper";
const SOLVE_REQUESTED: &str = "zisarch_requested";
const SOLVE_ENCODED: &str = "zisarch_encoded";
const SOLVE_DECODED: &str = "zisarch_decoded";
const WRAPPER_ENCODE_PC: usize = 1;
const WRAPPER_DECODE_PC: usize = 4;
const WRAPPER_EXECUTE_PC: usize = 6;
const OFFICIAL_FLOAT_77: &str = include_str!("official_float77.txt");

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum SolveEntryMode {
    FullEncoded32,
    ConstructorDiagnostic,
}

impl SolveEntryMode {
    fn for_clause(clause: &str) -> Self {
        let name = clause.strip_prefix('z').unwrap_or(clause);
        if OFFICIAL_FLOAT_77.lines().any(|entry| entry == name) {
            Self::FullEncoded32
        } else {
            Self::ConstructorDiagnostic
        }
    }

    fn as_str(self) -> &'static str {
        match self {
            Self::FullEncoded32 => "full-encoded-32",
            Self::ConstructorDiagnostic => "constructor-diagnostic",
        }
    }
}

/// 在 ISA 初始化前安装一个共享求解器的入口。入口态、编码、译码和执行均在同一条路径上。
pub fn install_solve_wrapper<B: BV>(arch: &mut Vec<Def<Name, B>>, symtab: &mut Symtab<'_>) {
    assert!(symtab.get(SOLVE_WRAPPER).is_none(), "solve wrapper 名称与 IR 冲突");
    for name in ["zencdec_forwards", "zext_decode", "zexecute", "zinstruction", "zExecutionResult"] {
        assert!(symtab.get(name).is_some(), "solve wrapper 缺少 IR 符号 {name}");
    }
    let wrapper = symtab.intern(SOLVE_WRAPPER);
    let requested = symtab.intern(SOLVE_REQUESTED);
    let encoded = symtab.intern(SOLVE_ENCODED);
    let decoded = symtab.intern(SOLVE_DECODED);
    let instruction_ty = Ty::Union(symtab.lookup("zinstruction"));
    let result_ty = Ty::Union(symtab.lookup("zExecutionResult"));
    let location = SourceLoc::unknown();
    arch.push(Def::Val(wrapper, vec![instruction_ty.clone()], result_ty.clone()));
    arch.push(Def::Fn(
        wrapper,
        vec![requested],
        vec![
            Instr::Decl(encoded, Ty::Bits(32), location),
            Instr::Call(Loc::Id(encoded), false, symtab.lookup("zencdec_forwards"), vec![Exp::Id(requested)], location),
            Instr::Jump(Exp::Id(HAVE_EXCEPTION), 9, location),
            Instr::Decl(decoded, instruction_ty, location),
            Instr::Call(Loc::Id(decoded), false, symtab.lookup("zext_decode"), vec![Exp::Id(encoded)], location),
            Instr::Jump(Exp::Id(HAVE_EXCEPTION), 10, location),
            Instr::Call(Loc::Id(RETURN), false, symtab.lookup("zexecute"), vec![Exp::Id(decoded)], location),
            Instr::Jump(Exp::Id(HAVE_EXCEPTION), 11, location),
            Instr::End,
            Instr::Arbitrary,
            Instr::Arbitrary,
            Instr::Arbitrary,
        ],
    ));
}

#[allow(non_camel_case_types)]
#[derive(Serialize, Deserialize, Clone)]
struct AssemGenJsonItem {
    arch: BTreeMap<String, String>,
    #[serde(rename = "test-ins")]
    test_ins: String,
    #[serde(rename = "test-ins-encdec")]
    test_ins_encdec: String,
    #[serde(rename = "isa-state")]
    isa_state: BTreeMap<String, String>,
    ret_val: String,
    #[serde(rename = "case-id")]
    case_id: u64,
    #[serde(rename = "path-signature")]
    path_signature: u64,
    #[serde(rename = "requested-instruction")]
    requested_instruction: String,
    #[serde(rename = "decoded-instruction")]
    decoded_instruction: String,
    #[serde(rename = "entry-domain")]
    entry_domain: String,
    #[serde(rename = "isa-state-complete")]
    isa_state_complete: BTreeMap<String, String>,
    #[serde(rename = "isa-state-post")]
    isa_state_post: BTreeMap<String, String>,
}
impl AssemGenJsonItem {
    pub fn new<B: BV>(
        target: &dyn Target<B>,
        test_ins: String,
        test_ins_encdec: String,
        isa_state: BTreeMap<String, String>,
        ret_val: String,
        case_id: u64,
        path_signature: u64,
        requested_instruction: String,
        decoded_instruction: String,
        entry_domain: String,
        isa_state_complete: BTreeMap<String, String>,
        isa_state_post: BTreeMap<String, String>,
    ) -> Self {
        let mut arch = BTreeMap::new();
        arch.insert("pretty-name".to_string(), target.arch_pretty_name().to_string());
        arch.insert("name".to_string(), target.arch_name().to_string());
        arch.insert("xlen".to_string(), target.xlen().to_string());
        AssemGenJsonItem {
            arch,
            test_ins,
            test_ins_encdec,
            isa_state,
            ret_val,
            case_id,
            path_signature,
            requested_instruction,
            decoded_instruction,
            entry_domain,
            isa_state_complete,
            isa_state_post,
        }
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
    summary: SolveSummary,
    terminals: Vec<TerminalRecord>,
}
impl ToJSON for AssemGenJson {}
impl ToJSON for AssemGenJsonItem {}
impl AssemGenJson {
    fn new(gen: Vec<AssemGenJsonItem>, summary: SolveSummary, terminals: Vec<TerminalRecord>) -> Self {
        AssemGenJson { gen, summary, terminals }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct TerminalRecord {
    #[serde(rename = "case-id")]
    case_id: u64,
    #[serde(rename = "path-signature")]
    path_signature: u64,
    status: String,
    phase: String,
    function: String,
    source: String,
    detail: Option<String>,
    sampled: bool,
    emitted: bool,
    #[serde(rename = "requested-instruction")]
    requested_instruction: Option<String>,
    #[serde(rename = "isa-state-complete")]
    isa_state_complete: Option<BTreeMap<String, String>>,
    #[serde(rename = "witness-error")]
    witness_error: Option<String>,
    #[serde(rename = "mapping-source")]
    mapping_source: Option<String>,
}

#[derive(Serialize, Deserialize)]
struct SolveSummary {
    clause: String,
    #[serde(rename = "entry-mode")]
    entry_mode: String,
    total: usize,
    counts: BTreeMap<String, usize>,
    complete: bool,
    #[serde(rename = "state-domain")]
    state_domain: BTreeMap<String, String>,
    emitted: usize,
    suppressed: usize,
}

impl SolveSummary {
    fn from_terminals(
        clause: &str,
        mode: SolveEntryMode,
        state_domain: BTreeMap<String, String>,
        terminals: &[TerminalRecord],
    ) -> Self {
        let mut counts = BTreeMap::new();
        for terminal in terminals {
            *counts.entry(terminal.status.clone()).or_default() += 1;
        }
        let complete = !terminals.is_empty()
            && terminals.iter().all(|terminal| {
                !terminal.sampled
                    && terminal.witness_error.is_none()
                    && matches!(
                        terminal.status.as_str(),
                        "retire" | "illegal" | "decode-rejected" | "non-encodable" | "unsat"
                    )
            });
        let emitted = terminals.iter().filter(|terminal| terminal.emitted).count();
        let suppressed = terminals
            .iter()
            .filter(|terminal| {
                matches!(terminal.status.as_str(), "retire" | "illegal" | "decode-rejected") && !terminal.emitted
            })
            .count();
        SolveSummary {
            clause: clause.to_string(),
            entry_mode: mode.as_str().to_string(),
            total: terminals.len(),
            counts,
            complete,
            state_domain,
            emitted,
            suppressed,
        }
    }
}

/// 一条完成的用例 + 它的路径签名。签名用于收尾阶段的稳定排序与配额取样，让多线程下
/// 的产出顺序不影响最终落盘的用例集合（按 codex 评审意见的"路径局部指纹 + 全量 canonical sort"）。
#[derive(Clone)]
struct CollectedCase {
    path_signature: u64,
    item: AssemGenJsonItem,
}

struct SolveCollectorState {
    cases: Vec<CollectedCase>,
    terminals: Vec<TerminalRecord>,
    case_quota: Option<CaseQuota>,
    first_error: Option<ExecError>,
}

impl SolveCollectorState {
    fn new() -> Self {
        Self::with_case_quota(None)
    }

    fn with_case_quota(case_quota: Option<CaseQuota>) -> Self {
        SolveCollectorState { first_error: None, cases: Vec::new(), terminals: Vec::new(), case_quota }
    }

    fn begin_terminal(&mut self, path_signature: u64, function: String, source: String, sampled: bool) -> u64 {
        let case_id = self.terminals.len() as u64 + 1;
        self.terminals.push(TerminalRecord {
            case_id,
            path_signature,
            status: "pending".to_string(),
            phase: "execute".to_string(),
            function,
            source,
            detail: None,
            sampled,
            emitted: false,
            requested_instruction: None,
            isa_state_complete: None,
            witness_error: None,
            mapping_source: None,
        });
        case_id
    }

    fn finish_terminal(&mut self, case_id: u64, status: &str, phase: &str, detail: Option<String>) {
        let terminal = self.terminals.get_mut((case_id - 1) as usize).expect("terminal case-id 必须已分配");
        terminal.status = status.to_string();
        terminal.phase = phase.to_string();
        terminal.detail = detail;
    }

    fn set_terminal_witness(&mut self, case_id: u64, witness: Result<(String, BTreeMap<String, String>), ExecError>) {
        let terminal = self.terminals.get_mut((case_id - 1) as usize).expect("terminal case-id 必须已分配");
        match witness {
            Ok((instruction, state)) => {
                terminal.requested_instruction = Some(instruction);
                terminal.isa_state_complete = Some(state);
            }
            Err(error) => {
                terminal.witness_error = Some(error.to_string());
                self.record_error(&error);
            }
        }
    }

    fn set_terminal_mapping_source(&mut self, case_id: u64, source: String) {
        let terminal = self.terminals.get_mut((case_id - 1) as usize).expect("terminal case-id 必须已分配");
        terminal.mapping_source = Some(source);
    }

    fn set_terminal_source(&mut self, case_id: u64, source: String) {
        let terminal = self.terminals.get_mut((case_id - 1) as usize).expect("terminal case-id 必须已分配");
        terminal.source = source;
    }

    fn record_error(&mut self, error: &ExecError) {
        if self.first_error.is_none() {
            self.first_error = Some(error.clone());
        }
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
        self.collected.lock().expect("solve collector mutex poisoned").record_error(error);
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
/// 因此 THREADS=1/4/64 下用例内容集合和排序稳定。case-id 是回调 ID，可能随调度变化。
fn finalize_cases(mut cases: Vec<CollectedCase>, quota: &Option<CaseQuota>) -> Vec<AssemGenJsonItem> {
    // 1. 组内配额：按 (助记符, 完整 test-ins, ret_val 类别) 分桶，每组按签名均匀取样。
    if let Some(quota) = quota {
        cases = apply_case_quota(cases, quota);
    }
    // 2. 全量稳定排序：签名 + 序列化文本做 tie-breaker，杜绝签名碰撞时的调度依赖。
    cases.sort_by(|a, b| {
        let a_text = case_sort_key(&a.item);
        let b_text = case_sort_key(&b.item);
        a.path_signature.cmp(&b.path_signature).then_with(|| a_text.cmp(&b_text))
    });
    cases.into_iter().map(|case| case.item).collect()
}

fn case_sort_key(item: &AssemGenJsonItem) -> String {
    let mut item = item.clone();
    // case-id 来自多线程回调顺序，只用于关联终态/itrace，不能参与内容排序或配额取样。
    item.case_id = 0;
    serde_json::to_string(&item).expect("AssemGenJsonItem 序列化失败")
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
                    let a_text = case_sort_key(&a.item);
                    let b_text = case_sort_key(&b.item);
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
                shared_state.itrace.set_runtime_catalog(shared_state);
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
            &timeout_reporter,
            case_quota.clone(),
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

fn encoder_rejection_pc<B: BV>(shared_state: &SharedState<B>, ctor: Name) -> Option<(usize, SourceLoc, SourceLoc)> {
    let encoder = shared_state.symtab.get("zencdec_forwards")?;
    let (_, _, instructions) = shared_state.functions.get(&encoder)?;
    let exits: Vec<_> = instructions
        .iter()
        .enumerate()
        .filter_map(|(pc, instr)| match instr {
            Instr::Exit(ExitCause::MatchFailure, source) => Some((pc, *source)),
            _ => None,
        })
        .collect();
    if exits.len() != 1 || exits[0].0 + 4 != instructions.len() {
        return None;
    }
    assert!(matches!(instructions[exits[0].0 + 1], Instr::Copy(Loc::Id(RETURN), _, _)));
    assert!(matches!(instructions[exits[0].0 + 2], Instr::End));
    assert!(matches!(instructions[exits[0].0 + 3], Instr::Arbitrary));
    let arm_source = instructions.iter().find_map(|instr| match instr {
        Instr::Jump(Exp::Kind(kind, _), _, source) if *kind == ctor && *source != SourceLoc::unknown() => Some(*source),
        _ => None,
    })?;
    Some((exits[0].0, exits[0].1, arm_source))
}

fn phase_from_frame<B: BV>(frame: &LocalFrame<B>, shared_state: &SharedState<B>) -> &'static str {
    let wrapper = shared_state.symtab.lookup(SOLVE_WRAPPER);
    let call_pc = if frame.function_name() == wrapper {
        Some(frame.pc())
    } else {
        frame.backtrace().iter().find(|(name, _)| *name == wrapper).map(|(_, pc)| *pc)
    };
    match call_pc {
        Some(WRAPPER_ENCODE_PC | 9) => "encode",
        Some(WRAPPER_DECODE_PC | 10) => "decode",
        Some(WRAPPER_EXECUTE_PC | 11) | None => "execute",
        Some(_) => "execute",
    }
}

fn wrapper_var<'ir, B: BV>(
    frame: &LocalFrame<'ir, B>,
    shared_state: &SharedState<B>,
    name: &str,
) -> Result<Val<B>, ExecError> {
    let id = shared_state.symtab.lookup(name);
    match frame.vars().get(&id) {
        Some(UVal::Init(value)) => Ok(value.clone()),
        _ => Err(ExecError::VariableNotFound(name.to_string(), SourceLoc::unknown())),
    }
}

fn stable_instruction_text<B: BV>(value: &Val<B>, shared_state: &SharedState<B>) -> String {
    match value {
        Val::Ctor(ctor, inner) => format!(
            "{}({})",
            zencode::decode(shared_state.symtab.to_str_demangled(*ctor)),
            stable_instruction_text(inner, shared_state)
        ),
        Val::Struct(fields) => {
            let mut fields: Vec<_> = fields.iter().collect();
            fields.sort_by_key(|(name, _)| shared_state.symtab.to_str(**name));
            let fields = fields
                .into_iter()
                .map(|(name, value)| {
                    format!(
                        "{}:{}",
                        zencode::decode(shared_state.symtab.to_str_demangled(*name)),
                        stable_instruction_text(value, shared_state)
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            format!("{{{fields}}}")
        }
        Val::Vector(values) | Val::List(values) => {
            let values = values.iter().map(|value| stable_instruction_text(value, shared_state)).collect::<Vec<_>>();
            format!("[{}]", values.join(","))
        }
        _ => value.to_str(shared_state),
    }
}

fn verify_decoded_instruction<B: BV>(
    requested: Val<B>,
    decoded: Val<B>,
    solver: &mut Solver<B>,
) -> Result<(), ExecError> {
    use isla_lib::smt::smtlib::Exp as SmtExp;
    let equality = isla_lib::primop::eq_anything(requested, decoded, solver, SourceLoc::unknown())?;
    let disequality = match equality {
        Val::Bool(true) => return Ok(()),
        Val::Bool(false) => {
            return Err(ExecError::Unreachable("编码再译码改变了 instruction constructor/参数".to_string()))
        }
        Val::Symbolic(sym) => SmtExp::Not(Box::new(SmtExp::Var(sym))),
        value => return Err(ExecError::Type(format!("instruction equality returned {value:?}"), SourceLoc::unknown())),
    };
    match solver.check_sat_with(&disequality, SourceLoc::unknown()) {
        isla_lib::smt::SmtResult::Unsat => Ok(()),
        isla_lib::smt::SmtResult::Sat => Err(ExecError::Unreachable("编码再译码关系存在反例".to_string())),
        isla_lib::smt::SmtResult::Unknown => Err(ExecError::Z3Unknown),
        isla_lib::smt::SmtResult::Error(error) => Err(ExecError::Smt(error)),
    }
}

fn nonencodable_witness<B: BV>(
    target: &dyn RISCV<B>,
    shared_state: &SharedState<B>,
    requested: &Val<B>,
    solver: &mut Solver<B>,
) -> Result<(String, BTreeMap<String, String>), ExecError> {
    match solver.check_sat(SourceLoc::unknown()) {
        isla_lib::smt::SmtResult::Sat => (),
        isla_lib::smt::SmtResult::Unsat => return Err(ExecError::NoModel),
        isla_lib::smt::SmtResult::Unknown => return Err(ExecError::Z3Unknown),
        isla_lib::smt::SmtResult::Error(error) => return Err(ExecError::Smt(error)),
    }
    let mut model = Model::new(solver);
    model.set_complete_model(true);
    let instruction = stable_instruction_text(&model.get_val(requested)?, shared_state);
    let state = target.solve_pre_state_complete(&mut model, shared_state)?;
    Ok((instruction, state))
}

fn materialize_finished_case<'ir, B: BV>(
    target: &dyn RISCV<B>,
    frame: &LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
    mut solver: Solver<B>,
    ret_val: &Val<B>,
    case_id: u64,
    mode: SolveEntryMode,
    fun_args: &[Val<B>],
) -> Result<AssemGenJsonItem, ExecError> {
    let requested = match mode {
        SolveEntryMode::FullEncoded32 => wrapper_var(frame, shared_state, SOLVE_REQUESTED)?,
        SolveEntryMode::ConstructorDiagnostic => fun_args[0].clone(),
    };
    let decoded = match mode {
        SolveEntryMode::FullEncoded32 => Some(wrapper_var(frame, shared_state, SOLVE_DECODED)?),
        SolveEntryMode::ConstructorDiagnostic => None,
    };
    let encoded = match mode {
        SolveEntryMode::FullEncoded32 => Some(wrapper_var(frame, shared_state, SOLVE_ENCODED)?),
        SolveEntryMode::ConstructorDiagnostic => None,
    };
    let decode_rejected = matches!(&decoded, Some(Val::Ctor(ctor, _)) if zencode::decode(shared_state.symtab.to_str_demangled(*ctor)) == "ILLEGAL");
    if decode_rejected
        && !matches!(ret_val, Val::Ctor(ctor, _) if zencode::decode(shared_state.symtab.to_str_demangled(*ctor)) == "Illegal_Instruction")
    {
        return Err(ExecError::Unreachable("decoder ILLEGAL did not execute to Illegal_Instruction".to_string()));
    }
    if let Some(decoded) = &decoded {
        if !decode_rejected {
            verify_decoded_instruction(requested.clone(), decoded.clone(), &mut solver)?;
        }
    }
    if matches!(ret_val, Val::Ctor(ctor, _) if zencode::decode(shared_state.symtab.to_str_demangled(*ctor)) == "Illegal_Instruction")
    {
        // 路径关系已在完整符号域验证；这里只为输出 witness 选一个可满足的代表值。
        diversify_unconstrained_finite_domains(
            std::slice::from_ref(&requested),
            frame.path_signature(),
            shared_state,
            &mut solver,
        )?;
    }
    match solver.check_sat(SourceLoc::unknown()) {
        isla_lib::smt::SmtResult::Sat => (),
        isla_lib::smt::SmtResult::Unsat => return Err(ExecError::NoModel),
        isla_lib::smt::SmtResult::Unknown => return Err(ExecError::Z3Unknown),
        isla_lib::smt::SmtResult::Error(error) => return Err(ExecError::Smt(error)),
    }
    let mut model = Model::new(&solver);
    let isa_state = target.solve_pre_state(&mut model, shared_state)?;
    model.set_complete_model(true);
    let requested_concrete = model.get_val(&requested)?;
    let decoded_concrete = decoded.as_ref().map(|value| model.get_val(value)).transpose()?;
    let encoded_concrete = encoded.as_ref().map(|value| model.get_val(value)).transpose()?;
    let requested_instruction = stable_instruction_text(&requested_concrete, shared_state);
    let decoded_instruction =
        decoded_concrete.as_ref().map(|value| stable_instruction_text(value, shared_state)).unwrap_or_default();
    let mut concrete_regs = regs.clone();
    for (name, value) in target.pre_state().iter() {
        concrete_regs.assign(*name, model.get_val(value)?, shared_state);
    }
    let test_ins = try_get_assembly_name(requested_concrete.clone(), shared_state, &concrete_regs, lets)?
        .ok_or_else(|| ExecError::Unreachable("assembly printer 未返回指令文本".to_string()))?;
    let test_ins_encdec = match encoded_concrete {
        Some(encoded) => FmtVal::from_val(&encoded, &mut model)?.to_str(shared_state),
        None => {
            let encoded = try_get_assembly_encdec(requested_concrete, shared_state, &concrete_regs, lets)?
                .ok_or_else(|| ExecError::Unreachable("diagnostic encoder 未返回编码".to_string()))?;
            FmtVal::from_val(&encoded, &mut model)?.to_str(shared_state)
        }
    };
    let isa_state_complete = target.solve_pre_state_complete(&mut model, shared_state)?;
    let isa_state_post = target.solve_post_state(frame.regs(), &mut model, shared_state)?;
    Ok(AssemGenJsonItem::new(
        target,
        test_ins,
        test_ins_encdec,
        isa_state,
        ret_val.to_str(shared_state).to_string(),
        case_id,
        frame.path_signature(),
        requested_instruction,
        decoded_instruction,
        match mode {
            SolveEntryMode::ConstructorDiagnostic => "constructor-diagnostic",
            SolveEntryMode::FullEncoded32 if decode_rejected => "decode-rejected",
            SolveEntryMode::FullEncoded32 => "decoded",
        }
        .to_string(),
        isa_state_complete,
        isa_state_post,
    ))
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
) -> Result<Option<String>, ExecError> {
    use isla_lib::smt::checkpoint;

    let mode = SolveEntryMode::for_clause(instruction_name);

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
    let result: Arc<Mutex<SolveCollectorState>> =
        Arc::new(Mutex::new(SolveCollectorState::with_case_quota(case_quota)));

    let task_state = TaskState::new().with_execution_limits(execution_limits.clone());

    isla_lib::executor::execute_ir_function_with_checkpoint_multi_thread(
        match mode {
            SolveEntryMode::FullEncoded32 => SOLVE_WRAPPER,
            SolveEntryMode::ConstructorDiagnostic => "zexecute",
        },
        &fun_args,
        shared_state,
        &symbolic_regs,
        lets,
        &result,
        &|thread, task_id, exec_result, shared_state, mut solver, collected| {
            let frame = match &exec_result {
                Ok((_, frame)) | Err((_, frame)) => frame,
            };
            let function = shared_state.symtab.to_str_demangled(frame.function_name()).to_string();
            let case_id = collected.lock().expect("solve collector mutex poisoned").begin_terminal(
                frame.path_signature(),
                function.clone(),
                match &exec_result {
                    Err((error, _)) => error.source_loc().location_string(shared_state.symtab.files()),
                    Ok(_) => SourceLoc::unknown().location_string(shared_state.symtab.files()),
                },
                frame.has_sampled_branch(),
            );
            let error_recorder = ErrorRecorder { collected, reporter: timeout_reporter, clause: instruction_name };
            let mut diagnostics = Vec::new();
            let (status, phase, detail) = match &exec_result {
                Ok((Run::Finished(Val::Poison), _)) => {
                    let phase = phase_from_frame(frame, shared_state);
                    if let Some(UVal::Init(Val::String(source))) = frame.lets().get(&THROW_LOCATION) {
                        collected
                            .lock()
                            .expect("solve collector mutex poisoned")
                            .set_terminal_source(case_id, source.clone());
                    }
                    let exception = format!(
                        "have_exception={:?}; exception={:?}; throw_location={:?}",
                        frame.lets().get(&HAVE_EXCEPTION),
                        frame.lets().get(&CURRENT_EXCEPTION),
                        frame.lets().get(&THROW_LOCATION),
                    );
                    let error = ExecError::Unreachable(format!(
                        "single instruction returned Poison during {}: {}",
                        phase, exception
                    ));
                    diagnostics = error_recorder.record_error_diagnostic(&error, frame, shared_state);
                    ("error", phase, Some(error.to_string()))
                }
                Ok((Run::Finished(ret_val), _)) => {
                    let result_class = match ret_val {
                        Val::Ctor(ctor, _) => zencode::decode(shared_state.symtab.to_str_demangled(*ctor)),
                        _ => String::new(),
                    };
                    if result_class != "Retire_Success" && result_class != "Illegal_Instruction" {
                        let error = ExecError::Unreachable(format!(
                            "unsupported ExecutionResult before materialization: {}",
                            ret_val.to_str(shared_state)
                        ));
                        diagnostics = error_recorder.record_error_diagnostic(&error, frame, shared_state);
                        ("error", "execute", Some(error.to_string()))
                    } else {
                        let sat = solver.check_sat(SourceLoc::unknown());
                        match sat {
                            isla_lib::smt::SmtResult::Unsat => {
                                ("unsat", "materialize", Some("final solver UNSAT".to_string()))
                            }
                            isla_lib::smt::SmtResult::Unknown => {
                                let error = ExecError::Z3Unknown;
                                diagnostics = error_recorder.record_error_diagnostic(&error, frame, shared_state);
                                ("error", "materialize", Some(error.to_string()))
                            }
                            isla_lib::smt::SmtResult::Error(error) => {
                                let error = ExecError::Smt(error);
                                diagnostics = error_recorder.record_error_diagnostic(&error, frame, shared_state);
                                ("error", "materialize", Some(error.to_string()))
                            }
                            isla_lib::smt::SmtResult::Sat => {
                                match materialize_finished_case(
                                    target,
                                    frame,
                                    shared_state,
                                    &symbolic_regs,
                                    lets,
                                    solver,
                                    ret_val,
                                    case_id,
                                    mode,
                                    &fun_args,
                                ) {
                                    Ok(item) => {
                                        let status = if item.entry_domain == "decode-rejected" {
                                            "decode-rejected"
                                        } else if item.ret_val.starts_with("Retire_Success") {
                                            "retire"
                                        } else if item.ret_val.starts_with("Illegal_Instruction") {
                                            "illegal"
                                        } else {
                                            "error"
                                        };
                                        if status == "error" {
                                            let error = ExecError::Unreachable(format!(
                                                "unexpected ExecutionResult: {}",
                                                item.ret_val
                                            ));
                                            diagnostics =
                                                error_recorder.record_error_diagnostic(&error, frame, shared_state);
                                            (status, "execute", Some(error.to_string()))
                                        } else {
                                            collected
                                                .lock()
                                                .expect("solve collector mutex poisoned")
                                                .cases
                                                .push(CollectedCase { path_signature: frame.path_signature(), item });
                                            (
                                                status,
                                                if status == "decode-rejected" { "decode" } else { "execute" },
                                                None,
                                            )
                                        }
                                    }
                                    Err(error) => {
                                        diagnostics =
                                            error_recorder.record_error_diagnostic(&error, frame, shared_state);
                                        ("materialization-error", "materialize", Some(error.to_string()))
                                    }
                                }
                            }
                        }
                    }
                }
                Ok((Run::Dead, _)) => ("unsat", phase_from_frame(frame, shared_state), Some("dead path".to_string())),
                Ok((Run::Exit, _)) => {
                    let error = ExecError::Unreachable("single instruction exited without ExecutionResult".to_string());
                    diagnostics = error_recorder.record_error_diagnostic(&error, frame, shared_state);
                    ("error", phase_from_frame(frame, shared_state), Some(error.to_string()))
                }
                Ok((Run::Suspended, _)) => {
                    let error = ExecError::Unreachable("single instruction suspended".to_string());
                    diagnostics = error_recorder.record_error_diagnostic(&error, frame, shared_state);
                    ("error", phase_from_frame(frame, shared_state), Some(error.to_string()))
                }
                Err((error, _)) => {
                    let encoder = shared_state.symtab.lookup("zencdec_forwards");
                    let requested_ctor = shared_state.symtab.lookup(instruction_name);
                    let encoder_rejection_site = encoder_rejection_pc(shared_state, requested_ctor);
                    let expected_encoder_rejection = mode == SolveEntryMode::FullEncoded32
                        && matches!(error, ExecError::MatchFailure(_))
                        && frame.function_name() == encoder
                        && encoder_rejection_site
                            .is_some_and(|(pc, source, _)| pc == frame.pc() && source == error.source_loc());
                    if expected_encoder_rejection {
                        let (_, _, arm_source) =
                            encoder_rejection_site.expect("已核准的 encoder rejection 必须有 arm source");
                        let witness = nonencodable_witness(target, shared_state, &fun_args[0], &mut solver);
                        let mut state = collected.lock().expect("solve collector mutex poisoned");
                        state.set_terminal_mapping_source(
                            case_id,
                            arm_source.location_string(shared_state.symtab.files()),
                        );
                        state.set_terminal_witness(case_id, witness);
                        ("non-encodable", "encode", Some(error.to_string()))
                    } else {
                        diagnostics = error_recorder.record_error_diagnostic(error, frame, shared_state);
                        let phase = phase_from_frame(frame, shared_state);
                        log!(
                            log::SYM_EXEC,
                            &format!(
                                "执行错误: {}({:?})[{}]; case-id={}; phase={}; backtrace={}",
                                error,
                                error,
                                error.source_loc().location_string(shared_state.symtab.files()),
                                case_id,
                                phase,
                                backtrace_string(frame.backtrace(), &shared_state.symtab)
                            )
                        );
                        ("error", phase, Some(error.to_string()))
                    }
                }
            };
            collected.lock().expect("solve collector mutex poisoned").finish_terminal(case_id, status, phase, detail);
            log!(
                log::PATH_RESULT,
                &format!(
                    "case-id={} clause={} status={} phase={} tid={} signature={}",
                    case_id,
                    instruction_name,
                    status,
                    phase,
                    thread,
                    frame.path_signature()
                )
            );
            isla_lib::executor::submit_itrace_for_local_frame_with_metadata(
                frame,
                shared_state,
                diagnostics,
                isla_lib::tracetool::ItraceTerminalMetadata {
                    scope: instruction_name.to_string(),
                    case_id,
                    status: status.to_string(),
                    phase: phase.to_string(),
                    path_signature: frame.path_signature(),
                },
            );
        },
        cp,
        num_threads,
        timeout,
        &task_state,
    );

    // 提取字符串结果
    let result_mutex = match Arc::try_unwrap(result) {
        Ok(result_mutex) => result_mutex,
        Err(_) => panic!("{} 执行结束后 result 收集器仍有共享引用", instruction_name),
    };
    let xlen_name_str = target.arch_pretty_name().to_string();
    let mut state = result_mutex.into_inner().expect("solve collector mutex poisoned");
    let quota = state.case_quota;
    let items = finalize_cases(state.cases, &quota);
    for item in &items {
        let terminal = state.terminals.get_mut((item.case_id - 1) as usize).expect("gen case-id 缺少 terminal");
        terminal.emitted = true;
    }
    let summary = SolveSummary::from_terminals(instruction_name, mode, target.domain_manifest(), &state.terminals);
    let complete = summary.complete;
    let json = AssemGenJson::new(items, summary, state.terminals);
    json.to_json(Some(format!("output/{}_{}.json", xlen_name_str, instruction_name)));
    match state.first_error {
        Some(error) => Err(error),
        None if complete => Ok(None),
        None => Err(ExecError::Unreachable(format!("{} terminal ledger is incomplete", instruction_name))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::bitvector::b129::B129;
    use isla_lib::bitvector::b64::B64;
    use isla_lib::config::{LimitBehaviorConfig, RegionForkLimitConfig};
    use isla_lib::executor::{LimitBehavior, SampleBias};
    use isla_lib::source_loc::SourceRegionSpec;
    use isla_lib::timeout::{SmtDumpNames, SmtDumpSource, SmtOperation, SmtTimeout, TimeoutSmtDump};
    use std::time::Duration;

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
    fn collector_keeps_non_timeout_execution_errors() {
        let mut state = SolveCollectorState::new();
        let failure = ExecError::AssertionFailure(Some("symbolic false arm".to_string()), SourceLoc::unknown());
        state.record_error(&failure);
        assert!(matches!(state.first_error, Some(ExecError::AssertionFailure(_, _))));
        state.record_error(&ExecError::Z3Unknown);
        assert!(matches!(state.first_error, Some(ExecError::AssertionFailure(_, _))));
    }

    #[test]
    fn terminal_ledger_retains_every_case_and_failure() {
        let mut state = SolveCollectorState::new();
        let first = state.begin_terminal(7, "zexecute".to_string(), "test.sail:1".to_string(), false);
        let second = state.begin_terminal(7, "zexecute".to_string(), "test.sail:2".to_string(), true);
        assert_ne!(first, second, "path signature 不保证绝对唯一，case-id 必须独立分配");
        state.finish_terminal(first, "retire", "execute", None);
        state.finish_terminal(second, "error", "execute", Some("assert failed".to_string()));
        let summary =
            SolveSummary::from_terminals("zTEST", SolveEntryMode::FullEncoded32, BTreeMap::new(), &state.terminals);
        assert_eq!(summary.total, 2);
        assert_eq!(summary.counts["retire"], 1);
        assert_eq!(summary.counts["error"], 1);
        assert!(!summary.complete);
        let json = serde_json::to_value(AssemGenJson::new(Vec::new(), summary, state.terminals)).unwrap();
        assert_eq!(json["terminals"][1]["case-id"], second);
        assert_eq!(json["summary"]["entry-mode"], "full-encoded-32");
    }

    #[test]
    fn official_float_list_is_the_only_full_encoded_domain() {
        let entries: Vec<_> = OFFICIAL_FLOAT_77.lines().collect();
        assert_eq!(entries.len(), 77);
        assert_eq!(entries.iter().collect::<HashSet<_>>().len(), 77);
        assert_eq!(SolveEntryMode::for_clause("zFLI_S"), SolveEntryMode::FullEncoded32);
        assert_eq!(SolveEntryMode::for_clause("zMRET"), SolveEntryMode::ConstructorDiagnostic);
    }

    #[test]
    fn solve_wrapper_short_circuits_sail_exceptions_at_each_stage() {
        let mut symtab = Symtab::new();
        for name in ["zencdec_forwards", "zext_decode", "zexecute", "zinstruction", "zExecutionResult"] {
            symtab.intern(name);
        }
        let mut defs: Vec<Def<Name, B64>> = Vec::new();
        install_solve_wrapper(&mut defs, &mut symtab);
        let Def::Fn(_, _, body) = &defs[1] else { panic!("wrapper body missing") };
        assert!(matches!(body[WRAPPER_ENCODE_PC], Instr::Call(_, false, _, _, _)));
        assert!(matches!(body[WRAPPER_DECODE_PC], Instr::Call(_, false, _, _, _)));
        assert!(matches!(body[WRAPPER_EXECUTE_PC], Instr::Call(_, false, _, _, _)));
        for (check_pc, handler_pc) in [(2, 9), (5, 10), (7, 11)] {
            assert!(matches!(body[check_pc], Instr::Jump(Exp::Id(HAVE_EXCEPTION), target, _) if target == handler_pc));
            assert!(matches!(body[handler_pc], Instr::Arbitrary));
        }
    }

    #[test]
    fn solve_wrapper_executes_encode_decode_execute_in_one_frame_and_stops_on_exception() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        for stage in ["encode", "decode", "normal"] {
            let mut symtab = Symtab::new();
            let instruction = symtab.intern("zinstruction");
            let result = symtab.intern("zExecutionResult");
            let test_ctor = symtab.intern("zTEST");
            let retire_ctor = symtab.intern("zRetire_Success");
            let encoder = symtab.intern("zencdec_forwards");
            let decoder = symtab.intern("zext_decode");
            let execute = symtab.intern("zexecute");
            let argument = symtab.intern("zargument");
            let register = symtab.intern("ztest_register");
            let location = SourceLoc::unknown();
            let mut encoder_body = Vec::new();
            if stage == "encode" {
                encoder_body.push(Instr::Copy(Loc::Id(HAVE_EXCEPTION), Exp::Bool(true), location));
            }
            encoder_body.push(Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(0x53, 32)), location));
            encoder_body.push(Instr::End);
            let mut decoder_body = Vec::new();
            if stage == "decode" {
                decoder_body.push(Instr::Copy(Loc::Id(HAVE_EXCEPTION), Exp::Bool(true), location));
            }
            decoder_body.push(Instr::Call(Loc::Id(RETURN), false, test_ctor, vec![Exp::Unit], location));
            decoder_body.push(Instr::End);
            let execute_body = if stage == "normal" {
                vec![
                    Instr::Copy(Loc::Id(register), Exp::Bits(B64::new(2, 8)), location),
                    Instr::Call(Loc::Id(RETURN), false, retire_ctor, vec![Exp::Unit], location),
                    Instr::End,
                ]
            } else {
                vec![Instr::Exit(ExitCause::AssertionFailure, location)]
            };
            let mut defs: Vec<Def<Name, B64>> = vec![
                Def::Register(register, Ty::Bits(8), vec![]),
                Def::Union(instruction, vec![(test_ctor, Ty::Unit)]),
                Def::Union(result, vec![(retire_ctor, Ty::Unit)]),
                Def::Val(encoder, vec![Ty::Union(instruction)], Ty::Bits(32)),
                Def::Fn(encoder, vec![argument], encoder_body),
                Def::Val(decoder, vec![Ty::Bits(32)], Ty::Union(instruction)),
                Def::Fn(decoder, vec![argument], decoder_body),
                Def::Val(execute, vec![Ty::Union(instruction)], Ty::Union(result)),
                Def::Fn(execute, vec![argument], execute_body),
            ];
            install_solve_wrapper(&mut defs, &mut symtab);
            let type_info = IRTypeInfo::new(&defs);
            let shared_state = SharedState::new(
                symtab,
                &defs,
                type_info,
                HashSet::new(),
                HashSet::new(),
                HashSet::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            );
            let observed = Mutex::new(Vec::new());
            let mut regs = RegisterBindings::new();
            regs.insert(register, false, UVal::Init(Val::Bits(B64::new(1, 8))));
            isla_lib::executor::execute_ir_function(
                SOLVE_WRAPPER,
                &[Val::Ctor(test_ctor, Box::new(Val::Unit))],
                &shared_state,
                &regs,
                &Bindings::default(),
                &observed,
                &|thread, task_id, result, callback_shared_state, solver, observed| {
                    let terminal = match result {
                        Ok((Run::Finished(value), frame)) => Ok((
                            value,
                            frame.pc(),
                            matches!(frame.lets().get(&HAVE_EXCEPTION), Some(UVal::Init(Val::Bool(true)))),
                            frame.regs().get_last_if_initialized(register).cloned(),
                        )),
                        Ok((_, _)) => Err("unexpected unfinished run".to_string()),
                        Err((error, _)) => Err(error.to_string()),
                    };
                    observed.lock().unwrap().push(terminal);
                },
            );
            let observed = observed.into_inner().unwrap();
            assert_eq!(observed.len(), 1, "{stage}");
            let (value, pc, exception, post_register) = observed.into_iter().next().unwrap().unwrap();
            match stage {
                "encode" => assert!(matches!(value, Val::Poison) && pc == 9 && exception),
                "decode" => assert!(matches!(value, Val::Poison) && pc == 10 && exception),
                "normal" => assert!(matches!(value, Val::Ctor(ctor, _) if ctor == retire_ctor) && !exception),
                _ => unreachable!(),
            }
            assert_eq!(post_register, Some(Val::Bits(B64::new(if stage == "normal" { 2 } else { 1 }, 8))));
        }
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
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
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
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
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
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
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
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
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
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
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

    fn collected_case(signature: u64, test_ins: &str, ret_val: &str) -> CollectedCase {
        CollectedCase {
            path_signature: signature,
            item: AssemGenJsonItem {
                arch: BTreeMap::new(),
                test_ins: test_ins.to_string(),
                test_ins_encdec: "32'h0000_0000".to_string(),
                isa_state: BTreeMap::new(),
                ret_val: ret_val.to_string(),
                case_id: signature,
                path_signature: signature,
                requested_instruction: String::new(),
                decoded_instruction: String::new(),
                entry_domain: "decoded".to_string(),
                isa_state_complete: BTreeMap::new(),
                isa_state_post: BTreeMap::new(),
            },
        }
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

    #[test]
    fn case_quota_tie_breaker_ignores_scheduler_case_id() {
        let quota = CaseQuota { per_class: BTreeMap::from([(String::from("Illegal_Instruction"), 1)]) };
        let mut first = collected_case(9, "vadd.vv v0, v1, v2", "Illegal_Instruction(())");
        first.item.isa_state_complete.insert("vtype".to_string(), "64'h1".to_string());
        let mut second = first.clone();
        second.item.isa_state_complete.insert("vtype".to_string(), "64'h2".to_string());
        first.item.case_id = 1;
        second.item.case_id = 2;
        let selected_a = finalize_cases(vec![first.clone(), second.clone()], &Some(quota.clone()));
        first.item.case_id = 2;
        second.item.case_id = 1;
        let selected_b = finalize_cases(vec![second, first], &Some(quota));
        assert_eq!(selected_a.len(), 1);
        assert_eq!(case_sort_key(&selected_a[0]), case_sort_key(&selected_b[0]));
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
