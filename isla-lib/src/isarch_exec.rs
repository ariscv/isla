use crate::bitvector::BV;
use crate::config::{AddressRange, ISAConfig, PageTablePreset, SymbolicMemoryConfig};
use crate::dprint::{self, colors};
use crate::error::{ExecError, IslaError};
use crate::executor::{backtrace_string, Backtrace, LocalFrame, RepeatLimitHit, Run, TaskId};
use crate::fmtval::FmtVal;
use crate::ir::UVal;
use crate::ir::*;
use crate::isarch::{self, get_assembly_name};
use crate::memory::Memory;
use crate::primop_util::symbolic;
use crate::register::RegisterBindings;
use crate::smt::{checkpoint, Config, Context, Event, Model, ModelVal};
use crate::smt::{Solver, Sym};
use crate::source_loc::SourceLoc;
use crate::zencode;
use crate::{dlog, log};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, HashSet};
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

const EQUIV_SUMMARY_SCHEMA_VERSION: u32 = 1;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum EquivalenceStatus {
    ProvedEquivalent,
    Mismatch,
    InconclusivePruned,
    ExecutionFailed,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SummaryAddressRange {
    pub base: u64,
    pub top: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TargetMemoryConfigSummary {
    pub ram_regions: Vec<SummaryAddressRange>,
    pub symbolic_regions: Vec<SummaryAddressRange>,
    pub page_table_preset: Option<String>,
    pub clint_enabled: bool,
    pub mmio_enabled: bool,
}

impl From<AddressRange> for SummaryAddressRange {
    fn from(range: AddressRange) -> Self {
        SummaryAddressRange { base: range.base, top: range.top }
    }
}

fn page_table_preset_name(preset: PageTablePreset) -> &'static str {
    match preset {
        PageTablePreset::Bare => "bare",
        PageTablePreset::Sv39 => "sv39",
        PageTablePreset::Sv48 => "sv48",
        PageTablePreset::Sv57 => "sv57",
    }
}

fn summarize_symbolic_memory_config(config: &SymbolicMemoryConfig) -> TargetMemoryConfigSummary {
    TargetMemoryConfigSummary {
        ram_regions: config.ram_regions.iter().copied().map(SummaryAddressRange::from).collect(),
        symbolic_regions: config.symbolic_regions.iter().copied().map(SummaryAddressRange::from).collect(),
        page_table_preset: Some(page_table_preset_name(config.page_table_preset).to_string()),
        clint_enabled: config.clint_enabled,
        mmio_enabled: config.mmio_enabled,
    }
}

fn build_symbolic_execute_memory<B: BV>(
    config: &SymbolicMemoryConfig,
) -> Result<(Memory<B>, TargetMemoryConfigSummary), ExecError> {
    let mut memory = Memory::new();
    for region in &config.ram_regions {
        memory.add_zero_region(region.base..region.top);
    }
    for region in &config.symbolic_regions {
        memory.add_symbolic_region(region.base..region.top);
    }

    Ok((memory, summarize_symbolic_memory_config(config)))
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct LinearizationStats {
    pub enabled: bool,
    pub attempted_functions: Vec<String>,
    pub succeeded_functions: Vec<String>,
    pub failed_functions: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct LimitStats {
    pub block_repeat_limit: Option<u64>,
    pub hit_limit: bool,
    pub pruned: bool,
    pub total_pruned_paths: u64,
    pub hits: Vec<LimitHitStats>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum FallbackPhase {
    LimitHit,
    LinearizationAttempted,
    LinearizationSucceeded,
    LinearizationFailed,
    Pruned,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct FallbackEvent {
    pub phase: FallbackPhase,
    pub related_function: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct FallbackStats {
    pub related_function: Option<String>,
    pub events: Vec<FallbackEvent>,
}

impl FallbackStats {
    pub fn from_limit_hit(hit: &RepeatLimitHit, linearization_succeeded: bool) -> Self {
        let related_function = hit.function.clone();
        let mut events = vec![
            FallbackEvent { phase: FallbackPhase::LimitHit, related_function: related_function.clone() },
            FallbackEvent { phase: FallbackPhase::LinearizationAttempted, related_function: related_function.clone() },
        ];

        if linearization_succeeded {
            events.push(FallbackEvent {
                phase: FallbackPhase::LinearizationSucceeded,
                related_function: related_function.clone(),
            });
        } else {
            events.push(FallbackEvent {
                phase: FallbackPhase::LinearizationFailed,
                related_function: related_function.clone(),
            });
            events.push(FallbackEvent { phase: FallbackPhase::Pruned, related_function: related_function.clone() });
        }

        FallbackStats { related_function: Some(related_function), events }
    }

    pub fn failed_status(&self) -> Option<EquivalenceStatus> {
        if self.events.iter().any(|event| event.phase == FallbackPhase::Pruned) {
            Some(EquivalenceStatus::InconclusivePruned)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct LimitHitStats {
    pub function: String,
    pub ir_pc: usize,
    pub arch_pc: Option<u64>,
    pub repeat_count: u64,
    pub configured_limit: u64,
    pub task_id: Option<usize>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct NormalizedBranchSummary {
    pub total_branches: u64,
    pub branch_signatures: Vec<String>,
    pub normalized_conditions: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct IsaStateDeltaSummary {
    pub changed: BTreeMap<String, String>,
    pub unchanged: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct MemAccessSummary {
    pub count: u64,
    pub summary: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct MemorySummary {
    pub reads: Vec<MemAccessSummary>,
    pub writes: Vec<MemAccessSummary>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum LoadExtensionSemantics {
    SignExtend,
    ZeroExtend,
    FullWidth,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct NormalLoadSummary {
    pub mnemonic: String,
    pub clause_id: String,
    pub bytes: u64,
    pub width_bits: u64,
    pub xlen_bits: u64,
    pub extension: LoadExtensionSemantics,
}

impl NormalLoadSummary {
    fn ret_val_metadata(&self) -> String {
        format!(
            "load:{} bytes={} width_bits={} xlen_bits={} extension={:?}",
            self.mnemonic, self.bytes, self.width_bits, self.xlen_bits, self.extension
        )
    }

    fn isa_state_delta_metadata(&self) -> String {
        format!("memory_read[{}] -> rd, width_bits={}, extension={:?}", self.mnemonic, self.width_bits, self.extension)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum StoreTruncationSemantics {
    ByteTruncate,
    HalfwordTruncate,
    WordTruncate,
    FullWidth,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct NormalStoreSummary {
    pub mnemonic: String,
    pub clause_id: String,
    pub bytes: u64,
    pub width_bits: u64,
    pub xlen_bits: u64,
    pub truncation: StoreTruncationSemantics,
}

impl NormalStoreSummary {
    fn ret_val_metadata(&self) -> String {
        format!(
            "store:{} bytes={} width_bits={} xlen_bits={} truncation={:?}",
            self.mnemonic, self.bytes, self.width_bits, self.xlen_bits, self.truncation
        )
    }

    fn isa_state_delta_metadata(&self) -> String {
        format!(
            "rs2 -> memory_write[{}], width_bits={}, truncation={:?}",
            self.mnemonic, self.width_bits, self.truncation
        )
    }
}

pub fn normal_rv64_load_summary(mnemonic: &str) -> Option<NormalLoadSummary> {
    let (bytes, width_bits, extension) = match mnemonic {
        "LB" => (1, 8, LoadExtensionSemantics::SignExtend),
        "LH" => (2, 16, LoadExtensionSemantics::SignExtend),
        "LW" => (4, 32, LoadExtensionSemantics::SignExtend),
        "LD" => (8, 64, LoadExtensionSemantics::FullWidth),
        "LBU" => (1, 8, LoadExtensionSemantics::ZeroExtend),
        "LHU" => (2, 16, LoadExtensionSemantics::ZeroExtend),
        "LWU" => (4, 32, LoadExtensionSemantics::ZeroExtend),
        _ => return None,
    };

    Some(NormalLoadSummary {
        mnemonic: mnemonic.to_string(),
        clause_id: "rv64d.zLOAD".to_string(),
        bytes,
        width_bits,
        xlen_bits: 64,
        extension,
    })
}

pub fn normal_rv64_load_mnemonics() -> [&'static str; 7] {
    ["LB", "LH", "LW", "LD", "LBU", "LHU", "LWU"]
}

pub fn normal_rv64_store_summary(mnemonic: &str) -> Option<NormalStoreSummary> {
    let (bytes, width_bits, truncation) = match mnemonic {
        "SB" => (1, 8, StoreTruncationSemantics::ByteTruncate),
        "SH" => (2, 16, StoreTruncationSemantics::HalfwordTruncate),
        "SW" => (4, 32, StoreTruncationSemantics::WordTruncate),
        "SD" => (8, 64, StoreTruncationSemantics::FullWidth),
        _ => return None,
    };

    Some(NormalStoreSummary {
        mnemonic: mnemonic.to_string(),
        clause_id: "rv64d.zSTORE".to_string(),
        bytes,
        width_bits,
        xlen_bits: 64,
        truncation,
    })
}

pub fn normal_rv64_store_mnemonics() -> [&'static str; 4] {
    ["SB", "SH", "SW", "SD"]
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryEvidenceStatus {
    pub required: bool,
    pub complete: bool,
    pub reason: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryTraceSummary {
    pub memory_summary: MemorySummary,
    pub evidence_status: MemoryEvidenceStatus,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum MemoryAccessKind {
    Load,
    Store,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct CompressedMemoryMapping {
    pub instruction: String,
    pub clause_id: String,
    pub base_mnemonic: String,
    pub access_kind: MemoryAccessKind,
}

pub fn compressed_rv64_memory_mapping(mnemonic: &str) -> Option<CompressedMemoryMapping> {
    let (base_mnemonic, access_kind, clause_id) = match mnemonic {
        "C.LW" | "C.LWSP" => ("LW", MemoryAccessKind::Load, "rv64d.zLOAD"),
        "C.LD" | "C.LDSP" => ("LD", MemoryAccessKind::Load, "rv64d.zLOAD"),
        "C.SW" | "C.SWSP" => ("SW", MemoryAccessKind::Store, "rv64d.zSTORE"),
        "C.SD" | "C.SDSP" => ("SD", MemoryAccessKind::Store, "rv64d.zSTORE"),
        _ => return None,
    };

    Some(CompressedMemoryMapping {
        instruction: mnemonic.to_string(),
        clause_id: clause_id.to_string(),
        base_mnemonic: base_mnemonic.to_string(),
        access_kind,
    })
}

pub fn compressed_rv64_memory_mnemonics() -> [&'static str; 8] {
    ["C.LW", "C.LD", "C.LWSP", "C.LDSP", "C.SW", "C.SD", "C.SWSP", "C.SDSP"]
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NormalizedExceptionStatus {
    pub exception_status: ExceptionStatus,
    pub clause_exception_matched: bool,
}

fn summarize_memory_val<B: BV>(val: &Val<B>, shared_state: Option<&SharedState<B>>) -> String {
    shared_state.map(|shared_state| val.to_string(shared_state)).unwrap_or_else(|| format!("{:?}", val))
}

pub fn summarize_memory_trace<B: BV>(
    events: &[Event<B>],
    shared_state: Option<&SharedState<B>>,
    memory_required: bool,
) -> MemoryTraceSummary {
    let mut reads = Vec::new();
    let mut writes = Vec::new();

    for event in events {
        match event {
            Event::ReadMem { value, read_kind, address, bytes, tag_value, region, .. } => {
                reads.push(MemAccessSummary {
                    count: 1,
                    summary: vec![
                        "kind=read".to_string(),
                        format!("address={}", summarize_memory_val(address, shared_state)),
                        format!("bytes={}", bytes),
                        format!("width_bits={}", bytes.saturating_mul(8)),
                        format!("value={}", summarize_memory_val(value, shared_state)),
                        format!("read_kind={}", summarize_memory_val(read_kind, shared_state)),
                        format!(
                            "tag={}",
                            tag_value
                                .as_ref()
                                .map(|tag| summarize_memory_val(tag, shared_state))
                                .unwrap_or_else(|| "unavailable".to_string())
                        ),
                        format!("region={}", region),
                        format!("exclusive={}", event.is_exclusive()),
                        format!("ifetch={}", event.is_ifetch()),
                        "guard=unavailable".to_string(),
                        "path=unavailable".to_string(),
                        "status=observed".to_string(),
                    ],
                });
            }
            Event::WriteMem { value, write_kind, address, data, bytes, tag_value, region, .. } => {
                writes.push(MemAccessSummary {
                    count: 1,
                    summary: vec![
                        "kind=write".to_string(),
                        format!("address={}", summarize_memory_val(address, shared_state)),
                        format!("bytes={}", bytes),
                        format!("width_bits={}", bytes.saturating_mul(8)),
                        format!("data={}", summarize_memory_val(data, shared_state)),
                        format!("write_kind={}", summarize_memory_val(write_kind, shared_state)),
                        format!("write_status_symbol=v{}", value),
                        format!(
                            "tag={}",
                            tag_value
                                .as_ref()
                                .map(|tag| summarize_memory_val(tag, shared_state))
                                .unwrap_or_else(|| "unavailable".to_string())
                        ),
                        format!("region={}", region),
                        format!("exclusive={}", event.is_exclusive()),
                        "guard=unavailable".to_string(),
                        "path=unavailable".to_string(),
                        "status=observed".to_string(),
                    ],
                });
            }
            _ => {}
        }
    }

    let missing_required_memory = memory_required && reads.is_empty() && writes.is_empty();
    let evidence_status = if missing_required_memory {
        MemoryEvidenceStatus {
            required: true,
            complete: false,
            reason: Some("required_memory_evidence_missing".to_string()),
        }
    } else {
        MemoryEvidenceStatus { required: memory_required, complete: true, reason: None }
    };

    MemoryTraceSummary { memory_summary: MemorySummary { reads, writes }, evidence_status }
}

pub fn equivalence_status_with_memory_evidence(
    requested_status: EquivalenceStatus,
    evidence_status: &MemoryEvidenceStatus,
) -> EquivalenceStatus {
    if requested_status == EquivalenceStatus::ProvedEquivalent && !evidence_status.complete {
        EquivalenceStatus::InconclusivePruned
    } else {
        requested_status
    }
}

fn summary_field<'a>(summary: &'a MemAccessSummary, prefix: &str) -> Option<&'a str> {
    summary.summary.iter().find_map(|field| field.strip_prefix(prefix))
}

fn summary_has_status(summary: &MemAccessSummary, status: &str) -> bool {
    summary_field(summary, "status=") == Some(status) || summary.summary.iter().any(|field| field == status)
}

fn parse_summary_address(summary: &MemAccessSummary) -> Option<u64> {
    let address = summary_field(summary, "address=")?.trim();
    let hex =
        address.strip_prefix("0x").or_else(|| address.strip_prefix("#x")).or_else(|| address.strip_prefix("#X"))?;
    u64::from_str_radix(hex, 16).ok()
}

fn summary_address_is_symbolic(summary: &MemAccessSummary) -> bool {
    summary_field(summary, "address=")
        .map(|address| {
            let address = address.to_ascii_lowercase();
            address.contains("symbolic") || address.contains("sym") || address.contains("unresolved")
        })
        .unwrap_or(false)
}

fn address_in_configured_memory(address: u64, target_memory_config: &TargetMemoryConfigSummary) -> Option<bool> {
    if target_memory_config.ram_regions.is_empty() && target_memory_config.symbolic_regions.is_empty() {
        return None;
    }

    let in_range = target_memory_config
        .ram_regions
        .iter()
        .chain(target_memory_config.symbolic_regions.iter())
        .any(|range| address >= range.base && address < range.top);
    Some(in_range)
}

fn normalize_access_exception_status(
    access: Option<&MemAccessSummary>,
    expected_bytes: Option<u64>,
    target_memory_config: &TargetMemoryConfigSummary,
) -> NormalizedExceptionStatus {
    let Some(access) = access else {
        return NormalizedExceptionStatus {
            exception_status: ExceptionStatus {
                exception: Some("unresolved_symbolic_address".to_string()),
                alignment: None,
            },
            clause_exception_matched: false,
        };
    };

    let clause_exception_matched = summary_has_status(access, "clause_exception_matched")
        || access.summary.contains(&"clause_exception_matched=true".to_string());

    for category in ["misaligned", "out_of_range", "mmio_disabled", "unresolved_symbolic_address"] {
        if summary_has_status(access, category) || access.summary.contains(&format!("exception={}", category)) {
            return NormalizedExceptionStatus {
                exception_status: ExceptionStatus {
                    exception: Some(category.to_string()),
                    alignment: Some(category == "misaligned"),
                },
                clause_exception_matched,
            };
        }
    }

    if summary_address_is_symbolic(access) {
        return NormalizedExceptionStatus {
            exception_status: ExceptionStatus {
                exception: Some("unresolved_symbolic_address".to_string()),
                alignment: None,
            },
            clause_exception_matched,
        };
    }

    if summary_field(access, "region=").map(|region| region.eq_ignore_ascii_case("mmio")).unwrap_or(false)
        && !target_memory_config.mmio_enabled
    {
        return NormalizedExceptionStatus {
            exception_status: ExceptionStatus { exception: Some("mmio_disabled".to_string()), alignment: None },
            clause_exception_matched,
        };
    }

    if let Some(address) = parse_summary_address(access) {
        if address_in_configured_memory(address, target_memory_config) == Some(false) {
            return NormalizedExceptionStatus {
                exception_status: ExceptionStatus { exception: Some("out_of_range".to_string()), alignment: None },
                clause_exception_matched,
            };
        }

        if let Some(bytes) = expected_bytes {
            if bytes > 1 && address % bytes != 0 {
                return NormalizedExceptionStatus {
                    exception_status: ExceptionStatus {
                        exception: Some("misaligned".to_string()),
                        alignment: Some(true),
                    },
                    clause_exception_matched,
                };
            }

            if bytes == 1 {
                return NormalizedExceptionStatus {
                    exception_status: ExceptionStatus { exception: None, alignment: Some(false) },
                    clause_exception_matched,
                };
            }
        }
    }

    NormalizedExceptionStatus {
        exception_status: ExceptionStatus { exception: None, alignment: Some(false) },
        clause_exception_matched,
    }
}

pub fn load_store_exception_status(
    kind: MemoryAccessKind,
    mnemonic: &str,
    memory_summary: &MemorySummary,
    target_memory_config: &TargetMemoryConfigSummary,
) -> NormalizedExceptionStatus {
    let expected_bytes = match kind {
        MemoryAccessKind::Load => normal_rv64_load_summary(mnemonic).map(|summary| summary.bytes),
        MemoryAccessKind::Store => normal_rv64_store_summary(mnemonic).map(|summary| summary.bytes),
    };
    let access = match kind {
        MemoryAccessKind::Load => memory_summary.reads.first(),
        MemoryAccessKind::Store => memory_summary.writes.first(),
    };

    normalize_access_exception_status(access, expected_bytes, target_memory_config)
}

pub fn equivalence_status_with_exception_status(
    requested_status: EquivalenceStatus,
    normalized_exception_status: &NormalizedExceptionStatus,
) -> EquivalenceStatus {
    if requested_status == EquivalenceStatus::ProvedEquivalent
        && normalized_exception_status.exception_status.exception.is_some()
        && !normalized_exception_status.clause_exception_matched
    {
        EquivalenceStatus::InconclusivePruned
    } else {
        requested_status
    }
}

pub fn load_memory_evidence_status(mnemonic: &str, memory_summary: &MemorySummary) -> MemoryEvidenceStatus {
    let Some(load_summary) = normal_rv64_load_summary(mnemonic) else {
        return MemoryEvidenceStatus {
            required: true,
            complete: false,
            reason: Some("unsupported_load_instruction".to_string()),
        };
    };

    if memory_summary.reads.is_empty() {
        return MemoryEvidenceStatus {
            required: true,
            complete: false,
            reason: Some("required_load_readmem_evidence_missing".to_string()),
        };
    }

    let expected_bytes = format!("bytes={}", load_summary.bytes);
    let expected_width = format!("width_bits={}", load_summary.width_bits);
    let has_matching_read = memory_summary.reads.iter().any(|read| {
        read.summary.contains(&"kind=read".to_string())
            && read.summary.contains(&expected_bytes)
            && read.summary.contains(&expected_width)
            && read.summary.contains(&"status=observed".to_string())
    });

    if has_matching_read {
        MemoryEvidenceStatus { required: true, complete: true, reason: None }
    } else {
        MemoryEvidenceStatus {
            required: true,
            complete: false,
            reason: Some("required_load_readmem_width_mismatch".to_string()),
        }
    }
}

pub fn store_memory_evidence_status(mnemonic: &str, memory_summary: &MemorySummary) -> MemoryEvidenceStatus {
    let Some(store_summary) = normal_rv64_store_summary(mnemonic) else {
        return MemoryEvidenceStatus {
            required: true,
            complete: false,
            reason: Some("unsupported_store_instruction".to_string()),
        };
    };

    if memory_summary.writes.is_empty() {
        return MemoryEvidenceStatus {
            required: true,
            complete: false,
            reason: Some("required_store_writemem_evidence_missing".to_string()),
        };
    }

    let expected_bytes = format!("bytes={}", store_summary.bytes);
    let expected_width = format!("width_bits={}", store_summary.width_bits);
    let has_matching_write = memory_summary.writes.iter().any(|write| {
        write.summary.contains(&"kind=write".to_string())
            && write.summary.contains(&expected_bytes)
            && write.summary.contains(&expected_width)
            && write.summary.contains(&"status=observed".to_string())
    });

    if has_matching_write {
        MemoryEvidenceStatus { required: true, complete: true, reason: None }
    } else {
        MemoryEvidenceStatus {
            required: true,
            complete: false,
            reason: Some("required_store_writemem_width_mismatch".to_string()),
        }
    }
}

pub fn normal_rv64_load_equiv_summary(
    mnemonic: &str,
    target_memory_config: TargetMemoryConfigSummary,
    memory_summary: MemorySummary,
    requested_status: EquivalenceStatus,
) -> EquivSummaryJsonItem {
    let load_summary = normal_rv64_load_summary(mnemonic).unwrap_or_else(|| NormalLoadSummary {
        mnemonic: mnemonic.to_string(),
        clause_id: "unavailable".to_string(),
        bytes: 0,
        width_bits: 0,
        xlen_bits: 64,
        extension: LoadExtensionSemantics::FullWidth,
    });
    let evidence_status = load_memory_evidence_status(mnemonic, &memory_summary);
    let normalized_exception_status =
        load_store_exception_status(MemoryAccessKind::Load, mnemonic, &memory_summary, &target_memory_config);
    let equivalence_status = equivalence_status_with_exception_status(
        equivalence_status_with_memory_evidence(requested_status, &evidence_status),
        &normalized_exception_status,
    );
    let extension_metadata = format!("extension={:?}", load_summary.extension);

    EquivSummaryJsonItem::new(
        load_summary.mnemonic.clone(),
        load_summary.clause_id.clone(),
        target_memory_config,
        LinearizationStats {
            enabled: false,
            attempted_functions: vec![],
            succeeded_functions: vec![],
            failed_functions: vec![],
        },
        LimitStats { block_repeat_limit: None, hit_limit: false, pruned: false, total_pruned_paths: 0, hits: vec![] },
        None,
        NormalizedBranchSummary { total_branches: 0, branch_signatures: vec![], normalized_conditions: vec![] },
        IsaStateDeltaSummary {
            changed: BTreeMap::from([(
                "rd".to_string(),
                format!(
                    "{}; bytes={}; width_bits={}; {}",
                    load_summary.isa_state_delta_metadata(),
                    load_summary.bytes,
                    load_summary.width_bits,
                    extension_metadata
                ),
            )]),
            unchanged: vec![],
        },
        format!(
            "{}; bytes={}; width_bits={}; {}",
            load_summary.ret_val_metadata(),
            load_summary.bytes,
            load_summary.width_bits,
            extension_metadata
        ),
        memory_summary,
        normalized_exception_status.exception_status,
        equivalence_status,
    )
}

pub fn compressed_rv64_memory_equiv_summary(
    mnemonic: &str,
    target_memory_config: TargetMemoryConfigSummary,
    memory_summary: MemorySummary,
    requested_status: EquivalenceStatus,
) -> EquivSummaryJsonItem {
    let Some(mapping) = compressed_rv64_memory_mapping(mnemonic) else {
        return EquivSummaryJsonItem::new(
            mnemonic.to_string(),
            "unavailable".to_string(),
            target_memory_config,
            LinearizationStats {
                enabled: false,
                attempted_functions: vec![],
                succeeded_functions: vec![],
                failed_functions: vec![],
            },
            LimitStats {
                block_repeat_limit: None,
                hit_limit: false,
                pruned: false,
                total_pruned_paths: 0,
                hits: vec![],
            },
            None,
            NormalizedBranchSummary { total_branches: 0, branch_signatures: vec![], normalized_conditions: vec![] },
            IsaStateDeltaSummary { changed: BTreeMap::new(), unchanged: vec![] },
            "missing_compressed_clause_mapping".to_string(),
            memory_summary,
            ExceptionStatus { exception: Some("missing_compressed_clause_mapping".to_string()), alignment: None },
            equivalence_status_with_memory_evidence(
                requested_status,
                &MemoryEvidenceStatus {
                    required: true,
                    complete: false,
                    reason: Some("missing_compressed_clause_mapping".to_string()),
                },
            ),
        );
    };

    match mapping.access_kind {
        MemoryAccessKind::Load => {
            let mut summary = normal_rv64_load_equiv_summary(
                &mapping.base_mnemonic,
                target_memory_config,
                memory_summary,
                requested_status,
            );
            summary.instruction = mapping.instruction.clone();
            summary.clause_id = mapping.clause_id.clone();
            summary.ret_val = format!(
                "compressed_instruction={} maps_to={} clause_id={}; {}",
                mapping.instruction, mapping.base_mnemonic, mapping.clause_id, summary.ret_val
            );
            summary.isa_state_delta.changed.insert(
                "compressed_mapping".to_string(),
                format!(
                    "compressed_instruction={} maps_to={} clause_id={} access_kind=load",
                    mapping.instruction, mapping.base_mnemonic, mapping.clause_id
                ),
            );
            summary
        }
        MemoryAccessKind::Store => {
            let mut summary = normal_rv64_store_equiv_summary(
                &mapping.base_mnemonic,
                target_memory_config,
                memory_summary,
                requested_status,
            );
            summary.instruction = mapping.instruction.clone();
            summary.clause_id = mapping.clause_id.clone();
            summary.ret_val = format!(
                "compressed_instruction={} maps_to={} clause_id={}; {}",
                mapping.instruction, mapping.base_mnemonic, mapping.clause_id, summary.ret_val
            );
            summary.isa_state_delta.changed.insert(
                "compressed_mapping".to_string(),
                format!(
                    "compressed_instruction={} maps_to={} clause_id={} access_kind=store",
                    mapping.instruction, mapping.base_mnemonic, mapping.clause_id
                ),
            );
            summary
        }
    }
}

pub fn normal_rv64_store_equiv_summary(
    mnemonic: &str,
    target_memory_config: TargetMemoryConfigSummary,
    memory_summary: MemorySummary,
    requested_status: EquivalenceStatus,
) -> EquivSummaryJsonItem {
    let store_summary = normal_rv64_store_summary(mnemonic).unwrap_or_else(|| NormalStoreSummary {
        mnemonic: mnemonic.to_string(),
        clause_id: "unavailable".to_string(),
        bytes: 0,
        width_bits: 0,
        xlen_bits: 64,
        truncation: StoreTruncationSemantics::FullWidth,
    });
    let evidence_status = store_memory_evidence_status(mnemonic, &memory_summary);
    let normalized_exception_status =
        load_store_exception_status(MemoryAccessKind::Store, mnemonic, &memory_summary, &target_memory_config);
    let equivalence_status = equivalence_status_with_exception_status(
        equivalence_status_with_memory_evidence(requested_status, &evidence_status),
        &normalized_exception_status,
    );
    let truncation_metadata = format!("truncation={:?}", store_summary.truncation);

    EquivSummaryJsonItem::new(
        store_summary.mnemonic.clone(),
        store_summary.clause_id.clone(),
        target_memory_config,
        LinearizationStats {
            enabled: false,
            attempted_functions: vec![],
            succeeded_functions: vec![],
            failed_functions: vec![],
        },
        LimitStats { block_repeat_limit: None, hit_limit: false, pruned: false, total_pruned_paths: 0, hits: vec![] },
        None,
        NormalizedBranchSummary { total_branches: 0, branch_signatures: vec![], normalized_conditions: vec![] },
        IsaStateDeltaSummary {
            changed: BTreeMap::from([(
                "memory".to_string(),
                format!(
                    "{}; bytes={}; width_bits={}; {}",
                    store_summary.isa_state_delta_metadata(),
                    store_summary.bytes,
                    store_summary.width_bits,
                    truncation_metadata
                ),
            )]),
            unchanged: vec![],
        },
        format!(
            "{}; bytes={}; width_bits={}; {}",
            store_summary.ret_val_metadata(),
            store_summary.bytes,
            store_summary.width_bits,
            truncation_metadata
        ),
        memory_summary,
        normalized_exception_status.exception_status,
        equivalence_status,
    )
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ExceptionStatus {
    pub exception: Option<String>,
    pub alignment: Option<bool>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct EquivSummaryJsonItem {
    pub schema_version: u32,
    pub instruction: String,
    pub clause_id: String,
    pub target_memory_config: TargetMemoryConfigSummary,
    pub linearization_stats: LinearizationStats,
    pub limit_stats: LimitStats,
    pub fallback_stats: Option<FallbackStats>,
    pub normalized_branch_summary: NormalizedBranchSummary,
    pub isa_state_delta: IsaStateDeltaSummary,
    pub ret_val: String,
    pub memory_summary: MemorySummary,
    pub exception_status: ExceptionStatus,
    pub equivalence_status: EquivalenceStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct EquivSummaryJson {
    pub summaries: Vec<EquivSummaryJsonItem>,
}

impl ToJSON for EquivSummaryJson {}

impl EquivSummaryJsonItem {
    pub fn new(
        instruction: String,
        clause_id: String,
        target_memory_config: TargetMemoryConfigSummary,
        linearization_stats: LinearizationStats,
        limit_stats: LimitStats,
        fallback_stats: Option<FallbackStats>,
        normalized_branch_summary: NormalizedBranchSummary,
        isa_state_delta: IsaStateDeltaSummary,
        ret_val: String,
        memory_summary: MemorySummary,
        exception_status: ExceptionStatus,
        equivalence_status: EquivalenceStatus,
    ) -> Self {
        Self {
            schema_version: EQUIV_SUMMARY_SCHEMA_VERSION,
            instruction,
            clause_id,
            target_memory_config,
            linearization_stats,
            limit_stats,
            fallback_stats,
            normalized_branch_summary,
            isa_state_delta,
            ret_val,
            memory_summary,
            exception_status,
            equivalence_status,
        }
    }
}

impl EquivSummaryJson {
    pub fn new(summaries: Vec<EquivSummaryJsonItem>) -> Self {
        Self { summaries }
    }
}

fn summary_has_incomplete_memory_evidence(summary: &EquivSummaryJsonItem) -> bool {
    summary.memory_summary.reads.iter().chain(summary.memory_summary.writes.iter()).any(|access| {
        access.summary.iter().any(|field| {
            matches!(
                field.as_str(),
                "status=unresolved_symbolic_address"
                    | "status=required_memory_evidence_missing"
                    | "status=required_load_readmem_evidence_missing"
                    | "status=required_store_writemem_evidence_missing"
                    | "required_memory_evidence_missing"
                    | "required_load_readmem_evidence_missing"
                    | "required_store_writemem_evidence_missing"
                    | "unresolved_symbolic_address"
            ) || field.contains("required_memory_evidence_missing")
                || field.contains("required_load_readmem_evidence_missing")
                || field.contains("required_store_writemem_evidence_missing")
                || field.contains("unresolved_symbolic_address")
                || field.contains("unresolved_symbolic_memory")
        })
    })
}

fn summary_has_fail_closed_diagnostic(summary: &EquivSummaryJsonItem) -> bool {
    summary.clause_id == "unavailable"
        || summary.ret_val == "missing_compressed_clause_mapping"
        || summary.ret_val.contains("missing_compressed_clause_mapping")
        || summary.ret_val.contains("normalization_failure")
        || summary.ret_val.contains("normalization_failed")
        || summary.exception_status.exception.as_deref() == Some("missing_compressed_clause_mapping")
        || summary.exception_status.exception.as_deref() == Some("unresolved_symbolic_address")
        || summary.exception_status.exception.as_deref() == Some("unresolved_symbolic_memory")
        || summary_has_incomplete_memory_evidence(summary)
}

fn summary_is_pruned_or_unresolved(summary: &EquivSummaryJsonItem) -> bool {
    summary.equivalence_status == EquivalenceStatus::InconclusivePruned
        || summary.limit_stats.pruned
        || summary.limit_stats.hit_limit
        || summary.limit_stats.total_pruned_paths > 0
        || !summary.limit_stats.hits.is_empty()
        || summary.fallback_stats.as_ref().and_then(FallbackStats::failed_status).is_some()
        || !summary.linearization_stats.failed_functions.is_empty()
        || summary_has_fail_closed_diagnostic(summary)
}

fn summaries_have_semantic_mismatch(expected: &EquivSummaryJsonItem, actual: &EquivSummaryJsonItem) -> bool {
    expected.instruction != actual.instruction
        || expected.clause_id != actual.clause_id
        || expected.normalized_branch_summary != actual.normalized_branch_summary
        || expected.isa_state_delta != actual.isa_state_delta
        || expected.ret_val != actual.ret_val
        || expected.memory_summary != actual.memory_summary
        || expected.exception_status != actual.exception_status
        || expected.linearization_stats != actual.linearization_stats
        || expected.limit_stats != actual.limit_stats
        || expected.fallback_stats != actual.fallback_stats
}

pub fn compare_equiv_summaries(expected: &EquivSummaryJsonItem, actual: &EquivSummaryJsonItem) -> EquivalenceStatus {
    if expected.equivalence_status == EquivalenceStatus::ExecutionFailed
        || actual.equivalence_status == EquivalenceStatus::ExecutionFailed
    {
        return EquivalenceStatus::ExecutionFailed;
    }

    if summaries_have_semantic_mismatch(expected, actual) {
        return EquivalenceStatus::Mismatch;
    }

    if summary_is_pruned_or_unresolved(expected) || summary_is_pruned_or_unresolved(actual) {
        return EquivalenceStatus::InconclusivePruned;
    }

    EquivalenceStatus::ProvedEquivalent
}

fn normalize_summary_filename_component(component: &str) -> String {
    let mut normalized = String::with_capacity(component.len());
    let mut prev_underscore = false;

    for ch in component.chars() {
        let mapped = if ch.is_ascii_alphanumeric() { ch.to_ascii_lowercase() } else { '_' };

        if mapped == '_' {
            if prev_underscore {
                continue;
            }
            prev_underscore = true;
        } else {
            prev_underscore = false;
        }

        normalized.push(mapped);
    }

    normalized.trim_matches('_').to_string()
}

pub fn equiv_summary_output_path(xlen_name: &str, instruction_name: &str) -> String {
    let xlen_component = normalize_summary_filename_component(xlen_name);
    let instruction_component = normalize_summary_filename_component(instruction_name);
    let instruction_component =
        if instruction_component.is_empty() { "unknown".to_string() } else { instruction_component };

    format!("output/{}_{}.equiv.json", xlen_component, instruction_component)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equiv_summary_output_path_is_deterministic() {
        assert_eq!(equiv_summary_output_path("rv64d", "LD"), "output/rv64d_ld.equiv.json");
        assert_eq!(equiv_summary_output_path("rv64d", "C.LWSP"), "output/rv64d_c_lwsp.equiv.json");
        assert_eq!(equiv_summary_output_path("RV64D", "C.SDSP/../../tmp"), "output/rv64d_c_sdsp_tmp.equiv.json");
    }

    #[test]
    fn equiv_summary_schema_requires_equivalence_status() {
        let summary = EquivSummaryJsonItem::new(
            "zload".to_string(),
            "rv64d.zload.clause0".to_string(),
            TargetMemoryConfigSummary {
                ram_regions: vec![SummaryAddressRange { base: 0x1000, top: 0x2000 }],
                symbolic_regions: vec![SummaryAddressRange { base: 0x3000, top: 0x4000 }],
                page_table_preset: Some("sv39".to_string()),
                clint_enabled: true,
                mmio_enabled: false,
            },
            LinearizationStats {
                enabled: true,
                attempted_functions: vec!["zLOAD".to_string()],
                succeeded_functions: vec!["zLOAD".to_string()],
                failed_functions: vec![],
            },
            LimitStats {
                block_repeat_limit: Some(8),
                hit_limit: false,
                pruned: false,
                total_pruned_paths: 0,
                hits: vec![],
            },
            None,
            NormalizedBranchSummary {
                total_branches: 1,
                branch_signatures: vec!["branch0".to_string()],
                normalized_conditions: vec!["x1 == x2".to_string()],
            },
            IsaStateDeltaSummary {
                changed: BTreeMap::from([(String::from("x1"), String::from("0x1"))]),
                unchanged: vec!["x2".to_string()],
            },
            "ret".to_string(),
            MemorySummary {
                reads: vec![MemAccessSummary { count: 1, summary: vec!["read@0x1000".to_string()] }],
                writes: vec![MemAccessSummary { count: 1, summary: vec!["write@0x1004".to_string()] }],
            },
            ExceptionStatus { exception: None, alignment: Some(false) },
            EquivalenceStatus::ProvedEquivalent,
        );
        let json = serde_json::to_string(&summary).unwrap();
        assert!(json.contains("\"equivalence_status\":\"proved_equivalent\""));
        assert!(json.contains("\"instruction\":\"zload\""));
        assert!(json.contains("\"clause_id\":\"rv64d.zload.clause0\""));
        assert!(json.contains("\"memory_summary\""));
        assert!(json.contains("\"reads\""));
        assert!(json.contains("\"writes\""));
        assert!(json.contains("\"exception_status\""));
        assert!(json.contains("\"alignment\":false"));

        let missing_equivalence_status = r#"{
            "schema_version":1,
            "instruction":"zload",
            "clause_id":"rv64d.zload.clause0",
            "target_memory_config":{
                "ram_regions":[{"base":4096,"top":8192}],
                "symbolic_regions":[{"base":12288,"top":16384}],
                "page_table_preset":"sv39",
                "clint_enabled":true,
                "mmio_enabled":false
            },
            "linearization_stats":{
                "enabled":true,
                "attempted_functions":["zLOAD"],
                "succeeded_functions":["zLOAD"],
                "failed_functions":[]
            },
            "limit_stats":{
                "block_repeat_limit":8,
                "hit_limit":false,
                "pruned":false,
                "total_pruned_paths":0,
                "hits":[]
            },
            "fallback_stats":null,
            "normalized_branch_summary":{
                "total_branches":1,
                "branch_signatures":["branch0"],
                "normalized_conditions":["x1 == x2"]
            },
            "isa_state_delta":{
                "changed":{"x1":"0x1"},
                "unchanged":["x2"]
            },
            "ret_val":"ret",
            "memory_summary":{
                "reads":[{"count":1,"summary":["read@0x1000"]}],
                "writes":[{"count":1,"summary":["write@0x1004"]}]
            },
            "exception_status":{"exception":null,"alignment":false}
        }"#;
        let err = serde_json::from_str::<EquivSummaryJsonItem>(missing_equivalence_status).unwrap_err();
        assert!(err.to_string().contains("equivalence_status"));
    }

    #[test]
    fn equivalence_status_variants_round_trip() {
        let variants = [
            (EquivalenceStatus::ProvedEquivalent, "proved_equivalent"),
            (EquivalenceStatus::Mismatch, "mismatch"),
            (EquivalenceStatus::InconclusivePruned, "inconclusive_pruned"),
            (EquivalenceStatus::ExecutionFailed, "execution_failed"),
        ];

        for (status, expected) in variants {
            let json = serde_json::to_string(&status).unwrap();
            assert_eq!(json, format!("\"{}\"", expected));
            let decoded: EquivalenceStatus = serde_json::from_str(&json).unwrap();
            assert_eq!(decoded, status);
        }

        for disallowed in ["pass", "failed", "unknown", "proved-equivalent"] {
            assert!(serde_json::from_str::<EquivalenceStatus>(&format!("\"{}\"", disallowed)).is_err());
        }
    }

    fn assert_required_equiv_summary_fields(summary: &EquivSummaryJsonItem) {
        let json = serde_json::to_value(summary).unwrap();
        let object = json.as_object().unwrap();
        for field in [
            "schema_version",
            "instruction",
            "clause_id",
            "target_memory_config",
            "linearization_stats",
            "limit_stats",
            "fallback_stats",
            "normalized_branch_summary",
            "isa_state_delta",
            "ret_val",
            "memory_summary",
            "exception_status",
            "equivalence_status",
        ] {
            assert!(object.contains_key(field), "missing required field {field}");
        }

        assert!(json["schema_version"].is_u64());
        assert!(json["instruction"].is_string());
        assert!(json["clause_id"].is_string());
        assert!(json["target_memory_config"].is_object());
        assert!(json["linearization_stats"].is_object());
        assert!(json["limit_stats"].is_object());
        assert!(json["fallback_stats"].is_null() || json["fallback_stats"].is_object());
        assert!(json["normalized_branch_summary"].is_object());
        assert!(json["isa_state_delta"].is_object());
        assert!(json["ret_val"].is_string());
        assert!(json["memory_summary"].is_object());
        assert!(json["memory_summary"]["reads"].is_array());
        assert!(json["memory_summary"]["writes"].is_array());
        assert!(json["exception_status"].is_object());
        assert!(json["equivalence_status"].is_string());

        assert!(matches!(
            json["equivalence_status"].as_str().unwrap(),
            "proved_equivalent" | "mismatch" | "inconclusive_pruned" | "execution_failed"
        ));
        serde_json::from_value::<EquivSummaryJsonItem>(json).unwrap();
    }

    fn assert_missing_required_field_fails(summary: &EquivSummaryJsonItem, field: &str) {
        let mut json = serde_json::to_value(summary).unwrap();
        json.as_object_mut().unwrap().remove(field).unwrap();
        let err = serde_json::from_value::<EquivSummaryJsonItem>(json).unwrap_err();
        assert!(err.to_string().contains(field), "{err}");
    }

    #[test]
    fn equiv_summary_required_fields_cover_load_store_exception_compressed_and_non_pass() {
        let normal_load = normal_rv64_load_equiv_summary(
            "LD",
            empty_target_memory_config(),
            load_read_memory_summary(8),
            EquivalenceStatus::ProvedEquivalent,
        );
        let normal_store = normal_rv64_store_equiv_summary(
            "SD",
            empty_target_memory_config(),
            store_write_memory_summary(8),
            EquivalenceStatus::ProvedEquivalent,
        );
        let alignment_exception = normal_rv64_load_equiv_summary(
            "LD",
            empty_target_memory_config(),
            load_read_memory_summary_at(0x8000_0004, 8),
            EquivalenceStatus::ProvedEquivalent,
        );
        let compressed_mapping = compressed_rv64_memory_equiv_summary(
            "C.LWSP",
            empty_target_memory_config(),
            load_read_memory_summary(4),
            EquivalenceStatus::ProvedEquivalent,
        );
        let non_pass_missing_mapping = compressed_rv64_memory_equiv_summary(
            "C.UNKNOWN",
            empty_target_memory_config(),
            MemorySummary { reads: vec![], writes: vec![] },
            EquivalenceStatus::ProvedEquivalent,
        );
        let non_pass_execution_failed = normal_rv64_store_equiv_summary(
            "SD",
            empty_target_memory_config(),
            store_write_memory_summary(8),
            EquivalenceStatus::ExecutionFailed,
        );
        let mut mismatch = normal_load.clone();
        mismatch.equivalence_status = EquivalenceStatus::Mismatch;

        for summary in [
            &normal_load,
            &normal_store,
            &alignment_exception,
            &compressed_mapping,
            &non_pass_missing_mapping,
            &non_pass_execution_failed,
            &mismatch,
        ] {
            assert_required_equiv_summary_fields(summary);
        }

        assert_eq!(normal_load.equivalence_status, EquivalenceStatus::ProvedEquivalent);
        assert_eq!(normal_store.equivalence_status, EquivalenceStatus::ProvedEquivalent);
        assert_eq!(alignment_exception.exception_status.exception, Some("misaligned".to_string()));
        assert_eq!(alignment_exception.equivalence_status, EquivalenceStatus::InconclusivePruned);
        assert!(compressed_mapping.isa_state_delta.changed.contains_key("compressed_mapping"));
        assert_eq!(non_pass_missing_mapping.equivalence_status, EquivalenceStatus::InconclusivePruned);
        assert_eq!(non_pass_execution_failed.equivalence_status, EquivalenceStatus::ExecutionFailed);
        assert_eq!(mismatch.equivalence_status, EquivalenceStatus::Mismatch);

        for field in [
            "schema_version",
            "instruction",
            "clause_id",
            "target_memory_config",
            "linearization_stats",
            "limit_stats",
            "normalized_branch_summary",
            "isa_state_delta",
            "ret_val",
            "memory_summary",
            "exception_status",
            "equivalence_status",
        ] {
            assert_missing_required_field_fails(&normal_load, field);
        }
    }

    #[test]
    fn original_json_and_equiv_summary_json_are_separate_schemas_and_paths() {
        let original = AssemGen_Json::new(vec![AssemGen_Json_Item::new(
            &RISCVTarget::RV64,
            "LD".to_string(),
            "0x0000b383".to_string(),
            BTreeMap::from([("x7".to_string(), "symbolic".to_string())]),
            "ret".to_string(),
        )]);
        let summary = EquivSummaryJson::new(vec![normal_rv64_load_equiv_summary(
            "LD",
            empty_target_memory_config(),
            load_read_memory_summary(8),
            EquivalenceStatus::ProvedEquivalent,
        )]);

        let original_json = serde_json::to_value(&original).unwrap();
        let summary_json = serde_json::to_value(&summary).unwrap();

        assert!(original_json.get("gen").unwrap().is_array());
        assert!(original_json.get("summaries").is_none());
        assert!(original_json["gen"][0].get("schema_version").is_none());
        assert!(original_json["gen"][0].get("memory_summary").is_none());
        assert!(original_json["gen"][0].get("equivalence_status").is_none());

        assert!(summary_json.get("summaries").unwrap().is_array());
        assert!(summary_json.get("gen").is_none());
        assert_eq!(summary_json["summaries"][0]["schema_version"], EQUIV_SUMMARY_SCHEMA_VERSION);
        assert_eq!(summary_json["summaries"][0]["equivalence_status"], "proved_equivalent");
        assert!(summary_json["summaries"][0].get("memory_summary").is_some());

        let original_path = "output/64_LD.json";
        let summary_path = equiv_summary_output_path("rv64d", "LD");
        assert_eq!(summary_path, "output/rv64d_ld.equiv.json");
        assert_ne!(summary_path, original_path);
        assert!(summary_path.ends_with(".equiv.json"));
        assert!(!original_path.ends_with(".equiv.json"));
    }

    #[test]
    fn runtime_equiv_summary_for_assembly_emits_load_store_and_compressed_only() {
        let cfg = empty_target_memory_config();
        let smt_cfg = Config::new();
        let ctx = Context::new(smt_cfg);
        let solver = Solver::<crate::bitvector::b64::B64>::new(&ctx);

        let load = runtime_equiv_summary_for_assembly("ld x1, 0(x2)", cfg.clone(), &solver).unwrap();
        let store = runtime_equiv_summary_for_assembly("sd x1, 0(x2)", cfg.clone(), &solver).unwrap();
        let compressed = runtime_equiv_summary_for_assembly("c.lwsp x1, 0(sp)", cfg.clone(), &solver).unwrap();

        assert_eq!(assembly_to_summary_mnemonic("ld x1, 0(x2)"), Some("LD".to_string()));
        assert_eq!(load.instruction, "LD");
        assert_eq!(store.instruction, "SD");
        assert_eq!(compressed.instruction, "C.LWSP");
        assert_eq!(runtime_equiv_summary_for_assembly("addi x1, x2, 1", cfg, &solver), None);
    }

    #[test]
    fn fallback_equiv_summaries_for_instruction_fail_closed_when_runtime_paths_are_empty() {
        let load = fallback_equiv_summaries_for_instruction("zLOAD", empty_target_memory_config());
        let store = fallback_equiv_summaries_for_instruction("zSTORE", empty_target_memory_config());
        let compressed = fallback_equiv_summaries_for_instruction("zC_LWSP", empty_target_memory_config());

        assert_eq!(load.len(), normal_rv64_load_mnemonics().len());
        assert_eq!(store.len(), normal_rv64_store_mnemonics().len());
        assert_eq!(compressed.len(), 1);
        assert!(load.iter().chain(store.iter()).chain(compressed.iter()).all(|summary| {
            summary.equivalence_status == EquivalenceStatus::InconclusivePruned
        }));
        assert!(fallback_equiv_summaries_for_instruction("zADDIW", empty_target_memory_config()).is_empty());
    }

    #[test]
    fn memory_summary_extracts_read_and_write_events() {
        let events = vec![
            Event::ReadMem {
                value: Val::Symbolic(Sym::from_u32(10)),
                read_kind: Val::String("ram-read".to_string()),
                address: Val::Bits(crate::bitvector::b64::B64::from_u64(0x1000)),
                bytes: 8,
                tag_value: None,
                opts: crate::smt::ReadOpts::default(),
                region: "ram",
            },
            Event::WriteMem {
                value: Sym::from_u32(11),
                write_kind: Val::String("ram-write".to_string()),
                address: Val::Bits(crate::bitvector::b64::B64::from_u64(0x1008)),
                data: Val::Symbolic(Sym::from_u32(12)),
                bytes: 4,
                tag_value: Some(Val::Bool(true)),
                opts: crate::smt::WriteOpts::default(),
                region: "ram",
            },
        ];

        let trace_summary = summarize_memory_trace(&events, None, true);

        assert!(trace_summary.evidence_status.complete);
        assert_eq!(trace_summary.memory_summary.reads.len(), 1);
        assert_eq!(trace_summary.memory_summary.writes.len(), 1);
        let read = &trace_summary.memory_summary.reads[0].summary;
        assert!(read.contains(&"kind=read".to_string()));
        assert!(read.iter().any(|field| field.contains("address=")));
        assert!(read.contains(&"bytes=8".to_string()));
        assert!(read.contains(&"width_bits=64".to_string()));
        assert!(read.iter().any(|field| field.contains("value=")));
        assert!(read.contains(&"guard=unavailable".to_string()));
        assert!(read.contains(&"path=unavailable".to_string()));
        assert!(read.contains(&"status=observed".to_string()));

        let write = &trace_summary.memory_summary.writes[0].summary;
        assert!(write.contains(&"kind=write".to_string()));
        assert!(write.iter().any(|field| field.contains("address=")));
        assert!(write.contains(&"bytes=4".to_string()));
        assert!(write.contains(&"width_bits=32".to_string()));
        assert!(write.iter().any(|field| field.contains("data=")));
        assert!(write.contains(&"write_status_symbol=v11".to_string()));
        assert!(write.contains(&"guard=unavailable".to_string()));
        assert!(write.contains(&"path=unavailable".to_string()));
        assert!(write.contains(&"status=observed".to_string()));
    }

    #[test]
    fn missing_required_memory_evidence_blocks_proved_equivalent() {
        let trace_summary = summarize_memory_trace::<crate::bitvector::b64::B64>(&[], None, true);

        assert!(!trace_summary.evidence_status.complete);
        assert_eq!(trace_summary.evidence_status.reason, Some("required_memory_evidence_missing".to_string()));
        assert_eq!(trace_summary.memory_summary.reads.len(), 0);
        assert_eq!(trace_summary.memory_summary.writes.len(), 0);
        assert_eq!(
            equivalence_status_with_memory_evidence(
                EquivalenceStatus::ProvedEquivalent,
                &trace_summary.evidence_status
            ),
            EquivalenceStatus::InconclusivePruned
        );
        assert_ne!(
            equivalence_status_with_memory_evidence(
                EquivalenceStatus::ProvedEquivalent,
                &trace_summary.evidence_status
            ),
            EquivalenceStatus::ProvedEquivalent
        );
    }

    fn empty_target_memory_config() -> TargetMemoryConfigSummary {
        TargetMemoryConfigSummary {
            ram_regions: vec![],
            symbolic_regions: vec![],
            page_table_preset: Some("bare".to_string()),
            clint_enabled: false,
            mmio_enabled: false,
        }
    }

    fn load_read_memory_summary(bytes: u32) -> MemorySummary {
        let events = vec![Event::ReadMem {
            value: Val::Symbolic(Sym::from_u32(20)),
            read_kind: Val::String("ram-read".to_string()),
            address: Val::Bits(crate::bitvector::b64::B64::from_u64(0x8000_0000)),
            bytes,
            tag_value: None,
            opts: crate::smt::ReadOpts::default(),
            region: "ram",
        }];

        summarize_memory_trace(&events, None, true).memory_summary
    }

    fn load_read_memory_summary_at(address: u64, bytes: u64) -> MemorySummary {
        MemorySummary {
            reads: vec![MemAccessSummary {
                count: 1,
                summary: vec![
                    "kind=read".to_string(),
                    format!("address=0x{:x}", address),
                    format!("bytes={}", bytes),
                    format!("width_bits={}", bytes * 8),
                    "value=v20".to_string(),
                    "read_kind=ram-read".to_string(),
                    "region=ram".to_string(),
                    "status=observed".to_string(),
                ],
            }],
            writes: vec![],
        }
    }

    fn store_write_memory_summary(bytes: u32) -> MemorySummary {
        let events = vec![Event::WriteMem {
            value: Sym::from_u32(30),
            write_kind: Val::String("ram-write".to_string()),
            address: Val::Bits(crate::bitvector::b64::B64::from_u64(0x8000_0010)),
            data: Val::Symbolic(Sym::from_u32(31)),
            bytes,
            tag_value: None,
            opts: crate::smt::WriteOpts::default(),
            region: "ram",
        }];

        summarize_memory_trace(&events, None, true).memory_summary
    }

    fn store_write_memory_summary_at(address: u64, bytes: u64) -> MemorySummary {
        MemorySummary {
            reads: vec![],
            writes: vec![MemAccessSummary {
                count: 1,
                summary: vec![
                    "kind=write".to_string(),
                    format!("address=0x{:x}", address),
                    format!("bytes={}", bytes),
                    format!("width_bits={}", bytes * 8),
                    "data=v31".to_string(),
                    "write_kind=ram-write".to_string(),
                    "region=ram".to_string(),
                    "status=observed".to_string(),
                ],
            }],
        }
    }

    fn semantic_equivalence_fixture() -> EquivSummaryJsonItem {
        normal_rv64_load_equiv_summary(
            "LD",
            empty_target_memory_config(),
            load_read_memory_summary(8),
            EquivalenceStatus::ProvedEquivalent,
        )
    }

    #[test]
    fn semantic_equivalence_exact_matching_summaries_are_proved_equivalent() {
        let expected = semantic_equivalence_fixture();
        let actual = expected.clone();

        assert_eq!(compare_equiv_summaries(&expected, &actual), EquivalenceStatus::ProvedEquivalent);
    }

    #[test]
    fn semantic_equivalence_summary_field_mismatches_are_mismatch() {
        let expected = semantic_equivalence_fixture();

        let mut ret_mismatch = expected.clone();
        ret_mismatch.ret_val.push_str("; changed_ret");
        assert_eq!(compare_equiv_summaries(&expected, &ret_mismatch), EquivalenceStatus::Mismatch);

        let mut memory_mismatch = expected.clone();
        memory_mismatch.memory_summary.reads[0].summary.push("value=changed".to_string());
        assert_eq!(compare_equiv_summaries(&expected, &memory_mismatch), EquivalenceStatus::Mismatch);

        let mut exception_mismatch = expected.clone();
        exception_mismatch.exception_status.exception = Some("misaligned".to_string());
        assert_eq!(compare_equiv_summaries(&expected, &exception_mismatch), EquivalenceStatus::Mismatch);

        let mut branch_mismatch = expected.clone();
        branch_mismatch.normalized_branch_summary.total_branches = 1;
        branch_mismatch.normalized_branch_summary.branch_signatures.push("branch0".to_string());
        assert_eq!(compare_equiv_summaries(&expected, &branch_mismatch), EquivalenceStatus::Mismatch);

        let mut state_mismatch = expected.clone();
        state_mismatch.isa_state_delta.changed.insert("rd".to_string(), "changed_state".to_string());
        assert_eq!(compare_equiv_summaries(&expected, &state_mismatch), EquivalenceStatus::Mismatch);
    }

    #[test]
    fn semantic_equivalence_pruned_limit_or_fallback_paths_are_inconclusive() {
        let expected = semantic_equivalence_fixture();

        let mut limit_pruned = expected.clone();
        limit_pruned.limit_stats.pruned = true;
        limit_pruned.equivalence_status = EquivalenceStatus::InconclusivePruned;
        assert_eq!(
            compare_equiv_summaries(&limit_pruned, &limit_pruned.clone()),
            EquivalenceStatus::InconclusivePruned
        );

        let mut limit_unresolved = expected.clone();
        limit_unresolved.limit_stats.hit_limit = true;
        limit_unresolved.limit_stats.hits.push(LimitHitStats {
            function: "zrepeat_test".to_string(),
            ir_pc: 3,
            arch_pc: None,
            repeat_count: 4,
            configured_limit: 3,
            task_id: Some(9),
        });
        assert_eq!(
            compare_equiv_summaries(&limit_unresolved, &limit_unresolved.clone()),
            EquivalenceStatus::InconclusivePruned
        );

        let hit = RepeatLimitHit {
            function: "zrepeat_test".to_string(),
            ir_pc: 3,
            arch_pc: None,
            repeat_count: 4,
            limit: 3,
            task_id: Some(9),
            worker_id: Some(1),
        };
        let mut fallback_pruned = expected.clone();
        fallback_pruned.fallback_stats = Some(FallbackStats::from_limit_hit(&hit, false));
        assert_eq!(
            compare_equiv_summaries(&fallback_pruned, &fallback_pruned.clone()),
            EquivalenceStatus::InconclusivePruned
        );
    }

    #[test]
    fn semantic_equivalence_execution_failed_input_is_execution_failed() {
        let expected = semantic_equivalence_fixture();
        let mut actual = expected.clone();
        actual.equivalence_status = EquivalenceStatus::ExecutionFailed;

        assert_eq!(compare_equiv_summaries(&expected, &actual), EquivalenceStatus::ExecutionFailed);
    }

    #[test]
    fn semantic_equivalence_missing_mapping_or_memory_evidence_never_passes() {
        let missing_mapping = compressed_rv64_memory_equiv_summary(
            "C.UNKNOWN",
            empty_target_memory_config(),
            MemorySummary { reads: vec![], writes: vec![] },
            EquivalenceStatus::ProvedEquivalent,
        );
        assert_eq!(
            compare_equiv_summaries(&missing_mapping, &missing_mapping.clone()),
            EquivalenceStatus::InconclusivePruned
        );

        let unresolved_memory = normal_rv64_load_equiv_summary(
            "LD",
            empty_target_memory_config(),
            MemorySummary {
                reads: vec![MemAccessSummary {
                    count: 1,
                    summary: vec![
                        "kind=read".to_string(),
                        "address=unresolved_symbolic_address".to_string(),
                        "bytes=8".to_string(),
                        "width_bits=64".to_string(),
                        "status=observed".to_string(),
                    ],
                }],
                writes: vec![],
            },
            EquivalenceStatus::ProvedEquivalent,
        );
        assert_eq!(
            compare_equiv_summaries(&unresolved_memory, &unresolved_memory.clone()),
            EquivalenceStatus::InconclusivePruned
        );

        let missing_evidence = normal_rv64_store_equiv_summary(
            "SD",
            empty_target_memory_config(),
            MemorySummary {
                reads: vec![],
                writes: vec![MemAccessSummary {
                    count: 0,
                    summary: vec!["required_store_writemem_evidence_missing".to_string()],
                }],
            },
            EquivalenceStatus::ProvedEquivalent,
        );
        assert_eq!(
            compare_equiv_summaries(&missing_evidence, &missing_evidence.clone()),
            EquivalenceStatus::InconclusivePruned
        );
    }

    #[test]
    fn load_summary_ld_aligned_has_one_64_bit_read() {
        let summary = normal_rv64_load_equiv_summary(
            "LD",
            empty_target_memory_config(),
            load_read_memory_summary(8),
            EquivalenceStatus::ProvedEquivalent,
        );

        assert_eq!(summary.instruction, "LD");
        assert_eq!(summary.clause_id, "rv64d.zLOAD");
        assert_eq!(summary.memory_summary.reads.len(), 1);
        assert!(summary.memory_summary.writes.is_empty());
        assert!(summary.memory_summary.reads[0].summary.contains(&"bytes=8".to_string()));
        assert!(summary.memory_summary.reads[0].summary.contains(&"width_bits=64".to_string()));
        assert!(summary.memory_summary.reads[0].summary.contains(&"status=observed".to_string()));
        assert_eq!(summary.exception_status.alignment, Some(false));
        assert_eq!(summary.equivalence_status, EquivalenceStatus::ProvedEquivalent);
    }

    #[test]
    fn load_summary_lwu_zero_extension_differs_from_lw_sign_extension() {
        let lw = normal_rv64_load_equiv_summary(
            "LW",
            empty_target_memory_config(),
            load_read_memory_summary(4),
            EquivalenceStatus::ProvedEquivalent,
        );
        let lwu = normal_rv64_load_equiv_summary(
            "LWU",
            empty_target_memory_config(),
            load_read_memory_summary(4),
            EquivalenceStatus::ProvedEquivalent,
        );

        assert!(lw.ret_val.contains("extension=SignExtend"));
        assert!(lw.isa_state_delta.changed.get("rd").unwrap().contains("extension=SignExtend"));
        assert!(lwu.ret_val.contains("extension=ZeroExtend"));
        assert!(lwu.isa_state_delta.changed.get("rd").unwrap().contains("extension=ZeroExtend"));
        assert_ne!(lw.ret_val, lwu.ret_val);
        assert!(lw.memory_summary.reads[0].summary.contains(&"bytes=4".to_string()));
        assert!(lwu.memory_summary.reads[0].summary.contains(&"width_bits=32".to_string()));
    }

    #[test]
    fn load_summary_covers_exact_normal_rv64_load_mnemonics() {
        let expected = [
            ("LB", 1, 8, LoadExtensionSemantics::SignExtend),
            ("LH", 2, 16, LoadExtensionSemantics::SignExtend),
            ("LW", 4, 32, LoadExtensionSemantics::SignExtend),
            ("LD", 8, 64, LoadExtensionSemantics::FullWidth),
            ("LBU", 1, 8, LoadExtensionSemantics::ZeroExtend),
            ("LHU", 2, 16, LoadExtensionSemantics::ZeroExtend),
            ("LWU", 4, 32, LoadExtensionSemantics::ZeroExtend),
        ];

        assert_eq!(normal_rv64_load_mnemonics(), ["LB", "LH", "LW", "LD", "LBU", "LHU", "LWU"]);
        for (mnemonic, bytes, width_bits, extension) in expected {
            let summary = normal_rv64_load_summary(mnemonic).unwrap();
            assert_eq!(summary.bytes, bytes);
            assert_eq!(summary.width_bits, width_bits);
            assert_eq!(summary.xlen_bits, 64);
            assert_eq!(summary.extension, extension);
            assert_eq!(summary.clause_id, "rv64d.zLOAD");
        }

        assert!(normal_rv64_load_summary("FLD").is_none());
        assert!(normal_rv64_load_summary("LR.D").is_none());
    }

    #[test]
    fn load_summary_missing_or_wrong_readmem_evidence_is_not_proved() {
        let missing = normal_rv64_load_equiv_summary(
            "LD",
            empty_target_memory_config(),
            MemorySummary { reads: vec![], writes: vec![] },
            EquivalenceStatus::ProvedEquivalent,
        );
        let wrong_width = normal_rv64_load_equiv_summary(
            "LD",
            empty_target_memory_config(),
            load_read_memory_summary(4),
            EquivalenceStatus::ProvedEquivalent,
        );

        assert_eq!(missing.equivalence_status, EquivalenceStatus::InconclusivePruned);
        assert_eq!(wrong_width.equivalence_status, EquivalenceStatus::InconclusivePruned);
    }

    #[test]
    fn alignment_summary_misaligned_ld_records_exception_and_fails_closed() {
        let summary = normal_rv64_load_equiv_summary(
            "LD",
            empty_target_memory_config(),
            load_read_memory_summary_at(0x8000_0004, 8),
            EquivalenceStatus::ProvedEquivalent,
        );

        assert_eq!(summary.exception_status.exception, Some("misaligned".to_string()));
        assert_eq!(summary.exception_status.alignment, Some(true));
        assert_eq!(summary.equivalence_status, EquivalenceStatus::InconclusivePruned);
    }

    #[test]
    fn alignment_summary_clause_matched_exception_can_preserve_equivalence() {
        let mut memory_summary = load_read_memory_summary_at(0x8000_0004, 8);
        memory_summary.reads[0].summary.push("clause_exception_matched=true".to_string());
        let summary = normal_rv64_load_equiv_summary(
            "LD",
            empty_target_memory_config(),
            memory_summary,
            EquivalenceStatus::ProvedEquivalent,
        );

        assert_eq!(summary.exception_status.exception, Some("misaligned".to_string()));
        assert_eq!(summary.exception_status.alignment, Some(true));
        assert_eq!(summary.equivalence_status, EquivalenceStatus::ProvedEquivalent);
    }

    #[test]
    fn alignment_summary_lb_unaligned_byte_address_does_not_alignment_fail() {
        let summary = normal_rv64_load_equiv_summary(
            "LB",
            empty_target_memory_config(),
            load_read_memory_summary_at(0x8000_0003, 1),
            EquivalenceStatus::ProvedEquivalent,
        );

        assert_eq!(summary.exception_status.exception, None);
        assert_eq!(summary.exception_status.alignment, Some(false));
        assert_eq!(summary.equivalence_status, EquivalenceStatus::ProvedEquivalent);
    }

    #[test]
    fn compressed_mapping_clwsp_records_stable_path_and_clause() {
        let mapping = compressed_rv64_memory_mapping("C.LWSP").unwrap();
        let summary = compressed_rv64_memory_equiv_summary(
            "C.LWSP",
            empty_target_memory_config(),
            load_read_memory_summary(4),
            EquivalenceStatus::ProvedEquivalent,
        );

        assert_eq!(equiv_summary_output_path("rv64d", "C.LWSP"), "output/rv64d_c_lwsp.equiv.json");
        assert_eq!(mapping.instruction, "C.LWSP");
        assert_eq!(mapping.base_mnemonic, "LW");
        assert_eq!(mapping.clause_id, "rv64d.zLOAD");
        assert_eq!(mapping.access_kind, MemoryAccessKind::Load);
        assert_eq!(summary.instruction, "C.LWSP");
        assert_eq!(summary.clause_id, "rv64d.zLOAD");
        assert!(summary.ret_val.contains("compressed_instruction=C.LWSP"));
        assert!(summary.ret_val.contains("maps_to=LW"));
        assert!(summary.isa_state_delta.changed.get("compressed_mapping").unwrap().contains("clause_id=rv64d.zLOAD"));
        assert_eq!(summary.equivalence_status, EquivalenceStatus::ProvedEquivalent);
    }

    #[test]
    fn compressed_mapping_covers_exact_load_store_mnemonics() {
        let expected = [
            ("C.LW", "LW", MemoryAccessKind::Load, "rv64d.zLOAD"),
            ("C.LD", "LD", MemoryAccessKind::Load, "rv64d.zLOAD"),
            ("C.LWSP", "LW", MemoryAccessKind::Load, "rv64d.zLOAD"),
            ("C.LDSP", "LD", MemoryAccessKind::Load, "rv64d.zLOAD"),
            ("C.SW", "SW", MemoryAccessKind::Store, "rv64d.zSTORE"),
            ("C.SD", "SD", MemoryAccessKind::Store, "rv64d.zSTORE"),
            ("C.SWSP", "SW", MemoryAccessKind::Store, "rv64d.zSTORE"),
            ("C.SDSP", "SD", MemoryAccessKind::Store, "rv64d.zSTORE"),
        ];

        assert_eq!(
            compressed_rv64_memory_mnemonics(),
            ["C.LW", "C.LD", "C.LWSP", "C.LDSP", "C.SW", "C.SD", "C.SWSP", "C.SDSP"]
        );
        for (mnemonic, base_mnemonic, access_kind, clause_id) in expected {
            let mapping = compressed_rv64_memory_mapping(mnemonic).unwrap();
            assert_eq!(mapping.instruction, mnemonic);
            assert_eq!(mapping.base_mnemonic, base_mnemonic);
            assert_eq!(mapping.access_kind, access_kind);
            assert_eq!(mapping.clause_id, clause_id);
        }
    }

    #[test]
    fn compressed_mapping_missing_mnemonic_is_non_pass() {
        let summary = compressed_rv64_memory_equiv_summary(
            "C.UNKNOWN",
            empty_target_memory_config(),
            MemorySummary { reads: vec![], writes: vec![] },
            EquivalenceStatus::ProvedEquivalent,
        );

        assert!(compressed_rv64_memory_mapping("C.UNKNOWN").is_none());
        assert_eq!(summary.instruction, "C.UNKNOWN");
        assert_eq!(summary.clause_id, "unavailable");
        assert_eq!(summary.exception_status.exception, Some("missing_compressed_clause_mapping".to_string()));
        assert_eq!(summary.equivalence_status, EquivalenceStatus::InconclusivePruned);
        assert_ne!(summary.equivalence_status, EquivalenceStatus::ProvedEquivalent);
    }

    #[test]
    fn compressed_mapping_excludes_floating_point_and_unrelated_compressed() {
        for mnemonic in ["C.FLD", "C.FSD", "C.FLW", "C.FSW", "C.ADDI", "C.J"] {
            assert!(compressed_rv64_memory_mapping(mnemonic).is_none());
        }
    }

    #[test]
    fn store_summary_sd_aligned_has_one_64_bit_write() {
        let summary = normal_rv64_store_equiv_summary(
            "SD",
            empty_target_memory_config(),
            store_write_memory_summary(8),
            EquivalenceStatus::ProvedEquivalent,
        );

        assert_eq!(summary.instruction, "SD");
        assert_eq!(summary.clause_id, "rv64d.zSTORE");
        assert!(summary.memory_summary.reads.is_empty());
        assert_eq!(summary.memory_summary.writes.len(), 1);
        assert!(summary.memory_summary.writes[0].summary.contains(&"kind=write".to_string()));
        assert!(summary.memory_summary.writes[0].summary.contains(&"bytes=8".to_string()));
        assert!(summary.memory_summary.writes[0].summary.contains(&"width_bits=64".to_string()));
        assert!(summary.memory_summary.writes[0].summary.contains(&"status=observed".to_string()));
        assert!(summary.ret_val.contains("truncation=FullWidth"));
        assert_eq!(summary.exception_status.alignment, Some(false));
        assert_eq!(summary.equivalence_status, EquivalenceStatus::ProvedEquivalent);
    }

    #[test]
    fn store_summary_sb_byte_truncation_differs_from_sd_full_width() {
        let sb = normal_rv64_store_equiv_summary(
            "SB",
            empty_target_memory_config(),
            store_write_memory_summary(1),
            EquivalenceStatus::ProvedEquivalent,
        );
        let sd = normal_rv64_store_equiv_summary(
            "SD",
            empty_target_memory_config(),
            store_write_memory_summary(8),
            EquivalenceStatus::ProvedEquivalent,
        );

        assert!(sb.ret_val.contains("truncation=ByteTruncate"));
        assert!(sb.isa_state_delta.changed.get("memory").unwrap().contains("truncation=ByteTruncate"));
        assert!(sd.ret_val.contains("truncation=FullWidth"));
        assert!(sd.isa_state_delta.changed.get("memory").unwrap().contains("truncation=FullWidth"));
        assert_ne!(sb.ret_val, sd.ret_val);
        assert!(sb.memory_summary.writes[0].summary.contains(&"bytes=1".to_string()));
        assert!(sb.memory_summary.writes[0].summary.contains(&"width_bits=8".to_string()));
        assert!(sd.memory_summary.writes[0].summary.contains(&"bytes=8".to_string()));
        assert!(sd.memory_summary.writes[0].summary.contains(&"width_bits=64".to_string()));
    }

    #[test]
    fn store_summary_covers_exact_normal_rv64_store_mnemonics() {
        let expected = [
            ("SB", 1, 8, StoreTruncationSemantics::ByteTruncate),
            ("SH", 2, 16, StoreTruncationSemantics::HalfwordTruncate),
            ("SW", 4, 32, StoreTruncationSemantics::WordTruncate),
            ("SD", 8, 64, StoreTruncationSemantics::FullWidth),
        ];

        assert_eq!(normal_rv64_store_mnemonics(), ["SB", "SH", "SW", "SD"]);
        for (mnemonic, bytes, width_bits, truncation) in expected {
            let summary = normal_rv64_store_summary(mnemonic).unwrap();
            assert_eq!(summary.bytes, bytes);
            assert_eq!(summary.width_bits, width_bits);
            assert_eq!(summary.xlen_bits, 64);
            assert_eq!(summary.truncation, truncation);
            assert_eq!(summary.clause_id, "rv64d.zSTORE");
        }

        assert!(normal_rv64_store_summary("FSW").is_none());
        assert!(normal_rv64_store_summary("AMOSWAP.D").is_none());
        assert!(normal_rv64_store_summary("SC.D").is_none());
        assert!(normal_rv64_store_summary("VS1R.V").is_none());
    }

    #[test]
    fn store_summary_missing_or_wrong_writemem_evidence_is_not_proved() {
        let missing = normal_rv64_store_equiv_summary(
            "SD",
            empty_target_memory_config(),
            MemorySummary { reads: vec![], writes: vec![] },
            EquivalenceStatus::ProvedEquivalent,
        );
        let wrong_width = normal_rv64_store_equiv_summary(
            "SD",
            empty_target_memory_config(),
            store_write_memory_summary(4),
            EquivalenceStatus::ProvedEquivalent,
        );
        let unsupported = normal_rv64_store_equiv_summary(
            "AMOSWAP.D",
            empty_target_memory_config(),
            store_write_memory_summary(8),
            EquivalenceStatus::ProvedEquivalent,
        );

        assert_eq!(missing.equivalence_status, EquivalenceStatus::InconclusivePruned);
        assert_eq!(wrong_width.equivalence_status, EquivalenceStatus::InconclusivePruned);
        assert_eq!(unsupported.equivalence_status, EquivalenceStatus::InconclusivePruned);
    }

    #[test]
    fn alignment_summary_sb_unaligned_byte_address_does_not_alignment_fail() {
        let summary = normal_rv64_store_equiv_summary(
            "SB",
            empty_target_memory_config(),
            store_write_memory_summary_at(0x8000_0005, 1),
            EquivalenceStatus::ProvedEquivalent,
        );

        assert_eq!(summary.exception_status.exception, None);
        assert_eq!(summary.exception_status.alignment, Some(false));
        assert_eq!(summary.equivalence_status, EquivalenceStatus::ProvedEquivalent);
    }

    #[test]
    fn alignment_summary_unsupported_or_unresolved_categories_fail_closed() {
        let unsupported = normal_rv64_load_equiv_summary(
            "FLD",
            empty_target_memory_config(),
            load_read_memory_summary_at(0x8000_0000, 8),
            EquivalenceStatus::ProvedEquivalent,
        );
        let unresolved = normal_rv64_store_equiv_summary(
            "SD",
            empty_target_memory_config(),
            MemorySummary { reads: vec![], writes: vec![] },
            EquivalenceStatus::ProvedEquivalent,
        );

        assert_eq!(unsupported.exception_status.exception, None);
        assert_eq!(unsupported.equivalence_status, EquivalenceStatus::InconclusivePruned);
        assert_eq!(unresolved.exception_status.exception, Some("unresolved_symbolic_address".to_string()));
        assert_eq!(unresolved.equivalence_status, EquivalenceStatus::InconclusivePruned);
    }

    #[test]
    fn fallback_stats_order_linearization_before_prune() {
        let hit = RepeatLimitHit {
            function: "zrepeat_test".to_string(),
            ir_pc: 3,
            arch_pc: None,
            repeat_count: 4,
            limit: 3,
            task_id: Some(9),
            worker_id: Some(1),
        };

        let stats = FallbackStats::from_limit_hit(&hit, false);

        assert_eq!(stats.related_function, Some("zrepeat_test".to_string()));
        assert_eq!(
            stats.events.iter().map(|event| &event.phase).collect::<Vec<_>>(),
            vec![
                &FallbackPhase::LimitHit,
                &FallbackPhase::LinearizationAttempted,
                &FallbackPhase::LinearizationFailed,
                &FallbackPhase::Pruned,
            ]
        );
        assert!(stats.events.iter().all(|event| event.related_function == "zrepeat_test"));
    }

    #[test]
    fn successful_fallback_records_linearization_without_prune() {
        let hit = RepeatLimitHit {
            function: "zrepeat_test".to_string(),
            ir_pc: 3,
            arch_pc: None,
            repeat_count: 4,
            limit: 3,
            task_id: Some(9),
            worker_id: Some(1),
        };

        let stats = FallbackStats::from_limit_hit(&hit, true);

        assert_eq!(
            stats.events.iter().map(|event| &event.phase).collect::<Vec<_>>(),
            vec![
                &FallbackPhase::LimitHit,
                &FallbackPhase::LinearizationAttempted,
                &FallbackPhase::LinearizationSucceeded
            ]
        );
        assert_eq!(stats.failed_status(), None);
    }

    #[test]
    fn failed_fallback_is_inconclusive_pruned_not_equivalent() {
        let hit = RepeatLimitHit {
            function: "zrepeat_test".to_string(),
            ir_pc: 3,
            arch_pc: None,
            repeat_count: 4,
            limit: 3,
            task_id: Some(9),
            worker_id: Some(1),
        };

        let stats = FallbackStats::from_limit_hit(&hit, false);
        let status = stats.failed_status().unwrap_or(EquivalenceStatus::ProvedEquivalent);

        assert_eq!(status, EquivalenceStatus::InconclusivePruned);
        assert_ne!(status, EquivalenceStatus::ProvedEquivalent);
    }

    #[test]
    fn symbolic_execute_memory_builds_configured_regions() {
        let config = SymbolicMemoryConfig {
            ram_regions: vec![AddressRange { base: 0x8000_0000, top: 0x8000_1000 }],
            symbolic_regions: vec![AddressRange { base: 0x8000_2000, top: 0x8000_3000 }],
            page_table_preset: PageTablePreset::Sv39,
            clint_enabled: true,
            mmio_enabled: true,
        };

        let (memory, summary) = build_symbolic_execute_memory::<crate::bitvector::b64::B64>(&config).unwrap();

        assert_eq!(memory.regions().len(), 2);
        assert_eq!(summary.ram_regions, vec![SummaryAddressRange { base: 0x8000_0000, top: 0x8000_1000 }]);
        assert_eq!(summary.symbolic_regions, vec![SummaryAddressRange { base: 0x8000_2000, top: 0x8000_3000 }]);
        assert_eq!(summary.page_table_preset, Some("sv39".to_string()));
        assert!(summary.clint_enabled);
        assert!(summary.mmio_enabled);
    }

    #[test]
    fn symbolic_execute_memory_allows_disabled_device_toggles_without_extra_ram() {
        let config = SymbolicMemoryConfig {
            ram_regions: vec![AddressRange { base: 0x8000_0000, top: 0x8000_1000 }],
            symbolic_regions: vec![AddressRange { base: 0x8000_2000, top: 0x8000_3000 }],
            page_table_preset: PageTablePreset::Bare,
            clint_enabled: false,
            mmio_enabled: false,
        };

        let (memory, summary) = build_symbolic_execute_memory::<crate::bitvector::b64::B64>(&config).unwrap();

        assert_eq!(memory.regions().len(), config.ram_regions.len() + config.symbolic_regions.len());
        assert_eq!(summary.ram_regions, vec![SummaryAddressRange { base: 0x8000_0000, top: 0x8000_1000 }]);
        assert_eq!(summary.symbolic_regions, vec![SummaryAddressRange { base: 0x8000_2000, top: 0x8000_3000 }]);
        assert!(!summary.clint_enabled);
        assert!(!summary.mmio_enabled);
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
    if (instruction_name == "zSTORE") {
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

fn assembly_to_summary_mnemonic(assembly: &str) -> Option<String> {
    assembly.split_whitespace().next().map(|mnemonic| mnemonic.trim_end_matches(',').to_ascii_uppercase())
}

fn runtime_equiv_summary_for_assembly<B: BV>(
    assembly: &str,
    target_memory_config: TargetMemoryConfigSummary,
    solver: &Solver<B>,
) -> Option<EquivSummaryJsonItem> {
    let mnemonic = assembly_to_summary_mnemonic(assembly)?;
    let events = solver.trace().to_vec();
    let mut reads = Vec::new();
    let mut writes = Vec::new();

    for event in events {
        match event {
            Event::ReadMem { value, read_kind, address, bytes, tag_value, region, .. } => {
                reads.push(MemAccessSummary {
                    count: 1,
                    summary: vec![
                        "kind=read".to_string(),
                        format!("address={:?}", address),
                        format!("bytes={}", bytes),
                        format!("width_bits={}", bytes.saturating_mul(8)),
                        format!("value={:?}", value),
                        format!("read_kind={:?}", read_kind),
                        format!("tag={:?}", tag_value),
                        format!("region={}", region),
                        format!("exclusive={}", event.is_exclusive()),
                        format!("ifetch={}", event.is_ifetch()),
                        "guard=unavailable".to_string(),
                        "path=unavailable".to_string(),
                        "status=observed".to_string(),
                    ],
                });
            }
            Event::WriteMem { value, write_kind, address, data, bytes, tag_value, region, .. } => {
                writes.push(MemAccessSummary {
                    count: 1,
                    summary: vec![
                        "kind=write".to_string(),
                        format!("address={:?}", address),
                        format!("bytes={}", bytes),
                        format!("width_bits={}", bytes.saturating_mul(8)),
                        format!("data={:?}", data),
                        format!("write_kind={:?}", write_kind),
                        format!("write_status_symbol=v{}", value),
                        format!("tag={:?}", tag_value),
                        format!("region={}", region),
                        format!("exclusive={}", event.is_exclusive()),
                        "guard=unavailable".to_string(),
                        "path=unavailable".to_string(),
                        "status=observed".to_string(),
                    ],
                });
            }
            _ => {}
        }
    }

    let memory_summary = MemorySummary { reads, writes };

    if normal_rv64_load_summary(&mnemonic).is_some() {
        Some(normal_rv64_load_equiv_summary(
            &mnemonic,
            target_memory_config,
            memory_summary,
            EquivalenceStatus::ProvedEquivalent,
        ))
    } else if normal_rv64_store_summary(&mnemonic).is_some() {
        Some(normal_rv64_store_equiv_summary(
            &mnemonic,
            target_memory_config,
            memory_summary,
            EquivalenceStatus::ProvedEquivalent,
        ))
    } else if compressed_rv64_memory_mapping(&mnemonic).is_some() {
        Some(compressed_rv64_memory_equiv_summary(
            &mnemonic,
            target_memory_config,
            memory_summary,
            EquivalenceStatus::ProvedEquivalent,
        ))
    } else {
        None
    }
}

fn fallback_equiv_summaries_for_instruction(
    instruction_name: &str,
    target_memory_config: TargetMemoryConfigSummary,
) -> Vec<EquivSummaryJsonItem> {
    let empty_memory = MemorySummary { reads: vec![], writes: vec![] };

    match instruction_name {
        "zLOAD" => normal_rv64_load_mnemonics()
            .into_iter()
            .map(|mnemonic| {
                normal_rv64_load_equiv_summary(
                    mnemonic,
                    target_memory_config.clone(),
                    empty_memory.clone(),
                    EquivalenceStatus::ProvedEquivalent,
                )
            })
            .collect(),
        "zSTORE" => normal_rv64_store_mnemonics()
            .into_iter()
            .map(|mnemonic| {
                normal_rv64_store_equiv_summary(
                    mnemonic,
                    target_memory_config.clone(),
                    empty_memory.clone(),
                    EquivalenceStatus::ProvedEquivalent,
                )
            })
            .collect(),
        "zC_LW" | "zC_LD" | "zC_LWSP" | "zC_LDSP" | "zC_SW" | "zC_SD" | "zC_SWSP" | "zC_SDSP" => {
            let mnemonic = zencode::decode(instruction_name.trim_start_matches('z'));
            vec![compressed_rv64_memory_equiv_summary(
                &mnemonic,
                target_memory_config,
                empty_memory,
                EquivalenceStatus::ProvedEquivalent,
            )]
        }
        _ => vec![],
    }
}

pub fn run_symbolic_execute<B: BV>(
    instruction_name: &str,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Result<Option<String>, ExecError> {
    run_symbolic_execute_with_memory_config(instruction_name, shared_state, regs, lets, None)
}

pub fn run_symbolic_execute_with_memory_config<B: BV>(
    instruction_name: &str,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
    isa_config: Option<&ISAConfig<B>>,
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

    // 使用checkpoint执行函数，支持错误传播
    let result: Arc<Mutex<(AssemGen_Json, EquivSummaryJson)>> =
        Arc::new(Mutex::new((AssemGen_Json::new(Vec::new()), EquivSummaryJson::new(Vec::new()))));
    let memory_and_summary =
        isa_config.and_then(|config| config.symbolic_memory.as_ref()).map(build_symbolic_execute_memory).transpose()?;
    if let Some((_, summary)) = &memory_and_summary {
        eprintln!("symbolic_memory effective config: {:?}", summary);
    }
    let runtime_target_memory_config =
        memory_and_summary.as_ref().map(|(_, summary)| summary.clone()).unwrap_or_else(|| TargetMemoryConfigSummary {
            ram_regions: vec![],
            symbolic_regions: vec![],
            page_table_preset: None,
            clint_enabled: false,
            mmio_enabled: false,
        });

    let collector = |thread: usize,
                     _task_id: TaskId,
                     exec_result: Result<(Run<B>, LocalFrame<B>), (ExecError, Backtrace)>,
                     shared_state: &SharedState<B>,
                     mut solver: Solver<B>,
                     collected: &Arc<Mutex<(AssemGen_Json, EquivSummaryJson)>>| {
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
                    let mut equiv_summary: Option<EquivSummaryJsonItem> = None;
                    // 获取ISA状态（寄存器、lets变量等）
                    // 首先检查solver是否可满足
                    if solver.check_sat(SourceLoc::unknown()) == crate::smt::SmtResult::Sat {
                        if let Ok(mut model) =
                            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| Model::new(&solver)))
                        {
                            println!("2. === ISA State (Thread {}) ===", thread);
                            let test = Sym::from_u32(6);
                            // dlog!("model.get_var({:?})={:?}", test, model.get_var(test));
                            // dlog!("fun_args={:#?}", model.get_val(&fun_args[0]));
                            match model.get_val(&fun_args[0]) {
                                Ok(arg_val) => {
                                    let asm_opt = isarch::get_assembly_name(arg_val.clone(), shared_state, regs, lets);
                                    println!("当前汇编：{:?}", asm_opt);
                                    match asm_opt {
                                        Some(asm) => test_ins = asm.clone(),
                                        None => return,
                                    }
                                    equiv_summary = runtime_equiv_summary_for_assembly(
                                        &test_ins,
                                        runtime_target_memory_config.clone(),
                                        &solver,
                                    );
                                    let asm_encdec_opt =
                                        isarch::get_assembly_encdec(arg_val.clone(), shared_state, regs, lets);
                                    let asm_encdec_opt = asm_encdec_opt
                                        .map(|val| FmtVal::from_val(&val, &mut model).unwrap().to_str(shared_state));
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
                                        Err(ExecError) => continue,
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
                        ret_val.to_str(shared_state).to_string(),
                    );
                    let mut collected_json = collected.lock().unwrap();
                    collected_json.0.gen.push(single_instruction_json);
                    if let Some(equiv_summary) = equiv_summary {
                        collected_json.1.summaries.push(equiv_summary);
                    }
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
    };

    if let Some((memory, _summary)) = memory_and_summary {
        crate::executor::execute_ir_function_with_checkpoint_and_memory(
            "zexecute",
            &fun_args,
            shared_state,
            regs,
            lets,
            memory,
            &result,
            &collector,
            cp,
        );
    } else {
        crate::executor::execute_ir_function_with_checkpoint(
            "zexecute",
            &fun_args,
            shared_state,
            regs,
            lets,
            &result,
            &collector,
            cp,
        );
    }

    // 提取字符串结果
    if let Ok(result_mutex) = Arc::try_unwrap(result) {
        let xlen_name = target.xlen_name();
        let (original_json, equiv_summary_json) = result_mutex.into_inner().unwrap();
        original_json.to_json(Some(format!("output/{}_{}.json", xlen_name, instruction_name)));
        let equiv_summary_json = if equiv_summary_json.summaries.is_empty() {
            EquivSummaryJson::new(fallback_equiv_summaries_for_instruction(instruction_name, runtime_target_memory_config))
        } else {
            equiv_summary_json
        };
        if !equiv_summary_json.summaries.is_empty() {
            equiv_summary_json.to_json(Some(equiv_summary_output_path(xlen_name, instruction_name)));
        }
        Ok(None)
    } else {
        eprintln!("警告: {}无法获取 result 收集器", instruction_name);
        Ok(None)
    }
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

    let excute_through_instruction_table = ["zSTORE", "zLOAD"];
    // instruction_table.extend( excute_through_instruction_table.to_vec());

    for ins_name in instruction_table {
        match run_symbolic_execute_with_memory_config(ins_name, &shared_state, regs, lets, Some(isa_config)) {
            Ok(_) => {}
            Err(e) => {
                eprintln!("test_exec_main: {}运行错误 {}", ins_name, e)
            }
        };
    }
}
