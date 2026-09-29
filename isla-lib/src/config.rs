// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// 1. Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

//! This module loads a TOML file containing configuration for a specific instruction set
//! architecture.

use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::str::FromStr;
use std::sync::Arc;
use toml::Value;

use crate::bitvector::BV;
use crate::ir::{IRTypeInfo, Loc, Name, Reset, Symtab, URVal, Val};
use crate::ir_lexer::new_ir_lexer;
use crate::primop_util::symbolic_from_typedefs;
use crate::smt::smtlib::Exp;
use crate::smt_parser;
use crate::source_loc::{SourceLoc, SourceRegionSpec};
use crate::value_parser::{LocParser, URValParser, ValParser};
use crate::zencode;

fn allowed_keys(config: &Value, root: &str, allowed_keys: &[&str]) -> Result<(), String> {
    let Value::Table(tbl) = config else { return Err(format!("{} should be a toml key-value table", root)) };

    'outer: for key in tbl.keys() {
        for allowed_key in allowed_keys {
            if key == allowed_key {
                continue 'outer;
            }
        }
        return Err(format!("Key {} is not allowed in {}", key, root));
    }

    Ok(())
}

fn allowed_table_keys(config: &toml::value::Table, root: &str, allowed_keys: &[&str]) -> Result<(), String> {
    'outer: for key in config.keys() {
        for allowed_key in allowed_keys {
            if key == allowed_key {
                continue 'outer;
            }
        }
        return Err(format!("Key {} is not allowed in {}", key, root));
    }

    Ok(())
}

/// We make use of various external tools like an assembler/objdump utility. We want to make sure
/// they are available.
fn find_tool_path<P>(program: P) -> Result<PathBuf, String>
where
    P: AsRef<Path>,
{
    if program.as_ref().is_absolute() {
        Ok(program.as_ref().to_path_buf())
    } else {
        env::var_os("PATH")
            .and_then(|paths| {
                env::split_paths(&paths).find_map(|dir| {
                    let full_path = dir.join(&program);
                    if full_path.is_file() {
                        Some(full_path)
                    } else {
                        None
                    }
                })
            })
            .ok_or_else(|| format!("Tool {} not found in $PATH", program.as_ref().display()))
    }
}

#[derive(Debug)]
pub struct Tool {
    pub executable: PathBuf,
    pub options: Vec<String>,
}

impl Tool {
    pub fn command(&self) -> Command {
        let mut cmd = Command::new(&self.executable);
        cmd.args(&self.options);
        cmd
    }
}

#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryRegionType {
    Concrete,
    Symbolic,
    /// 判死区域：声明"这一段不关心"，读写（符号或具体地址）落到区域内即把
    /// 该执行路径判死（Unsat / BadRead/BadWrite），不产生任何访存事件。
    Excluded,
}

impl FromStr for MemoryRegionType {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "concrete" => Ok(MemoryRegionType::Concrete),
            "symbolic" => Ok(MemoryRegionType::Symbolic),
            "excluded" => Ok(MemoryRegionType::Excluded),
            _ => Err(format!("Unknown memory region type {}", s)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct MemoryRegionConfig {
    pub name: String,
    pub base: u64,
    pub size: u64,
    pub region_type: MemoryRegionType,
}

/// `zmisaligned_fault` 枚举（IR rv64d.ir:671）的配置镜像。模型字段语义见
/// zpmaCheck：NoFault 不因未对齐 trap；AccessFault/AlignmentFault 在地址
/// 未对齐时分别转 access/alignment fault。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PmaMisalignedFault {
    NoFault,
    AccessFault,
    AlignmentFault,
}

impl FromStr for PmaMisalignedFault {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "no_fault" => Ok(PmaMisalignedFault::NoFault),
            "access_fault" => Ok(PmaMisalignedFault::AccessFault),
            "alignment_fault" => Ok(PmaMisalignedFault::AlignmentFault),
            _ => Err(format!("Unknown PMA misaligned policy {}", s)),
        }
    }
}

/// `zReservability` 枚举（IR rv64d.ir:3161）的配置镜像。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PmaReservability {
    None,
    NonEventual,
    Eventual,
}

impl FromStr for PmaReservability {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "none" => Ok(PmaReservability::None),
            "non_eventual" => Ok(PmaReservability::NonEventual),
            "eventual" => Ok(PmaReservability::Eventual),
            _ => Err(format!("Unknown PMA reservability {}", s)),
        }
    }
}

/// `zPMA` record（IR rv64d.ir:3295）的配置镜像：别名（ram/rom/mmio/hole）
/// 与明细字段都解析到这个结构。字段语义由模型 zpmaCheck 消费。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PmaAttributes {
    pub readable: bool,
    pub writable: bool,
    pub executable: bool,
    pub cacheable: bool,
    pub coherent: bool,
    pub read_idempotent: bool,
    pub write_idempotent: bool,
    pub supports_cbo_zzero: bool,
    pub misaligned_fault: PmaMisalignedFault,
    pub reservability: PmaReservability,
    pub include_in_device_tree: bool,
}

impl PmaAttributes {
    /// attr 别名底座。ram/mmio 镜像 IR 固化 zpma_regions 默认 region 的属性，
    /// rom/hole 取最保守值（rom 只读；hole 全 false）。
    fn from_alias(alias: &str) -> Option<PmaAttributes> {
        let attributes = match alias {
            "ram" => PmaAttributes {
                readable: true,
                writable: true,
                executable: true,
                cacheable: true,
                coherent: true,
                read_idempotent: true,
                write_idempotent: true,
                supports_cbo_zzero: true,
                misaligned_fault: PmaMisalignedFault::NoFault,
                reservability: PmaReservability::Eventual,
                include_in_device_tree: true,
            },
            "rom" => PmaAttributes {
                readable: true,
                writable: false,
                executable: false,
                cacheable: true,
                coherent: true,
                read_idempotent: true,
                write_idempotent: true,
                supports_cbo_zzero: false,
                misaligned_fault: PmaMisalignedFault::NoFault,
                reservability: PmaReservability::None,
                include_in_device_tree: false,
            },
            "mmio" => PmaAttributes {
                readable: true,
                writable: true,
                executable: false,
                cacheable: false,
                coherent: true,
                read_idempotent: false,
                write_idempotent: false,
                supports_cbo_zzero: false,
                misaligned_fault: PmaMisalignedFault::AlignmentFault,
                reservability: PmaReservability::None,
                include_in_device_tree: false,
            },
            "hole" => PmaAttributes {
                readable: false,
                writable: false,
                executable: false,
                cacheable: false,
                coherent: false,
                read_idempotent: false,
                write_idempotent: false,
                supports_cbo_zzero: false,
                misaligned_fault: PmaMisalignedFault::NoFault,
                reservability: PmaReservability::None,
                include_in_device_tree: false,
            },
            _ => return None,
        };
        Some(attributes)
    }

    /// 无 attr 明细字段模式的基线：除 include_in_device_tree=true 外全 false。
    fn detailed_default() -> PmaAttributes {
        PmaAttributes {
            readable: false,
            writable: false,
            executable: false,
            cacheable: false,
            coherent: false,
            read_idempotent: false,
            write_idempotent: false,
            supports_cbo_zzero: false,
            misaligned_fault: PmaMisalignedFault::NoFault,
            reservability: PmaReservability::None,
            include_in_device_tree: true,
        }
    }
}

/// `zPMA_Region` record（IR rv64d.ir:3309）的配置镜像：base+size 布局
/// （非 base+end），属性见 [PmaAttributes]。
#[derive(Debug, Clone)]
pub struct PmaRegionConfig {
    pub name: String,
    pub base: u64,
    pub size: PmaSize,
    pub attributes: PmaAttributes,
}

/// S2（W17）：[[pma_regions]] 的 size 字段。`Concrete` 为固定值（W10 行为）；
/// `Symbolic` 把 IR 字段 zsizze 声明为 64 位符号常量，并在注入时附加闭区间
/// 取值域约束 [min, max]（bvule）——默认域防全 64 位空间稀释求解。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PmaSize {
    Concrete(u64),
    Symbolic { min: u64, max: u64 },
}

impl PmaSize {
    /// 取值域上界（具体 size 即自身）：重叠自校验用符号域上界做保守检查，
    /// 保证任意模型取值下相邻 region 都不重叠。
    fn upper_bound(&self) -> u64 {
        match self {
            PmaSize::Concrete(size) => *size,
            PmaSize::Symbolic { max, .. } => *max,
        }
    }
}

/// 符号 size 未声明 size_bounds 时的默认取值域：[4KiB, 2^43)。
/// 上界 2^43 锚定 W13 实测的 emu RAM 顶界（SimMemSize 8190GiB），下界 4KiB
/// 是最小页粒度（size=0 的 region 无意义，与具体路径的 size>0 校验一致）。
const SYMBOLIC_SIZE_DEFAULT_MIN: u64 = 0x1000;
const SYMBOLIC_SIZE_DEFAULT_MAX: u64 = 0x80000000000;

#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PageTableMode {
    SV39,
    SV48,
}

impl FromStr for PageTableMode {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "sv39" => Ok(PageTableMode::SV39),
            "sv48" => Ok(PageTableMode::SV48),
            _ => Err(format!("Unknown page table mode {}", s)),
        }
    }
}

#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PageTablePreset {
    Identity,
    Offset,
    ProtectedLinear,
    SymbolicMapping,
}

impl FromStr for PageTablePreset {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "identity" => Ok(PageTablePreset::Identity),
            "offset" => Ok(PageTablePreset::Offset),
            "protected" => Ok(PageTablePreset::ProtectedLinear),
            "symbolic" => Ok(PageTablePreset::SymbolicMapping),
            _ => Err(format!("Unknown page table preset {}", s)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ProtectedRange {
    pub base: u64,
    pub size: u64,
    pub flags: String,
}

#[derive(Debug, Clone)]
pub struct PageTableConfig {
    pub mode: PageTableMode,
    pub preset: PageTablePreset,
    pub base: u64,
    pub page_size: u64,
    pub offset: Option<i64>,
    pub protected_ranges: Option<Vec<ProtectedRange>>,
}

#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PmpMode {
    Tor,
    Na4,
    Napot,
}

impl FromStr for PmpMode {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "tor" => Ok(PmpMode::Tor),
            "na4" => Ok(PmpMode::Na4),
            "napot" => Ok(PmpMode::Napot),
            _ => Err(format!("Unknown PMP mode {}", s)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct PmpRule {
    pub index: u32,
    pub mode: PmpMode,
    pub base: u64,
    pub size: Option<u64>,
    pub permissions: String,
    pub locked: bool,
}

#[derive(Debug, Clone)]
pub struct PmpConfig {
    pub rules: Vec<PmpRule>,
    pub symbolic: bool,
}

/// W22：`derive_bit` 派生位约束。声明"target 位 ⇔ OR(每组组内全 1)"的
/// **双向等价**（不是单向蕴含）：任一组全 1 则 target 位必为 1；target 位为 1
/// 则必有某组全 1。用于架构只读镜像位——如 mstatus.SD ⇔ FS=Dirty(11) ∨
/// VS=Dirty(11) ∨ XS=Dirty(11)。钉 0 会与位组自由取值矛盾（组可取 Dirty），
/// 派生等价保持模型值架构自洽（重放侧 CSR 写经 WARL 合法化会按同一投影重算
/// SD，前态不自洽的值在 emu 内被改写、重放不可比）。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DerivedBitConfig {
    pub bit: u32,
    pub groups: Vec<Vec<u32>>,
}

/// W21：`[symbolic_registers]` 声明的 CSR 符号化条目。寄存器不再从
/// `[registers.defaults]` 取具体值（那里同名即冲突硬失败），改在 solve-state
/// 启动、checkpoint 之前注入 solver 期符号常量（见 target.rs
/// `apply_symbolic_csrs_to_registers`）。
///
/// - `pin_mask`/`pin_value`：位级钉死。注入后附加 `(sym & mask) == value` 断言，
///   钉死位不产生探索分支（如 mstatus 的 MBE/SBE 必须小端、UXL/SXL 固定 64 位）。
/// - `nonzero_groups`：位组非全零域约束。每组断言"组内位按位或 != 0"——用于
///   表达"该位组有探索意义的取值域"（如 mstatus[FS]≠Off：solve-state 绕过
///   decode，执行本体不读 FS，纯符号时模型任意值取 0 会令 encdec 守卫
///   `currentlyEnabled` 恒假；把 FS≠0 声明为取值域是对 decode 守卫语义的
///   最小复刻）。组内位不得与 pin_mask 重叠（钉死位的组约束是恒真或恒假，
///   配置歧义，硬失败）。
/// - `derive_bit`（W22）：派生位等价约束，见 [DerivedBitConfig]。派生位与
///   组内位都不得与 pin_mask 重叠，派生位不得出现在任何组内（自引用退化）。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolicRegisterConfig {
    pub name: String,
    pub pin_mask: u64,
    pub pin_value: u64,
    pub nonzero_groups: Vec<Vec<u32>>,
    pub derive_bit: Option<DerivedBitConfig>,
}

/// P1（plan-bughunt 值域 signposting）：`[[value_hints]]` 声明的维度类别。
/// solve-state 自由求解存在系统性取值退化（成功路径地址恒对齐、基址退化 x0/
/// 低位、源数据初值全零/任意——W24 campaign + B2/B3 归因），错位/边界类 bug
/// 在生成层不可见。维度类别把"哪一类寄存器的取值域需要定向探索"声明为配置。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueHintTarget {
    /// 访存基址寄存器（GPR：x1..x31）——错位、边界±1、低位洞、对齐锚点。
    Base,
    /// 源数据寄存器（向量 vr0..vr31 与浮点 f0..f31）——非零非恒等模式。
    Data,
    /// 向量上下文（vl/vstart）——0/1/典型 VLMAX 界值。
    VectorCtx,
}

/// 内置候选值模式名。展开为具体候选值列表的锚点（PMA/内存区域配置）与展开
/// 规则见 isarch 侧 `value_hints` 模块；配置层只负责名字的合法性。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValuePattern {
    /// PMA 各边界±1（从已注入 [[pma_regions]] 或 [[memory_regions]] 推导）。
    PmaBoundaryPm1,
    /// 按访存宽度（2/4/8/16B）的错位偏移，锚定首个具体区域基址。
    Misaligned,
    /// 低位洞（区域地图之下的低位地址）。
    LowHole,
    /// 区域内对齐锚点（基址、+8、+16、+4KiB）。
    Aligned,
    /// 非零非恒等模式：0xA5 步进 / 0x00FF 掩码 / 全 1 极值三选（跨寄存器
    /// XOR 步进保持源寄存器间可区分——错源类 bug 如 #6486 需要可区分源）。
    NonzeroPattern,
    /// 向量界值：vl ∈ {0,1,8,16,128}、vstart ∈ {0,1}（VLMAX 相对值依赖 vtype，
    /// 钉值机制只能钉常量，见机制说明）。
    VectorBounds,
}

impl ValuePattern {
    fn from_str_name(name: &str) -> Result<Self, String> {
        match name {
            "pma_boundary_pm1" => Ok(ValuePattern::PmaBoundaryPm1),
            "misaligned" => Ok(ValuePattern::Misaligned),
            "low_hole" => Ok(ValuePattern::LowHole),
            "aligned" => Ok(ValuePattern::Aligned),
            "nonzero_pattern" => Ok(ValuePattern::NonzeroPattern),
            "vector_bounds" => Ok(ValuePattern::VectorBounds),
            _ => Err(format!("Unknown value hint pattern {}", name)),
        }
    }
}

/// `[[value_hints]]` 单条声明：一个维度类别 + 候选值来源（内置模式名集合与
/// 显式数值列表的并集）+ 作用域（`clauses` 缺省为全局，条目名按 isarch 的
/// normalize_clause_name 归一后匹配）。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueHintConfig {
    pub target: ValueHintTarget,
    pub patterns: Vec<ValuePattern>,
    pub values: Vec<u64>,
    pub clauses: Option<Vec<String>>,
}

fn get_value_hints(config: &Value) -> Result<Option<Vec<ValueHintConfig>>, String> {
    let Some(value_hints) = config.get("value_hints") else { return Ok(None) };
    let Some(value_hints) = value_hints.as_array() else {
        return Err("value_hints should be an array of tables".to_string());
    };

    let mut hints = Vec::with_capacity(value_hints.len());
    for (index, hint) in value_hints.iter().enumerate() {
        let Some(hint) = hint.as_table() else {
            return Err("value_hints should be an array of tables".to_string());
        };

        allowed_table_keys(hint, "[[value_hints]]", &["target", "patterns", "values", "clauses"])?;

        let context = format!("value_hints[{}]", index);
        let target = match hint.get("target") {
            Some(Value::String(name)) => match name.as_str() {
                "base" => ValueHintTarget::Base,
                "data" => ValueHintTarget::Data,
                "vector_ctx" => ValueHintTarget::VectorCtx,
                _ => return Err(format!("Unknown value hint target {} in {}", name, context)),
            },
            Some(_) => return Err(format!("{}.target should be a string", context)),
            None => return Err(format!("No {}.target found", context)),
        };

        let mut patterns = Vec::new();
        match hint.get("patterns") {
            Some(Value::Array(entries)) => {
                for entry in entries {
                    match entry {
                        Value::String(name) => patterns.push(ValuePattern::from_str_name(name)?),
                        _ => return Err(format!("{}.patterns should be an array of strings", context)),
                    }
                }
            }
            Some(_) => return Err(format!("{}.patterns should be an array of strings", context)),
            None => (),
        }

        let mut values = Vec::new();
        match hint.get("values") {
            Some(Value::Array(entries)) => {
                for entry in entries {
                    values.push(parse_u64_value(entry, &format!("{}.values", context))?);
                }
            }
            Some(_) => return Err(format!("{}.values should be an array of integers", context)),
            None => (),
        }

        if patterns.is_empty() && values.is_empty() {
            return Err(format!("{} 需要 patterns 或 values 至少一项", context));
        }

        let clauses = match hint.get("clauses") {
            Some(Value::Array(entries)) => {
                let mut names = Vec::with_capacity(entries.len());
                for entry in entries {
                    match entry {
                        Value::String(name) => names.push(name.clone()),
                        _ => return Err(format!("{}.clauses should be an array of strings", context)),
                    }
                }
                Some(names)
            }
            Some(_) => return Err(format!("{}.clauses should be an array of strings", context)),
            None => None,
        };

        hints.push(ValueHintConfig { target, patterns, values, clauses });
    }

    Ok(Some(hints))
}

fn get_tool_path(config: &Value, tool: &str) -> Result<Tool, String> {
    match config.get(tool) {
        Some(Value::String(tool)) => {
            let mut words = tool.split_whitespace();
            let program = words.next().ok_or_else(|| format!("Toolchain option {} cannot be an empty string", tool))?;
            Ok(Tool { executable: find_tool_path(program)?, options: words.map(|w| w.to_string()).collect() })
        }
        _ => Err(format!("Toolchain option {} must be specified", tool)),
    }
}

fn parse_u64_value(value: &Value, context: &str) -> Result<u64, String> {
    match value {
        Value::Integer(i) => u64::try_from(*i).map_err(|e| format!("failed to parse integer in {}: {}", context, e)),
        Value::String(s) => {
            if s.len() >= 2 && &s[0..2] == "0x" { u64::from_str_radix(&s[2..], 16) } else { u64::from_str_radix(s, 10) }
                .map_err(|e| format!("Could not parse {} as a 64-bit unsigned integer in {}: {}", s, context, e))
        }
        _ => Err(format!("{} should be an integer or string", context)),
    }
}

fn parse_i64_value(s: &str) -> Result<i64, String> {
    if s.len() >= 2 && &s[0..2] == "0x" { i64::from_str_radix(&s[2..], 16) } else { s.parse::<i64>() }
        .map_err(|e| format!("Could not parse '{}' as i64: {}", s, e))
}

fn parse_aligned_u64_value(value: &Value, context: &str) -> Result<u64, String> {
    let parsed = parse_u64_value(value, context)?;
    if parsed % 4096 != 0 {
        Err(format!("{} must be page-aligned", context))
    } else {
        Ok(parsed)
    }
}

fn get_memory_regions(config: &Value) -> Result<Option<Vec<MemoryRegionConfig>>, String> {
    let Some(memory_regions) = config.get("memory_regions") else { return Ok(None) };
    let Some(memory_regions) = memory_regions.as_array() else {
        return Err("memory_regions should be an array of tables".to_string());
    };

    let regions = memory_regions
        .iter()
        .map(|region| {
            let Some(region) = region.as_table() else {
                return Err("memory_regions should be an array of tables".to_string());
            };

            let name = region
                .get("name")
                .and_then(Value::as_str)
                .ok_or_else(|| "memory_regions.name should be a string".to_string())?
                .to_string();
            let base = region
                .get("base")
                .ok_or_else(|| format!("No memory_regions.base found for region {}", name))
                .and_then(|value| parse_aligned_u64_value(value, &format!("memory_regions.{}.base", name)))?;
            let size = region
                .get("size")
                .ok_or_else(|| format!("No memory_regions.size found for region {}", name))
                .and_then(|value| parse_aligned_u64_value(value, &format!("memory_regions.{}.size", name)))?;
            if size == 0 {
                return Err(format!("memory_regions.{}.size must be greater than 0", name));
            }
            let region_type = region
                .get("region_type")
                .and_then(Value::as_str)
                .ok_or_else(|| "memory_regions.region_type should be a string".to_string())?
                .parse::<MemoryRegionType>()?;

            Ok(MemoryRegionConfig { name, base, size, region_type })
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(Some(regions))
}

/// 解析 `[[pma_regions]]`（W10/S1 配置化 PMA 地图）。返回的列表按 base 降序
/// （与 IR 固化 zpma_regions 列表次序一致），并完成 size/溢出/重叠自校验——
/// isarch 不经过模型的 zcheck_mem_layout，排序与重叠检查必须在配置解析做。
fn get_pma_regions(config: &Value) -> Result<Option<Vec<PmaRegionConfig>>, String> {
    let Some(pma_regions) = config.get("pma_regions") else { return Ok(None) };
    let Some(pma_regions) = pma_regions.as_array() else {
        return Err("pma_regions should be an array of tables".to_string());
    };

    let mut regions = Vec::with_capacity(pma_regions.len());
    for (index, region) in pma_regions.iter().enumerate() {
        let Some(region) = region.as_table() else {
            return Err("pma_regions should be an array of tables".to_string());
        };

        allowed_table_keys(
            region,
            "[[pma_regions]]",
            &[
                "name",
                "base",
                "size",
                "size_bounds",
                "attr",
                "readable",
                "writable",
                "executable",
                "cacheable",
                "coherent",
                "read_idempotent",
                "write_idempotent",
                "supports_cbo_zero",
                "misaligned",
                "reservability",
                "include_in_device_tree",
            ],
        )?;

        let name =
            region.get("name").and_then(Value::as_str).map(str::to_string).unwrap_or_else(|| format!("pma{}", index));
        let context = format!("pma_regions.{}", name);
        let base = region
            .get("base")
            .ok_or_else(|| format!("No {}.base found", context))
            .and_then(|value| parse_u64_value(value, &format!("{}.base", context)))?;
        // S2（W17）：size = "symbolic" 声明符号边界（可选 size_bounds = [下界, 上界]
        // 闭区间），其余写法仍是 W10 的具体十六进制。
        let size = match region.get("size") {
            Some(Value::String(text)) if text == "symbolic" => {
                let (min, max) = match region.get("size_bounds") {
                    None => (SYMBOLIC_SIZE_DEFAULT_MIN, SYMBOLIC_SIZE_DEFAULT_MAX),
                    Some(Value::Array(bounds)) if bounds.len() == 2 => {
                        let min = parse_u64_value(&bounds[0], &format!("{}.size_bounds[0]", context))?;
                        let max = parse_u64_value(&bounds[1], &format!("{}.size_bounds[1]", context))?;
                        (min, max)
                    }
                    Some(_) => {
                        return Err(format!("{}.size_bounds should be an array of two integers", context));
                    }
                };
                if min == 0 {
                    return Err(format!("{}.size_bounds lower bound must be greater than 0", context));
                }
                if min > max {
                    return Err(format!(
                        "{}.size_bounds lower bound 0x{:x} exceeds upper bound 0x{:x}",
                        context, min, max
                    ));
                }
                if base.checked_add(max).is_none() {
                    return Err(format!("{}.base + size_bounds upper bound overflows 64-bit address space", context));
                }
                PmaSize::Symbolic { min, max }
            }
            Some(value) => {
                if region.contains_key("size_bounds") {
                    return Err(format!("{}.size_bounds 只能与 size = \"symbolic\" 搭配", context));
                }
                let size = parse_u64_value(value, &format!("{}.size", context))?;
                if size == 0 {
                    return Err(format!("{}.size must be greater than 0", context));
                }
                if base.checked_add(size).is_none() {
                    return Err(format!("{}.base + size overflows 64-bit address space", context));
                }
                PmaSize::Concrete(size)
            }
            None => return Err(format!("No {}.size found", context)),
        };

        // attr 别名给底座（无 attr 用明细模式基线），明细字段逐项覆盖
        let mut attributes = match region.get("attr") {
            Some(Value::String(alias)) => PmaAttributes::from_alias(alias)
                .ok_or_else(|| format!("Unknown PMA attr alias {} in {}", alias, context))?,
            Some(_) => return Err(format!("{}.attr should be a string", context)),
            None => PmaAttributes::detailed_default(),
        };
        let mut has_detail = false;
        let bool_field = |region: &toml::value::Table, key: &str| -> Result<Option<bool>, String> {
            match region.get(key) {
                Some(Value::Boolean(b)) => Ok(Some(*b)),
                Some(_) => Err(format!("{}.{} should be a boolean", context, key)),
                None => Ok(None),
            }
        };
        for (key, target) in [
            ("readable", &mut attributes.readable),
            ("writable", &mut attributes.writable),
            ("executable", &mut attributes.executable),
            ("cacheable", &mut attributes.cacheable),
            ("coherent", &mut attributes.coherent),
            ("read_idempotent", &mut attributes.read_idempotent),
            ("write_idempotent", &mut attributes.write_idempotent),
            ("supports_cbo_zero", &mut attributes.supports_cbo_zzero),
            ("include_in_device_tree", &mut attributes.include_in_device_tree),
        ] {
            if let Some(value) = bool_field(region, key)? {
                *target = value;
                has_detail = true;
            }
        }
        match region.get("misaligned") {
            Some(Value::String(s)) => {
                attributes.misaligned_fault = s.parse::<PmaMisalignedFault>()?;
                has_detail = true;
            }
            Some(_) => return Err(format!("{}.misaligned should be a string", context)),
            None => (),
        }
        match region.get("reservability") {
            Some(Value::String(s)) => {
                attributes.reservability = s.parse::<PmaReservability>()?;
                has_detail = true;
            }
            Some(_) => return Err(format!("{}.reservability should be a string", context)),
            None => (),
        }
        if !region.contains_key("attr") && !has_detail {
            return Err(format!("{} 需要 attr 别名或至少一个明细属性字段", context));
        }

        regions.push(PmaRegionConfig { name, base, size, attributes });
    }

    // 按 base 降序（IR 固化 zpma_regions 的列表次序），再做相邻重叠检查。
    // 区间按起点排序后，任意重叠必然产生一对相邻重叠。符号 size 用取值域上界
    // 参与检查（保守：任意模型取值下都不重叠）。
    regions.sort_by(|a, b| b.base.cmp(&a.base));
    for pair in regions.windows(2) {
        let (upper, lower) = (&pair[0], &pair[1]);
        let lower_end = lower.base.checked_add(lower.size.upper_bound()).expect("已校验 base+size 上界不溢出");
        if lower_end > upper.base {
            return Err(format!(
                "pma_regions.{} [0x{:x},0x{:x}) 与 pma_regions.{} [0x{:x},0x{:x}) 重叠",
                upper.name,
                upper.base,
                upper.base + upper.size.upper_bound(),
                lower.name,
                lower.base,
                lower_end
            ));
        }
    }

    Ok(Some(regions))
}

fn get_page_table_config(config: &Value) -> Result<Option<PageTableConfig>, String> {
    let Some(page_table_config) = config.get("page_table_config") else { return Ok(None) };
    let Some(page_table_config) = page_table_config.as_table() else {
        return Err("page_table_config should be a table".to_string());
    };

    let mode = page_table_config
        .get("mode")
        .and_then(Value::as_str)
        .ok_or_else(|| "page_table_config.mode should be a string".to_string())?
        .parse::<PageTableMode>()?;
    let preset = page_table_config
        .get("preset")
        .and_then(Value::as_str)
        .ok_or_else(|| "page_table_config.preset should be a string".to_string())?
        .parse::<PageTablePreset>()?;
    let base = page_table_config
        .get("base")
        .ok_or_else(|| "No page_table_config.base found in config".to_string())
        .and_then(|value| parse_aligned_u64_value(value, "page_table_config.base"))?;
    let page_size = page_table_config
        .get("page_size")
        .ok_or_else(|| "No page_table_config.page_size found in config".to_string())
        .and_then(|value| parse_aligned_u64_value(value, "page_table_config.page_size"))?;
    if page_size != 4096 {
        return Err(format!("page_table_config.page_size must be 4096, got {}", page_size));
    }
    let offset = match page_table_config.get("offset") {
        Some(Value::Integer(i)) => Some(*i),
        Some(Value::String(s)) => Some(parse_i64_value(s)?),
        Some(_) => return Err("page_table_config.offset should be an integer or string".to_string()),
        None => None,
    };
    let protected_ranges = match page_table_config.get("protected_ranges") {
        None => None,
        Some(value) => {
            let Some(ranges) = value.as_array() else {
                return Err("page_table_config.protected_ranges should be an array of tables".to_string());
            };
            Some(
                ranges
                    .iter()
                    .map(|range| {
                        let Some(range) = range.as_table() else {
                            return Err("page_table_config.protected_ranges should be an array of tables".to_string());
                        };
                        let base = range
                            .get("base")
                            .ok_or_else(|| "No page_table_config.protected_ranges.base found in config".to_string())
                            .and_then(|value| {
                                parse_aligned_u64_value(value, "page_table_config.protected_ranges.base")
                            })?;
                        let size = range
                            .get("size")
                            .ok_or_else(|| "No page_table_config.protected_ranges.size found in config".to_string())
                            .and_then(|value| {
                                parse_aligned_u64_value(value, "page_table_config.protected_ranges.size")
                            })?;
                        if size == 0 {
                            return Err("page_table_config.protected_ranges.size must be greater than 0".to_string());
                        }
                        let flags = range
                            .get("flags")
                            .and_then(Value::as_str)
                            .ok_or_else(|| "page_table_config.protected_ranges.flags should be a string".to_string())?
                            .to_string();
                        Ok(ProtectedRange { base, size, flags })
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            )
        }
    };

    Ok(Some(PageTableConfig { mode, preset, base, page_size, offset, protected_ranges }))
}

// The current RISC-V IR snapshots expose PMP register families as `zpmpcfg_n` and `zpmpaddr_n`
// in the IR, with concrete architectural names `pmpcfg0`..`pmpcfg15` and `pmpaddr0`..`pmpaddr63`.
// Use the concrete names when looking up symbols, and note the family form for the generated IR.
fn get_pmp_config(config: &Value) -> Result<Option<PmpConfig>, String> {
    let Some(pmp_config) = config.get("pmp") else { return Ok(None) };
    let Some(pmp_config) = pmp_config.as_table() else {
        return Err("pmp should be a table".to_string());
    };

    allowed_table_keys(pmp_config, "[pmp]", &["symbolic", "rules"])?;

    let symbolic = match pmp_config.get("symbolic") {
        Some(Value::Boolean(b)) => *b,
        Some(_) => return Err("pmp.symbolic should be a boolean".to_string()),
        None => false,
    };

    let rules = match pmp_config.get("rules") {
        None => Vec::new(),
        Some(value) => {
            let Some(rules) = value.as_array() else {
                return Err("pmp.rules should be an array of tables".to_string());
            };

            rules
                .iter()
                .map(|rule| {
                    let Some(rule) = rule.as_table() else {
                        return Err("pmp.rules should be an array of tables".to_string());
                    };

                    allowed_table_keys(
                        rule,
                        "[[pmp.rules]]",
                        &["index", "mode", "base", "size", "permissions", "locked"],
                    )?;

                    let index = rule
                        .get("index")
                        .and_then(Value::as_integer)
                        .ok_or_else(|| "pmp.rules.index should be an integer".to_string())
                        .and_then(|i| {
                            u32::try_from(i).map_err(|e| format!("failed to parse integer in pmp.rules.index: {}", e))
                        })?;
                    if index >= 64 {
                        return Err(format!("pmp.rules.index must be < 64, got {}", index));
                    }
                    let mode = rule
                        .get("mode")
                        .and_then(Value::as_str)
                        .ok_or_else(|| "pmp.rules.mode should be a string".to_string())?
                        .parse::<PmpMode>()?;
                    let base = rule
                        .get("base")
                        .ok_or_else(|| format!("No pmp.rules.base found for index {}", index))
                        .and_then(|value| parse_u64_value(value, &format!("pmp.rules[{}].base", index)))?;
                    let size = match rule.get("size") {
                        Some(value) => Some(parse_u64_value(value, &format!("pmp.rules[{}].size", index))?),
                        None => None,
                    };
                    if matches!(mode, PmpMode::Napot) && size.is_none() {
                        return Err(format!("pmp.rules[{}].size is required for napot mode", index));
                    }
                    if matches!(mode, PmpMode::Napot) {
                        if let Some(size) = size {
                            if size < 8 {
                                return Err(format!("pmp.rules[{}].size must be >= 8 for NAPOT, got {}", index, size));
                            }
                            if !size.is_power_of_two() {
                                return Err(format!(
                                    "pmp.rules[{}].size must be a power of 2 for NAPOT, got {}",
                                    index, size
                                ));
                            }
                            if base % size != 0 {
                                return Err(format!(
                                    "pmp.rules[{}].base 0x{:x} must be aligned to size 0x{:x}",
                                    index, base, size
                                ));
                            }
                        }
                    }
                    let permissions = rule
                        .get("permissions")
                        .and_then(Value::as_str)
                        .ok_or_else(|| "pmp.rules.permissions should be a string".to_string())?
                        .to_string();
                    if permissions.contains('w') && !permissions.contains('r') {
                        return Err(format!(
                            "pmp.rules[{}].permissions 'w' requires 'r' (W=1,R=0 is reserved in RISC-V)",
                            index
                        ));
                    }
                    let locked = match rule.get("locked") {
                        Some(Value::Boolean(b)) => *b,
                        Some(_) => return Err("pmp.rules.locked should be a boolean".to_string()),
                        None => false,
                    };

                    Ok(PmpRule { index, mode, base, size, permissions, locked })
                })
                .collect::<Result<Vec<_>, _>>()?
        }
    };

    Ok(Some(PmpConfig { rules, symbolic }))
}

fn get_clint_enabled(config: &Value) -> Result<Option<bool>, String> {
    match config.get("clint_enabled") {
        Some(value) => value.as_bool().map(Some).ok_or_else(|| "clint_enabled should be a boolean".to_string()),
        None => Ok(None),
    }
}

/// 解析 `[symbolic_registers]`（W21）。每个键是寄存器名（须存在于 symtab，
/// 否则硬失败——静默跳过会让用户误以为已符号化）；值二选一：
///
/// ```toml
/// [symbolic_registers]
/// mstatus = "symbolic"                    # 整寄存器符号化，无位约束
///
/// [symbolic_registers.mstatus]            # 表形式：位级钉死 + 位组域 + 派生位
/// pin_mask  = "0x0000183C00000000"        # MBE(37)|SBE(36)|UXL(44:43)|SXL(35:34)
/// pin_value = "0x0000100800000000"        # 小端 + XLEN=64
/// nonzero_groups = [[13, 14]]             # FS != Off
/// derive_bit = { bit = 63, groups = [[14, 13], [10, 9], [16, 15]] }  # SD 派生
/// ```
///
/// 与 `[registers.defaults]` 同名冲突（含 PMP 规则注入的 pmpcfg/pmpaddr，
/// 那部分由 isarch_main 在注入后复查）在本函数按解析期已知的 defaults
/// 硬失败；PMP 注入晚于解析，其冲突由调用方兜底。
fn get_symbolic_registers<B: BV>(
    config: &Value,
    symtab: &Symtab,
    default_registers: &HashMap<Name, Val<B>>,
) -> Result<Vec<SymbolicRegisterConfig>, String> {
    let Some(section) = config.get("symbolic_registers") else { return Ok(Vec::new()) };
    let Some(table) = section.as_table() else {
        return Err("symbolic_registers should be a table of <register> = \"symbolic\" or sub-tables".to_string());
    };

    let mut registers = Vec::new();
    for (name, entry) in table {
        let Some(register) = symtab.get(&zencode::encode(name)) else {
            return Err(format!("symbolic_registers.{}：当前 IR 不存在该寄存器", name));
        };
        if default_registers.contains_key(&register) {
            return Err(format!(
                "symbolic_registers.{} 与 registers.defaults 同名冲突：符号化寄存器不得同时配置具体默认值",
                name
            ));
        }

        let mut pin_mask = 0;
        let mut pin_value = 0;
        let mut nonzero_groups = Vec::new();
        let mut derive_bit = None;
        match entry {
            Value::String(text) if text == "symbolic" => (),
            Value::String(other) => {
                return Err(format!(
                    "symbolic_registers.{} 只接受 \"symbolic\" 字符串或子表，实际 \"{}\"",
                    name, other
                ));
            }
            Value::Table(sub) => {
                allowed_table_keys(
                    sub,
                    &format!("symbolic_registers.{}", name),
                    &["pin_mask", "pin_value", "nonzero_groups", "derive_bit"],
                )?;
                if let Some(value) = sub.get("pin_mask") {
                    pin_mask = parse_u64_value(value, &format!("symbolic_registers.{}.pin_mask", name))?;
                    pin_value = match sub.get("pin_value") {
                        Some(value) => parse_u64_value(value, &format!("symbolic_registers.{}.pin_value", name))?,
                        None => return Err(format!("symbolic_registers.{}.pin_value 与 pin_mask 必须同时配置", name)),
                    };
                    if pin_value & !pin_mask != 0 {
                        return Err(format!(
                            "symbolic_registers.{}.pin_value 0x{:x} 含 pin_mask 0x{:x} 之外的位",
                            name, pin_value, pin_mask
                        ));
                    }
                } else if sub.contains_key("pin_value") {
                    return Err(format!("symbolic_registers.{}.pin_value 与 pin_mask 必须同时配置", name));
                }
                if let Some(value) = sub.get("nonzero_groups") {
                    let Some(groups) = value.as_array() else {
                        return Err(format!("symbolic_registers.{}.nonzero_groups 应为位数组的数组", name));
                    };
                    for group in groups {
                        let Some(bits) = group.as_array() else {
                            return Err(format!("symbolic_registers.{}.nonzero_groups 的每个组应为位数组", name));
                        };
                        if bits.is_empty() {
                            return Err(format!("symbolic_registers.{}.nonzero_groups 不接受空组", name));
                        }
                        let mut parsed_group = Vec::with_capacity(bits.len());
                        for bit in bits {
                            let Some(index) = bit.as_integer() else {
                                return Err(format!("symbolic_registers.{}.nonzero_groups 的位应为非负整数", name));
                            };
                            let Ok(index) = u32::try_from(index) else {
                                return Err(format!("symbolic_registers.{}.nonzero_groups 位号超出 u32", name));
                            };
                            if index >= 64 {
                                return Err(format!(
                                    "symbolic_registers.{}.nonzero_groups 位号 {} 超出 64 位 CSR 宽度",
                                    name, index
                                ));
                            }
                            if pin_mask >> index & 1 == 1 {
                                return Err(format!(
                                    "symbolic_registers.{}.nonzero_groups 位 {} 与 pin_mask 钉死位重叠",
                                    name, index
                                ));
                            }
                            parsed_group.push(index);
                        }
                        nonzero_groups.push(parsed_group);
                    }
                }
                derive_bit = parse_derive_bit(sub, &format!("symbolic_registers.{}", name), pin_mask)?;
            }
            _ => {
                return Err(format!("symbolic_registers.{} 只接受 \"symbolic\" 字符串或子表，实际 {}", name, entry));
            }
        }

        if registers.iter().any(|existing: &SymbolicRegisterConfig| &existing.name == name) {
            return Err(format!("symbolic_registers.{} 重复声明", name));
        }
        registers.push(SymbolicRegisterConfig {
            name: name.to_string(),
            pin_mask,
            pin_value,
            nonzero_groups,
            derive_bit,
        });
    }
    // toml 表迭代按字典序：显式排序保证注入次序与输出确定性
    registers.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(registers)
}

/// 解析 `derive_bit = { bit, groups }`（W22）。位号/组形状/与 pin_mask 的
/// 冲突/自引用都在这里硬失败；与实际寄存器位宽的比较在注入期（配置期不知宽）。
fn parse_derive_bit(sub: &toml::value::Table, root: &str, pin_mask: u64) -> Result<Option<DerivedBitConfig>, String> {
    let Some(value) = sub.get("derive_bit") else { return Ok(None) };
    let table = value.as_table().ok_or_else(|| format!("{}.derive_bit 应为 {{ bit, groups }} 表", root))?;
    allowed_table_keys(table, &format!("{}.derive_bit", root), &["bit", "groups"])?;

    let bit =
        table.get("bit").and_then(Value::as_integer).ok_or_else(|| format!("{}.derive_bit.bit 应为非负整数", root))?;
    let Ok(bit) = u32::try_from(bit) else {
        return Err(format!("{}.derive_bit.bit 位号超出 u32", root));
    };
    if bit >= 64 {
        return Err(format!("{}.derive_bit.bit 位号 {} 超出 64 位 CSR 宽度", root, bit));
    }
    if pin_mask >> bit & 1 == 1 {
        return Err(format!("{}.derive_bit.bit 位 {} 与 pin_mask 钉死位重叠：派生位不得再钉死", root, bit));
    }

    let groups_value = table.get("groups").ok_or_else(|| format!("{}.derive_bit.groups 是必填项", root))?;
    let groups_raw = groups_value.as_array().ok_or_else(|| format!("{}.derive_bit.groups 应为位数组的数组", root))?;
    if groups_raw.is_empty() {
        return Err(format!(
            "{}.derive_bit.groups 不接受空数组：无组的派生等价于把派生位钉 0，请直接用 pin_mask",
            root
        ));
    }

    let mut groups = Vec::with_capacity(groups_raw.len());
    for group in groups_raw {
        let bits = group.as_array().ok_or_else(|| format!("{}.derive_bit.groups 的每个组应为位数组", root))?;
        if bits.is_empty() {
            return Err(format!("{}.derive_bit.groups 不接受空组", root));
        }
        let mut parsed_group = Vec::with_capacity(bits.len());
        for bit_value in bits {
            let index = bit_value.as_integer().ok_or_else(|| format!("{}.derive_bit.groups 的位应为非负整数", root))?;
            let Ok(index) = u32::try_from(index) else {
                return Err(format!("{}.derive_bit.groups 位号超出 u32", root));
            };
            if index >= 64 {
                return Err(format!("{}.derive_bit.groups 位号 {} 超出 64 位 CSR 宽度", root, index));
            }
            if pin_mask >> index & 1 == 1 {
                return Err(format!("{}.derive_bit.groups 位 {} 与 pin_mask 钉死位重叠", root, index));
            }
            if index == bit {
                return Err(format!("{}.derive_bit 派生位 {} 出现在组内：自引用等价无法表达镜像语义", root, bit));
            }
            parsed_group.push(index);
        }
        groups.push(parsed_group);
    }

    Ok(Some(DerivedBitConfig { bit, groups }))
}

struct Toolchain {
    assembler: Tool,
    objdump: Tool,
    nm: Tool,
    linker: Tool,
}

fn get_toolchain(config: &Value, chosen: Option<&str>) -> Result<Toolchain, String> {
    use std::env::consts::*;

    // if we don't have a [[toolchain]] array just try to get values from the toplevel
    let Some(Value::Array(toolchains)) = config.get("toolchain") else {
        return Ok(Toolchain {
            assembler: get_tool_path(config, "assembler")?,
            objdump: get_tool_path(config, "objdump")?,
            nm: get_tool_path(config, "nm")?,
            linker: get_tool_path(config, "linker")?,
        });
    };

    for toolchain in toolchains {
        allowed_keys(toolchain, "[[toolchain]]", &["name", "os", "arch", "assembler", "objdump", "linker", "nm"])?;
    }

    for toolchain in toolchains {
        let Some(name) = toolchain.get("name").and_then(Value::as_str) else {
            return Err("toolchain entry must have a name field".to_string());
        };

        let os = match toolchain.get("os") {
            Some(Value::String(os)) => Some(os),
            None => None,
            Some(_) => return Err("os key must be a string in toolchain definition".to_string()),
        };

        let arch = match toolchain.get("arch") {
            Some(Value::String(arch)) => Some(arch),
            None => None,
            Some(_) => return Err("arch key must be a string in toolchain definition".to_string()),
        };

        let usable_toolchain = if let Some(chosen_name) = chosen {
            name == chosen_name
        } else {
            match (os, arch) {
                (Some(os), Some(arch)) => os == OS && arch == ARCH,
                (Some(os), None) => os == OS,
                (None, Some(arch)) => arch == ARCH,
                (None, None) => true,
            }
        };

        if usable_toolchain {
            return Ok(Toolchain {
                assembler: get_tool_path(toolchain, "assembler")?,
                objdump: get_tool_path(toolchain, "objdump")?,
                nm: get_tool_path(toolchain, "nm")?,
                linker: get_tool_path(toolchain, "linker")?,
            });
        }
    }

    if let Some(chosen_name) = chosen {
        Err(format!("Configuration file did not contain a usable toolchain named {}", chosen_name))
    } else {
        Err(format!("Configuration file did not contain a usable toolchain for os = {}, arch = {}", OS, ARCH))
    }
}

/// Get the program counter from the ISA config, and map it to the
/// correct register identifer in the symbol table.
fn get_program_counter(config: &Value, symtab: &Symtab) -> Result<Name, String> {
    match config.get("pc") {
        Some(Value::String(register)) => match symtab.get(&zencode::encode(register)) {
            Some(symbol) => Ok(symbol),
            None => Err(format!("Register {} does not exist in supplied architecture", register)),
        },
        _ => Err("Configuration file must specify the program counter via `pc = \"REGISTER_NAME\"`".to_string()),
    }
}

fn get_zero_announce_exit(config: &Value) -> Result<bool, String> {
    match config.get("zero_announce_exit") {
        Some(Value::Boolean(b)) => Ok(*b),
        Some(_) => Err("zero_announce_exit must have a boolean value if it exists in configuration".to_string()),
        None => Ok(false),
    }
}

macro_rules! event_kinds_in_table {
    ($events: ident, $kind: path, $event_str: expr, $result: ident, $symtab: ident) => {
        for (k, sets) in $events {
            let k = $symtab
                .get(&zencode::encode(k))
                .ok_or_else(|| format!(concat!("Could not find ", $event_str, " {} in architecture"), k))?;
            let sets = match sets.as_str() {
                Some(set) => vec![set],
                None => sets
                    .as_array()
                    .and_then(|sets| sets.iter().map(|set| set.as_str()).collect::<Option<Vec<_>>>())
                    .ok_or_else(|| {
                        format!(concat!(
                            "Each ",
                            $event_str,
                            " in [",
                            $event_str,
                            "s] must specify at least one cat set"
                        ))
                    })?,
            };
            for set in sets.into_iter() {
                match $result.get_mut(set) {
                    None => {
                        $result.insert(set.to_string(), vec![$kind(k)]);
                    }
                    Some(kinds) => kinds.push($kind(k)),
                }
            }
        }
    };
}

pub enum RegisterKind {
    Read(Name),
    Write(Name),
}

impl RegisterKind {
    pub fn is_read(&self) -> bool {
        matches!(self, RegisterKind::Read(_))
    }

    pub fn is_write(&self) -> bool {
        matches!(self, RegisterKind::Write(_))
    }

    pub fn name(&self) -> Name {
        match self {
            RegisterKind::Read(n) => *n,
            RegisterKind::Write(n) => *n,
        }
    }
}

fn get_register_event_sets(config: &Value, symtab: &Symtab) -> Result<HashMap<String, Vec<RegisterKind>>, String> {
    let empty = toml::value::Map::new();

    let register_reads = config
        .get("registers")
        .and_then(Value::as_table)
        .and_then(|registers| registers.get("read_events"))
        .and_then(Value::as_table)
        .unwrap_or(&empty);
    let register_writes = config
        .get("registers")
        .and_then(Value::as_table)
        .and_then(|registers| registers.get("write_events"))
        .and_then(Value::as_table)
        .unwrap_or(&empty);

    let mut result: HashMap<String, Vec<RegisterKind>> = HashMap::new();

    event_kinds_in_table!(register_reads, RegisterKind::Read, "register name", result, symtab);
    event_kinds_in_table!(register_writes, RegisterKind::Write, "register name", result, symtab);

    Ok(result)
}

#[allow(clippy::from_str_radix_10)]
fn get_table_value(config: &Value, table: &str, key: &str) -> Result<u64, String> {
    config
        .get(table)
        .and_then(|table| table.get(key).and_then(|value| value.as_str()))
        .ok_or_else(|| format!("No {}.{} found in config", table, key))
        .and_then(|value| {
            if value.len() >= 2 && &value[0..2] == "0x" {
                u64::from_str_radix(&value[2..], 16)
            } else {
                u64::from_str_radix(value, 10)
            }
            .map_err(|e| format!("Could not parse {} as a 64-bit unsigned integer in {}.{}: {}", value, table, key, e))
        })
}

fn get_table_string(config: &Value, table: &str, key: &str) -> Result<String, String> {
    config
        .get(table)
        .and_then(|table| table.get(key).and_then(|value| value.as_str()))
        .ok_or_else(|| format!("No {}.{} found in config", table, key))
        .map(|value| value.to_string())
}

fn from_toml_value<B: BV>(value: &Value, symtab: &Symtab<'_>, type_info: &IRTypeInfo) -> Result<Val<B>, String> {
    match value {
        Value::Boolean(b) => Ok(Val::Bool(*b)),
        Value::Integer(i) => Ok(Val::I128(*i as i128)),
        Value::String(s) => match ValParser::new().parse(symtab, type_info, new_ir_lexer(s)) {
            Ok(value) => Ok(value),
            Err(e) => Err(format!("Parse error when reading register value from configuration: {}", e)),
        },
        _ => Err(format!("Could not parse TOML value {} as register value", value)),
    }
}

fn from_toml_value_undef<B: BV>(
    value: &Value,
    symtab: &Symtab<'_>,
    type_info: &IRTypeInfo,
) -> Result<URVal<B>, String> {
    match value {
        Value::Boolean(b) => Ok(URVal::Init(Val::Bool(*b))),
        Value::Integer(i) => Ok(URVal::Init(Val::I128(*i as i128))),
        Value::String(s) => match URValParser::new().parse(symtab, type_info, new_ir_lexer(s)) {
            Ok(value) => Ok(value),
            Err(e) => Err(format!("Parse error when reading register value from configuration: {}", e)),
        },
        _ => Err(format!("Could not parse TOML value {} as register value", value)),
    }
}

fn get_default_registers<B: BV>(
    config: &Value,
    symtab: &Symtab,
    type_info: &IRTypeInfo,
) -> Result<HashMap<Name, Val<B>>, String> {
    let defaults = config
        .get("registers")
        .and_then(|registers| registers.as_table())
        .and_then(|registers| registers.get("defaults"));

    if let Some(defaults) = defaults {
        if let Some(defaults) = defaults.as_table() {
            defaults
                .into_iter()
                .filter_map(|(register, value)| {
                    if let Some(register) = symtab.get(&zencode::encode(register)) {
                        match from_toml_value(value, symtab, type_info) {
                            Ok(value) => Some(Ok((register, value))),
                            Err(e) => Some(Err(e)),
                        }
                    } else {
                        eprintln!(
                            "Warning: Could not find register {} when parsing registers.defaults in configuration",
                            register
                        );
                        None
                    }
                })
                .collect()
        } else {
            Err("registers.defaults should be a table of <register> = <value> pairs".to_string())
        }
    } else {
        Ok(HashMap::new())
    }
}

fn get_const_primops<B: BV>(
    config: &Value,
    symtab: &Symtab,
    type_info: &IRTypeInfo,
) -> Result<HashMap<String, Reset<B>>, String> {
    let defaults = config.get("const_primops");

    if let Some(defaults) = defaults {
        if let Some(defaults) = defaults.as_table() {
            defaults
                .into_iter()
                .map(|(primop, value)| match reset_to_toml_value(value, symtab, type_info) {
                    Ok(value) => Ok((primop.clone(), value)),
                    Err(e) => Err(e),
                })
                .collect()
        } else {
            Err("const_primops should be a table of <primop> = <value> pairs".to_string())
        }
    } else {
        Ok(HashMap::new())
    }
}

pub fn reset_to_toml_value<B: BV>(
    value: &Value,
    symtab: &Symtab<'_>,
    type_info: &IRTypeInfo,
) -> Result<Reset<B>, String> {
    let v = from_toml_value_undef::<B>(value, symtab, type_info)?;
    Ok(Arc::new(move |_, typedefs, solver| match &v {
        URVal::Init(value) => Ok(value.clone()),
        URVal::Uninit(ty) => symbolic_from_typedefs(ty, typedefs, solver, SourceLoc::command_line()),
    }))
}

pub type Resets<B> = Vec<(Loc<Name>, Reset<B>)>;

pub fn toml_reset_registers<B: BV>(toml: &Value, symtab: &Symtab, type_info: &IRTypeInfo) -> Result<Resets<B>, String> {
    if let Some(defaults) = toml.as_table() {
        defaults
            .into_iter()
            .map(|(register, value)| {
                if let Ok(loc) = LocParser::new().parse::<B, _, _>(symtab, type_info, new_ir_lexer(register)) {
                    if let Some(loc) = symtab.get_loc(&loc) {
                        Ok((loc, reset_to_toml_value(value, symtab, type_info)?))
                    } else {
                        Err(format!("Could not find register {} when parsing register reset information", register))
                    }
                } else {
                    Err(format!("Could not parse register {} when parsing register reset information", register))
                }
            })
            .collect()
    } else {
        Err("registers.reset should be a table of <register> = <value> pairs".to_string())
    }
}

fn get_reset_registers<B: BV>(config: &Value, symtab: &Symtab, type_info: &IRTypeInfo) -> Result<Resets<B>, String> {
    let defaults =
        config.get("registers").and_then(|registers| registers.as_table()).and_then(|registers| registers.get("reset"));

    if let Some(defaults) = defaults {
        toml_reset_registers(defaults, symtab, type_info)
    } else {
        Ok(Vec::new())
    }
}

fn get_reset_constraints(config: &Value) -> Result<Vec<Exp<Loc<String>>>, String> {
    let reset_toml =
        config.get("constraints").and_then(|section| section.as_table()).and_then(|section| section.get("reset"));
    if let Some(toml) = reset_toml {
        let constraints = toml
            .as_array()
            .and_then(|vec| vec.iter().map(|item| item.as_str()).collect::<Option<Vec<_>>>())
            .ok_or_else(|| "constraints.reset should be an array of constraint strings".to_string())?;
        constraints
            .iter()
            .map(|constraint| smt_parser::ExpParser::new().parse(constraint).map_err(|err| err.to_string()))
            .collect::<Result<Vec<_>, _>>()
    } else {
        Ok(Vec::new())
    }
}

fn get_register_renames(config: &Value, symtab: &Symtab) -> Result<HashMap<String, Name>, String> {
    let defaults = config
        .get("registers")
        .and_then(|registers| registers.as_table())
        .and_then(|registers| registers.get("renames"));

    if let Some(defaults) = defaults {
        if let Some(defaults) = defaults.as_table() {
            defaults
                .into_iter()
                .map(|(name, register)| {
                    if let Some(register) = register.as_str().and_then(|r| symtab.get(&zencode::encode(r))) {
                        Ok((name.to_string(), register))
                    } else {
                        Err(format!(
                            "Could not find register {} when parsing registers.renames in configuration",
                            register
                        ))
                    }
                })
                .collect()
        } else {
            Err("registers.names should be a table or <name> = <register> pairs".to_string())
        }
    } else {
        Ok(HashMap::new())
    }
}

fn get_translation_function(config: &Value, symtab: &Symtab) -> Result<Option<Name>, String> {
    if let Some(value) = config.get("translation_function") {
        if let Some(string) = value.as_str() {
            if let Some(name) = symtab.get(&zencode::encode(string)) {
                Ok(Some(name))
            } else {
                Err(format!("function {} does not exist in supplied architecture", string))
            }
        } else {
            Err("translation_function must be a string".to_string())
        }
    } else {
        Ok(None)
    }
}

fn get_trace_functions(config: &Value, symtab: &Symtab) -> Result<HashSet<Name>, String> {
    let trace = config.get("trace");

    if let Some(trace) = trace {
        if let Some(trace) = trace.as_array() {
            trace
                .iter()
                .map(|function| {
                    if let Some(function) = function.as_str().and_then(|f| symtab.get(&zencode::encode(f))) {
                        Ok(function)
                    } else {
                        Err(format!("Could not find function {} when parsing trace in configuration", function))
                    }
                })
                .collect()
        } else {
            Err("trace should be a list of function names".to_string())
        }
    } else {
        Ok(HashSet::new())
    }
}

fn get_registers_set<C>(config: &Value, set_name: &str, symtab: &Symtab) -> Result<C, String>
where
    C: FromIterator<Name> + Default,
{
    let ignored = config
        .get("registers")
        .and_then(|registers| registers.as_table())
        .and_then(|registers| registers.get(set_name));

    if let Some(ignored) = ignored {
        if let Some(ignored) = ignored.as_array() {
            ignored
                .iter()
                .map(|register| {
                    if let Some(register) = register.as_str().and_then(|r| symtab.get(&zencode::encode(r))) {
                        Ok(register)
                    } else {
                        Err(format!(
                            "Could not find register {} when parsing registers.{} in configuration",
                            register, set_name
                        ))
                    }
                })
                .collect()
        } else {
            Err(format!("registers.{} should be a list of register names", set_name))
        }
    } else {
        Ok(C::default())
    }
}

fn get_in_program_order(config: &Value, symtab: &Symtab) -> Result<HashSet<Name>, String> {
    let mut events = HashSet::new();

    let Some(in_po) = config.get("in_program_order") else { return Ok(events) };

    let Some(event_names) = in_po.as_array() else {
        return Err("in_program_order should be an array in configuration".to_string());
    };

    for event_name in event_names {
        let Some(s) = event_name.as_str() else {
            return Err("in_program_order should contain strings in configuration".to_string());
        };

        let Some(name) = symtab.get(&zencode::encode(s)) else {
            return Err(format!("{} is not a known event name for in_program_order in configuration", s));
        };

        events.insert(name);
    }

    Ok(events)
}

fn get_default_sizeof(config: &Value) -> Result<u32, String> {
    let Some(v) = config.get("default_sizeof") else { return Ok(4) };
    let Some(i) = v.as_integer() else { return Err("default_sizeof should be an integer".to_string()) };
    match u32::try_from(i) {
        Ok(n) => Ok(n),
        Err(e) => Err(format!("failed to parse integer in default_sizeof: {}", e)),
    }
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct ExecutionLimitsConfig {
    pub strict: bool,
    pub ir_sha256: Option<String>,
    pub enabled: Option<bool>,
    pub max_forks_per_branch: Option<u32>,
    pub max_forks_per_path: Option<u32>,
    pub max_backjumps_per_loop: Option<u32>,
    pub max_path_depth: Option<u64>,
    pub max_fork_pct_per_branch: Option<f64>,
    pub max_fork_pct_check_delay: Option<u32>,
    pub call_context_depth: Option<usize>,
    pub branch_sampling_seed: Option<u64>,
    pub on_limit_reached: Option<LimitBehaviorConfig>,
    pub regions: Option<Vec<SourceRegionSpec>>,
    pub branch_region_limits: Option<Vec<BranchRegionLimitConfig>>,
    pub region_fork_limits: Option<Vec<RegionForkLimitConfig>>,
    /// 输出层按 `ret_val` 构造子分类的用例配额，由 isarch 收尾阶段消费。
    pub case_quota: Option<BTreeMap<String, u32>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchRegionLimitConfig {
    pub max_forks_per_branch: u32,
    pub region: SourceRegionSpec,
}

/// 一条路径在整段源码区间内总共允许的 fork 次数。与 `BranchRegionLimitConfig` 的区别是
/// 预算由区间内所有分支点共享，因此能压住 `match` 链这种"每个 arm 判定都是独立分支点"的
/// 展开：预算 N 对应 N+1 个取值。
///
/// `sample_bias` 是可选的具体化方向偏置 `(分母, 方向)`：预算耗尽后的具体化抽样默认是 50/50，
/// 配了偏置就只有 `1/分母` 的路径会抽到指定方向。方向 `true` = 跳转到 target，
/// `false` = 顺序执行下一条。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegionForkLimitConfig {
    pub max_forks_per_region: u32,
    pub sample_bias: Option<(u32, bool)>,
    pub region: SourceRegionSpec,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LimitBehaviorConfig {
    Truncate,
    Concretize,
}

fn optional_bool(table: &toml::value::Table, key: &str, root: &str) -> Result<Option<bool>, String> {
    table.get(key).map(|value| value.as_bool().ok_or_else(|| format!("{}.{} 必须是布尔值", root, key))).transpose()
}

fn optional_u32(table: &toml::value::Table, key: &str, root: &str) -> Result<Option<u32>, String> {
    table
        .get(key)
        .map(|value| {
            let value = value.as_integer().ok_or_else(|| format!("{}.{} 必须是非负整数", root, key))?;
            u32::try_from(value).map_err(|_| format!("{}.{} 超出 u32 范围", root, key))
        })
        .transpose()
}

fn optional_u64(table: &toml::value::Table, key: &str, root: &str) -> Result<Option<u64>, String> {
    table
        .get(key)
        .map(|value| {
            let value = value.as_integer().ok_or_else(|| format!("{}.{} 必须是非负整数", root, key))?;
            u64::try_from(value).map_err(|_| format!("{}.{} 超出 u64 范围", root, key))
        })
        .transpose()
}

fn optional_sha256(table: &toml::value::Table, key: &str, root: &str) -> Result<Option<String>, String> {
    table
        .get(key)
        .map(|value| {
            let value = value.as_str().ok_or_else(|| format!("{}.{} 必须是字符串", root, key))?;
            if value.len() != 64 || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
                return Err(format!("{}.{} 必须是 64 位十六进制 SHA-256", root, key));
            }
            Ok(value.to_ascii_lowercase())
        })
        .transpose()
}

fn required_u32(table: &toml::value::Table, key: &str, root: &str) -> Result<u32, String> {
    optional_u32(table, key, root)?.ok_or_else(|| format!("{}.{} 是必填项", root, key))
}

fn required_u16(table: &toml::value::Table, key: &str, root: &str) -> Result<u16, String> {
    let value = required_u32(table, key, root)?;
    u16::try_from(value).map_err(|_| format!("{}.{} 超出 u16 范围", root, key))
}

/// 解析具体化抽样的方向偏置 `(分母, 方向)`；两个字段要么都配、要么都不配。
///
/// 偏置的作用是：一侧注定通向无趣结果（例如 `return Illegal_Instruction()`）的分支点上，
/// 默认的 50/50 抽样会把一半路径白白送过去；配 `sample_bias = 16` 之后只有 1/16 会过去。
/// 方向必须显式写，因为抽样器不理解语义——写错的后果只是被压制的那类结果变多，
/// 跑一轮看条数就能发现并翻转（不会丢失路径，见 `SampleBias` 的文档）。
fn sample_bias(table: &toml::value::Table, root: &str) -> Result<Option<(u32, bool)>, String> {
    let denominator = optional_u32(table, "sample_bias", root)?;
    let direction = table
        .get("sample_bias_direction")
        .map(|value| match value.as_str() {
            Some("jump") => Ok(true),
            Some("fallthrough") => Ok(false),
            _ => Err(format!("{}.sample_bias_direction 必须是 jump 或 fallthrough", root)),
        })
        .transpose()?;

    match (denominator, direction) {
        (Some(denominator), Some(direction)) => {
            if denominator < 2 {
                return Err(format!("{}.sample_bias 必须 >= 2：1 表示每条路径都抽到该方向，等于没有偏置", root));
            }
            Ok(Some((denominator, direction)))
        }
        (None, None) => Ok(None),
        _ => Err(format!("{}.sample_bias 与 {}.sample_bias_direction 必须同时配置", root, root)),
    }
}

fn source_region_spec(table: &toml::value::Table, root: &str) -> Result<SourceRegionSpec, String> {
    let file = table.get("file").and_then(Value::as_str).ok_or_else(|| format!("{}.file 是必填字符串", root))?;
    Ok(SourceRegionSpec::new(
        file,
        (required_u32(table, "start_line", root)?, required_u16(table, "start_column", root)?),
        (required_u32(table, "end_line", root)?, required_u16(table, "end_column", root)?),
    ))
}

impl ExecutionLimitsConfig {
    pub fn from_file(path: impl AsRef<Path>) -> Result<Self, String> {
        let path = path.as_ref();
        let mut file = File::open(path).map_err(|error| format!("{}: {}", path.display(), error))?;
        let mut contents = String::new();
        file.read_to_string(&mut contents).map_err(|error| format!("{}: {}", path.display(), error))?;
        let value = contents.parse::<Value>().map_err(|error| format!("{}: {}", path.display(), error))?;
        allowed_keys(&value, "execution limits config", &["execution_limits"])?;
        get_execution_limits_config(&value)?.ok_or_else(|| format!("{}: 缺少 [execution_limits] 配置", path.display()))
    }

    pub fn validate_ir_sha256(&self, actual: &str) -> Result<(), String> {
        if !self.strict {
            return Ok(());
        }
        let expected = self.ir_sha256.as_deref().expect("strict execution limits config 必须包含 ir_sha256");
        if expected.eq_ignore_ascii_case(actual) {
            Ok(())
        } else {
            Err(format!("IR SHA-256 不匹配：期望 {}，实际 {}", expected, actual))
        }
    }
}

fn get_execution_limits_config(config: &Value) -> Result<Option<ExecutionLimitsConfig>, String> {
    let Some(value) = config.get("execution_limits") else { return Ok(None) };
    let Some(table) = value.as_table() else { return Err("[execution_limits] 必须是 TOML table".to_string()) };
    allowed_table_keys(
        table,
        "[execution_limits]",
        &[
            "strict",
            "ir_sha256",
            "enabled",
            "max_forks_per_branch",
            "max_forks_per_path",
            "max_backjumps_per_loop",
            "max_path_depth",
            "max_fork_pct_per_branch",
            "max_fork_pct_check_delay",
            "call_context_depth",
            "branch_sampling_seed",
            "on_limit_reached",
            "regions",
            "branch_region_limits",
            "region_fork_limits",
            "case_quota",
        ],
    )?;

    let enabled = optional_bool(table, "enabled", "execution_limits")?;
    if enabled == Some(false) && table.len() != 1 {
        return Err("execution_limits.enabled=false 时不能再配置其他 execution limit 字段".to_string());
    }

    let strict = optional_bool(table, "strict", "execution_limits")?.unwrap_or(false);
    let ir_sha256 = optional_sha256(table, "ir_sha256", "execution_limits")?;
    if strict && ir_sha256.is_none() {
        return Err("execution_limits.strict=true 时必须配置 execution_limits.ir_sha256".to_string());
    }

    let max_fork_pct_per_branch = table
        .get("max_fork_pct_per_branch")
        .map(|value| {
            let value = value
                .as_float()
                .or_else(|| value.as_integer().map(|value| value as f64))
                .ok_or_else(|| "execution_limits.max_fork_pct_per_branch 必须是 0.0..=1.0 的数值".to_string())?;
            if value.is_finite() && (0.0..=1.0).contains(&value) {
                Ok(value)
            } else {
                Err("execution_limits.max_fork_pct_per_branch 必须是 0.0..=1.0 的数值".to_string())
            }
        })
        .transpose()?;

    let on_limit_reached = table
        .get("on_limit_reached")
        .map(|value| match value.as_str() {
            Some("concretize") => Ok(LimitBehaviorConfig::Concretize),
            Some("truncate") => Ok(LimitBehaviorConfig::Truncate),
            _ => Err("execution_limits.on_limit_reached 必须是 concretize 或 truncate".to_string()),
        })
        .transpose()?;

    let regions = table
        .get("regions")
        .map(|value| {
            let regions = value.as_array().ok_or_else(|| "execution_limits.regions 必须是数组".to_string())?;
            if regions.is_empty() {
                return Err("execution_limits.regions 不能为空；如需关闭执行限制请设置 enabled=false".to_string());
            }
            regions
                .iter()
                .enumerate()
                .map(|(index, value)| {
                    let root = format!("execution_limits.regions[{}]", index);
                    let table = value.as_table().ok_or_else(|| format!("{} 必须是 TOML table", root))?;
                    allowed_table_keys(
                        table,
                        &root,
                        &["file", "start_line", "start_column", "end_line", "end_column"],
                    )?;
                    source_region_spec(table, &root)
                })
                .collect()
        })
        .transpose()?;

    let branch_region_limits = table
        .get("branch_region_limits")
        .map(|value| {
            let limits =
                value.as_array().ok_or_else(|| "execution_limits.branch_region_limits 必须是数组".to_string())?;
            if limits.is_empty() {
                return Err("execution_limits.branch_region_limits 不能为空".to_string());
            }
            limits
                .iter()
                .enumerate()
                .map(|(index, value)| {
                    let root = format!("execution_limits.branch_region_limits[{}]", index);
                    let table = value.as_table().ok_or_else(|| format!("{} 必须是 TOML table", root))?;
                    allowed_table_keys(
                        table,
                        &root,
                        &["max_forks_per_branch", "file", "start_line", "start_column", "end_line", "end_column"],
                    )?;
                    Ok(BranchRegionLimitConfig {
                        max_forks_per_branch: required_u32(table, "max_forks_per_branch", &root)?,
                        region: source_region_spec(table, &root)?,
                    })
                })
                .collect()
        })
        .transpose()?;

    let region_fork_limits = table
        .get("region_fork_limits")
        .map(|value| {
            let limits =
                value.as_array().ok_or_else(|| "execution_limits.region_fork_limits 必须是数组".to_string())?;
            if limits.is_empty() {
                return Err("execution_limits.region_fork_limits 不能为空".to_string());
            }
            limits
                .iter()
                .enumerate()
                .map(|(index, value)| {
                    let root = format!("execution_limits.region_fork_limits[{}]", index);
                    let table = value.as_table().ok_or_else(|| format!("{} 必须是 TOML table", root))?;
                    allowed_table_keys(
                        table,
                        &root,
                        &[
                            "max_forks_per_region",
                            "sample_bias",
                            "sample_bias_direction",
                            "file",
                            "start_line",
                            "start_column",
                            "end_line",
                            "end_column",
                        ],
                    )?;
                    Ok(RegionForkLimitConfig {
                        max_forks_per_region: required_u32(table, "max_forks_per_region", &root)?,
                        sample_bias: sample_bias(table, &root)?,
                        region: source_region_spec(table, &root)?,
                    })
                })
                .collect()
        })
        .transpose()?;

    Ok(Some(ExecutionLimitsConfig {
        strict,
        ir_sha256,
        enabled,
        max_forks_per_branch: optional_u32(table, "max_forks_per_branch", "execution_limits")?,
        max_forks_per_path: optional_u32(table, "max_forks_per_path", "execution_limits")?,
        max_backjumps_per_loop: optional_u32(table, "max_backjumps_per_loop", "execution_limits")?,
        max_path_depth: optional_u64(table, "max_path_depth", "execution_limits")?,
        max_fork_pct_per_branch,
        max_fork_pct_check_delay: optional_u32(table, "max_fork_pct_check_delay", "execution_limits")?,
        call_context_depth: optional_u64(table, "call_context_depth", "execution_limits")?
            .map(|value| usize::try_from(value).expect("usize 无法表示 execution_limits.call_context_depth")),
        branch_sampling_seed: optional_u64(table, "branch_sampling_seed", "execution_limits")?,
        on_limit_reached,
        regions,
        branch_region_limits,
        region_fork_limits,
        case_quota: case_quota_table(table)?,
    }))
}

fn case_quota_table(table: &toml::value::Table) -> Result<Option<BTreeMap<String, u32>>, String> {
    let Some(value) = table.get("case_quota") else { return Ok(None) };
    let sub = value.as_table().ok_or_else(|| "execution_limits.case_quota 必须是 TOML table".to_string())?;
    if sub.is_empty() {
        return Err("execution_limits.case_quota 不能为空".to_string());
    }
    let mut map = BTreeMap::new();
    for (key, value) in sub {
        let value = value.as_integer().ok_or_else(|| format!("execution_limits.case_quota.{} 必须是非负整数", key))?;
        map.insert(
            key.clone(),
            u32::try_from(value).map_err(|_| format!("execution_limits.case_quota.{} 超出 u32 范围", key))?,
        );
    }
    Ok(Some(map))
}

pub struct ISAConfig<B> {
    /// The identifier for the program counter register
    pub pc: Name,
    /// Map from cat sets to register event kinds
    pub register_event_sets: HashMap<String, Vec<RegisterKind>>,
    /// A path to an assembler for the architecture
    pub assembler: Tool,
    /// A path to an objdump for the architecture
    pub objdump: Tool,
    /// A path to an nm for the architecture
    pub nm: Tool,
    /// A path to a linker for the architecture
    pub linker: Tool,
    /// The base address for the page tables
    pub page_table_base: u64,
    /// The number of bytes in each page
    pub page_size: u64,
    /// The base address for the page tables (stage 2)
    pub s2_page_table_base: u64,
    /// The number of bytes in each page (stage 2)
    pub s2_page_size: u64,
    /// Default commands for page table setup
    pub default_page_table_setup: String,
    /// The base address for the threads in a litmus test
    pub thread_base: u64,
    /// The top address for the thread memory region
    pub thread_top: u64,
    /// The number of bytes between each thread
    pub thread_stride: u64,
    /// The first address to use when allocating symbolic addresses
    pub symbolic_addr_base: u64,
    /// One above the maximum address to use when allocating symbolic
    /// addresses (i.e. the range is half-open `[base, top)`)
    pub symbolic_addr_top: u64,
    /// The number of bytes between each symbolic address
    pub symbolic_addr_stride: u64,
    /// Default values for specified registers
    pub default_registers: HashMap<Name, Val<B>>,
    /// Reset values for specified registers
    pub reset_registers: Vec<(Loc<Name>, Reset<B>)>,
    /// Constraints that should hold at reset_registers
    pub reset_constraints: Vec<Exp<Loc<String>>>,
    /// Constant primops
    pub const_primops: HashMap<String, Reset<B>>,
    /// Assumptions to use about function behaviour
    pub function_assumptions: Vec<(String, Vec<Option<Exp<Loc<String>>>>, Exp<Loc<String>>)>,
    /// Register synonyms to rename
    pub register_renames: HashMap<String, Name>,
    /// Registers to ignore during footprint analysis
    pub ignored_registers: HashSet<Name>,
    /// Relaxed registers
    pub relaxed_registers: HashSet<Name>,
    /// Print debug information for any function calls in this set during symbolic execution
    pub probes: HashSet<Name>,
    /// Probe information under these functions
    pub probe_functions: HashSet<Name>,
    /// Trace calls to functions in this set
    pub trace_functions: HashSet<Name>,
    /// Address translation function
    pub translation_function: Option<Name>,
    /// The abstract events that should be included in program order
    pub in_program_order: HashSet<Name>,
    /// The default size (in bytes) for memory accesses in litmus tests
    pub default_sizeof: u32,
    /// Exit if sail_instr_announce is called with a zero bitvector
    pub zero_announce_exit: bool,
    /// Optional memory regions for symbolic/concrete setup
    pub memory_regions: Option<Vec<MemoryRegionConfig>>,
    /// Optional PMA map regions written into the zpma_regions register (W10/S1)
    pub pma_regions: Option<Vec<PmaRegionConfig>>,
    /// Optional page table configuration
    pub page_table_config: Option<PageTableConfig>,
    /// Optional PMP configuration
    pub pmp: Option<PmpConfig>,
    /// W21：`[symbolic_registers]` 声明的 CSR 符号化条目（solver 期注入）
    pub symbolic_registers: Vec<SymbolicRegisterConfig>,
    /// P1：`[[value_hints]]` 声明的值域 signposting 条目（solve-state 批调度）
    pub value_hints: Vec<ValueHintConfig>,
    /// Optional CLINT enable flag
    pub clint_enabled: Option<bool>,
    /// solve-state 的 execution-limit TOML 覆盖；未配置时由调用方使用代码默认值。
    pub execution_limits: Option<ExecutionLimitsConfig>,
}

impl<B: BV> ISAConfig<B> {
    pub fn parse(
        contents: &str,
        toolchain_name: Option<&str>,
        symtab: &Symtab,
        type_info: &IRTypeInfo,
    ) -> Result<Self, String> {
        let config = match contents.parse::<Value>() {
            Ok(config) => config,
            Err(e) => return Err(format!("Error when parsing configuration: {}", e)),
        };

        // Insert the translation_function into the set of functions
        // to trace, if it is provided by the config
        let translation_function = get_translation_function(&config, symtab)?;
        let mut trace_functions = get_trace_functions(&config, symtab)?;
        if let Some(f) = translation_function {
            trace_functions.insert(f);
        }

        let toolchain = get_toolchain(&config, toolchain_name)?;

        let mut default_registers = get_default_registers(&config, symtab, type_info)?;
        let symbolic_registers = get_symbolic_registers(&config, symtab, &default_registers)?;
        let value_hints = get_value_hints(&config)?.unwrap_or_default();
        let pmp = get_pmp_config(&config)?;

        Ok(ISAConfig {
            pc: get_program_counter(&config, symtab)?,
            register_event_sets: get_register_event_sets(&config, symtab)?,
            assembler: toolchain.assembler,
            objdump: toolchain.objdump,
            nm: toolchain.nm,
            linker: toolchain.linker,
            page_table_base: get_table_value(&config, "mmu", "page_table_base")?,
            page_size: get_table_value(&config, "mmu", "page_size")?,
            s2_page_table_base: get_table_value(&config, "mmu", "s2_page_table_base")?,
            s2_page_size: get_table_value(&config, "mmu", "s2_page_size")?,
            default_page_table_setup: get_table_string(&config, "mmu", "default_setup")
                .unwrap_or_else(|_| String::new()),
            thread_base: get_table_value(&config, "threads", "base")?,
            thread_top: get_table_value(&config, "threads", "top")?,
            thread_stride: get_table_value(&config, "threads", "stride")?,
            symbolic_addr_base: get_table_value(&config, "symbolic_addrs", "base")?,
            symbolic_addr_top: get_table_value(&config, "symbolic_addrs", "top")?,
            symbolic_addr_stride: get_table_value(&config, "symbolic_addrs", "stride")?,
            default_registers,
            reset_registers: get_reset_registers(&config, symtab, type_info)?,
            reset_constraints: get_reset_constraints(&config)?,
            const_primops: get_const_primops(&config, symtab, type_info)?,
            function_assumptions: Vec::new(),
            register_renames: get_register_renames(&config, symtab)?,
            ignored_registers: get_registers_set(&config, "ignore", symtab)?,
            relaxed_registers: get_registers_set(&config, "relaxed", symtab)?,
            probes: HashSet::new(),
            probe_functions: HashSet::new(),
            trace_functions,
            translation_function,
            in_program_order: get_in_program_order(&config, symtab)?,
            default_sizeof: get_default_sizeof(&config)?,
            zero_announce_exit: get_zero_announce_exit(&config)?,
            memory_regions: get_memory_regions(&config)?,
            pma_regions: get_pma_regions(&config)?,
            page_table_config: get_page_table_config(&config)?,
            pmp,
            symbolic_registers,
            value_hints,
            clint_enabled: get_clint_enabled(&config)?,
            execution_limits: get_execution_limits_config(&config)?,
        })
    }

    pub fn read_event_registers(&self) -> HashSet<Name> {
        let mut registers = HashSet::new();
        for (_, regs) in self.register_event_sets.iter() {
            for reg in regs.iter() {
                if let RegisterKind::Read(name) = reg {
                    registers.insert(*name);
                }
            }
        }
        registers
    }

    pub fn write_event_registers(&self) -> HashSet<Name> {
        let mut registers = HashSet::new();
        for (_, regs) in self.register_event_sets.iter() {
            for reg in regs.iter() {
                if let RegisterKind::Write(name) = reg {
                    registers.insert(*name);
                }
            }
        }
        registers
    }

    /// Load the configuration from a TOML file.
    pub fn from_file<P>(
        hasher: &mut Sha256,
        path: P,
        toolchain_name: Option<&str>,
        symtab: &Symtab,
        type_info: &IRTypeInfo,
    ) -> Result<Self, String>
    where
        P: AsRef<Path>,
    {
        let mut contents = String::new();
        match File::open(&path) {
            Ok(mut handle) => match handle.read_to_string(&mut contents) {
                Ok(_) => (),
                Err(e) => return Err(format!("Unexpected failure while reading config: {}", e)),
            },
            Err(e) => return Err(format!("Error when loading config '{}': {}", path.as_ref().display(), e)),
        };
        hasher.input(&contents);
        hasher.input(toolchain_name.unwrap_or("default"));

        match Self::parse(&contents, toolchain_name, symtab, type_info) {
            Ok(config) => Ok(config),
            Err(msg) => Err(format!("{}: {}", path.as_ref().display(), msg)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;

    #[test]
    fn execution_limits_config_parses_source_regions_and_overrides() {
        let value = r#"
            [execution_limits]
            max_forks_per_branch = 7
            max_forks_per_path = 11
            max_path_depth = 1234
            call_context_depth = 3
            branch_sampling_seed = 99
            on_limit_reached = "truncate"

            [[execution_limits.regions]]
            file = "extensions/V/vext_arith_insts.sail"
            start_line = 186
            start_column = 6
            end_line = 192
            end_column = 7
        "#
        .parse::<Value>()
        .unwrap();
        let config = get_execution_limits_config(&value).unwrap().unwrap();

        assert_eq!(config.max_forks_per_branch, Some(7));
        assert_eq!(config.max_forks_per_path, Some(11));
        assert_eq!(config.max_path_depth, Some(1234));
        assert_eq!(config.call_context_depth, Some(3));
        assert_eq!(config.branch_sampling_seed, Some(99));
        assert_eq!(config.on_limit_reached, Some(LimitBehaviorConfig::Truncate));
        assert_eq!(
            config.regions.unwrap()[0],
            SourceRegionSpec::new("extensions/V/vext_arith_insts.sail", (186, 6), (192, 7))
        );
    }

    #[test]
    fn execution_limits_config_parses_region_scoped_branch_and_loop_limits() {
        let value = r#"
            [execution_limits]
            max_forks_per_branch = 2
            max_backjumps_per_loop = 16
            on_limit_reached = "concretize"

            [[execution_limits.regions]]
            file = "extensions/V/vext_arith_insts.sail"
            start_line = 186
            start_column = 6
            end_line = 192
            end_column = 7

            [[execution_limits.regions]]
            file = "sys/vmem_utils.sail"
            start_line = 146
            start_column = 2
            end_line = 171
            end_column = 0
        "#
        .parse::<Value>()
        .unwrap();
        let config = get_execution_limits_config(&value).unwrap().unwrap();

        assert_eq!(config.max_forks_per_branch, Some(2));
        assert_eq!(config.max_backjumps_per_loop, Some(16));
        assert_eq!(config.on_limit_reached, Some(LimitBehaviorConfig::Concretize));
        assert_eq!(
            config.regions,
            Some(vec![
                SourceRegionSpec::new("extensions/V/vext_arith_insts.sail", (186, 6), (192, 7)),
                SourceRegionSpec::new("sys/vmem_utils.sail", (146, 2), (171, 0)),
            ])
        );
    }

    #[test]
    fn execution_limits_config_parses_narrow_branch_region_limits() {
        let value = r#"
            [execution_limits]
            max_forks_per_branch = 2
            on_limit_reached = "concretize"

            [[execution_limits.branch_region_limits]]
            max_forks_per_branch = 1
            file = "extensions/V/vext_control.sail"
            start_line = 29
            start_column = 2
            end_line = 35
            end_column = 3

            [[execution_limits.branch_region_limits]]
            max_forks_per_branch = 1
            file = "extensions/V/vext_utils_insts.sail"
            start_line = 729
            start_column = 2
            end_line = 750
            end_column = 1
        "#
        .parse::<Value>()
        .unwrap();
        let config = get_execution_limits_config(&value).unwrap().unwrap();

        assert_eq!(
            config.branch_region_limits,
            Some(vec![
                BranchRegionLimitConfig {
                    max_forks_per_branch: 1,
                    region: SourceRegionSpec::new("extensions/V/vext_control.sail", (29, 2), (35, 3)),
                },
                BranchRegionLimitConfig {
                    max_forks_per_branch: 1,
                    region: SourceRegionSpec::new("extensions/V/vext_utils_insts.sail", (729, 2), (750, 1)),
                },
            ])
        );
    }

    #[test]
    fn execution_limits_config_parses_region_fork_limits() {
        let value = r#"
            [execution_limits]
            max_forks_per_branch = 1
            on_limit_reached = "concretize"

            [[execution_limits.region_fork_limits]]
            max_forks_per_region = 1
            file = "extensions/V/vext_control.sail"
            start_line = 29
            start_column = 2
            end_line = 35
            end_column = 3
        "#
        .parse::<Value>()
        .unwrap();
        let config = get_execution_limits_config(&value).unwrap().unwrap();

        assert_eq!(
            config.region_fork_limits,
            Some(vec![RegionForkLimitConfig {
                max_forks_per_region: 1,
                sample_bias: None,
                region: SourceRegionSpec::new("extensions/V/vext_control.sail", (29, 2), (35, 3)),
            }])
        );
    }

    #[test]
    fn execution_limits_config_rejects_empty_region_fork_limits() {
        let value = "[execution_limits]\nregion_fork_limits = []".parse::<Value>().unwrap();
        let error = get_execution_limits_config(&value).unwrap_err();
        assert!(error.contains("execution_limits.region_fork_limits 不能为空"), "{}", error);
    }

    #[test]
    fn execution_limits_config_parses_case_quota_including_zero() {
        let value = r#"
            [execution_limits]

            [execution_limits.case_quota]
            Illegal_Instruction = 0
            Retire_Success = 3
        "#
        .parse::<Value>()
        .unwrap();

        let config = get_execution_limits_config(&value).unwrap().unwrap();

        assert_eq!(
            config.case_quota,
            Some(BTreeMap::from([(String::from("Illegal_Instruction"), 0), (String::from("Retire_Success"), 3)]))
        );
    }

    #[test]
    fn execution_limits_config_strict_mode_requires_matching_ir_hash() {
        let value = r#"
            [execution_limits]
            strict = true
            ir_sha256 = "c48050efa221b53ac70a2ae924d1b4d4794e8b4cc6dd78e8a0612451a34559cf"
        "#
        .parse::<Value>()
        .unwrap();
        let config = get_execution_limits_config(&value).unwrap().unwrap();

        assert!(config.validate_ir_sha256("c48050efa221b53ac70a2ae924d1b4d4794e8b4cc6dd78e8a0612451a34559cf").is_ok());
        let error =
            config.validate_ir_sha256("d48050efa221b53ac70a2ae924d1b4d4794e8b4cc6dd78e8a0612451a34559cf").unwrap_err();
        assert!(error.contains("期望 c48050ef"));
        assert!(error.contains("实际 d48050ef"));
    }

    #[test]
    fn execution_limits_config_rejects_invalid_strict_hash() {
        let missing = "[execution_limits]\nstrict = true".parse::<Value>().unwrap();
        let error = get_execution_limits_config(&missing).unwrap_err();
        assert!(error.contains("strict=true"));
        assert!(error.contains("ir_sha256"));

        let invalid = r#"
            [execution_limits]
            strict = true
            ir_sha256 = "not-a-sha256"
        "#
        .parse::<Value>()
        .unwrap();
        let error = get_execution_limits_config(&invalid).unwrap_err();
        assert!(error.contains("64 位十六进制"));
    }

    #[test]
    fn execution_limits_config_reads_standalone_toml_file() {
        let path = std::env::temp_dir().join(format!("isla-execution-limits-{}.toml", std::process::id()));
        std::fs::write(
            &path,
            r#"
                [execution_limits]
                strict = true
                ir_sha256 = "c48050efa221b53ac70a2ae924d1b4d4794e8b4cc6dd78e8a0612451a34559cf"
                max_forks_per_branch = 1
            "#,
        )
        .unwrap();

        let config = ExecutionLimitsConfig::from_file(&path).unwrap();

        std::fs::remove_file(&path).unwrap();
        assert!(config.strict);
        assert_eq!(config.max_forks_per_branch, Some(1));
        assert!(config.validate_ir_sha256("c48050efa221b53ac70a2ae924d1b4d4794e8b4cc6dd78e8a0612451a34559cf").is_ok());
    }

    #[test]
    fn execution_limits_config_rejects_empty_region_override() {
        let value = "[execution_limits]\nregions = []".parse::<Value>().unwrap();
        let error = get_execution_limits_config(&value).unwrap_err();

        assert!(error.contains("regions 不能为空"));
    }

    #[test]
    fn execution_limits_config_rejects_unknown_keys() {
        let value = "[execution_limits]\nmax_global_forks = 8".parse::<Value>().unwrap();
        let error = get_execution_limits_config(&value).unwrap_err();

        assert!(error.contains("max_global_forks"));
    }

    /// W9 判死区域解析：region_type = "excluded" 进入 MemoryRegionConfig，
    /// 与 concrete/symbolic 并存；未知取值仍报错。
    #[test]
    fn memory_regions_parse_excluded_type() {
        let value = r#"
            [[memory_regions]]
            name = "code"
            base = "0x0"
            size = "0x1000"
            region_type = "concrete"

            [[memory_regions]]
            name = "mmio_hole"
            base = "0x02000000"
            size = "0x02000000"
            region_type = "excluded"
        "#
        .parse::<Value>()
        .unwrap();

        let regions = get_memory_regions(&value).unwrap().unwrap();
        assert_eq!(regions.len(), 2);
        assert_eq!(regions[0].region_type, MemoryRegionType::Concrete);
        assert_eq!(regions[1].name, "mmio_hole");
        assert_eq!(regions[1].base, 0x0200_0000);
        assert_eq!(regions[1].size, 0x0200_0000);
        assert_eq!(regions[1].region_type, MemoryRegionType::Excluded);

        let bad = r#"
            [[memory_regions]]
            name = "x"
            base = "0x0"
            size = "0x1000"
            region_type = "dead"
        "#
        .parse::<Value>()
        .unwrap();
        assert!(get_memory_regions(&bad).is_err(), "未知 region_type 仍应报错");
    }

    /// W10（S1）[[pma_regions]] 未配置时必须返回 Ok(None)：不注入任何地图，
    /// 行为与现状（IR 固化 zpma_regions 默认值）逐项一致。
    #[test]
    fn pma_regions_absent_returns_none() {
        let value = r#"
            [[memory_regions]]
            name = "sym_ram"
            base = "0x80000000"
            size = "0x10000000"
            region_type = "symbolic"
        "#
        .parse::<Value>()
        .unwrap();
        assert!(matches!(get_pma_regions(&value), Ok(None)));
    }

    /// 别名 ram/rom/mmio/hole 的关键字段映射（S1 别名映射完整性）：
    /// ram=RWX+cacheable+no_fault+eventual，rom=R 只，mmio=RW 不 cacheable+
    /// alignment_fault，hole=全 false。别名取值镜像 IR 固化 zpma_regions 的
    /// 默认 region 属性（ram/mmio）与最保守取值（rom/hole）。
    #[test]
    fn pma_regions_alias_mapping() {
        let value = r#"
            [[pma_regions]]
            base = "0x80000000"
            size = "0x10000000"
            attr = "ram"

            [[pma_regions]]
            base = "0x1000"
            size = "0x1000"
            attr = "rom"

            [[pma_regions]]
            base = "0x02000000"
            size = "0x02000000"
            attr = "mmio"

            [[pma_regions]]
            base = "0x40000000"
            size = "0x10000000"
            attr = "hole"
        "#
        .parse::<Value>()
        .unwrap();

        // 输出按 base 降序：ram(0x80000000) > hole(0x40000000) > mmio(0x02000000) > rom(0x1000)
        let regions = get_pma_regions(&value).unwrap().unwrap();
        assert_eq!(regions.len(), 4);

        let ram = &regions[0];
        assert_eq!(ram.base, 0x8000_0000);
        assert_eq!(ram.size, PmaSize::Concrete(0x1000_0000));
        let a = &ram.attributes;
        assert!(a.readable && a.writable && a.executable && a.cacheable && a.coherent);
        assert!(a.read_idempotent && a.write_idempotent && a.supports_cbo_zzero);
        assert_eq!(a.misaligned_fault, PmaMisalignedFault::NoFault);
        assert_eq!(a.reservability, PmaReservability::Eventual);
        assert!(a.include_in_device_tree);

        let hole = &regions[1];
        let a = &hole.attributes;
        assert!(!a.readable && !a.writable && !a.executable && !a.cacheable && !a.coherent);
        assert!(!a.read_idempotent && !a.write_idempotent && !a.supports_cbo_zzero);
        assert_eq!(a.misaligned_fault, PmaMisalignedFault::NoFault);
        assert_eq!(a.reservability, PmaReservability::None);
        assert!(!a.include_in_device_tree);

        let mmio = &regions[2];
        let a = &mmio.attributes;
        assert!(a.readable && a.writable && !a.executable && !a.cacheable);
        assert!(!a.read_idempotent && !a.write_idempotent && !a.supports_cbo_zzero);
        assert_eq!(a.misaligned_fault, PmaMisalignedFault::AlignmentFault);
        assert_eq!(a.reservability, PmaReservability::None);

        let rom = &regions[3];
        let a = &rom.attributes;
        assert!(a.readable && !a.writable && !a.executable && a.cacheable);
        assert_eq!(a.misaligned_fault, PmaMisalignedFault::NoFault);
        assert_eq!(a.reservability, PmaReservability::None);
        assert!(!a.include_in_device_tree);

        // 未知别名必须报错
        let bad = r#"
            [[pma_regions]]
            base = "0x0"
            size = "0x1000"
            attr = "sram"
        "#
        .parse::<Value>()
        .unwrap();
        assert!(get_pma_regions(&bad).is_err(), "未知 attr 别名仍应报错");
    }

    /// 明细字段模式：无 attr 时以 include_in_device_tree=true、其余全 false 为
    /// 基线，明细字段逐项覆盖；attr 与明细字段可同时出现（attr 给底、明细覆盖）。
    #[test]
    fn pma_regions_detailed_fields_and_override() {
        let value = r#"
            [[pma_regions]]
            base = "0x80000000"
            size = "0x1000"
            readable = true
            misaligned = "alignment_fault"
            reservability = "eventual"
        "#
        .parse::<Value>()
        .unwrap();
        let regions = get_pma_regions(&value).unwrap().unwrap();
        let a = &regions[0].attributes;
        assert!(a.readable && !a.writable && !a.executable);
        assert!(a.include_in_device_tree, "明细模式 include_in_device_tree 默认 true");
        assert_eq!(a.misaligned_fault, PmaMisalignedFault::AlignmentFault);
        assert_eq!(a.reservability, PmaReservability::Eventual);

        let value = r#"
            [[pma_regions]]
            base = "0x80000000"
            size = "0x1000"
            attr = "mmio"
            executable = true
            include_in_device_tree = true
        "#
        .parse::<Value>()
        .unwrap();
        let regions = get_pma_regions(&value).unwrap().unwrap();
        let a = &regions[0].attributes;
        assert!(a.executable, "明细字段应覆盖 attr 底座");
        assert!(!a.cacheable, "未被覆盖的 attr 字段保持 mmio 取值");
        assert_eq!(a.misaligned_fault, PmaMisalignedFault::AlignmentFault);
        assert!(a.include_in_device_tree);

        // 既无 attr 也无任何明细属性字段的 region 是配置疑点，直接报错
        let bare = r#"
            [[pma_regions]]
            base = "0x0"
            size = "0x1000"
        "#
        .parse::<Value>()
        .unwrap();
        assert!(get_pma_regions(&bare).is_err(), "无 attr 且无明细字段应报错");
    }

    /// 配置解析自校验（对齐 MemoryBuilder 硬失败风格）：size=0、base+size 溢出、
    /// 区域重叠都必须报错；重叠检测与 TOML 书写顺序无关（解析内部按 base 降序
    /// 排序后再做相邻重叠检查，注入的 zpma_regions 列表即该降序）。
    #[test]
    fn pma_regions_validation_hard_fails() {
        let cases = [
            (
                r#"
                [[pma_regions]]
                base = "0x80000000"
                size = "0x0"
                attr = "ram"
                "#,
                "size 为 0",
            ),
            (
                r#"
                [[pma_regions]]
                base = "0xffffffffffffffff"
                size = "0x2"
                attr = "ram"
                "#,
                "base+size 溢出",
            ),
            (
                r#"
                [[pma_regions]]
                base = "0x80000000"
                size = "0x10000000"
                attr = "ram"

                [[pma_regions]]
                base = "0x8ffff000"
                size = "0x1000"
                attr = "ram"
                "#,
                "相邻区域重叠",
            ),
            (
                r#"
                [[pma_regions]]
                base = "0x0"
                size = "0x2000"
                attr = "rom"

                [[pma_regions]]
                base = "0x1000"
                size = "0x2000"
                attr = "ram"
                "#,
                "乱序书写仍检出重叠",
            ),
        ];
        for (toml, why) in cases {
            let value = toml.parse::<Value>().unwrap();
            let err = get_pma_regions(&value).unwrap_err();
            assert!(!err.is_empty(), "{} 应报错", why);
        }

        // 合法乱序配置：输出按 base 降序（与 IR 固化 zpma_regions 的列表次序一致）
        let value = r#"
            [[pma_regions]]
            base = "0x80000000"
            size = "0x10000000"
            attr = "ram"

            [[pma_regions]]
            base = "0x1000"
            size = "0x1000"
            attr = "rom"
        "#
        .parse::<Value>()
        .unwrap();
        let regions = get_pma_regions(&value).unwrap().unwrap();
        assert!(regions[0].base > regions[1].base, "输出应按 base 降序");
    }

    /// S2（W17）：size = "symbolic" 声明符号边界。显式 size_bounds 取闭区间
    /// [下界, 上界]；未声明时用默认域 [4KiB, 2^43)（emu RAM 顶界锚点）。
    /// 具体与符号 region 可混排（重叠检查按符号域上界保守处理）。
    #[test]
    fn pma_regions_symbolic_size_parsing() {
        let value = r#"
            [[pma_regions]]
            base = "0x80000000"
            size = "symbolic"
            size_bounds = ["0x800", "0x1000000000"]
            attr = "ram"
        "#
        .parse::<Value>()
        .unwrap();
        let regions = get_pma_regions(&value).unwrap().unwrap();
        assert_eq!(regions.len(), 1);
        assert_eq!(regions[0].size, PmaSize::Symbolic { min: 0x800, max: 0x10_0000_0000 });

        // 未声明 size_bounds：默认域
        let value = r#"
            [[pma_regions]]
            base = "0x80000000"
            size = "symbolic"
            attr = "ram"
        "#
        .parse::<Value>()
        .unwrap();
        let regions = get_pma_regions(&value).unwrap().unwrap();
        assert_eq!(regions[0].size, PmaSize::Symbolic { min: 0x1000, max: 0x80000000000 });

        // 具体与符号混排合法：重叠检查用符号域上界（0x80000000+0x2000 <= 0x90000000 不重叠）
        let value = r#"
            [[pma_regions]]
            base = "0x80000000"
            size = "symbolic"
            size_bounds = ["0x1000", "0x2000"]
            attr = "ram"

            [[pma_regions]]
            base = "0x90000000"
            size = "0x1000"
            attr = "ram"
        "#
        .parse::<Value>()
        .unwrap();
        let regions = get_pma_regions(&value).unwrap().unwrap();
        assert_eq!(regions.len(), 2, "符号域上界不与具体 region 重叠时应放行");
    }

    /// S2（W17）：符号边界自校验硬失败——size_bounds 元数错误/下界为 0/下界超
    /// 上界/base+上界溢出/具体 size 搭配 size_bounds/符号域上界与邻居重叠。
    #[test]
    fn pma_regions_symbolic_bounds_hard_fails() {
        let cases = [
            (
                r#"
                [[pma_regions]]
                base = "0x80000000"
                size = "symbolic"
                size_bounds = ["0x1000"]
                attr = "ram"
                "#,
                "size_bounds 元数不是 2",
            ),
            (
                r#"
                [[pma_regions]]
                base = "0x80000000"
                size = "symbolic"
                size_bounds = ["0x0", "0x1000"]
                attr = "ram"
                "#,
                "下界为 0",
            ),
            (
                r#"
                [[pma_regions]]
                base = "0x80000000"
                size = "symbolic"
                size_bounds = ["0x2000", "0x1000"]
                attr = "ram"
                "#,
                "下界超上界",
            ),
            (
                r#"
                [[pma_regions]]
                base = "0xffffffffffffffff"
                size = "symbolic"
                attr = "ram"
                "#,
                "base + 默认域上界溢出",
            ),
            (
                r#"
                [[pma_regions]]
                base = "0x80000000"
                size = "0x1000"
                size_bounds = ["0x1000", "0x2000"]
                attr = "ram"
                "#,
                "具体 size 搭配 size_bounds",
            ),
            (
                r#"
                [[pma_regions]]
                base = "0x80000000"
                size = "symbolic"
                size_bounds = ["0x1000", "0x20000000"]
                attr = "ram"

                [[pma_regions]]
                base = "0x90000000"
                size = "0x1000"
                attr = "ram"
                "#,
                "符号域上界与相邻 region 重叠",
            ),
        ];
        for (toml, why) in cases {
            let value = toml.parse::<Value>().unwrap();
            assert!(get_pma_regions(&value).is_err(), "{} 应报错", why);
        }
    }

    /// W21：[symbolic_registers] 最小夹具——只 intern zmstatus/zsatp 的 symtab
    /// 与空/含默认值的 default_registers。
    fn symbolic_registers_fixture(register_names: &[&str]) -> (Symtab<'static>, HashMap<Name, Val<B64>>) {
        let mut symtab = Symtab::new();
        for name in register_names {
            let encoded: &'static str = Box::leak(zencode::encode(name).into_boxed_str());
            symtab.intern(encoded);
        }
        (symtab, HashMap::new())
    }

    #[test]
    fn symbolic_registers_absent_returns_empty() {
        let (symtab, defaults) = symbolic_registers_fixture(&["mstatus"]);
        let value = "[registers]\n".parse::<Value>().unwrap();
        assert!(get_symbolic_registers(&value, &symtab, &defaults).unwrap().is_empty());
    }

    #[test]
    fn symbolic_registers_parses_string_and_table_forms() {
        let (mut symtab, defaults) = symbolic_registers_fixture(&["mstatus", "satp"]);
        let satp = symtab.get(&zencode::encode("satp")).unwrap();
        let value = r#"
            [symbolic_registers]
            satp = "symbolic"

            [symbolic_registers.mstatus]
            pin_mask = "0x8000003000000000"
            pin_value = "0x0"
            nonzero_groups = [[13, 14]]
        "#
        .parse::<Value>()
        .unwrap();
        assert_eq!(
            get_symbolic_registers(&value, &symtab, &defaults).unwrap(),
            vec![
                SymbolicRegisterConfig {
                    name: "mstatus".to_string(),
                    pin_mask: 0x8000_0030_0000_0000,
                    pin_value: 0,
                    nonzero_groups: vec![vec![13, 14]],
                    derive_bit: None,
                },
                SymbolicRegisterConfig {
                    name: "satp".to_string(),
                    pin_mask: 0,
                    pin_value: 0,
                    nonzero_groups: vec![],
                    derive_bit: None,
                },
            ]
        );
        let _ = satp;
    }

    /// W22：derive_bit 派生位约束解析（mstatus.SD 形状：位 63 ⇔ 三组全 1 的或）。
    #[test]
    fn symbolic_registers_parses_derive_bit() {
        let (symtab, defaults) = symbolic_registers_fixture(&["mstatus"]);
        let value = r#"
            [symbolic_registers.mstatus]
            pin_mask = "0x0000183C00000000"
            pin_value = "0x0000100800000000"
            nonzero_groups = [[13, 14]]
            derive_bit = { bit = 63, groups = [[14, 13], [10, 9], [16, 15]] }
        "#
        .parse::<Value>()
        .unwrap();
        assert_eq!(
            get_symbolic_registers(&value, &symtab, &defaults).unwrap(),
            vec![SymbolicRegisterConfig {
                name: "mstatus".to_string(),
                pin_mask: 0x0000_183C_0000_0000,
                pin_value: 0x0000_1008_0000_0000,
                nonzero_groups: vec![vec![13, 14]],
                derive_bit: Some(DerivedBitConfig { bit: 63, groups: vec![vec![14, 13], vec![10, 9], vec![16, 15]] }),
            }]
        );
    }

    /// W22：derive_bit 非法配置全部硬失败（钉死冲突、自引用、空组、形状错误）。
    #[test]
    fn symbolic_registers_derive_bit_hard_fails() {
        let cases = [
            (
                r#"[symbolic_registers.mstatus]
                derive_bit = { bit = 64, groups = [[14, 13]] }"#,
                "派生位号超出 64 位",
            ),
            (
                r#"[symbolic_registers.mstatus]
                derive_bit = { groups = [[14, 13]] }"#,
                "缺 bit",
            ),
            (
                r#"[symbolic_registers.mstatus]
                derive_bit = { bit = 63 }"#,
                "缺 groups",
            ),
            (
                r#"[symbolic_registers.mstatus]
                derive_bit = { bit = 63, groups = [] }"#,
                "空 groups",
            ),
            (
                r#"[symbolic_registers.mstatus]
                derive_bit = { bit = 63, groups = [[]] }"#,
                "空组",
            ),
            (
                r#"[symbolic_registers.mstatus]
                derive_bit = { bit = 63, groups = [[64]] }"#,
                "组内位号超出 64 位",
            ),
            (
                r#"[symbolic_registers.mstatus]
                pin_mask = "0x8000000000000000"
                pin_value = "0x0"
                derive_bit = { bit = 63, groups = [[14, 13]] }"#,
                "派生位与钉死位重叠",
            ),
            (
                r#"[symbolic_registers.mstatus]
                pin_mask = "0x2000"
                pin_value = "0x0"
                derive_bit = { bit = 63, groups = [[14, 13]] }"#,
                "组内位与钉死位重叠",
            ),
            (
                r#"[symbolic_registers.mstatus]
                derive_bit = { bit = 13, groups = [[14, 13]] }"#,
                "派生位出现在组内（自引用）",
            ),
            (
                r#"[symbolic_registers.mstatus]
                derive_bit = { bit = 63, groups = [[14, 13]], extra = 1 }"#,
                "未知子键",
            ),
            (
                r#"[symbolic_registers.mstatus]
                derive_bit = 63"#,
                "derive_bit 不是表",
            ),
        ];
        for (toml, why) in cases {
            let (symtab, defaults) = symbolic_registers_fixture(&["mstatus"]);
            let value = toml.parse::<Value>().unwrap();
            assert!(get_symbolic_registers(&value, &symtab, &defaults).is_err(), "{} 应报错", why);
        }
    }

    #[test]
    fn symbolic_registers_hard_fails() {
        let cases = [
            (
                r#"[symbolic_registers]
                mstatus = "symbolic""#,
                None,
                "IR 缺该寄存器",
            ),
            (
                r#"[symbolic_registers]
                mstatus = "concrete""#,
                Some(&["mstatus"]),
                "字符串取值不是 symbolic",
            ),
            (
                r#"[symbolic_registers.mstatus]
                pin_value = "0x1""#,
                Some(&["mstatus"]),
                "pin_value 缺 pin_mask",
            ),
            (
                r#"[symbolic_registers.mstatus]
                pin_mask = "0x1""#,
                Some(&["mstatus"]),
                "pin_mask 缺 pin_value",
            ),
            (
                r#"[symbolic_registers.mstatus]
                pin_mask = "0x1"
                pin_value = "0x2""#,
                Some(&["mstatus"]),
                "pin_value 含 mask 外位",
            ),
            (
                r#"[symbolic_registers.mstatus]
                nonzero_groups = [[]]"#,
                Some(&["mstatus"]),
                "空组",
            ),
            (
                r#"[symbolic_registers.mstatus]
                nonzero_groups = [[64]]"#,
                Some(&["mstatus"]),
                "位号超出 64 位",
            ),
            (
                r#"[symbolic_registers.mstatus]
                pin_mask = "0x2000"
                pin_value = "0x2000"
                nonzero_groups = [[13]]"#,
                Some(&["mstatus"]),
                "组位与钉死位重叠",
            ),
            (
                r#"[symbolic_registers.mstatus]
                unknown_key = 1"#,
                Some(&["mstatus"]),
                "未知子键",
            ),
        ];
        for (toml, fixture_names, why) in cases {
            let names: &[&str] = match fixture_names {
                Some(names) => names,
                None => &[],
            };
            let (symtab, defaults) = symbolic_registers_fixture(names);
            let value = toml.parse::<Value>().unwrap();
            assert!(get_symbolic_registers(&value, &symtab, &defaults).is_err(), "{} 应报错", why);
        }
    }

    #[test]
    fn symbolic_registers_conflicts_with_defaults() {
        let (symtab, mut defaults) = symbolic_registers_fixture(&["mstatus"]);
        let mstatus = symtab.get(&zencode::encode("mstatus")).unwrap();
        defaults.insert(mstatus, Val::Bool(true));
        let value = r#"
            [symbolic_registers]
            mstatus = "symbolic"
        "#
        .parse::<Value>()
        .unwrap();
        let error = get_symbolic_registers(&value, &symtab, &defaults).unwrap_err();
        assert!(error.contains("冲突"), "{}", error);
    }

    /// P1（plan-bughunt 值域 signposting）：[[value_hints]] 合法解析——维度类别、
    /// 内置模式名集合、显式数值列表、per-clause 作用域与全局作用域（缺省）。
    #[test]
    fn value_hints_parsing_dimensions_patterns_scope() {
        let value = r#"
            [[value_hints]]
            target = "base"
            patterns = ["misaligned", "pma_boundary_pm1"]
            clauses = ["zSTORE", "STORECON"]

            [[value_hints]]
            target = "data"
            patterns = ["nonzero_pattern"]

            [[value_hints]]
            target = "vector_ctx"
            patterns = ["vector_bounds"]
            values = ["0x40", 7]
        "#
        .parse::<Value>()
        .unwrap();
        let hints = get_value_hints(&value).unwrap().unwrap();
        assert_eq!(hints.len(), 3);

        assert_eq!(hints[0].target, ValueHintTarget::Base);
        assert_eq!(hints[0].patterns, vec![ValuePattern::Misaligned, ValuePattern::PmaBoundaryPm1]);
        assert!(hints[0].values.is_empty());
        assert_eq!(hints[0].clauses.as_deref(), Some(&["zSTORE".to_string(), "STORECON".to_string()][..]));

        assert_eq!(hints[1].target, ValueHintTarget::Data);
        assert_eq!(hints[1].patterns, vec![ValuePattern::NonzeroPattern]);
        // 缺省 clauses 即全局作用域
        assert_eq!(hints[1].clauses, None);

        assert_eq!(hints[2].target, ValueHintTarget::VectorCtx);
        assert_eq!(hints[2].patterns, vec![ValuePattern::VectorBounds]);
        // 模式与显式数值可并存（候选并集）
        assert_eq!(hints[2].values, vec![0x40, 7]);
    }

    /// 解析硬失败（对齐 [[pma_regions]]/[[memory_regions]] 风格）：未知维度类别、
    /// 未知模式名、空候选（patterns 与 values 全缺）、字段类型不符都必须报错。
    #[test]
    fn value_hints_hard_fails() {
        let cases = [
            (
                r#"
                [[value_hints]]
                target = "stack"
                patterns = ["misaligned"]
                "#,
                "未知维度类别",
            ),
            (
                r#"
                [[value_hints]]
                target = "base"
                patterns = ["misalignd"]
                "#,
                "未知模式名",
            ),
            (
                r#"
                [[value_hints]]
                target = "base"
                "#,
                "空候选（patterns 与 values 全缺）",
            ),
            (
                r#"
                [[value_hints]]
                target = "base"
                patterns = "misaligned"
                "#,
                "patterns 不是数组",
            ),
            (
                r#"
                [[value_hints]]
                target = "base"
                values = [-1]
                "#,
                "负数值候选",
            ),
            (
                r#"
                [[value_hints]]
                target = "data"
                patterns = ["nonzero_pattern"]
                clauses = "zSTORE"
                "#,
                "clauses 不是数组",
            ),
            (
                r#"
                value_hints = { target = "base" }
                "#,
                "value_hints 不是 array-of-tables",
            ),
        ];
        for (toml, why) in cases {
            let value = toml.parse::<Value>().unwrap();
            assert!(get_value_hints(&value).is_err(), "{} 应报错", why);
        }
    }
}
