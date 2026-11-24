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

use serde::Deserialize;
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

pub fn allowed_table_keys(config: &toml::value::Table, root: &str, allowed_keys: &[&str]) -> Result<(), String> {
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

/// 仅在真正调用工具时查找程序，不让求解等无工具路径依赖宿主机工具链。
fn find_tool_path<P>(program: P) -> Result<PathBuf, String>
where
    P: AsRef<Path>,
{
    if program.as_ref().is_absolute() {
        if program.as_ref().is_file() {
            Ok(program.as_ref().to_path_buf())
        } else {
            Err(format!("工具路径不存在：{}", program.as_ref().display()))
        }
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
    pub executable: Option<PathBuf>,
    pub options: Vec<String>,
}

impl Tool {
    pub fn resolve(&self, required_by: &str) -> Result<PathBuf, String> {
        let caller = env::args().next().expect("进程参数必须包含程序名");
        let program = self.executable.as_ref().ok_or_else(|| format!("{caller}：{required_by} 需要的工具未配置"))?;
        find_tool_path(program).map_err(|error| {
            format!("{caller}：{required_by} 需要工具命令 {} {}：{error}", program.display(), self.options.join(" "))
        })
    }

    pub fn command(&self, required_by: &str) -> Result<Command, String> {
        let mut cmd = Command::new(self.resolve(required_by)?);
        cmd.args(&self.options);
        Ok(cmd)
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
/// - `allowed`：枚举寄存器的允许成员名集合；与位约束互斥，不能为空或重复。
/// - `derive_bit`（W22）：派生位等价约束，见 [DerivedBitConfig]。派生位与
///   组内位都不得与 pin_mask 重叠，派生位不得出现在任何组内（自引用退化）。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolicRegisterConfig {
    pub name: String,
    pub pin_mask: u64,
    pub pin_value: u64,
    pub nonzero_groups: Vec<Vec<u32>>,
    pub derive_bit: Option<DerivedBitConfig>,
    /// 枚举允许成员；与所有位约束互斥，保持配置顺序供固定编码译码使用。
    pub allowed: Option<Vec<String>>,
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

/// P2（plan-bughunt 编码维度预分片）：`[[encoding_slices]]` 单条声明。
/// 整片自由求解从未选中具体编码（51 例 VSSEG 无 vsseg3e32、VLX/VSX 整片超时），
/// 编码维度（nf×eew×mop…）按维度表预分片枚举——每片钉死编码字段独立求解，
/// 替代自由求解撞运气。维度值域推导与编码构造见 isarch 侧 `encoding_slices`
/// 模块；配置层只负责名字与形态的合法性。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EncodingSliceConfig {
    /// 作用 clause（按 isarch 的 normalize_clause_name 归一匹配）
    pub clause: String,
    /// 全枚举维度字段名：值域由维度表从 IR 类型（枚举成员、位宽）或内置域
    /// （nf=2..=8）推导。
    pub enumerate: Vec<String>,
    /// 显式钉值维度：字段名 → 语义值候选（如 eew 用 8/16/32/64、mop 用 0/1）。
    pub dimensions: BTreeMap<String, Vec<u64>>,
    /// 非维度操作数字段的具体选择（缺省沿用维度表内置默认 rs1/vs2/vs3=6、vm=1）。
    pub operand_defaults: BTreeMap<String, u64>,
    /// 每片附加寄存器钉值：寄存器名 → 值文本（--prestate 语法）。向量编码的
    /// 译码守卫需要具体 mstatus/cur_privilege 打开扩展域（E 线 T1 先例）。
    pub prestate: BTreeMap<String, String>,
    /// 每片用例数上限（None 沿用全局配额）。
    pub case_limit: Option<u32>,
    /// 每片求解时间盒秒数（None 沿用全局 --timeout）。
    pub timebox_s: Option<u64>,
}

pub fn get_encoding_slices(config: &Value) -> Result<Option<Vec<EncodingSliceConfig>>, String> {
    let Some(slices) = config.get("encoding_slices") else { return Ok(None) };
    let Some(slices) = slices.as_array() else {
        return Err("encoding_slices should be an array of tables".to_string());
    };

    let mut parsed = Vec::with_capacity(slices.len());
    for (index, slice) in slices.iter().enumerate() {
        let Some(slice) = slice.as_table() else {
            return Err("encoding_slices should be an array of tables".to_string());
        };
        allowed_table_keys(
            slice,
            "[[encoding_slices]]",
            &["clause", "enumerate", "dimensions", "operand_defaults", "prestate", "case_limit", "timebox_s"],
        )?;

        let context = format!("encoding_slices[{}]", index);
        let clause = match slice.get("clause") {
            Some(Value::String(name)) => name.clone(),
            Some(_) => return Err(format!("{}.clause should be a string", context)),
            None => return Err(format!("No {}.clause found", context)),
        };

        let mut enumerate = Vec::new();
        match slice.get("enumerate") {
            Some(Value::Array(entries)) => {
                for entry in entries {
                    match entry {
                        Value::String(name) => enumerate.push(name.clone()),
                        _ => return Err(format!("{}.enumerate should be an array of strings", context)),
                    }
                }
            }
            Some(_) => return Err(format!("{}.enumerate should be an array of strings", context)),
            None => (),
        }

        let mut dimensions = BTreeMap::new();
        match slice.get("dimensions") {
            Some(Value::Table(table)) => {
                for (field, values) in table {
                    let Some(values) = values.as_array() else {
                        return Err(format!("{}.dimensions.{} should be an array of integers", context, field));
                    };
                    let mut candidates = Vec::with_capacity(values.len());
                    if candidates.is_empty() && values.is_empty() {
                        return Err(format!("{}.dimensions.{} 候选列表为空", context, field));
                    }
                    for value in values {
                        candidates.push(parse_u64_value(value, &format!("{}.dimensions.{}", context, field))?);
                    }
                    dimensions.insert(field.clone(), candidates);
                }
            }
            Some(_) => return Err(format!("{}.dimensions should be a table", context)),
            None => (),
        }

        // 同一字段既声明全枚举又声明显式钉值是歧义配置，硬失败
        for field in &enumerate {
            if dimensions.contains_key(field) {
                return Err(format!("{} 字段 {} 同时出现在 enumerate 与 dimensions", context, field));
            }
        }

        let mut operand_defaults = BTreeMap::new();
        match slice.get("operand_defaults") {
            Some(Value::Table(table)) => {
                for (field, value) in table {
                    operand_defaults.insert(
                        field.clone(),
                        parse_u64_value(value, &format!("{}.operand_defaults.{}", context, field))?,
                    );
                }
            }
            Some(_) => return Err(format!("{}.operand_defaults should be a table", context)),
            None => (),
        }

        let mut prestate = BTreeMap::new();
        match slice.get("prestate") {
            Some(Value::Table(table)) => {
                for (register, value) in table {
                    let Some(value) = value.as_str() else {
                        return Err(format!("{}.prestate.{} should be a string", context, register));
                    };
                    prestate.insert(register.clone(), value.to_string());
                }
            }
            Some(_) => return Err(format!("{}.prestate should be a table", context)),
            None => (),
        }

        let case_limit = match slice.get("case_limit") {
            Some(value) => {
                let limit = parse_u64_value(value, &format!("{}.case_limit", context))?;
                let limit = u32::try_from(limit).map_err(|_| format!("{}.case_limit 应为正 u32", context))?;
                if limit == 0 {
                    return Err(format!("{}.case_limit 应为正 u32", context));
                }
                Some(limit)
            }
            None => None,
        };

        let timebox_s = match slice.get("timebox_s") {
            Some(value) => {
                let seconds = parse_u64_value(value, &format!("{}.timebox_s", context))?;
                if seconds == 0 {
                    return Err(format!("{}.timebox_s 应为正数秒", context));
                }
                Some(seconds)
            }
            None => None,
        };

        parsed.push(EncodingSliceConfig {
            clause,
            enumerate,
            dimensions,
            operand_defaults,
            prestate,
            case_limit,
            timebox_s,
        });
    }

    Ok(Some(parsed))
}

fn get_tool_path(config: &Value, tool: &str) -> Result<Tool, String> {
    match config.get(tool) {
        Some(Value::String(command)) => {
            let mut words = command.split_whitespace();
            let program = words.next().ok_or_else(|| format!("Toolchain option {} cannot be an empty string", tool))?;
            Ok(Tool { executable: Some(PathBuf::from(program)), options: words.map(|w| w.to_string()).collect() })
        }
        None => Ok(Tool { executable: None, options: Vec::new() }),
        _ => Err(format!("Toolchain option {} must be a string", tool)),
    }
}

pub fn parse_u64_value(value: &Value, context: &str) -> Result<u64, String> {
    match value {
        Value::Integer(i) => u64::try_from(*i).map_err(|e| format!("failed to parse integer in {}: {}", context, e)),
        Value::String(s) => {
            if let Some(hex) = s.strip_prefix("0x") { u64::from_str_radix(hex, 16) } else { u64::from_str_radix(s, 10) }
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
/// cur_privilege = { allowed = ["User", "Supervisor"] }  # 枚举取值域
///
/// [symbolic_registers.mstatus]            # 表形式：位级钉死 + 位组域 + 派生位
/// pin_mask  = "0x0000003F00000000"        # MBE(37)|SBE(36)|SXL(35:34)|UXL(33:32)
/// pin_value = "0x0000000A00000000"        # 小端 + XLEN=64
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
        let mut allowed = None;
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
                    &["pin_mask", "pin_value", "nonzero_groups", "derive_bit", "allowed"],
                )?;
                if let Some(value) = sub.get("allowed") {
                    if sub.len() != 1 {
                        return Err(format!("symbolic_registers.{}.allowed 不能与位约束混用", name));
                    }
                    let members = value
                        .as_array()
                        .filter(|members| !members.is_empty())
                        .ok_or_else(|| format!("symbolic_registers.{}.allowed 必须是非空成员名数组", name))?;
                    let mut names = Vec::new();
                    for member in members {
                        let member = member
                            .as_str()
                            .ok_or_else(|| format!("symbolic_registers.{}.allowed 只接受成员名字符串", name))?;
                        if symtab.get(&zencode::encode(member)).is_none() {
                            return Err(format!("symbolic_registers.{}.allowed：当前 IR 不存在成员 {}", name, member));
                        }
                        if names.iter().any(|existing| existing == member) {
                            return Err(format!("symbolic_registers.{}.allowed 重复成员 {}", name, member));
                        }
                        names.push(member.to_string());
                    }
                    allowed = Some(names);
                }
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
            allowed,
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
) -> Result<HashMap<String, (Reset<B>, crate::primop::Effect)>, String> {
    let defaults = config.get("const_primops");

    if let Some(defaults) = defaults {
        if let Some(defaults) = defaults.as_table() {
            defaults
                .into_iter()
                .map(|(primop, value)| {
                    let value = from_toml_value_undef::<B>(value, symtab, type_info)?;
                    let effect = crate::primop::const_primop_effect(&value);
                    Ok((primop.clone(), (value.into_reset(), effect)))
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
    Ok(from_toml_value_undef::<B>(value, symtab, type_info)?.into_reset())
}

impl<B: BV> URVal<B> {
    fn into_reset(self) -> Reset<B> {
        Arc::new(move |_, typedefs, solver| match &self {
            URVal::Init(value) => Ok(value.clone()),
            URVal::Uninit(ty) => symbolic_from_typedefs(ty, typedefs, solver, SourceLoc::command_line()),
        })
    }
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

fn get_constraints(config: &Value, phase: &str) -> Result<Vec<Exp<Loc<String>>>, String> {
    let reset_toml =
        config.get("constraints").and_then(|section| section.as_table()).and_then(|section| section.get(phase));
    if let Some(toml) = reset_toml {
        let constraints = toml
            .as_array()
            .and_then(|vec| vec.iter().map(|item| item.as_str()).collect::<Option<Vec<_>>>())
            .ok_or_else(|| format!("constraints.{phase} 必须是约束字符串数组"))?;
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

pub mod region_options;
pub use region_options::RegionOptions;
pub mod path_merge;
pub use path_merge::PathFailureAction as SolverOnUnknown;
pub use path_merge::{
    PathFailureAction, PathMergeConfig, PathMergeDiagnostics, PathMergeParallelConfig, PathMergeRegionConfig,
    SolverConfig,
};

/// 路径合并执行策略；递归是兼容默认值。
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum MergeStrategy {
    #[default]
    Recursive,
    Flat,
}
impl std::str::FromStr for MergeStrategy {
    type Err = String;
    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "recursive" => Ok(Self::Recursive),
            "flat" => Ok(Self::Flat),
            _ => Err("strategy 必须是 recursive 或 flat".into()),
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct ExecutionLimitsConfig {
    pub on_path_timeout: PathFailureAction,
    pub solver: SolverConfig,
    pub path_merge: PathMergeConfig,
    /// resident judge 同时恢复的路径上限，默认使用线程数。
    pub judge_resident_batch_size: Option<usize>,
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
    /// 输出层按 `ret_val` 构造子分类的用例配额，由 isarch 收尾阶段消费。
    pub case_quota: Option<BTreeMap<String, u32>>,
    /// 抛出时丢弃的 Sail 异常构造子，终态收集也使用此列表。
    pub filter_model_exceptions: Vec<String>,
    /// 在 Sail IR 的 match 失败出口处丢弃路径。
    pub filter_match_failures: bool,
}

/// 合并路径结束后的两级投影枚举；上限只限制输出，不改变执行路径条件。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MergeEnumerationConfig {
    pub enabled: bool,
    pub mode: MergeEnumerationMode,
    pub class_cap: Option<usize>,
    pub path_cap: Option<usize>,
    pub sample_stride: usize,
    pub enumeration_threads: usize,
    pub outputs: Vec<SampleOutputConfig>,
    /// None 表示流式二进制输出不限字节。
    pub max_output_bytes: Option<u64>,
    /// 显式设置探测次数才允许近似预测。
    pub predict_probes: Option<usize>,
    pub predict_seed: u64,
    pub predict_domain_cap: Option<usize>,
}

impl MergeEnumerationConfig {
    pub fn streams_binary(&self) -> bool {
        self.sample_stride == 1
            && matches!(self.outputs.as_slice(), [SampleOutputConfig { format: SampleOutputFormat::Binary, .. }])
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SampleOutputConfig {
    pub format: SampleOutputFormat,
    pub path: std::path::PathBuf,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SampleOutputFormat {
    V1Jsonl,
    CompactJsonl,
    Binary,
}

impl Default for MergeEnumerationConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            mode: MergeEnumerationMode::Samples,
            class_cap: None,
            path_cap: None,
            sample_stride: 1,
            enumeration_threads: std::thread::available_parallelism().unwrap().get().min(16),
            outputs: Vec::new(),
            max_output_bytes: None,
            predict_probes: None,
            predict_seed: 0,
            predict_domain_cap: None,
        }
    }
}

/// 枚举时导出代表样本，或只统计投影域。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MergeEnumerationMode {
    Samples,
    Count,
    Predict,
}

/// 局部路径合并策略；这里只描述配置，不改变解释器行为。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MergeMode {
    Force,
    Adaptive,
    Off,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MergePolicyConfig {
    pub mode: MergeMode,
    pub selector: MergePolicySelectorConfig,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MergePolicySelectorConfig {
    /// 保存经现有 zencode 工具编码后的 IR 函数名。
    Function(String),
    Region(SourceRegionSpec),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
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
    let start = (required_u32(table, "start_line", root)?, required_u16(table, "start_column", root)?);
    let end = (required_u32(table, "end_line", root)?, required_u16(table, "end_column", root)?);
    if file.is_empty() || start.0 == 0 || end.0 == 0 || start > end {
        return Err(format!("{} 的源码区域非法：文件名不能为空、行号必须大于 0，且起点不能晚于终点", root));
    }
    Ok(SourceRegionSpec::new(file, start, end))
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

    /// 在 IR 加载后、执行前调用。`functions` 只能包含 IR 中实际定义的函数，
    /// `branch_locations` 由调用方提供实际分支位置，不能用全部指令位置代替。
    /// strict 启用源码区域匹配检查。需要比较 IR 哈希的调用方可单独调用 validate_ir_sha256。
    /// force 的后支配点/回边校验留给后续静态区域分析。
    pub fn validate_merge_policy(
        &self,
        symtab: &Symtab,
        functions: &HashSet<Name>,
        branch_locations: &[crate::source_loc::SourceLoc],
    ) -> Result<(), String> {
        let rules = self.path_merge.policies();
        if rules.is_empty() {
            return Ok(());
        };
        validate_merge_policy_conflicts(&rules)?;
        for (index, rule) in rules.iter().enumerate() {
            match &rule.selector {
                MergePolicySelectorConfig::Function(function) => {
                    if !symtab.get(function).map_or(false, |name| functions.contains(&name)) {
                        return Err(format!(
                            "execution_limits.path_merge.regions[{}] 的函数 {} 不存在于 IR 函数集合中",
                            index,
                            zencode::decode(function)
                        ));
                    }
                }
                MergePolicySelectorConfig::Region(spec) => {
                    // 非 strict 时，无法解析的文件与 region_fork_limits 一样不匹配任何位置。
                    if self.strict
                        && !spec.resolve(symtab.files()).map_or(false, |region| {
                            branch_locations.iter().any(|location| region.selects_ir_location(*location))
                        })
                    {
                        return Err(format!(
                            "execution_limits.path_merge.regions[{}] 的源码区域 {:?} 未匹配任何 IR 分支（strict=true）",
                            index, spec
                        ));
                    }
                }
            }
        }
        Ok(())
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

fn validate_merge_policy_conflicts(rules: &[MergePolicyConfig]) -> Result<(), String> {
    for (index, rule) in rules.iter().enumerate() {
        for (previous_index, previous) in rules[..index].iter().enumerate() {
            if previous.selector == rule.selector && previous.mode != rule.mode {
                return Err(format!(
                    "execution_limits.path_merge.regions[{}] 与 [{}] 的同一选择器 {:?} 存在 mode 冲突：{:?} / {:?}",
                    previous_index, index, rule.selector, previous.mode, rule.mode
                ));
            }
        }
    }
    Ok(())
}

/// TOML 与 CLI 共用的校验；None 表示不设步数上限。
pub fn parse_region_step_budget(value: i64) -> Result<Option<usize>, String> {
    match value {
        -1 => Ok(None),
        1.. => usize::try_from(value)
            .map(Some)
            .map_err(|_| "execution_limits.path_merge.step_budget 超出 usize 范围".to_string()),
        _ => Err("execution_limits.path_merge.step_budget 必须为正整数或 -1（关闭预算）".to_string()),
    }
}

fn get_execution_limits_config(config: &Value) -> Result<Option<ExecutionLimitsConfig>, String> {
    let Some(value) = config.get("execution_limits") else { return Ok(None) };
    let Some(table) = value.as_table() else { return Err("[execution_limits] 必须是 TOML table".to_string()) };
    // 只给迁移指引，不读取旧值，也不建立兼容别名。
    for (old, new) in [
        ("path_merging", "execution_limits.path_merge.enabled"),
        ("region_step_budget", "execution_limits.path_merge.step_budget"),
        (
            "region_options",
            "execution_limits.path_merge / execution_limits.path_merge.diagnostics / execution_limits.solver",
        ),
        ("regions", "execution_limits.path_merge.regions (kind=limit_filter)"),
        ("branch_region_limits", "execution_limits.path_merge.regions (kind=branch_limit)"),
        ("region_fork_limits", "execution_limits.path_merge.regions (kind=fork_limit)"),
        ("merge_policy", "execution_limits.path_merge.regions (kind=merge_policy)"),
        ("merge_enumeration", "execution_limits.path_merge.enumeration"),
    ] {
        if table.contains_key(old) {
            return Err(format!("execution_limits.{old} 已删除；请迁移到 {new}"));
        }
    }
    let mut config: ExecutionLimitsConfig = value.clone().try_into().map_err(|e| format!("execution_limits: {e}"))?;
    if config.enabled == Some(false) && table.len() != 1 {
        return Err("execution_limits.enabled=false 时不能再配置其他 execution limit 字段".into());
    }
    config.ir_sha256 = optional_sha256(table, "ir_sha256", "execution_limits")?;
    if config.strict && config.ir_sha256.is_none() {
        return Err("execution_limits.strict=true 时必须配置 execution_limits.ir_sha256".into());
    }
    if let Some(value) = config.max_fork_pct_per_branch {
        if !value.is_finite() || !(0.0..=1.0).contains(&value) {
            return Err("execution_limits.max_fork_pct_per_branch 必须是 0.0..=1.0 的数值".into());
        }
    }
    if config.judge_resident_batch_size == Some(0) {
        return Err("judge_resident_batch_size 必须大于零".into());
    }
    config.case_quota = case_quota_table(table)?;
    for name in &config.filter_model_exceptions {
        if name.trim().is_empty() || name != name.trim() {
            return Err("execution_limits.filter_model_exceptions 必须包含非空构造子名称，且不得有首尾空格".into());
        }
    }
    config.path_merge.validate()?;
    RegionOptions::from_config(&config).validate()?;
    Ok(Some(config))
}

fn parse_merge_enumeration(table: &toml::value::Table) -> Result<Option<MergeEnumerationConfig>, String> {
    table
        .get("enumeration")
        .map(|value| {
            let root = "execution_limits.path_merge.enumeration";
            let sub = value.as_table().ok_or_else(|| format!("{root} 必须是 TOML table"))?;
            allowed_table_keys(
                sub,
                root,
                &[
                    "enabled",
                    "mode",
                    "class_cap",
                    "path_cap",
                    "sample_stride",
                    "enumeration_threads",
                    "outputs",
                    "max_output_bytes",
                    "predict_probes",
                    "predict_seed",
                    "predict_domain_cap",
                ],
            )?;
            let mut config = MergeEnumerationConfig::default();
            if let Some(outputs) = sub.get("outputs") {
                let outputs = outputs.as_array().ok_or_else(|| format!("{root}.outputs 必须是数组"))?;
                let mut formats = std::collections::HashSet::new();
                let mut paths = std::collections::HashSet::new();
                for value in outputs {
                    let table = value.as_table().ok_or_else(|| format!("{root}.outputs 项必须是 table"))?;
                    allowed_table_keys(table, root, &["format", "path"])?;
                    let format = match table.get("format").and_then(toml::Value::as_str) {
                        Some("v1_jsonl") => SampleOutputFormat::V1Jsonl,
                        Some("compact_jsonl") => SampleOutputFormat::CompactJsonl,
                        Some("binary") => SampleOutputFormat::Binary,
                        _ => return Err(format!("{root}.outputs.format 必须是 v1_jsonl、compact_jsonl 或 binary")),
                    };
                    let path = table
                        .get("path")
                        .and_then(toml::Value::as_str)
                        .filter(|path| !path.is_empty())
                        .ok_or_else(|| format!("{root}.outputs.path 必须是非空字符串"))?;
                    if !formats.insert(format) || !paths.insert(path) {
                        return Err(format!("{root}.outputs 不得重复格式或文件路径"));
                    }
                    config.outputs.push(SampleOutputConfig { format, path: path.into() });
                }
            }
            if let Some(mode) = sub.get("mode") {
                config.mode = match mode.as_str() {
                    Some("samples") => MergeEnumerationMode::Samples,
                    Some("count") => MergeEnumerationMode::Count,
                    Some("predict") => MergeEnumerationMode::Predict,
                    _ => return Err(format!("{root}.mode 必须是 samples、count 或 predict")),
                };
            }
            if let Some(enabled) = optional_bool(sub, "enabled", root)? {
                config.enabled = enabled;
            }
            if let Some(value) = optional_u64(sub, "predict_probes", root)? {
                if value < 200 {
                    return Err(format!("{root}.predict_probes 必须至少为 200"));
                }
                config.predict_probes =
                    Some(usize::try_from(value).map_err(|error| format!("{root}.predict_probes: {error}"))?);
            }
            if let Some(value) = optional_u64(sub, "predict_seed", root)? {
                config.predict_seed = value;
            }
            if let Some(value) = optional_u64(sub, "predict_domain_cap", root)? {
                if value == 0 || config.predict_probes.is_none() {
                    return Err(format!("{root}.predict_domain_cap 必须为正数且同时设置 predict_probes"));
                }
                config.predict_domain_cap =
                    Some(usize::try_from(value).map_err(|error| format!("{root}.predict_domain_cap: {error}"))?);
            }
            if config.predict_probes.is_some() && config.predict_domain_cap.is_none() {
                return Err(format!("{root}.predict_probes 要求显式设置 predict_domain_cap"));
            }
            if let Some(value) = optional_u64(sub, "max_output_bytes", root)? {
                if value == 0 {
                    return Err(format!("{root}.max_output_bytes 必须大于零"));
                }
                if config.outputs.len() != 1 || config.outputs[0].format != SampleOutputFormat::Binary {
                    return Err(format!("{root}.max_output_bytes 要求只启用一个 binary 后端"));
                }
                config.max_output_bytes = Some(value);
            }
            let positive_usize = |name| {
                optional_u64(sub, name, root)?
                    .map(|value| {
                        if value == 0 {
                            return Err(format!("{root}.{name} 必须大于零"));
                        }
                        usize::try_from(value).map_err(|error| format!("{root}.{name}: {error}"))
                    })
                    .transpose()
            };
            config.class_cap = positive_usize("class_cap")?;
            config.path_cap = positive_usize("path_cap")?;
            if let Some(stride) = positive_usize("sample_stride")? {
                config.sample_stride = stride;
            }
            if let Some(threads) = positive_usize("enumeration_threads")? {
                config.enumeration_threads = threads;
            }
            if config.max_output_bytes.is_some() && config.sample_stride != 1 {
                return Err(format!("{root}.max_output_bytes 流式会话要求 sample_stride=1"));
            }
            Ok(config)
        })
        .transpose()
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

/// solve-state 的位向量初态；None 值表示稳定的符号值（`?` 或 `x`）。
#[derive(Clone, Debug)]
pub struct InitialRegisterConfig {
    pub name: String,
    /// (高位, 低位)；None 范围表示整个寄存器。
    pub fields: Vec<(Option<(u32, u32)>, Option<u64>)>,
}

fn get_initial_state(config: &Value) -> Result<Vec<InitialRegisterConfig>, String> {
    let Some(section) = config.get("initial_state") else { return Ok(Vec::new()) };
    let table = section.as_table().ok_or("initial_state 必须是表")?;
    let mut entries = Vec::new();
    for (name, entry) in table {
        if name == "x0" || name == "PC" {
            return Err(format!("initial_state.{} 不支持覆盖恒零寄存器或执行入口 PC", name));
        }
        let mut parsed = Vec::new();
        if let Some(pattern) = entry.as_str().and_then(|text| text.strip_prefix("0b")) {
            // 位模式从右向左对应 bit 0、bit 1……；未写出的高位继续符号化。
            let pattern = pattern.replace('_', "");
            if pattern.is_empty() {
                return Err(format!("initial_state.{}：位模式不能为空", name));
            }
            for (bit, value) in pattern.chars().rev().enumerate() {
                let bit = u32::try_from(bit).map_err(|_| "位模式过长")?;
                let value = match value {
                    '0' => Some(0),
                    '1' => Some(1),
                    '?' | 'x' => None,
                    _ => return Err(format!("initial_state.{}：位模式只接受 0、1、?、x 和分隔符 _", name)),
                };
                parsed.push((Some((bit, bit)), value));
            }
        } else {
            let concrete = match entry {
                Value::String(text) if text == "?" || text == "x" => None,
                _ => Some(parse_u64_value(entry, &format!("initial_state.{}", name))?),
            };
            parsed.push((None, concrete));
        }
        entries.push(InitialRegisterConfig { name: name.clone(), fields: parsed });
    }
    Ok(entries)
}

pub struct ISAConfig<B> {
    /// The identifier for the program counter register
    pub pc: Name,
    /// Map from cat sets to register event kinds
    pub register_event_sets: HashMap<String, Vec<RegisterKind>>,
    /// 配置中的汇编器命令；调用时才解析路径。
    pub assembler: Tool,
    /// 配置中的 objdump 命令；调用时才解析路径。
    pub objdump: Tool,
    /// 配置中的 nm 命令；调用时才解析路径。
    pub nm: Tool,
    /// 配置中的链接器命令；调用时才解析路径。
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
    /// 所有初态注入完成后、编码预检前施加的通用约束。
    pub initial_constraints: Vec<Exp<Loc<String>>>,
    /// 配置原语：分类随闭包保存，避免丢失配置值是否为 Uninit 的来源信息。
    pub const_primops: HashMap<String, (Reset<B>, crate::primop::Effect)>,
    /// Assumptions to use about function behaviour
    pub function_assumptions: Vec<(String, Vec<Option<Exp<Loc<String>>>>, Exp<Loc<String>>)>,
    /// Register synonyms to rename
    pub register_renames: HashMap<String, Name>,
    /// Registers to ignore during footprint analysis
    pub ignored_registers: HashSet<Name>,
    /// 不发布读写轨迹事件的寄存器；不影响状态更新或区域读写集。
    pub untraced_registers: HashSet<Name>,
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
    /// Optional page table configuration
    pub page_table_config: Option<PageTableConfig>,
    /// Optional PMP configuration
    pub pmp: Option<PmpConfig>,
    /// W21：`[symbolic_registers]` 声明的 CSR 符号化条目（solver 期注入）
    pub symbolic_registers: Vec<SymbolicRegisterConfig>,
    /// P1：`[[value_hints]]` 声明的值域 signposting 条目（solve-state 批调度）
    pub value_hints: Vec<ValueHintConfig>,
    /// P2 编码维度预分片：`[[encoding_slices]]` 声明（见 EncodingSliceConfig）
    pub encoding_slices: Vec<EncodingSliceConfig>,
    /// Optional CLINT enable flag
    pub clint_enabled: Option<bool>,
    /// solve-state 的 execution-limit TOML 覆盖；未配置时由调用方使用代码默认值。
    pub execution_limits: Option<ExecutionLimitsConfig>,
    pub initial_state: Vec<InitialRegisterConfig>,
}

/// 通用配置及 includes 合并后的原始表，供调用方解析 target 专属配置。
pub struct LoadedConfig<B: BV> {
    pub isa: ISAConfig<B>,
    pub merged: Value,
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
        if config.get("includes").is_some() {
            return Err("includes 需要通过 ISAConfig::from_file 加载，以确定相对路径".to_string());
        }

        // Insert the translation_function into the set of functions
        // to trace, if it is provided by the config
        let translation_function = get_translation_function(&config, symtab)?;
        let mut trace_functions = get_trace_functions(&config, symtab)?;
        if let Some(f) = translation_function {
            trace_functions.insert(f);
        }

        let toolchain = get_toolchain(&config, toolchain_name)?;

        let default_registers = get_default_registers(&config, symtab, type_info)?;
        let symbolic_registers = get_symbolic_registers(&config, symtab, &default_registers)?;
        let value_hints = get_value_hints(&config)?.unwrap_or_default();
        let encoding_slices = get_encoding_slices(&config)?.unwrap_or_default();
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
            reset_constraints: get_constraints(&config, "reset")?,
            initial_constraints: get_constraints(&config, "initial")?,
            const_primops: get_const_primops(&config, symtab, type_info)?,
            function_assumptions: Vec::new(),
            register_renames: get_register_renames(&config, symtab)?,
            ignored_registers: get_registers_set(&config, "ignore", symtab)?,
            untraced_registers: get_registers_set(&config, "ignore_events", symtab)?,
            relaxed_registers: get_registers_set(&config, "relaxed", symtab)?,
            probes: HashSet::new(),
            probe_functions: HashSet::new(),
            trace_functions,
            translation_function,
            in_program_order: get_in_program_order(&config, symtab)?,
            default_sizeof: get_default_sizeof(&config)?,
            zero_announce_exit: get_zero_announce_exit(&config)?,
            memory_regions: get_memory_regions(&config)?,
            page_table_config: get_page_table_config(&config)?,
            pmp,
            symbolic_registers,
            value_hints,
            encoding_slices,
            clint_enabled: get_clint_enabled(&config)?,
            execution_limits: get_execution_limits_config(&config)?,
            initial_state: get_initial_state(&config)?,
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
        Self::from_file_with_merged(hasher, path, toolchain_name, symtab, type_info).map(|loaded| loaded.isa)
    }

    /// 同时返回合并后的 TOML；不解释调用方的 target 字段。
    pub fn from_file_with_merged<P: AsRef<Path>>(
        hasher: &mut Sha256,
        path: P,
        toolchain_name: Option<&str>,
        symtab: &Symtab,
        type_info: &IRTypeInfo,
    ) -> Result<LoadedConfig<B>, String> {
        let contents = read_config_contents(path.as_ref(), &mut Vec::new())?;
        hasher.input(&contents);
        hasher.input(toolchain_name.unwrap_or("default"));
        let merged = contents.parse::<Value>().expect("已加载配置必须是有效 TOML");
        let isa = Self::parse(&contents, toolchain_name, symtab, type_info)
            .map_err(|msg| format!("{}: {}", path.as_ref().display(), msg))?;
        Ok(LoadedConfig { isa, merged })
    }
}

/// 按 includes 数组顺序加载，再覆盖本文件；相对路径以声明文件的目录为基准。
/// 表递归合并，其余值（含数组）整体替换，不为具体架构设置特殊合并规则。
fn read_config_contents(path: &Path, stack: &mut Vec<PathBuf>) -> Result<String, String> {
    let canonical = path.canonicalize().map_err(|error| format!("读取配置 {} 失败：{}", path.display(), error))?;
    if stack.contains(&canonical) {
        return Err(format!("配置 includes 循环：{:?} -> {}", stack, path.display()));
    }
    let contents =
        std::fs::read_to_string(path).map_err(|error| format!("读取配置 {} 失败：{}", path.display(), error))?;
    let mut config = contents.parse::<Value>().map_err(|error| format!("{}：{}", path.display(), error))?;
    let Some(includes) = config.as_table_mut().expect("TOML 顶层必须是表").remove("includes") else {
        return Ok(contents);
    };
    let includes = includes.as_array().ok_or_else(|| format!("{}：includes 必须是文件名数组", path.display()))?;
    // 规范路径只用于判环；相对 include 必须保留任务目录中的符号链接布局。
    stack.push(canonical);
    let mut merged = Value::Table(toml::value::Table::new());
    for include in includes {
        let include = include.as_str().ok_or_else(|| format!("{}：includes 只接受文件名字符串", path.display()))?;
        let included = read_config_contents(&path.parent().expect("配置文件路径必须有父目录").join(include), stack)?;
        merge_config_values(&mut merged, included.parse::<Value>().expect("已加载配置必须是有效 TOML"));
    }
    stack.pop();
    merge_config_values(&mut merged, config);
    Ok(merged.to_string())
}

fn merge_config_values(base: &mut Value, overrides: Value) {
    match (base, overrides) {
        (Value::Table(base), Value::Table(overrides)) => {
            for (key, value) in overrides {
                match base.get_mut(&key) {
                    Some(previous) => merge_config_values(previous, value),
                    None => {
                        base.insert(key, value);
                    }
                }
            }
        }
        (base, overrides) => *base = overrides,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;

    #[test]
    fn register_event_filter_is_explicit_and_validated() {
        let mut symtab = Symtab::new();
        let encoded = zencode::encode("large_state");
        let reg = symtab.intern(&encoded);
        let empty: HashSet<Name> = get_registers_set(&"".parse::<Value>().unwrap(), "ignore_events", &symtab).unwrap();
        assert!(empty.is_empty());
        let config = "[registers]\nignore_events=['large_state']".parse::<Value>().unwrap();
        let set: HashSet<Name> = get_registers_set(&config, "ignore_events", &symtab).unwrap();
        assert_eq!(set, HashSet::from([reg]));
        for text in ["[registers]\nignore_events=42", "[registers]\nignore_events=['missing']"] {
            assert!(
                get_registers_set::<HashSet<Name>>(&text.parse::<Value>().unwrap(), "ignore_events", &symtab).is_err()
            );
        }
    }

    #[test]
    fn config_includes_merge_relative_files_in_order() {
        let dir = std::env::temp_dir().join(format!("isla-config-includes-{}", std::process::id()));
        std::fs::create_dir_all(dir.join("overrides")).unwrap();
        std::fs::write(
            dir.join("base.toml"),
            "pc='PC'\n[constraints]\ninitial=['base']\n[symbolic_registers.mstatus]\npin_mask='0xf'\npin_value='0x8'\n",
        )
        .unwrap();
        std::fs::write(dir.join("extra.toml"), "[symbolic_registers.mstatus]\npin_value='0x4'\n").unwrap();
        let top = dir.join("overrides/clause.toml");
        std::fs::write(&top, "includes=['../base.toml','../extra.toml']\n[constraints]\ninitial=['clause']\n[symbolic_registers.mstatus]\nnonzero_groups=[[13,14]]\n").unwrap();
        let value = read_config_contents(&top, &mut Vec::new()).unwrap().parse::<Value>().unwrap();
        assert_eq!(value["pc"].as_str(), Some("PC"));
        assert_eq!(value["symbolic_registers"]["mstatus"]["pin_mask"].as_str(), Some("0xf"));
        assert_eq!(value["symbolic_registers"]["mstatus"]["pin_value"].as_str(), Some("0x4"));
        assert_eq!(value["symbolic_registers"]["mstatus"]["nonzero_groups"][0][1].as_integer(), Some(14));
        assert_eq!(value["constraints"]["initial"].as_array().unwrap().len(), 1);
        assert_eq!(value["constraints"]["initial"][0].as_str(), Some("clause"));
        assert!(value.get("includes").is_none());
        // 同一基础文件可被不同分支共享，不应误判成递归环。
        std::fs::write(dir.join("extra.toml"), "includes=['base.toml']\n").unwrap();
        assert!(read_config_contents(&top, &mut Vec::new()).is_ok());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn config_includes_reject_cycles_missing_files_and_invalid_entries() {
        let dir = std::env::temp_dir().join(format!("isla-config-includes-errors-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let top = dir.join("top.toml");
        for invalid in ["includes='base.toml'", "includes=[42]"] {
            std::fs::write(&top, invalid).unwrap();
            assert!(read_config_contents(&top, &mut Vec::new()).unwrap_err().contains("includes"));
        }
        std::fs::write(&top, "includes=['missing.toml']").unwrap();
        assert!(read_config_contents(&top, &mut Vec::new()).unwrap_err().contains("missing.toml"));
        std::fs::write(&top, "includes=['./top.toml']").unwrap();
        assert!(read_config_contents(&top, &mut Vec::new()).unwrap_err().contains("循环"));
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    #[cfg(unix)]
    fn config_includes_resolve_relative_to_staged_symlink() {
        let dir = std::env::temp_dir().join(format!("isla-config-includes-symlink-{}", std::process::id()));
        std::fs::create_dir_all(dir.join("objects")).unwrap();
        std::fs::create_dir_all(dir.join("staged")).unwrap();
        std::fs::write(dir.join("objects/base"), "pc='PC'").unwrap();
        std::fs::write(dir.join("objects/override"), "includes=['base.toml']\nzero_announce_exit=true").unwrap();
        std::os::unix::fs::symlink(dir.join("objects/base"), dir.join("staged/base.toml")).unwrap();
        std::os::unix::fs::symlink(dir.join("objects/override"), dir.join("staged/config.toml")).unwrap();
        let text = read_config_contents(&dir.join("staged/config.toml"), &mut Vec::new()).unwrap();
        let value = text.parse::<Value>().unwrap();
        assert_eq!(value["pc"].as_str(), Some("PC"));
        assert_eq!(value["zero_announce_exit"].as_bool(), Some(true));
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn config_includes_load_through_isa_config_and_keep_conflict_checks() {
        let dir = std::env::temp_dir().join(format!("isla-config-includes-api-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let base = r#"pc = "PC"
[[toolchain]]
name = "default"
assembler = "as"
objdump = "objdump"
nm = "nm"
linker = "ld"
[mmu]
page_table_base = "0"
page_size = "4096"
s2_page_table_base = "0"
s2_page_size = "4096"
[threads]
base = "0"
top = "4096"
stride = "4096"
[symbolic_addrs]
base = "4096"
top = "8192"
stride = "16"
[registers.defaults]
r0 = "0x0000000000000000"
"#;
        std::fs::write(dir.join("base.toml"), base).unwrap();
        let path = dir.join("clause.toml");
        std::fs::write(&path, "includes=['base.toml']\nzero_announce_exit=true").unwrap();
        let mut symtab = Symtab::new();
        symtab.intern("zPC");
        symtab.intern("zr0");
        let types = IRTypeInfo::new::<B64>(&[]);
        let config = ISAConfig::<B64>::from_file(&mut Sha256::new(), &path, None, &symtab, &types).unwrap();
        assert!(config.zero_announce_exit);
        assert_eq!(config.default_registers.len(), 1);
        std::fs::write(&path, "includes=['base.toml']\n[symbolic_registers]\nr0='symbolic'").unwrap();
        let result = ISAConfig::<B64>::from_file(&mut Sha256::new(), &path, None, &symtab, &types);
        assert!(result.err().unwrap().contains("同名冲突"));
        let result = ISAConfig::<B64>::parse("includes=['base.toml']", None, &symtab, &types);
        assert!(result.err().unwrap().contains("from_file"));
        std::fs::remove_dir_all(dir).unwrap();
    }

    fn merge_config(text: &str) -> Result<ExecutionLimitsConfig, String> {
        get_execution_limits_config(&text.parse::<Value>().unwrap()).map(Option::unwrap)
    }

    #[test]
    fn arm_error_batch_size_accepts_only_positive_integers() {
        let table = "[execution_limits.path_merge.solver]";
        for size in [1, 8, 16] {
            assert!(merge_config(&format!("{table}\narm_error_batch_size={size}")).is_ok());
        }
        for size in ["0", "-1", "true", "1.5"] {
            assert!(merge_config(&format!("{table}\narm_error_batch_size={size}")).is_err());
        }
    }

    #[test]
    fn merge_concrete_values_defaults_on_and_accepts_explicit_false() {
        use crate::executor::ExecutionLimits;
        let symtab = Symtab::new();
        assert!(ExecutionLimits::default().merge_concrete_values);
        for (text, expected) in [
            ("[execution_limits]", true),
            ("[execution_limits.path_merge]", true),
            ("[execution_limits.path_merge]\nmerge_concrete_values=true", true),
            ("[execution_limits.path_merge]\nmerge_concrete_values=false", false),
        ] {
            let config = merge_config(text).unwrap();
            assert_eq!(config.path_merge.merge_concrete_values, expected);
            assert_eq!(ExecutionLimits::default().with_config(&config, &symtab).merge_concrete_values, expected);
        }
    }

    #[test]
    fn prune_constant_branches_config_scope_and_type() {
        let defaults = merge_config("[execution_limits.path_merge]").unwrap();
        assert!(RegionOptions::from_config(&defaults).prune_constant_branches);
        assert!(RegionOptions::default().prune_constant_branches);
        for enabled in [false, true] {
            let config =
                merge_config(&format!("[execution_limits.path_merge]\nprune_constant_branches={enabled}")).unwrap();
            assert_eq!(RegionOptions::from_config(&config).prune_constant_branches, enabled);
        }
        for section in [
            "execution_limits",
            "execution_limits.region_options",
            "execution_limits.solver",
            "execution_limits.path_merge.diagnostics",
        ] {
            assert!(merge_config(&format!("[{section}]\nprune_constant_branches=true")).is_err());
        }
        assert!(merge_config("[execution_limits.path_merge]\nfold_constant_conditions=true").is_err());
        for value in ["1", "'true'", "[]"] {
            assert!(merge_config(&format!("[execution_limits.path_merge]\nprune_constant_branches={value}")).is_err());
        }
    }

    #[test]
    fn config_layout_new_sections_preserve_runtime_defaults_and_local_semantics() {
        use crate::executor::ExecutionLimits;
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["model.sail"]);
        let defaults = merge_config(
            "[execution_limits.path_merge]\n[execution_limits.solver]\n[execution_limits.path_merge.diagnostics]",
        )
        .unwrap();
        assert_eq!(defaults, ExecutionLimitsConfig::default());
        let limits = ExecutionLimits::default().with_config(&defaults, &symtab);
        assert!(!limits.path_merging);
        assert_eq!(limits.region_step_budget, None);
        let config = merge_config(
            r#"
[execution_limits.path_merge]
enabled = true
step_budget = -1
defer_exit_check = true
[execution_limits.solver]
bool_proof_rlimit = 7
[execution_limits.path_merge.diagnostics]
progress = true
[[execution_limits.path_merge.regions]]
kind = "limit_filter"
file = "model.sail"
start_line = 1
start_column = 0
end_line = 9
end_column = 0
[[execution_limits.path_merge.regions]]
kind = "branch_limit"
max_forks_per_branch = 3
file = "model.sail"
start_line = 2
start_column = 0
end_line = 4
end_column = 0
"#,
        )
        .unwrap();
        let limits = ExecutionLimits::default().with_config(&config, &symtab);
        assert!(limits.path_merging);
        assert_eq!(limits.region_step_budget, None);
        assert_eq!(limits.regions.as_ref().unwrap().len(), 1);
        assert_eq!(limits.branch_region_limits[0].1, 3);
    }

    #[test]
    fn config_layout_removed_fields_report_new_locations() {
        for (old, new) in [
            ("path_merging=true", "execution_limits.path_merge.enabled"),
            ("region_step_budget=1", "execution_limits.path_merge.step_budget"),
            ("region_options={}", "execution_limits.path_merge"),
            ("regions=[]", "execution_limits.path_merge.regions"),
            ("branch_region_limits=[]", "execution_limits.path_merge.regions"),
            ("region_fork_limits=[]", "execution_limits.path_merge.regions"),
            ("merge_policy=[]", "execution_limits.path_merge.regions"),
            ("merge_enumeration={}", "execution_limits.path_merge.enumeration"),
        ] {
            let error = merge_config(&format!("[execution_limits]\n{old}")).unwrap_err();
            assert!(error.contains(new), "{old}: {error}");
        }
        for section in ["solver", "path_merge", "path_merge.diagnostics"] {
            assert!(merge_config(&format!("[execution_limits.{section}]\nunknown=true")).is_err());
        }
    }

    #[test]
    fn no_smt_solver_config_defaults_switches_and_runtime_snapshot() {
        let defaults = merge_config("[execution_limits.solver]").unwrap();
        assert_eq!(RegionOptions::from_config(&defaults), RegionOptions::default());
        for field in ["skip_branch_checks", "skip_bool_proofs", "no_smt", "no_smt_keep_bool_proofs"] {
            let prefix = if field == "no_smt_keep_bool_proofs" { "no_smt=true\n" } else { "" };
            let config = merge_config(&format!("[execution_limits.solver]\n{prefix}{field}=true")).unwrap();
            let expected: RegionOptions = toml::from_str(&format!("{prefix}{field}=true")).unwrap();
            assert_eq!(RegionOptions::from_config(&config), expected, "{field}");
            assert_eq!(
                merge_config(&format!("[execution_limits.solver]\n{field}=false")).unwrap(),
                defaults,
                "{field}"
            );
            for value in ["1", "'true'", "[]"] {
                assert!(merge_config(&format!("[execution_limits.solver]\n{field}={value}")).is_err());
            }
        }
    }

    #[test]
    fn no_smt_solver_config_rejects_old_and_misplaced_fields() {
        for field in ["skip_branch_checks", "skip_bool_proofs", "no_smt", "no_smt_keep_bool_proofs"] {
            for section in [
                "execution_limits.region_options",
                "execution_limits",
                "execution_limits.path_merge",
                "execution_limits.path_merge.diagnostics",
            ] {
                let error = merge_config(&format!("[{section}]\n{field}=true")).unwrap_err();
                assert!(
                    error.contains(if section.ends_with("region_options") { "execution_limits.solver" } else { field }),
                    "{section}.{field}: {error}"
                );
            }
        }
    }

    #[test]
    fn no_smt_solver_config_proof_dependency() {
        for text in ["no_smt_keep_bool_proofs=true", "no_smt=true\nno_smt_keep_bool_proofs=true\nskip_bool_proofs=true"]
        {
            assert!(merge_config(&format!("[execution_limits.solver]\n{text}")).is_err());
        }
        merge_config("[execution_limits.solver]\nno_smt=true\nno_smt_keep_bool_proofs=true").unwrap();
    }

    #[test]
    fn resident_batch_size_toml_requires_positive_integer() {
        assert_eq!(merge_config("[execution_limits]").unwrap().judge_resident_batch_size, None);
        for size in [1, 2, 32] {
            assert_eq!(
                merge_config(&format!("[execution_limits]\njudge_resident_batch_size={size}"))
                    .unwrap()
                    .judge_resident_batch_size,
                Some(size)
            );
        }
        for value in ["0", "-1", "true", "'32'", "1.5"] {
            assert!(merge_config(&format!("[execution_limits]\njudge_resident_batch_size={value}")).is_err());
        }
    }

    #[test]
    fn region_merge_finite_domain_config() {
        let defaults = merge_config("[execution_limits.path_merge]").unwrap().path_merge;
        assert!(defaults.finite_domain_enumeration);
        assert!(defaults.finite_domain_ground_eval);
        for enabled in [false, true] {
            let config =
                merge_config(&format!(
                    "[execution_limits.path_merge]\nfinite_domain_enumeration={enabled}\nfinite_domain_ground_eval={enabled}"
                )).unwrap();
            assert_eq!(config.path_merge.finite_domain_enumeration, enabled);
            assert_eq!(config.path_merge.finite_domain_ground_eval, enabled);
        }
        for section in ["execution_limits", "execution_limits.path_merge", "execution_limits.solver"] {
            assert!(merge_config(&format!("[{section}]\nfinite_domain_max=64")).is_err());
        }
        for section in ["execution_limits", "execution_limits.solver"] {
            assert!(merge_config(&format!("[{section}]\nfinite_domain_enumeration=true")).is_err());
        }
    }

    #[test]
    fn region_newbase_path_merge_fields_and_defaults() {
        let defaults = RegionOptions::from_config(&merge_config("[execution_limits.path_merge]").unwrap());
        assert!(defaults.defer_range_proofs && defaults.defer_ctor_checks);
        let disabled =
            merge_config("[execution_limits.path_merge]\ndefer_range_proofs=false\ndefer_ctor_checks=false").unwrap();
        let disabled = RegionOptions::from_config(&disabled);
        assert!(!disabled.defer_range_proofs && !disabled.defer_ctor_checks);
        let limits = merge_config("[execution_limits.path_merge]\nmax_merge_depth=32\ndefer_range_proofs=true\ndefer_ctor_checks=true\nstep_budget=-1\n[execution_limits.solver]\nno_smt=true").unwrap();
        let options = RegionOptions::from_config(&limits);
        assert_eq!(options.merge_depth_limit(), Some(32));
        assert!(options.defer_range_proofs && options.defer_ctor_checks && options.no_smt);
        assert_eq!(crate::executor::ExecutionLimits::default().region_step_budget, None);
        for field in [
            "max_merge_depth=0",
            "max_merge_depth=-2",
            "max_merge_depth=true",
            "defer_range_proofs=1",
            "defer_ctor_checks=1",
        ] {
            assert!(merge_config(&format!("[execution_limits.path_merge]\n{field}")).is_err(), "{field}");
        }
        for field in ["max_merge_depth=32", "defer_range_proofs=true", "defer_ctor_checks=true"] {
            assert!(merge_config(&format!("[execution_limits]\n{field}")).is_err());
            assert!(merge_config(&format!("[execution_limits.region_options]\n{field}")).is_err());
        }
    }

    #[test]
    fn unknown_taxonomy_rejects_removed_combined_switch() {
        assert!(merge_config("[execution_limits.path_merge]\npartial_commit_solver=true").is_err());
        assert!(merge_config("[execution_limits.path_merge]\npartial_commit_solver_unknown=true").is_err());
        use crate::executor::SpeculativeRejectReason::*;
        let switches = [
            ("partial_commit_finite_domain", UnknownFiniteDomain),
            ("partial_commit_unknown_z3", UnknownZ3),
            ("partial_commit_z3_timeout", Z3Timeout),
            ("partial_commit_z3_resource_exhausted", Z3ResourceExhausted),
            ("partial_commit_deferred_mode", UnknownDeferredMode),
        ];
        for (field, enabled) in switches {
            let config = merge_config(&format!("[execution_limits.path_merge]\n{field}=true")).unwrap();
            let options = RegionOptions::from_config(&config);
            for (_, reason) in switches {
                assert_eq!(reason.partial_commit(&options), reason == enabled);
            }
            assert!(!PathTimeout.partial_commit(&options));
            assert!(!ExitUnsat.partial_commit(&options));
        }
    }

    #[test]
    fn region_options_toml_accepts_switches_and_limits() {
        assert!(!RegionOptions::default().partial_commit_retry_operand);
        assert!(!RegionOptions::default().partial_commit_prefix);
        assert!(!RegionOptions::default().partial_commit_structure);
        assert!(!RegionOptions::default().partial_commit_state_effect);
        assert!(!RegionOptions::default().partial_commit_control);
        let retry = merge_config("[execution_limits.path_merge]\npartial_commit_retry_operand=true").unwrap();
        assert!(RegionOptions::from_config(&retry).partial_commit_retry_operand);
        assert!(merge_config(
            "[execution_limits.path_merge]\ndefer_exit_check=true\npartial_commit_unknown_z3=true\nwitness_eval=true\n[execution_limits.solver]\nbool_proof_rlimit=1"
        )
        .is_ok());
        assert!(merge_config("[execution_limits.path_merge.diagnostics]\nquery_dump_sites=['f@1']\nquery_dump_dir='queries'\nsame_context_sites=['f@1']").is_ok());
    }

    #[test]
    fn region_options_toml_scalar_and_loop_defaults() {
        let config = merge_config("[execution_limits.path_merge]").unwrap();
        assert_eq!(config.path_merge, PathMergeConfig::default());
        assert!(config.path_merge.symbolic_scalar_resolver);
        assert!(config.path_merge.loop_fold_shapes);
        assert!(config.path_merge.prefix_compact);
        assert!(!config.path_merge.partial_commit_prefix);
        assert!(!config.path_merge.arms_as_tasks);

        let options = RegionOptions::from_config(&config);
        assert!(options.symbolic_scalar_resolver);
        assert!(options.loop_fold_shapes);
        assert!(options.prefix_compact);
        assert!(!options.partial_commit_prefix);
    }

    #[test]
    fn region_options_lazy_scope_toml_defaults_and_dependency() {
        let defaults = merge_config("[execution_limits.path_merge]\n").unwrap().path_merge;
        assert!(!defaults.lazy_z3_scope);
        let enabled = merge_config("[execution_limits.path_merge]\nlazy_z3_scope=true").unwrap().path_merge;
        assert!(enabled.lazy_z3_scope);
        assert!(!enabled.defer_exit_check, "不依赖 defer 的配置校验；作用域创建时才决定是否生效");
        let disabled = merge_config("[execution_limits.path_merge]\nlazy_z3_scope=false").unwrap().path_merge;
        assert_eq!(disabled, defaults);
        for value in ["1", "'true'", "[]"] {
            assert!(merge_config(&format!("[execution_limits.path_merge]\nlazy_z3_scope={value}")).is_err());
        }
    }

    #[test]
    fn region_options_toml_rejects_invalid_values() {
        for (section, fields) in [
            ("path_merge", "defer_exit_check=1"),
            ("solver", "bool_proof_rlimit=-1"),
            ("solver", "bool_proof_rlimit=4294967296"),
            ("path_merge.diagnostics", "query_dump_sites='f@1'"),
            ("path_merge", "unknown=true"),
            ("path_merge.diagnostics", "same_context_sites=['a','b','c']"),
            ("path_merge.diagnostics", "query_dump_sites=['f@1']"),
            ("path_merge.regions", "mode='off'"),
        ] {
            assert!(merge_config(&format!("[execution_limits.{section}]\n{fields}")).is_err(), "{section}: {fields}");
        }
    }

    #[test]
    fn bv_rewrite_config_bool_lists_and_strict_location() {
        use crate::smt::rewrite::BvRewrite;

        let all = BvRewrite::parse("true").unwrap();
        for text in ["[execution_limits]\n", "[execution_limits.solver]\n"] {
            let config = merge_config(text).unwrap();
            assert_eq!(config.solver.bv_rewrite, all);
            assert_eq!(RegionOptions::from_config(&config).bv_rewrite, all);
        }
        for (value, rules) in [
            ("true", "true"),
            ("false", "false"),
            ("[]", "false"),
            ("[\"mask-and\"]", "mask-and"),
            ("[\"data-ite-eq\",\"sign-bound\"]", "data-ite-eq,sign-bound"),
        ] {
            let config = merge_config(&format!("[execution_limits.solver]\nbv_rewrite={value}")).unwrap();
            let expected = BvRewrite::parse(rules).unwrap();
            assert_eq!(config.solver.bv_rewrite, expected);
            assert_eq!(RegionOptions::from_config(&config).bv_rewrite, expected);
        }
        for text in
            ["[execution_limits.solver]\nbv_rewrite=[\"oops\"]", "[execution_limits.path_merge]\nbv_rewrite=true"]
        {
            assert!(merge_config(text).is_err());
        }
    }

    #[test]
    fn config_layout_freeze_snapshot_preserves_all_twenty_options() {
        let config = merge_config(
            r#"
[execution_limits.solver]
bool_proof_rlimit = 17
skip_branch_checks = true
skip_bool_proofs = true
no_smt = true
no_smt_keep_bool_proofs = false
[execution_limits.path_merge]
defer_exit_check = true
lazy_z3_scope = true
witness_eval = true
prefix_compact = true
[execution_limits.path_merge.diagnostics]
witness_shadow = true
witness_local_shadow = true
bool_proof_profile = true
progress = true
native_snapshot = true
call_census = true
probe_round_cost = true
probe_query_timings = true
query_dump_sites = ["f@1"]
same_context_sites = ["g@2"]
query_dump_dir = "queries"
obligation_dump_dir = "obligations"
"#,
        )
        .unwrap();
        let options = RegionOptions::from_config(&config);
        assert_eq!(
            options,
            RegionOptions {
                bv_rewrite: Default::default(),
                max_merge_depth: None,
                symbolic_scalar_resolver: true,
                scalar_domain_persist: true,
                width_closed_continuation: false,
                defer_range_proofs: true,
                defer_ctor_checks: true,
                prune_constant_branches: true,
                arm_error_leaf: false,
                arm_error_batch_size: PathMergeConfig::default().solver.arm_error_batch_size,
                skip_branch_checks: true,
                skip_bool_proofs: true,
                no_smt: true,
                no_smt_keep_bool_proofs: false,
                defer_exit_check: true,
                partial_commit_finite_domain: false,
                partial_commit_unknown_z3: false,
                partial_commit_z3_timeout: false,
                partial_commit_z3_resource_exhausted: false,
                partial_commit_deferred_mode: false,
                partial_commit_retry_operand: false,
                partial_commit_prefix: false,
                partial_commit_structure: false,
                partial_commit_state_effect: false,
                partial_commit_control: false,
                lazy_z3_scope: true,
                witness_eval: true,
                prefix_compact: true,
                loop_fold_shapes: true,
                witness_shadow: true,
                witness_local_shadow: true,
                bool_proof_profile: true,
                progress: true,
                native_snapshot: true,
                call_census: true,
                probe_round_cost: true,
                probe_query_timings: true,
                bool_proof_rlimit: 17,
                query_dump_sites: vec!["f@1".into()],
                same_context_sites: vec!["g@2".into()],
                query_dump_dir: Some("queries".into()),
                obligation_dump_dir: Some("obligations".into()),
            }
        );
    }

    #[test]
    fn model_exception_filter_config_accepts_constructor_list() {
        assert!(merge_config(
            "[execution_limits]\nfilter_model_exceptions=['Error_internal_error','Error_reserved_behavior']"
        )
        .is_ok());
        assert_eq!(
            merge_config("[execution_limits]\nfilter_model_exceptions=[]").unwrap().filter_model_exceptions,
            Vec::<String>::new()
        );
        assert!(merge_config("[execution_limits]").unwrap().filter_model_exceptions.is_empty());
        assert_eq!(
            merge_config("[execution_limits]\nfilter_model_exceptions=['Custom_error']")
                .unwrap()
                .filter_model_exceptions,
            vec!["Custom_error"]
        );
        for value in ["true", "'Error_internal_error'", "[1]", "['']"] {
            assert!(merge_config(&format!("[execution_limits]\nfilter_model_exceptions={value}")).is_err());
        }
    }

    #[test]
    fn execution_limits_flat_strategy_and_ordered_events() {
        let config = merge_config("[execution_limits.path_merge]\nstrategy='flat'\nordered_events=true").unwrap();
        assert_eq!(config.path_merge.strategy, Some(MergeStrategy::Flat));
        assert_eq!(config.path_merge.ordered_events, Some(true));
        let defaults = merge_config("[execution_limits]").unwrap();
        assert!(defaults.path_merge.strategy.is_none() && defaults.path_merge.ordered_events.is_none());
        for body in [
            "[execution_limits]\nmerge_strategy='flat'",
            "[execution_limits]\nordered_events=true",
            "[execution_limits.path_merge]\nmerge_strategy='flat'",
            "[execution_limits.path_merge]\nstrategy='bad'",
            "[execution_limits.path_merge]\nordered_events=1",
            "[execution_limits.region_options]\nmerge_strategy='flat'",
        ] {
            assert!(merge_config(body).is_err(), "{body}");
        }
    }

    #[test]
    fn execution_limits_region_fragment_limit_values() {
        for (limit, expected) in [("", None), ("max_fragments = -1", None), ("max_fragments = 8", Some(8))] {
            let config = merge_config(&format!("[execution_limits.path_merge]\n{limit}")).unwrap();
            assert_eq!(
                crate::executor::ExecutionLimits::default().with_config(&config, &Symtab::new()).max_region_fragments,
                expected
            );
        }
        for limit in ["0", "-2", "true"] {
            assert!(merge_config(&format!("[execution_limits.path_merge]\nmax_fragments = {limit}")).is_err());
        }
    }

    #[test]
    fn match_failure_filter_defaults_off_and_requires_a_boolean() {
        assert!(!merge_config("[execution_limits]").unwrap().filter_match_failures);
        assert!(!merge_config("[execution_limits]\nfilter_match_failures=false").unwrap().filter_match_failures);
        assert!(merge_config("[execution_limits]\nfilter_match_failures=true").unwrap().filter_match_failures);
        assert!(merge_config("[execution_limits]\nfilter_match_failures=1").is_err());
    }

    #[test]
    fn execution_limits_region_step_budget_values() {
        for value in ["8192", "1", "32768", "-1"] {
            assert!(
                merge_config(&format!("[execution_limits]\n\n[execution_limits.path_merge]\nstep_budget = {value}"))
                    .is_ok(),
                "{value}"
            );
        }
        for value in ["0", "-2", "-9223372036854775808", "true", "1.5", "\"8192\""] {
            assert!(
                merge_config(&format!("[execution_limits]\n\n[execution_limits.path_merge]\nstep_budget = {value}"))
                    .is_err(),
                "{value}"
            );
        }
    }

    #[test]
    fn execution_limits_merge_enumeration_sample_stride() {
        let config = merge_config("[execution_limits.path_merge.enumeration]\nsample_stride = 7");
        assert!(config.is_ok(), "正整数 stride 必须可解析：{config:?}");
        assert_eq!(config.unwrap().path_merge.enumeration.unwrap().sample_stride, 7);
        assert_eq!(MergeEnumerationConfig::default().sample_stride, 1);
        for value in ["0", "-1", "true", "1.5", "\"7\""] {
            assert!(
                merge_config(&format!("[execution_limits.path_merge.enumeration]\nsample_stride = {value}")).is_err()
            );
        }
    }

    #[test]
    fn execution_limits_merge_enumeration_threads() {
        let config = merge_config("[execution_limits.path_merge.enumeration]\nenumeration_threads = 3").unwrap();
        assert_eq!(config.path_merge.enumeration.unwrap().enumeration_threads, 3);
        for value in ["0", "-1", "true", "\"4\""] {
            assert!(merge_config(&format!("[execution_limits.path_merge.enumeration]\nenumeration_threads = {value}"))
                .is_err());
        }
        assert_eq!(
            MergeEnumerationConfig::default().enumeration_threads,
            std::thread::available_parallelism().unwrap().get().min(16)
        );
    }

    #[test]
    fn execution_limits_predict_不生成样本且至少200次独立探测() {
        let text="[execution_limits.path_merge.enumeration]\nenabled=true\nmode='predict'\npredict_probes=256\npredict_seed=7\npredict_domain_cap=256";
        let config = merge_config(text).unwrap().path_merge.enumeration.unwrap();
        assert_eq!(config.mode, MergeEnumerationMode::Predict);
        assert_eq!(config.predict_probes, Some(256));
        assert_eq!(config.predict_domain_cap, Some(256));
        assert!(merge_config(&text.replace("predict_probes=256", "")).is_err());
        assert!(merge_config(&text.replace("predict_domain_cap=256", "")).is_err());
        for probes in ["0", "199", "-1"] {
            assert!(merge_config(&text.replace("predict_probes=256", &format!("predict_probes={probes}"))).is_err());
        }
    }

    #[test]
    fn execution_limits_a1_终值查询仅在显式配置时有独立时限() {
        let table = "[execution_limits.solver]";
        assert_eq!(merge_config(table).unwrap().solver.model_timeout_ms, None);
        let explicit = merge_config(&format!("{table}\nmodel_timeout_ms=5000")).unwrap();
        assert_eq!(explicit.solver.model_timeout_ms.unwrap().get(), 5000);
        for invalid in ["0", "-1", "1.5", "true"] {
            assert!(merge_config(&format!("{table}\nmodel_timeout_ms={invalid}")).is_err());
        }
    }

    #[test]
    fn execution_limits_a1_单二进制省略配置时无枚举和字节上限() {
        let text = "[execution_limits.path_merge.enumeration]\nenabled=true\n[[execution_limits.path_merge.enumeration.outputs]]\nformat='binary'\npath='samples.bin'";
        let config = merge_config(text).unwrap().path_merge.enumeration.unwrap();
        assert_eq!(config.max_output_bytes, None);
        assert_eq!(config.class_cap, None);
        assert_eq!(config.path_cap, None);
        assert_eq!(config.sample_stride, 1);
    }

    #[test]
    fn execution_limits_output_budget_必须为正且只用二进制() {
        let text = "[execution_limits.path_merge.enumeration]\nenabled=true\nmax_output_bytes=25000000000\n[[execution_limits.path_merge.enumeration.outputs]]\nformat='binary'\npath='samples.bin'";
        assert_eq!(merge_config(text).unwrap().path_merge.enumeration.unwrap().max_output_bytes, Some(25_000_000_000));
        assert!(merge_config(&text.replace("25000000000", "0")).is_err());
        assert!(merge_config(&text.replace("'binary'", "'v1_jsonl'")).is_err());
    }

    #[test]
    fn execution_limits_merge_enumeration_output_backends() {
        let config = merge_config(
            r#"
            [[execution_limits.path_merge.enumeration.outputs]]
            format = "v1_jsonl"
            path = "samples.jsonl"
            [[execution_limits.path_merge.enumeration.outputs]]
            format = "compact_jsonl"
            path = "compact.jsonl"
            [[execution_limits.path_merge.enumeration.outputs]]
            format = "binary"
            path = "samples.bin"
        "#,
        )
        .unwrap();
        assert_eq!(config.path_merge.enumeration.unwrap().outputs.len(), 3);
        for fields in [
            "format='unknown'\npath='a'",
            "format='binary'",
            "format='binary'\npath=''",
            "format='binary'\npath='a'\nextra=1",
        ] {
            assert!(merge_config(&format!("[[execution_limits.path_merge.enumeration.outputs]]\n{fields}")).is_err());
        }
    }

    #[test]
    fn execution_limits_merge_enumeration_count_mode() {
        for mode in ["count", "samples"] {
            assert!(merge_config(&format!(
                "[execution_limits.path_merge.enumeration]\nmode = \"{mode}\"\nenabled = true"
            ))
            .is_ok());
        }
        for mode in ["\"unknown\"", "1", "true"] {
            assert!(merge_config(&format!("[execution_limits.path_merge.enumeration]\nmode = {mode}")).is_err());
        }
    }

    #[test]
    fn execution_limits_merge_enumeration_table() {
        let config =
            merge_config("[execution_limits.path_merge.enumeration]\nenabled = true\nclass_cap = 7\npath_cap = 11")
                .unwrap();
        assert_eq!(
            config.path_merge.enumeration.unwrap(),
            MergeEnumerationConfig { enabled: true, class_cap: Some(7), path_cap: Some(11), ..Default::default() }
        );
        assert_eq!(
            merge_config("[execution_limits.path_merge.enumeration]").unwrap().path_merge.enumeration.unwrap(),
            MergeEnumerationConfig::default()
        );
        assert!(merge_config("[execution_limits]").unwrap().path_merge.enumeration.is_none());
        for fields in ["enabled = 1", "class_cap = 0", "path_cap = -1", "unknown = true"] {
            assert!(merge_config(&format!("[execution_limits.path_merge.enumeration]\n{fields}")).is_err());
        }
    }

    #[test]
    fn execution_limits_merge_policy_parses_modes_and_selectors() {
        for (text, mode) in [("force", MergeMode::Force), ("adaptive", MergeMode::Adaptive), ("off", MergeMode::Off)] {
            let config = merge_config(&format!(
                r#"
                [[execution_limits.path_merge.regions]]
kind = "merge_policy"
                function = "pte_is_invalid"
                mode = "{text}"
                [[execution_limits.path_merge.regions]]
kind = "merge_policy"
                mode = "{text}"
                file = "model.sail"
                start_line = 10
                start_column = 0
                end_line = 20
                end_column = 0
            "#
            ))
            .unwrap();
            let rules = config.path_merge.policies();
            assert_eq!(rules[0].mode, mode);
            assert_eq!(rules[0].selector, MergePolicySelectorConfig::Function(zencode::encode("pte_is_invalid")));
            assert_eq!(
                rules[1].selector,
                MergePolicySelectorConfig::Region(SourceRegionSpec::new("model.sail", (10, 0), (20, 0)))
            );
        }
    }

    #[test]
    fn execution_limits_merge_policy_rejects_invalid_rules_and_conflicts() {
        for fields in [
            "mode = 'invalid'\nfunction = 'f'",
            "mode = 'off'",
            "mode = 'force'\nfunction = ''",
            "mode = 'off'\nfunction = 1",
            "mode = 'off'\nfunction = 'f'\nfile = 'model.sail'",
            "mode = 'off'\nfile = 'model.sail'",
            "mode = 'off'\nfunction = 'f'\nextra = true",
            "mode = 'off'\nfile = ''\nstart_line = 1\nstart_column = 0\nend_line = 2\nend_column = 0",
            "mode = 'off'\nfile = 'model.sail'\nstart_line = 0\nstart_column = 0\nend_line = 2\nend_column = 0",
            "mode = 'off'\nfile = 'model.sail'\nstart_line = 3\nstart_column = 0\nend_line = 2\nend_column = 0",
        ] {
            assert!(
                merge_config(&format!("[[execution_limits.path_merge.regions]]\nkind = \"merge_policy\"\n{fields}"))
                    .is_err(),
                "{fields}"
            );
        }
        for value in ["[]", "true", "['off']"] {
            assert!(merge_config(&format!("[execution_limits.path_merge]\nregions = {value}")).is_err());
        }
        for selector in
            ["function = 'f'", "file = 'model.sail'\nstart_line = 10\nstart_column = 0\nend_line = 20\nend_column = 0"]
        {
            let text = format!("[[execution_limits.path_merge.regions]]\nkind = \"merge_policy\"\nmode = 'force'\n{selector}\n[[execution_limits.path_merge.regions]]\nkind = \"merge_policy\"\nmode = 'off'\n{selector}");
            let error = merge_config(&text).unwrap_err();
            assert!(error.contains("冲突") && error.contains("path_merge.regions"), "{error}");
            assert!(merge_config(&text.replace("mode = 'off'", "mode = 'force'")).is_ok());
        }
    }

    #[test]
    fn execution_limits_merge_policy_defaults_priority_and_path_merging() {
        use crate::executor::ExecutionLimits;
        use crate::source_loc::SourceLoc;
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["model.sail"]);
        let f = symtab.intern("zf");
        let g = symtab.intern("zg");
        let unknown = SourceLoc::unknown();
        let defaults = ExecutionLimits::default();
        assert_eq!(defaults.merge_mode(f, unknown, None), MergeMode::Off);
        assert_eq!(defaults.clone().with_path_merging(true).merge_mode(f, unknown, None), MergeMode::Adaptive);
        assert_eq!(defaults.merge_mode(f, unknown, Some(MergeMode::Force)), MergeMode::Force);
        let config = merge_config(
            r#"
            [execution_limits]

[execution_limits.path_merge]
            enabled = true
            [[execution_limits.path_merge.regions]]
kind = "merge_policy"
            mode = "off"
            function = "f"
            [[execution_limits.path_merge.regions]]
kind = "merge_policy"
            mode = "force"
            file = "model.sail"
            start_line = 10
            start_column = 0
            end_line = 30
            end_column = 0
            [[execution_limits.path_merge.regions]]
kind = "merge_policy"
            mode = "adaptive"
            file = "model.sail"
            start_line = 15
            start_column = 2
            end_line = 16
            end_column = 8
        "#,
        )
        .unwrap();
        let limits = defaults.with_config(&config, &symtab);
        assert!(limits.path_merging);
        assert_eq!(limits.merge_mode(g, unknown, None), MergeMode::Adaptive);
        assert_eq!(limits.merge_mode(f, unknown, Some(MergeMode::Force)), MergeMode::Off);
        assert_eq!(limits.merge_mode(g, unknown, Some(MergeMode::Off)), MergeMode::Off);
        assert_eq!(limits.merge_mode(f, SourceLoc::new(0, 12, 0, 12, 1), Some(MergeMode::Off)), MergeMode::Force);
        assert_eq!(limits.merge_mode(f, SourceLoc::new(0, 15, 3, 15, 4), Some(MergeMode::Force)), MergeMode::Adaptive);
        let mut reversed = config.clone();
        reversed.path_merge.regions.as_mut().unwrap().reverse();
        let reversed = ExecutionLimits::default().with_config(&reversed, &symtab);
        assert_eq!(reversed.merge_mode(f, SourceLoc::new(0, 15, 3, 15, 4), None), MergeMode::Adaptive);
        for enabled in [true, false] {
            let config =
                merge_config(&format!("[execution_limits]\n\n[execution_limits.path_merge]\nenabled = {enabled}"))
                    .unwrap();
            let limits = ExecutionLimits::default().with_path_merging(!enabled).with_config(&config, &symtab);
            assert_eq!(limits.path_merging, enabled);
            assert_eq!(limits.merge_mode(g, unknown, None), if enabled { MergeMode::Adaptive } else { MergeMode::Off });
        }
    }

    #[test]
    fn execution_limits_merge_policy_columns_crossing_and_unknown_files() {
        use crate::executor::ExecutionLimits;
        use crate::source_loc::SourceLoc;
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["model.sail"]);
        let function = symtab.intern("zf");
        let config = merge_config(
            r#"
            [[execution_limits.path_merge.regions]]
kind = "merge_policy"
            mode = "force"
            file = "model.sail"
            start_line = 10
            start_column = 0
            end_line = 10
            end_column = 40
            [[execution_limits.path_merge.regions]]
kind = "merge_policy"
            mode = "off"
            file = "model.sail"
            start_line = 10
            start_column = 10
            end_line = 10
            end_column = 20
            [[execution_limits.path_merge.regions]]
kind = "merge_policy"
            mode = "adaptive"
            file = "model.sail"
            start_line = 10
            start_column = 15
            end_line = 10
            end_column = 25
            [[execution_limits.path_merge.regions]]
kind = "merge_policy"
            mode = "off"
            file = "missing.sail"
            start_line = 1
            start_column = 0
            end_line = 30
            end_column = 0
        "#,
        )
        .unwrap();
        assert!(config.validate_merge_policy(&symtab, &HashSet::from([function]), &[]).is_ok());
        let limits = ExecutionLimits::default().with_config(&config, &symtab);
        assert_eq!(limits.merge_mode(function, SourceLoc::new(0, 10, 9, 10, 10), None), MergeMode::Force);
        assert_eq!(limits.merge_mode(function, SourceLoc::new(0, 10, 12, 10, 13), None), MergeMode::Off);
        assert_eq!(limits.merge_mode(function, SourceLoc::new(0, 10, 20, 10, 21), None), MergeMode::Adaptive);
        assert_eq!(limits.merge_mode(function, SourceLoc::new(0, 10, 40, 10, 41), None), MergeMode::Off);
        let mut reversed = config.clone();
        reversed.path_merge.regions.as_mut().unwrap().reverse();
        let reversed = ExecutionLimits::default().with_config(&reversed, &symtab);
        let overlap = SourceLoc::new(0, 10, 17, 10, 18);
        assert_eq!(limits.merge_mode(function, overlap, None), reversed.merge_mode(function, overlap, None));
    }

    #[test]
    fn execution_limits_merge_policy_validates_ir_functions_and_strict_regions() {
        use crate::source_loc::SourceLoc;
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["model.sail"]);
        let f = symtab.intern("zf");
        let config = merge_config(
            "[[execution_limits.path_merge.regions]]\nkind = \"merge_policy\"\nmode = 'force'\nfunction = 'f'",
        )
        .unwrap();
        let functions = HashSet::from([f]);
        assert!(config.validate_merge_policy(&symtab, &functions, &[]).is_ok());
        let error = config.validate_merge_policy(&symtab, &HashSet::new(), &[]).unwrap_err();
        assert!(error.contains("函数") && error.contains("f"), "{error}");
        let missing = merge_config(
            "[[execution_limits.path_merge.regions]]\nkind = \"merge_policy\"\nmode = 'off'\nfunction = 'missing'",
        )
        .unwrap();
        assert!(missing.validate_merge_policy(&symtab, &functions, &[]).unwrap_err().contains("missing"));
        let region = "[[execution_limits.path_merge.regions]]\nkind = \"merge_policy\"\nmode = 'off'\nfile = 'model.sail'\nstart_line = 10\nstart_column = 0\nend_line = 20\nend_column = 0";
        let config = merge_config(region).unwrap();
        assert!(config.validate_merge_policy(&symtab, &functions, &[]).is_ok());
        let strict =
            merge_config(&format!("[execution_limits]\nstrict = true\nir_sha256 = '{}'\n{region}", "a".repeat(64)))
                .unwrap();
        assert!(strict.validate_ir_sha256(&"a".repeat(64)).is_ok());
        assert!(strict.validate_ir_sha256(&"b".repeat(64)).is_err());
        let error = strict.validate_merge_policy(&symtab, &functions, &[]).unwrap_err();
        assert!(error.contains("strict") && error.contains("分支"), "{error}");
        assert!(strict.validate_merge_policy(&symtab, &functions, &[SourceLoc::new(0, 12, 0, 12, 1)]).is_ok());
        assert!(strict
            .validate_merge_policy(&symtab, &functions, &[SourceLoc::unknown(), SourceLoc::new(0, 20, 0, 20, 1)])
            .is_err());
        let missing_file = merge_config(&format!(
            "[execution_limits]\nstrict = true\nir_sha256 = '{}'\n{}",
            "a".repeat(64),
            region.replace("model.sail", "missing.sail")
        ))
        .unwrap();
        assert!(missing_file.validate_merge_policy(&symtab, &functions, &[]).is_err());
    }

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

            [[execution_limits.path_merge.regions]]
kind = "limit_filter"
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
            match &config.path_merge.regions.as_ref().unwrap()[0] {
                PathMergeRegionConfig::LimitFilter(spec) => spec.clone(),
                _ => panic!("必须是范围筛选"),
            },
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

            [[execution_limits.path_merge.regions]]
kind = "limit_filter"
            file = "extensions/V/vext_arith_insts.sail"
            start_line = 186
            start_column = 6
            end_line = 192
            end_column = 7

            [[execution_limits.path_merge.regions]]
kind = "limit_filter"
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
            config.path_merge.regions.as_ref().map(|rules| rules
                .iter()
                .filter_map(|rule| match rule {
                    PathMergeRegionConfig::LimitFilter(spec) => Some(spec.clone()),
                    _ => None,
                })
                .collect::<Vec<_>>()),
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

            [[execution_limits.path_merge.regions]]
kind = "branch_limit"
            max_forks_per_branch = 1
            file = "extensions/V/vext_control.sail"
            start_line = 29
            start_column = 2
            end_line = 35
            end_column = 3

            [[execution_limits.path_merge.regions]]
kind = "branch_limit"
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
            config.path_merge.regions.as_ref().map(|rules| rules
                .iter()
                .filter_map(|rule| match rule {
                    PathMergeRegionConfig::BranchLimit(limit) => Some(limit.clone()),
                    _ => None,
                })
                .collect::<Vec<_>>()),
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

            [[execution_limits.path_merge.regions]]
kind = "fork_limit"
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
            config.path_merge.regions.as_ref().map(|rules| rules
                .iter()
                .filter_map(|rule| match rule {
                    PathMergeRegionConfig::ForkLimit(limit) => Some(limit.clone()),
                    _ => None,
                })
                .collect::<Vec<_>>()),
            Some(vec![RegionForkLimitConfig {
                max_forks_per_region: 1,
                sample_bias: None,
                region: SourceRegionSpec::new("extensions/V/vext_control.sail", (29, 2), (35, 3)),
            }])
        );
    }

    #[test]
    fn execution_limits_config_rejects_empty_region_fork_limits() {
        let value = "[execution_limits.path_merge]\nregions = []".parse::<Value>().unwrap();
        let error = get_execution_limits_config(&value).unwrap_err();
        assert!(error.contains("execution_limits.path_merge.regions 不能为空"), "{}", error);
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
        let value = "[execution_limits.path_merge]\nregions = []".parse::<Value>().unwrap();
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
    fn symbolic_registers_parses_enum_allowed() {
        let (symtab, defaults) = symbolic_registers_fixture(&["cur_privilege", "User", "Supervisor"]);
        let value = r#"[symbolic_registers]
cur_privilege = { allowed = ["User", "Supervisor"] }
"#
        .parse::<Value>()
        .unwrap();
        let registers = get_symbolic_registers(&value, &symtab, &defaults).unwrap();
        assert_eq!(registers.len(), 1);
        assert_eq!(registers[0].name, "cur_privilege");
    }

    #[test]
    fn symbolic_registers_rejects_invalid_allowed() {
        for entry in [
            r#"{ allowed = [] }"#,
            r#"{ allowed = "User" }"#,
            r#"{ allowed = [1] }"#,
            r#"{ allowed = ["Usr"] }"#,
            r#"{ allowed = ["User", "User"] }"#,
            r#"{ allowed = ["User"], pin_mask = 0, pin_value = 0 }"#,
            r#"{ allowed = ["User"], nonzero_groups = [] }"#,
            r#"{ allowed = ["User"], derive_bit = {bit = 1, groups = [[2]]} }"#,
        ] {
            let (symtab, defaults) = symbolic_registers_fixture(&["cur_privilege", "User"]);
            let value = format!("[symbolic_registers]\ncur_privilege = {entry}").parse::<Value>().unwrap();
            assert!(get_symbolic_registers(&value, &symtab, &defaults).is_err(), "应拒绝 {entry}");
        }
    }

    #[test]
    fn symbolic_registers_absent_returns_empty() {
        let (symtab, defaults) = symbolic_registers_fixture(&["mstatus"]);
        let value = "[registers]\n".parse::<Value>().unwrap();
        assert!(get_symbolic_registers(&value, &symtab, &defaults).unwrap().is_empty());
    }

    #[test]
    fn symbolic_registers_x1_without_bit_constraints() {
        let (symtab, defaults) = symbolic_registers_fixture(&["x1"]);
        let value = r#"
            [symbolic_registers]
            x1 = "symbolic"
        "#
        .parse::<Value>()
        .unwrap();
        let registers = get_symbolic_registers(&value, &symtab, &defaults).unwrap();
        assert_eq!(registers.len(), 1);
        assert_eq!(registers[0].name, "x1");
        assert_eq!(registers[0].pin_mask, 0);
        assert_eq!(registers[0].pin_value, 0);
        assert!(registers[0].nonzero_groups.is_empty());
        assert_eq!(registers[0].derive_bit, None);
        assert_eq!(registers[0].allowed, None);
    }

    #[test]
    fn symbolic_registers_parses_string_and_table_forms() {
        let (symtab, defaults) = symbolic_registers_fixture(&["mstatus", "satp"]);
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
                    allowed: None,
                },
                SymbolicRegisterConfig {
                    name: "satp".to_string(),
                    pin_mask: 0,
                    pin_value: 0,
                    nonzero_groups: vec![],
                    derive_bit: None,
                    allowed: None,
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
                allowed: None,
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

    /// P2 编码分片：合法声明解析——全枚举维度、显式钉值维度、操作数默认、
    /// 每片寄存器钉值与预算覆写。
    #[test]
    fn encoding_slices_parses() {
        let value = r#"
            [[encoding_slices]]
            clause = "VSSEGTYPE"
            enumerate = ["nf", "eew"]

            [[encoding_slices]]
            clause = "zVSXSEGTYPE"
            dimensions = { nf = [2, 3], mop = [0, 1] }
            operand_defaults = { rs1 = 6, vs2 = 7, vs3 = 8, vm = 1 }
            case_limit = 2
            timebox_s = 30
            [encoding_slices.prestate]
            mstatus = "{ bits = 0x8000100800007E00 }"
            cur_privilege = "Machine"
        "#
        .parse::<Value>()
        .unwrap();
        let slices = get_encoding_slices(&value).unwrap().unwrap();
        assert_eq!(slices.len(), 2);

        assert_eq!(slices[0].clause, "VSSEGTYPE");
        assert_eq!(slices[0].enumerate, vec!["nf", "eew"]);
        assert!(slices[0].dimensions.is_empty());
        assert_eq!(slices[0].case_limit, None);

        assert_eq!(slices[1].clause, "zVSXSEGTYPE");
        assert!(slices[1].enumerate.is_empty());
        assert_eq!(slices[1].dimensions.get("nf"), Some(&vec![2, 3]));
        assert_eq!(slices[1].dimensions.get("mop"), Some(&vec![0, 1]));
        assert_eq!(slices[1].operand_defaults.get("rs1"), Some(&6));
        assert_eq!(slices[1].prestate.get("cur_privilege").map(String::as_str), Some("Machine"));
        assert_eq!(slices[1].case_limit, Some(2));
        assert_eq!(slices[1].timebox_s, Some(30));
    }

    /// P2 编码分片解析硬失败：缺 clause、同字段既枚举又显式钉值、类型不符、
    /// 非法顶层数组形态。
    #[test]
    fn encoding_slices_hard_fails() {
        let cases = [
            (
                r#"
                [[encoding_slices]]
                enumerate = ["nf"]
                "#,
                "缺 clause",
            ),
            (
                r#"
                [[encoding_slices]]
                clause = "VSSEGTYPE"
                enumerate = ["nf"]
                dimensions = { nf = [2, 3] }
                "#,
                "同字段既枚举又显式钉值",
            ),
            (
                r#"
                [[encoding_slices]]
                clause = "VSSEGTYPE"
                dimensions = "nf"
                "#,
                "dimensions 不是表",
            ),
            (
                r#"
                [[encoding_slices]]
                clause = "VSSEGTYPE"
                dimensions = { nf = [2, -3] }
                "#,
                "负维度值",
            ),
            (
                r#"
                [[encoding_slices]]
                clause = "VSSEGTYPE"
                case_limit = 0
                "#,
                "case_limit 非正",
            ),
            (
                r#"
                [[encoding_slices]]
                clause = "VSSEGTYPE"
                prestate = ["x6 = 1"]
                "#,
                "prestate 不是表",
            ),
            (
                r#"
                encoding_slices = { clause = "VSSEGTYPE" }
                "#,
                "encoding_slices 不是 array-of-tables",
            ),
        ];
        for (toml, why) in cases {
            let value = toml.parse::<Value>().unwrap();
            assert!(get_encoding_slices(&value).is_err(), "{} 应报错", why);
        }
    }
}

#[cfg(test)]
mod initial_state_tests {
    use super::*;

    #[test]
    fn initial_constraints_default_empty_and_independent_from_reset() {
        let mut symtab = Symtab::new();
        symtab.intern("zPC");
        let types = IRTypeInfo::new::<crate::bitvector::b64::B64>(&[]);
        let base = r#"pc = "PC"
assembler = "as"
objdump = "objdump"
nm = "nm"
linker = "ld"
[mmu]
page_table_base = "0"
page_size = "4096"
s2_page_table_base = "0"
s2_page_size = "4096"
[threads]
base = "0"
top = "4096"
stride = "4096"
[symbolic_addrs]
base = "4096"
top = "8192"
stride = "16"
"#;
        let empty = ISAConfig::<crate::bitvector::b64::B64>::parse(base, None, &symtab, &types).unwrap();
        assert!(empty.initial_constraints.is_empty());
        let config = ISAConfig::<crate::bitvector::b64::B64>::parse(
            &format!("{base}\n[constraints]\ninitial = [\"false\"]\nreset = [\"true\"]"),
            None,
            &symtab,
            &types,
        )
        .unwrap();
        assert_eq!(config.initial_constraints, vec![Exp::Bool(false)]);
        assert_eq!(config.reset_constraints, vec![Exp::Bool(true)]);
    }

    #[test]
    fn initial_state_mixed_bits() {
        let config: Value = r#"[initial_state]
mstatus = "0b?x11_?0x1"
"#
        .parse()
        .unwrap();
        let entries = get_initial_state(&config).unwrap();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].name, "mstatus");
        assert_eq!(
            entries[0].fields,
            vec![
                (Some((0, 0)), Some(1)),
                (Some((1, 1)), None),
                (Some((2, 2)), Some(0)),
                (Some((3, 3)), None),
                (Some((4, 4)), Some(1)),
                (Some((5, 5)), Some(1)),
                (Some((6, 6)), None),
                (Some((7, 7)), None),
            ]
        );
    }

    #[test]
    fn initial_state_whole_registers() {
        let config: Value = r#"[initial_state]
x1 = 42
x2 = "?"
x3 = "x"
x4 = "0xffffffffffffffff"
fcsr = "0b010_?????"
"#
        .parse()
        .unwrap();
        assert_eq!(get_initial_state(&config).unwrap().len(), 5);
        assert!(get_initial_state(&"".parse().unwrap()).unwrap().is_empty());
    }

    #[test]
    fn initial_state_rejects_invalid_fields() {
        for text in [
            "[initial_state]\nx1 = -1",
            "[initial_state]\nx1 = true",
            "[initial_state]\nx1 = \"unknown\"",
            "[initial_state]\nx1 = \"中\"",
            "[initial_state]\nx1 = \"0b\"",
            "[initial_state]\nx1 = \"0b__\"",
            "[initial_state]\nx1 = \"0b?2\"",
            "[initial_state.mstatus]\nVS = 3",
        ] {
            assert!(get_initial_state(&text.parse().unwrap()).is_err(), "{}", text);
        }
    }
}

#[cfg(test)]
mod initial_constraints_tests {
    use super::*;

    #[test]
    fn rv64_initial_domain_preserves_all_writable_vstart_values() {
        use crate::bitvector::{b64::B64, BV};
        use crate::ir::Val;
        use crate::smt::{smtlib, Config, Context, SmtResult, Solver};
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let configs = [
            include_str!("../../configs/riscv64_difftest.toml"),
            include_str!("../../configs/riscv64_difftest_fd.toml"),
            include_str!("../../configs/riscv64_difftest_vabs_v.toml"),
        ];
        for text in configs {
            let config = text.parse::<Value>().unwrap();
            let constraints: Vec<_> = config["constraints"]["initial"]
                .as_array()
                .unwrap()
                .iter()
                .map(|value| value.as_str().unwrap())
                .filter(|expression| expression.contains("vstart"))
                .map(|expression| crate::smt_parser::ExpParser::new().parse(expression).unwrap())
                .collect();
            assert!(!constraints.is_empty(), "RV64 初态必须声明模型可写的 vstart 完整范围");
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let info = crate::source_loc::SourceLoc::unknown();
            let vstart = solver.declare_bitvector(64, info);
            for constraint in constraints {
                let expression = constraint
                    .map_var(&mut |location| -> Result<_, ()> {
                        assert_eq!(location, &Loc::Id("zvstart".to_string()));
                        Ok(smtlib::Exp::Var(vstart))
                    })
                    .unwrap();
                solver.assert(expression);
            }
            // 当前模型 VLEN=128，set_vstart 将低7位零扩展；128个可写值全部保留。
            for value in 0..128 {
                assert_eq!(
                    solver.check_sat_with(
                        &smtlib::Exp::Eq(
                            Box::new(smtlib::Exp::Var(vstart)),
                            Box::new(smtlib::Exp::Bits64(B64::new(value, 64))),
                        ),
                        info,
                    ),
                    SmtResult::Sat,
                    "合法起点 {value}，包括大于 vl 的起点，不得固定或删去"
                );
            }
            let outside = smtlib::Exp::Bvuge(
                Box::new(smtlib::Exp::Var(vstart)),
                Box::new(smtlib::Exp::Bits64(B64::new(128, 64))),
            );
            assert_eq!(solver.check_sat_with(&outside, info), SmtResult::Unsat, "不可写的高位必须为零");
            // 沿真实原语链验证循环入口窄化；不放宽真实整数溢出检查。
            let integer =
                crate::primop::unary_primops()["sail_unsigned"](Val::Symbolic(vstart), &mut solver, info).unwrap();
            assert!(crate::primop::unary_primops()["%i->%i64"](integer, &mut solver, info).is_ok());
        }
    }
    #[test]
    fn initial_constraints_share_reset_parser_and_validate_input() {
        let value: Value = r#"[constraints]
initial = ["= ((_ extract 35 34) status.bits) #b10"]
reset = ["= ((_ extract 35 34) status.bits) #b10"]
"#
        .parse()
        .unwrap();
        assert_eq!(get_constraints(&value, "initial").unwrap(), get_constraints(&value, "reset").unwrap());
        assert!(get_constraints(&"".parse().unwrap(), "initial").unwrap().is_empty());
        for text in ["initial = true", "initial = [1]", r#"initial = ["(broken"]"#] {
            assert!(get_constraints(&format!("[constraints]\n{text}").parse().unwrap(), "initial").is_err());
        }
    }
}

#[cfg(test)]
mod tool_path_tests {
    use super::*;
    use crate::bitvector::b64::B64;

    #[test]
    fn invoking_a_missing_tool_names_the_command_and_role() {
        for role in ["assembler", "objdump", "nm", "linker"] {
            let program = format!("isla-test-missing-{role}");
            let config: Value = format!("{role} = '{program} --configured-option'").parse().unwrap();
            let tool = get_tool_path(&config, role).expect("配置加载不查找工具");
            let context = format!("测试调用入口 {role}");
            let error = tool.command(&context).unwrap_err();
            assert!(error.contains(&context) && error.contains(&program), "{error}");
            assert!(error.contains("--configured-option"), "错误应保留配置命令：{error}");
            let missing = get_tool_path(&"".parse::<Value>().unwrap(), role).unwrap();
            let error = missing.command(&context).unwrap_err();
            assert!(error.contains(&context) && error.contains("未配置"), "{error}");
        }
    }

    #[test]
    fn missing_absolute_tool_path_reports_the_calling_command() {
        let tool = Tool { executable: Some(PathBuf::from("/isla-test-no-toolchain/assembler")), options: vec![] };
        let error = tool.command("测试绝对路径 assembler").unwrap_err();
        assert!(error.contains("测试绝对路径 assembler") && error.contains("/isla-test-no-toolchain/assembler"));
    }

    #[test]
    fn configured_options_are_preserved_when_the_tool_is_invoked() {
        let config: Value = "assembler = '/bin/echo 配置参数'".parse().unwrap();
        let tool = get_tool_path(&config, "assembler").unwrap();
        let output = tool.command("测试实际调用 assembler").unwrap().arg("调用参数").output().unwrap();
        assert!(output.status.success());
        assert_eq!(String::from_utf8(output.stdout).unwrap().trim(), "配置参数 调用参数");
        assert!(get_tool_path(&"assembler = 7".parse::<Value>().unwrap(), "assembler").is_err());
        assert!(get_tool_path(&"assembler = ''".parse::<Value>().unwrap(), "assembler").is_err());
    }

    #[test]
    fn config_loading_does_not_require_tools_in_path() {
        // 子进程隔离 PATH，不修改并行测试共享的环境。
        if env::var_os("ISLA_LAZY_TOOL_TEST_CHILD").is_none() {
            let result = Command::new(env::current_exe().unwrap())
                .args([
                    "--exact",
                    "config::tool_path_tests::config_loading_does_not_require_tools_in_path",
                    "--nocapture",
                ])
                .env("ISLA_LAZY_TOOL_TEST_CHILD", "1")
                .env("PATH", "/isla-test-no-toolchain")
                .output()
                .unwrap();
            assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stdout));
            return;
        }
        let mut symtab = Symtab::new();
        symtab.intern("zPC");
        let types = IRTypeInfo::new::<B64>(&[]);
        let config = r#"pc = "PC"
[[toolchain]]
name = "default"
assembler = "isla-test-missing-as -march=rv64imac"
objdump = "isla-test-missing-objdump"
nm = "isla-test-missing-nm"
linker = "isla-test-missing-ld"
[mmu]
page_table_base = "0"
page_size = "4096"
s2_page_table_base = "0"
s2_page_size = "4096"
[threads]
base = "0"
top = "4096"
stride = "4096"
[symbolic_addrs]
base = "4096"
top = "8192"
stride = "16"
"#;
        let isa = ISAConfig::<B64>::parse(config, None, &symtab, &types).expect("加载配置不得查找工具");
        assert_eq!(isa.assembler.options, ["-march=rv64imac"]);
    }

    #[test]
    fn unused_tools_can_be_omitted_from_toolchain() {
        let config: Value = "[[toolchain]]\nname = 'default'".parse().unwrap();
        get_toolchain(&config, None).expect("不使用工具时不要求配置四个工具");
    }
}
