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
}

impl FromStr for MemoryRegionType {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "concrete" => Ok(MemoryRegionType::Concrete),
            "symbolic" => Ok(MemoryRegionType::Symbolic),
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
    /// Optional page table configuration
    pub page_table_config: Option<PageTableConfig>,
    /// Optional PMP configuration
    pub pmp: Option<PmpConfig>,
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
            page_table_config: get_page_table_config(&config)?,
            pmp,
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
}
