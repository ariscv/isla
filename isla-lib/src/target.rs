use std::collections::HashMap;

use crate::bitvector::BV;
use crate::config::{PmpConfig, PmpMode};
use crate::error::ExecError;
use crate::ir::{IRTypeInfo, Name, SharedState, Symtab, Val};
use crate::register::RegisterBindings;
use crate::smt::{smtlib, Solver};
use crate::source_loc::SourceLoc;
use crate::zencode;

pub trait Target
where
    Self: Sync,
{
    fn arch_name(&self) -> &'static str;
    fn arch_pretty_name(&self) -> &'static str;
    fn xlen(&self) -> &'static str;
    fn isa_state_list(&self) -> Vec<String>;
}

pub trait RISCV: Target {
    const XLEN: u32;

    fn xlen_name() -> &'static str;
}

impl<T: RISCV> Target for T {
    fn arch_name(&self) -> &'static str {
        "riscv"
    }

    fn arch_pretty_name(&self) -> &'static str {
        T::xlen_name()
    }

    fn xlen(&self) -> &'static str {
        const { assert!(T::XLEN == 32 || T::XLEN == 64) };
        match T::XLEN {
            32 => "32",
            64 => "64",
            _ => "0",
        }
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

pub struct RV32;

impl RISCV for RV32 {
    const XLEN: u32 = 32;

    fn xlen_name() -> &'static str {
        "rv32"
    }
}

pub struct RV64;

impl RISCV for RV64 {
    const XLEN: u32 = 64;

    fn xlen_name() -> &'static str {
        "rv64"
    }
}

impl RV64 {
    pub const PAGE_SIZE: u64 = 4096;
    pub const PAGE_SHIFT: u64 = 12;
    pub const PTE_SIZE: u64 = 8;
    pub const VPN_BITS: u64 = 9;
    pub const PTES_PER_LEVEL: u64 = 512;
    pub const PAGE_TABLE_SIZE: u64 = Self::PTES_PER_LEVEL * Self::PTE_SIZE;

    pub const PTE_V: u64 = 1;
    pub const PTE_R: u64 = 2;
    pub const PTE_W: u64 = 4;
    pub const PTE_X: u64 = 8;
    pub const PTE_U: u64 = 16;
    pub const PTE_A: u64 = 64;
    pub const PTE_D: u64 = 128;

    pub const SV39_LEVELS: u64 = 3;
    pub const SV48_LEVELS: u64 = 4;
}

const PPN_MASK: u64 = 0xFFF_FFFF_FFF;

#[derive(Debug)]
pub struct RiscvPte {
    pub bits: u64,
}

impl RiscvPte {
    pub fn new(ppn: u64, flags: u64) -> Self {
        Self { bits: ((ppn & PPN_MASK) << 10) | (flags & 0xFF) }
    }

    pub fn ppn(&self) -> u64 {
        (self.bits >> 10) & PPN_MASK
    }

    pub fn flags(&self) -> u64 {
        self.bits & 0xFF
    }

    pub fn is_valid(&self) -> bool {
        self.bits & RV64::PTE_V != 0
    }

    pub fn has_read(&self) -> bool {
        self.bits & RV64::PTE_R != 0
    }

    pub fn has_write(&self) -> bool {
        self.bits & RV64::PTE_W != 0
    }

    pub fn has_execute(&self) -> bool {
        self.bits & RV64::PTE_X != 0
    }

    pub fn to_bytes(&self) -> [u8; 8] {
        self.bits.to_le_bytes()
    }
}

pub fn sv39_vpn_indices(va: u64) -> [u64; 3] {
    [(va >> 12) & 0x1FF, (va >> 21) & 0x1FF, (va >> 30) & 0x1FF]
}

pub fn sv48_vpn_indices(va: u64) -> [u64; 4] {
    [(va >> 12) & 0x1FF, (va >> 21) & 0x1FF, (va >> 30) & 0x1FF, (va >> 39) & 0x1FF]
}

pub fn ppn_from_pa(pa: u64) -> u64 {
    pa >> RV64::PAGE_SHIFT
}

pub fn pa_from_ppn(ppn: u64) -> u64 {
    ppn << RV64::PAGE_SHIFT
}

// PMP operations

pub fn encode_napot(base: u64, size: u64) -> u64 {
    (base >> 2) | ((size >> 3) - 1)
}

pub fn encode_pmpcfg_byte(mode: PmpMode, permissions: &str, locked: bool) -> u8 {
    let mode_bits = match mode {
        PmpMode::Tor => 0b01,
        PmpMode::Na4 => 0b10,
        PmpMode::Napot => 0b11,
    };

    let mut cfg = 0u8;
    if permissions.contains('r') {
        cfg |= 1 << 0;
    }
    if permissions.contains('w') {
        cfg |= 1 << 1;
    }
    if permissions.contains('x') {
        cfg |= 1 << 2;
    }
    cfg |= mode_bits << 3;
    if locked {
        cfg |= 1 << 7;
    }
    cfg
}

fn insert_register<B: BV>(
    symtab: &Symtab,
    default_registers: &mut HashMap<Name, Val<B>>,
    register_name: &str,
    value: Val<B>,
) -> Result<(), String> {
    if let Some(name) = symtab.get(&zencode::encode(register_name)) {
        default_registers.insert(name, value);
        Ok(())
    } else {
        Err(format!("Could not find register {} when applying PMP configuration", register_name))
    }
}

pub fn apply_pmp_rules_to_config<B: BV>(
    pmp_config: &PmpConfig,
    symtab: &Symtab,
    _type_info: &IRTypeInfo,
    default_registers: &mut HashMap<Name, Val<B>>,
) -> Result<(), String> {
    let mut pmpcfg_values = HashMap::<u32, u64>::new();

    for rule in &pmp_config.rules {
        let pmpaddr_value = match rule.mode {
            PmpMode::Tor | PmpMode::Na4 => rule.base >> 2,
            PmpMode::Napot => encode_napot(rule.base, rule.size.expect("NAPOT PMP rules require size")),
        };
        insert_register(symtab, default_registers, &format!("pmpaddr{}", rule.index), Val::I64(pmpaddr_value as i64))?;

        let cfg_register = (rule.index / 8) * 2;
        let byte_offset = rule.index % 8;
        let cfg_byte = u64::from(encode_pmpcfg_byte(rule.mode, &rule.permissions, rule.locked));
        let entry = pmpcfg_values.entry(cfg_register).or_insert_with(|| {
            symtab
                .get(&zencode::encode(&format!("pmpcfg{}", cfg_register)))
                .and_then(|name| match default_registers.get(&name) {
                    Some(Val::I64(value)) => Some(*value as u64),
                    Some(Val::I128(value)) => Some(*value as u64),
                    _ => None,
                })
                .unwrap_or(0)
        });
        *entry &= !(0xff << (byte_offset * 8));
        *entry |= cfg_byte << (byte_offset * 8);
    }

    for (cfg_register, value) in pmpcfg_values {
        insert_register(symtab, default_registers, &format!("pmpcfg{}", cfg_register), Val::I64(value as i64))?;
    }

    Ok(())
}

pub fn apply_symbolic_pmp_to_registers<'ir, B: BV>(
    symtab: &Symtab,
    default_registers: &mut RegisterBindings<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<(), ExecError> {
    for index in 0..64 {
        let sym = solver.declare_const(smtlib::Ty::BitVec(64), SourceLoc::unknown());
        insert_symbolic_register(
            symtab,
            default_registers,
            shared_state,
            &format!("pmpaddr{}", index),
            Val::Symbolic(sym),
        );
    }

    for index in 0..16 {
        let sym = solver.declare_const(smtlib::Ty::BitVec(64), SourceLoc::unknown());
        insert_symbolic_register(
            symtab,
            default_registers,
            shared_state,
            &format!("pmpcfg{}", index),
            Val::Symbolic(sym),
        );
    }

    Ok(())
}

fn insert_symbolic_register<'ir, B: BV>(
    symtab: &Symtab,
    default_registers: &mut RegisterBindings<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    register_name: &str,
    value: Val<B>,
) {
    if let Some(name) = symtab.get(&zencode::encode(register_name)) {
        default_registers.assign(name, value, shared_state);
    } else {
        eprintln!("Warning: Could not find register {} when applying PMP configuration", register_name);
    }
}
