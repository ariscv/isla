use std::collections::{BTreeMap, HashMap};

use isla_lib::bitvector::BV;
use isla_lib::config::{PmpConfig, PmpMode};
use isla_lib::error::ExecError;
use isla_lib::fmtval::FmtVal;
use isla_lib::ir::{Bindings, IRTypeInfo, Name, SharedState, Symtab, Ty, UVal, Val};
use isla_lib::log;
use isla_lib::primop_util::symbolic;
use isla_lib::register::RegisterBindings;
use isla_lib::smt::Model;
use isla_lib::smt::{smtlib, Solver};
use isla_lib::source_loc::SourceLoc;
use isla_lib::zencode;

#[derive(Debug, Clone)]
pub struct PreStateCtx<B: BV> {
    map: HashMap<Name, Val<B>>,
}

impl<B: BV> PreStateCtx<B> {
    pub fn new() -> Self {
        PreStateCtx { map: HashMap::new() }
    }

    pub fn get(&self, name: &Name) -> Option<&Val<B>> {
        self.map.get(name)
    }

    pub fn get_from_str(&self, name_str: &str, symtab: &Symtab) -> Option<&Val<B>> {
        let name_zstr = zencode::encode(name_str);
        let name = symtab.get(&name_zstr)?;
        self.map.get(&name)
    }

    pub fn insert(&mut self, name: Name, value: Val<B>) -> Option<Val<B>> {
        self.map.insert(name, value)
    }

    pub fn insert_from_str(&mut self, name_str: &str, value: Val<B>, symtab: &Symtab) -> Option<Val<B>> {
        let name_zstr = zencode::encode(name_str);
        let name = symtab.get(&name_zstr)?;
        self.map.insert(name, value)
    }

    pub fn iter(&self) -> std::collections::hash_map::Iter<Name, Val<B>> {
        self.map.iter()
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }
}

pub trait Target<B: BV>
where
    Self: Sync,
{
    fn arch_name(&self) -> &'static str;
    fn xlen_name(&self) -> &'static str;
    fn xlen(&self) -> &'static str;

    fn arch_pretty_name(&self) -> &'static str {
        self.xlen_name()
    }

    fn reg_list(&self) -> Vec<String>;

    fn setup_pre_state<'ir>(
        &mut self,
        regs: &mut RegisterBindings<'ir, B>,
        lets: &Bindings<'ir, B>,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
    ) -> Result<(), ExecError> {
        let reg_names = self.reg_list();
        let pre_state = self.pre_state_mut();
        let symtab = &shared_state.symtab;
        for reg_name_str in reg_names.into_iter().filter(|r| r != "x0" && r != "PC") {
            let Some(name) = symtab.get(&zencode::encode(&reg_name_str)) else { continue };
            let sym_val = match shared_state.registers.get(&name) {
                Some(Ty::AnyBits) if is_vector_register_name(&reg_name_str) => {
                    let vlen = vlen_from_lets(lets, symtab);
                    Val::Symbolic(solver.declare_const(smtlib::Ty::BitVec(vlen), SourceLoc::unknown()))
                }
                Some(Ty::AnyBits) => {
                    panic!("防御性编程：寄存器 {} 是 %bv，但不是已知可由 vlen 定宽的 vr* 寄存器", reg_name_str)
                }
                Some(ty) => symbolic(ty, shared_state, solver, SourceLoc::unknown()).unwrap_or_else(|err| {
                    panic!("防御性编程：寄存器 {} 无法符号化，类型 {:?}: {:?}", reg_name_str, ty, err)
                }),
                None => Val::Poison,
            };
            let recorded = if matches!(sym_val, Val::Poison) {
                panic!(
                    "防御性编程：寄存器 {} 的类型 {:?} 无法表示为符号值",
                    reg_name_str,
                    shared_state.registers.get(&name)
                );
            } else {
                regs.assign(name, sym_val.clone(), shared_state);
                sym_val
            };
            if !matches!(recorded, Val::Poison) {
                pre_state.insert(name, recorded);
            }
        }

        Ok(())
    }

    fn solve_pre_state<'state>(
        &self,
        model: &mut Model<'_, B>,
        shared_state: &SharedState<'state, B>,
    ) -> BTreeMap<String, String> {
        let pre_state = self.pre_state();
        let symtab = &shared_state.symtab;
        let mut result = BTreeMap::new();
        for (name, val) in pre_state.iter() {
            let reg_name = zencode::decode(symtab.to_str(*name));
            match FmtVal::from_val(val, model) {
                Ok(fmt_val) => {
                    // 过滤未约束的符号变量（与历史提交 4639bd7 的 isa-state 打印过滤一致）：
                    // is_arbitrary 为真表示该 pre-state 符号在最终 model 中没有被任何约束定值
                    //（complete_model=false 下，z3 对从未出现在断言中的声明常量返回 Arbitrary）。
                    // 这类寄存器对当前指令路径没有实际约束，跳过不输出，避免 isa-state 被全 0
                    // 的 arbitrary 值淹没，只保留真正被符号执行约束过的 pre-state。
                    if fmt_val.is_arbitrary() {
                        continue;
                    }
                    result.insert(reg_name, fmt_val.to_str(shared_state));
                }
                Err(e) => {
                    log!(log::PATH_RESULT, &format!("警告: pre-state 寄存器 {} 无法求解: {:?}", reg_name, e));
                }
            }
        }
        result
    }

    fn pre_state(&self) -> &PreStateCtx<B>;
    fn pre_state_mut(&mut self) -> &mut PreStateCtx<B>;
}

fn is_vector_register_name(reg_name: &str) -> bool {
    reg_name.strip_prefix("vr").is_some_and(|suffix| !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()))
}

fn vlen_from_lets<B: BV>(lets: &Bindings<B>, symtab: &Symtab) -> u32 {
    let vlen_name = symtab.get(&zencode::encode("vlen")).expect("防御性编程：IR 中缺少 let vlen");
    let vlen = lets.get(&vlen_name).expect("防御性编程：let vlen 未初始化");
    let value = match vlen {
        UVal::Init(Val::I64(value)) => *value as i128,
        UVal::Init(Val::I128(value)) => *value,
        UVal::Init(value) => panic!("防御性编程：let vlen 不是整数值: {:?}", value),
        UVal::Uninit(ty) => panic!("防御性编程：let vlen 仍未求值，类型 {:?}", ty),
    };
    u32::try_from(value).unwrap_or_else(|err| panic!("防御性编程：let vlen 不能作为 bitvector 宽度: {}", err))
}

pub trait RISCV<B: BV>: Target<B> {
    fn pmp_symbolic(&self) -> bool;
    fn ppn_from_pa(&self, pa: u64) -> u64 {
        pa >> 12
    }

    fn pa_from_ppn(&self, ppn: u64) -> u64 {
        ppn << 12
    }

    // Page table constants (hardcoded defaults; override per-impl if needed)
    fn page_size(&self) -> u64 {
        4096
    }
    fn page_shift(&self) -> u64 {
        12
    }
    fn pte_size(&self) -> u64 {
        8
    }
    fn ptes_per_level(&self) -> u64 {
        512
    }
    fn page_table_size(&self) -> u64 {
        self.ptes_per_level() * self.pte_size()
    }
    fn pte_v(&self) -> u64 {
        1
    }
    fn pte_r(&self) -> u64 {
        2
    }
    fn pte_w(&self) -> u64 {
        4
    }
    fn pte_x(&self) -> u64 {
        8
    }
    fn pte_u(&self) -> u64 {
        16
    }
    fn pte_a(&self) -> u64 {
        64
    }
    fn pte_d(&self) -> u64 {
        128
    }
    fn vpn_bits(&self) -> u64 {
        9
    }
    fn sv39_levels(&self) -> u64 {
        3
    }
    fn sv48_levels(&self) -> u64 {
        4
    }

    fn apply_pmp_rules_to_config(
        &self,
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
                _ => rule.base >> 2,
            };
            insert_register(
                symtab,
                default_registers,
                &format!("pmpaddr{}", rule.index),
                Val::I64(pmpaddr_value as i64),
            )?;

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

    fn apply_symbolic_pmp_to_registers<'ir>(
        &self,
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
}

pub struct RV32<B: BV> {
    pub pmp_symbolic: bool,
    pub pre_state: PreStateCtx<B>,
}

impl<B: BV> Default for RV32<B> {
    fn default() -> Self {
        RV32 { pmp_symbolic: false, pre_state: PreStateCtx::new() }
    }
}

impl<B: BV> Target<B> for RV32<B> {
    fn arch_name(&self) -> &'static str {
        "riscv"
    }
    fn xlen_name(&self) -> &'static str {
        "rv32"
    }
    fn xlen(&self) -> &'static str {
        "32"
    }
    fn reg_list(&self) -> Vec<String> {
        let mut regs: Vec<String> = (0..32).map(|r| format!("x{}", r)).collect();
        regs.extend((0..32).map(|r| format!("f{}", r)));
        regs.extend((0..32).map(|r| format!("vr{}", r)));
        regs.push("PC".to_string());
        regs.push("cur_privilege".to_string());
        regs.push("mstatus".to_string());
        regs.push("vtype".to_string());
        regs
    }
    fn pre_state(&self) -> &PreStateCtx<B> {
        &self.pre_state
    }
    fn pre_state_mut(&mut self) -> &mut PreStateCtx<B> {
        &mut self.pre_state
    }
}

impl<B: BV> RISCV<B> for RV32<B> {
    fn pmp_symbolic(&self) -> bool {
        self.pmp_symbolic
    }
}

pub struct RV64<B: BV> {
    pub pmp_symbolic: bool,
    pub pre_state: PreStateCtx<B>,
}

impl<B: BV> Default for RV64<B> {
    fn default() -> Self {
        RV64 { pmp_symbolic: false, pre_state: PreStateCtx::new() }
    }
}

impl<B: BV> Target<B> for RV64<B> {
    fn arch_name(&self) -> &'static str {
        "riscv"
    }
    fn xlen_name(&self) -> &'static str {
        "rv64"
    }
    fn xlen(&self) -> &'static str {
        "64"
    }
    fn reg_list(&self) -> Vec<String> {
        let mut regs: Vec<String> = (0..32).map(|r| format!("x{}", r)).collect();
        regs.extend((0..32).map(|r| format!("f{}", r)));
        regs.extend((0..32).map(|r| format!("vr{}", r)));
        regs.push("PC".to_string());
        regs.push("cur_privilege".to_string());
        regs.push("mstatus".to_string());
        regs.push("vtype".to_string());
        regs
    }
    fn pre_state(&self) -> &PreStateCtx<B> {
        &self.pre_state
    }
    fn pre_state_mut(&mut self) -> &mut PreStateCtx<B> {
        &mut self.pre_state
    }
}

impl<B: BV> RISCV<B> for RV64<B> {
    fn pmp_symbolic(&self) -> bool {
        self.pmp_symbolic
    }
}

impl<B: BV> RV64<B> {
    pub fn sv39_vpn_indices(&self, va: u64) -> [u64; 3] {
        [(va >> 12) & 0x1FF, (va >> 21) & 0x1FF, (va >> 30) & 0x1FF]
    }

    pub fn sv48_vpn_indices(&self, va: u64) -> [u64; 4] {
        [(va >> 12) & 0x1FF, (va >> 21) & 0x1FF, (va >> 39) & 0x1FF, (va >> 39) & 0x1FF]
    }
}

pub struct ARM<B: BV> {
    pub pre_state: PreStateCtx<B>,
}

impl<B: BV> Target<B> for ARM<B> {
    fn arch_name(&self) -> &'static str {
        "aarch64"
    }
    fn xlen_name(&self) -> &'static str {
        "aarch64"
    }
    fn xlen(&self) -> &'static str {
        "64"
    }
    fn arch_pretty_name(&self) -> &'static str {
        "AArch64"
    }
    fn reg_list(&self) -> Vec<String> {
        let mut regs: Vec<String> = (0..31).map(|r| format!("R{}", r)).collect();
        regs.push("PC".to_string());
        regs
    }
    fn pre_state(&self) -> &PreStateCtx<B> {
        &self.pre_state
    }
    fn pre_state_mut(&mut self) -> &mut PreStateCtx<B> {
        &mut self.pre_state
    }
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
        self.bits & 1 != 0
    }

    pub fn has_read(&self) -> bool {
        self.bits & 2 != 0
    }

    pub fn has_write(&self) -> bool {
        self.bits & 4 != 0
    }

    pub fn has_execute(&self) -> bool {
        self.bits & 8 != 0
    }

    pub fn to_bytes(&self) -> [u8; 8] {
        self.bits.to_le_bytes()
    }
}

fn encode_napot(base: u64, size: u64) -> u64 {
    (base >> 2) | ((size >> 3) - 1)
}

fn encode_pmpcfg_byte(mode: PmpMode, permissions: &str, locked: bool) -> u8 {
    let mode_bits = match mode {
        PmpMode::Tor => 0b01,
        PmpMode::Na4 => 0b10,
        PmpMode::Napot => 0b11,
        _ => 0,
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

fn insert_symbolic_register<'ir, B: BV>(
    symtab: &Symtab,
    default_registers: &mut RegisterBindings<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    register_name: &str,
    value: Val<B>,
) {
    if let Some(name) = symtab.get(&zencode::encode(register_name)) {
        default_registers.assign(name, value, shared_state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::bitvector::b64::B64;

    fn rv64() -> RV64<B64> {
        RV64::default()
    }
    fn rv32() -> RV32<B64> {
        RV32::default()
    }
    #[test]
    fn pte_new_and_extract() {
        let pte = RiscvPte::new(0x1234, 0xF);
        assert_eq!(pte.ppn(), 0x1234);
        assert_eq!(pte.flags(), 0xF);
        assert!(pte.is_valid());
        assert!(pte.has_read());
        assert!(pte.has_write());
        assert!(pte.has_execute());
    }

    #[test]
    fn pte_flag_masks() {
        let pte = RiscvPte::new(0xFFFF_FFFF_FFFF, 0xFF);
        assert_eq!(pte.ppn(), 0xFFF_FFFF_FFF);
        assert_eq!(pte.flags(), 0xFF);
    }

    #[test]
    fn pte_not_valid() {
        let pte = RiscvPte::new(0, 0);
        assert!(!pte.is_valid());
        assert!(!pte.has_read());
        assert!(!pte.has_write());
        assert!(!pte.has_execute());
    }

    #[test]
    fn pte_individual_flags() {
        let r = rv64();
        let pte_v = RiscvPte::new(0, r.pte_v());
        assert!(pte_v.is_valid());
        assert!(!pte_v.has_read());

        let pte_r = RiscvPte::new(0, r.pte_r());
        assert!(!pte_r.is_valid());
        assert!(pte_r.has_read());

        let pte_w = RiscvPte::new(0, r.pte_w());
        assert!(pte_w.has_write());

        let pte_x = RiscvPte::new(0, r.pte_x());
        assert!(pte_x.has_execute());
    }

    #[test]
    fn pte_to_bytes_little_endian() {
        let pte = RiscvPte::new(0, 0x01);
        let bytes = pte.to_bytes();
        assert_eq!(bytes[0], 0x01);
        assert_eq!(bytes[1..], [0u8; 7]);
    }

    #[test]
    fn pte_roundtrip() {
        let r = rv64();
        let ppn = 0xABCD;
        let flags = r.pte_v() | r.pte_r() | r.pte_w() | r.pte_a() | r.pte_d();
        let pte = RiscvPte::new(ppn, flags);
        let reconstructed = RiscvPte::new(pte.ppn(), pte.flags());
        assert_eq!(pte.bits, reconstructed.bits);
    }

    #[test]
    fn sv39_vpn_indices_zero() {
        assert_eq!(rv64().sv39_vpn_indices(0), [0, 0, 0]);
    }

    #[test]
    fn sv39_vpn_indices_known() {
        let indices = rv64().sv39_vpn_indices(0x0400_0000);
        assert_eq!(indices[0], 0);
        assert_eq!(indices[1], 32);
        assert_eq!(indices[2], 0);
    }

    #[test]
    fn sv39_vpn_indices_max() {
        let va = (0x1FFu64 << 12) | (0x1FF << 21) | (0x1FF << 30);
        let indices = rv64().sv39_vpn_indices(va);
        assert_eq!(indices, [511, 511, 511]);
    }

    #[test]
    fn sv48_vpn_indices_zero() {
        assert_eq!(rv64().sv48_vpn_indices(0), [0, 0, 0, 0]);
    }

    #[test]
    fn sv48_vpn_indices_four_levels() {
        let va = (0x1u64 << 12) | (0x2u64 << 21) | (0x3u64 << 30) | (0x4u64 << 39);
        let indices = rv64().sv48_vpn_indices(va);
        assert_eq!(indices, [1, 2, 3, 4]);
    }

    #[test]
    fn ppn_pa_roundtrip() {
        let pa = 0x8000_1000u64;
        let rv64 = rv64();
        let ppn = rv64.ppn_from_pa(pa);
        assert_eq!(ppn, 0x8000_1);
        assert_eq!(rv64.pa_from_ppn(ppn), pa);
    }

    #[test]
    fn ppn_from_pa_strips_offset() {
        assert_eq!(rv64().ppn_from_pa(0x8000_1234), 0x8000_1);
    }

    #[test]
    fn pa_from_ppn_aligned() {
        let rv64 = rv64();
        let pa = rv64.pa_from_ppn(0x1234);
        assert_eq!(pa % rv64.page_size(), 0);
    }

    #[test]
    fn rv64_target_trait() {
        let target = rv64();
        assert_eq!(target.arch_name(), "riscv");
        assert_eq!(target.xlen(), "64");
        assert_eq!(target.xlen_name(), "rv64");
        // registers_of_interest 是 pre-state 与 post-state 的统一来源（全量并集）
        let regs = target.reg_list();
        assert!(regs.contains(&"x0".to_string()));
        assert!(regs.contains(&"PC".to_string()));
        assert!(regs.contains(&"vr0".to_string()));
        assert!(regs.contains(&"mstatus".to_string()));
        assert!(regs.contains(&"vtype".to_string()));
        // pre-state 派生（setup_pre_state 内部）：排除 x0 和 PC（不做主动符号化）
        let pre_state: Vec<String> = regs.into_iter().filter(|r| r != "x0" && r != "PC").collect();
        assert!(!pre_state.contains(&"x0".to_string()));
        assert!(!pre_state.contains(&"PC".to_string()));
        assert!(pre_state.contains(&"vr0".to_string()));
        assert!(pre_state.contains(&"mstatus".to_string()));
        assert!(pre_state.contains(&"vtype".to_string()));
    }

    #[test]
    fn rv32_target_trait() {
        let target = rv32();
        assert_eq!(target.arch_name(), "riscv");
        assert_eq!(target.xlen(), "32");
        assert_eq!(target.xlen_name(), "rv32");
        assert!(target.reg_list().contains(&"vtype".to_string()));
    }

    #[test]
    fn rv64_constants() {
        let r = rv64();
        assert_eq!(r.page_size(), 4096);
        assert_eq!(r.page_shift(), 12);
        assert_eq!(r.ptes_per_level(), 512);
        assert_eq!(r.page_table_size(), 512 * 8);
        assert_eq!(1u64 << r.page_shift(), r.page_size());
        assert_eq!(r.pte_v(), 1);
        assert_eq!(r.pte_r(), 2);
        assert_eq!(r.pte_w(), 4);
        assert_eq!(r.pte_x(), 8);
    }
}
