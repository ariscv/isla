use std::collections::HashMap;
use std::ops::Range;

use isla_lib::bitvector::BV;
use isla_lib::config::{PmpConfig, PmpMode};
use isla_lib::error::ExecError;
use isla_lib::executor::LocalFrame;
use isla_lib::ir::{IRTypeInfo, Name, SharedState, Symtab, Ty, Val};
use isla_lib::register::RegisterBindings;
use isla_lib::smt::smtlib::{bits64, Exp};
use isla_lib::smt::{smtlib, Solver, Sym};
use isla_lib::source_loc::SourceLoc;
use isla_lib::zencode;

use super::context_state::GVAccessor;

pub type TranslationTableInfo = (Range<u64>, u64, u64);

pub trait Target
where
    Self: Sync,
{
    fn arch_name(&self) -> &'static str;
    fn arch_pretty_name(&self) -> &'static str;
    fn xlen(&self) -> &'static str;
    fn isa_state_list(&self) -> Vec<String>;

    /// 返回 Sail 模型初始化寄存器使用的函数名。
    fn init_function(&self) -> String {
        // RISC-V IR 中初始化函数名会通过 zencode 编码后查找。
        "initialize_registers".to_string()
    }

    /// 返回 testgen 执行单条指令时使用的默认起始 PC。
    fn default_init_pc(&self) -> u64 {
        // 该地址同时作为符号代码区的起点。
        0x8010_0000
    }

    /// 返回目标架构地址位宽。
    fn addr_size(&self) -> u32 {
        // 默认直接复用 xlen；解析失败时保守退回 64 位。
        self.xlen().parse().unwrap_or(64)
    }

    /// 返回需要符号化并纳入上下文观察的寄存器列表。
    fn regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)> {
        // 当前只支持 bitvector 形态的通用寄存器、浮点寄存器和 PC。
        self.isa_state_list()
            .into_iter()
            .filter(|reg| {
                reg == "PC"
                    || reg.strip_prefix('x').map(|suffix| suffix.chars().all(|c| c.is_ascii_digit())).unwrap_or(false)
                    || reg.strip_prefix('f').map(|suffix| suffix.chars().all(|c| c.is_ascii_digit())).unwrap_or(false)
            })
            .map(|reg| (reg, vec![]))
            .collect()
    }

    /// 返回即使 trace 未提及也必须输出的关键寄存器。
    fn essential_regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)> {
        // RISC-V 当前没有额外强制输出的系统寄存器。
        vec![]
    }

    /// 为特殊寄存器提供自定义初始化逻辑。
    fn special_reg_init<'ctx, 'ir, B: BV>(
        &self,
        _reg: &str,
        _acc: &Vec<GVAccessor<String>>,
        _ty: &Ty<Name>,
        _shared_state: &SharedState<'ir, B>,
        _frame: &mut LocalFrame<'ir, B>,
        _ctx: &'ctx isla_lib::smt::Context,
        _solver: &mut Solver<'ctx, B>,
    ) -> Option<(Sym, Val<B>)> {
        // 默认没有特殊寄存器，调用方会走通用符号化路径。
        None
    }

    /// 为特殊寄存器提供自定义 post-state 编码逻辑。
    fn special_reg_encode<'ctx, 'ir, B: BV>(
        &self,
        _reg: &str,
        _acc: &Vec<GVAccessor<String>>,
        _ty: &Ty<Name>,
        _shared_state: &SharedState<'ir, B>,
        _frame: &mut LocalFrame<'ir, B>,
        _ctx: &'ctx isla_lib::smt::Context,
        _solver: &mut Solver<'ctx, B>,
    ) -> Option<Val<B>> {
        // 默认直接读取寄存器当前值，不做额外编码。
        None
    }

    /// 在寄存器符号化后执行目标架构额外初始化。
    fn init<'ir, B: BV>(
        &self,
        _shared_state: &SharedState<'ir, B>,
        _frame: &mut LocalFrame<'ir, B>,
        _solver: &mut Solver<B>,
        _init_pc: u64,
        _regs: &HashMap<(String, Vec<GVAccessor<String>>), Sym>,
    ) {
        // RISC-V 当前没有额外初始化约束。
    }

    /// 单条指令执行完成后执行目标架构额外处理。
    fn post_instruction<'ir, B: BV>(
        &self,
        _shared_state: &SharedState<'ir, B>,
        _frame: &mut LocalFrame<'ir, B>,
        _solver: &mut Solver<B>,
    ) {
        // RISC-V 当前不需要额外 post-instruction 处理。
    }

    /// 返回用于特殊翻译表建模的信息。
    fn translation_table_info(&self) -> Option<TranslationTableInfo> {
        // RISC-V 当前不使用 testgen 的独立 translation table 建模。
        None
    }

    /// 返回 PC 对齐粒度的 2 的幂。
    fn pc_alignment_pow() -> u32 {
        // RISC-V 启用压缩指令时按 2 字节对齐。
        1
    }

    /// 返回 IR 中 PC 寄存器的编码名和 accessor。
    fn pc_reg(&self) -> (String, Vec<GVAccessor<String>>) {
        // 当前调用方直接查 symtab，因此这里返回 zencode 后的 zPC。
        ("zPC".to_string(), vec![])
    }

    /// 返回通用整数寄存器数量。
    fn number_gprs() -> u32 {
        // RISC-V 有 32 个 x 寄存器。
        32
    }

    /// 判断 IR 寄存器名是否为 RISC-V GPR，并返回编号。
    fn is_gpr(name: &str) -> Option<u32> {
        // IR 名称已经是 zencode 形式，例如 zx0。
        name.strip_prefix("zx").and_then(|reg| reg.parse().ok())
    }

    /// 返回需要作为异常边界停止的 Sail 函数名。
    fn exception_stop_functions() -> Vec<String> {
        // 保留通用 trap/exception handler 名称，避免异常路径继续扩展。
        vec!["trap_handler".to_string(), "exception_handler".to_string()]
    }

    /// 对执行结束后的 frame/solver 做目标架构后处理。
    fn postprocess<'ir, B: BV>(
        &self,
        _shared_state: &SharedState<'ir, B>,
        _frame: &LocalFrame<'ir, B>,
        _solver: &mut Solver<B>,
    ) -> Result<(), String> {
        // 默认认为执行结束状态已经可用于上下文提取。
        Ok(())
    }

    /// 返回 capability 地址清 tag 时使用的地址掩码。
    fn capability_address_mask() -> u64 {
        // RISC-V 无 capability tag 对齐需求。
        0
    }

    /// 返回执行单条指令时调用的 Sail step 函数名。
    fn run_instruction_function() -> String {
        // RISC-V Sail 模型从 hart 运行函数进入取指执行流程。
        "run_hart_active".to_string()
    }

    /// 返回 RISC-V step 函数所需的默认参数。
    fn run_instruction_args<B: BV>() -> Vec<Val<B>> {
        // run_hart_active 的 hart id 固定为 0。
        vec![Val::I128(0)]
    }

    /// 返回 harness 收尾用的最终指令 opcode。
    fn final_instruction<B: BV>(&self, _exit_register: u32) -> B {
        // ebreak 作为默认终止指令。
        B::from_u32(0x0010_0073)
    }
}

/// 构造翻译表范围内内存读取的 SMT 等式约束。
pub fn translation_table_exp(
    tt_info: &TranslationTableInfo,
    read_exp: smtlib::Exp<Sym>,
    addr_exp: smtlib::Exp<Sym>,
    bytes: u32,
) -> smtlib::Exp<Sym> {
    // 只为给定地址范围和 entry 生成一个小型 ITE 约束。
    let (addresses, tt_base, entry) = tt_info;
    let bits = 8 * bytes;
    let mask: u64 = 0xffff_ffff_ffff_ffff >> (64 - bits);
    let address_prop = Exp::And(
        Box::new(Exp::Bvule(Box::new(bits64(addresses.start, 64)), Box::new(addr_exp.clone()))),
        Box::new(Exp::Bvult(Box::new(addr_exp.clone()), Box::new(bits64(addresses.end, 64)))),
    );
    let mut value_exp = bits64(0, bits);
    for byte in (0..8).rev() {
        value_exp = Exp::Ite(
            Box::new(Exp::Eq(Box::new(addr_exp.clone()), Box::new(bits64(*tt_base + byte, 64)))),
            Box::new(bits64((*entry >> (byte * 8)) & mask, bits)),
            Box::new(value_exp),
        );
    }
    Exp::And(Box::new(address_prop), Box::new(Exp::Eq(Box::new(read_exp), Box::new(value_exp))))
}

pub trait RISCV: Target {
    const XLEN: u32;

    fn xlen_name(&self) -> &'static str;
    fn pmp_symbolic(&self) -> bool;

    fn ppn_from_pa(&self, pa: u64) -> u64 {
        pa >> 12
    }

    fn pa_from_ppn(&self, ppn: u64) -> u64 {
        ppn << 12
    }

    // Page table constants
    const PAGE_SIZE: u64 = 4096;
    const PAGE_SHIFT: u64 = 12;
    const PTE_SIZE: u64 = 8;
    const PTES_PER_LEVEL: u64 = 512;
    const PAGE_TABLE_SIZE: u64 = Self::PTES_PER_LEVEL * Self::PTE_SIZE;
    const PTE_V: u64 = 1;
    const PTE_R: u64 = 2;
    const PTE_W: u64 = 4;
    const PTE_X: u64 = 8;
    const PTE_U: u64 = 16;
    const PTE_A: u64 = 64;
    const PTE_D: u64 = 128;

    fn page_size(&self) -> u64 {
        Self::PAGE_SIZE
    }
    fn page_shift(&self) -> u64 {
        Self::PAGE_SHIFT
    }
    fn pte_size(&self) -> u64 {
        Self::PTE_SIZE
    }
    fn ptes_per_level(&self) -> u64 {
        Self::PTES_PER_LEVEL
    }
    fn page_table_size(&self) -> u64 {
        Self::PAGE_TABLE_SIZE
    }
    fn pte_v(&self) -> u64 {
        Self::PTE_V
    }
    fn pte_r(&self) -> u64 {
        Self::PTE_R
    }
    fn pte_w(&self) -> u64 {
        Self::PTE_W
    }
    fn pte_x(&self) -> u64 {
        Self::PTE_X
    }
    fn pte_u(&self) -> u64 {
        Self::PTE_U
    }
    fn pte_a(&self) -> u64 {
        Self::PTE_A
    }
    fn pte_d(&self) -> u64 {
        Self::PTE_D
    }

    fn apply_pmp_rules_to_config<B: BV>(
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

    fn apply_symbolic_pmp_to_registers<'ir, B: BV>(
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

impl<T: RISCV> Target for T {
    fn arch_name(&self) -> &'static str {
        "riscv"
    }

    fn arch_pretty_name(&self) -> &'static str {
        self.xlen_name()
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

pub struct RV32 {
    pub pmp_symbolic: bool,
}

impl Default for RV32 {
    fn default() -> Self {
        RV32 { pmp_symbolic: false }
    }
}

impl RISCV for RV32 {
    const XLEN: u32 = 32;

    fn xlen_name(&self) -> &'static str {
        "rv32"
    }

    fn pmp_symbolic(&self) -> bool {
        self.pmp_symbolic
    }
}

pub struct RV64 {
    pub pmp_symbolic: bool,
}

impl Default for RV64 {
    fn default() -> Self {
        RV64 { pmp_symbolic: false }
    }
}

impl RISCV for RV64 {
    const XLEN: u32 = 64;

    fn xlen_name(&self) -> &'static str {
        "rv64"
    }

    fn pmp_symbolic(&self) -> bool {
        self.pmp_symbolic
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

    pub fn sv39_vpn_indices(&self, va: u64) -> [u64; 3] {
        [(va >> 12) & 0x1FF, (va >> 21) & 0x1FF, (va >> 30) & 0x1FF]
    }

    pub fn sv48_vpn_indices(&self, va: u64) -> [u64; 4] {
        [(va >> 12) & 0x1FF, (va >> 21) & 0x1FF, (va >> 30) & 0x1FF, (va >> 39) & 0x1FF]
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
        let pte_v = RiscvPte::new(0, RV64::PTE_V);
        assert!(pte_v.is_valid());
        assert!(!pte_v.has_read());

        let pte_r = RiscvPte::new(0, RV64::PTE_R);
        assert!(!pte_r.is_valid());
        assert!(pte_r.has_read());

        let pte_w = RiscvPte::new(0, RV64::PTE_W);
        assert!(pte_w.has_write());

        let pte_x = RiscvPte::new(0, RV64::PTE_X);
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
        let ppn = 0xABCD;
        let flags = RV64::PTE_V | RV64::PTE_R | RV64::PTE_W | RV64::PTE_A | RV64::PTE_D;
        let pte = RiscvPte::new(ppn, flags);
        let reconstructed = RiscvPte::new(pte.ppn(), pte.flags());
        assert_eq!(pte.bits, reconstructed.bits);
    }

    #[test]
    fn sv39_vpn_indices_zero() {
        assert_eq!(RV64::default().sv39_vpn_indices(0), [0, 0, 0]);
    }

    #[test]
    fn sv39_vpn_indices_known() {
        let indices = RV64::default().sv39_vpn_indices(0x0400_0000);
        assert_eq!(indices[0], 0);
        assert_eq!(indices[1], 32);
        assert_eq!(indices[2], 0);
    }

    #[test]
    fn sv39_vpn_indices_max() {
        let va = (0x1FFu64 << 12) | (0x1FF << 21) | (0x1FF << 30);
        let indices = RV64::default().sv39_vpn_indices(va);
        assert_eq!(indices, [511, 511, 511]);
    }

    #[test]
    fn sv48_vpn_indices_zero() {
        assert_eq!(RV64::default().sv48_vpn_indices(0), [0, 0, 0, 0]);
    }

    #[test]
    fn sv48_vpn_indices_four_levels() {
        let va = (0x1u64 << 12) | (0x2u64 << 21) | (0x3u64 << 30) | (0x4u64 << 39);
        let indices = RV64::default().sv48_vpn_indices(va);
        assert_eq!(indices, [1, 2, 3, 4]);
    }

    #[test]
    fn ppn_pa_roundtrip() {
        let pa = 0x8000_1000u64;
        let rv64 = RV64::default();
        let ppn = rv64.ppn_from_pa(pa);
        assert_eq!(ppn, 0x8000_1);
        assert_eq!(rv64.pa_from_ppn(ppn), pa);
    }

    #[test]
    fn ppn_from_pa_strips_offset() {
        assert_eq!(RV64::default().ppn_from_pa(0x8000_1234), 0x8000_1);
    }

    #[test]
    fn pa_from_ppn_aligned() {
        let rv64 = RV64::default();
        let pa = rv64.pa_from_ppn(0x1234);
        assert_eq!(pa % RV64::PAGE_SIZE, 0);
    }

    #[test]
    fn rv64_target_trait() {
        let target = RV64::default();
        assert_eq!(target.arch_name(), "riscv");
        assert_eq!(target.xlen(), "64");
        assert_eq!(target.xlen_name(), "rv64");
        let regs = target.isa_state_list();
        assert!(regs.contains(&"x0".to_string()));
        assert!(regs.contains(&"PC".to_string()));
    }

    #[test]
    fn rv32_target_trait() {
        let target = RV32::default();
        assert_eq!(target.arch_name(), "riscv");
        assert_eq!(target.xlen(), "32");
        assert_eq!(target.xlen_name(), "rv32");
    }

    #[test]
    fn rv64_constants() {
        assert_eq!(RV64::PAGE_SIZE, 4096);
        assert_eq!(RV64::PAGE_SHIFT, 12);
        assert_eq!(RV64::PTES_PER_LEVEL, 512);
        assert_eq!(RV64::PAGE_TABLE_SIZE, 512 * 8);
        assert_eq!(1u64 << RV64::PAGE_SHIFT, RV64::PAGE_SIZE);
        assert_eq!(RV64::PTE_V, 1);
        assert_eq!(RV64::PTE_R, 2);
        assert_eq!(RV64::PTE_W, 4);
        assert_eq!(RV64::PTE_X, 8);
    }
}
