//! RISC-V target 的配置、模型初始化与已有 RV32／RV64 实现。
use super::*;
mod platform;
pub mod pma;
pub use platform::RiscvPlatformConfig;

pub trait RISCV<B: BV>: Target<B> {
    fn pmp_symbolic(&self) -> bool;
    fn ppn_from_pa(&self, pa: u64) -> u64 {
        pa >> 12
    }

    fn pa_from_ppn(&self, ppn: u64) -> u64 {
        ppn << 12
    }

    // 页表常量使用既有默认值，各实现可按需覆盖。
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
    pub platform: RiscvPlatformConfig,
    pub model_bindings: Vec<(String, Sym)>,
    pub symbolic_csrs: Vec<SymbolicRegisterConfig>,
    pub pre_state: PreStateCtx<B>,
}

impl<B: BV> Default for RV32<B> {
    fn default() -> Self {
        RV32 {
            pmp_symbolic: false,
            platform: RiscvPlatformConfig::default(),
            model_bindings: Vec::new(),
            symbolic_csrs: Vec::new(),
            pre_state: PreStateCtx::new(),
        }
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
    fn configure_model(
        &mut self,
        merged: &toml::Value,
        symtab: &Symtab,
        type_info: &IRTypeInfo,
        defaults: &mut HashMap<Name, Val<B>>,
    ) -> Result<(), String> {
        self.platform = RiscvPlatformConfig::from_merged_toml(merged)?;
        self.model_bindings.clear();
        self.platform.configure_model(symtab, type_info, defaults)
    }
    fn initialize_execution<'ir>(
        &mut self,
        regs: &mut RegisterBindings<'ir, B>,
        shared: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
    ) -> Result<(), ExecError> {
        // 每个 clause／hint 批使用新 solver，旧批绑定不能带入本批。
        self.model_bindings = self
            .platform
            .initialize_execution(regs, shared, solver)
            .map_err(|error| ExecError::Type(error, SourceLoc::command_line()))?;
        Ok(())
    }
    fn model_bindings(&self) -> &[(String, Sym)] {
        &self.model_bindings
    }
    fn restore_model_bindings(&mut self, bindings: &[(String, Sym)]) -> Result<(), String> {
        assert!(self.model_bindings.is_empty(), "恢复前模型绑定必须为空");
        self.platform.validate_bindings(bindings)?;
        self.model_bindings.extend_from_slice(bindings);
        Ok(())
    }
    fn symbolic_csrs(&self) -> &[SymbolicRegisterConfig] {
        &self.symbolic_csrs
    }
    fn reg_list(&self) -> Vec<String> {
        let mut regs: Vec<String> = (1..32).map(|r| format!("x{}", r)).collect();
        regs.extend((0..32).map(|r| format!("f{}", r)));
        regs.extend((0..32).map(|r| format!("vr{}", r)));
        regs.push("PC".to_string());
        regs.push("cur_privilege".to_string());
        regs.push("mstatus".to_string());
        regs.push("fcsr".to_string());
        regs.push("vl".to_string());
        regs.push("vstart".to_string());
        regs.push("vtype".to_string());
        regs.push("vcsr".to_string());
        regs.push("reservation_valid".to_string());
        regs.push("reservation_addr".to_string());
        regs
    }
    fn must_output_register(&self, reg_name: &str) -> bool {
        matches!(reg_name, "reservation_valid" | "reservation_addr")
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
    pub platform: RiscvPlatformConfig,
    pub model_bindings: Vec<(String, Sym)>,
    pub symbolic_csrs: Vec<SymbolicRegisterConfig>,
    pub pre_state: PreStateCtx<B>,
    pub initial_state: Vec<InitialRegisterConfig>,
}

impl<B: BV> Default for RV64<B> {
    fn default() -> Self {
        RV64 {
            pmp_symbolic: false,
            platform: RiscvPlatformConfig::default(),
            model_bindings: Vec::new(),
            symbolic_csrs: Vec::new(),
            pre_state: PreStateCtx::new(),
            initial_state: Vec::new(),
        }
    }
}

impl<B: BV> Target<B> for RV64<B> {
    fn initial_state(&self) -> &[InitialRegisterConfig] {
        &self.initial_state
    }

    fn arch_name(&self) -> &'static str {
        "riscv"
    }
    fn xlen_name(&self) -> &'static str {
        "rv64"
    }
    fn xlen(&self) -> &'static str {
        "64"
    }
    fn configure_model(
        &mut self,
        merged: &toml::Value,
        symtab: &Symtab,
        type_info: &IRTypeInfo,
        defaults: &mut HashMap<Name, Val<B>>,
    ) -> Result<(), String> {
        self.platform = RiscvPlatformConfig::from_merged_toml(merged)?;
        self.model_bindings.clear();
        self.platform.configure_model(symtab, type_info, defaults)
    }
    fn initialize_execution<'ir>(
        &mut self,
        regs: &mut RegisterBindings<'ir, B>,
        shared: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
    ) -> Result<(), ExecError> {
        // 每个 clause／hint 批使用新 solver，旧批绑定不能带入本批。
        self.model_bindings = self
            .platform
            .initialize_execution(regs, shared, solver)
            .map_err(|error| ExecError::Type(error, SourceLoc::command_line()))?;
        Ok(())
    }
    fn model_bindings(&self) -> &[(String, Sym)] {
        &self.model_bindings
    }
    fn restore_model_bindings(&mut self, bindings: &[(String, Sym)]) -> Result<(), String> {
        assert!(self.model_bindings.is_empty(), "恢复前模型绑定必须为空");
        self.platform.validate_bindings(bindings)?;
        self.model_bindings.extend_from_slice(bindings);
        Ok(())
    }
    fn symbolic_csrs(&self) -> &[SymbolicRegisterConfig] {
        &self.symbolic_csrs
    }
    fn reg_list(&self) -> Vec<String> {
        let mut regs: Vec<String> = (1..32).map(|r| format!("x{}", r)).collect();
        regs.extend((0..32).map(|r| format!("f{}", r)));
        regs.extend((0..32).map(|r| format!("vr{}", r)));
        // regs.push("PC".to_string());
        regs.push("cur_privilege".to_string());
        regs.push("mstatus".to_string());
        regs.push("fcsr".to_string());
        regs.push("vl".to_string());
        regs.push("vstart".to_string());
        regs.push("vtype".to_string());
        regs.push("vcsr".to_string());
        regs.push("reservation_valid".to_string());
        regs.push("reservation_addr".to_string());
        regs
    }
    fn must_output_register(&self, reg_name: &str) -> bool {
        // V 上下文寄存器沿用原必输出集合；f0-f31/vr0-vr31 为 F4 扩展（见 trait
        // 默认实现的注释），复用 is_vector_register_name 的 vr 判定形态。
        if matches!(reg_name, "vl" | "vstart" | "vtype" | "vcsr" | "reservation_valid" | "reservation_addr") {
            return true;
        }
        let digits = reg_name.strip_prefix("vr").or_else(|| reg_name.strip_prefix('f')).unwrap_or("");
        !digits.is_empty()
            && digits.len() <= 2
            && digits.bytes().all(|byte| byte.is_ascii_digit())
            && digits.parse::<u32>().map(|index| index < 32).unwrap_or(false)
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
        [(va >> 12) & 0x1FF, (va >> 21) & 0x1FF, (va >> 30) & 0x1FF, (va >> 39) & 0x1FF]
    }
}

#[cfg(test)]
mod reservation_tests;
