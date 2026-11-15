//! RISC-V 平台配置及 PMA 的模型生命周期；不在通用层解释 Sail 字段。
use super::pma::{self, PmaRegionConfig, PmaSize};
use isla_lib::bitvector::BV;
use isla_lib::ir::{IRTypeInfo, Name, SharedState, Symtab, Val};
use isla_lib::register::RegisterBindings;
use isla_lib::smt::{Solver, Sym};
use std::collections::HashMap;

#[derive(Debug, Clone, Default)]
pub struct RiscvPlatformConfig {
    pub pma_regions: Option<Vec<PmaRegionConfig>>,
}

impl RiscvPlatformConfig {
    pub fn from_merged_toml(merged: &toml::Value) -> Result<Self, String> {
        Ok(Self { pma_regions: pma::get_pma_regions(merged)? })
    }

    pub(super) fn configure_model<B: BV>(
        &self,
        symtab: &Symtab,
        type_info: &IRTypeInfo,
        defaults: &mut HashMap<Name, Val<B>>,
    ) -> Result<(), String> {
        if let Some(regions) = &self.pma_regions {
            if !regions.iter().any(|region| matches!(region.size, PmaSize::Symbolic { .. })) {
                pma::apply_pma_regions_to_config(regions, symtab, type_info, defaults)?;
            }
        }
        Ok(())
    }

    pub(super) fn initialize_execution<'ir, B: BV>(
        &self,
        regs: &mut RegisterBindings<'ir, B>,
        shared: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
    ) -> Result<Vec<(String, Sym)>, String> {
        if let Some(regions) = &self.pma_regions {
            if regions.iter().any(|region| matches!(region.size, PmaSize::Symbolic { .. })) {
                return pma::apply_symbolic_pma_regions_to_registers(
                    regions,
                    &shared.symtab,
                    &shared.type_info,
                    regs,
                    shared,
                    solver,
                );
            }
        }
        Ok(Vec::new())
    }

    pub(super) fn validate_bindings(&self, bindings: &[(String, Sym)]) -> Result<(), String> {
        let mut expected = HashMap::<String, usize>::new();
        for region in self.pma_regions.iter().flatten().filter(|region| matches!(region.size, PmaSize::Symbolic { .. }))
        {
            *expected.entry(format!("pma_regions.{}.size", region.name)).or_default() += 1;
        }
        for (name, _) in bindings {
            let count = expected.get_mut(name).ok_or_else(|| format!("未知的 RISC-V 模型绑定 {}", name))?;
            if *count == 0 {
                return Err(format!("重复的 RISC-V 模型绑定 {}", name));
            }
            *count -= 1;
        }
        if expected.values().any(|count| *count != 0) {
            return Err("RISC-V 模型绑定缺少已配置的符号 size".to_string());
        }
        Ok(())
    }
}
