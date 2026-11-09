use std::collections::HashMap;
use std::ops::Range;
use std::sync::Arc;

use super::target::{RiscvPte, RISCV};
use isla_lib::bitvector::BV;
use isla_lib::config::{ISAConfig, MemoryRegionType, PageTableConfig, PageTableMode, PageTablePreset, ProtectedRange};
use isla_lib::memory::{Memory, Region};

enum PendingRegion {
    Concrete { base: u64, size: u64 },
    Symbolic { base: u64, size: u64 },
    Excluded { base: u64, size: u64 },
}

pub struct MemoryBuilder<'a, B: BV> {
    target: &'a dyn RISCV<B>,
    regions: Vec<PendingRegion>,
    page_table_config: Option<PageTableConfig>,
    clint_enabled: bool,
    clint_base: u64,
    clint_size: u64,
}

impl<'a, B: BV> MemoryBuilder<'a, B> {
    pub fn new(target: &'a dyn RISCV<B>) -> Self {
        MemoryBuilder {
            target,
            regions: Vec::new(),
            page_table_config: None,
            clint_enabled: true,
            clint_base: 0x2000000,
            clint_size: 0xc0000,
        }
    }

    pub fn from_config(target: &'a dyn RISCV<B>, config: &ISAConfig<B>) -> Result<Self, String> {
        let mut builder = MemoryBuilder::new(target);
        if let Some(ref regions) = config.memory_regions {
            for region in regions {
                builder = match region.region_type {
                    MemoryRegionType::Concrete => builder.add_concrete_region(region.base, region.size),
                    MemoryRegionType::Symbolic => builder.add_symbolic_region(region.base, region.size),
                    MemoryRegionType::Excluded => builder.add_excluded_region(region.base, region.size),
                    // MemoryRegionType 标了 non_exhaustive，穷举需要兜底臂；三个
                    // 已知变体都已处理，走到这里说明 isla 与 isla-lib 版本不一致。
                    _ => panic!("MemoryRegionType 出现未覆盖的变体（isla 与 isla-lib 版本不一致）"),
                };
            }
        }
        builder.page_table_config = config.page_table_config.clone();
        if config.clint_enabled == Some(false) {
            builder = builder.set_clint_enabled(false);
        }
        Ok(builder)
    }

    pub fn add_concrete_region(mut self, base: u64, size: u64) -> Self {
        self.regions.push(PendingRegion::Concrete { base, size });
        self
    }

    pub fn add_symbolic_region(mut self, base: u64, size: u64) -> Self {
        self.regions.push(PendingRegion::Symbolic { base, size });
        self
    }

    pub fn add_excluded_region(mut self, base: u64, size: u64) -> Self {
        self.regions.push(PendingRegion::Excluded { base, size });
        self
    }

    pub fn set_clint_enabled(mut self, enabled: bool) -> Self {
        self.clint_enabled = enabled;
        self
    }

    pub fn set_clint_params(mut self, base: u64, size: u64) -> Self {
        self.clint_base = base;
        self.clint_size = size;
        self
    }

    pub fn with_identity_mapping(mut self, page_table_base: u64) -> Result<Self, String> {
        self.page_table_config = Some(PageTableConfig {
            mode: PageTableMode::SV39,
            preset: PageTablePreset::Identity,
            base: page_table_base,
            page_size: 4096,
            offset: None,
            protected_ranges: None,
        });
        Ok(self)
    }

    pub fn with_offset_mapping(mut self, page_table_base: u64, offset: u64) -> Result<Self, String> {
        self.page_table_config = Some(PageTableConfig {
            mode: PageTableMode::SV39,
            preset: PageTablePreset::Offset,
            base: page_table_base,
            page_size: 4096,
            offset: Some(offset as i64),
            protected_ranges: None,
        });
        Ok(self)
    }

    pub fn with_protected_mapping(
        mut self,
        page_table_base: u64,
        protected_ranges: Vec<ProtectedRange>,
    ) -> Result<Self, String> {
        self.page_table_config = Some(PageTableConfig {
            mode: PageTableMode::SV39,
            preset: PageTablePreset::ProtectedLinear,
            base: page_table_base,
            page_size: 4096,
            offset: None,
            protected_ranges: Some(protected_ranges),
        });
        Ok(self)
    }

    pub fn with_symbolic_mapping(mut self, page_table_base: u64) -> Result<Self, String> {
        self.page_table_config = Some(PageTableConfig {
            mode: PageTableMode::SV39,
            preset: PageTablePreset::SymbolicMapping,
            base: page_table_base,
            page_size: 4096,
            offset: None,
            protected_ranges: None,
        });
        Ok(self)
    }

    pub fn page_table_config(mut self, config: PageTableConfig) -> Self {
        self.page_table_config = Some(config);
        self
    }

    pub fn clint(mut self, enabled: bool) -> Self {
        self.clint_enabled = enabled;
        self
    }

    pub fn clint_with_params(mut self, enabled: bool, base: u64, size: u64) -> Self {
        self.clint_enabled = enabled;
        self.clint_base = base;
        self.clint_size = size;
        self
    }

    pub fn build(mut self) -> Result<Memory<B>, String> {
        let mut ranges: Vec<(&str, Range<u64>)> = Vec::new();

        for region in &self.regions {
            let (label, base, size) = match region {
                PendingRegion::Concrete { base, size } => ("concrete", *base, *size),
                PendingRegion::Symbolic { base, size } => ("symbolic", *base, *size),
                PendingRegion::Excluded { base, size } => ("excluded", *base, *size),
            };
            let end = base
                .checked_add(size)
                .ok_or_else(|| format!("{} region at 0x{:x} with size 0x{:x} overflows", label, base, size))?;
            ranges.push((label, base..end));
        }

        if self.clint_enabled {
            if self.clint_size == 0 {
                return Err("CLINT size must be greater than 0".to_string());
            }
            let clint_end =
                self.clint_base.checked_add(self.clint_size).ok_or_else(|| "CLINT address range overflows")?;
            ranges.push(("clint", self.clint_base..clint_end));
        }

        if let Some(ref config) = self.page_table_config {
            self.validate_page_table_config(config)?;
            let pt_end = config
                .base
                .checked_add(self.page_table_size(config))
                .ok_or_else(|| "page table address range overflows".to_string())?;
            ranges.push(("page table", config.base..pt_end));
        }

        let mut sorted: Vec<(&str, Range<u64>)> = ranges;
        sorted.sort_by_key(|(_, r)| r.start);

        for pair in sorted.windows(2) {
            let (prev_label, prev_range) = &pair[0];
            let (curr_label, curr_range) = &pair[1];
            if prev_range.end > curr_range.start {
                return Err(format!(
                    "overlapping regions: {} [0x{:x}, 0x{:x}) and {} [0x{:x}, 0x{:x})",
                    prev_label, prev_range.start, prev_range.end, curr_label, curr_range.start, curr_range.end
                ));
            }
        }

        let mut memory = Memory::new();

        for region in &self.regions {
            match region {
                PendingRegion::Concrete { base, size } => {
                    memory.add_zero_region(*base..base + size);
                }
                PendingRegion::Symbolic { base, size } => {
                    memory.add_symbolic_region(*base..base + size);
                }
                PendingRegion::Excluded { base, size } => {
                    memory.add_excluded_region(*base..base + size);
                }
            }
        }

        if self.clint_enabled {
            memory.add_zero_region(self.clint_base..self.clint_base + self.clint_size);
        }

        if let Some(ref config) = self.page_table_config {
            match config.preset {
                PageTablePreset::Identity => self.populate_identity_mapping(config, &mut memory)?,
                PageTablePreset::Offset => self.populate_offset_mapping(config, &mut memory)?,
                PageTablePreset::ProtectedLinear => self.populate_protected_mapping(config, &mut memory)?,
                PageTablePreset::SymbolicMapping => self.populate_symbolic_mapping(config, &mut memory)?,
                _ => return Err("unsupported page table preset".to_string()),
            }
        }

        Ok(memory)
    }

    fn populate_identity_mapping(&self, config: &PageTableConfig, memory: &mut Memory<B>) -> Result<(), String> {
        self.validate_page_table_config(config)?;
        match config.mode {
            PageTableMode::SV39 => self
                .populate_sv39_tables(config, |vpn1| Ok(self.default_leaf_pte(vpn1 << 21)))
                .map(|region| memory.add_region(region)),
            PageTableMode::SV48 => self
                .populate_sv48_tables(config, |vpn1| Ok(self.default_leaf_pte(vpn1 << 21)))
                .map(|region| memory.add_region(region)),
            _ => Err("unsupported page table mode".to_string()),
        }
    }

    fn populate_offset_mapping(&self, config: &PageTableConfig, memory: &mut Memory<B>) -> Result<(), String> {
        self.validate_page_table_config(config)?;
        let offset = config.offset.ok_or_else(|| "offset mapping requires offset field".to_string())?;
        if offset % (1 << 21) != 0 {
            return Err(format!("offset 0x{:x} must be 2MiB aligned for megapage mapping", offset));
        }
        match config.mode {
            PageTableMode::SV39 => self
                .populate_sv39_tables(config, |vpn1| {
                    let pa = (vpn1 << 21).wrapping_add(offset as u64);
                    Ok(self.default_leaf_pte(pa))
                })
                .map(|region| memory.add_region(region)),
            PageTableMode::SV48 => self
                .populate_sv48_tables(config, |vpn1| {
                    let pa = (vpn1 << 21).wrapping_add(offset as u64);
                    Ok(self.default_leaf_pte(pa))
                })
                .map(|region| memory.add_region(region)),
            _ => Err("unsupported page table mode".to_string()),
        }
    }

    fn populate_protected_mapping(&self, config: &PageTableConfig, memory: &mut Memory<B>) -> Result<(), String> {
        self.validate_page_table_config(config)?;
        match config.mode {
            PageTableMode::SV39 => self
                .populate_sv39_tables(config, |vpn1| {
                    let va = vpn1 << 21;
                    let flags = self.flags_for_va(config, va)?;
                    Ok(RiscvPte::new(self.target.ppn_from_pa(va), flags))
                })
                .map(|region| memory.add_region(region)),
            PageTableMode::SV48 => self
                .populate_sv48_tables(config, |vpn1| {
                    let va = vpn1 << 21;
                    let flags = self.flags_for_va(config, va)?;
                    Ok(RiscvPte::new(self.target.ppn_from_pa(va), flags))
                })
                .map(|region| memory.add_region(region)),
            _ => Err("unsupported page table mode".to_string()),
        }
    }

    fn populate_symbolic_mapping(&self, config: &PageTableConfig, memory: &mut Memory<B>) -> Result<(), String> {
        self.validate_page_table_config(config)?;
        let pt_size = match config.mode {
            PageTableMode::SV39 => self.sv39_table_size(),
            PageTableMode::SV48 => self.sv48_table_size(),
            _ => return Err("unsupported page table mode".to_string()),
        };
        memory.add_symbolic_region(config.base..config.base + pt_size);
        Ok(())
    }

    /// SV39 two-level page table: L2(root) -> L1(megapage leaves, 2MiB each).
    /// Only L2 entry[0] is valid (non-leaf pointing to L1 table).
    /// L1 has 512 leaf PTEs covering virtual addresses 0..1GiB.
    fn populate_sv39_tables<F>(&self, config: &PageTableConfig, mut pte_for_vpn1: F) -> Result<Region<B>, String>
    where
        F: FnMut(u64) -> Result<RiscvPte, String>,
    {
        let l1_base = config
            .base
            .checked_add(self.target.page_table_size())
            .ok_or_else(|| "SV39 L1 table address overflows".to_string())?;

        let mut pte_bytes = HashMap::new();

        // L2 (root) table: entry[0] = non-leaf pointer to L1, rest invalid (zero)
        let l2_pte = RiscvPte::new(self.target.ppn_from_pa(l1_base), self.target.pte_v());
        for (i, &byte) in l2_pte.to_bytes().iter().enumerate() {
            pte_bytes.insert(config.base + i as u64, byte);
        }

        // L1 table: 512 leaf PTEs, each mapping a 2MiB megapage
        for vpn1 in 0..self.target.ptes_per_level() {
            let bytes = pte_for_vpn1(vpn1)?.to_bytes();
            let addr = l1_base + vpn1 * self.target.pte_size();
            for (i, &byte) in bytes.iter().enumerate() {
                pte_bytes.insert(addr + i as u64, byte);
            }
        }

        Ok(Region::Concrete(config.base..config.base + self.sv39_table_size(), Arc::new(pte_bytes)))
    }

    /// SV48 three-level page table: L3(root) -> L2 -> L1(megapage leaves, 2MiB each).
    /// L3 entry[0] -> L2 table, L2 entry[0] -> L1 table.
    /// L1 has 512 leaf PTEs covering virtual addresses 0..1GiB.
    fn populate_sv48_tables<F>(&self, config: &PageTableConfig, mut pte_for_vpn1: F) -> Result<Region<B>, String>
    where
        F: FnMut(u64) -> Result<RiscvPte, String>,
    {
        let l2_base = config
            .base
            .checked_add(self.target.page_table_size())
            .ok_or_else(|| "SV48 L2 table address overflows".to_string())?;
        let l1_base = l2_base
            .checked_add(self.target.page_table_size())
            .ok_or_else(|| "SV48 L1 table address overflows".to_string())?;

        let mut pte_bytes = HashMap::new();

        // L3 (root) table: entry[0] = non-leaf pointer to L2, rest invalid (zero)
        let l3_pte = RiscvPte::new(self.target.ppn_from_pa(l2_base), self.target.pte_v());
        for (i, &byte) in l3_pte.to_bytes().iter().enumerate() {
            pte_bytes.insert(config.base + i as u64, byte);
        }

        // L2 table: entry[0] = non-leaf pointer to L1, rest invalid (zero)
        let l2_pte = RiscvPte::new(self.target.ppn_from_pa(l1_base), self.target.pte_v());
        for (i, &byte) in l2_pte.to_bytes().iter().enumerate() {
            pte_bytes.insert(l2_base + i as u64, byte);
        }

        // L1 table: 512 leaf PTEs, each mapping a 2MiB megapage
        for vpn1 in 0..self.target.ptes_per_level() {
            let bytes = pte_for_vpn1(vpn1)?.to_bytes();
            let addr = l1_base + vpn1 * self.target.pte_size();
            for (i, &byte) in bytes.iter().enumerate() {
                pte_bytes.insert(addr + i as u64, byte);
            }
        }

        Ok(Region::Concrete(config.base..config.base + self.sv48_table_size(), Arc::new(pte_bytes)))
    }

    fn flags_for_va(&self, config: &PageTableConfig, va: u64) -> Result<u64, String> {
        if let Some(ref ranges) = config.protected_ranges {
            for range in ranges {
                let end = range.base.checked_add(range.size).ok_or_else(|| {
                    format!("protected range at 0x{:x} with size 0x{:x} overflows", range.base, range.size)
                })?;
                let page_end = va + self.l1_megapage_size();
                if va < end && page_end > range.base {
                    return self.parse_pte_flags(&range.flags);
                }
            }
        }

        Ok(self.default_leaf_flags())
    }

    fn parse_pte_flags(&self, flags: &str) -> Result<u64, String> {
        let mut pte_flags = self.target.pte_v() | self.target.pte_a() | self.target.pte_d();
        for flag in flags.chars() {
            match flag {
                'r' => pte_flags |= self.target.pte_r(),
                'w' => pte_flags |= self.target.pte_w(),
                'x' => pte_flags |= self.target.pte_x(),
                'u' => pte_flags |= self.target.pte_u(),
                _ => return Err(format!("unknown protected range PTE flag '{}'", flag)),
            }
        }
        if pte_flags & self.target.pte_w() != 0 && pte_flags & self.target.pte_r() == 0 {
            return Err("PTE flags 'w' requires 'r' (W=1,R=0 is reserved in RISC-V)".to_string());
        }
        Ok(pte_flags)
    }

    fn default_leaf_pte(&self, pa: u64) -> RiscvPte {
        RiscvPte::new(self.target.ppn_from_pa(pa), self.default_leaf_flags())
    }

    fn default_leaf_flags(&self) -> u64 {
        self.target.pte_v()
            | self.target.pte_r()
            | self.target.pte_w()
            | self.target.pte_x()
            | self.target.pte_u()
            | self.target.pte_a()
            | self.target.pte_d()
    }

    fn validate_page_table_config(&self, config: &PageTableConfig) -> Result<(), String> {
        if config.base % 4096 != 0 {
            return Err(format!("page_table_config.base 0x{:x} must be 4KiB aligned", config.base));
        }
        match config.mode {
            PageTableMode::SV39 | PageTableMode::SV48 => {}
            _ => return Err("unsupported page table mode".to_string()),
        }
        Ok(())
    }

    fn page_table_size(&self, config: &PageTableConfig) -> u64 {
        match config.mode {
            PageTableMode::SV39 => self.sv39_table_size(),
            PageTableMode::SV48 => self.sv48_table_size(),
            _ => 0,
        }
    }

    fn sv39_table_size(&self) -> u64 {
        2 * self.target.page_table_size()
    }

    fn sv48_table_size(&self) -> u64 {
        3 * self.target.page_table_size()
    }

    fn l1_megapage_size(&self) -> u64 {
        self.target.ptes_per_level() * self.target.page_size()
    }
}

/// solve-state 内存装配的可选兜底：`add_default_ram=true` 且配置未声明任何
/// `Region::Symbolic` 区域时补一个默认符号 RAM 区域。
///
/// W6 起零配置的语义是**彻底全符号化**：数组内存模型（W2
/// `memory_model::SeqMemory`）下地址与数组内容全部自由，可满足性不依赖区域
/// （写侧空 OR 链折叠成 `false` 的 bug 已修复），因此默认**不再**隐式补区域。
/// `ISLA_RISCV_DEFAULT_SYM_RAM=1`（`default_sym_ram_enabled`）显式要求时才补，
/// 范围与 riscv64_difftest_mem.toml 的 sym_ram 对齐（0x80000000 起 256MB），
/// 供 difftest 重放在未配置 `[[memory_regions]]` 时把访存地址圈进常规 RAM。
/// 已配置符号区域时保持不变；默认范围与既有区域重叠属于配置错误，直接
/// panic 提示显式声明 `[[memory_regions]]`。
pub fn ensure_solve_state_memory<B: BV>(mut memory: Memory<B>, add_default_ram: bool) -> Memory<B> {
    if !add_default_ram {
        return memory;
    }
    if memory.regions().iter().any(|region| matches!(region, Region::Symbolic(_))) {
        return memory;
    }
    const DEFAULT_SYMBOLIC_RAM_BASE: u64 = 0x8000_0000;
    const DEFAULT_SYMBOLIC_RAM_SIZE: u64 = 0x1000_0000;
    let default_range = DEFAULT_SYMBOLIC_RAM_BASE..DEFAULT_SYMBOLIC_RAM_BASE + DEFAULT_SYMBOLIC_RAM_SIZE;
    let overlaps = memory.regions().iter().any(|region| {
        region.region_range().start < default_range.end && default_range.start < region.region_range().end
    });
    if overlaps {
        panic!(
            "solve-state 默认符号 RAM 区域 [0x{:x}, 0x{:x}) 与配置的内存区域重叠，请在配置中显式声明 [[memory_regions]] 的 symbolic 区域",
            default_range.start, default_range.end
        );
    }
    memory.add_symbolic_region(default_range);
    memory
}

/// 环境变量 `ISLA_RISCV_DEFAULT_SYM_RAM` 是否要求 solve-state 补默认符号 RAM。
///
/// 默认关闭（尊重零配置 = 彻底全符号化的设计语义）；`1`/`true`/`on`（大小写
/// 不敏感）开启，供 difftest 重放等需要固定 RAM 竞技场的场景显式声明。
pub fn default_sym_ram_enabled() -> bool {
    let value = match std::env::var("ISLA_RISCV_DEFAULT_SYM_RAM") {
        Ok(value) => value,
        Err(std::env::VarError::NotPresent) => return false,
        Err(err) => panic!("读取环境变量 ISLA_RISCV_DEFAULT_SYM_RAM 失败: {}", err),
    };
    match value.to_ascii_lowercase().as_str() {
        "1" | "true" | "on" => true,
        "0" | "false" | "off" => false,
        other => panic!("ISLA_RISCV_DEFAULT_SYM_RAM 仅支持 1/true/on 或 0/false/off，实际为 '{}'", other),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::isarch::target::RV64;
    use isla_lib::bitvector::b64::B64;
    use isla_lib::config::{PageTableConfig, PageTableMode, PageTablePreset, ProtectedRange};
    use isla_lib::memory::Region;

    fn has_concrete_region(memory: &Memory<B64>, base: u64, size: u64) -> bool {
        memory.regions().iter().any(
            |region| matches!(region, Region::Concrete(range, _) if range.start == base && range.end == base + size),
        )
    }

    fn has_symbolic_region(memory: &Memory<B64>, base: u64, size: u64) -> bool {
        memory
            .regions()
            .iter()
            .any(|region| matches!(region, Region::Symbolic(range) if range.start == base && range.end == base + size))
    }

    fn has_excluded_region(memory: &Memory<B64>, base: u64, size: u64) -> bool {
        memory
            .regions()
            .iter()
            .any(|region| matches!(region, Region::Excluded(range) if range.start == base && range.end == base + size))
    }

    /// W9 判死区域构造：`add_excluded_region` 产出 `Region::Excluded`，与
    /// concrete/symbolic 区域并存。
    #[test]
    fn excluded_region_builds_and_coexists() {
        let rv64: RV64<B64> = RV64::default();
        let memory = MemoryBuilder::<B64>::new(&rv64)
            .add_concrete_region(0x8000_0000, 0x1000)
            .add_symbolic_region(0x9000_0000, 0x2000)
            .add_excluded_region(0x0200_0000, 0x0200_0000)
            .set_clint_enabled(false)
            .build()
            .unwrap();

        assert_eq!(memory.regions().len(), 3);
        assert!(has_concrete_region(&memory, 0x8000_0000, 0x1000));
        assert!(has_symbolic_region(&memory, 0x9000_0000, 0x2000));
        assert!(has_excluded_region(&memory, 0x0200_0000, 0x0200_0000), "应构造出 MMIO 判死区域");
        assert_eq!(memory.region_name_at(0x0300_0000), "excluded", "判死区域命名应可用于事件标注");
    }

    /// 判死区域与其他区域重叠属于配置错误，构建直接失败（与既有重叠校验一致）。
    #[test]
    fn excluded_region_overlap_rejected() {
        let rv64: RV64<B64> = RV64::default();
        let result = MemoryBuilder::<B64>::new(&rv64)
            .add_symbolic_region(0x1000, 0x2000)
            .add_excluded_region(0x2000, 0x1000)
            .set_clint_enabled(false)
            .build();
        assert!(result.is_err(), "判死区域与 symbolic 区域重叠应构建失败");
    }

    /// 默认 CLINT 与判死段重叠同样拒绝——演示配置需显式 clint_enabled=false
    /// 或收缩判死段边界（见 configs/riscv64_difftest_mem_excluded.toml）。
    #[test]
    fn excluded_region_overlap_clint_rejected() {
        let rv64: RV64<B64> = RV64::default();
        // CLINT 默认 [0x2000000,0x20c0000) 落在判死段 [0x02000000,0x04000000) 内
        let result = MemoryBuilder::<B64>::new(&rv64).add_excluded_region(0x0200_0000, 0x0200_0000).build();
        assert!(result.is_err(), "判死段包住默认 CLINT 应构建失败");
    }

    #[test]
    fn new_builder_defaults() {
        let rv64: RV64<B64> = RV64::default();
        let builder: MemoryBuilder<B64> = MemoryBuilder::new(&rv64);
        let memory = builder.build().unwrap();

        assert_eq!(memory.regions().len(), 1);
        assert!(has_concrete_region(&memory, 0x2000000, 0xc0000));
    }

    /// W6 语义调整：零配置（默认 difftest 配置只有 CLINT concrete 区域）不再
    /// 隐式补默认符号 RAM——数组模型下地址与数组内容全部符号化，可满足性不
    /// 依赖区域。W5 版本曾默认补 RAM 救活访存路径，当时的写侧空 OR 链折叠
    /// bug（空 Symbolic 区域集被折成 `false` 判死写路径）已在 memory_model
    /// 的 `region_address_constraint` 修复，因此默认关闭改为显式开关。
    #[test]
    fn ensure_solve_state_memory_默认不补ram尊重零配置() {
        let rv64: RV64<B64> = RV64::default();
        let memory = MemoryBuilder::<B64>::new(&rv64).build().unwrap();
        assert!(!memory.regions().iter().any(|r| matches!(r, Region::Symbolic(_))), "默认配置内存应无符号区域");

        let memory = ensure_solve_state_memory(memory, false);
        assert!(
            !memory.regions().iter().any(|r| matches!(r, Region::Symbolic(_))),
            "默认（开关关闭）不应隐式补符号 RAM"
        );
        assert!(has_concrete_region(&memory, 0x2000000, 0xc0000), "原有 CLINT concrete 区域保留");
    }

    /// 开关打开且未配置符号区域时补与 riscv64_difftest_mem.toml 的 sym_ram
    /// 对齐的默认 RAM（difftest 重放兜底，经 ISLA_RISCV_DEFAULT_SYM_RAM=1 开启）。
    #[test]
    fn ensure_solve_state_memory_开关打开时补默认ram() {
        let rv64: RV64<B64> = RV64::default();
        let memory = MemoryBuilder::<B64>::new(&rv64).build().unwrap();

        let memory = ensure_solve_state_memory(memory, true);
        assert!(has_symbolic_region(&memory, 0x8000_0000, 0x1000_0000), "开关打开时应补默认符号 RAM");
        assert!(has_concrete_region(&memory, 0x2000000, 0xc0000), "原有 CLINT concrete 区域保留");
    }

    /// 配置已声明符号区域（如 riscv64_difftest_mem.toml 的 sym_ram）时装配应保持不变
    /// （无论开关状态，都不重复追加）。
    #[test]
    fn ensure_solve_state_memory_已有符号区域时不变() {
        let rv64: RV64<B64> = RV64::default();
        let memory = MemoryBuilder::<B64>::new(&rv64).add_symbolic_region(0x9000_0000, 0x2000).build().unwrap();

        let memory = ensure_solve_state_memory(memory, true);
        assert_eq!(memory.regions().len(), 2, "不应重复追加区域");
        assert!(has_symbolic_region(&memory, 0x9000_0000, 0x2000));
    }

    #[test]
    fn builder_chaining() {
        let rv64: RV64<B64> = RV64::default();
        let builder: MemoryBuilder<B64> = MemoryBuilder::new(&rv64)
            .add_concrete_region(0x8000_0000, 0x1000)
            .add_symbolic_region(0x9000_0000, 0x2000)
            .set_clint_enabled(false);
        let memory = builder.build().unwrap();

        assert_eq!(memory.regions().len(), 2);
        assert!(has_concrete_region(&memory, 0x8000_0000, 0x1000));
        assert!(has_symbolic_region(&memory, 0x9000_0000, 0x2000));
    }

    #[test]
    fn identity_mapping_creates_config() {
        let rv64: RV64<B64> = RV64::default();
        let builder: MemoryBuilder<B64> =
            MemoryBuilder::new(&rv64).with_identity_mapping(0x1_0000).unwrap().set_clint_enabled(false);
        let memory = builder.build().unwrap();

        assert_eq!(memory.regions().len(), 1);
        assert!(has_concrete_region(&memory, 0x1_0000, 2 * rv64.page_table_size()));
    }

    #[test]
    fn offset_mapping_config() {
        let rv64: RV64<B64> = RV64::default();
        let builder: MemoryBuilder<B64> =
            MemoryBuilder::new(&rv64).with_offset_mapping(0x1_0000, 0x1000_0000).unwrap().set_clint_enabled(false);
        let memory = builder.build().unwrap();

        assert_eq!(memory.regions().len(), 1);
        assert!(has_concrete_region(&memory, 0x1_0000, 2 * rv64.page_table_size()));
    }

    #[test]
    fn symbolic_mapping_config() {
        let rv64: RV64<B64> = RV64::default();
        let builder: MemoryBuilder<B64> =
            MemoryBuilder::new(&rv64).with_symbolic_mapping(0x1_0000).unwrap().set_clint_enabled(false);
        let memory = builder.build().unwrap();

        assert_eq!(memory.regions().len(), 1);
        assert!(has_symbolic_region(&memory, 0x1_0000, 2 * rv64.page_table_size()));
    }

    #[test]
    fn overlapping_regions_rejected() {
        let rv64: RV64<B64> = RV64::default();
        let result = MemoryBuilder::<B64>::new(&rv64)
            .add_concrete_region(0x1000, 0x2000)
            .add_concrete_region(0x2000, 0x1000)
            .set_clint_enabled(false)
            .build();

        assert!(result.is_err());
    }

    #[test]
    fn adjacent_regions_allowed() {
        let rv64: RV64<B64> = RV64::default();
        let memory = MemoryBuilder::<B64>::new(&rv64)
            .add_concrete_region(0x1000, 0x1000)
            .add_concrete_region(0x2000, 0x1000)
            .set_clint_enabled(false)
            .build()
            .unwrap();

        assert!(has_concrete_region(&memory, 0x1000, 0x1000));
        assert!(has_concrete_region(&memory, 0x2000, 0x1000));
    }

    #[test]
    fn protected_mapping_with_ranges() {
        let protected = vec![ProtectedRange { base: 0x8000_0000, size: 0x1000, flags: "rwx".to_string() }];
        let rv64: RV64<B64> = RV64::default();
        let builder: MemoryBuilder<B64> = MemoryBuilder::new(&rv64)
            .with_protected_mapping(0x1_0000, protected.clone())
            .unwrap()
            .set_clint_enabled(false);
        let memory = builder.build().unwrap();

        assert_eq!(protected.len(), 1);
        assert!(has_concrete_region(&memory, 0x1_0000, 2 * rv64.page_table_size()));
    }

    #[test]
    fn clint_disabled() {
        let rv64: RV64<B64> = RV64::default();
        let memory = MemoryBuilder::<B64>::new(&rv64).set_clint_enabled(false).build().unwrap();

        assert!(memory.regions().is_empty());
    }

    #[test]
    fn clint_custom_params() {
        let rv64: RV64<B64> = RV64::default();
        let memory = MemoryBuilder::<B64>::new(&rv64).clint_with_params(true, 0x3000_0000, 0x10000).build().unwrap();

        assert_eq!(memory.regions().len(), 1);
        assert!(has_concrete_region(&memory, 0x3000_0000, 0x10000));
    }

    #[test]
    fn pte_flags_in_page_table() {
        let rv64: RV64<B64> = RV64::default();
        let pte = RiscvPte::new(
            rv64.ppn_from_pa(0x8000_0000),
            rv64.pte_v() | rv64.pte_r() | rv64.pte_w() | rv64.pte_x() | rv64.pte_a() | rv64.pte_d() | rv64.pte_u(),
        );

        assert!(pte.is_valid());
        assert!(pte.has_read());
        assert!(pte.has_write());
        assert!(pte.has_execute());
    }

    #[test]
    fn sv39_table_size_is_two_pages() {
        let rv64: RV64<B64> = RV64::default();
        let config = PageTableConfig {
            mode: PageTableMode::SV39,
            preset: PageTablePreset::Identity,
            base: 0x1_0000,
            page_size: 4096,
            offset: None,
            protected_ranges: None,
        };

        let builder = MemoryBuilder::<B64>::new(&rv64);
        assert_eq!(builder.page_table_size(&config), 2 * rv64.page_table_size());
        assert_eq!(2 * rv64.page_table_size(), 8192);
    }

    #[test]
    fn sv48_table_size_is_three_pages() {
        let rv64: RV64<B64> = RV64::default();
        let config = PageTableConfig {
            mode: PageTableMode::SV48,
            preset: PageTablePreset::Identity,
            base: 0x1_0000,
            page_size: 4096,
            offset: None,
            protected_ranges: None,
        };

        let builder = MemoryBuilder::<B64>::new(&rv64);
        assert_eq!(builder.page_table_size(&config), 3 * rv64.page_table_size());
        assert_eq!(3 * rv64.page_table_size(), 12288);
    }

    #[test]
    fn build_identity_mapping_includes_page_table() {
        let rv64: RV64<B64> = RV64::default();
        let builder: MemoryBuilder<B64> =
            MemoryBuilder::new(&rv64).with_identity_mapping(0x1_0000).unwrap().set_clint_enabled(false);
        let memory = builder.build().unwrap();

        assert!(has_concrete_region(&memory, 0x1_0000, 2 * rv64.page_table_size()));
        assert_eq!(memory.region_name_at(0x1_0000), "concrete");
    }
}
