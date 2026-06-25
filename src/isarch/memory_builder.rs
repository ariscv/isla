use std::collections::HashMap;
use std::ops::Range;

use super::target::{RiscvPte, RISCV};
use isla_lib::bitvector::BV;
use isla_lib::config::{ISAConfig, MemoryRegionType, PageTableConfig, PageTableMode, PageTablePreset, ProtectedRange};
use isla_lib::memory::{Memory, Region};

enum PendingRegion {
    Concrete { base: u64, size: u64 },
    Symbolic { base: u64, size: u64 },
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
                    _ => return Err("unsupported memory region type".to_string()),
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

        Ok(Region::Concrete(config.base..config.base + self.sv39_table_size(), pte_bytes))
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

        Ok(Region::Concrete(config.base..config.base + self.sv48_table_size(), pte_bytes))
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

    #[test]
    fn new_builder_defaults() {
        let rv64: RV64<B64> = RV64::default();
        let builder: MemoryBuilder<B64> = MemoryBuilder::new(&rv64);
        let memory = builder.build().unwrap();

        assert_eq!(memory.regions().len(), 1);
        assert!(has_concrete_region(&memory, 0x2000000, 0xc0000));
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
