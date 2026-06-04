use std::collections::HashMap;
use std::ops::Range;

use super::target::{RiscvPte, RISCV, RV64};
use isla_lib::bitvector::BV;
use isla_lib::config::{ISAConfig, MemoryRegionType, PageTableConfig, PageTableMode, PageTablePreset, ProtectedRange};
use isla_lib::memory::{Memory, Region};

enum PendingRegion {
    Concrete { base: u64, size: u64 },
    Symbolic { base: u64, size: u64 },
}

pub struct MemoryBuilder<B> {
    regions: Vec<PendingRegion>,
    page_table_config: Option<PageTableConfig>,
    clint_enabled: bool,
    clint_base: u64,
    clint_size: u64,
    _phantom: std::marker::PhantomData<B>,
}

impl<B: BV> MemoryBuilder<B> {
    pub fn new() -> Self {
        MemoryBuilder {
            regions: Vec::new(),
            page_table_config: None,
            clint_enabled: true,
            clint_base: 0x2000000,
            clint_size: 0xc0000,
            _phantom: std::marker::PhantomData,
        }
    }

    pub fn from_config(config: &ISAConfig<B>) -> Result<Self, String> {
        let mut builder = MemoryBuilder::new();
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

    pub fn build(self) -> Result<Memory<B>, String> {
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
            Self::validate_page_table_config(config)?;
            let pt_end = config
                .base
                .checked_add(Self::page_table_size(config))
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
                PageTablePreset::Identity => Self::populate_identity_mapping(config, &mut memory)?,
                PageTablePreset::Offset => Self::populate_offset_mapping(config, &mut memory)?,
                PageTablePreset::ProtectedLinear => Self::populate_protected_mapping(config, &mut memory)?,
                PageTablePreset::SymbolicMapping => Self::populate_symbolic_mapping(config, &mut memory)?,
                _ => return Err("unsupported page table preset".to_string()),
            }
        }

        Ok(memory)
    }

    fn populate_identity_mapping(config: &PageTableConfig, memory: &mut Memory<B>) -> Result<(), String> {
        Self::validate_page_table_config(config)?;
        match config.mode {
            PageTableMode::SV39 => Self::populate_sv39_tables(config, |vpn1| Ok(Self::default_leaf_pte(vpn1 << 21)))
                .map(|region| memory.add_region(region)),
            PageTableMode::SV48 => Self::populate_sv48_tables(config, |vpn1| Ok(Self::default_leaf_pte(vpn1 << 21)))
                .map(|region| memory.add_region(region)),
            _ => Err("unsupported page table mode".to_string()),
        }
    }

    fn populate_offset_mapping(config: &PageTableConfig, memory: &mut Memory<B>) -> Result<(), String> {
        Self::validate_page_table_config(config)?;
        let offset = config.offset.ok_or_else(|| "offset mapping requires offset field".to_string())?;
        if offset % (1 << 21) != 0 {
            return Err(format!("offset 0x{:x} must be 2MiB aligned for megapage mapping", offset));
        }
        match config.mode {
            PageTableMode::SV39 => Self::populate_sv39_tables(config, |vpn1| {
                let pa = (vpn1 << 21).wrapping_add(offset as u64);
                Ok(Self::default_leaf_pte(pa))
            })
            .map(|region| memory.add_region(region)),
            PageTableMode::SV48 => Self::populate_sv48_tables(config, |vpn1| {
                let pa = (vpn1 << 21).wrapping_add(offset as u64);
                Ok(Self::default_leaf_pte(pa))
            })
            .map(|region| memory.add_region(region)),
            _ => Err("unsupported page table mode".to_string()),
        }
    }

    fn populate_protected_mapping(config: &PageTableConfig, memory: &mut Memory<B>) -> Result<(), String> {
        Self::validate_page_table_config(config)?;
        match config.mode {
            PageTableMode::SV39 => Self::populate_sv39_tables(config, |vpn1| {
                let va = vpn1 << 21;
                let flags = Self::flags_for_va(config, va)?;
                Ok(RiscvPte::new(RV64.ppn_from_pa(va), flags))
            })
            .map(|region| memory.add_region(region)),
            PageTableMode::SV48 => Self::populate_sv48_tables(config, |vpn1| {
                let va = vpn1 << 21;
                let flags = Self::flags_for_va(config, va)?;
                Ok(RiscvPte::new(RV64.ppn_from_pa(va), flags))
            })
            .map(|region| memory.add_region(region)),
            _ => Err("unsupported page table mode".to_string()),
        }
    }

    fn populate_symbolic_mapping(config: &PageTableConfig, memory: &mut Memory<B>) -> Result<(), String> {
        Self::validate_page_table_config(config)?;
        let pt_size = match config.mode {
            PageTableMode::SV39 => Self::sv39_table_size(),
            PageTableMode::SV48 => Self::sv48_table_size(),
            _ => return Err("unsupported page table mode".to_string()),
        };
        memory.add_symbolic_region(config.base..config.base + pt_size);
        Ok(())
    }

    /// SV39 two-level page table: L2(root) -> L1(megapage leaves, 2MiB each).
    /// Only L2 entry[0] is valid (non-leaf pointing to L1 table).
    /// L1 has 512 leaf PTEs covering virtual addresses 0..1GiB.
    fn populate_sv39_tables<F>(config: &PageTableConfig, mut pte_for_vpn1: F) -> Result<Region<B>, String>
    where
        F: FnMut(u64) -> Result<RiscvPte, String>,
    {
        let l1_base = config
            .base
            .checked_add(RV64::PAGE_TABLE_SIZE)
            .ok_or_else(|| "SV39 L1 table address overflows".to_string())?;

        let mut pte_bytes = HashMap::new();

        // L2 (root) table: entry[0] = non-leaf pointer to L1, rest invalid (zero)
        let l2_pte = RiscvPte::new(RV64.ppn_from_pa(l1_base), RV64::PTE_V);
        for (i, &byte) in l2_pte.to_bytes().iter().enumerate() {
            pte_bytes.insert(config.base + i as u64, byte);
        }

        // L1 table: 512 leaf PTEs, each mapping a 2MiB megapage
        for vpn1 in 0..RV64::PTES_PER_LEVEL {
            let bytes = pte_for_vpn1(vpn1)?.to_bytes();
            let addr = l1_base + vpn1 * RV64::PTE_SIZE;
            for (i, &byte) in bytes.iter().enumerate() {
                pte_bytes.insert(addr + i as u64, byte);
            }
        }

        Ok(Region::Concrete(config.base..config.base + Self::sv39_table_size(), pte_bytes))
    }

    /// SV48 three-level page table: L3(root) -> L2 -> L1(megapage leaves, 2MiB each).
    /// L3 entry[0] -> L2 table, L2 entry[0] -> L1 table.
    /// L1 has 512 leaf PTEs covering virtual addresses 0..1GiB.
    fn populate_sv48_tables<F>(config: &PageTableConfig, mut pte_for_vpn1: F) -> Result<Region<B>, String>
    where
        F: FnMut(u64) -> Result<RiscvPte, String>,
    {
        let l2_base = config
            .base
            .checked_add(RV64::PAGE_TABLE_SIZE)
            .ok_or_else(|| "SV48 L2 table address overflows".to_string())?;
        let l1_base =
            l2_base.checked_add(RV64::PAGE_TABLE_SIZE).ok_or_else(|| "SV48 L1 table address overflows".to_string())?;

        let mut pte_bytes = HashMap::new();

        // L3 (root) table: entry[0] = non-leaf pointer to L2, rest invalid (zero)
        let l3_pte = RiscvPte::new(RV64.ppn_from_pa(l2_base), RV64::PTE_V);
        for (i, &byte) in l3_pte.to_bytes().iter().enumerate() {
            pte_bytes.insert(config.base + i as u64, byte);
        }

        // L2 table: entry[0] = non-leaf pointer to L1, rest invalid (zero)
        let l2_pte = RiscvPte::new(RV64.ppn_from_pa(l1_base), RV64::PTE_V);
        for (i, &byte) in l2_pte.to_bytes().iter().enumerate() {
            pte_bytes.insert(l2_base + i as u64, byte);
        }

        // L1 table: 512 leaf PTEs, each mapping a 2MiB megapage
        for vpn1 in 0..RV64::PTES_PER_LEVEL {
            let bytes = pte_for_vpn1(vpn1)?.to_bytes();
            let addr = l1_base + vpn1 * RV64::PTE_SIZE;
            for (i, &byte) in bytes.iter().enumerate() {
                pte_bytes.insert(addr + i as u64, byte);
            }
        }

        Ok(Region::Concrete(config.base..config.base + Self::sv48_table_size(), pte_bytes))
    }

    fn flags_for_va(config: &PageTableConfig, va: u64) -> Result<u64, String> {
        if let Some(ref ranges) = config.protected_ranges {
            for range in ranges {
                let end = range.base.checked_add(range.size).ok_or_else(|| {
                    format!("protected range at 0x{:x} with size 0x{:x} overflows", range.base, range.size)
                })?;
                let page_end = va + Self::l1_megapage_size();
                if va < end && page_end > range.base {
                    return Self::parse_pte_flags(&range.flags);
                }
            }
        }

        Ok(Self::default_leaf_flags())
    }

    fn parse_pte_flags(flags: &str) -> Result<u64, String> {
        let mut pte_flags = RV64::PTE_V | RV64::PTE_A | RV64::PTE_D;
        for flag in flags.chars() {
            match flag {
                'r' => pte_flags |= RV64::PTE_R,
                'w' => pte_flags |= RV64::PTE_W,
                'x' => pte_flags |= RV64::PTE_X,
                'u' => pte_flags |= RV64::PTE_U,
                _ => return Err(format!("unknown protected range PTE flag '{}'", flag)),
            }
        }
        if pte_flags & RV64::PTE_W != 0 && pte_flags & RV64::PTE_R == 0 {
            return Err("PTE flags 'w' requires 'r' (W=1,R=0 is reserved in RISC-V)".to_string());
        }
        Ok(pte_flags)
    }

    fn default_leaf_pte(pa: u64) -> RiscvPte {
        RiscvPte::new(RV64.ppn_from_pa(pa), Self::default_leaf_flags())
    }

    fn default_leaf_flags() -> u64 {
        RV64::PTE_V | RV64::PTE_R | RV64::PTE_W | RV64::PTE_X | RV64::PTE_U | RV64::PTE_A | RV64::PTE_D
    }

    fn validate_page_table_config(config: &PageTableConfig) -> Result<(), String> {
        if config.base % 4096 != 0 {
            return Err(format!("page_table_config.base 0x{:x} must be 4KiB aligned", config.base));
        }
        match config.mode {
            PageTableMode::SV39 | PageTableMode::SV48 => {}
            _ => return Err("unsupported page table mode".to_string()),
        }
        Ok(())
    }

    fn page_table_size(config: &PageTableConfig) -> u64 {
        match config.mode {
            PageTableMode::SV39 => Self::sv39_table_size(),
            PageTableMode::SV48 => Self::sv48_table_size(),
            _ => 0,
        }
    }

    fn sv39_table_size() -> u64 {
        2 * RV64::PAGE_TABLE_SIZE
    }

    fn sv48_table_size() -> u64 {
        3 * RV64::PAGE_TABLE_SIZE
    }

    fn l1_megapage_size() -> u64 {
        1 << 21
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
        let builder: MemoryBuilder<B64> = MemoryBuilder::new();
        let memory = builder.build().unwrap();

        assert_eq!(memory.regions().len(), 1);
        assert!(has_concrete_region(&memory, 0x2000000, 0xc0000));
    }

    #[test]
    fn builder_chaining() {
        let builder: MemoryBuilder<B64> = MemoryBuilder::new()
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
        let builder: MemoryBuilder<B64> =
            MemoryBuilder::new().with_identity_mapping(0x1_0000).unwrap().set_clint_enabled(false);
        let memory = builder.build().unwrap();

        assert_eq!(memory.regions().len(), 1);
        assert!(has_concrete_region(&memory, 0x1_0000, 2 * RV64::PAGE_TABLE_SIZE));
    }

    #[test]
    fn offset_mapping_config() {
        let builder: MemoryBuilder<B64> =
            MemoryBuilder::new().with_offset_mapping(0x1_0000, 0x1000_0000).unwrap().set_clint_enabled(false);
        let memory = builder.build().unwrap();

        assert_eq!(memory.regions().len(), 1);
        assert!(has_concrete_region(&memory, 0x1_0000, 2 * RV64::PAGE_TABLE_SIZE));
    }

    #[test]
    fn symbolic_mapping_config() {
        let builder: MemoryBuilder<B64> =
            MemoryBuilder::new().with_symbolic_mapping(0x1_0000).unwrap().set_clint_enabled(false);
        let memory = builder.build().unwrap();

        assert_eq!(memory.regions().len(), 1);
        assert!(has_symbolic_region(&memory, 0x1_0000, 2 * RV64::PAGE_TABLE_SIZE));
    }

    #[test]
    fn overlapping_regions_rejected() {
        let result = MemoryBuilder::<B64>::new()
            .add_concrete_region(0x1000, 0x2000)
            .add_concrete_region(0x2000, 0x1000)
            .set_clint_enabled(false)
            .build();

        assert!(result.is_err());
    }

    #[test]
    fn adjacent_regions_allowed() {
        let memory = MemoryBuilder::<B64>::new()
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
        let builder: MemoryBuilder<B64> =
            MemoryBuilder::new().with_protected_mapping(0x1_0000, protected.clone()).unwrap().set_clint_enabled(false);
        let memory = builder.build().unwrap();

        assert_eq!(protected.len(), 1);
        assert!(has_concrete_region(&memory, 0x1_0000, 2 * RV64::PAGE_TABLE_SIZE));
    }

    #[test]
    fn clint_disabled() {
        let memory = MemoryBuilder::<B64>::new().set_clint_enabled(false).build().unwrap();

        assert!(memory.regions().is_empty());
    }

    #[test]
    fn clint_custom_params() {
        let memory = MemoryBuilder::<B64>::new().clint_with_params(true, 0x3000_0000, 0x10000).build().unwrap();

        assert_eq!(memory.regions().len(), 1);
        assert!(has_concrete_region(&memory, 0x3000_0000, 0x10000));
    }

    #[test]
    fn pte_flags_in_page_table() {
        let pte = RiscvPte::new(
            RV64.ppn_from_pa(0x8000_0000),
            RV64::PTE_V | RV64::PTE_R | RV64::PTE_W | RV64::PTE_X | RV64::PTE_A | RV64::PTE_D | RV64::PTE_U,
        );

        assert!(pte.is_valid());
        assert!(pte.has_read());
        assert!(pte.has_write());
        assert!(pte.has_execute());
    }

    #[test]
    fn sv39_table_size_is_two_pages() {
        let config = PageTableConfig {
            mode: PageTableMode::SV39,
            preset: PageTablePreset::Identity,
            base: 0x1_0000,
            page_size: 4096,
            offset: None,
            protected_ranges: None,
        };

        assert_eq!(MemoryBuilder::<B64>::page_table_size(&config), 2 * RV64::PAGE_TABLE_SIZE);
        assert_eq!(2 * RV64::PAGE_TABLE_SIZE, 8192);
    }

    #[test]
    fn sv48_table_size_is_three_pages() {
        let config = PageTableConfig {
            mode: PageTableMode::SV48,
            preset: PageTablePreset::Identity,
            base: 0x1_0000,
            page_size: 4096,
            offset: None,
            protected_ranges: None,
        };

        assert_eq!(MemoryBuilder::<B64>::page_table_size(&config), 3 * RV64::PAGE_TABLE_SIZE);
        assert_eq!(3 * RV64::PAGE_TABLE_SIZE, 12288);
    }

    #[test]
    fn build_identity_mapping_includes_page_table() {
        let builder: MemoryBuilder<B64> =
            MemoryBuilder::new().with_identity_mapping(0x1_0000).unwrap().set_clint_enabled(false);
        let memory = builder.build().unwrap();

        assert!(has_concrete_region(&memory, 0x1_0000, 2 * RV64::PAGE_TABLE_SIZE));
        assert_eq!(memory.region_name_at(0x1_0000), "concrete");
    }
}
