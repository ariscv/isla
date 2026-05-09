use std::collections::HashMap;
use std::ops::Range;

use crate::bitvector::BV;
use crate::config::{ISAConfig, MemoryRegionType, PageTableConfig, PageTableMode, PageTablePreset, ProtectedRange};
use crate::memory::{Memory, Region};
use crate::target::{ppn_from_pa, RiscvPte, RV64};

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
        }
    }

    fn populate_offset_mapping(config: &PageTableConfig, memory: &mut Memory<B>) -> Result<(), String> {
        Self::validate_page_table_config(config)?;
        let offset = config.offset.ok_or_else(|| "offset mapping requires offset field".to_string())?;
        if offset % (1 << 21) != 0 {
            return Err(format!(
                "offset 0x{:x} must be 2MiB aligned for megapage mapping",
                offset
            ));
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
        }
    }

    fn populate_protected_mapping(config: &PageTableConfig, memory: &mut Memory<B>) -> Result<(), String> {
        Self::validate_page_table_config(config)?;
        match config.mode {
            PageTableMode::SV39 => Self::populate_sv39_tables(config, |vpn1| {
                let va = vpn1 << 21;
                let flags = Self::flags_for_va(config, va)?;
                Ok(RiscvPte::new(ppn_from_pa(va), flags))
            })
            .map(|region| memory.add_region(region)),
            PageTableMode::SV48 => Self::populate_sv48_tables(config, |vpn1| {
                let va = vpn1 << 21;
                let flags = Self::flags_for_va(config, va)?;
                Ok(RiscvPte::new(ppn_from_pa(va), flags))
            })
            .map(|region| memory.add_region(region)),
        }
    }

    // TODO(s symbolic): currently identical to identity mapping. True symbolic PTEs need a Solver
    // at build time, which MemoryBuilder doesn't have. Revisit when executor supports post-build
    // PTE symbolization.
    fn populate_symbolic_mapping(config: &PageTableConfig, memory: &mut Memory<B>) -> Result<(), String> {
        eprintln!("Warning: page table preset 'symbolic' currently behaves as 'identity' — symbolic PTEs not yet implemented");
        Self::populate_identity_mapping(config, memory)
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
        let l2_pte = RiscvPte::new(ppn_from_pa(l1_base), RV64::PTE_V);
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

        Ok(Region::Concrete(
            config.base..config.base + Self::sv39_table_size(),
            pte_bytes,
        ))
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
        let l1_base = l2_base
            .checked_add(RV64::PAGE_TABLE_SIZE)
            .ok_or_else(|| "SV48 L1 table address overflows".to_string())?;

        let mut pte_bytes = HashMap::new();

        // L3 (root) table: entry[0] = non-leaf pointer to L2, rest invalid (zero)
        let l3_pte = RiscvPte::new(ppn_from_pa(l2_base), RV64::PTE_V);
        for (i, &byte) in l3_pte.to_bytes().iter().enumerate() {
            pte_bytes.insert(config.base + i as u64, byte);
        }

        // L2 table: entry[0] = non-leaf pointer to L1, rest invalid (zero)
        let l2_pte = RiscvPte::new(ppn_from_pa(l1_base), RV64::PTE_V);
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

        Ok(Region::Concrete(
            config.base..config.base + Self::sv48_table_size(),
            pte_bytes,
        ))
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
        RiscvPte::new(ppn_from_pa(pa), Self::default_leaf_flags())
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
        }
        Ok(())
    }

    fn page_table_size(config: &PageTableConfig) -> u64 {
        match config.mode {
            PageTableMode::SV39 => Self::sv39_table_size(),
            PageTableMode::SV48 => Self::sv48_table_size(),
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
