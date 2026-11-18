//! 只恢复实际访存路径上的 PTE 地址；期望结果直接取样本，不重做模型裁决。
use super::*;
use crate::isarch::target::RiscvPte;
use isla_lib::executor::samples::MemoryCell;

#[derive(Debug, Deserialize)]
pub struct Platform {
    pub regions: Vec<Region>,
    pub harness: Harness,
    pub isa: PagingIsa,
    pub isla: Value,
}

#[derive(Debug, Deserialize)]
pub struct Region {
    pub base: u64,
    pub size: u64,
    pub kind: String,
}

#[derive(Debug, Deserialize)]
pub struct Harness {
    pub reserved: [u64; 2],
}

#[derive(Debug, Deserialize)]
pub struct PagingIsa {
    pub svrsw60t59b: bool,
    pub standard_paging: bool,
}

impl Platform {
    pub(super) fn contains(&self, kind: &str, address: u64) -> bool {
        self.regions.iter().any(|region| {
            region.kind == kind
                && region.base <= address
                && u128::from(address) + 8 <= u128::from(region.base) + u128::from(region.size)
        })
    }

    pub(super) fn ram(&self, address: u64) -> bool {
        address >= 0x80100000 && address < 1 << 43 && self.contains("ram", address)
    }
}

pub(super) fn bits(value: &Value, width: usize) -> Result<u64, String> {
    let text = value["bits"].as_str().ok_or("缺少具体位串")?;
    if text.len() != width || !text.bytes().all(|b| b == b'0' || b == b'1') {
        return Err(format!("要求 {width} 位具体位串"));
    }
    Ok(u64::from_str_radix(text, 2).unwrap())
}

fn integer(value: &Value) -> Result<u64, String> {
    match value.as_str() {
        Some(text) if text.starts_with("0x") => u64::from_str_radix(&text[2..], 16).map_err(|e| e.to_string()),
        Some(text) => text.parse().map_err(|e: std::num::ParseIntError| e.to_string()),
        None => value.as_u64().ok_or_else(|| "要求无符号整数或整数字符串".into()),
    }
}

fn memory(cells: &[MemoryCell]) -> Result<BTreeMap<u64, Option<u8>>, String> {
    let mut memory = BTreeMap::new();
    for cell in cells {
        if cell.bytes != 1 || memory.insert(cell.address, cell.value).is_some() {
            return Err("只接受无重复地址的 samples v1 字节内存".into());
        }
    }
    Ok(memory)
}

fn read_word(memory: &BTreeMap<u64, Option<u8>>, address: u64) -> Result<u64, String> {
    let mut bytes = [0; 8];
    for (offset, byte) in bytes.iter_mut().enumerate() {
        *byte = memory
            .get(&(address + offset as u64))
            .copied()
            .flatten()
            .ok_or_else(|| format!("缺少已知的内存字节：{:#x}", address + offset as u64))?;
    }
    Ok(u64::from_le_bytes(bytes))
}

fn instruction(sample: &Sample) -> Result<Instruction, String> {
    let (access, offset, base, register, width, unsigned) = if let Some(ctor) = sample.pre_registers.get("$instruction")
    {
        let access = match ctor["ctor"].as_str() {
            Some("LOAD") => Access::Load,
            Some("STORE") => Access::Store,
            _ => return Err("仅支持 LOAD(ld)/STORE(sd) 构造子".into()),
        };
        let prefix = match access {
            Access::Load => "tuple#%bv12_%bv5_%bv5_%bool_%i64",
            Access::Store => "tuple#%bv12_%bv5_%bv5_%i64",
        };
        let fields = ctor["value"]["struct"].as_object().ok_or("指令构造子必须含结构体")?;
        let field = |index| fields.get(&format!("{prefix}{index}")).ok_or("指令构造子缺少字段");
        let width_index = if access == Access::Load { 4 } else { 3 };
        if fields.len() != width_index + 1 {
            return Err("指令构造子字段数量错误".into());
        }
        let value = field(width_index)?;
        let width = if value.get("i64").is_some() { integer(&value["i64"])? } else { bits(value, 64)? };
        if ![1, 2, 4, 8].contains(&width) {
            return Err("非硬件编码宽度".into());
        }
        let unsigned = access == Access::Load && field(3)?["bool"].as_bool().ok_or("加载符号位必须具体")?;
        if width == 8 && unsigned {
            return Err("RV64没有8字节无符号加载编码".into());
        }
        let immediate = bits(field(0)?, 12)? as i16;
        let first = bits(field(1)?, 5)? as u8;
        let second = bits(field(2)?, 5)? as u8;
        (
            access,
            (immediate << 4) >> 4,
            if access == Access::Load { first } else { second },
            if access == Access::Load { second } else { first },
            width,
            unsigned,
        )
    } else {
        // 展示字符串是无构造子的历史协议；构造子损坏时绝不改用此来源。
        let text = sample.isa_state.get("$instruction").ok_or("缺少被测指令")?;
        let (mnemonic, operands) = text.split_once(char::is_whitespace).ok_or("缺少指令操作数")?;
        let (register, address) = operands.trim_start().split_once(',').ok_or("缺少操作数分隔符")?;
        let access = match mnemonic {
            "ld" => Access::Load,
            "sd" => Access::Store,
            _ => return Err("仅支持 ld/sd 指令".into()),
        };
        let parse_register = |text: &str| -> Result<u8, String> {
            let number: u8 = text
                .strip_prefix('x')
                .ok_or("寄存器必须为 xN")?
                .parse()
                .map_err(|e: std::num::ParseIntError| e.to_string())?;
            if number > 31 {
                return Err("寄存器编号超界".into());
            }
            Ok(number)
        };
        let register = parse_register(register)?;
        let (immediate, base) = address.trim_start().split_once('(').ok_or("缺少基址寄存器")?;
        let base = parse_register(base.strip_suffix(')').ok_or("缺少右括号")?)?;
        let (negative, magnitude) = match immediate.strip_prefix('-') {
            Some(text) => (true, text),
            None => (false, immediate.strip_prefix('+').unwrap_or(immediate)),
        };
        let magnitude = integer(&Value::String(magnitude.into()))?;
        let offset = if negative { -i128::from(magnitude) } else { i128::from(magnitude) };
        if !(-2048..=2047).contains(&offset) {
            return Err("ld/sd 立即数超界".into());
        }
        (access, offset as i16, base, register, 8, false)
    };
    let imm = u32::from(offset as u16) & 4095;
    let word = (u32::from(base) << 15)
        | ((width.trailing_zeros() + if unsigned { 4 } else { 0 }) << 12)
        | match access {
            Access::Load => (imm << 20) | (u32::from(register) << 7) | 3,
            Access::Store => ((imm >> 5) << 25) | (u32::from(register) << 20) | ((imm & 31) << 7) | 0x23,
        };
    let mnemonic = match (access, width, unsigned) {
        (Access::Load, 1, false) => "lb",
        (Access::Load, 1, true) => "lbu",
        (Access::Load, 2, false) => "lh",
        (Access::Load, 2, true) => "lhu",
        (Access::Load, 4, false) => "lw",
        (Access::Load, 4, true) => "lwu",
        (Access::Load, 8, false) => "ld",
        (Access::Store, 1, _) => "sb",
        (Access::Store, 2, _) => "sh",
        (Access::Store, 4, _) => "sw",
        (Access::Store, 8, _) => "sd",
        _ => unreachable!(),
    };
    Ok(Instruction {
        access,
        offset,
        base,
        register,
        word,
        width,
        unsigned,
        assembly: format!("{mnemonic} x{register}, {offset}(x{base})"),
    })
}

pub(super) fn prepare(sample: &Sample, platform: &Platform, mode: EntryMode) -> Result<Generated, String> {
    if sample.schema_version != 1 || sample.truncated {
        return Err("要求完整的 samples v1 样本".into());
    }
    if platform.harness.reserved != [0x80000000, 0x80100000] {
        return Err("平台代码窗口必须为 [0x80000000, 0x80100000)".into());
    }
    let instruction = instruction(sample)?;
    let pre = &sample.pre_registers;
    let mut registers = BTreeMap::new();
    for index in 1..32 {
        let key = format!("x{index}");
        if let Some(value) = pre.get(&key) {
            registers.insert(key, bits(value, 64)?);
        }
    }
    let register_value = |values: &BTreeMap<String, Value>, index: u8| -> Result<u64, String> {
        if index == 0 {
            Ok(0)
        } else {
            bits(values.get(&format!("x{index}")).ok_or("缺少指令操作数寄存器")?, 64)
        }
    };
    let va = register_value(pre, instruction.base)?.wrapping_add(instruction.offset as u64);
    let satp = bits(pre.get("satp").ok_or("缺少 satp")?, 64)?;
    let levels = match satp >> 60 {
        8 => 3,
        9 => 4,
        _ => return Err("仅支持 Sv39/Sv48".into()),
    };
    let status = bits(&pre.get("mstatus").ok_or("缺少 mstatus")?["struct"]["bits"], 64)?;
    let privilege = pre.get("cur_privilege").ok_or("缺少当前特权级")?["enum"].as_str().ok_or("特权级必须为枚举")?;
    let privilege_bits = match privilege {
        "User" => 0,
        "Supervisor" => 1,
        _ => return Err("仅支持 U/S 前态".into()),
    };
    if mode == EntryMode::S && privilege != "Supervisor" {
        return Err("真 S 态入口要求 Supervisor 前态".into());
    }
    if status & (1 << 17) != 0 || bits(&pre.get("menvcfg").ok_or("缺少 menvcfg")?["struct"]["bits"], 64)? != 0 {
        return Err("入口要求 MPRV=0、menvcfg=0".into());
    }
    if status & (1u64 << 42) != 0 {
        return Err("当前陷阱观察器不支持MDT双重陷阱前态".into());
    }
    let tlb = pre.get("tlb").ok_or("缺少 TLB")?["vector"].as_array().ok_or("TLB 必须为向量")?;
    if tlb.iter().any(|entry| *entry != serde_json::json!({"ctor":"None<RTLB_Entry>","value":{"unit":true}})) {
        return Err("要求空 TLB".into());
    }
    let scenario = platform.isla.get("scenario").ok_or("平台缺少场景约束")?;
    if let Some(allowed) = scenario.get("privilege_domain") {
        if !allowed.as_array().ok_or("privilege_domain 必须为数组")?.contains(&Value::String(privilege.into())) {
            return Err("特权级不满足场景约束".into());
        }
    } else if privilege
        != scenario.get("privilege").map_or("Supervisor", |v| v.as_str().expect("平台特权级必须为字符串"))
    {
        return Err("特权级不满足场景约束".into());
    }
    if let Some(mask) = scenario.get("mstatus_mask") {
        if status & integer(mask)? != integer(&scenario["mstatus_value"])? {
            return Err("mstatus 不满足场景约束".into());
        }
    } else if let Some(value) = scenario.get("mstatus") {
        if status != integer(value)? {
            return Err("mstatus 不满足场景约束".into());
        }
    }
    for key in ["va", "va_values"] {
        if let Some(value) = scenario.get(key) {
            let values = match value.as_array() {
                Some(values) => values.clone(),
                None => vec![value.clone()],
            };
            if !values.iter().map(integer).collect::<Result<Vec<_>, _>>()?.contains(&va) {
                return Err("VA 不满足场景约束".into());
            }
        }
    }
    if let Some(domain) = scenario.get("va_domain") {
        let domain = domain.as_object().ok_or("VA 地址域必须为对象")?;
        if domain.keys().any(|key| !["base", "size", "mask", "value"].contains(&key.as_str()))
            || domain.contains_key("base") != domain.contains_key("size")
            || domain.contains_key("mask") != domain.contains_key("value")
        {
            return Err("VA 地址域字段不符".into());
        }
        if let Some(base) = domain.get("base") {
            let base = integer(base)?;
            let end = u128::from(base) + u128::from(integer(&domain["size"])?);
            if end > 1u128 << 64 || end <= u128::from(base) || va < base || u128::from(va) >= end {
                return Err("VA 超出场景地址域".into());
            }
        }
        if let Some(mask) = domain.get("mask") {
            let mask = integer(mask)?;
            let value = integer(&domain["value"])?;
            if value & !mask != 0 || va & mask != value {
                return Err("VA 不满足场景掩码".into());
            }
        }
    }
    for (key, value) in [("satp_modes", satp >> 60), ("instructions", u64::from(instruction.word))] {
        if let Some(values) = scenario.get(key) {
            if !values
                .as_array()
                .ok_or("场景列表必须为数组")?
                .iter()
                .map(integer)
                .collect::<Result<Vec<_>, _>>()?
                .contains(&value)
            {
                return Err(format!("{key} 不满足场景约束"));
            }
        }
    }
    if let Some(access) = scenario.get("access") {
        if *access != serde_json::to_value(instruction.access).unwrap() {
            return Err("指令不满足场景访问约束".into());
        }
    }
    let cause = match sample.result["ctor"].as_str() {
        Some("Retire_Success") if sample.result["value"] == serde_json::json!({"unit":true}) => 0,
        Some("Memory_Exception") => {
            let fields = &sample.result["value"]["struct"];
            if bits(&fields["tuple#%bv64_%union zExceptionType0"], 64)? != va {
                return Err("样本异常地址与有效地址不一致".into());
            }
            let exception = &fields["tuple#%bv64_%union zExceptionType1"];
            if exception["value"] != serde_json::json!({"unit":true}) {
                return Err("异常类型载荷必须为 unit".into());
            }
            match (instruction.access, exception["ctor"].as_str()) {
                (Access::Load, Some("E_Load_Page_Fault")) => 13,
                (Access::Load, Some("E_Load_Access_Fault")) => 5,
                (Access::Load, Some("E_Load_Addr_Align")) => 4,
                (Access::Store, Some("E_SAMO_Page_Fault")) => 15,
                (Access::Store, Some("E_SAMO_Access_Fault")) => 7,
                (Access::Store, Some("E_SAMO_Addr_Align")) => 6,
                _ => return Err("不支持此访存异常类型".into()),
            }
        }
        _ => return Err("不支持此样本结果".into()),
    };
    let expected = Expected {
        cause,
        tval: if cause == 0 { 0 } else { va },
        rd: if instruction.access == Access::Load {
            Some(register_value(&sample.post_registers, instruction.register)?)
        } else {
            None
        },
    };
    let memory = memory(&sample.pre_memory)?;
    let post = self::memory(&sample.post_memory)?;
    if memory.keys().ne(post.keys())
        || post.values().any(Option::is_none)
        || memory.keys().any(|address| !platform.ram(address & !7))
    {
        return Err("前后内存地址集合必须一致且全部位于可重放 DRAM，后态必须已知".into());
    }
    let mut filled = memory
        .iter()
        .map(|(address, value)| {
            (
                *address,
                Some(match value {
                    Some(value) => *value,
                    None => post[address].unwrap() ^ 255,
                }),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut expected_memory = post;
    let mut pte_addresses = Vec::new();
    let va_bits = 12 + 9 * levels;
    let canonical = (((va << (64 - va_bits)) as i64) >> (64 - va_bits)) as u64;
    let root = (satp & ((1 << 44) - 1)) << 12;
    if va == canonical && va & (instruction.width - 1) == 0 {
        let mut table = root;
        for level in (0..levels).rev() {
            let address = table + ((va >> (12 + 9 * level)) & 511) * 8;
            if (0..8).all(|i| !memory.contains_key(&(address + i)))
                && platform.contains("hole", address)
                && matches!(cause, 5 | 7)
            {
                break;
            }
            let pte = RiscvPte { bits: read_word(&memory, address)? };
            pte_addresses.push(address);
            let decoy = (address & !0xfff) | ((address + 8) & 0xfff);
            if platform.ram(decoy) && (0..8).all(|i| !memory.contains_key(&(decoy + i))) {
                for (i, byte) in 0xa55aa55aa55aa55au64.to_le_bytes().iter().enumerate() {
                    filled.insert(decoy + i as u64, Some(*byte));
                    expected_memory.insert(decoy + i as u64, Some(*byte));
                }
            }
            let nonleaf = !(pte.has_read() || pte.has_write() || pte.has_execute());
            let extension_invalid =
                pte.bits & (0x1f << 54 | 3 << 61) != 0 || (!platform.isa.svrsw60t59b && pte.bits & (3 << 59) != 0);
            let n = pte.bits >> 63 != 0;
            let invalid = !pte.is_valid()
                || (pte.has_write() && !pte.has_read())
                || extension_invalid
                || if platform.isa.standard_paging {
                    (nonleaf && pte.bits & (0xd0 | 1 << 63) != 0) || (n && (level != 0 || pte.ppn() & 15 != 8))
                } else {
                    n
                };
            if !platform.isa.standard_paging && nonleaf && pte.bits & 0xd0 != 0 {
                return Err("旧平台不接受指针 U/A/D 非零".into());
            }
            if !platform.isa.standard_paging && pte.is_valid() && pte.ppn() >= 1 << 36 && matches!(cause, 13 | 15) {
                return Err("旧平台高 PPN 与页异常优先级尚未签收".into());
            }
            if invalid || !nonleaf || level == 0 {
                break;
            }
            table = pte.ppn() << 12;
        }
    }
    let addresses = filled.keys().map(|address| address & !7).collect::<BTreeSet<_>>();
    // 模型未读取的同字节槽以零初始化并检查保持；已记录的字节不改变。
    for address in &addresses {
        for offset in 0..8 {
            filled.entry(address + offset).or_insert(Some(0));
            expected_memory.entry(address + offset).or_insert(Some(0));
        }
    }
    let mut writes = addresses
        .into_iter()
        .map(|address| {
            Ok(Word {
                address,
                value: read_word(&filled, address)?,
                expected_value: read_word(&expected_memory, address)?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    if mode == EntryMode::S {
        // 取指 VA=0x80000000。Sv48 复用样本的高层指针；绝不覆盖样本或诱饵。
        let mut table = root;
        for level in (2..levels).rev() {
            let address = table + ((0x80000000u64 >> (12 + 9 * level)) & 511) * 8;
            if level == 2 {
                if writes.iter().any(|word| word.address == address) {
                    return Err("S 态取指映射与样本或诱饵重叠".into());
                }
                let value = RiscvPte::new(0x80000000 >> 12, 0xcb).bits;
                if !platform.ram(address) {
                    return Err("S 态取指页表不在 DRAM".into());
                }
                writes.push(Word { address, value, expected_value: value });
            } else if let Some(word) = writes.iter().find(|word| word.address == address) {
                let pte = RiscvPte { bits: word.value };
                if !pte.is_valid() || pte.bits & (0xde | (0x3ff << 54)) != 0 {
                    return Err("S 态取指路径与样本高层 PTE 冲突".into());
                }
                table = pte.ppn() << 12;
            } else {
                let page = (0x80100000..1 << 43)
                    .step_by(4096)
                    .find(|page| platform.ram(*page) && !writes.iter().any(|word| word.address & !0xfff == *page))
                    .ok_or("没有空闲的取指页表页")?;
                let value = RiscvPte::new(page >> 12, 1).bits;
                if !platform.ram(address) {
                    return Err("S 态取指页表不在 DRAM".into());
                }
                writes.push(Word { address, value, expected_value: value });
                table = page;
            }
        }
        writes.sort_by_key(|word| word.address);
    }
    // 原输入是非虚拟U/S态；桥接设置MPRV或通过MRET进入时，不能激活原先不活动的MPV。
    let status = (status & !((3 << 11) | (1 << 3) | (1 << 17) | (1u64 << 39)))
        | (privilege_bits << 11)
        | if mode == EntryMode::Mprv { 1 << 17 } else { 0 };
    Ok(Generated {
        registers,
        satp,
        status,
        instruction,
        expected,
        writes,
        pte_addresses,
        assembly: String::new(),
        linker: String::new(),
    })
}

#[cfg(test)]
mod ablation_tests {
    use super::*;
    use serde_json::json;
    #[test]
    fn legal_widths_accept_bits_and_encode_funct3() {
        for access in [Access::Load, Access::Store] {
            for width in [1u64, 2, 4, 8] {
                for unsigned in [false, true] {
                    if unsigned && (access == Access::Store || width == 8) {
                        continue;
                    }
                    let mut sample = crate::isarch::fuzz::tests::example_sample();
                    let (ctor, prefix, index) = if access == Access::Load {
                        ("LOAD", "tuple#%bv12_%bv5_%bv5_%bool_%i64", 4)
                    } else {
                        ("STORE", "tuple#%bv12_%bv5_%bv5_%i64", 3)
                    };
                    let mut fields = serde_json::Map::new();
                    for (i, bits) in [(0, "000000000000"), (1, "00001"), (2, "00010")] {
                        fields.insert(format!("{prefix}{i}"), json!({"bits":bits}));
                    }
                    if access == Access::Load {
                        fields.insert(format!("{prefix}3"), json!({"bool":unsigned}));
                    }
                    fields.insert(format!("{prefix}{index}"), json!({"bits":format!("{width:064b}")}));
                    sample.pre_registers.insert("$instruction".into(), json!({"ctor":ctor,"value":{"struct":fields}}));
                    let decoded = instruction(&sample).unwrap();
                    assert_eq!((decoded.word >> 12) & 7, width.trailing_zeros() + if unsigned { 4 } else { 0 });
                }
            }
        }
    }
}

#[cfg(test)]
mod bridge_tests {
    use super::*;
    use serde_json::json;
    #[test]
    fn ablation_bridge_preserves_nonvirtual_effective_access() {
        let mut sample = crate::isarch::fuzz::tests::example_sample();
        let bits = |value: u64| json!({"bits":format!("{value:064b}")});
        let va = 1u64 << 63;
        let status = (1u64 << 39) | (1 << 18) | (1 << 19);
        sample.pre_registers.insert("satp".into(), bits(8u64 << 60));
        sample.pre_registers.insert("mstatus".into(), json!({"struct":{"bits":bits(status)}}));
        sample.pre_registers.insert("menvcfg".into(), json!({"struct":{"bits":bits(0)}}));
        sample.pre_registers.insert("cur_privilege".into(), json!({"enum":"Supervisor"}));
        sample.pre_registers.insert("tlb".into(), json!({"vector":[]}));
        sample.pre_registers.insert("x1".into(), bits(va));
        sample.pre_registers.insert("x2".into(), bits(0));
        sample.post_registers.insert("x2".into(), bits(0));
        sample.pre_registers.insert(
            "$instruction".into(),
            json!({"ctor":"LOAD","value":{"struct":{
                "tuple#%bv12_%bv5_%bv5_%bool_%i640":{"bits":"000000000000"},
                "tuple#%bv12_%bv5_%bv5_%bool_%i641":{"bits":"00001"},
                "tuple#%bv12_%bv5_%bv5_%bool_%i642":{"bits":"00010"},
                "tuple#%bv12_%bv5_%bv5_%bool_%i643":{"bool":false},
                "tuple#%bv12_%bv5_%bv5_%bool_%i644":bits(1)
            }}}),
        );
        sample.result = json!({"ctor":"Memory_Exception","value":{"struct":{
            "tuple#%bv64_%union zExceptionType0":bits(va),
            "tuple#%bv64_%union zExceptionType1":{"ctor":"E_Load_Page_Fault","value":{"unit":true}}
        }}});
        sample.pre_memory.clear();
        sample.post_memory.clear();
        let platform: Platform = serde_json::from_value(json!({
            "regions":[],"harness":{"reserved":[0x80000000u64,0x80100000u64]},
            "isa":{"svrsw60t59b":false,"standard_paging":true},
            "isla":{"scenario":{"privilege_domain":["Supervisor"],"satp_modes":[8]}}
        }))
        .unwrap();
        let generated = prepare(&sample, &platform, EntryMode::Mprv).unwrap();
        assert_eq!(generated.status & (1 << 39), 0, "MPRV桥接不能激活原先不活动的MPV");
        assert_eq!(generated.status & ((1 << 18) | (1 << 19)), status & ((1 << 18) | (1 << 19)));
        assert_eq!(sample.pre_registers["mstatus"]["struct"]["bits"], bits(status));
        sample.pre_registers.insert("mstatus".into(), json!({"struct":{"bits":bits(1u64<<42)}}));
        assert!(prepare(&sample, &platform, EntryMode::Mprv).is_err(), "M陷阱观察器不能接纳MDT双重陷阱前态");
    }
}
