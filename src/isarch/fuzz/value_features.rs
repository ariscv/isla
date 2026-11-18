//! 从样本的 RV64 分页前态提取字段桶；只重建 PTE 读取，不判定指令结果。
use isla_lib::executor::samples::Sample;
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};

fn bits(value: &Value, width: usize) -> u64 {
    let text = value["bits"].as_str().expect("字段必须是具体位串");
    assert_eq!(text.len(), width, "字段位宽不符");
    u64::from_str_radix(text, 2).expect("字段必须是二进制位串")
}

pub(super) fn extract(sample: &Sample) -> (BTreeSet<String>, usize) {
    let mut buckets = BTreeSet::new();
    // 不具有 satp 的 ISA 没有这里定义的 RISC-V 分页字段。
    let Some(satp) = sample.pre_registers.get("satp") else { return (buckets, 0) };
    let satp = bits(satp, 64);
    let levels = match satp >> 60 {
        0 => return (buckets, 0),
        8 => 3,
        9 => 4,
        10 => 5,
        mode => panic!("字段反馈不支持 satp.MODE={mode}"),
    };
    let status = bits(&sample.pre_registers["mstatus"]["struct"]["bits"], 64);
    let privilege = if status & (1 << 17) != 0 {
        match (status >> 11) & 3 {
            0 => "User",
            1 => "Supervisor",
            3 => "Machine",
            _ => panic!("mstatus.MPP 为保留值"),
        }
    } else {
        sample.pre_registers["cur_privilege"]["enum"].as_str().expect("缺少特权级")
    };
    match privilege {
        "Machine" => return (buckets, 0),
        "User" | "Supervisor" => (),
        _ => panic!("未知特权级 {privilege}"),
    }
    let instruction = &sample.pre_registers["$instruction"];
    let constructor = instruction["ctor"].as_str().expect("缺少指令构造子");
    let fields = instruction["value"]["struct"].as_object().expect("访存指令参数必须为结构体");
    let (base_index, width_index) = match constructor {
        "LOAD" => (1, 4),
        "STORE" => (2, 3),
        _ => panic!("分页字段反馈尚不支持指令构造子 {constructor}"),
    };
    assert_eq!(fields.len(), width_index + 1, "访存指令参数数量不符");
    // 样本用有序 tuple 字段保存构造子参数；不依赖生成的 tuple 类型名字。
    let field = |index: usize| {
        let suffix = index.to_string();
        let mut matching = fields.iter().filter(|(name, _)| name.ends_with(&suffix));
        let value = matching.next().expect("缺少访存指令参数").1;
        assert!(matching.next().is_none(), "访存指令参数序号重复");
        value
    };
    let immediate = bits(field(0), 12);
    let offset = ((immediate as i64) << 52) >> 52;
    let register = bits(field(base_index), 5);
    let width: u64 = if let Some(width) = field(width_index)["i64"].as_str() {
        width.parse().unwrap()
    } else {
        bits(field(width_index), 64)
    };
    assert!(matches!(width, 1 | 2 | 4 | 8), "不支持的访存宽度 {width}");
    let base = if register == 0 { 0 } else { bits(&sample.pre_registers[&format!("x{register}")], 64) };
    let address = base.wrapping_add(offset as u64);
    let va_bits = 12 + 9 * levels;
    let canonical = (((address << (64 - va_bits)) as i64) >> (64 - va_bits)) as u64;
    if address % width != 0 || address != canonical {
        return (buckets, 0);
    }
    let mut memory = BTreeMap::new();
    for cell in &sample.pre_memory {
        assert_eq!(cell.bytes, 1, "样本内存必须逐字节保存");
        assert!(memory.insert(cell.address, cell.value).is_none(), "样本内存地址重复");
    }
    let root = (satp & ((1 << 44) - 1)) << 12;
    let mut table = root;
    let mut entries = Vec::new();
    for level in (0..levels).rev() {
        let paddr = table + ((address >> (12 + 9 * level)) & 511) * 8;
        // PMA 可证明读取前终止；缺少字节本身不能当成正常终止。
        if let Some(regions) = sample.pre_registers.get("pma_regions") {
            let readable = regions["list"]
                .as_array()
                .expect("PMA 区域必须为列表")
                .iter()
                .find_map(|region| {
                    let region = &region["struct"];
                    let base = bits(&region["base"], 64) as u128;
                    let end = base + bits(&region["size"], 64) as u128;
                    (base <= paddr as u128 && paddr as u128 + 8 <= end).then(|| {
                        region["attributes"]["struct"]["readable"]["bool"].as_bool().expect("缺少 PMA 读取权限")
                    })
                })
                .unwrap_or(false);
            if !readable {
                assert!((0..8).all(|i| !memory.contains_key(&(paddr + i))), "PMA 拒绝的 PTE 却有前态字节");
                break;
            }
        }
        let mut pte = 0;
        for i in 0..8 {
            pte |= u64::from(memory.get(&(paddr + i)).copied().flatten().expect("页表读取缺少已知前态字节")) << (8 * i);
        }
        entries.push((level, paddr, pte));
        // 只有合法非叶 PTE 会继续读取；G 与低 RSW 位不阻止遍历。
        let pointer = pte & 1 != 0 && pte & 0xe == 0 && pte & 0xd0 == 0 && pte >> 54 == 0;
        if !pointer {
            break;
        }
        table = ((pte >> 10) & ((1 << 44) - 1)) << 12;
    }
    for &(level, _, pte) in &entries {
        for (name, lo, width) in [
            ("V", 0, 1),
            ("R", 1, 1),
            ("W", 2, 1),
            ("X", 3, 1),
            ("U", 4, 1),
            ("G", 5, 1),
            ("A", 6, 1),
            ("D", 7, 1),
            ("RSW", 8, 2),
            ("reserved", 54, 5),
            ("RSW_60t59b", 59, 2),
            ("PBMT", 61, 2),
            ("N", 63, 1),
        ] {
            buckets.insert(json!([level, name, (pte >> lo) & ((1u64 << width) - 1)]).to_string());
        }
        let address = ((pte >> 10) & ((1 << 44) - 1)) << 12;
        // 优先级也是旧反馈格式的一部分：高地址先于页表别名。
        let region = if address >= 1 << 48 {
            "ge_2p48"
        } else if address >= 1 << 43 {
            "ge_2p43"
        } else if address == root {
            "root_table"
        } else if entries.iter().any(|(_, paddr, _)| paddr & !4095 == address) {
            "page_tables"
        } else if (0x80000000..0x80100000).contains(&address) {
            "harness"
        } else if address < 0x80000000 {
            "below_dram"
        } else if address >= (1 << 43) - (1 << 20) {
            "dram_top"
        } else if address < 1 << 32 {
            "dram_low"
        } else {
            "dram_middle"
        };
        buckets.insert(json!([level, "PPN", region]).to_string());
    }
    // 九个单比特字段、三个双比特字段、五位 reserved，以及 PPN 九桶。
    (buckets, entries.len() * (9 * 2 + 3 * 4 + 32 + 9))
}
