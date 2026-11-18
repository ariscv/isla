//! 核对链接后真实指令，确保 GOOD 出口只能从完整内存检查块顺序落入。
use super::*;

pub fn check_exit_layout(disassembly: &str, symbols: &BTreeMap<String, u64>) -> Result<(), String> {
    let mut words = BTreeMap::new();
    for line in disassembly.lines() {
        let fields: Vec<_> = line.split_whitespace().collect();
        if fields.len() < 3 || !fields[0].ends_with(':') || fields[1].len() != 8 {
            continue;
        }
        let pc = match u64::from_str_radix(fields[0].trim_end_matches(':'), 16) {
            Ok(pc) => pc,
            Err(_) => continue,
        };
        let word = u32::from_str_radix(fields[1], 16).map_err(|e| format!("出口静态检查：指令不可解析：{e}"))?;
        if words.insert(pc, word).is_some() {
            return Err("出口静态检查：重复指令地址".into());
        }
    }
    let symbol = |name: &str| symbols.get(name).copied().ok_or_else(|| format!("出口静态检查：缺少符号 {name}"));
    let failure_names = FAILURE_REASONS.iter().map(|reason| format!("fail_{reason}_trap")).collect::<BTreeSet<_>>();
    let failure_entries = FAILURE_REASONS.iter().map(|reason| format!("fail_{reason}")).collect::<BTreeSet<_>>();
    let actual_names = symbols
        .keys()
        .filter(|name| name.starts_with("fail_") && name.ends_with("_trap") && !failure_entries.contains(*name))
        .cloned()
        .collect::<BTreeSet<_>>();
    if actual_names != failure_names {
        return Err("出口静态检查：失败桩符号集合错误".into());
    }
    let mut traps = failure_names.iter().map(|name| symbol(name)).collect::<Result<BTreeSet<_>, _>>()?;
    traps.insert(symbol("good_trap_ins")?);
    if traps.len() != FAILURE_REASONS.len() + 1 {
        return Err("出口静态检查：失败桩符号地址不唯一".into());
    }
    if words.iter().filter_map(|(pc, word)| (word & 0x7f == 0x6b).then_some(*pc)).collect::<BTreeSet<_>>() != traps {
        return Err("出口静态检查：存在未登记的 XSTrap 或出口缺失".into());
    }
    for name in &failure_names {
        let address = symbol(name)?;
        if words.get(&address.checked_sub(4).ok_or("出口静态检查：失败桩地址错误")?) != Some(&0x00100513)
            || words.get(&address) != Some(&0x0005006b)
        {
            return Err("出口静态检查：失败桩编码错误".into());
        }
    }
    let check = symbol("check_memory")?;
    let good = symbol("good_trap")?;
    let trap = symbol("good_trap_ins")?;
    if check >= good
        || trap != good + 4
        || words.get(&good) != Some(&0x00000513)
        || words.get(&trap) != Some(&0x0005006b)
    {
        return Err("出口静态检查：GOOD 桩布局错误".into());
    }
    let failure_addresses = failure_entries.iter().map(|name| symbol(name)).collect::<Result<BTreeSet<_>, _>>()?;
    for (pc, word) in &words {
        let opcode = word & 0x7f;
        if opcode == 0x67 {
            return Err("出口静态检查：不允许间接跳转".into());
        }
        if matches!(opcode, 0x63 | 0x6f) {
            // 直接从 B/J 编码恢复相对目标，避免依赖 objdump 的别名和文本格式。
            let offset = if opcode == 0x63 {
                let immediate = ((word >> 31) << 12)
                    | (((word >> 7) & 1) << 11)
                    | (((word >> 25) & 63) << 5)
                    | (((word >> 8) & 15) << 1);
                ((immediate << 19) as i32) >> 19
            } else {
                let immediate = ((word >> 31) << 20)
                    | (((word >> 12) & 255) << 12)
                    | (((word >> 20) & 1) << 11)
                    | (((word >> 21) & 1023) << 1);
                ((immediate << 11) as i32) >> 11
            };
            let destination = pc.wrapping_add(offset as u64);
            if check < destination && destination <= trap {
                return Err("出口静态检查：跳转绕过内存检查".into());
            }
            if check <= *pc && *pc < good && (opcode != 0x63 || !failure_addresses.contains(&destination)) {
                return Err("出口静态检查：内存检查块不能顺序落入 GOOD".into());
            }
        }
    }
    if !words.get(&(good - 4)).is_some_and(|word| word & 0x7f == 0x63) {
        return Err("出口静态检查：GOOD 前缺少内存检查".into());
    }
    Ok(())
}
