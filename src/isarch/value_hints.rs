//! P1（plan-bughunt 值域 signposting）：`[[value_hints]]` 的候选值展开与钉值
//! 物化。
//!
//! solve-state 自由求解的取值系统性退化（W24 campaign + B2/B3 归因：成功路径
//! 地址恒对齐、基址退化 x0/低位、源数据初值全零/任意），使错位/边界类 bug
//! （#1574 错位 SC、#6486 发错数据）在生成层不可见。本模块把配置声明的
//! "候选值集"展开为具体钉值批（机制 (b)：复用 fixed_prestate 通道注入，
//! E 线已证定向钉值有效），批调度见 exec.rs 的 solve_state_main。

use isla_lib::bitvector::BV;
use isla_lib::config::{MemoryRegionConfig, PmaRegionConfig, PmaSize, ValueHintConfig, ValueHintTarget, ValuePattern};
use isla_lib::ir::*;
use isla_lib::register::RegisterBindings;
use isla_lib::zencode;
use std::collections::HashMap;

use super::clause::normalize_clause_name;

/// 候选值的宽度语义：`Exact` 不允许超出寄存器宽度（显式数值，超宽即配置
/// 错误）；`RepeatToFill` 按低 64 位模式重复填充寄存器宽度（nonzero_pattern
/// 一类模式值，64 位寄存器取原样、128 位 vreg 取双份重复）。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PinWidth {
    Exact,
    RepeatToFill,
}

/// 一个候选值批：目标维度的全部寄存器 + 候选值。批内寄存器取值可各不相同
/// （data 维度按寄存器序号 XOR 步进，保持源寄存器间可区分——错源类 bug 如
/// #6486 的签名依赖可区分源）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PinSet {
    pub label: String,
    pub pins: Vec<(String, u128, PinWidth)>,
}

/// 候选值展开的区域锚点：具体 (base, top) 边界表，按 base 升序。
/// 优先 concrete [[pma_regions]]；无具体 PMA 区域时退回 [[memory_regions]]
/// 的非 excluded 区域（excluded 是判死段，锚在那里只会全批 Unsat）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegionAnchors {
    pub regions: Vec<(u64, u64)>,
}

/// 从配置推导区域锚点。没有任何可用具体区域时报错（需要锚点的模式无法展开）。
pub fn region_anchors(
    pma_regions: Option<&[PmaRegionConfig]>,
    memory_regions: Option<&[MemoryRegionConfig]>,
) -> Result<RegionAnchors, String> {
    let mut regions = Vec::new();
    if let Some(pma) = pma_regions {
        for region in pma {
            if let PmaSize::Concrete(size) = region.size {
                // base+size 不溢出已在配置解析校验
                regions.push((region.base, region.base + size));
            }
            // 符号边界的 top 不是常量，不能作常量候选的锚点，跳过
        }
    }
    if regions.is_empty() {
        if let Some(memory) = memory_regions {
            for region in memory {
                if region.region_type != isla_lib::config::MemoryRegionType::Excluded {
                    regions.push((region.base, region.base + region.size));
                }
            }
        }
    }
    if regions.is_empty() {
        return Err("值域 hint 需要 [[pma_regions]] 或 [[memory_regions]] 提供具体区域锚点".to_string());
    }
    regions.sort();
    Ok(RegionAnchors { regions })
}

/// 目标维度的默认寄存器集合：
/// - base → x1..x31（x0 恒零寄存器不可钉）；
/// - data → vr0..vr31 + f0..f31（向量/浮点源数据；标量源数据与基址同属 GPR，
///   机制 (b) 无法把二者分开钉，钉 base 已顺带给标量源数据非零非恒等值）；
/// - vector_ctx → vl、vstart。
pub fn dimension_registers(target: ValueHintTarget) -> Vec<String> {
    match target {
        ValueHintTarget::Base => (1..32).map(|r| format!("x{}", r)).collect(),
        ValueHintTarget::Data => {
            let mut regs = (0..32).map(|r| format!("vr{}", r)).collect::<Vec<_>>();
            regs.extend((0..32).map(|r| format!("f{}", r)));
            regs
        }
        ValueHintTarget::VectorCtx => vec!["vl".to_string(), "vstart".to_string()],
    }
}

/// 单个内置模式展开为候选值列表（u128，宽度语义见 PinWidth）。
/// 锚点依赖：pma_boundary_pm1/misaligned/low_hole/aligned 需要区域锚点；
/// vector_bounds 只允许 vector_ctx 维度（界值语义只对 vl/vstart 成立）。
pub fn expand_pattern(
    pattern: ValuePattern,
    target: ValueHintTarget,
    anchors: &RegionAnchors,
) -> Result<Vec<(u128, PinWidth)>, String> {
    match pattern {
        ValuePattern::PmaBoundaryPm1 => {
            let mut candidates = Vec::new();
            for &(base, top) in &anchors.regions {
                // base=0 时 base-1 回绕、top=u64::MAX 时 top+1 溢出，均跳过
                let mut around = Vec::new();
                if base > 0 {
                    around.push(base - 1);
                }
                around.push(base + 1);
                around.push(top - 1);
                if top < u64::MAX {
                    around.push(top + 1);
                }
                for value in around {
                    if !candidates.contains(&value) {
                        candidates.push(value);
                    }
                }
            }
            Ok(candidates.into_iter().map(|value| (u128::from(value), PinWidth::Exact)).collect())
        }
        ValuePattern::Misaligned => {
            // 锚定最低区域基址，奇偏移对 2/4/8/16B 访问宽度全部错位；
            // 有效地址 = 钉值基址 + 符号立即数，Z3 默认给 imm 取 0/小值，
            // 奇基址在多数模型取值下保持错位（E 线钉值机制的批化）。
            let base = anchors.regions[0].0;
            let candidates = [1_u64, 3, 7, 15].map(|offset| (u128::from(base + offset), PinWidth::Exact));
            Ok(candidates.to_vec())
        }
        ValuePattern::LowHole => {
            // 低位洞：最低区域基址之下的低位地址（配置地图外）。
            let lowest = anchors.regions[0].0;
            let candidates = [0x0_u64, 0x1, 0xf, 0xfff].into_iter().filter(|&v| v < lowest).collect::<Vec<_>>();
            if candidates.is_empty() {
                return Err("low_hole 无可用候选：区域地图已覆盖全部低位地址".to_string());
            }
            Ok(candidates.into_iter().map(|value| (u128::from(value), PinWidth::Exact)).collect())
        }
        ValuePattern::Aligned => {
            let base = anchors.regions[0].0;
            let candidates = [base, base + 8, base + 16, base + 0x1000];
            Ok(candidates.into_iter().map(|value| (u128::from(value), PinWidth::Exact)).collect())
        }
        ValuePattern::NonzeroPattern => {
            // 0xA5 步进 / 0x00FF 掩码 / 全 1 极值三选；RepeatToFill 按宽度重复。
            let candidates = [0xA5A5_A5A5_A5A5_A5A5_u64, 0x00FF_00FF_00FF_00FF, 0xFFFF_FFFF_FFFF_FFFF];
            Ok(candidates.into_iter().map(|value| (u128::from(value), PinWidth::RepeatToFill)).collect())
        }
        ValuePattern::VectorBounds => {
            if target != ValueHintTarget::VectorCtx {
                return Err("vector_bounds 模式只支持 vector_ctx 维度".to_string());
            }
            // vl 界值（VLMAX 相对值依赖 vtype，钉值机制只能钉常量，取典型
            // VLMAX 锚点 8/16/128 与边界 0/1；vstart 界值 0/1 由调用侧逐寄存器生成）
            Ok(vec![
                (0, PinWidth::Exact),
                (1, PinWidth::Exact),
                (8, PinWidth::Exact),
                (16, PinWidth::Exact),
                (128, PinWidth::Exact),
            ])
        }
    }
}

/// 单条 hint 在指定 clause 上的作用域匹配（clauses 缺省全局）。
pub fn hint_matches_clause(hint: &ValueHintConfig, clause: &str) -> bool {
    match &hint.clauses {
        None => true,
        Some(names) => names.iter().any(|name| normalize_clause_name(name) == clause),
    }
}

/// 把单条 hint 展开为候选批集合。data 维度按寄存器序号 XOR 步进生成各寄存器
/// 的区分值；base 维度整组同值；vector_ctx 每个界值候选只钉单个寄存器
/// （vl 优先，vstart 取 0/1）。
pub fn hint_pin_sets(hint: &ValueHintConfig, clause: &str, anchors: &RegionAnchors) -> Result<Vec<PinSet>, String> {
    if !hint_matches_clause(hint, clause) {
        return Ok(Vec::new());
    }

    let mut sets = Vec::new();
    let dimension = dimension_registers(hint.target);

    // vector_ctx 维度只接受 vector_bounds 模式（界值语义只对 vl/vstart 成立，
    // 地址模式钉进 vl 只会产生非法向量上下文）
    if hint.target == ValueHintTarget::VectorCtx {
        for &pattern in &hint.patterns {
            if pattern != ValuePattern::VectorBounds {
                return Err(format!("vector_ctx 维度不支持模式 {:?}（只支持 vector_bounds）", pattern));
            }
        }
    }

    // 模式候选
    for &pattern in &hint.patterns {
        let candidates = expand_pattern(pattern, hint.target, anchors)?;
        match hint.target {
            ValueHintTarget::VectorCtx if pattern == ValuePattern::VectorBounds => {
                // vl 取全部界值候选；vstart 补 0/1 界值
                for (value, width) in candidates {
                    sets.push(PinSet {
                        label: format!("vector_ctx/vector_bounds:vl={:#x}", value),
                        pins: vec![("vl".to_string(), value, width)],
                    });
                }
                for value in [0_u128, 1] {
                    sets.push(PinSet {
                        label: format!("vector_ctx/vector_bounds:vstart={:#x}", value),
                        pins: vec![("vstart".to_string(), value, PinWidth::Exact)],
                    });
                }
            }
            ValueHintTarget::Data => {
                for (value, width) in candidates {
                    // XOR 步进：第 i 个寄存器取 value ^ i，跨寄存器可区分且无进位回绕
                    let pins = dimension
                        .iter()
                        .enumerate()
                        .map(|(index, reg)| (reg.clone(), value ^ (index as u128), width))
                        .collect();
                    sets.push(PinSet { label: format!("data/{:?}:{:#x}", pattern, value), pins });
                }
            }
            _ => {
                for (value, width) in candidates {
                    let pins = dimension.iter().map(|reg| (reg.clone(), value, width)).collect();
                    sets.push(PinSet { label: format!("{:?}/{:?}:{:#x}", hint.target, pattern, value), pins });
                }
            }
        }
    }

    // 显式数值候选：整组同值（vector_ctx 维度钉 vl）
    for &value in &hint.values {
        let pins = if hint.target == ValueHintTarget::VectorCtx {
            vec![("vl".to_string(), u128::from(value), PinWidth::Exact)]
        } else {
            dimension.iter().map(|reg| (reg.clone(), u128::from(value), PinWidth::Exact)).collect()
        };
        sets.push(PinSet { label: format!("{:?}/explicit:{:#x}", hint.target, value), pins });
    }

    Ok(sets)
}

/// 候选批与既有固定初态（CLI --prestate）的寄存器冲突检测：同一寄存器既被
/// CLI 钉值又被 hint 钉值是歧义配置，硬失败。
pub fn detect_prestate_conflicts<B: BV>(
    pins: &[(String, u128, PinWidth)],
    prestate: &HashMap<Name, Val<B>>,
    symtab: &Symtab,
) -> Result<(), String> {
    for (reg_name, _, _) in pins {
        if let Some(reg_id) = symtab.get(&zencode::encode(reg_name)) {
            if prestate.contains_key(&reg_id) {
                return Err(format!("值域 hint 与 --prestate 重复钉值寄存器 {}", reg_name));
            }
        }
    }
    Ok(())
}

/// 求解批：自由批（label 为 None，prestate 即 CLI 固定初态）或值域 hint 批
/// （label 携带维度/模式/候选值，prestate 为 CLI 固定初态 + 候选钉值的并集）。
/// 批间不共享假设——每批独立重置 checkpoint 后求解（机制 (b) 的批化形态）。
///
/// P2 编码维度预分片扩展：`instruction` 钉死本批的指令编码（None = 自由
/// 求解指令），`case_limit`/`timeout` 为分片批的预算覆写（None 沿用全局）。
pub struct SolveBatch<B: BV> {
    pub label: Option<String>,
    pub prestate: HashMap<Name, Val<B>>,
    pub instruction: Option<super::exec::FixedInstruction>,
    pub case_limit: Option<u32>,
    pub timeout: Option<u64>,
}

/// 区域配置输入（isarch_main 从 ISAConfig 装配传入，避免 exec 依赖整个 ISAConfig）。
#[derive(Clone, Copy)]
pub struct RegionConfigInput<'a> {
    pub pma_regions: Option<&'a [PmaRegionConfig]>,
    pub memory_regions: Option<&'a [MemoryRegionConfig]>,
}

/// 计算一个 clause 的求解批序列：首批恒为自由批（保留无提示档做对照，
/// signposting 不压缩纯符号路径），其后为作用域内全部 hint 候选批（按
/// PinSet label 去重）。
pub fn plan_solve_batches<'ir, B: BV>(
    value_hints: &[ValueHintConfig],
    clause: &str,
    region_configs: RegionConfigInput<'_>,
    shared_state: &SharedState<'ir, B>,
    regs: &RegisterBindings<'ir, B>,
    lets: &Bindings<'ir, B>,
    cli_prestate: &HashMap<Name, Val<B>>,
) -> Result<Vec<SolveBatch<B>>, String> {
    let mut batches = vec![SolveBatch {
        label: None,
        prestate: cli_prestate.clone(),
        instruction: None,
        case_limit: None,
        timeout: None,
    }];

    let matching: Vec<&ValueHintConfig> = value_hints.iter().filter(|hint| hint_matches_clause(hint, clause)).collect();
    if matching.is_empty() {
        return Ok(batches);
    }

    let anchors = region_anchors(region_configs.pma_regions, region_configs.memory_regions)?;

    let mut seen_labels = std::collections::HashSet::new();
    for hint in matching {
        for pin_set in hint_pin_sets(hint, clause, &anchors)? {
            if !seen_labels.insert(pin_set.label.clone()) {
                continue;
            }
            detect_prestate_conflicts(&pin_set.pins, cli_prestate, &shared_state.symtab)?;
            let mut prestate = cli_prestate.clone();
            prestate.extend(materialize_pins(&pin_set.pins, shared_state, lets, regs)?);
            batches.push(SolveBatch {
                label: Some(pin_set.label),
                prestate,
                instruction: None,
                case_limit: None,
                timeout: None,
            });
        }
    }
    Ok(batches)
}

/// 物化候选批为 fixed_prestate 通道的固定值表：按寄存器 IR 类型构造具体
/// Val::Bits 并复用 validate_fixed_prestate_value 做严格类型校验。
pub fn materialize_pins<B: BV>(
    pins: &[(String, u128, PinWidth)],
    shared_state: &SharedState<B>,
    lets: &Bindings<B>,
    regs: &RegisterBindings<B>,
) -> Result<HashMap<Name, Val<B>>, String> {
    let mut fixed = HashMap::new();
    for (reg_name, value, width_kind) in pins {
        let reg_id = shared_state
            .symtab
            .get(&zencode::encode(reg_name))
            .ok_or_else(|| format!("值域 hint 未知寄存器 {}", reg_name))?;
        let ty = shared_state.registers.get(&reg_id).ok_or_else(|| format!("值域 hint {} 不是寄存器", reg_name))?;
        let Ty::Bits(width) = ty else {
            return Err(format!("值域 hint 寄存器 {} 不是定宽位向量（类型 {:?}）", reg_name, ty));
        };
        let bits = bits_from_candidate::<B>(*value, *width_kind, *width)?;
        let value = Val::Bits(bits);
        super::target::validate_fixed_prestate_value(reg_name, reg_id, &value, ty, shared_state, lets, regs)?;
        fixed.insert(reg_id, value);
    }
    Ok(fixed)
}

/// 候选值 → 指定宽度位向量。Exact 超宽即配置错误；RepeatToFill 用低 64 位
/// 模式重复填充（64 位寄存器取原样，128 位 vreg 双份重复后截断）。
fn bits_from_candidate<B: BV>(value: u128, width_kind: PinWidth, width: u32) -> Result<B, String> {
    if width > B::MAX_WIDTH {
        return Err(format!("寄存器宽度 {} 超出位向量后端上限 {}", width, B::MAX_WIDTH));
    }
    let filled = match width_kind {
        PinWidth::Exact => {
            // width 可达 128，u128 >> 128 会溢出 panic，用移位前宽度判断
            if width < 128 && (value >> width) != 0 {
                return Err(format!("候选值 {:#x} 超出寄存器宽度 {} 位", value, width));
            }
            value
        }
        PinWidth::RepeatToFill => {
            let low = value as u64;
            if width <= 64 {
                u128::from(low & mask_u64(width))
            } else {
                // 高于 64 位的部分用低 64 位模式重复填充
                (u128::from(low) << 64) | u128::from(low)
            }
        }
    };
    Ok(bits_from_u128::<B>(filled, width))
}

fn mask_u64(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1_u64 << width) - 1
    }
}

/// u128 → B（按位分片装配，支持超过 64 位的宽度如 128 位 vreg）。
fn bits_from_u128<B: BV>(value: u128, width: u32) -> B {
    if width <= 64 {
        B::new((value as u64) & mask_u64(width), width)
    } else {
        let low = B::new(value as u64, 64);
        let high_width = width - 64;
        let high = B::new((value >> 64) as u64 & mask_u64(high_width), high_width);
        B::zeros(width).set_slice(0, low).set_slice(64, high)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::bitvector::b129::B129;
    use isla_lib::bitvector::b64::B64;
    use isla_lib::config::MemoryRegionType;

    fn anchors_fixture() -> RegionAnchors {
        RegionAnchors { regions: vec![(0x8000_0000, 0x9000_0000)] }
    }

    fn hint(
        target: ValueHintTarget,
        patterns: &[ValuePattern],
        values: &[u64],
        clauses: Option<&[&str]>,
    ) -> ValueHintConfig {
        ValueHintConfig {
            target,
            patterns: patterns.to_vec(),
            values: values.to_vec(),
            clauses: clauses.map(|names| names.iter().map(|name| name.to_string()).collect()),
        }
    }

    /// 属性字段内容对锚点展开无关，构造一个合法的基线即可。
    fn baseline_pma_attributes() -> isla_lib::config::PmaAttributes {
        use isla_lib::config::{PmaAttributes, PmaMisalignedFault, PmaReservability};
        PmaAttributes {
            readable: true,
            writable: true,
            executable: true,
            cacheable: true,
            coherent: true,
            read_idempotent: true,
            write_idempotent: true,
            supports_cbo_zzero: true,
            misaligned_fault: PmaMisalignedFault::NoFault,
            reservability: PmaReservability::Eventual,
            include_in_device_tree: true,
        }
    }

    #[test]
    fn region_anchors_prefers_concrete_pma_and_skips_symbolic() {
        let ram_attrs = baseline_pma_attributes();
        let pma = vec![
            PmaRegionConfig {
                name: "ram".to_string(),
                base: 0x8000_0000,
                size: PmaSize::Concrete(0x1000_0000),
                attributes: ram_attrs.clone(),
            },
            PmaRegionConfig {
                name: "sym".to_string(),
                base: 0x9000_0000,
                size: PmaSize::Symbolic { min: 0x1000, max: 0x2000 },
                attributes: ram_attrs,
            },
        ];
        let anchors = region_anchors(Some(&pma), None).unwrap();
        // 符号 size 区域不能提供常量锚点
        assert_eq!(anchors.regions, vec![(0x8000_0000, 0x9000_0000)]);

        // 无具体 PMA 时退回 memory_regions 非 excluded 区域
        let memory = vec![
            MemoryRegionConfig {
                name: "code".to_string(),
                base: 0x0,
                size: 0x1000,
                region_type: MemoryRegionType::Concrete,
            },
            MemoryRegionConfig {
                name: "hole".to_string(),
                base: 0x0200_0000,
                size: 0x2000_0000,
                region_type: MemoryRegionType::Excluded,
            },
        ];
        let anchors = region_anchors(None, Some(&memory)).unwrap();
        assert_eq!(anchors.regions, vec![(0x0, 0x1000)]);

        assert!(region_anchors(None, None).is_err());
    }

    #[test]
    fn pattern_expansion_boundaries_and_offsets() {
        let anchors = anchors_fixture();
        // pma_boundary_pm1：base/top 各 ±1
        let candidates = expand_pattern(ValuePattern::PmaBoundaryPm1, ValueHintTarget::Base, &anchors).unwrap();
        let values: Vec<u128> = candidates.into_iter().map(|(value, _)| value).collect();
        assert_eq!(values, vec![0x7fff_ffff, 0x8000_0001, 0x8fff_ffff, 0x9000_0001]);

        // misaligned：锚定最低区域基址的奇偏移（对 2/4/8/16B 全部错位）
        let candidates = expand_pattern(ValuePattern::Misaligned, ValueHintTarget::Base, &anchors).unwrap();
        let values: Vec<u128> = candidates.into_iter().map(|(value, _)| value).collect();
        assert_eq!(values, vec![0x8000_0001, 0x8000_0003, 0x8000_0007, 0x8000_000f]);

        // aligned：基址及对齐锚点
        let candidates = expand_pattern(ValuePattern::Aligned, ValueHintTarget::Base, &anchors).unwrap();
        let values: Vec<u128> = candidates.into_iter().map(|(value, _)| value).collect();
        assert_eq!(values, vec![0x8000_0000, 0x8000_0008, 0x8000_0010, 0x8000_1000]);

        // low_hole：最低基址之下的低位地址
        let candidates = expand_pattern(ValuePattern::LowHole, ValueHintTarget::Base, &anchors).unwrap();
        let values: Vec<u128> = candidates.into_iter().map(|(value, _)| value).collect();
        assert_eq!(values, vec![0x0, 0x1, 0xf, 0xfff]);

        // 地图覆盖全部低位时 low_hole 报错
        let covering = RegionAnchors { regions: vec![(0x0, 0x1000)] };
        assert!(expand_pattern(ValuePattern::LowHole, ValueHintTarget::Base, &covering).is_err());

        // vector_bounds 只允许 vector_ctx
        assert!(expand_pattern(ValuePattern::VectorBounds, ValueHintTarget::Base, &anchors).is_err());
    }

    #[test]
    fn hint_pin_sets_scope_and_dimensions() {
        let anchors = anchors_fixture();
        // 作用域：clauses 内归一匹配，不在作用域返回空
        let scoped = hint(ValueHintTarget::Base, &[ValuePattern::Misaligned], &[], Some(&["STORE", "zLOAD"]));
        assert_eq!(hint_pin_sets(&scoped, "zSTORE", &anchors).unwrap().len(), 4);
        assert!(hint_pin_sets(&scoped, "zVSSEGTYPE", &anchors).unwrap().is_empty());

        // base 维度：整组 GPR 同值（x0 不在集合）
        let global = hint(ValueHintTarget::Base, &[ValuePattern::Misaligned], &[], None);
        let sets = hint_pin_sets(&global, "zSTORE", &anchors).unwrap();
        assert_eq!(sets.len(), 4);
        assert_eq!(sets[0].pins.len(), 31);
        assert!(sets[0].pins.iter().all(|(reg, _, _)| reg != "x0"));
        assert!(sets[0].pins.iter().all(|(_, value, _)| *value == 0x8000_0001));

        // data 维度：XOR 步进，寄存器间可区分且均非零
        let data = hint(ValueHintTarget::Data, &[ValuePattern::NonzeroPattern], &[], None);
        let sets = hint_pin_sets(&data, "zVSSEGTYPE", &anchors).unwrap();
        assert_eq!(sets.len(), 3, "nonzero_pattern 三选（步进/掩码/极值）");
        assert_eq!(sets[0].pins.len(), 64, "vr0..vr31 + f0..f31");
        let vr0 = sets[0].pins.iter().find(|(reg, _, _)| reg == "vr0").unwrap();
        let vr1 = sets[0].pins.iter().find(|(reg, _, _)| reg == "vr1").unwrap();
        assert_eq!(vr0.1, 0xA5A5_A5A5_A5A5_A5A5);
        assert_eq!(vr1.1, 0xA5A5_A5A5_A5A5_A5A4, "第 i 个寄存器取 value ^ i");
        assert!(sets[0].pins.iter().all(|(_, value, _)| *value != 0));

        // vector_ctx 维度：vl 界值批 + vstart 0/1 批，每批单寄存器
        let ctx = hint(ValueHintTarget::VectorCtx, &[ValuePattern::VectorBounds], &[], None);
        let sets = hint_pin_sets(&ctx, "zVSSEGTYPE", &anchors).unwrap();
        assert_eq!(sets.len(), 7, "vl 界值 5 批 + vstart 2 批");
        assert!(sets.iter().all(|set| set.pins.len() == 1));

        // 显式数值：base 整组同值 / vector_ctx 钉 vl
        let explicit = hint(ValueHintTarget::Base, &[], &[0x8000_1000], None);
        let sets = hint_pin_sets(&explicit, "zSTORE", &anchors).unwrap();
        assert_eq!(sets.len(), 1);
        assert!(sets[0].pins.iter().all(|(_, value, _)| *value == 0x8000_1000));
        let explicit_ctx = hint(ValueHintTarget::VectorCtx, &[], &[7], None);
        let sets = hint_pin_sets(&explicit_ctx, "zVSSEGTYPE", &anchors).unwrap();
        assert_eq!(sets[0].pins, vec![("vl".to_string(), 7, PinWidth::Exact)]);
    }

    /// 物化：64 位 GPR 取原样；128 位 vreg 模式双份重复；Exact 超宽硬失败；
    /// 物化结果通过 validate_fixed_prestate_value 的严格类型校验。
    #[test]
    fn materialize_pins_widths_and_validation() {
        let mut symtab = Symtab::new();
        let x5_text = zencode::encode("x5");
        let vr0_text = zencode::encode("vr0");
        let vr1_text = zencode::encode("vr1");
        let x5_name = symtab.intern(&x5_text);
        let vr0_name = symtab.intern(&vr0_text);
        let vr1_name = symtab.intern(&vr1_text);
        let mut shared_state = SharedState::empty(symtab);
        shared_state.registers.insert(x5_name, Ty::Bits(64));
        shared_state.registers.insert(vr0_name, Ty::Bits(128));
        shared_state.registers.insert(vr1_name, Ty::Bits(128));
        let mut reg_bindings = RegisterBindings::new();
        let x5_ty = Ty::Bits(64);
        let vr0_ty = Ty::Bits(128);
        let vr1_ty = Ty::Bits(128);
        reg_bindings.insert(x5_name, false, UVal::Uninit(&x5_ty));
        reg_bindings.insert(vr0_name, false, UVal::Uninit(&vr0_ty));
        reg_bindings.insert(vr1_name, false, UVal::Uninit(&vr1_ty));
        let lets = Bindings::default();

        let pins = vec![
            ("x5".to_string(), 0x8000_0001, PinWidth::Exact),
            ("vr0".to_string(), 0xA5A5_A5A5_A5A5_A5A5, PinWidth::RepeatToFill),
            ("vr1".to_string(), 0xA5A5_A5A5_A5A5_A5A4, PinWidth::RepeatToFill),
        ];
        let fixed = materialize_pins::<B129>(&pins, &shared_state, &lets, &reg_bindings).unwrap();

        assert_eq!(fixed.get(&x5_name), Some(&Val::Bits(B129::new(0x8000_0001, 64))));
        let vr0 = match fixed.get(&vr0_name) {
            Some(Val::Bits(bits)) => *bits,
            other => panic!("vr0 未物化为位向量: {:?}", other),
        };
        assert_eq!(vr0.len(), 128);
        assert_eq!((vr0 >> B129::new(64, 7)).lower_u64(), 0xA5A5_A5A5_A5A5_A5A5, "高 64 位为低 64 位模式重复");
        assert_eq!(vr0.lower_u64(), 0xA5A5_A5A5_A5A5_A5A5);
        // vr1 步进值只落在低 64 位模式上
        let vr1 = match fixed.get(&vr1_name) {
            Some(Val::Bits(bits)) => *bits,
            other => panic!("vr1 未物化为位向量: {:?}", other),
        };
        assert_eq!(vr1.lower_u64(), 0xA5A5_A5A5_A5A5_A5A4);

        // Exact 超宽：128 位候选值钉 64 位寄存器必须报错
        let overflow = vec![("x5".to_string(), 0x1_0000_0000_0000_0000, PinWidth::Exact)];
        assert!(materialize_pins::<B129>(&overflow, &shared_state, &lets, &reg_bindings).is_err());

        // 未知寄存器报错
        let unknown = vec![("x99".to_string(), 1, PinWidth::Exact)];
        assert!(materialize_pins::<B129>(&unknown, &shared_state, &lets, &reg_bindings).is_err());

        // 64 位后端对 128 位寄存器报错（宽度超后端上限）
        let mut symtab64 = Symtab::new();
        let vr0_text64 = zencode::encode("vr0");
        let vr0_name64 = symtab64.intern(&vr0_text64);
        let mut shared_state64 = SharedState::empty(symtab64);
        shared_state64.registers.insert(vr0_name64, Ty::Bits(128));
        let reg_bindings64 = RegisterBindings::new();
        let pins64 = vec![("vr0".to_string(), 0xA5A5_A5A5_A5A5_A5A5, PinWidth::RepeatToFill)];
        assert!(materialize_pins::<B64>(&pins64, &shared_state64, &Bindings::default(), &reg_bindings64).is_err());
    }

    /// 批计划：首批恒为自由批；hint 批按候选展开并物化钉值；CLI --prestate
    /// 与 hint 钉值冲突硬失败；无匹配 hint 时只有自由批。
    #[test]
    fn plan_solve_batches_free_first_and_materialized() {
        let mut symtab = Symtab::new();
        let reg_names: Vec<String> = (1..32)
            .map(|r| format!("x{}", r))
            .chain((0..32).map(|r| format!("vr{}", r)))
            .chain((0..32).map(|r| format!("f{}", r)))
            .chain(["vl".to_string(), "vstart".to_string()])
            .collect();
        let texts: Vec<String> = reg_names.iter().map(|reg| zencode::encode(reg)).collect();
        let names: Vec<(Name, &String)> = texts.iter().map(|text| (symtab.intern(text), text)).collect();
        let mut shared_state = SharedState::<B129>::empty(symtab);
        for &(name, _) in &names {
            shared_state.registers.insert(name, Ty::Bits(128));
        }
        let reg_bindings = RegisterBindings::new();
        let lets = Bindings::default();
        let region_configs = RegionConfigInput {
            pma_regions: Some(&[PmaRegionConfig {
                name: "ram".to_string(),
                base: 0x8000_0000,
                size: PmaSize::Concrete(0x1000_0000),
                attributes: baseline_pma_attributes(),
            }]),
            memory_regions: None,
        };

        // 无匹配 hint：只有自由批
        let no_hints: Vec<ValueHintConfig> = Vec::new();
        let batches = plan_solve_batches(
            &no_hints,
            "zSTORE",
            region_configs,
            &shared_state,
            &reg_bindings,
            &lets,
            &HashMap::new(),
        )
        .unwrap();
        assert_eq!(batches.len(), 1);
        assert_eq!(batches[0].label, None);

        // base:misaligned 4 候选 + 自由批
        let hints = vec![hint(ValueHintTarget::Base, &[ValuePattern::Misaligned], &[], Some(&["zSTORE"]))];
        let batches =
            plan_solve_batches(&hints, "zSTORE", region_configs, &shared_state, &reg_bindings, &lets, &HashMap::new())
                .unwrap();
        assert_eq!(batches.len(), 5, "自由批 + 4 个错位候选批");
        assert_eq!(batches[0].label, None);
        assert_eq!(batches[1].label.as_deref(), Some("Base/Misaligned:0x80000001"));
        // 钉值物化：x5 = 0x80000001（128 位寄存器宽度下 Exact 值高位为零）
        let x5_index = reg_names.iter().position(|reg| reg == "x5").unwrap();
        let x5_name = names[x5_index].0;
        let _ = &texts;
        match batches[1].prestate.get(&x5_name) {
            Some(Val::Bits(bits)) => assert_eq!(bits.lower_u64(), 0x8000_0001),
            other => panic!("x5 未被钉值: {:?}", other),
        }
        // 批间不共享假设：每批 prestate 独立，自由批不含钉值
        assert!(batches[0].prestate.is_empty());

        // CLI --prestate 冲突硬失败
        let mut cli_prestate = HashMap::new();
        cli_prestate.insert(x5_name, Val::Bits(B129::new(0, 128)));
        assert!(plan_solve_batches(
            &hints,
            "zSTORE",
            region_configs,
            &shared_state,
            &reg_bindings,
            &lets,
            &cli_prestate
        )
        .is_err());

        // 作用域外 clause：只有自由批（且不要求锚点）
        let batches = plan_solve_batches(
            &hints,
            "zVSSEGTYPE",
            region_configs,
            &shared_state,
            &reg_bindings,
            &lets,
            &HashMap::new(),
        )
        .unwrap();
        assert_eq!(batches.len(), 1);

        // 两条 hint 同候选（同 label）去重
        let duplicated = vec![
            hint(ValueHintTarget::Base, &[ValuePattern::Misaligned], &[], None),
            hint(ValueHintTarget::Base, &[ValuePattern::Misaligned], &[], None),
        ];
        let batches = plan_solve_batches(
            &duplicated,
            "zSTORE",
            region_configs,
            &shared_state,
            &reg_bindings,
            &lets,
            &HashMap::new(),
        )
        .unwrap();
        assert_eq!(batches.len(), 5, "重复候选按 label 去重");
    }

    /// 钉值批与 CLI --prestate 的寄存器冲突必须被检出（歧义配置硬失败）。
    #[test]
    fn detect_prestate_conflicts_reports_overlap() {
        let mut symtab = Symtab::new();
        let x5_text = zencode::encode("x5");
        let x6_text = zencode::encode("x6");
        let x5_name = symtab.intern(&x5_text);
        let x6_name = symtab.intern(&x6_text);
        let prestate = HashMap::from([(x5_name, Val::Bits(B64::new(1, 64)))]);

        let pins = vec![("x5".to_string(), 0x8000_0001, PinWidth::Exact)];
        let error = detect_prestate_conflicts::<B64>(&pins, &prestate, &symtab).unwrap_err();
        assert!(error.contains("x5"), "{}", error);

        let pins = vec![("x6".to_string(), 0x8000_0001, PinWidth::Exact)];
        assert!(detect_prestate_conflicts::<B64>(&pins, &prestate, &symtab).is_ok());
    }
}
