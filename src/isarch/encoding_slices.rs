//! P2（plan-bughunt 编码维度预分片）：`[[encoding_slices]]` 的维度表、分片
//! 枚举与编码构造。
//!
//! 整片自由求解从未选中具体编码（B3 归因：51 例 VSSEG 无一产出 vsseg3e32，
//! #6475 确定性 abort 因此漏掉；VLX/VSX 整片 3600s 超时零产物）。本模块把
//! clause 载荷元组的编码维度（nf×eew×mop…）按维度表展开为钉死编码字段的
//! 求解批：每片构造具体 Ctor 经 zencdec_forwards 求编码，复用
//! --instruction-bits 通道（decode_fixed_instruction 会再走译码回环校验），
//! 批调度见 exec.rs 的 solve_state_main。

use isla_lib::bitvector::BV;
use isla_lib::config::EncodingSliceConfig;
use isla_lib::ir::*;
use isla_lib::register::RegisterBindings;
use isla_lib::smt::{EnumId, EnumMember};
use isla_lib::source_loc::SourceLoc;
use isla_lib::zencode;
use std::collections::{BTreeMap, HashMap};

use super::clause::normalize_clause_name;
use super::exec::{concrete_function_result, decode_register_bindings, FixedInstruction};
use super::value_hints::SolveBatch;

/// 语义字段种类：值域推导与 Val 构造方式。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EncodingFieldKind {
    /// 段字段数 nf（%i64）：内置域 2..=8（Sail RVV 段指令 nfields 装配约束）。
    Nf,
    /// 掩码位 vm（%bv1）：内置域 {0,1}。
    Vm,
    /// 5 位寄存器号（%bv5）：rs1/vs2/vs3——操作数字段，非编码维度，
    /// 内置默认（rs1=6、vs2=7、vs3=8），可用 operand_defaults 或显式
    /// dimensions 枚举覆盖。
    Reg5,
    /// 元素宽度 eew（enum zvlewidth）：域 = IR 枚举成员（语义值 8/16/32/64）。
    Eew,
    /// 索引 mop（enum zindexed_mop）：域 = IR 枚举成员（语义值 0/1）。
    Mop,
}

/// 维度表条目：语义字段名 + 种类。
#[derive(Clone, Copy, Debug)]
pub struct EncodingField {
    pub name: &'static str,
    pub kind: EncodingFieldKind,
}

const fn field(name: &'static str, kind: EncodingFieldKind) -> EncodingField {
    EncodingField { name, kind }
}

/// 段式（unit-strided）载荷元组：VSSEGTYPE / VLSEGFFTYPE。
const SEG_LAYOUT: &[EncodingField] = &[
    field("nf", EncodingFieldKind::Nf),
    field("vm", EncodingFieldKind::Vm),
    field("rs1", EncodingFieldKind::Reg5),
    field("eew", EncodingFieldKind::Eew),
    field("vs3", EncodingFieldKind::Reg5),
];

/// 索引式载荷元组：VLXSEGTYPE / VSXSEGTYPE。
const IDX_SEG_LAYOUT: &[EncodingField] = &[
    field("nf", EncodingFieldKind::Nf),
    field("vm", EncodingFieldKind::Vm),
    field("rs1", EncodingFieldKind::Reg5),
    field("vs2", EncodingFieldKind::Reg5),
    field("eew", EncodingFieldKind::Eew),
    field("vs3", EncodingFieldKind::Reg5),
    field("mop", EncodingFieldKind::Mop),
];

/// 内置维度表：clause（归一名）→ 载荷元组语义布局。条目按位置与 IR
/// union 载荷结构体字段序一一对应，展开前用 [`validate_layout_against_ir`]
/// 逐位核对类型，IR 漂移（重生成/重绑 workaround）即硬失败，不静默产出
/// 错位编码。
pub fn clause_layout(clause: &str) -> Option<&'static [EncodingField]> {
    match normalize_clause_name(clause).as_str() {
        "zVSSEGTYPE" | "zVLSEGFFTYPE" => Some(SEG_LAYOUT),
        "zVLXSEGTYPE" | "zVSXSEGTYPE" => Some(IDX_SEG_LAYOUT),
        _ => None,
    }
}

/// 非维度操作数字段的内置默认（可被 operand_defaults / dimensions 覆盖）。
/// rs1/vs2/vs3 取互不相同且非零的寄存器号（错源类 bug 如 #6486 依赖可区分
/// 源），vm 缺省不掩码（掩码变体按需声明为维度枚举）。
fn builtin_operand_default(name: &str) -> Option<u64> {
    match name {
        "vm" => Some(1),
        "rs1" => Some(6),
        "vs2" => Some(7),
        "vs3" => Some(8),
        _ => None,
    }
}

/// clause 在 zinstruction union 中的载荷类型（Def::Union 的 ctors 逐条核对）。
fn clause_payload_ty<'a, B: BV>(clause: &str, shared_state: &'a SharedState<B>) -> Result<&'a Ty<Name>, String> {
    let normalized = normalize_clause_name(clause);
    let ctor_name = shared_state
        .symtab
        .get(&normalized)
        .ok_or_else(|| format!("编码分片：clause {} 不在当前 IR symtab", zencode::decode(&normalized)))?;
    let instruction_union =
        shared_state.symtab.get("zinstruction").ok_or_else(|| "编码分片：缺少 zinstruction union".to_string())?;
    let members = shared_state
        .type_info
        .unions
        .get(&instruction_union)
        .unwrap_or_else(|| panic!("防御性编程：zinstruction 在 symtab 但不在 type_info.unions"));
    members
        .iter()
        .find(|(name, _)| *name == ctor_name)
        .map(|(_, ty)| ty)
        .ok_or_else(|| format!("编码分片：{} 不在 zinstruction union 载荷中", zencode::decode(&normalized)))
}

/// 布局与 IR 类型核对：载荷结构体字段数、逐位置类型（i64/bv1/bv5/枚举身份）
/// 与维度表一致才通过。
pub fn validate_layout_against_ir<B: BV>(
    clause: &str,
    layout: &[EncodingField],
    shared_state: &SharedState<B>,
) -> Result<(), String> {
    let payload_ty = clause_payload_ty(clause, shared_state)?;
    let Ty::Struct(struct_name) = payload_ty else {
        return Err(format!("编码分片：{} 载荷不是结构体元组（{:?}）", clause, payload_ty));
    };
    let fields = shared_state
        .type_info
        .structs
        .get(struct_name)
        .unwrap_or_else(|| panic!("防御性编程：载荷结构体 {:?} 不在 type_info.structs", struct_name));
    if fields.len() != layout.len() {
        return Err(format!(
            "编码分片：{} 载荷字段数 {} 与维度表 {} 不符（IR 漂移，需修订维度表）",
            clause,
            fields.len(),
            layout.len()
        ));
    }
    for (position, (expected, (_, actual))) in layout.iter().zip(fields.iter()).enumerate() {
        let matches = match expected.kind {
            EncodingFieldKind::Nf => matches!(actual, Ty::I64),
            EncodingFieldKind::Vm => matches!(actual, Ty::Bits(1)),
            EncodingFieldKind::Reg5 => matches!(actual, Ty::Bits(5)),
            EncodingFieldKind::Eew => {
                matches!(actual, Ty::Enum(name) if Some(*name) == shared_state.symtab.get("zvlewidth"))
            }
            EncodingFieldKind::Mop => {
                matches!(actual, Ty::Enum(name) if Some(*name) == shared_state.symtab.get("zindexed_mop"))
            }
        };
        if !matches {
            return Err(format!(
                "编码分片：{} 载荷第 {} 位应为 {:?}，IR 实际 {:?}（IR 漂移，需修订维度表）",
                clause, position, expected.kind, actual
            ));
        }
    }
    Ok(())
}

/// eew 语义值（8/16/32/64）→ zvlewidth 成员序。
fn eew_member_index(value: u64) -> Result<usize, String> {
    match value {
        8 => Ok(0),
        16 => Ok(1),
        32 => Ok(2),
        64 => Ok(3),
        _ => Err(format!("eew 候选 {:#x} 不在 zvlewidth 域 {{8,16,32,64}}", value)),
    }
}

/// 全枚举模式的字段值域：nf 取内置 2..=8；vm 取 {0,1}；eew/mop 取 IR 枚举
/// 成员数（eew 映射回语义值）；rs1/vs2/vs3 是操作数字段，无枚举语义。
pub fn enumerate_domain<B: BV>(kind: EncodingFieldKind, shared_state: &SharedState<B>) -> Result<Vec<u64>, String> {
    match kind {
        EncodingFieldKind::Nf => Ok((2..=8).collect()),
        EncodingFieldKind::Vm => Ok(vec![0, 1]),
        EncodingFieldKind::Eew => {
            let name = shared_state.symtab.get("zvlewidth").ok_or("编码分片：IR 缺少 zvlewidth 枚举")?;
            let members = shared_state
                .type_info
                .enums
                .get(&name)
                .expect("防御性编程：zvlewidth 在 symtab 但不在 type_info.enums");
            // 成员序 0..=3 ↔ 语义值 8/16/32/64（eew_member_index 的一一对应）
            Ok((0..members.len()).map(|index| 8_u64 << index).collect())
        }
        EncodingFieldKind::Mop => {
            let name = shared_state.symtab.get("zindexed_mop").ok_or("编码分片：IR 缺少 zindexed_mop 枚举")?;
            let members = shared_state
                .type_info
                .enums
                .get(&name)
                .expect("防御性编程：zindexed_mop 在 symtab 但不在 type_info.enums");
            Ok((0..members.len() as u64).collect())
        }
        EncodingFieldKind::Reg5 => Err("rs1/vs2/vs3 是操作数字段，无全枚举域（用 dimensions 显式列举）".to_string()),
    }
}

/// 单字段的取值域：显式 dimensions 优先，其次 enumerate 声明的推导域。
/// 显式候选做语义合法性校验（eew ∈ {8,16,32,64}、寄存器号 ≤ 31）。
pub fn field_values<B: BV>(
    layout_field: &EncodingField,
    slice: &EncodingSliceConfig,
    shared_state: &SharedState<B>,
) -> Result<Vec<u64>, String> {
    if let Some(values) = slice.dimensions.get(layout_field.name) {
        validate_field_values(layout_field, values)?;
        return Ok(values.clone());
    }
    if slice.enumerate.iter().any(|name| name == layout_field.name) {
        return enumerate_domain(layout_field.kind, shared_state);
    }
    Err(format!("编码分片字段 {} 既不在 dimensions 也不在 enumerate", layout_field.name))
}

fn validate_field_values(layout_field: &EncodingField, values: &[u64]) -> Result<(), String> {
    for &value in values {
        match layout_field.kind {
            EncodingFieldKind::Eew => {
                eew_member_index(value)?;
            }
            EncodingFieldKind::Reg5 => {
                if value > 31 {
                    return Err(format!("字段 {} 寄存器号 {:#x} 超 5 位域", layout_field.name, value));
                }
            }
            _ => (),
        }
    }
    Ok(())
}

/// 一个分片：各字段的钉值（维度字段 + 操作数默认），label 按字段名排序拼接。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SliceAssignment {
    pub label: String,
    pub values: BTreeMap<&'static str, u64>,
}

/// 维度展开：声明为维度（enumerate/dimensions）的字段做笛卡尔积，其余字段
/// 取 operand_defaults 或内置默认。任何字段无值即配置错误（不编造）。
pub fn expand_slice_assignments<B: BV>(
    layout: &[EncodingField],
    slice: &EncodingSliceConfig,
    shared_state: &SharedState<B>,
) -> Result<Vec<SliceAssignment>, String> {
    // 非维度字段先定值；维度字段收集候选
    let mut fixed: BTreeMap<&'static str, u64> = BTreeMap::new();
    let mut dimensions: Vec<(&EncodingField, Vec<u64>)> = Vec::new();
    for layout_field in layout {
        if slice.dimensions.contains_key(layout_field.name)
            || slice.enumerate.iter().any(|name| name == layout_field.name)
        {
            dimensions.push((layout_field, field_values(layout_field, slice, shared_state)?));
        } else if let Some(value) = slice.operand_defaults.get(layout_field.name) {
            validate_field_values(layout_field, std::slice::from_ref(value))?;
            fixed.insert(layout_field.name, *value);
        } else if let Some(value) = builtin_operand_default(layout_field.name) {
            fixed.insert(layout_field.name, value);
        } else {
            return Err(format!("编码分片字段 {} 未定值：声明为维度或写入 operand_defaults", layout_field.name));
        }
    }
    // 声明了维度/操作数默认但不在布局中的字段名是配置笔误，硬失败
    for name in slice.dimensions.keys().chain(slice.enumerate.iter()).chain(slice.operand_defaults.keys()) {
        if !layout.iter().any(|layout_field| layout_field.name == name.as_str()) {
            return Err(format!("编码分片字段 {} 不在 clause {} 的维度表中", name, slice.clause));
        }
    }

    // 笛卡尔积（BTreeMap 迭代按字段名排序，标签确定性与 worker 调度无关）
    let mut assignments = vec![fixed.clone()];
    for (layout_field, values) in &dimensions {
        let mut next = Vec::with_capacity(assignments.len() * values.len());
        for assignment in &assignments {
            for value in values {
                let mut extended = assignment.clone();
                extended.insert(layout_field.name, *value);
                next.push(extended);
            }
        }
        assignments = next;
    }
    Ok(assignments
        .into_iter()
        .map(|values| SliceAssignment { label: format_assignment_label(&values), values })
        .collect())
}

fn format_assignment_label(values: &BTreeMap<&'static str, u64>) -> String {
    values.iter().map(|(name, value)| format!("{}={}", name, value)).collect::<Vec<_>>().join(",")
}

/// 按布局构造 clause 的具体 Ctor：载荷结构体逐位置填值（nf→I64、vm→bv1、
/// 寄存器号→bv5、eew/mop→枚举成员）。
pub fn build_clause_ctor<B: BV>(
    clause: &str,
    layout: &[EncodingField],
    assignment: &BTreeMap<&'static str, u64>,
    shared_state: &SharedState<B>,
) -> Result<Val<B>, String> {
    let payload_ty = clause_payload_ty(clause, shared_state)?;
    let Ty::Struct(struct_name) = payload_ty else {
        return Err(format!("编码分片：{} 载荷不是结构体元组", clause));
    };
    let fields = shared_state
        .type_info
        .structs
        .get(struct_name)
        .unwrap_or_else(|| panic!("防御性编程：载荷结构体 {:?} 不在 type_info.structs", struct_name));

    let mut values: ahash::HashMap<Name, Val<B>> =
        ahash::HashMap::with_capacity_and_hasher(fields.len(), ahash::RandomState::new());
    for (position, (field_name, _)) in fields.iter().enumerate() {
        let layout_field = layout.get(position).expect("防御性编程：布局校验已保证字段数一致");
        let value = assignment
            .get(layout_field.name)
            .copied()
            .ok_or_else(|| format!("编码分片字段 {} 未定值（构造 Ctor 前必须全量定值）", layout_field.name))?;
        let val = match layout_field.kind {
            EncodingFieldKind::Nf => Val::I64(value as i64),
            EncodingFieldKind::Vm => Val::Bits(B::new(value, 1)),
            EncodingFieldKind::Reg5 => Val::Bits(B::new(value, 5)),
            EncodingFieldKind::Eew => Val::Enum(EnumMember {
                enum_id: EnumId::from_name(
                    shared_state.symtab.get("zvlewidth").expect("防御性编程：布局校验已保证 zvlewidth 存在"),
                ),
                member: eew_member_index(value)?,
            }),
            EncodingFieldKind::Mop => Val::Enum(EnumMember {
                enum_id: EnumId::from_name(
                    shared_state.symtab.get("zindexed_mop").expect("防御性编程：布局校验已保证 zindexed_mop 存在"),
                ),
                member: value as usize,
            }),
        };
        values.insert(*field_name, val);
    }
    Ok(Val::Ctor(
        shared_state.symtab.get(&normalize_clause_name(clause)).expect("防御性编程：clause_payload_ty 已核对 ctor 名"),
        Box::new(Val::Struct(values)),
    ))
}

/// 分片 → 指令编码：构造 Ctor 经 zencdec_forwards（concrete_function_result
/// 独立 solver 执行，环境用初始具体表 + 分片钉值——与 decode_fixed_instruction
/// 同一约束：不得携带主 solver 符号）求编码位。调用侧随后仍走
/// decode_fixed_instruction 的译码回环校验（编码合法性与 clause 归属双确认）。
pub fn slice_instruction_bits<B: BV + Send + Sync>(
    clause: &str,
    layout: &[EncodingField],
    assignment: &BTreeMap<&'static str, u64>,
    prestate: &HashMap<Name, Val<B>>,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Result<FixedInstruction, String> {
    let ctor = build_clause_ctor(clause, layout, assignment, shared_state)?;
    let decode_regs = decode_register_bindings(regs, prestate, shared_state, &[]);
    let encoded = concrete_function_result("zencdec_forwards", ctor, shared_state, &decode_regs, lets)?;
    let Val::Bits(bits) = encoded else {
        return Err(format!("编码分片 {} 重新编码未得到位向量", format_assignment_label(assignment)));
    };
    let width = u32::try_from(bits.len()).expect("编码宽度超过 u32");
    let fixed = FixedInstruction { bits: bits.lower_u64(), width };
    // 与 parse_fixed_instruction_bits 同一合法性口径：32 位编码低两位必为 11
    if (width == 16 && fixed.bits & 3 == 3) || (width == 32 && fixed.bits & 3 != 3) {
        return Err(format!(
            "编码分片 {} 产出的编码 {:#x} 与宽度 {} 不符",
            format_assignment_label(assignment),
            fixed.bits,
            width
        ));
    }
    Ok(fixed)
}

/// 计算一个 clause 的编码分片批序列：None = 该 clause 无分片声明（走既有
/// value_hints/自由批计划）。Some 时批序列 = [自由对照批] + 每片一批：
/// instruction 钉死该片编码、prestate 为 CLI 固定初态 + 分片寄存器钉值的
/// 并集（同寄存器重复钉值是歧义配置，硬失败）。
pub fn plan_slice_batches<'ir, B: BV + Send + Sync>(
    slices: &[EncodingSliceConfig],
    clause: &str,
    shared_state: &SharedState<'ir, B>,
    regs: &RegisterBindings<'ir, B>,
    lets: &Bindings<'ir, B>,
    cli_prestate: &HashMap<Name, Val<B>>,
    cli_instruction: Option<FixedInstruction>,
) -> Result<Option<Vec<SolveBatch<B>>>, String> {
    let matching: Vec<&EncodingSliceConfig> =
        slices.iter().filter(|slice| normalize_clause_name(&slice.clause) == clause).collect();
    if matching.is_empty() {
        return Ok(None);
    }
    if cli_instruction.is_some() {
        return Err("--instruction-bits 与 [[encoding_slices]] 不能同时使用（编码来源歧义）".to_string());
    }

    let mut batches = vec![SolveBatch {
        label: None,
        prestate: cli_prestate.clone(),
        instruction: None,
        case_limit: None,
        timeout: None,
    }];
    // 同 clause 多条声明可能产生相同维度组合（如仅 prestate 不同——EMUL 变体
    // 经 vtype 钉值区分），标签追加 # 序号消歧，保证 JSON 的 encoding-slice
    // 字段可区分
    let mut seen_labels: HashMap<String, u32> = HashMap::new();
    for slice in matching {
        let layout = clause_layout(clause).ok_or_else(|| {
            format!("编码分片：clause {} 无内置维度表（可扩展 encoding_slices::clause_layout）", clause)
        })?;
        validate_layout_against_ir(clause, layout, shared_state)?;

        // 分片寄存器钉值按 --prestate 语法解析并严格校验
        let prestate_args: Vec<String> =
            slice.prestate.iter().map(|(register, value)| format!("{} = {}", register, value)).collect();
        let slice_prestate = super::exec::parse_fixed_prestate(&prestate_args, shared_state, regs, lets)
            .map_err(|error| format!("编码分片 {} 的 prestate 钉值无效: {}", slice.clause, error))?;
        for (name, _) in &slice_prestate {
            if cli_prestate.contains_key(name) {
                return Err(format!(
                    "编码分片 {} 的 prestate 钉值 {} 与 --prestate 重复（同一寄存器两个来源）",
                    slice.clause,
                    zencode::decode(shared_state.symtab.to_str(*name))
                ));
            }
        }

        for assignment in expand_slice_assignments(layout, slice, shared_state)? {
            let mut prestate = cli_prestate.clone();
            prestate.extend(slice_prestate.clone());
            let instruction =
                slice_instruction_bits(clause, layout, &assignment.values, &prestate, shared_state, regs, lets)?;
            let occurrence = seen_labels.entry(assignment.label.clone()).or_insert(0);
            *occurrence += 1;
            let label = if *occurrence == 1 {
                assignment.label.clone()
            } else {
                format!("{}#{}", assignment.label, occurrence)
            };
            batches.push(SolveBatch {
                label: Some(format!("enc-slice:{}", label)),
                prestate,
                instruction: Some(instruction),
                case_limit: slice.case_limit,
                timeout: slice.timebox_s,
            });
        }
    }
    Ok(Some(batches))
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::bitvector::b64::B64;

    /// 最小 IR：zinstruction union（zVSSEGTYPE/zVSXSEGTYPE 载荷元组）、
    /// zvlewidth/zindexed_mop 枚举、vtype 寄存器、常量版 zencdec_forwards
    /// （返回固定编码位，只验证装配管线，真实编码由集成运行覆盖）。
    fn mini_shared_state() -> SharedState<'static, B64> {
        let mut symtab = Symtab::new();
        let seg_struct: &'static str = "ztuple_seg5";
        let idx_struct: &'static str = "ztuple_idxseg7";
        let seg_struct_name = symtab.intern(seg_struct);
        let idx_struct_name = symtab.intern(idx_struct);
        let zinstruction = symtab.intern("zinstruction");
        let vsseg = symtab.intern("zVSSEGTYPE");
        let vsxseg = symtab.intern("zVSXSEGTYPE");
        let vlewidth = symtab.intern("zvlewidth");
        let indexed_mop = symtab.intern("zindexed_mop");
        let forwards = symtab.intern("zencdec_forwards");
        let arg = symtab.intern("zarg");
        let vtype = symtab.intern(Box::leak(zencode::encode("vtype").into_boxed_str()));
        let x6 = symtab.intern(Box::leak(zencode::encode("x6").into_boxed_str()));
        // 载荷字段名（位置序 intern，BTreeMap 按 Name 序即位置序）
        let seg_fields: Vec<Name> =
            (0..5).map(|i| symtab.intern(Box::leak(format!("{}_{}", seg_struct, i).into_boxed_str()))).collect();
        let idx_fields: Vec<Name> =
            (0..7).map(|i| symtab.intern(Box::leak(format!("{}_{}", idx_struct, i).into_boxed_str()))).collect();

        let defs: &'static [Def<Name, B64>] = Box::leak(
            vec![
                Def::Enum(
                    vlewidth,
                    vec![
                        symtab.intern("zVLE8"),
                        symtab.intern("zVLE16"),
                        symtab.intern("zVLE32"),
                        symtab.intern("zVLE64"),
                    ],
                ),
                Def::Enum(indexed_mop, vec![symtab.intern("zINDEXED_UNORDERED"), symtab.intern("zINDEXED_ORDERED")]),
                Def::Struct(
                    seg_struct_name,
                    vec![
                        (seg_fields[0], Ty::I64),
                        (seg_fields[1], Ty::Bits(1)),
                        (seg_fields[2], Ty::Bits(5)),
                        (seg_fields[3], Ty::Enum(vlewidth)),
                        (seg_fields[4], Ty::Bits(5)),
                    ],
                ),
                Def::Struct(
                    idx_struct_name,
                    vec![
                        (idx_fields[0], Ty::I64),
                        (idx_fields[1], Ty::Bits(1)),
                        (idx_fields[2], Ty::Bits(5)),
                        (idx_fields[3], Ty::Bits(5)),
                        (idx_fields[4], Ty::Enum(vlewidth)),
                        (idx_fields[5], Ty::Bits(5)),
                        (idx_fields[6], Ty::Enum(indexed_mop)),
                    ],
                ),
                Def::Register(vtype, Ty::Bits(64), Vec::new()),
                Def::Register(x6, Ty::Bits(64), Vec::new()),
                Def::Val(forwards, vec![Ty::Unit], Ty::Bits(32)),
                Def::Fn(
                    forwards,
                    vec![arg],
                    vec![
                        Instr::Copy(Loc::Id(RETURN), Exp::Bits(B64::new(0x4203_6327, 32)), SourceLoc::unknown()),
                        Instr::End,
                    ],
                ),
            ]
            .into_boxed_slice(),
        );
        let mut type_info = IRTypeInfo::new(defs);
        // 手工装配 union 载荷（ctors 需引用上面的结构体类型）
        type_info
            .unions
            .insert(zinstruction, vec![(vsseg, Ty::Struct(seg_struct_name)), (vsxseg, Ty::Struct(idx_struct_name))]);
        SharedState::new(
            symtab,
            defs,
            type_info,
            Default::default(),
            Default::default(),
            Default::default(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
    }

    fn slice_config(clause: &str) -> EncodingSliceConfig {
        EncodingSliceConfig {
            clause: clause.to_string(),
            enumerate: Vec::new(),
            dimensions: BTreeMap::new(),
            operand_defaults: BTreeMap::new(),
            prestate: BTreeMap::new(),
            case_limit: None,
            timebox_s: None,
        }
    }

    /// 布局表与 IR 类型核对：字段数/逐位类型不符（IR 漂移）硬失败。
    #[test]
    fn 布局校验_类型漂移报错() {
        let shared_state = mini_shared_state();
        assert!(validate_layout_against_ir("zVSSEGTYPE", clause_layout("zVSSEGTYPE").unwrap(), &shared_state).is_ok());
        assert!(validate_layout_against_ir("zVSXSEGTYPE", clause_layout("zVSXSEGTYPE").unwrap(), &shared_state).is_ok());
        // 交叉布局（段 clause 用索引布局）字段数不符
        assert!(validate_layout_against_ir("zVSSEGTYPE", clause_layout("zVSXSEGTYPE").unwrap(), &shared_state).is_err());
        // 未知 clause 无布局
        assert!(clause_layout("zAMOTYPE").is_none());
    }

    /// 维度展开：全枚举 nf×eew = 7×4；显式钉值域生效；非法候选与配置笔误
    /// 硬失败；标签按字段名排序。
    #[test]
    fn 维度展开_全枚举与显式钉值() {
        let shared_state = mini_shared_state();
        let layout = clause_layout("zVSSEGTYPE").unwrap();
        let mut slice = slice_config("VSSEGTYPE");
        slice.enumerate = vec!["nf".to_string(), "eew".to_string()];
        let assignments = expand_slice_assignments(layout, &slice, &shared_state).unwrap();
        assert_eq!(assignments.len(), 28, "nf(2..=8) × eew(4)");
        let target =
            assignments.iter().find(|a| a.label == "eew=32,nf=3,rs1=6,vm=1,vs3=8").expect("必须含 vsseg3e32 对应组合");
        assert_eq!(target.values.get("nf"), Some(&3));
        assert_eq!(target.values.get("eew"), Some(&32));

        // 显式钉值缩小域：nf∈{2,3}、eew∈{32}
        slice.enumerate.clear();
        slice.dimensions = BTreeMap::from([("nf".to_string(), vec![2, 3]), ("eew".to_string(), vec![32])]);
        let assignments = expand_slice_assignments(layout, &slice, &shared_state).unwrap();
        assert_eq!(assignments.len(), 2);
        assert!(assignments.iter().all(|a| a.values.get("eew") == Some(&32)));

        // 非法候选：eew=24 / rs1=40
        slice.dimensions = BTreeMap::from([("nf".to_string(), vec![2]), ("eew".to_string(), vec![24])]);
        assert!(expand_slice_assignments(layout, &slice, &shared_state).is_err());
        slice.dimensions =
            BTreeMap::from([("rs1".to_string(), vec![40]), ("nf".to_string(), vec![2]), ("eew".to_string(), vec![8])]);
        assert!(expand_slice_assignments(layout, &slice, &shared_state).is_err());
        // 操作数字段无全枚举域
        slice.dimensions = BTreeMap::new();
        slice.enumerate = vec!["rs1".to_string()];
        assert!(expand_slice_assignments(layout, &slice, &shared_state).is_err());
        // 未定值字段（eew 无内置默认）
        slice.enumerate.clear();
        assert!(expand_slice_assignments(layout, &slice, &shared_state).is_err());
        // 配置笔误：不在布局中的字段名
        slice.dimensions =
            BTreeMap::from([("nf".to_string(), vec![2]), ("eew".to_string(), vec![8]), ("mop".to_string(), vec![0])]);
        assert!(expand_slice_assignments(layout, &slice, &shared_state).is_err());
    }

    /// Ctor 构造：逐位置类型正确（I64/bv1/bv5/枚举成员序）。
    #[test]
    fn ctor构造_位置与类型() {
        let shared_state = mini_shared_state();
        let layout = clause_layout("zVSXSEGTYPE").unwrap();
        let values =
            BTreeMap::from([("nf", 3), ("vm", 0), ("rs1", 6), ("vs2", 7), ("eew", 32), ("vs3", 8), ("mop", 1)]);
        let ctor = build_clause_ctor::<B64>("zVSXSEGTYPE", layout, &values, &shared_state).unwrap();
        let Val::Ctor(ctor_name, payload) = ctor else { panic!("应构造 Ctor") };
        assert_eq!(ctor_name, shared_state.symtab.lookup("zVSXSEGTYPE"));
        let Val::Struct(fields) = *payload else { panic!("载荷应为结构体") };
        let payload_ty = clause_payload_ty("zVSXSEGTYPE", &shared_state).unwrap();
        let Ty::Struct(struct_name) = payload_ty else { panic!("载荷应为结构体元组") };
        let ordered: Vec<&Val<B64>> = shared_state
            .type_info
            .structs
            .get(struct_name)
            .unwrap()
            .keys()
            .map(|field_name| fields.get(field_name).unwrap())
            .collect();
        assert_eq!(ordered[0], &Val::I64(3));
        assert_eq!(ordered[1], &Val::Bits(B64::new(0, 1)));
        assert_eq!(ordered[2], &Val::Bits(B64::new(6, 5)));
        assert_eq!(ordered[3], &Val::Bits(B64::new(7, 5)));
        match ordered[4] {
            Val::Enum(member) => {
                assert_eq!(member.member, 2, "eew=32 → zvlewidth 成员序 2");
                assert_eq!(member.enum_id.to_name(), shared_state.symtab.lookup("zvlewidth"));
            }
            other => panic!("eew 应为枚举成员: {:?}", other),
        }
        assert_eq!(ordered[5], &Val::Bits(B64::new(8, 5)));
        match ordered[6] {
            Val::Enum(member) => assert_eq!(member.member, 1, "mop=1 → zINDEXED_ORDERED"),
            other => panic!("mop 应为枚举成员: {:?}", other),
        }
    }

    /// 分片批计划：自由批 + 每片一批；编码经 zencdec_forwards（常量桩）产出；
    /// --instruction-bits 冲突与 prestate 重复钉值硬失败；无声明 clause 返回
    /// None；无内置维度表的 clause 声明分片硬失败。
    #[test]
    fn 分片批计划_装配与冲突() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let shared_state = mini_shared_state();
        // 寄存器绑定表按真实初始化形态预置（decode_register_bindings 只对已存在
        // 的寄存器 assign，与 setup_pre_state 同一约定）
        let mut regs = RegisterBindings::new();
        let ty = Ty::<Name>::Bits(64);
        regs.insert(shared_state.symtab.get(&zencode::encode("vtype")).unwrap(), false, UVal::Uninit(&ty));
        regs.insert(shared_state.symtab.get(&zencode::encode("x6")).unwrap(), false, UVal::Uninit(&ty));
        let lets = Bindings::default();
        // 无声明 clause
        assert!(plan_slice_batches(&[], "zVSSEGTYPE", &shared_state, &regs, &lets, &HashMap::new(), None)
            .unwrap()
            .is_none());

        let mut slice = slice_config("VSSEGTYPE");
        slice.enumerate = vec!["nf".to_string()];
        slice.dimensions = BTreeMap::from([("eew".to_string(), vec![32])]);
        slice.prestate = BTreeMap::from([("vtype".to_string(), "0x0000000000000010".to_string())]);
        slice.case_limit = Some(2);
        slice.timebox_s = Some(30);
        let batches =
            plan_slice_batches(&[slice.clone()], "zVSSEGTYPE", &shared_state, &regs, &lets, &HashMap::new(), None)
                .unwrap()
                .expect("应有分片批");
        assert_eq!(batches.len(), 8, "自由批 + nf(2..=8)×eew(32) 共 7 片");
        assert_eq!(batches[0].label, None);
        assert!(batches[0].instruction.is_none());
        let third = &batches[2];
        assert_eq!(third.label.as_deref(), Some("enc-slice:eew=32,nf=3,rs1=6,vm=1,vs3=8"));
        assert_eq!(third.instruction, Some(FixedInstruction { bits: 0x4203_6327, width: 32 }));
        assert_eq!(third.case_limit, Some(2));
        assert_eq!(third.timeout, Some(30));
        assert!(third.prestate.contains_key(&shared_state.symtab.get(&zencode::encode("vtype")).unwrap()));

        // CLI --instruction-bits 与分片声明冲突
        assert!(plan_slice_batches(
            &[slice.clone()],
            "zVSSEGTYPE",
            &shared_state,
            &regs,
            &lets,
            &HashMap::new(),
            Some(FixedInstruction { bits: 0x4203_6327, width: 32 })
        )
        .is_err());

        // CLI --prestate 与分片 prestate 同寄存器重复
        let x6_name = shared_state.symtab.get(&zencode::encode("x6")).unwrap();
        let cli_prestate = HashMap::from([(x6_name, Val::Bits(B64::new(0x8000_0000, 64)))]);
        let mut conflicting = slice.clone();
        conflicting.prestate.insert("x6".to_string(), "0x0000000080010000".to_string());
        assert!(
            plan_slice_batches(&[conflicting], "zVSSEGTYPE", &shared_state, &regs, &lets, &cli_prestate, None).is_err()
        );

        // 无内置维度表的 clause 声明分片 → 硬失败
        let unknown = EncodingSliceConfig { clause: "AMOTYPE".to_string(), ..slice.clone() };
        assert!(plan_slice_batches(&[unknown], "zAMOTYPE", &shared_state, &regs, &lets, &HashMap::new(), None).is_err());

        // 两条同 clause 声明产生相同维度组合（如仅 prestate 不同）时，标签
        // 追加 # 序号消歧，JSON 的 encoding-slice 字段保持可区分
        let mut second = slice_config("VSSEGTYPE");
        second.enumerate = vec!["nf".to_string()];
        second.dimensions = BTreeMap::from([("eew".to_string(), vec![32])]);
        second.prestate = BTreeMap::from([("vtype".to_string(), "0x0000000000000011".to_string())]);
        let batches =
            plan_slice_batches(&[slice, second], "zVSSEGTYPE", &shared_state, &regs, &lets, &HashMap::new(), None)
                .unwrap()
                .expect("应有分片批");
        assert_eq!(batches.len(), 15, "自由批 + 7 片 × 2 条声明");
        let labels: Vec<&str> = batches.iter().filter_map(|batch| batch.label.as_deref()).collect();
        let unique: std::collections::HashSet<&str> = labels.iter().copied().collect();
        assert_eq!(labels.len(), unique.len(), "标签必须唯一");
        assert!(labels.contains(&"enc-slice:eew=32,nf=3,rs1=6,vm=1,vs3=8#2"), "重复组合追加 # 序号");
    }
}
