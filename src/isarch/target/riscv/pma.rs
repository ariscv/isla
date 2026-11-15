use isla_lib::bitvector::BV;
use isla_lib::config::{allowed_table_keys, parse_u64_value};
use isla_lib::ir::{IRTypeInfo, Name, SharedState, Symtab, Ty, Val};
use isla_lib::register::RegisterBindings;
use isla_lib::smt::{smtlib, EnumId, EnumMember, Solver, Sym};
use isla_lib::source_loc::SourceLoc;
use isla_lib::zencode;
use std::collections::HashMap;
use std::str::FromStr;
use toml::Value;

/// `zmisaligned_fault` 枚举（IR rv64d.ir:671）的配置镜像。模型字段语义见
/// zpmaCheck：NoFault 不因未对齐 trap；AccessFault/AlignmentFault 在地址
/// 未对齐时分别转 access/alignment fault。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PmaMisalignedFault {
    NoFault,
    AccessFault,
    AlignmentFault,
}

impl FromStr for PmaMisalignedFault {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "no_fault" => Ok(PmaMisalignedFault::NoFault),
            "access_fault" => Ok(PmaMisalignedFault::AccessFault),
            "alignment_fault" => Ok(PmaMisalignedFault::AlignmentFault),
            _ => Err(format!("Unknown PMA misaligned policy {}", s)),
        }
    }
}

/// `zReservability` 枚举（IR rv64d.ir:3161）的配置镜像。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PmaReservability {
    None,
    NonEventual,
    Eventual,
}

impl FromStr for PmaReservability {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "none" => Ok(PmaReservability::None),
            "non_eventual" => Ok(PmaReservability::NonEventual),
            "eventual" => Ok(PmaReservability::Eventual),
            _ => Err(format!("Unknown PMA reservability {}", s)),
        }
    }
}

/// PMA 支持的 AMO 等级；CAS 等级包含经典 AMO，并分别限定 CAS 最大宽度。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PmaAtomicSupport {
    None,
    Swap,
    Logical,
    Arithmetic,
    CasW,
    CasD,
    CasQ,
}

impl FromStr for PmaAtomicSupport {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "none" => Ok(Self::None),
            "swap" => Ok(Self::Swap),
            "logical" => Ok(Self::Logical),
            "arithmetic" => Ok(Self::Arithmetic),
            "cas_w" => Ok(Self::CasW),
            "cas_d" => Ok(Self::CasD),
            "cas_q" => Ok(Self::CasQ),
            _ => Err(format!("未知 PMA atomic_support {}", s)),
        }
    }
}

/// `zPMA` record（IR rv64d.ir:3295）的配置镜像：别名（ram/rom/mmio/hole）
/// 与明细字段都解析到这个结构。字段语义由模型 zpmaCheck 消费。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PmaAttributes {
    pub readable: bool,
    pub writable: bool,
    pub executable: bool,
    pub cacheable: bool,
    pub coherent: bool,
    pub read_idempotent: bool,
    pub write_idempotent: bool,
    pub supports_cbo_zzero: bool,
    pub misaligned_fault: PmaMisalignedFault,
    pub reservability: PmaReservability,
    pub atomic_support: PmaAtomicSupport,
    pub include_in_device_tree: bool,
}

impl PmaAttributes {
    /// attr 别名底座。ram/mmio 镜像 IR 固化 zpma_regions 默认 region 的属性，
    /// rom/hole 取最保守值（rom 只读；hole 全 false）。
    fn from_alias(alias: &str) -> Option<PmaAttributes> {
        let attributes = match alias {
            "ram" => PmaAttributes {
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
                atomic_support: PmaAtomicSupport::CasQ,
                include_in_device_tree: true,
            },
            "rom" => PmaAttributes {
                readable: true,
                writable: false,
                executable: false,
                cacheable: true,
                coherent: true,
                read_idempotent: true,
                write_idempotent: true,
                supports_cbo_zzero: false,
                misaligned_fault: PmaMisalignedFault::NoFault,
                reservability: PmaReservability::None,
                atomic_support: PmaAtomicSupport::CasQ,
                include_in_device_tree: false,
            },
            "mmio" => PmaAttributes {
                readable: true,
                writable: true,
                executable: false,
                cacheable: false,
                coherent: true,
                read_idempotent: false,
                write_idempotent: false,
                supports_cbo_zzero: false,
                misaligned_fault: PmaMisalignedFault::AlignmentFault,
                reservability: PmaReservability::None,
                atomic_support: PmaAtomicSupport::CasQ,
                include_in_device_tree: false,
            },
            "hole" => PmaAttributes {
                readable: false,
                writable: false,
                executable: false,
                cacheable: false,
                coherent: false,
                read_idempotent: false,
                write_idempotent: false,
                supports_cbo_zzero: false,
                misaligned_fault: PmaMisalignedFault::NoFault,
                reservability: PmaReservability::None,
                atomic_support: PmaAtomicSupport::CasQ,
                include_in_device_tree: false,
            },
            _ => return None,
        };
        Some(attributes)
    }

    /// 无 attr 明细模式的基线：布尔位除 include_in_device_tree=true 外全 false，AMO 等级保持旧平台范围。
    fn detailed_default() -> PmaAttributes {
        PmaAttributes {
            readable: false,
            writable: false,
            executable: false,
            cacheable: false,
            coherent: false,
            read_idempotent: false,
            write_idempotent: false,
            supports_cbo_zzero: false,
            misaligned_fault: PmaMisalignedFault::NoFault,
            reservability: PmaReservability::None,
            atomic_support: PmaAtomicSupport::CasQ,
            include_in_device_tree: true,
        }
    }
}

/// `zPMA_Region` record（IR rv64d.ir:3309）的配置镜像：base+size 布局
/// （非 base+end），属性见 [PmaAttributes]。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PmaRegionConfig {
    pub name: String,
    pub base: u64,
    pub size: PmaSize,
    pub attributes: PmaAttributes,
    /// 平台 atomic 位；声明后映射到 AMO 权限和 LR/SC 权限。
    pub atomic: Option<bool>,
    pub backing: Option<PmaBacking>,
}

/// S2（W17）：[[pma_regions]] 的 size 字段。`Concrete` 为固定值（W10 行为）；
/// `Symbolic` 把 IR 字段 zsizze 声明为 64 位符号常量，并在注入时附加闭区间
/// 取值域约束 [min, max]（bvule）——默认域防全 64 位空间稀释求解。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PmaSize {
    Concrete(u64),
    Symbolic { min: u64, max: u64 },
}

impl PmaSize {
    /// 取值域上界（具体 size 即自身）：重叠自校验用符号域上界做保守检查，
    /// 保证任意模型取值下相邻 region 都不重叠。
    fn upper_bound(&self) -> u64 {
        match self {
            PmaSize::Concrete(size) => *size,
            PmaSize::Symbolic { max, .. } => *max,
        }
    }
}

/// 符号 size 未声明 size_bounds 时的默认取值域：[4KiB, 2^43]（闭区间）。
/// 上界 2^43 锚定 W13 实测的 emu RAM 顶界（SimMemSize 8190GiB），下界 4KiB
/// 是最小页粒度（size=0 的 region 无意义，与具体路径的 size>0 校验一致）。
const SYMBOLIC_SIZE_DEFAULT_MIN: u64 = 0x1000;
const SYMBOLIC_SIZE_DEFAULT_MAX: u64 = 0x80000000000;

/// 区域实际接线的元数据；本阶段不据此改变模型或 testcase 接纳。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PmaBacking {
    Memory,
    DeviceBus,
    Denied,
}

/// 解析 `[[pma_regions]]`（W10/S1 配置化 PMA 地图）。返回的列表按 base 降序
/// （与 IR 固化 zpma_regions 列表次序一致），并完成 size/溢出/重叠自校验——
/// isarch 不经过模型的 zcheck_mem_layout，排序与重叠检查必须在配置解析做。
pub fn get_pma_regions(config: &Value) -> Result<Option<Vec<PmaRegionConfig>>, String> {
    let Some(pma_regions) = config.get("pma_regions") else { return Ok(None) };
    let Some(pma_regions) = pma_regions.as_array() else {
        return Err("pma_regions should be an array of tables".to_string());
    };

    let mut regions = Vec::with_capacity(pma_regions.len());
    for (index, region) in pma_regions.iter().enumerate() {
        let Some(region) = region.as_table() else {
            return Err("pma_regions should be an array of tables".to_string());
        };

        allowed_table_keys(
            region,
            "[[pma_regions]]",
            &[
                "atomic",
                "atomic_support",
                "backing",
                "name",
                "base",
                "size",
                "size_bounds",
                "attr",
                "readable",
                "writable",
                "executable",
                "cacheable",
                "coherent",
                "read_idempotent",
                "write_idempotent",
                "supports_cbo_zero",
                "misaligned",
                "reservability",
                "include_in_device_tree",
            ],
        )?;

        let name =
            region.get("name").and_then(Value::as_str).map(str::to_string).unwrap_or_else(|| format!("pma{}", index));
        let context = format!("pma_regions.{}", name);
        let base = region
            .get("base")
            .ok_or_else(|| format!("No {}.base found", context))
            .and_then(|value| parse_u64_value(value, &format!("{}.base", context)))?;
        // S2（W17）：size = "symbolic" 声明符号边界（可选 size_bounds = [下界, 上界]
        // 闭区间），其余写法仍是 W10 的具体十六进制。
        let size = match region.get("size") {
            Some(Value::String(text)) if text == "symbolic" => {
                let (min, max) = match region.get("size_bounds") {
                    None => (SYMBOLIC_SIZE_DEFAULT_MIN, SYMBOLIC_SIZE_DEFAULT_MAX),
                    Some(Value::Array(bounds)) if bounds.len() == 2 => {
                        let min = parse_u64_value(&bounds[0], &format!("{}.size_bounds[0]", context))?;
                        let max = parse_u64_value(&bounds[1], &format!("{}.size_bounds[1]", context))?;
                        (min, max)
                    }
                    Some(_) => {
                        return Err(format!("{}.size_bounds should be an array of two integers", context));
                    }
                };
                if min == 0 {
                    return Err(format!("{}.size_bounds lower bound must be greater than 0", context));
                }
                if min > max {
                    return Err(format!(
                        "{}.size_bounds lower bound 0x{:x} exceeds upper bound 0x{:x}",
                        context, min, max
                    ));
                }
                if base.checked_add(max).is_none() {
                    return Err(format!("{}.base + size_bounds upper bound overflows 64-bit address space", context));
                }
                PmaSize::Symbolic { min, max }
            }
            Some(value) => {
                if region.contains_key("size_bounds") {
                    return Err(format!("{}.size_bounds 只能与 size = \"symbolic\" 搭配", context));
                }
                let size = parse_u64_value(value, &format!("{}.size", context))?;
                if size == 0 {
                    return Err(format!("{}.size must be greater than 0", context));
                }
                if base.checked_add(size).is_none() {
                    return Err(format!("{}.base + size overflows 64-bit address space", context));
                }
                PmaSize::Concrete(size)
            }
            None => return Err(format!("No {}.size found", context)),
        };

        // attr 别名给底座（无 attr 用明细模式基线），明细字段逐项覆盖
        let mut attributes = match region.get("attr") {
            Some(Value::String(alias)) => PmaAttributes::from_alias(alias)
                .ok_or_else(|| format!("Unknown PMA attr alias {} in {}", alias, context))?,
            Some(_) => return Err(format!("{}.attr should be a string", context)),
            None => PmaAttributes::detailed_default(),
        };
        let mut has_detail = false;
        let bool_field = |region: &toml::value::Table, key: &str| -> Result<Option<bool>, String> {
            match region.get(key) {
                Some(Value::Boolean(b)) => Ok(Some(*b)),
                Some(_) => Err(format!("{}.{} should be a boolean", context, key)),
                None => Ok(None),
            }
        };
        for (key, target) in [
            ("readable", &mut attributes.readable),
            ("writable", &mut attributes.writable),
            ("executable", &mut attributes.executable),
            ("cacheable", &mut attributes.cacheable),
            ("coherent", &mut attributes.coherent),
            ("read_idempotent", &mut attributes.read_idempotent),
            ("write_idempotent", &mut attributes.write_idempotent),
            ("supports_cbo_zero", &mut attributes.supports_cbo_zzero),
            ("include_in_device_tree", &mut attributes.include_in_device_tree),
        ] {
            if let Some(value) = bool_field(region, key)? {
                *target = value;
                has_detail = true;
            }
        }
        match region.get("misaligned") {
            Some(Value::String(s)) => {
                attributes.misaligned_fault = s.parse::<PmaMisalignedFault>()?;
                has_detail = true;
            }
            Some(_) => return Err(format!("{}.misaligned should be a string", context)),
            None => (),
        }
        match region.get("reservability") {
            Some(Value::String(s)) => {
                attributes.reservability = s.parse::<PmaReservability>()?;
                has_detail = true;
            }
            Some(_) => return Err(format!("{}.reservability should be a string", context)),
            None => (),
        }
        let atomic = bool_field(region, "atomic")?;
        // 未配置的新字段保持旧平台的 AMO 接纳范围；显式 atomic=true 只保证经典 AMO。
        attributes.atomic_support = match region.get("atomic_support") {
            Some(Value::String(s)) => {
                has_detail = true;
                s.parse::<PmaAtomicSupport>()?
            }
            Some(_) => return Err(format!("{}.atomic_support 应为字符串", context)),
            None => match atomic {
                Some(false) => PmaAtomicSupport::None,
                Some(true) => PmaAtomicSupport::Arithmetic,
                None => PmaAtomicSupport::CasQ,
            },
        };
        if atomic == Some(false) {
            if attributes.atomic_support != PmaAtomicSupport::None
                || (region.contains_key("reservability") && attributes.reservability != PmaReservability::None)
            {
                return Err(format!("{}.atomic=false 与原子权限明细冲突", context));
            }
            attributes.reservability = PmaReservability::None;
        }
        if !region.contains_key("attr") && !has_detail {
            return Err(format!("{} 需要 attr 别名或至少一个明细属性字段", context));
        }

        let backing = match region.get("backing") {
            None => None,
            Some(Value::String(value)) => Some(match value.as_str() {
                "memory" => PmaBacking::Memory,
                "device_bus" => PmaBacking::DeviceBus,
                "denied" => PmaBacking::Denied,
                _ => return Err(format!("{}.backing 未知接线 {}", context, value)),
            }),
            Some(_) => return Err(format!("{}.backing 应为字符串", context)),
        };
        regions.push(PmaRegionConfig { name, base, size, attributes, atomic, backing });
    }

    // 按 base 降序（IR 固化 zpma_regions 的列表次序），再做相邻重叠检查。
    // 区间按起点排序后，任意重叠必然产生一对相邻重叠。符号 size 用取值域上界
    // 参与检查（保守：任意模型取值下都不重叠）。
    regions.sort_by(|a, b| b.base.cmp(&a.base));
    for pair in regions.windows(2) {
        let (upper, lower) = (&pair[0], &pair[1]);
        let lower_end = lower.base.checked_add(lower.size.upper_bound()).expect("已校验 base+size 上界不溢出");
        if lower_end > upper.base {
            return Err(format!(
                "pma_regions.{} [0x{:x},0x{:x}) 与 pma_regions.{} [0x{:x},0x{:x}) 重叠",
                upper.name,
                upper.base,
                upper.base + upper.size.upper_bound(),
                lower.name,
                lower.base,
                lower_end
            ));
        }
    }

    Ok(Some(regions))
}

/// 枚举成员的 IR 名（z 前缀）到 Val::Enum 的转换：symtab 查成员名，enum_members
/// 拿 (序号, 所在枚举)，构造与 IR 枚举身份一致的 EnumMember。
fn pma_enum_member<B: BV>(
    symtab: &Symtab,
    type_info: &IRTypeInfo,
    member_ir_name: &str,
    expected_enum: Name,
    context: &str,
) -> Result<Val<B>, String> {
    let member_name = symtab
        .get(&zencode::encode(member_ir_name))
        .ok_or_else(|| format!("IR 缺少枚举成员 {}（{}）", member_ir_name, context))?;
    let (member, _, enum_name) = type_info
        .enum_members
        .get(&member_name)
        .ok_or_else(|| format!("type_info 缺少枚举成员 {}（{}）", member_ir_name, context))?;
    if *enum_name != expected_enum {
        return Err(format!("IR 枚举成员 {} 与 {} 字段的枚举类型不匹配", member_ir_name, context));
    }
    Ok(Val::Enum(EnumMember { enum_id: EnumId::from_name(*enum_name), member: *member }))
}

/// 按 zPMA record 的字段定义，把配置属性构造成 Val::Struct。字段名从
/// type_info 取（decode 回原始名后匹配配置），IR 新增字段没有对应配置时
/// 硬报错，避免静默产出缺字段的错误地图。
fn pma_attributes_value<B: BV>(
    attributes: &PmaAttributes,
    pma_struct_name: Name,
    symtab: &Symtab,
    type_info: &IRTypeInfo,
) -> Result<Val<B>, String> {
    let struct_def = type_info
        .structs
        .get(&pma_struct_name)
        .ok_or_else(|| format!("type_info 缺少 struct {}（PMA 属性 record）", symtab.to_str(pma_struct_name)))?;

    if struct_def.len() != 11 {
        return Err("IR PMA 属性 record 缺少字段或包含未知字段".to_string());
    }
    let mut fields: ahash::HashMap<Name, Val<B>> =
        HashMap::with_capacity_and_hasher(struct_def.len(), ahash::RandomState::new());
    for (field_name, field_ty) in struct_def {
        let field = zencode::decode(symtab.to_str(*field_name));
        let value = match (field.as_str(), field_ty) {
            ("cacheable", Ty::Bool) => Val::Bool(attributes.cacheable),
            ("coherent", Ty::Bool) => Val::Bool(attributes.coherent),
            ("executable", Ty::Bool) => Val::Bool(attributes.executable),
            ("read_idempotent", Ty::Bool) => Val::Bool(attributes.read_idempotent),
            ("readable", Ty::Bool) => Val::Bool(attributes.readable),
            ("supports_cbo_zero", Ty::Bool) => Val::Bool(attributes.supports_cbo_zzero),
            ("writable", Ty::Bool) => Val::Bool(attributes.writable),
            ("write_idempotent", Ty::Bool) => Val::Bool(attributes.write_idempotent),
            ("misaligned_fault", Ty::Enum(enum_name)) => match attributes.misaligned_fault {
                PmaMisalignedFault::NoFault => {
                    pma_enum_member(symtab, type_info, "NoFault", *enum_name, "misaligned_fault")?
                }
                PmaMisalignedFault::AccessFault => {
                    pma_enum_member(symtab, type_info, "AccessFault", *enum_name, "misaligned_fault")?
                }
                PmaMisalignedFault::AlignmentFault => {
                    pma_enum_member(symtab, type_info, "AlignmentFault", *enum_name, "misaligned_fault")?
                }
            },
            ("atomic_support", Ty::Enum(enum_name)) => {
                let member = match attributes.atomic_support {
                    PmaAtomicSupport::None => "AMONone",
                    PmaAtomicSupport::Swap => "AMOSwap",
                    PmaAtomicSupport::Logical => "AMOLogical",
                    PmaAtomicSupport::Arithmetic => "AMOArithmetic",
                    PmaAtomicSupport::CasW => "AMOCASW",
                    PmaAtomicSupport::CasD => "AMOCASD",
                    PmaAtomicSupport::CasQ => "AMOCASQ",
                };
                pma_enum_member(symtab, type_info, member, *enum_name, "atomic_support")?
            }
            ("reservability", Ty::Enum(enum_name)) => match attributes.reservability {
                PmaReservability::None => pma_enum_member(symtab, type_info, "RsrvNone", *enum_name, "reservability")?,
                PmaReservability::NonEventual => {
                    pma_enum_member(symtab, type_info, "RsrvNonEventual", *enum_name, "reservability")?
                }
                PmaReservability::Eventual => {
                    pma_enum_member(symtab, type_info, "RsrvEventual", *enum_name, "reservability")?
                }
            },
            _ => return Err(format!("zPMA 字段 {}（类型 {:?}）无法从 [[pma_regions]] 配置映射", field, field_ty)),
        };
        fields.insert(*field_name, value);
    }
    Ok(Val::Struct(fields))
}

/// 把配置的 [[pma_regions]] 构造成 zpma_regions 寄存器的值：
/// `Val::List(vec![Val::Struct(zPMA_Region {...})])`。字段名/类型全部从
/// symtab + type_info 查（结构同 generate_default_value 的按 Ty 递归构造，
/// 但取配置值）；配置列表的次序（解析时已按 base 降序）原样保留。
/// zsizze 字段值由调用方逐 region 提供（size_values，与 regions 一一对应）：
/// 具体路径给 Val::Bits，符号路径给声明好的 Val::Symbolic。
fn pma_regions_list_value<B: BV>(
    regions: &[PmaRegionConfig],
    size_values: &[Val<B>],
    symtab: &Symtab,
    type_info: &IRTypeInfo,
) -> Result<Val<B>, String> {
    if regions.len() != size_values.len() {
        panic!("防御性编程：size_values 长度 {} 与 regions 长度 {} 不一致", size_values.len(), regions.len());
    }
    let region_struct_name = symtab
        .get(&zencode::encode("PMA_Region"))
        .ok_or_else(|| "symtab 缺少 struct PMA_Region：当前 IR 不含 zpma_regions 模型".to_string())?;
    let struct_def = type_info
        .structs
        .get(&region_struct_name)
        .ok_or_else(|| "type_info 缺少 struct PMA_Region 定义".to_string())?;

    if struct_def.len() != 4 {
        return Err("IR PMA_Region record 缺少字段或包含未知字段".to_string());
    }
    let mut items = Vec::with_capacity(regions.len());
    for (region, size_value) in regions.iter().zip(size_values) {
        let mut fields: ahash::HashMap<Name, Val<B>> =
            HashMap::with_capacity_and_hasher(struct_def.len(), ahash::RandomState::new());
        for (field_name, field_ty) in struct_def {
            let field = zencode::decode(symtab.to_str(*field_name));
            let value = match (field.as_str(), field_ty) {
                ("attributes", Ty::Struct(pma_struct_name)) => {
                    pma_attributes_value(&region.attributes, *pma_struct_name, symtab, type_info)?
                }
                ("base", Ty::Bits(64)) => Val::Bits(B::new(region.base, 64)),
                ("size", Ty::Bits(64)) => size_value.clone(),
                ("include_in_device_tree", Ty::Bool) => Val::Bool(region.attributes.include_in_device_tree),
                _ => {
                    return Err(format!(
                        "zPMA_Region 字段 {}（类型 {:?}）无法从 [[pma_regions]] 配置映射",
                        field, field_ty
                    ))
                }
            };
            fields.insert(*field_name, value);
        }
        items.push(Val::Struct(fields));
    }
    Ok(Val::List(items))
}

/// W10（S1）：[[pma_regions]] 配置注入。把配置地图构造成 list-of-records 值写入
/// default_registers 的 zpma_regions 键——solve-state 启动时
/// initialize_architecture/initialize_register 用它替代 IR 固化默认地图，模型
/// 的 zpmaCheck/zmatching_pma 逻辑零改动。未配置时调用方不调本函数，沿用 IR
/// 固化默认。只接受全具体 size（符号边界走执行期注入
/// apply_symbolic_pma_regions_to_registers）。
pub fn apply_pma_regions_to_config<B: BV>(
    regions: &[PmaRegionConfig],
    symtab: &Symtab,
    type_info: &IRTypeInfo,
    default_registers: &mut HashMap<Name, Val<B>>,
) -> Result<(), String> {
    let size_values: Vec<Val<B>> = regions
        .iter()
        .map(|region| match region.size {
            PmaSize::Concrete(size) => Val::Bits(B::new(size, 64)),
            PmaSize::Symbolic { .. } => {
                panic!("防御性编程：具体注入路径不得收到 symbolic size（region {}）", region.name)
            }
        })
        .collect();
    let list = pma_regions_list_value(regions, &size_values, symtab, type_info)?;
    // IR 寄存器名 zpma_regions 即 zencode("pma_regions")。
    let name = symtab
        .get(&zencode::encode("pma_regions"))
        .ok_or_else(|| "Could not find register pma_regions when applying PMA configuration".to_string())?;
    default_registers.insert(name, list);
    Ok(())
}

/// S2（W17）：含符号边界的 [[pma_regions]] 执行期注入。符号 zsizze 必须活在
/// 本次求解的 solver 里（config 期没有 solver 上下文），因此不走
/// default_registers，而是在 solve-state 启动、checkpoint 之前把整张地图
/// （具体/符号字段混合）直接赋给执行帧的 zpma_regions 寄存器（镜像符号 PMP
/// 的 apply_symbolic_pmp_to_registers 装配方式）。符号 size 的取值域
/// [min, max]（闭区间）以 bvule 断言附加在主 solver 上，checkpoint 之后所有
/// 路径共享同一组符号声明与域约束。返回 (完整输出键, Sym) 记录，供
/// solve_pre_state 从最终模型输出边界值。
pub fn apply_symbolic_pma_regions_to_registers<'ir, B: BV>(
    regions: &[PmaRegionConfig],
    symtab: &Symtab,
    type_info: &IRTypeInfo,
    regs: &mut RegisterBindings<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<Vec<(String, Sym)>, String> {
    let mut records = Vec::new();
    let mut size_values: Vec<Val<B>> = Vec::with_capacity(regions.len());
    for region in regions {
        match region.size {
            PmaSize::Concrete(size) => size_values.push(Val::Bits(B::new(size, 64))),
            PmaSize::Symbolic { min, max } => {
                let sym = solver.declare_const(smtlib::Ty::BitVec(64), SourceLoc::unknown());
                // 闭区间 [min, max]：min <= size 且 size <= max
                solver.assert(smtlib::Exp::And(
                    Box::new(smtlib::Exp::Bvule(Box::new(smtlib::bits64(min, 64)), Box::new(smtlib::Exp::Var(sym)))),
                    Box::new(smtlib::Exp::Bvule(Box::new(smtlib::Exp::Var(sym)), Box::new(smtlib::bits64(max, 64)))),
                ));
                records.push((format!("pma_regions.{}.size", region.name), sym));
                size_values.push(Val::Symbolic(sym));
            }
        }
    }
    let list = pma_regions_list_value(regions, &size_values, symtab, type_info)?;
    let Some(name) = symtab.get(&zencode::encode("pma_regions")) else {
        return Err("Could not find register pma_regions when applying PMA configuration".to_string());
    };
    regs.assign(name, list, shared_state);
    Ok(records)
}

#[cfg(test)]
mod tests;
