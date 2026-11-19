use super::*;
use isla_lib::bitvector::b64::B64;
use isla_lib::ir::UVal;
use isla_lib::smt::{Config, Context, Model, SmtResult};
use std::collections::{BTreeMap, HashMap, HashSet};
use toml::Value;
/// W10（S1）[[pma_regions]] 未配置时必须返回 Ok(None)：不注入任何地图，
/// 行为与现状（IR 固化 zpma_regions 默认值）逐项一致。
#[test]
fn pma_regions_absent_returns_none() {
    let value = r#"
            [[memory_regions]]
            name = "sym_ram"
            base = "0x80000000"
            size = "0x10000000"
            region_type = "symbolic"
        "#
    .parse::<Value>()
    .unwrap();
    assert!(matches!(get_pma_regions(&value), Ok(None)));
}

/// 别名 ram/rom/mmio/hole 的关键字段映射（S1 别名映射完整性）：
/// ram=RWX+cacheable+no_fault+eventual，rom=R 只，mmio=RW 不 cacheable+
/// alignment_fault，hole=全 false。别名取值镜像 IR 固化 zpma_regions 的
/// 默认 region 属性（ram/mmio）与最保守取值（rom/hole）。
#[test]
fn pma_regions_alias_mapping() {
    let value = r#"
            [[pma_regions]]
            base = "0x80000000"
            size = "0x10000000"
            attr = "ram"

            [[pma_regions]]
            base = "0x1000"
            size = "0x1000"
            attr = "rom"

            [[pma_regions]]
            base = "0x02000000"
            size = "0x02000000"
            attr = "mmio"

            [[pma_regions]]
            base = "0x40000000"
            size = "0x10000000"
            attr = "hole"
        "#
    .parse::<Value>()
    .unwrap();

    // 输出按 base 降序：ram(0x80000000) > hole(0x40000000) > mmio(0x02000000) > rom(0x1000)
    let regions = get_pma_regions(&value).unwrap().unwrap();
    assert_eq!(regions.len(), 4);

    let ram = &regions[0];
    assert_eq!(ram.base, 0x8000_0000);
    assert_eq!(ram.size, PmaSize::Concrete(0x1000_0000));
    let a = &ram.attributes;
    assert!(a.readable && a.writable && a.executable && a.cacheable && a.coherent);
    assert!(a.read_idempotent && a.write_idempotent && a.supports_cbo_zzero);
    assert_eq!(a.misaligned_fault, PmaMisalignedFault::NoFault);
    assert_eq!(a.reservability, PmaReservability::Eventual);
    assert!(a.include_in_device_tree);

    let hole = &regions[1];
    let a = &hole.attributes;
    assert!(!a.readable && !a.writable && !a.executable && !a.cacheable && !a.coherent);
    assert!(!a.read_idempotent && !a.write_idempotent && !a.supports_cbo_zzero);
    assert_eq!(a.misaligned_fault, PmaMisalignedFault::NoFault);
    assert_eq!(a.reservability, PmaReservability::None);
    assert!(!a.include_in_device_tree);

    let mmio = &regions[2];
    let a = &mmio.attributes;
    assert!(a.readable && a.writable && !a.executable && !a.cacheable);
    assert!(!a.read_idempotent && !a.write_idempotent && !a.supports_cbo_zzero);
    assert_eq!(a.misaligned_fault, PmaMisalignedFault::AlignmentFault);
    assert_eq!(a.reservability, PmaReservability::None);

    let rom = &regions[3];
    let a = &rom.attributes;
    assert!(a.readable && !a.writable && !a.executable && a.cacheable);
    assert_eq!(a.misaligned_fault, PmaMisalignedFault::NoFault);
    assert_eq!(a.reservability, PmaReservability::None);
    assert!(!a.include_in_device_tree);

    // 未知别名必须报错
    let bad = r#"
            [[pma_regions]]
            base = "0x0"
            size = "0x1000"
            attr = "sram"
        "#
    .parse::<Value>()
    .unwrap();
    assert!(get_pma_regions(&bad).is_err(), "未知 attr 别名仍应报错");
}

/// 明细字段模式：无 attr 时以 include_in_device_tree=true、其余全 false 为
/// 基线，明细字段逐项覆盖；attr 与明细字段可同时出现（attr 给底、明细覆盖）。
#[test]
fn pma_regions_detailed_fields_and_override() {
    let value = r#"
            [[pma_regions]]
            base = "0x80000000"
            size = "0x1000"
            readable = true
            misaligned = "alignment_fault"
            reservability = "eventual"
        "#
    .parse::<Value>()
    .unwrap();
    let regions = get_pma_regions(&value).unwrap().unwrap();
    let a = &regions[0].attributes;
    assert!(a.readable && !a.writable && !a.executable);
    assert!(a.include_in_device_tree, "明细模式 include_in_device_tree 默认 true");
    assert_eq!(a.misaligned_fault, PmaMisalignedFault::AlignmentFault);
    assert_eq!(a.reservability, PmaReservability::Eventual);

    let value = r#"
            [[pma_regions]]
            base = "0x80000000"
            size = "0x1000"
            attr = "mmio"
            executable = true
            include_in_device_tree = true
        "#
    .parse::<Value>()
    .unwrap();
    let regions = get_pma_regions(&value).unwrap().unwrap();
    let a = &regions[0].attributes;
    assert!(a.executable, "明细字段应覆盖 attr 底座");
    assert!(!a.cacheable, "未被覆盖的 attr 字段保持 mmio 取值");
    assert_eq!(a.misaligned_fault, PmaMisalignedFault::AlignmentFault);
    assert!(a.include_in_device_tree);

    // 既无 attr 也无任何明细属性字段的 region 是配置疑点，直接报错
    let bare = r#"
            [[pma_regions]]
            base = "0x0"
            size = "0x1000"
        "#
    .parse::<Value>()
    .unwrap();
    assert!(get_pma_regions(&bare).is_err(), "无 attr 且无明细字段应报错");
}

/// 配置解析自校验（对齐 MemoryBuilder 硬失败风格）：size=0、base+size 溢出、
/// 区域重叠都必须报错；重叠检测与 TOML 书写顺序无关（解析内部按 base 降序
/// 排序后再做相邻重叠检查，注入的 zpma_regions 列表即该降序）。
#[test]
fn pma_regions_validation_hard_fails() {
    let cases = [
        (
            r#"
                [[pma_regions]]
                base = "0x80000000"
                size = "0x0"
                attr = "ram"
                "#,
            "size 为 0",
        ),
        (
            r#"
                [[pma_regions]]
                base = "0xffffffffffffffff"
                size = "0x2"
                attr = "ram"
                "#,
            "base+size 溢出",
        ),
        (
            r#"
                [[pma_regions]]
                base = "0x80000000"
                size = "0x10000000"
                attr = "ram"

                [[pma_regions]]
                base = "0x8ffff000"
                size = "0x1000"
                attr = "ram"
                "#,
            "相邻区域重叠",
        ),
        (
            r#"
                [[pma_regions]]
                base = "0x0"
                size = "0x2000"
                attr = "rom"

                [[pma_regions]]
                base = "0x1000"
                size = "0x2000"
                attr = "ram"
                "#,
            "乱序书写仍检出重叠",
        ),
    ];
    for (toml, why) in cases {
        let value = toml.parse::<Value>().unwrap();
        let err = get_pma_regions(&value).unwrap_err();
        assert!(!err.is_empty(), "{} 应报错", why);
    }

    // 合法乱序配置：输出按 base 降序（与 IR 固化 zpma_regions 的列表次序一致）
    let value = r#"
            [[pma_regions]]
            base = "0x80000000"
            size = "0x10000000"
            attr = "ram"

            [[pma_regions]]
            base = "0x1000"
            size = "0x1000"
            attr = "rom"
        "#
    .parse::<Value>()
    .unwrap();
    let regions = get_pma_regions(&value).unwrap().unwrap();
    assert!(regions[0].base > regions[1].base, "输出应按 base 降序");
}

/// S2（W17）：size = "symbolic" 声明符号边界。显式 size_bounds 取闭区间
/// [下界, 上界]；未声明时用默认域 [4KiB, 2^43]（emu RAM 顶界锚点）。
/// 具体与符号 region 可混排（重叠检查按符号域上界保守处理）。
#[test]
fn pma_regions_symbolic_size_parsing() {
    let value = r#"
            [[pma_regions]]
            base = "0x80000000"
            size = "symbolic"
            size_bounds = ["0x800", "0x1000000000"]
            attr = "ram"
        "#
    .parse::<Value>()
    .unwrap();
    let regions = get_pma_regions(&value).unwrap().unwrap();
    assert_eq!(regions.len(), 1);
    assert_eq!(regions[0].size, PmaSize::Symbolic { min: 0x800, max: 0x10_0000_0000 });

    // 未声明 size_bounds：默认域
    let value = r#"
            [[pma_regions]]
            base = "0x80000000"
            size = "symbolic"
            attr = "ram"
        "#
    .parse::<Value>()
    .unwrap();
    let regions = get_pma_regions(&value).unwrap().unwrap();
    assert_eq!(regions[0].size, PmaSize::Symbolic { min: 0x1000, max: 0x80000000000 });

    // 具体与符号混排合法：重叠检查用符号域上界（0x80000000+0x2000 <= 0x90000000 不重叠）
    let value = r#"
            [[pma_regions]]
            base = "0x80000000"
            size = "symbolic"
            size_bounds = ["0x1000", "0x2000"]
            attr = "ram"

            [[pma_regions]]
            base = "0x90000000"
            size = "0x1000"
            attr = "ram"
        "#
    .parse::<Value>()
    .unwrap();
    let regions = get_pma_regions(&value).unwrap().unwrap();
    assert_eq!(regions.len(), 2, "符号域上界不与具体 region 重叠时应放行");
}

/// S2（W17）：符号边界自校验硬失败——size_bounds 元数错误/下界为 0/下界超
/// 上界/base+上界溢出/具体 size 搭配 size_bounds/符号域上界与邻居重叠。
#[test]
fn pma_regions_symbolic_bounds_hard_fails() {
    let cases = [
        (
            r#"
                [[pma_regions]]
                base = "0x80000000"
                size = "symbolic"
                size_bounds = ["0x1000"]
                attr = "ram"
                "#,
            "size_bounds 元数不是 2",
        ),
        (
            r#"
                [[pma_regions]]
                base = "0x80000000"
                size = "symbolic"
                size_bounds = ["0x0", "0x1000"]
                attr = "ram"
                "#,
            "下界为 0",
        ),
        (
            r#"
                [[pma_regions]]
                base = "0x80000000"
                size = "symbolic"
                size_bounds = ["0x2000", "0x1000"]
                attr = "ram"
                "#,
            "下界超上界",
        ),
        (
            r#"
                [[pma_regions]]
                base = "0xffffffffffffffff"
                size = "symbolic"
                attr = "ram"
                "#,
            "base + 默认域上界溢出",
        ),
        (
            r#"
                [[pma_regions]]
                base = "0x80000000"
                size = "0x1000"
                size_bounds = ["0x1000", "0x2000"]
                attr = "ram"
                "#,
            "具体 size 搭配 size_bounds",
        ),
        (
            r#"
                [[pma_regions]]
                base = "0x80000000"
                size = "symbolic"
                size_bounds = ["0x1000", "0x20000000"]
                attr = "ram"

                [[pma_regions]]
                base = "0x90000000"
                size = "0x1000"
                attr = "ram"
                "#,
            "符号域上界与相邻 region 重叠",
        ),
    ];
    for (toml, why) in cases {
        let value = toml.parse::<Value>().unwrap();
        assert!(get_pma_regions(&value).is_err(), "{} 应报错", why);
    }
}

/// W10（S1）[[pma_regions]] → zpma_regions 寄存器值构造的测试夹具：
/// 手工搭出与 rv64d.ir 相同形状的 symtab/type_info（struct zPMA_Region、
/// struct zPMA、enum zmisaligned_fault、enum zReservability、寄存器名
/// zpma_regions），使构造逻辑可在单测中全量验证；真实 IR 的形状保真由
/// 端到端测试（zSTORE 圈外 fault）兜底。
fn pma_type_fixture() -> (Symtab<'static>, IRTypeInfo) {
    let mut symtab = Symtab::new();
    let pma_region_name = symtab.intern("zPMA_Region");
    let pma_name = symtab.intern("zPMA");
    let misaligned_enum = symtab.intern("zmisaligned_fault");
    let reservability_enum = symtab.intern("zReservability");

    let mut pma_fields = BTreeMap::new();
    pma_fields.insert(symtab.intern("zcacheable"), Ty::Bool);
    pma_fields.insert(symtab.intern("zcoherent"), Ty::Bool);
    pma_fields.insert(symtab.intern("zexecutable"), Ty::Bool);
    pma_fields.insert(symtab.intern("zmisaligned_fault"), Ty::Enum(misaligned_enum));
    pma_fields.insert(symtab.intern("zread_idempotent"), Ty::Bool);
    pma_fields.insert(symtab.intern("zreadable"), Ty::Bool);
    pma_fields.insert(symtab.intern("zreservability"), Ty::Enum(reservability_enum));
    pma_fields.insert(symtab.intern("zsupports_cbo_zzero"), Ty::Bool);
    pma_fields.insert(symtab.intern("zwritable"), Ty::Bool);
    pma_fields.insert(symtab.intern("zwrite_idempotent"), Ty::Bool);

    let mut region_fields = BTreeMap::new();
    region_fields.insert(symtab.intern("zattributes"), Ty::Struct(pma_name));
    region_fields.insert(symtab.intern("zbase"), Ty::Bits(64));
    region_fields.insert(symtab.intern("zinclude_in_device_tree"), Ty::Bool);
    region_fields.insert(symtab.intern("zsizze"), Ty::Bits(64));

    let mut structs = HashMap::new();
    structs.insert(pma_name, pma_fields);
    structs.insert(pma_region_name, region_fields);

    let mut enums = HashMap::new();
    let misaligned_members =
        vec![symtab.intern("zNoFault"), symtab.intern("zAccessFault"), symtab.intern("zAlignmentFault")];
    let reservability_members =
        vec![symtab.intern("zRsrvNone"), symtab.intern("zRsrvNonEventual"), symtab.intern("zRsrvEventual")];
    enums.insert(misaligned_enum, misaligned_members.clone());
    enums.insert(reservability_enum, reservability_members.clone());

    let mut enum_members = HashMap::new();
    for (pos, member) in misaligned_members.iter().enumerate() {
        enum_members.insert(*member, (pos, misaligned_members.len(), misaligned_enum));
    }
    for (pos, member) in reservability_members.iter().enumerate() {
        enum_members.insert(*member, (pos, reservability_members.len(), reservability_enum));
    }

    let type_info = IRTypeInfo { structs, enums, enum_members, unions: HashMap::new(), union_ctors: HashSet::new() };
    (symtab, type_info)
}

fn pma_region(base: u64, size: u64, attr: &str) -> super::PmaRegionConfig {
    use super::{PmaAttributes, PmaMisalignedFault, PmaRegionConfig, PmaReservability, PmaSize};
    // 别名取值与本模块的 pma_regions_alias_mapping 测试锁定的映射一致；
    // 这里直接构造，聚焦验证 Val 构造侧。
    let attributes = match attr {
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
            include_in_device_tree: true,
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
            include_in_device_tree: false,
        },
        other => panic!("测试不支持别名 {}", other),
    };
    PmaRegionConfig {
        name: attr.to_string(),
        base,
        size: PmaSize::Concrete(size),
        attributes,
        atomic: None,
        backing: None,
    }
}

/// 构造出的 zpma_regions 值必须是 Val::List(Val::Struct...)，record 的
/// base/size（注意 IR 字段名 zsizze 是 size 的 zencode）与别名属性逐字段
/// 正确，枚举成员身份（enum_id + 序号）与 IR 定义一致。
#[test]
fn pma_regions_list_value_alias_fields() {
    let (symtab, type_info) = pma_type_fixture();
    let regions = vec![pma_region(0x8000_0000, 0x1000_0000, "ram"), pma_region(0x0200_0000, 0x0200_0000, "mmio")];

    let size_values: Vec<Val<B64>> = regions
        .iter()
        .map(|r| match r.size {
            super::PmaSize::Concrete(size) => Val::Bits(B64::new(size, 64)),
            super::PmaSize::Symbolic { .. } => panic!("本测试只用具体 size"),
        })
        .collect();
    let value = pma_regions_list_value::<B64>(&regions, &size_values, &symtab, &type_info).unwrap();
    let Val::List(items) = &value else { panic!("zpma_regions 值必须是 Val::List，实际 {:?}", value) };
    assert_eq!(items.len(), 2);

    let ram = match &items[0] {
        Val::Struct(fields) => fields,
        other => panic!("region 必须是 Struct，实际 {:?}", other),
    };
    let field = |name: &str| {
        let id = symtab.get(&zencode::encode(name)).unwrap_or_else(|| panic!("夹具缺字段 {}", name));
        ram.get(&id).unwrap_or_else(|| panic!("构造值缺字段 {}", name))
    };
    match field("base") {
        Val::Bits(bv) => assert_eq!(bv.lower_u64(), 0x8000_0000),
        other => panic!("base 必须是 Bits，实际 {:?}", other),
    }
    match field("size") {
        Val::Bits(bv) => assert_eq!(bv.lower_u64(), 0x1000_0000, "IR 字段 zsizze 应取配置 size"),
        other => panic!("size 必须是 Bits，实际 {:?}", other),
    }
    assert!(matches!(field("include_in_device_tree"), Val::Bool(true)));

    let attributes = match field("attributes") {
        Val::Struct(fields) => fields,
        other => panic!("attributes 必须是 Struct，实际 {:?}", other),
    };
    let attr_field = |name: &str| {
        let id = symtab.get(&zencode::encode(name)).unwrap();
        attributes.get(&id).unwrap_or_else(|| panic!("attributes 缺字段 {}", name))
    };
    assert!(matches!(attr_field("readable"), Val::Bool(true)));
    assert!(matches!(attr_field("writable"), Val::Bool(true)));
    assert!(matches!(attr_field("executable"), Val::Bool(true)));
    assert!(matches!(attr_field("cacheable"), Val::Bool(true)));
    assert!(matches!(attr_field("read_idempotent"), Val::Bool(true)));
    assert!(matches!(attr_field("write_idempotent"), Val::Bool(true)));
    assert!(matches!(attr_field("supports_cbo_zero"), Val::Bool(true)));
    let misaligned_enum = symtab.get(&zencode::encode("misaligned_fault")).unwrap();
    match attr_field("misaligned_fault") {
        Val::Enum(member) => {
            assert_eq!(member.enum_id.to_name(), misaligned_enum);
            assert_eq!(member.member, 0, "ram 的 misaligned 应是 zNoFault（首成员）");
        }
        other => panic!("misaligned_fault 必须是 Enum，实际 {:?}", other),
    }
    let reservability_enum = symtab.get(&zencode::encode("Reservability")).unwrap();
    match attr_field("reservability") {
        Val::Enum(member) => {
            assert_eq!(member.enum_id.to_name(), reservability_enum);
            assert_eq!(member.member, 2, "ram 的 reservability 应是 zRsrvEventual（第 3 成员）");
        }
        other => panic!("reservability 必须是 Enum，实际 {:?}", other),
    }

    // mmio：misaligned=AlignmentFault（第 3 成员）、reservability=RsrvNone（首成员）
    let mmio = match &items[1] {
        Val::Struct(fields) => fields,
        other => panic!("region 必须是 Struct，实际 {:?}", other),
    };
    let attributes = match mmio.get(&symtab.get(&zencode::encode("attributes")).unwrap()) {
        Some(Val::Struct(fields)) => fields,
        other => panic!("attributes 必须是 Struct，实际 {:?}", other),
    };
    let misaligned = symtab.get(&zencode::encode("misaligned_fault")).unwrap();
    match attributes.get(&symtab.get(&zencode::encode("misaligned_fault")).unwrap()) {
        Some(Val::Enum(member)) => {
            assert_eq!(member.enum_id.to_name(), misaligned);
            assert_eq!(member.member, 2, "mmio 的 misaligned 应是 zAlignmentFault");
        }
        other => panic!("misaligned_fault 必须是 Enum，实际 {:?}", other),
    }
}

/// 注入：apply_pma_regions_to_config 把构造值写入 default_registers 的
/// zpma_regions 键；symtab 缺 zpma_regions 寄存器名（IR 不含 PMA 模型）时
/// 报错而非静默注入。
#[test]
fn pma_regions_apply_to_config_registers() {
    let regions = vec![pma_region(0x8000_0000, 0x1000_0000, "ram")];

    // 夹具 symtab 尚未 intern zpma_regions：等价于"IR 无该寄存器"
    let (symtab, type_info) = pma_type_fixture();
    let mut default_registers = HashMap::new();
    assert!(
        apply_pma_regions_to_config::<B64>(&regions, &symtab, &type_info, &mut default_registers).is_err(),
        "缺 zpma_regions 寄存器名应报错"
    );
    assert!(default_registers.is_empty(), "失败时不得注入任何值");

    // intern 寄存器名后注入成功
    let (mut symtab, type_info) = pma_type_fixture();
    let zpma = symtab.intern("zpma_regions");
    let mut default_registers = HashMap::new();
    apply_pma_regions_to_config::<B64>(&regions, &symtab, &type_info, &mut default_registers).unwrap();
    assert!(matches!(default_registers.get(&zpma), Some(Val::List(_))), "zpma_regions 应已注入");
}

/// S2（W17）：符号边界执行期注入。apply_symbolic_pma_regions_to_registers
/// 对 Symbolic size 的 region 声明 64 位常量、附加闭区间域约束、把混合
/// （具体+符号）地图赋给执行帧 zpma_regions，并返回 (完整输出键, Sym) 记录。
/// 具体字段（base/属性/具体 size）保持 W10 构造形状。
#[test]
fn pma_regions_symbolic_injection_assigns_register_and_records_syms() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    use super::PmaSize;
    use isla_lib::ir::SharedState;
    use isla_lib::register::RegisterBindings;
    use isla_lib::smt::{Config, Context, Solver};

    let (mut symtab, type_info) = pma_type_fixture();
    let zpma = symtab.intern("zpma_regions");
    let mut symbolic = pma_region(0x8000_0000, 0, "ram");
    symbolic.size = PmaSize::Symbolic { min: 0x1000, max: 0x80000000000 };
    let mut concrete = pma_region(0x0200_0000, 0x0200_0000, "mmio");
    concrete.name = "mmio0".to_string();
    let regions = vec![symbolic, concrete];

    // 夹具 SharedState：注入只用到 symtab，构造最小空架构即可。
    let arch: &'static [isla_lib::ir::Def<Name, B64>] = Box::leak(Vec::new().into_boxed_slice());
    let shared_state = SharedState::new(
        symtab,
        arch,
        type_info.clone(),
        HashSet::new(),
        HashSet::new(),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    let mut regs = RegisterBindings::new();
    // 生产路径里寄存器表由 initialize_architecture 建立（assign 只写已存在的键），
    // 夹具手动补 zpma_regions 的未初始化槽位。PMA_Region 结构名在夹具
    // symtab 中已 intern，直接按名取。
    let region_struct = shared_state
        .type_info
        .structs
        .keys()
        .find(|name| shared_state.symtab.to_str(**name) == "zPMA_Region")
        .copied()
        .expect("夹具缺 struct zPMA_Region");
    let region_ty: &'static Ty<Name> = Box::leak(Box::new(Ty::List(Box::new(Ty::Struct(region_struct)))));
    regs.insert(zpma, false, UVal::Uninit(region_ty));
    let ctx = Context::new(Config::new());
    let mut solver = Solver::new(&ctx);

    let records = apply_symbolic_pma_regions_to_registers::<B64>(
        &regions,
        &shared_state.symtab,
        &shared_state.type_info,
        &mut regs,
        &shared_state,
        &mut solver,
    )
    .unwrap();

    // 记录只含符号 region
    assert_eq!(records.len(), 1, "只有符号 size 的 region 被记录");
    assert_eq!(records[0].0, "pma_regions.ram.size");

    // 寄存器已赋值，zsizze 是符号常量、base/具体字段保持具体
    let Some(Val::List(items)) = regs.get_last_if_initialized(zpma) else {
        panic!("zpma_regions 应已初始化为 Val::List")
    };
    assert_eq!(items.len(), 2);
    let ram = match &items[0] {
        Val::Struct(fields) => fields,
        other => panic!("region 必须是 Struct，实际 {:?}", other),
    };
    let size_id = shared_state.symtab.get(&zencode::encode("size")).unwrap();
    match ram.get(&size_id) {
        Some(Val::Symbolic(sym)) => assert_eq!(*sym, records[0].1, "zsizze 应取声明并记录的符号常量"),
        other => panic!("符号 region 的 zsizze 必须是 Symbolic，实际 {:?}", other),
    }
    let base_id = shared_state.symtab.get(&zencode::encode("base")).unwrap();
    match ram.get(&base_id) {
        Some(Val::Bits(bv)) => assert_eq!(bv.lower_u64(), 0x8000_0000),
        other => panic!("base 必须保持具体，实际 {:?}", other),
    }
    let mmio = match &items[1] {
        Val::Struct(fields) => fields,
        other => panic!("region 必须是 Struct，实际 {:?}", other),
    };
    match mmio.get(&size_id) {
        Some(Val::Bits(bv)) => assert_eq!(bv.lower_u64(), 0x0200_0000, "具体 region 的 zsizze 保持具体"),
        other => panic!("具体 region 的 zsizze 必须是 Bits，实际 {:?}", other),
    }

    // 域约束已进入 solver：Sat 且模型值落在 [0x1000, 0x80000000000] 内
    assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
    let mut model = Model::new(&solver);
    match model.get_var(records[0].1).unwrap() {
        isla_lib::smt::ModelVal::Exp(isla_lib::smt::smtlib::Exp::Bits64(bv)) => {
            let size = bv.lower_u64();
            assert!(size >= 0x1000 && size <= 0x80000000000, "模型 size={:#x} 应在声明域内", size);
        }
        other => panic!("size 模型值必须是 64 位位向量，实际 {:?}", other),
    }
}

fn encoded(regions: &[PmaRegionConfig], symtab: &Symtab, types: &IRTypeInfo) -> Val<B64> {
    let sizes = regions
        .iter()
        .map(|r| match r.size {
            PmaSize::Concrete(size) => Val::Bits(B64::new(size, 64)),
            _ => panic!("该夹具仅编码具体值"),
        })
        .collect::<Vec<_>>();
    pma_regions_list_value(regions, &sizes, symtab, types).unwrap()
}

fn normalized(value: &Val<B64>, symtab: &Symtab) -> serde_json::Value {
    match value {
        Val::List(values) => values.iter().map(|v| normalized(v, symtab)).collect(),
        Val::Struct(fields) => {
            fields.iter().map(|(n, v)| (zencode::decode(symtab.to_str(*n)), normalized(v, symtab))).collect()
        }
        Val::Bits(value) => serde_json::json!(value.lower_u64()),
        Val::Bool(value) => serde_json::json!(value),
        Val::Enum(value) => serde_json::json!({"enum": value.member}),
        value => panic!("非预期PMA值 {:?}", value),
    }
}

#[test]
fn pma_regions_real_nine_regions_match_configured_encoding() {
    let text = include_str!("../../../../../configs/riscv64_xiangshan_fullsym.toml");
    let old: Value = text.parse().unwrap();
    let legacy = get_pma_regions(&old).unwrap().unwrap();
    assert_eq!(legacy.len(), 9);
    let (mut symtab, types) = pma_type_fixture();
    let register = symtab.intern("zpma_regions");
    // 56bae3f2 将香山的六个设备区改为 AccessFault（夹具枚举成员 1）。
    let expected: serde_json::Value = serde_json::from_str(include_str!("xiangshan-nine-regions.json")).unwrap();
    let value = encoded(&legacy, &symtab, &types);
    assert_eq!(normalized(&value, &symtab), expected);
    use crate::isarch::target::{Target, RV64};
    let mut target = RV64::<B64>::default();
    let mut defaults = HashMap::new();
    target.configure_model(&old, &symtab, &types, &mut defaults).unwrap();
    assert_eq!(normalized(&defaults[&register], &symtab), expected);
}

#[test]
fn pma_regions_optional_metadata_does_not_change_encoding() {
    let legacy = "[[pma_regions]]\nname='ram'\nbase=4096\nsize=4096\nattr='ram'\n";
    let (symtab, types) = pma_type_fixture();
    let old = get_pma_regions(&legacy.parse().unwrap()).unwrap().unwrap();
    assert_eq!(old[0].atomic, None);
    assert_eq!(old[0].backing, None);
    for (name, backing) in
        [("memory", PmaBacking::Memory), ("device_bus", PmaBacking::DeviceBus), ("denied", PmaBacking::Denied)]
    {
        for atomic in [true, false] {
            let text = legacy.to_string() + &format!("atomic={atomic}\nbacking='{name}'\n");
            let new = get_pma_regions(&text.parse().unwrap()).unwrap().unwrap();
            assert_eq!(new[0].atomic, Some(atomic));
            assert_eq!(new[0].backing, Some(backing));
            assert_eq!(
                normalized(&encoded(&old, &symtab, &types), &symtab),
                normalized(&encoded(&new, &symtab, &types), &symtab)
            );
        }
    }
    for bad in ["atomic='true'", "backing=true", "backing='ram'", "typo=true"] {
        assert!(get_pma_regions(&(legacy.to_string() + bad).parse().unwrap()).is_err());
    }
}

#[test]
fn pma_regions_wrong_architecture_is_rejected() {
    use crate::isarch::target::{PreStateCtx, Target, ARM};
    let (symtab, types) = pma_type_fixture();
    let mut arm = ARM::<B64> { pre_state: PreStateCtx::new() };
    for text in [
        "[[pma_regions]]\nbase=4096\nsize=4096\nattr='ram'",
        "[[pma_regions]]\nbase=4096\nsize=4096\nattr='ram'\natomic=true\nbacking='memory'",
        "pma_regions=[]",
    ] {
        assert!(arm.configure_model(&text.parse().unwrap(), &symtab, &types, &mut HashMap::new()).is_err());
    }
    arm.configure_model(&"".parse().unwrap(), &symtab, &types, &mut HashMap::new()).unwrap();
}

#[test]
fn pma_regions_aliases_encode_every_legacy_attribute() {
    let (symtab, types) = pma_type_fixture();
    for (alias, flags, misaligned, reservability, device_tree) in [
        ("ram", [true, true, true, true, true, true, true, true], 0, 2, true),
        ("rom", [true, false, false, true, true, true, true, false], 0, 0, false),
        ("mmio", [true, true, false, false, true, false, false, false], 2, 0, false),
        ("hole", [false; 8], 0, 0, false),
    ] {
        let text = format!("[[pma_regions]]\nbase=4096\nsize=4096\nattr='{alias}'");
        let regions = get_pma_regions(&text.parse().unwrap()).unwrap().unwrap();
        let value = normalized(&encoded(&regions, &symtab, &types), &symtab);
        let attrs = &value[0]["attributes"];
        for (field, expected) in [
            "readable",
            "writable",
            "executable",
            "cacheable",
            "coherent",
            "read_idempotent",
            "write_idempotent",
            "supports_cbo_zero",
        ]
        .iter()
        .zip(flags)
        {
            assert_eq!(attrs[field], serde_json::json!(expected), "{alias}.{field}");
        }
        assert_eq!(attrs["misaligned_fault"], serde_json::json!({"enum":misaligned}));
        assert_eq!(attrs["reservability"], serde_json::json!({"enum":reservability}));
        assert_eq!(value[0]["include_in_device_tree"], serde_json::json!(device_tree));
    }
}

#[test]
fn pma_regions_includes_replace_entire_array_and_keep_merged_value() {
    use isla_lib::config::ISAConfig;
    use sha2::{Digest, Sha256};
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(".tmp")
        .join(format!("pma-includes-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let common = r#"pc='PC'
[[toolchain]]
name='default'
assembler='as'
objdump='objdump'
nm='nm'
linker='ld'
[mmu]
page_table_base='0'
page_size='4096'
s2_page_table_base='0'
s2_page_size='4096'
[threads]
base='0'
top='4096'
stride='4096'
[symbolic_addrs]
base='4096'
top='8192'
stride='16'
"#;
    let mut symtab = Symtab::new();
    symtab.intern("zPC");
    let types = IRTypeInfo::new::<B64>(&[]);
    let base = format!("{common}\n[[pma_regions]]\nname='a'\nbase=0\nsize=4096\nattr='hole'\n[[pma_regions]]\nname='b'\nbase=4096\nsize=4096\nattr='ram'");
    std::fs::write(directory.join("base.toml"), base).unwrap();
    let path = directory.join("override.toml");
    std::fs::write(&path, "includes=['base.toml']\n[[pma_regions]]\nname='replacement'\nbase=8192\nsize=4096\nattr='rom'\natomic=false\nbacking='denied'").unwrap();
    let loaded = ISAConfig::<B64>::from_file_with_merged(&mut Sha256::new(), &path, None, &symtab, &types).unwrap();
    assert_eq!(loaded.isa.pc, symtab.get("zPC").unwrap());
    assert!(loaded.merged.get("includes").is_none());
    let regions = get_pma_regions(&loaded.merged).unwrap().unwrap();
    assert_eq!(regions.len(), 1);
    assert_eq!(regions[0].name, "replacement");
    assert_eq!(regions[0].atomic, Some(false));
    assert_eq!(regions[0].backing, Some(PmaBacking::Denied));
    let old_api = ISAConfig::<B64>::from_file(&mut Sha256::new(), &path, None, &symtab, &types).unwrap();
    assert_eq!(old_api.pc, loaded.isa.pc);
    std::fs::write(&path, "includes=['base.toml']\npma_regions=[]").unwrap();
    let loaded = ISAConfig::<B64>::from_file_with_merged(&mut Sha256::new(), &path, None, &symtab, &types).unwrap();
    // 显式空数组同样整体替换，而不是保留父文件中的条目。
    assert!(get_pma_regions(&loaded.merged).unwrap().unwrap().is_empty());
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn pma_regions_lifecycle_checkpoint_output_and_restore_keep_legacy_names() {
    use crate::isarch::target::{Target, RV64};
    use isla_lib::ir::{Bindings, Def};
    use isla_lib::smt::{checkpoint, smtlib, Model};
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let (mut symtab, types) = pma_type_fixture();
    let register = symtab.intern("zpma_regions");
    let region = symtab.get("zPMA_Region").unwrap();
    let ty = Ty::List(Box::new(Ty::Struct(region)));
    let arch: Vec<Def<Name, B64>> = vec![Def::Register(register, ty.clone(), vec![])];
    let mut shared = SharedState::<B64>::empty(symtab);
    shared.type_info = types;
    shared.registers.insert(register, ty.clone());
    let config: Value =
        "[[pma_regions]]\nname='bounds'\nbase=4096\nsize='symbolic'\nsize_bounds=[4096,8192]\nattr='ram'"
            .parse()
            .unwrap();
    let mut target = RV64::default();
    let mut defaults = HashMap::new();
    target.configure_model(&config, &shared.symtab, &shared.type_info, &mut defaults).unwrap();
    assert!(defaults.is_empty(), "符号表留到执行期，不能塞进配置默认值");
    let mut regs = RegisterBindings::new();
    let Def::Register(_, ty, _) = &arch[0] else { panic!() };
    regs.insert(register, false, UVal::Uninit(ty));
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    target.setup_pre_state(&mut regs, &Bindings::default(), &shared, &mut solver, &HashMap::new()).unwrap();
    target.initialize_execution(&mut regs, &shared, &mut solver).unwrap();
    let [(name, symbol)] = target.model_bindings() else { panic!("应有一个size绑定") };
    assert_eq!(name, "pma_regions.bounds.size");
    let symbol = *symbol;
    assert!(matches!(regs.get_last_if_initialized(register), Some(Val::List(_))));
    let cp = checkpoint(&mut solver);
    for value in [4095, 4096, 8192, 8193] {
        let mut branch = Solver::from_checkpoint(&context, cp.clone());
        branch.assert_eq(smtlib::Exp::Var(symbol), smtlib::bits64(value, 64));
        let expected = if (4096..=8192).contains(&value) { SmtResult::Sat } else { SmtResult::Unsat };
        assert_eq!(branch.check_sat(SourceLoc::unknown()), expected);
        if expected == SmtResult::Sat {
            let state = target.solve_pre_state(&mut Model::new(&branch), &shared).unwrap();
            assert!(state.contains_key("pma_regions.bounds.size"));
            assert_eq!(state.len(), 1);
        }
    }
    let bindings = target.model_bindings().to_vec();
    let mut restored = RV64::<B64>::default();
    restored.configure_model(&config, &shared.symtab, &shared.type_info, &mut HashMap::new()).unwrap();
    assert!(restored.restore_model_bindings(&[("unknown".to_string(), symbol)]).is_err());
    assert!(restored.model_bindings().is_empty());
    assert!(restored.restore_model_bindings(&[]).is_err());
    assert!(restored.restore_model_bindings(&[bindings[0].clone(), bindings[0].clone()]).is_err());
    restored.restore_model_bindings(&bindings).unwrap();
    assert_eq!(restored.model_bindings(), target.model_bindings());
    let mut branch = Solver::from_checkpoint(&context, cp);
    branch.assert_eq(smtlib::Exp::Var(symbol), smtlib::bits64(8192, 64));
    assert_eq!(branch.check_sat(SourceLoc::unknown()), SmtResult::Sat);
    let mut model = Model::new(&branch);
    assert_eq!(
        restored.solve_pre_state(&mut model, &shared).unwrap(),
        target.solve_pre_state(&mut model, &shared).unwrap()
    );
    // 同一个 target 会连续处理 clause／hint 批；新 solver 必须只保留本批绑定。
    let mut next_solver = Solver::<B64>::new(&context);
    next_solver.declare_const(smtlib::Ty::Bool, SourceLoc::unknown());
    target.initialize_execution(&mut regs, &shared, &mut next_solver).unwrap();
    assert_eq!(target.model_bindings().len(), 1);
    assert_ne!(target.model_bindings()[0].1, symbol);
    assert_eq!(next_solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
    assert!(target
        .solve_pre_state(&mut Model::new(&next_solver), &shared)
        .unwrap()
        .contains_key("pma_regions.bounds.size"));
}

#[test]
fn pma_regions_ir_missing_fields_and_wrong_enum_types_are_rejected() {
    let (mut symtab, types) = pma_type_fixture();
    symtab.intern("zpma_regions");
    let regions = vec![pma_region(0x8000_0000, 4096, "ram")];
    let pma = symtab.get("zPMA").unwrap();
    let region = symtab.get("zPMA_Region").unwrap();
    for (structure, field) in [(pma, "zreadable"), (region, "zsizze")] {
        let mut missing = types.clone();
        missing.structs.get_mut(&structure).unwrap().remove(&symtab.get(field).unwrap());
        assert!(
            apply_pma_regions_to_config::<B64>(&regions, &symtab, &missing, &mut HashMap::new()).is_err(),
            "缺少{field}应报错"
        );
    }
    let mut wrong = types.clone();
    wrong
        .structs
        .get_mut(&pma)
        .unwrap()
        .insert(symtab.get("zmisaligned_fault").unwrap(), Ty::Enum(symtab.get("zReservability").unwrap()));
    assert!(apply_pma_regions_to_config::<B64>(&regions, &symtab, &wrong, &mut HashMap::new()).is_err());
    let mut wrong = types.clone();
    wrong.structs.get_mut(&region).unwrap().insert(symtab.get("zsizze").unwrap(), Ty::Bits(32));
    assert!(apply_pma_regions_to_config::<B64>(&regions, &symtab, &wrong, &mut HashMap::new()).is_err());
}
