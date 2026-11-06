//! 配置具体枚举绕过 IR 常量读取后，仍须在区域合并前登记类型。
use super::*;
use crate::config::{PmaMisalignedFault, PmaReservability};
use crate::smt::{EnumId, EnumMember};

const PMA_IR: &str = r#"
register zPC : %bv64
enum zReservability { zRsrvNone, zRsrvNonEventual, zRsrvEventual }
enum zmisaligned_fault { zNoFault, zAccessFault, zAlignmentFault }
struct zPMA {
  zreadable: %bool, zwritable: %bool, zexecutable: %bool,
  zcacheable: %bool, zcoherent: %bool,
  zread_idempotent: %bool, zwrite_idempotent: %bool,
  zsupports_cbo_zzero: %bool,
  zmisaligned_fault: %enum zmisaligned_fault,
  zreservability: %enum zReservability
}
struct zPMA_Region {
  zbase: %bv64, zsizze: %bv64,
  zinclude_in_device_tree: %bool, zattributes: %struct zPMA
}
union zOptionPMA { zSomePMA: %struct zPMA_Region, zNonePMA: %unit }
register zpma_result : %union zOptionPMA
"#;

fn check_pma_merge(overrides: &str) {
    let (symtab, definitions) = parse_ir_string(PMA_IR);
    let types = IRTypeInfo::new(&definitions);
    let baseline = include_str!("../../../../agents/path_merge_call_support/baseline_config.toml")
        .replace("in_program_order = [\"sail_barrier\"]", "in_program_order = []");
    let config = ISAConfig::<B64>::parse(
        &format!(
            "{baseline}\n\
            [[pma_regions]]\nbase = \"0x80000000\"\nsize = \"0x1000\"\nattr = \"ram\"\n\
            [[pma_regions]]\nbase = \"0x30000000\"\nsize = \"0x1000\"\nattr = \"ram\"\n{overrides}\n"
        ),
        None,
        &symtab,
        &types,
    )
    .unwrap();
    let definitions = Box::leak(definitions.into_boxed_slice());
    let shared = SharedState::new(
        symtab,
        definitions,
        types,
        HashSet::new(),
        HashSet::new(),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    // 镜像配置注入：只有 EnumId，没有临时求解器的 get_enum 调用。
    let member = |name| {
        let (member, _, id) = shared.type_info.enum_members[&shared.symtab.lookup(name)];
        Val::Enum(EnumMember { enum_id: EnumId::from_name(id), member })
    };
    let values: Vec<_> = config
        .pma_regions
        .as_ref()
        .unwrap()
        .iter()
        .map(|region| {
            let a = &region.attributes;
            let mut fields: ahash::HashMap<_, _> = [
                ("zreadable", a.readable),
                ("zwritable", a.writable),
                ("zexecutable", a.executable),
                ("zcacheable", a.cacheable),
                ("zcoherent", a.coherent),
                ("zread_idempotent", a.read_idempotent),
                ("zwrite_idempotent", a.write_idempotent),
                ("zsupports_cbo_zzero", a.supports_cbo_zzero),
            ]
            .into_iter()
            .map(|(name, value)| (shared.symtab.lookup(name), Val::Bool(value)))
            .collect();
            fields.insert(
                shared.symtab.lookup("zreservability"),
                member(match a.reservability {
                    PmaReservability::None => "zRsrvNone",
                    PmaReservability::NonEventual => "zRsrvNonEventual",
                    PmaReservability::Eventual => "zRsrvEventual",
                }),
            );
            fields.insert(
                shared.symtab.lookup("zmisaligned_fault"),
                member(match a.misaligned_fault {
                    PmaMisalignedFault::NoFault => "zNoFault",
                    PmaMisalignedFault::AccessFault => "zAccessFault",
                    PmaMisalignedFault::AlignmentFault => "zAlignmentFault",
                }),
            );
            Val::Ctor(
                shared.symtab.lookup("zSomePMA"),
                Box::new(Val::Struct(HashMap::from_iter([
                    (shared.symtab.lookup("zbase"), Val::Bits(B64::new(region.base, 64))),
                    (
                        shared.symtab.lookup("zsizze"),
                        Val::Bits(B64::new(
                            match region.size {
                                crate::config::PmaSize::Concrete(size) => size,
                                _ => panic!("回归配置必须使用具体大小"),
                            },
                            64,
                        )),
                    ),
                    (shared.symtab.lookup("zinclude_in_device_tree"), Val::Bool(a.include_in_device_tree)),
                    (shared.symtab.lookup("zattributes"), Val::Struct(fields)),
                ]))),
            )
        })
        .collect();
    assert_ne!(values[0], values[1]);
    // 三个实际合并入口：局部变量、let 和寄存器；首个 checkpoint 不含枚举定义。
    for slot in ["var", "let", "reg"] {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let condition = solver.declare_const(smtlib::Ty::Bool, info());
        let mut solver = Solver::from_checkpoint(&context, checkpoint(&mut solver));
        let result = shared.symtab.lookup("zpma_result");
        let mut frame = make_frame(vec![
            Instr::Jump(Exp::Bool(true), 3, info()),
            Instr::Copy(Loc::Id(result), Exp::Id(test_name(900)), info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(result), Exp::Id(test_name(901)), info()),
            Instr::End,
        ]);
        for (index, value) in values.iter().enumerate() {
            frame.vars_mut().insert(test_name(900 + index as u32), UVal::Init(value.clone()));
        }
        match slot {
            "var" => frame.vars_mut().insert(result, UVal::Init(values[0].clone())),
            "let" => frame.lets_mut().insert(result, UVal::Init(values[0].clone())),
            "reg" => {
                frame.regs_mut().insert(result, false, UVal::Init(values[0].clone()));
                None
            }
            _ => unreachable!(),
        };
        let original = frame.clone();
        // 先验证事务回滚，再重试；成功登记必须进入可重放的 DefineEnum 事件。
        for rollback in [true, false] {
            let tx = solver.start_transaction();
            assert_eq!(
                merge_region_for_test(condition, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(),
                Some(4)
            );
            assert!(!frame.region_merge_records().is_empty());
            if rollback {
                solver.rollback_transaction(tx);
                frame = original.clone();
            } else {
                solver.commit_transaction();
            }
        }
        let merged = match slot {
            "var" => match &frame.vars()[&result] {
                UVal::Init(value) => value.clone(),
                _ => panic!("合并结果必须初始化"),
            },
            "let" => match &frame.lets()[&result] {
                UVal::Init(value) => value.clone(),
                _ => panic!("合并结果必须初始化"),
            },
            "reg" => frame.regs().get_last_if_initialized(result).unwrap().clone(),
            _ => unreachable!(),
        };
        let mut replay = Solver::<B64>::from_checkpoint(&context, checkpoint(&mut solver));
        for (direction, expected) in [(false, &values[0]), (true, &values[1])] {
            let tx = replay.start_transaction();
            replay
                .assert(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(condition)), Box::new(smtlib::Exp::Bool(direction))));
            assert!(replay.check_sat(info()).is_sat().unwrap());
            let mut model = Model::new(&mut replay);
            model.set_complete_model(true);
            assert_eq!(&model.get_val(&merged).unwrap(), expected, "{slot}, 条件={direction}");
            drop(model);
            replay.rollback_transaction(tx);
        }
    }
}

#[test]
fn pma_enum_reservability_merge() {
    check_pma_merge("reservability = \"none\"");
}

#[test]
fn pma_enum_reservability_non_eventual_merge() {
    check_pma_merge("reservability = \"non_eventual\"");
}

#[test]
fn pma_enum_misaligned_merge() {
    for policy in ["access_fault", "alignment_fault"] {
        check_pma_merge(&format!("misaligned = \"{policy}\""));
    }
}

#[test]
fn pma_enum_boolean_attributes_merge() {
    for field in [
        "readable",
        "writable",
        "executable",
        "cacheable",
        "coherent",
        "read_idempotent",
        "write_idempotent",
        "supports_cbo_zero",
        "include_in_device_tree",
    ] {
        check_pma_merge(&format!("{field} = false"));
    }
}
