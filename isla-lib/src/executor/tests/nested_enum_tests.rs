//! 配置具体枚举绕过 IR 常量读取后，仍须在区域合并前登记类型。
use super::*;
use crate::smt::{EnumId, EnumMember};

const NESTED_ENUM_IR: &str = r#"
register zPC : %bv64
enum zChoice { zChoiceFirst, zChoiceMiddle, zChoiceLast }
enum zstatus { zStatusFirst, zStatusMiddle, zStatusLast }
struct zInnerRecord {
  zflag0: %bool, zflag1: %bool, zflag2: %bool,
  zflag3: %bool, zflag4: %bool,
  zflag5: %bool, zflag6: %bool,
  zflag7: %bool,
  zstatus: %enum zstatus,
  zchoice: %enum zChoice
}
struct zOuterRecord {
  zbase: %bv64, zsizze: %bv64,
  zenabled: %bool, zpayload: %struct zInnerRecord
}
union zOptionRecord { zSomeRecord: %struct zOuterRecord, zNoneRecord: %unit }
register zrecord_result : %union zOptionRecord
"#;

// 通用夹具保留嵌套 record、union、两种枚举与布尔字段，不依赖架构配置。
fn check_nested_enum_merge(field: &str, replacement: &str) {
    let (symtab, definitions) = parse_ir_string(NESTED_ENUM_IR);
    let types = IRTypeInfo::new(&definitions);
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
    let values: Vec<_> = [0x8000_0000, 0x3000_0000]
        .into_iter()
        .enumerate()
        .map(|(index, base)| {
            let mut fields: ahash::HashMap<_, _> =
                ["flag0", "flag1", "flag2", "flag3", "flag4", "flag5", "flag6", "flag7"]
                    .into_iter()
                    .map(|name| {
                        let value = !(index == 1 && name == field);
                        (shared.symtab.lookup(&zencode::encode(name)), Val::Bool(value))
                    })
                    .collect();
            for (name, default) in [("choice", "zChoiceLast"), ("status", "zStatusFirst")] {
                let value = if index == 1 && name == field { replacement } else { default };
                fields.insert(shared.symtab.lookup(&zencode::encode(name)), member(value));
            }
            Val::Ctor(
                shared.symtab.lookup("zSomeRecord"),
                Box::new(Val::Struct(HashMap::from_iter([
                    (shared.symtab.lookup("zbase"), Val::Bits(B64::new(base, 64))),
                    (shared.symtab.lookup("zsizze"), Val::Bits(B64::new(4096, 64))),
                    (shared.symtab.lookup("zenabled"), Val::Bool(!(index == 1 && field == "enabled"))),
                    (shared.symtab.lookup("zpayload"), Val::Struct(fields)),
                ]))),
            )
        })
        .collect();
    assert_ne!(values[0], values[1]);
    // 三个实际合并入口：局部变量、let 和寄存器；首个 checkpoint 不含枚举定义。
    for slot in ["var", "let", "reg"] {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let condition = solver.declare_const(smtlib::Ty::Bool, info());
        let mut solver = Solver::from_checkpoint(&context, checkpoint(&mut solver));
        let result = shared.symtab.lookup("zrecord_result");
        let mut frame = make_frame(vec![
            Instr::Jump(Exp::Id(test_name(902)), 3, info()),
            Instr::Copy(Loc::Id(result), Exp::Id(test_name(900)), info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(result), Exp::Id(test_name(901)), info()),
            Instr::End,
        ]);
        // 现行常量剪边会折叠 true；夹具必须用真实符号条件保留两臂。
        frame.vars_mut().insert(test_name(902), UVal::Init(Val::Symbolic(condition)));
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
fn nested_enum_first_member_merge() {
    check_nested_enum_merge("choice", "zChoiceFirst");
}

#[test]
fn nested_enum_second_member_merge() {
    check_nested_enum_merge("choice", "zChoiceMiddle");
}

#[test]
fn nested_enum_other_type_merge() {
    for policy in ["zStatusMiddle", "zStatusLast"] {
        check_nested_enum_merge("status", policy);
    }
}

#[test]
fn nested_enum_boolean_fields_merge() {
    for field in ["flag0", "flag1", "flag2", "flag3", "flag4", "flag5", "flag6", "flag7", "enabled"] {
        check_nested_enum_merge(field, "false");
    }
}
