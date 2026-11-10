//! 平台外部函数沿用原语加载入口，不修改输入 IR。
use super::*;

#[test]
fn get_16_random_bits_bodyless_val_and_extern_use_registered_primop() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    for declaration in [
        "val zget_16_random_bits : (%unit) -> %bv16",
        "val zget_16_random_bits = \"get_16_random_bits\" : (%unit) -> %bv16",
    ] {
        let text = format!(
            "{declaration}\nval zcaller : (%unit) -> %bv16\nfn zcaller(zu) {{\nreturn = zget_16_random_bits(());\nend;\n}}"
        );
        let mut symtab = Symtab::new();
        let mut defs: Vec<crate::ir::Def<Name, B64>> =
            crate::ir_parser::IrParser::new().parse(&mut symtab, crate::ir_lexer::new_ir_lexer(&text)).unwrap();
        crate::ir::insert_primops(&mut defs, &symtab, crate::ir::AssertionMode::Optimistic, &empty_isa_config());
        let caller = symtab.lookup("zcaller");
        let body = defs
            .iter()
            .find_map(|def| match def {
                crate::ir::Def::Fn(name, _, body) if *name == caller => Some(body),
                _ => None,
            })
            .unwrap();
        match &body[0] {
            Instr::PrimopUnary(_, implementation, Exp::Unit, _) => {
                let context = Context::new(Config::new());
                let mut solver = Solver::new(&context);
                let value = implementation(Val::Unit, &mut solver, info()).unwrap();
                assert!(matches!(value, Val::Symbolic(_)));
                assert_eq!(crate::primop_util::length_bits(&value, &mut solver, info()).unwrap(), 16);
                assert_eq!(primop::unary_effect(*implementation), Some(primop::Effect::WritesState));
            }
            instr => panic!("无函数体平台声明必须接入一元原语：{instr:?}"),
        }
    }
}

#[test]
fn platform_primop_registration_preserves_function_bodies_and_unknown_calls() {
    const IR: &str = r#"
val zget_16_random_bits : (%unit) -> %bv16
fn zget_16_random_bits(zu) {
  return = 0x1234;
  end;
}
val zunknown_platform_function : (%unit) -> %bv16
val zcaller : (%unit) -> %bv16
fn zcaller(zu) {
  return = zget_16_random_bits(());
  return = zunknown_platform_function(());
  end;
}
"#;
    let (symtab, mut defs) = parse_ir_string(IR);
    crate::ir::insert_primops(&mut defs, &symtab, crate::ir::AssertionMode::Optimistic, &empty_isa_config());
    let caller = symtab.lookup("zcaller");
    let body = defs
        .iter()
        .find_map(|def| match def {
            crate::ir::Def::Fn(name, _, body) if *name == caller => Some(body),
            _ => None,
        })
        .unwrap();
    assert!(matches!(body[0], Instr::Call(..)), "保留模型已有函数体");
    assert!(matches!(body[1], Instr::Call(..)), "未知函数不得变成未定义值");
}
