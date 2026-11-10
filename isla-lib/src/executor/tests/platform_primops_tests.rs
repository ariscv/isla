//! 通用库只按显式 extern 接线，不识别 RISC-V 平台声明。
use super::*;

#[test]
fn library_keeps_bodyless_model_calls_outside_explicit_externs() {
    const IR: &str = "val zundefined_bool : (%unit) -> %bool\nval zcaller : (%unit) -> %bool\nfn zcaller(zu) {\nreturn = zundefined_bool(());\nend;\n}";
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
    assert!(matches!(body[0], Instr::Call(..)), "未声明 extern 的模型调用不能因同名而替换成原语");
}

#[test]
fn library_primop_registry_does_not_define_riscv_entropy_platform() {
    assert!(!primop::unary_primops::<B64>().contains_key("get_16_random_bits"));
}
