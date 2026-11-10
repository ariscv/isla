//! isarch 的 RISC-V 平台适配，通用执行库不识别平台函数名。
use isla_lib::bitvector::BV;
use isla_lib::config::ISAConfig;
use isla_lib::ir::{Def, Name, Symtab};

pub fn configure<B: BV>(defs: &mut [Def<Name, B>], symtab: &Symtab, config: &mut ISAConfig<B>) {
    let Some(name) = symtab.get("zget_16_random_bits") else {
        return;
    };
    // 模型提供函数体时保持原实现；只适配缺少平台实现的声明。
    if defs.iter().any(|def| matches!(def, Def::Fn(function, _, _) if *function == name)) {
        return;
    }
    for def in defs {
        match def {
            Def::Val(function, args, result) if *function == name => {
                assert!(matches!(args.as_slice(), [isla_lib::ir::Ty::Unit]), "平台熵接口参数必须为 unit");
                assert!(matches!(result, isla_lib::ir::Ty::Bits(16)), "平台熵接口必须返回 16 位");
                *def = Def::Extern(name, false, "get_16_random_bits".into(), args.clone(), result.clone());
            }
            Def::Extern(function, abstract_call, external, args, result) if *function == name => {
                assert!(!*abstract_call && external == "get_16_random_bits", "平台熵接口外部绑定不符合契约");
                assert!(matches!(args.as_slice(), [isla_lib::ir::Ty::Unit]));
                assert!(matches!(result, isla_lib::ir::Ty::Bits(16)));
            }
            _ => continue,
        }
        config.const_primops.entry("get_16_random_bits".into()).or_insert_with(|| {
            let reset: isla_lib::ir::Reset<B> = std::sync::Arc::new(|_, _, solver| {
                Ok(isla_lib::ir::Val::Symbolic(
                    solver.declare_bitvector(16, isla_lib::source_loc::SourceLoc::unknown()),
                ))
            });
            (reset, isla_lib::primop::Effect::WritesState)
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::bitvector::b64::B64;
    use isla_lib::ir::{IRTypeInfo, Val};
    use isla_lib::smt::{Config, Context, SmtResult, Solver};
    use isla_lib::source_loc::SourceLoc;

    fn fixture(declaration: &str) -> (Symtab<'_>, Vec<Def<Name, B64>>, ISAConfig<B64>) {
        let mut symtab = Symtab::new();
        symtab.intern("zPC");
        let defs = isla_lib::ir_parser::IrParser::new()
            .parse(&mut symtab, isla_lib::ir_lexer::new_ir_lexer(declaration))
            .unwrap();
        let types = IRTypeInfo::new(&defs);
        let text = r#"pc = "PC"
assembler = "as"
objdump = "objdump"
nm = "nm"
linker = "ld"
[mmu]
page_table_base = "0"
page_size = "4096"
s2_page_table_base = "0"
s2_page_size = "4096"
[threads]
base = "0"
top = "4096"
stride = "4096"
[symbolic_addrs]
base = "4096"
top = "8192"
stride = "16"
"#;
        let config = ISAConfig::parse(text, None, &symtab, &types).unwrap();
        (symtab, defs, config)
    }

    #[test]
    fn platform_entropy_uses_fresh_unconstrained_reset_for_val_and_extern() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        for declaration in [
            "val zget_16_random_bits : (%unit) -> %bv16",
            "val zget_16_random_bits = \"get_16_random_bits\" : (%unit) -> %bv16",
        ] {
            let (symtab, mut defs, mut config) = fixture(declaration);
            configure(&mut defs, &symtab, &mut config);
            assert!(matches!(defs[0], Def::Extern(..)), "只将平台无体声明接入既有 extern 通道");
            let (reset, effect) = &config.const_primops["get_16_random_bits"];
            assert_eq!(*effect, isla_lib::primop::Effect::WritesState);
            let context = Context::new(Config::new());
            let mut solver = Solver::new(&context);
            let types = IRTypeInfo::new(&defs);
            let typedefs = isla_lib::ir::Typedefs {
                structs: &types.structs,
                enums: &types.enums,
                unions: &types.unions,
                symtab: &symtab,
            };
            let memory = isla_lib::memory::Memory::new();
            let first = reset(&memory, typedefs, &mut solver).unwrap();
            let second = reset(&memory, typedefs, &mut solver).unwrap();
            assert!(matches!(first, Val::Symbolic(_)));
            assert_ne!(first, second);
            for value in [&first, &second] {
                assert_eq!(isla_lib::primop_util::length_bits(value, &mut solver, SourceLoc::unknown()).unwrap(), 16);
            }
            for (left, right) in [(0, 0xffff), (0xffff, 0), (0x1234, 0x1234)] {
                let exp = |value: &Val<B64>| isla_lib::primop_util::smt_value(value, SourceLoc::unknown()).unwrap();
                use isla_lib::smt::smtlib::Exp;
                let condition = Exp::And(
                    Box::new(Exp::Eq(Box::new(exp(&first)), Box::new(isla_lib::smt::smtlib::bits64(left, 16)))),
                    Box::new(Exp::Eq(Box::new(exp(&second)), Box::new(isla_lib::smt::smtlib::bits64(right, 16)))),
                );
                assert_eq!(solver.check_sat_with(&condition, SourceLoc::unknown()), SmtResult::Sat);
            }
        }
    }

    #[test]
    fn platform_entropy_reaches_existing_loader_reset_channel() {
        let (symtab, mut defs, mut config) = fixture("val zget_16_random_bits : (%unit) -> %bv16\nval zcaller : (%unit) -> %bv16\nfn zcaller(zu) {\nreturn = zget_16_random_bits(());\nend;\n}");
        configure(&mut defs, &symtab, &mut config);
        let types = IRTypeInfo::new(&defs);
        let initialized = isla_lib::init::initialize_architecture(
            &mut defs,
            symtab,
            types,
            &config,
            isla_lib::ir::AssertionMode::Optimistic,
            false,
        );
        let caller = initialized.shared_state.symtab.lookup("zcaller");
        let body = initialized.shared_state.functions[&caller].2;
        assert!(
            matches!(body[0], isla_lib::ir::Instr::PrimopReset(_, _, isla_lib::primop::Effect::WritesState, _)),
            "平台随机值必须通过已有副作用分类和加载器进入执行"
        );
    }

    #[test]
    fn platform_adapter_preserves_model_body_and_unknown_declarations() {
        let (symtab, mut defs, mut config) = fixture("val zget_16_random_bits : (%unit) -> %bv16\nfn zget_16_random_bits(zu) {\nreturn = 0x1234;\nend;\n}\nval zunknown : (%unit) -> %bv16");
        configure(&mut defs, &symtab, &mut config);
        assert!(matches!(defs[0], Def::Val(..)));
        assert!(matches!(defs[1], Def::Fn(..)));
        assert!(matches!(defs[2], Def::Val(..)));
        assert!(!config.const_primops.contains_key("get_16_random_bits"));
    }
}
