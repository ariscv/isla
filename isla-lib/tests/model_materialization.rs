use isla_lib::bitvector::{b129::B129, b64::B64, BV};
use isla_lib::ir::{BitsSegment, Name, SharedState, Symtab, Val};
use isla_lib::smt::{
    configure_tastic,
    smtlib::{Exp, Ty},
    Config, Context, Model, SmtResult, Solver, Tactic,
};
use isla_lib::source_loc::SourceLoc;

// 独立按低位到高位读回分段，验证全值与分段顺序，避免只检查宿主边界不报错。
fn concrete_bits<B: BV>(value: &Val<B>) -> Vec<bool> {
    match value {
        Val::Bits(bits) => bits.to_vec(),
        Val::MixedBits(segments) => segments
            .iter()
            .rev()
            .flat_map(|segment| match segment {
                BitsSegment::Concrete(bits) => bits.to_vec(),
                BitsSegment::Symbolic(_) => panic!("物化后不能残留符号段"),
            })
            .collect(),
        _ => panic!("必须是具体位向量"),
    }
}

fn check_widths<B: BV>() {
    configure_tastic(Tactic::Qfaufbv);
    for width in [1, 63, 64, 65, 128, 129, 130, 256, 512] {
        for pattern in 0..3 {
            let raw: Vec<bool> = (0..width)
                .map(|index| match pattern {
                    0 => index == 0 || index == width - 1 || index == 64 || index == 128,
                    1 => index % 3 == 1,
                    _ => true,
                })
                .collect();
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B>::new(&ctx);
            let info = SourceLoc::unknown();
            let sym = solver.declare_const(Ty::BitVec(width), info);
            solver.assert_eq(Exp::Var(sym), Exp::Bits(raw.clone()));
            assert_eq!(solver.check_sat(info), SmtResult::Sat);
            let mut model = Model::new(&solver);
            let value = Val::Symbolic(sym);
            let concrete = model.get_val(&value).unwrap();
            assert!(concrete.is_concrete());
            assert_eq!(concrete_bits(&concrete), raw, "宽度{width}、模式{pattern}");
            assert_eq!(matches!(concrete, Val::Bits(_)), width <= B::MAX_WIDTH);
            let shared = SharedState::<B>::empty(Symtab::new());
            assert_eq!(
                model.get_fmtval(&value).unwrap().to_str(&shared),
                model.get_fmtval(&concrete).unwrap().to_str(&shared)
            );
            let mixed = Val::MixedBits(vec![
                BitsSegment::Concrete(B::new(0x13, 5)),
                BitsSegment::Symbolic(sym),
                BitsSegment::Concrete(B::new(5, 3)),
            ]);
            let mut expected = B::new(5, 3).to_vec();
            expected.extend(&raw);
            expected.extend(B::new(0x13, 5).to_vec());
            assert_eq!(concrete_bits(&model.get_val(&mixed).unwrap()), expected);
            let mut fields = ahash::HashMap::default();
            let field = Name::from_u32(40);
            fields.insert(field, mixed);
            let composite =
                Val::List(vec![Val::Vector(vec![Val::Struct(fields)]), Val::Ctor(Name::from_u32(41), Box::new(value))]);
            let Val::List(values) = model.get_val(&composite).unwrap() else { panic!("必须保留list") };
            let Val::Vector(values0) = &values[0] else { panic!("必须保留vector") };
            let Val::Struct(fields) = &values0[0] else { panic!("必须保留struct") };
            assert_eq!(concrete_bits(&fields[&field]), expected);
            let Val::Ctor(_, payload) = &values[1] else { panic!("必须保留ctor") };
            assert_eq!(concrete_bits(payload), raw);
        }
    }
}

#[test]
fn model_materializes_wide_values_with_b64() {
    check_widths::<B64>();
}
#[test]
fn model_materializes_wide_values_with_b129() {
    check_widths::<B129>();
}

#[test]
fn wide_arbitrary_values_keep_zero_choice_without_completing_model() {
    configure_tastic(Tactic::Qfaufbv);
    for complete in [false, true] {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B129>::new(&ctx);
        let sym = solver.declare_const(Ty::BitVec(512), SourceLoc::unknown());
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        let mut model = Model::new(&solver);
        model.set_complete_model(complete);
        assert_eq!(model.get_var(sym).unwrap().is_arbitrary(), !complete);
        assert_eq!(concrete_bits(&model.get_val(&Val::Symbolic(sym)).unwrap()), vec![false; 512]);
        assert_eq!(model.get_var(sym).unwrap().is_arbitrary(), !complete);
    }
}
