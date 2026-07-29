use isla_lib::bitvector::{b64::B64, BV};
use isla_lib::error::ExecError;
use isla_lib::ir::{Name, Val};
use isla_lib::smt::smtlib::{Exp, Ty};
use isla_lib::smt::{Config, Context, EnumMember, Model, ModelVal, SmtResult, Solver, Sym};
use isla_lib::source_loc::SourceLoc;

#[test]
fn solver_and_model_obey_the_common_contract() {
    let mut config = Config::new();
    config.set_param_value("model", "true");
    let context = Context::new(config);
    let mut solver = Solver::<B64>::new(&context);

    let flag = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let bits = solver.declare_const(Ty::BitVec(4), SourceLoc::unknown());
    let enum_id = solver.get_enum(Name::from_u32(4000), 3);
    let enum_symbol = solver.declare_const(Ty::Enum(enum_id), SourceLoc::unknown());
    let choice_left = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let choice_right = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let enum_member = EnumMember { enum_id, member: 2 };

    solver.assert(Exp::Var(flag));
    solver.assert_eq(Exp::Var(bits), Exp::Bits(vec![false, true, false, true]));
    solver.assert_eq(Exp::Var(enum_symbol), Exp::Enum(enum_member));
    solver.assert(Exp::Neq(Box::new(Exp::Var(choice_left)), Box::new(Exp::Var(choice_right))));

    assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
    assert_eq!(solver.check_sat_with(&Exp::Not(Box::new(Exp::Var(flag))), SourceLoc::unknown()), SmtResult::Unsat);
    assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);

    let mut model = Model::new(&solver);
    assert!(matches!(model.get_var(flag).unwrap(), ModelVal::Exp(Exp::Bool(true))));
    let ModelVal::Exp(Exp::Bits64(model_bits)) = model.get_exp(&Exp::Var(bits)).unwrap() else {
        panic!("solver did not preserve the four-bit model value")
    };
    assert_eq!(model_bits.lower_u64(), 10);
    assert!(matches!(
        model.get_var(enum_symbol).unwrap(),
        ModelVal::Exp(Exp::Enum(member)) if member == enum_member
    ));
    assert_eq!(
        model.get_val(&Val::Vector(vec![Val::Symbolic(flag), Val::Symbolic(bits)])).unwrap(),
        Val::Vector(vec![Val::Bool(true), Val::Bits(B64::new(10, 4))])
    );
    let Val::Vector(choice) =
        model.get_val(&Val::Vector(vec![Val::Symbolic(choice_left), Val::Symbolic(choice_right)])).unwrap()
    else {
        panic!("solver did not return the batched model values as a vector")
    };
    assert!(matches!(choice.as_slice(), [Val::Bool(left), Val::Bool(right)] if left != right));
    assert!(!format!("{:?}", model).is_empty());

    let unbound = Sym::from_u32(999_999);
    let ExecError::Type(_, _) = model.get_var(unbound).unwrap_err() else {
        panic!("solver changed the ordinary unbound-variable error variant")
    };
    assert!(matches!(model.get_var(flag).unwrap(), ModelVal::Exp(Exp::Bool(true))));

    drop(model);
    solver.assert(Exp::Not(Box::new(Exp::Var(flag))));
    assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Unsat);
}
