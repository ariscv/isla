#![cfg(feature = "smt-thread-interrupt")]

use isla_lib::bitvector::b64::B64;
use isla_lib::smt::smtlib::{Exp, Ty};
use isla_lib::smt::{Context, Model, ModelVal, SmtResult, Solver};
use isla_lib::source_loc::SourceLoc;

#[test]
fn thread_interrupt_wrapper_uses_the_public_solver_and_model_types() {
    let context = Context::new(isla_lib::smt::Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let symbol = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    solver.assert(Exp::Var(symbol));
    assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);

    let mut model = Model::new(&solver);
    assert!(matches!(model.get_var(symbol).unwrap(), ModelVal::Exp(Exp::Bool(true))));
}

#[test]
fn model_formatting_keeps_direct_z3_semantics() {
    let mut config = isla_lib::smt::Config::new();
    config.set_param_value("model", "true");
    let context = Context::new(config);
    let mut solver = Solver::<B64>::new(&context);
    let symbol = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    solver.assert(Exp::Var(symbol));
    assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);

    let model = Model::new(&solver);
    assert!(!format!("{:?}", model).is_empty());
}
