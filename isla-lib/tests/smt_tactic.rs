use isla_lib::bitvector::b64::B64;
use isla_lib::smt::{configure_tastic, Config, Context, SmtResult, Solver, Tactic};
use isla_lib::source_loc::SourceLoc;

#[test]
fn tactic_choices_are_explicit() {
    assert_eq!(Tactic::default(), Tactic::Qfaufbv);
    for (name, tactic) in [("default", Tactic::Default), ("qfaufbv", Tactic::Qfaufbv), ("smt", Tactic::Smt)] {
        assert_eq!(name.parse::<Tactic>().unwrap(), tactic);
    }
    for name in ["", "skip", "isla-invalid-tactic"] {
        assert!(name.parse::<Tactic>().is_err(), "不应接受 tactic：{name}");
    }
}

#[test]
fn default_tactic_can_solve() {
    configure_tastic(Tactic::default());
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&ctx);
    assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
}
