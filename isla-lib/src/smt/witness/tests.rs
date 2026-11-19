use super::*;
use crate::bitvector::b64::B64;

#[test]
fn witness_randomization_is_reproducible_and_respects_path() {
    configure_tastic(Tactic::Qfaufbv);
    let run = |seed| {
        let mut config = Config::new();
        config.set_param_value("model", "true");
        let context = Context::new(config);
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let free = solver.declare_bitvector(16, info);
        let fixed = solver.declare_bitvector(16, info);
        solver.assert(Exp::Eq(Box::new(Exp::Var(fixed)), Box::new(smtlib::bits64(0xfedc, 16))));
        assert_eq!(solver.check_sat(info), SmtResult::Sat);
        let randomized = solver.randomize_witness(&[free, fixed, free], seed, 89);
        let mut model = solver.take_stashed_model().unwrap();
        model.set_complete_model(true);
        let value = model.get_var(free).unwrap().unwrap_exp();
        assert_eq!(model.get_var(fixed).unwrap().unwrap_exp(), smtlib::bits64(0xfedc, 16));
        drop(model);
        // 随机偏好从未成为路径断言。
        assert_eq!(
            solver.check_sat_with(&Exp::Neq(Box::new(Exp::Var(free)), Box::new(value.clone())), info),
            SmtResult::Sat
        );
        (value, randomized)
    };
    let witnesses: Vec<_> = (0..24).map(run).collect();
    assert_eq!(witnesses[13], run(13));
    assert!(witnesses.iter().any(|(_, record)| record.injected == 1 && record.attempted == 2));
    assert!(witnesses.iter().any(|(_, record)| record.injected == 0 && record.attempted == 2));
    assert!(witnesses.iter().any(|(value, _)| *value != witnesses[0].0));
}
