use super::*;
use crate::bitvector::b64::B64;

fn equal(symbol: Sym, value: u64) -> Exp<Sym> {
    Exp::Eq(Box::new(Exp::Var(symbol)), Box::new(bits64(value, 8)))
}

fn not(exp: Exp<Sym>) -> Exp<Sym> {
    Exp::Not(Box::new(exp))
}

fn values(solver: &Solver<'_, B64>, symbol: Sym, expected: &[u64]) {
    let FiniteDomain::Known(values) = solver.finite_domain(symbol) else {
        panic!("应得到已确认的有限域");
    };
    assert_eq!(values, expected.iter().map(|value| bits64(*value, 8)).collect::<Vec<_>>());
}

#[test]
fn finite_domain_prefix_shares_fork_candidates_and_does_not_revisit_events() {
    configure_tastic(Tactic::Qfaufbv);
    let mut config = Config::new();
    config.solver_options.finite_domain_enumeration = true;
    let context = Context::new(config);
    let mut solver = Solver::<B64>::new(&context);
    let x = solver.declare_bitvector(8, SourceLoc::unknown());
    let allowed = Exp::Or(Box::new(equal(x, 1)), Box::new(equal(x, 2)));
    solver.assert(allowed);
    let point = checkpoint(&mut solver);
    let mut solver = Solver::<B64>::from_checkpoint(&context, point);
    let root = solver.start_transaction();
    for i in 0..257 {
        solver.define_bitvector(bits64(i, 16), SourceLoc::unknown());
    }
    let positive = equal(x, 1);
    let negative = not(positive.clone());
    PREFIX_EVENT_VISITS.set(0);
    BOUND_SEARCHES.set(0);
    assert_eq!(solver.finite_domain_bool(&positive), None);
    assert_eq!(solver.finite_domain_bool(&negative), None);
    assert_eq!((PREFIX_EVENT_VISITS.get(), BOUND_SEARCHES.get()), (0, 1));

    let first = solver.start_transaction_with_guard(Some(positive.clone()));
    assert_eq!(solver.finite_domain_bool(&positive), Some(true));
    assert_eq!(solver.finite_domain_bool(&negative), Some(false));
    solver.rollback_transaction(first);
    let second = solver.start_transaction_with_guard(Some(negative.clone()));
    assert_eq!(solver.finite_domain_bool(&positive), Some(false));
    assert_eq!(solver.finite_domain_bool(&negative), Some(true));
    solver.rollback_transaction(second);
    assert_eq!(solver.finite_domain_bool(&positive), None);
    solver.rollback_transaction(root);
}

#[test]
fn finite_domain_prefix_tracks_guarded_commit_rebinding_and_rollback() {
    configure_tastic(Tactic::Qfaufbv);
    let mut config = Config::new();
    config.solver_options.finite_domain_enumeration = true;
    let context = Context::new(config);
    let mut solver = Solver::<B64>::new(&context);
    let x = solver.declare_bitvector(8, SourceLoc::unknown());
    let g = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    let allowed = Exp::Or(Box::new(equal(x, 1)), Box::new(equal(x, 2)));
    solver.assert(allowed);
    values(&solver, x, &[1, 2]);

    let root = solver.start_transaction();
    let inner = solver.start_transaction_with_guard(Some(Exp::Var(g)));
    solver.assert(equal(x, 2));
    values(&solver, x, &[2]);
    solver.commit_transaction();
    values(&solver, x, &[1, 2]);

    let rebind = solver.start_transaction();
    solver.add(Def::DefineConst(x, bits64(3, 8)));
    assert!(matches!(solver.finite_domain(x), FiniteDomain::Unknown));
    assert_eq!(solver.finite_domain_bool(&equal(x, 3)), None);
    solver.commit_transaction();
    assert!(matches!(solver.finite_domain(x), FiniteDomain::Unknown));
    solver.rollback_transaction(root);
    values(&solver, x, &[1, 2]);

    let publish = solver.start_transaction();
    solver.with_transaction_condition(&Exp::Var(g), |solver| {
        solver.assert(equal(x, 2));
        assert_eq!(solver.finite_domain_bool(&equal(x, 1)), Some(false));
    });
    solver.commit_transaction();
    values(&solver, x, &[1, 2]);
    let point = checkpoint(&mut solver);
    let mut replayed = Solver::<B64>::from_checkpoint(&context, point);
    values(&replayed, x, &[1, 2]);
    let guarded = replayed.start_transaction_with_guard(Some(equal(x, 1)));
    assert_eq!(replayed.finite_domain_bool(&equal(x, 2)), Some(false));
    replayed.rollback_transaction(guarded);
}

#[test]
fn finite_domain_prefix_follows_trace_compaction_and_group_selection() {
    configure_tastic(Tactic::Qfaufbv);
    let mut config = Config::new();
    config.solver_options.finite_domain_enumeration = true;
    let context = Context::new(config);
    let mut solver = Solver::<B64>::new(&context);
    let x = solver.declare_bitvector(8, SourceLoc::unknown());
    solver.start_transaction();
    let discarded = solver.new_logical_arm(None);
    let left = solver.new_logical_arm(None);
    let right = solver.new_logical_arm(None);
    solver.with_logical_arm(discarded, |solver| solver.cycle_count());
    let alias = solver.with_logical_arm(left, |solver| {
        solver.assert(equal(x, 5));
        solver.define_bitvector(Exp::Var(x), SourceLoc::unknown())
    });
    values(&solver, alias, &[5]);
    solver.discard_logical_arm_effects(discarded);
    values(&solver, alias, &[5]);

    for group in solver.commit_region_groups(&[left, right]) {
        solver.select_region_group(group);
        values(&solver, alias, &[5]);
        let replayed = Solver::<B64>::from_checkpoint(&context, solver.region_group_checkpoint());
        values(&replayed, alias, &[5]);
    }
}
