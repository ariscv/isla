use super::*;
use crate::bitvector::{b64::B64, BV};

fn solver_config(enabled: bool) -> Config {
    let mut cfg = Config::new();
    cfg.solver_options.coi_query_slicing = enabled;
    cfg
}

#[test]
fn stage3_coi_matches_unsliced_z3_for_disjoint_assertions() {
    configure_tastic(Tactic::Qfaufbv);
    let full_ctx = Context::new(solver_config(false));
    let sliced_ctx = Context::new(solver_config(true));
    let loc = SourceLoc::unknown();
    let mut rng = 0x79df_a432_u32;
    let mut next = || {
        rng ^= rng << 13;
        rng ^= rng >> 17;
        rng ^= rng << 5;
        u64::from(rng)
    };
    let constant = |n| Box::new(Exp::Bits64(B64::new(n, 8)));
    let mut dropped = 0;
    for sample in 0..128 {
        let mut full = Solver::<B64>::new(&full_ctx);
        let mut sliced = Solver::<B64>::new(&sliced_ctx);
        let mut goals = Vec::new();
        let lengths = [1 + next() % 5, 1 + next() % 5, 1 + next() % 5];
        let values = [next() % 16, next() % 16, next() % 16];
        for solver in [&mut full, &mut sliced] {
            let vars: Vec<_> = (0..3).map(|_| solver.declare_bitvector(8, loc)).collect();
            for (group, &var) in vars.iter().enumerate() {
                let alias = solver.define_const(Exp::Bvadd(Box::new(Exp::Var(var)), constant(1)), loc);
                for i in 0..lengths[group] {
                    solver.assert(Exp::Neq(Box::new(Exp::Var(alias)), constant(values[group] + i + 1)));
                }
                if sample % 8 == 0 && group == 2 {
                    solver.assert_eq(Exp::Var(var), *constant(values[group]));
                }
            }
            goals.push(Exp::Eq(Box::new(Exp::Var(vars[0])), constant(values[0] + (sample % 2))));
        }
        assert_eq!(goals[0], goals[1]);
        assert_eq!(
            sliced.coi_feasibility(&[goals[1].clone()], Some(&goals[1]), loc, "branch_feasibility"),
            Some(full.check_sat_with(&goals[0], loc)),
            "随机断言集合 {sample}"
        );
        dropped += sliced.coi_removed_assertions();
    }
    assert!(dropped >= 256, "定向检查必须实际移除断言");
}

#[test]
fn stage3_coi_follows_definition_links_and_keeps_full_model_api() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(solver_config(true));
    let loc = SourceLoc::unknown();
    let mut solver = Solver::<B64>::new(&ctx);
    let x = solver.declare_bitvector(8, loc);
    let y = solver.declare_bitvector(8, loc);
    let independent = solver.declare_const(Ty::Bool, loc);
    let alias = solver.define_const(Exp::Bvadd(Box::new(Exp::Var(x)), Box::new(Exp::Bits64(B64::new(1, 8)))), loc);
    solver.assert_eq(Exp::Var(alias), Exp::Var(y));
    solver.assert_eq(Exp::Var(y), Exp::Bits64(B64::new(9, 8)));
    solver.assert(Exp::Var(independent));
    let invalid = Exp::Eq(Box::new(Exp::Var(x)), Box::new(Exp::Bits64(B64::new(9, 8))));
    assert_eq!(solver.coi_feasibility(&[invalid.clone()], Some(&invalid), loc, "branch_feasibility"), Some(Unsat));
    assert_eq!(solver.coi_removed_assertions(), 1);
    assert!(!solver.has_stashed_model());
    assert_eq!(solver.check_sat(loc), Sat);
    assert_eq!(solver.cached_bool_value(&Exp::Var(independent)).unwrap(), Some(true));
}
