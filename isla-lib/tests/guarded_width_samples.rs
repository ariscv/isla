//! 核对原生位宽经过两种缓存编码和具体样本重放后仍然一致。
use std::collections::BTreeMap;

use isla_lib::bitvector::{b64::B64, BV};
use isla_lib::executor::{path_cache, samples};
use isla_lib::ir::{SharedState, Symtab, Val};
use isla_lib::smt::{smtlib, Config, Context, Model, Solver};
use isla_lib::source_loc::SourceLoc;

#[test]
fn region_union_width_sample_round_trip() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let guard = solver.declare_const(smtlib::Ty::Bool, SourceLoc::unknown());
    let short = Val::Bits(B64::new(3, 4));
    let long = Val::Bits(B64::new(3, 8));
    let guarded = Val::Guarded(guard, Box::new((short, long)));
    let shared = SharedState::empty(Symtab::new());
    let path = samples::SamplePath {
        terminal: Default::default(),
        pre: BTreeMap::from([("pick".into(), Val::Symbolic(guard))]),
        post: BTreeMap::new(),
        result: guarded,
        memory: Vec::new(),
        memory_guards: BTreeMap::new(),
    };
    let cached = path_cache::PathData::from(path);
    let json: path_cache::PathData<B64> = serde_json::from_slice(&serde_json::to_vec(&cached).unwrap()).unwrap();
    let bin: path_cache::PathData<B64> = bincode::deserialize(&bincode::serialize(&cached).unwrap()).unwrap();
    for cached in [json, bin] {
        let path = samples::SamplePath::from(cached);
        for (selected, bits) in [(true, "0011"), (false, "00000011")] {
            let tx = solver.start_transaction_with_guard(Some(smtlib::Exp::Bool(true)));
            solver.assert_eq(smtlib::Exp::Var(guard), smtlib::Exp::Bool(selected));
            assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
            let sample = path.materialize(&mut Model::new(&solver), &shared, "merge", 0, None).unwrap();
            assert_eq!(sample.result["bits"], bits);
            let sample = serde_json::from_slice(&serde_json::to_vec(&sample).unwrap()).unwrap();
            solver.rollback_transaction(tx);
            assert_eq!(path.check(&mut solver, &shared, &sample).unwrap(), Some(true));
        }
    }
}
