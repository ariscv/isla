use super::*;
use crate::smt::{smtlib::Ty, Config, Context, ModelVal};

#[test]
fn random_fill_unconstrained_model_completion_is_zero_or_arbitrary() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let free = solver.declare_bitvector(64, SourceLoc::unknown());
    assert!(sat(&mut solver).unwrap());
    let mut model = Model::new(&solver);
    assert!(matches!(model.get_exp(&Exp::Var(free)).unwrap(), ModelVal::Arbitrary(Ty::BitVec(64))));
    model.set_complete_model(true);
    assert_eq!(model.get_exp(&Exp::Var(free)).unwrap().unwrap_exp(), Exp::Bits64(B64::new(0, 64)));
}

#[test]
fn random_fill_preserves_constraints_aliases_inactive_reads_and_post_state() {
    use crate::smt::smtlib::bits64;
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new_for_samples(&context, Some(42));
    let x = solver.declare_bitvector(64, SourceLoc::unknown());
    let byte = solver.declare_bitvector(8, SourceLoc::unknown());
    let inactive = solver.declare_bitvector(8, SourceLoc::unknown());
    let result = solver.define_const(Exp::Bvadd(Box::new(Exp::Var(x)), Box::new(bits64(1, 64))), SourceLoc::unknown());
    solver.assert(Exp::Eq(Box::new(Exp::Extract(3, 0, Box::new(Exp::Var(x)))), Box::new(bits64(5, 4))));
    solver.assert(Exp::Eq(Box::new(Exp::Var(byte)), Box::new(Exp::Extract(7, 0, Box::new(Exp::Var(x))))));
    let read = |value, address| Event::ReadMem {
        value: Val::Symbolic(value),
        read_kind: Val::Unit,
        address: Val::Bits(B64::new(address, 64)),
        bytes: 1,
        tag_value: None,
        opts: Default::default(),
        region: "mem",
    };
    let path = SamplePath {
        terminal: Terminal::Normal,
        pre: BTreeMap::from([("x".into(), Val::Symbolic(x)), ("alias".into(), Val::Symbolic(x))]),
        post: BTreeMap::from([("x".into(), Val::Symbolic(result))]),
        result: Val::Symbolic(result),
        memory: vec![read(byte, 4096), read(byte, 4096), read(inactive, 8192)],
        memory_guards: BTreeMap::from([(2, Exp::Bool(false))]),
    };
    let shared = SharedState::empty(crate::ir::Symtab::new());
    let condition = Exp::Bool(true);
    assert!(sat(&mut solver).unwrap());
    fill_arbitrary_inputs(&mut solver, &condition, &mut || 0xfedcba9876543210).unwrap();
    assert!(solver.check_sat_with(&condition, SourceLoc::unknown()).is_sat().unwrap());
    let sample = path.materialize(&mut Model::new(&solver), &shared, "merge", 1, Some(0)).unwrap();
    let x_value = u64::from_str_radix(sample.pre_registers["x"]["bits"].as_str().unwrap(), 2).unwrap();
    assert_eq!(x_value & 15, 5);
    assert_eq!(sample.pre_registers["x"], sample.pre_registers["alias"]);
    assert_eq!(sample.pre_memory.len(), 1);
    assert_eq!(sample.pre_memory[0].value, Some(x_value as u8));
    assert_eq!(
        u64::from_str_radix(sample.post_registers["x"]["bits"].as_str().unwrap(), 2).unwrap(),
        x_value.wrapping_add(1)
    );
    assert_eq!(path.check(&mut solver, &shared, &sample).unwrap(), Some(true));
}

#[test]
fn random_phase_constrained_values_change_and_free_values_use_isla_stream() {
    use crate::smt::smtlib::bits64;
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let run = |seed| {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new_for_samples(&context, Some(seed));
        let x = solver.declare_bitvector(64, SourceLoc::unknown());
        let y = solver.declare_bitvector(64, SourceLoc::unknown());
        let u = solver.declare_bitvector(64, SourceLoc::unknown());
        solver.assert(Exp::Bvugt(Box::new(Exp::Var(x)), Box::new(bits64(5, 64))));
        solver.assert(Exp::Eq(Box::new(Exp::Extract(7, 0, Box::new(Exp::Var(y)))), Box::new(bits64(0xa5, 8))));
        assert!(sat(&mut solver).unwrap());
        assert!(Model::new(&solver).get_var(u).unwrap().is_arbitrary());
        let mut words = 0;
        fill_arbitrary_inputs(&mut solver, &Exp::Bool(true), &mut || {
            words += 1;
            0xfedcba9876543210
        })
        .unwrap();
        assert_eq!(words, 1, "只有完全无约束的 u 使用 Isla 随机流");
        let mut model = Model::new(&solver);
        let value = |model: &mut Model<B64>, symbol| match model.get_var(symbol).unwrap().unwrap_exp() {
            Exp::Bits64(bits) => bits.lower_u64(),
            value => panic!("预期 64 位具体值：{value:?}"),
        };
        let values = [value(&mut model, x), value(&mut model, y), value(&mut model, u)];
        assert!(values[0] > 5);
        assert_eq!(values[1] & 255, 0xa5);
        assert_eq!(values[2], 0xfedcba9876543210);
        values
    };
    assert_eq!(run(42), run(42));
    assert_ne!(run(42)[0], run(43)[0]);
}

#[test]
fn samples_without_random_phase_match_seeded_baseline() {
    use crate::smt::smtlib::bits64;
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let run = |samples| {
        let context = Context::new(Config::new());
        let mut solver = if samples {
            Solver::<B64>::new_for_samples(&context, None)
        } else {
            Solver::<B64>::new_seeded(&context, 0)
        };
        let x = solver.declare_bitvector(64, SourceLoc::unknown());
        solver.assert(Exp::Bvugt(Box::new(Exp::Var(x)), Box::new(bits64(5, 64))));
        assert!(sat(&mut solver).unwrap());
        let concrete = Model::new(&solver).get_var(x).unwrap().unwrap_exp();
        concrete
    };
    assert_eq!(run(false), run(true));
}

#[test]
fn random_fill_handles_booleans_wide_vectors_and_repeated_aliases() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new_for_samples(&context, Some(42));
    let wide = solver.declare_bitvector(129, SourceLoc::unknown());
    let flag = solver.declare_const(Ty::Bool, SourceLoc::unknown());
    assert!(sat(&mut solver).unwrap());
    let mut words = [u64::MAX, 0, 1, 1].into_iter();
    fill_arbitrary_inputs(&mut solver, &Exp::Bool(true), &mut || words.next().unwrap()).unwrap();
    assert_eq!(words.next(), None);
    let mut model = Model::new(&solver);
    let Exp::Bits(bits) = model.get_var(wide).unwrap().unwrap_exp() else { panic!("预期宽位向量") };
    assert_eq!(bits.len(), 129);
    assert!(bits[..64].iter().all(|bit| *bit));
    assert!(bits[64..128].iter().all(|bit| !*bit));
    assert!(bits[128]);
    assert_eq!(model.get_var(flag).unwrap().unwrap_exp(), Exp::Bool(true));
    assert_eq!(model.get_var(wide).unwrap().unwrap_exp(), Exp::Bits(bits));
}

#[test]
fn random_fill_keeps_the_random_phase_witness_for_constrained_scalars() {
    use crate::smt::smtlib::bits64;
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new_for_samples(&context, Some(42));
    let x = solver.declare_bitvector(64, SourceLoc::unknown());
    let array =
        solver.declare_const(Ty::Array(Box::new(Ty::BitVec(64)), Box::new(Ty::BitVec(64))), SourceLoc::unknown());
    let read =
        solver.define_const(Exp::Select(Box::new(Exp::Var(array)), Box::new(bits64(0, 64))), SourceLoc::unknown());
    for n in 0..128 {
        solver.declare_bitvector(64 + n % 2, SourceLoc::unknown());
    }
    solver.assert(Exp::Bvugt(Box::new(Exp::Var(x)), Box::new(bits64(5, 64))));
    solver.assert(Exp::Bvugt(Box::new(Exp::Var(read)), Box::new(bits64(5, 64))));
    let condition = Exp::Bvult(Box::new(Exp::Var(x)), Box::new(bits64(1 << 63, 64)));
    assert!(solver.check_sat_with(&condition, SourceLoc::unknown()).is_sat().unwrap());
    let mut model = Model::new(&solver);
    let before = [model.get_var(x).unwrap().unwrap_exp(), model.get_var(read).unwrap().unwrap_exp()];
    drop(model);
    fill_arbitrary_inputs(&mut solver, &condition, &mut || 0xfedcba9876543210).unwrap();
    let mut model = Model::new(&solver);
    assert_eq!([model.get_var(x).unwrap().unwrap_exp(), model.get_var(read).unwrap().unwrap_exp()], before);
}
