//! 非叶页表项的递归路径。读取次数只用于观测，守卫仍取自冻结 IR 的整数运算。
use super::*;

const WALK: &str = r#"
val zwiden = "%i64->%i" : (%i64) -> %i
val znarrow = "%i->%i64" : (%i) -> %i64
val zgt_int = "gt" : (%i, %i) -> %bool
val zsub_atom = "sub_int" : (%i, %i) -> %i
val zoverrun : (%unit) -> %i64
fn zoverrun(zunit) {
  return = 6;
  end;
}
val zpt_walk : (%i64, %i64) -> %i64
fn zpt_walk(zlevel, zreads) {
  jump @eq(zreads, 6) goto 16;
  zwide : %i;
  zwide = zwiden(zlevel);
  zzero : %i;
  zzero = zwiden(0);
  zpositive : %bool;
  zpositive = zgt_int(zwide, zzero);
  jump zpositive goto 10;
  return = zreads;
  goto 17;
  zwide_one : %i;
  zwide_one = zwiden(1);
  zwide = zsub_atom(zwide, zwide_one);
  zlevel = znarrow(zwide);
  return = zpt_walk(zlevel, @iadd(zreads, 1));
  goto 17;
  return = zoverrun(());
  end;
}
"#;

fn check_walk(defer: bool) {
    use smtlib::bits64;
    use smtlib::Exp::{Eq, Ite, Var};

    crate::config::RegionOptions { defer_exit_check: defer, ..Default::default() }.configure();
    let (mut shared, _, _) = shared_state_and_bindings_from_ir(WALK);
    let walk = shared.symtab.lookup("zpt_walk");
    let overrun = shared.symtab.lookup("zoverrun");
    let (params, ty, _) = shared.functions[&overrun].clone();
    let poison = Instr::PrimopReset(
        Loc::Id(RETURN),
        Arc::new(move |_, _, solver| {
            panic!("发生第六次读取，defer={defer}，延后作用域={}", solver.region_queries_deferred())
        }),
        primop::Effect::Pure,
        info(),
    );
    shared.functions.insert(overrun, (params, ty, Box::leak(vec![poison, Instr::End].into_boxed_slice())));

    // 分页路径在外层区域中执行，其余路径返回 0。
    let level = shared.symtab.intern("zinitial_level");
    let program = vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::I64(0), info()),
        Instr::Goto(4),
        Instr::Call(Loc::Id(RETURN), false, walk, vec![Exp::Id(level), Exp::I64(1)], info()),
        Instr::End,
    ];
    let mut width = None;
    let (paths, _, _) = paths_with_solver_state(
        program,
        &shared,
        1,
        ExecutionLimits::default().with_path_merging(true),
        crate::memory::Memory::new(),
        |frame, solver| {
            let sv_width = solver.declare_const(smtlib::Ty::BitVec(64), info());
            width = Some(sv_width);
            let initial = [(48, 3), (39, 2), (32, 1)].into_iter().fold(bits64(4, 64), |rest, (width, level)| {
                Ite(
                    Box::new(Eq(Box::new(Var(sv_width)), Box::new(bits64(width, 64)))),
                    Box::new(bits64(level, 64)),
                    Box::new(rest),
                )
            });
            frame.vars_mut().insert(level, UVal::Init(Val::Symbolic(solver.define_const(initial, info()))));
        },
        false,
    );

    // 非叶且 level=0 时的返回值记录 Invalid_PTE 所在的读取次数。
    let ctx = Context::new(Config::new());
    for (mode, reads) in [(32, 2), (39, 3), (48, 4), (57, 5)] {
        let mut witnessed = false;
        for path in &paths {
            let mut solver = Solver::from_checkpoint(&ctx, path.checkpoint.clone());
            solver.assert(Var(Sym { id: 0 }));
            solver.assert(Eq(Box::new(Var(width.unwrap())), Box::new(bits64(mode, 64))));
            let expected = Eq(Box::new(smt_value(&path.value, info()).unwrap()), Box::new(bits64(reads, 64)));
            assert!(solver.check_sat_with(&smtlib::Exp::Not(Box::new(expected.clone())), info()).is_unsat().unwrap());
            witnessed |= solver.check_sat_with(&expected, info()).is_sat().unwrap();
        }
        assert!(witnessed, "宽度 {mode} 必须在第 {reads} 次读取返回 Invalid_PTE");
    }
}

#[test]
fn ptwalk_bound_deferred() {
    if run_in_diagnostics_process(concat!(module_path!(), "::ptwalk_bound_deferred")) {
        run_deep_region_test(|| check_walk(true));
    }
}

#[test]
fn ptwalk_bound_eager() {
    if run_in_diagnostics_process(concat!(module_path!(), "::ptwalk_bound_eager")) {
        run_deep_region_test(|| check_walk(false));
    }
}

#[test]
fn ptwalk_bound_signed_thresholds_allow_wraparound() {
    use smtlib::bits64;
    use smtlib::Exp::*;
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let choice = solver.declare_const(smtlib::Ty::Bool, info());
    let pair = |a, b| Ite(Box::new(Var(choice)), Box::new(bits64(a, 8)), Box::new(bits64(b, 8)));
    let zero = || Box::new(bits64(0, 8));
    let decremented = |a, b| Box::new(Bvsub(Box::new(pair(a, b)), Box::new(bits64(1, 8))));
    // 0 和 1 减一得到 -1 和 0；严格与非严格比较在端点的结论不同。
    assert_eq!(solver.structural_bool(&Bvsgt(decremented(0, 1), zero())), Some(false));
    assert_eq!(solver.structural_bool(&Bvsle(decremented(0, 1), zero())), Some(true));
    assert_eq!(solver.structural_bool(&Bvslt(decremented(0, 1), zero())), None);
    assert_eq!(solver.structural_bool(&Bvsge(zero(), decremented(0, 1))), Some(true));
    // -128 减一在八位位向量上回绕到 127；另一候选 0 减一得到 -1。
    assert_eq!(solver.structural_bool(&Bvsgt(decremented(128, 0), zero())), None);
}
