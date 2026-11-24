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

// 页表递归保留 IR 中的 128 位减法和 64 位回写。
fn superpage_level(solver: &mut Solver<B64>, decrements: usize) -> (Sym, Sym, Sym) {
    use smtlib::bits64;
    use smtlib::Exp::*;
    let sv39 = solver.declare_const(smtlib::Ty::Bool, info());
    let sv48 = solver.declare_const(smtlib::Ty::Bool, info());
    let rest =
        solver.define_const(Ite(Box::new(Var(sv48)), Box::new(bits64(3, 128)), Box::new(bits64(4, 128))), info());
    let mut level =
        solver.define_const(Ite(Box::new(Var(sv39)), Box::new(bits64(2, 128)), Box::new(Var(rest))), info());
    for _ in 0..decrements {
        let prev = solver.define_const(Bvsub(Box::new(Var(level)), Box::new(bits64(1, 128))), info());
        let lo = solver.define_const(Extract(63, 0, Box::new(Var(prev))), info());
        level = solver.define_const(SignExtend(64, Box::new(Var(lo))), info());
    }
    (sv39, sv48, level)
}

#[test]
fn ptwalk_zeros_positive_arm_projects_level() {
    if !run_in_diagnostics_process(concat!(module_path!(), "::ptwalk_zeros_positive_arm_projects_level")) {
        return;
    }
    run_deep_region_test(|| {
        use smtlib::bits64;
        use smtlib::Exp as F;

        crate::config::RegionOptions { defer_exit_check: true, ..Default::default() }.configure();
        let (mut shared, _, _) = shared_state_and_bindings_from_ir(
            r#"
val zwiden = "%i64->%i" : (%i64) -> %i
val znarrow = "%i->%i64" : (%i) -> %i64
val zgt = "gt" : (%i,%i) -> %bool
val zmul = "mult_int" : (%i,%i) -> %i
val zzeros = "zeros" : (%i) -> %bv
val zlength = "length" : (%bv) -> %i
val zwalk : (%i64) -> %i
fn zwalk(zlevel) {
    zwide : %i;
    zwide = zwiden(zlevel);
    zc : %i;
    zc = zwiden(0);
    zp : %bool;
    zp = zgt(zwide, zc);
    jump zp goto 9;
    return = zc;
    goto 18;
    zc = zwiden(9);
    zn : %i;
    zn = zmul(zwide, zc);
    zsmall : %i64;
    zsmall = znarrow(zn);
    zn = zwiden(zsmall);
    zb : %bv;
    zb = zzeros(zn);
    return = zlength(zb);
    end;
}
"#,
        );
        let walk = shared.symtab.lookup("zwalk");
        let level = shared.symtab.intern("zinput_level");
        let prog = vec![Instr::Call(Loc::Id(RETURN), false, walk, vec![Exp::Id(level)], info()), Instr::End];
        crate::smt::reset_test_mandatory_query_count();
        for (decrements, exclude_long) in [(3, false), (2, false), (2, true)] {
            let mut input = None;
            let (paths, _, rejects) = paths_with_solver_state(
                prog.clone(),
                &shared,
                0,
                ExecutionLimits::default().with_path_merging(true),
                crate::memory::Memory::new(),
                |frame, solver| {
                    let (sv39, sv48, wide_level) = superpage_level(solver, decrements);
                    let other = solver.declare_bitvector(64, info());
                    solver.assert(F::Bvule(Box::new(F::Var(other)), Box::new(bits64(100, 64))));
                    if exclude_long {
                        // 在保留原前缀的独立认证中，sv48=false 与 other 的两条范围约束矛盾。
                        solver.assert(F::Or(
                            Box::new(F::Var(sv48)),
                            Box::new(F::Bvugt(Box::new(F::Var(other)), Box::new(bits64(200, 64)))),
                        ));
                    }
                    input = Some((sv39, sv48));
                    let value = solver.define_const(F::Extract(63, 0, Box::new(F::Var(wide_level))), info());
                    frame.vars_mut().insert(level, UVal::Init(Val::Symbolic(value)));
                },
                false,
            );
            assert_eq!(crate::smt::test_mandatory_query_count(), 0, "{rejects}");
            let ctx = Context::new(Config::new());
            let (sv39, sv48) = input.unwrap();
            for (a, b, initial) in [(true, true, 2usize), (true, false, 2), (false, true, 3), (false, false, 4)] {
                let n = (initial.saturating_sub(decrements) * 9) as u64;
                let mut reached = false;
                for p in &paths {
                    let mut v = Solver::from_checkpoint(&ctx, p.checkpoint.clone());
                    v.assert_eq(F::Var(sv39), F::Bool(a));
                    v.assert_eq(F::Var(sv48), F::Bool(b));
                    let good = F::Eq(Box::new(smt_value(&p.value, info()).unwrap()), Box::new(bits64(n, 128)));
                    assert!(v.check_sat_with(&F::Not(Box::new(good.clone())), info()).is_unsat().unwrap());
                    reached |= v.check_sat_with(&good, info()).is_sat().unwrap();
                }
                assert_eq!(reached, !exclude_long || b);
            }
        }
    });
}

#[test]
fn finite_domain_ptwalk_zeros_projects_signed_arm_through_narrowing() {
    use crate::smt::FiniteDomain;
    use smtlib::bits64;
    use smtlib::Exp::*;
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let mut cfg = Config::new();
    cfg.solver_options.finite_domain_enumeration = true;
    let ctx = Context::new(cfg);
    let mut solver = Solver::<B64>::new(&ctx);
    let (_, _, level) = superpage_level(&mut solver, 3);
    let positive = solver.define_const(Bvsgt(Box::new(Var(level)), Box::new(bits64(0, 128))), info());
    let product = solver.define_const(Bvmul(Box::new(bits64(9, 128)), Box::new(Var(level))), info());
    let lo = solver.define_const(Extract(63, 0, Box::new(Var(product))), info());
    let width = solver.define_const(SignExtend(64, Box::new(Var(lo))), info());
    let lengths = |values: &[i128]| values.iter().copied().map(crate::primop_util::smt_i128).collect::<Vec<_>>();
    let original = solver.finite_domain(width);
    let tx = solver.start_transaction_with_guard(Some(Var(positive)));
    assert_eq!(solver.finite_domain(width), FiniteDomain::Bounded(lengths(&[-9, 0, 9])));
    solver.rollback_transaction(tx);

    for residual in [false, true] {
        if residual {
            let other = solver.declare_bitvector(64, info());
            solver.assert(Bvule(Box::new(Var(other)), Box::new(bits64(100, 64))));
        }
        let expected = |values: &[i128]| {
            if residual {
                FiniteDomain::Bounded(lengths(values))
            } else {
                FiniteDomain::Known(lengths(values))
            }
        };
        solver.with_deferred_region_queries(|solver| {
            let tx = solver.start_transaction_with_guard(Some(Var(positive)));
            crate::smt::reset_test_mandatory_query_count();
            assert_eq!(solver.finite_domain(width), expected(&[9]));
            let zero_value = primop::unary_primops()["zeros"](Val::Symbolic(width), solver, info()).unwrap();
            assert_eq!(crate::smt::test_mandatory_query_count(), 0);
            solver.assert_test_bitvector(&zero_value, B64::zeros(9));
            solver.rollback_transaction(tx);
            let sibling = solver.start_transaction_with_guard(Some(Not(Box::new(Var(positive)))));
            assert_eq!(solver.finite_domain(width), expected(&[-9, 0]));
            solver.rollback_transaction(sibling);
        });
        if !residual {
            assert_eq!(solver.finite_domain(width), original);
        }
    }
}

// 标签与载荷共用分支。深臂从零递减时错误标签生效，负载荷仍保留。
fn merged_length(solver: &mut Solver<B64>) -> ((Sym, Sym, Sym), Sym, Sym) {
    use smtlib::bits64;
    use smtlib::Exp as F;
    let mode_a = solver.declare_const(smtlib::Ty::Bool, info());
    let mode_b = solver.declare_const(smtlib::Ty::Bool, info());
    let mode_sort = solver.get_enum(Name::from_u32(8100), 3);
    let member = |member| F::Enum(crate::smt::EnumMember { enum_id: mode_sort, member });
    let mode = solver.define_const(
        F::Ite(
            Box::new(F::Var(mode_a)),
            Box::new(member(0)),
            Box::new(F::Ite(Box::new(F::Var(mode_b)), Box::new(member(1)), Box::new(member(2)))),
        ),
        info(),
    );
    let matches = |index| F::Eq(Box::new(F::Var(mode)), Box::new(member(index)));
    let first = solver.define_const(matches(0), info());
    let second = solver.define_const(matches(1), info());
    let initial = solver.define_const(
        F::Ite(
            Box::new(F::Var(first)),
            Box::new(bits64(2, 128)),
            Box::new(F::Ite(Box::new(F::Var(second)), Box::new(bits64(3, 128)), Box::new(bits64(4, 128)))),
        ),
        info(),
    );
    let prior = solver.define_const(F::Bvsub(Box::new(F::Var(initial)), Box::new(bits64(2, 128))), info());
    let route = solver.declare_bitvector(8, info());
    let deep = solver.define_const(F::Bvugt(Box::new(F::Var(route)), Box::new(bits64(10, 8))), info());
    let allow = solver.define_const(F::Bvsgt(Box::new(F::Var(prior)), Box::new(bits64(0, 128))), info());
    let next = solver.define_const(F::Bvsub(Box::new(F::Var(prior)), Box::new(bits64(1, 128))), info());
    let narrow = solver.define_const(F::Extract(63, 0, Box::new(F::Var(next))), info());
    let merged =
        solver.define_const(F::Ite(Box::new(F::Var(deep)), Box::new(F::Var(narrow)), Box::new(bits64(2, 64))), info());
    let payload = solver.define_const(
        F::Bvmul(Box::new(F::SignExtend(64, Box::new(F::Var(merged)))), Box::new(bits64(9, 128))),
        info(),
    );
    let success = bits64(17, 32);
    let failure = bits64(16, 32);
    let deep_tag = solver
        .define_const(F::Ite(Box::new(F::Var(allow)), Box::new(success.clone()), Box::new(failure.clone())), info());
    let merged_tag =
        solver.define_const(F::Ite(Box::new(F::Var(deep)), Box::new(F::Var(deep_tag)), Box::new(success)), info());
    let ok = solver.define_const(F::Neq(Box::new(F::Var(merged_tag)), Box::new(failure)), info());
    let other = solver.declare_bitvector(64, info());
    solver.assert(F::Bvule(Box::new(F::Var(other)), Box::new(bits64(100, 64))));
    ((mode_a, mode_b, route), ok, payload)
}

#[test]
fn ones_shift_guard_projection_matches_eager_solver() {
    use smtlib::Exp::*;
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let mut cfg = Config::new();
    cfg.solver_options.finite_domain_enumeration = true;
    let ctx = Context::new(cfg);
    let mut solver = Solver::<B64>::new(&ctx);
    let (_, ok, width) = merged_length(&mut solver);
    let all: Vec<_> = [-9, 0, 9, 18].into_iter().map(crate::primop_util::smt_i128).collect();
    for guard in [Some(Var(ok)), Some(Not(Box::new(Var(ok)))), None] {
        let tx = solver.start_transaction_with_guard(guard);
        let mut actual = all.clone();
        solver.refine_guarded_values(width, &mut actual, |_| false, true);
        let expected: Vec<_> = all
            .iter()
            .filter(|v| {
                solver.check_sat_with(&Eq(Box::new(Var(width)), Box::new((*v).clone())), info()).is_sat().unwrap()
            })
            .cloned()
            .collect();
        assert_eq!(actual, expected);
        solver.rollback_transaction(tx);
    }
}

#[test]
fn ones_shift_merged_tag_guards_length() {
    if !run_in_diagnostics_process(concat!(module_path!(), "::ones_shift_merged_tag_guards_length")) {
        return;
    }
    run_deep_region_test(|| {
        use smtlib::bits64;
        use smtlib::Exp as F;
        crate::config::RegionOptions { defer_exit_check: true, ..Default::default() }.configure();
        let (mut shared, _, _) = shared_state_and_bindings_from_ir(
            r#"
val zzeros = "zeros" : (%i) -> %bv
val zlength = "length" : (%bv) -> %i
val zwiden = "%i64->%i" : (%i64) -> %i
val zmask : (%bool, %i) -> %i
fn zmask(zok, zshift) {
    jump zok goto 3;
    return = zwiden(0);
    goto 6;
    zbits : %bv;
    zbits = zzeros(zshift);
    return = zlength(zbits);
    end;
}
"#,
        );
        let mask = shared.symtab.lookup("zmask");
        let tag = shared.symtab.intern("zsuccess");
        let width = shared.symtab.intern("zwidth");
        let program =
            vec![Instr::Call(Loc::Id(RETURN), false, mask, vec![Exp::Id(tag), Exp::Id(width)], info()), Instr::End];
        let mut inputs = None;
        crate::smt::reset_test_mandatory_query_count();
        let (paths, _, rejects) = paths_with_solver_state(
            program,
            &shared,
            0,
            ExecutionLimits::default().with_path_merging(true),
            crate::memory::Memory::new(),
            |frame, solver| {
                let (choices, ok, payload) = merged_length(solver);
                frame.vars_mut().insert(tag, UVal::Init(Val::Symbolic(ok)));
                frame.vars_mut().insert(width, UVal::Init(Val::Symbolic(payload)));
                inputs = Some(choices);
            },
            false,
        );
        let blocked = crate::smt::test_mandatory_query_count();
        let (a, b, route) = inputs.unwrap();
        let ctx = Context::new(Config::new());
        for (sv39, sv48, initial) in [(true, true, 2u64), (true, false, 2), (false, true, 3), (false, false, 4)] {
            for (r, expected) in [(10, 18), (11, initial.saturating_sub(3) * 9)] {
                let mut witnessed = false;
                for path in &paths {
                    let mut solver = Solver::from_checkpoint(&ctx, path.checkpoint.clone());
                    solver.assert_eq(F::Var(a), F::Bool(sv39));
                    solver.assert_eq(F::Var(b), F::Bool(sv48));
                    solver.assert_eq(F::Var(route), bits64(r, 8));
                    let matches =
                        F::Eq(Box::new(smt_value(&path.value, info()).unwrap()), Box::new(bits64(expected, 128)));
                    assert!(solver.check_sat_with(&F::Not(Box::new(matches.clone())), info()).is_unsat().unwrap());
                    witnessed |= solver.check_sat_with(&matches, info()).is_sat().unwrap();
                }
                assert!(witnessed, "{sv39}/{sv48}/{r}");
            }
        }
        assert_eq!(blocked, 0, "{rejects}");
        assert_eq!(Solver::<B64>::test_split_recomputations(), 0, "已拆分的操作数不应重新枚举整个前缀");
    });
}
