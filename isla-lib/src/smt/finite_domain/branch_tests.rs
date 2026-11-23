use super::*;

// 4880c857 的分支判定。对照求解器独占自己的正反谓词缓存。
impl<B: BV> Solver<'_, B> {
    fn reference_branch_bool(&self, exp: &Exp<Sym>) -> Option<bool> {
        let prefix = PathConditions::new(self)?;
        let mut subjects = Vec::new();
        prefix.comparison_subjects(exp, &mut subjects);
        let predicate = self.translate_exp(exp);
        if subjects.is_empty() {
            return None;
        }

        // 两侧仍分别化简各自的谓词。共享候选及排除结果，空域时两侧均可判死。
        let mut branch_exp = exp;
        while let Exp::Not(inner) = branch_exp {
            branch_exp = inner;
        }
        let mut cache = prefix.index.branch.borrow_mut();
        if cache.as_ref().is_none_or(|entry| &entry.predicate != branch_exp) {
            *cache = Some(BranchCandidates { predicate: branch_exp.clone(), subjects: Vec::new() });
        }
        let prepared = &mut cache.as_mut().unwrap().subjects;
        for (index, subject) in subjects.into_iter().enumerate() {
            if index == prepared.len() {
                prepared.push(prefix.bounds(subject).map(|candidates| {
                    candidates.into_iter().map(|value| Candidate { value, excluded: None }).collect()
                }));
            }
            let Some(candidates) = &mut prepared[index] else { continue };
            let anchor = self.translate_exp(subject);
            let mut result = None;
            let mut undecided = false;
            for candidate in candidates {
                let value = self.translate_exp(&candidate.value);
                if *candidate.excluded.get_or_insert_with(|| {
                    prefix.assertions().any(|fact| {
                        let original = self.translate_projection_assertion(fact);
                        let mut narrowed = original.substitute(&anchor, &value);
                        narrowed.z3_ast != original.z3_ast && narrowed.structural_bool() == Some(false)
                    })
                }) {
                    continue;
                }
                match predicate.substitute(&anchor, &value).structural_bool() {
                    Some(current) if result.is_none() || result == Some(current) => result = Some(current),
                    _ => {
                        undecided = true;
                        break;
                    }
                }
            }
            if !undecided {
                return result.or(Some(false));
            }
        }
        None
    }
}

fn eq(x: Sym, n: u64) -> Exp<Sym> {
    Exp::Eq(Box::new(Exp::Var(x)), Box::new(bits64(n, 8)))
}

fn allowed(x: Sym, n: u64) -> Exp<Sym> {
    (0..n).map(|i| eq(x, i)).reduce(|a, b| Exp::Or(Box::new(a), Box::new(b))).unwrap()
}

fn not(exp: Exp<Sym>) -> Exp<Sym> {
    Exp::Not(Box::new(exp))
}

fn measured(f: impl FnOnce() -> Option<bool>) -> (Option<bool>, [usize; 3]) {
    PROJECT_TRANSLATIONS.set(0);
    PROJECT_SUBSTITUTIONS.set(0);
    STRUCTURAL_BOOLS.set(0);
    (f(), [PROJECT_TRANSLATIONS.get(), PROJECT_SUBSTITUTIONS.get(), STRUCTURAL_BOOLS.get()])
}

#[test]
fn branch_prefix_filters_and_reuses_candidate_checks() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let mut s = Solver::<B64>::new(&ctx);
    let info = SourceLoc::unknown();
    let x = s.declare_bitvector(8, info);
    let y = s.declare_bitvector(8, info);
    s.assert(allowed(x, 16));
    s.assert(allowed(y, 2));
    for _ in 0..256 {
        let b = s.declare_const(Ty::Bool, info);
        s.assert(Exp::Var(b));
    }
    let reference = Solver::from_checkpoint(&ctx, checkpoint(&mut s));
    let run = |s: &Solver<'_, B64>, p: Exp<Sym>| {
        let (old, before) = measured(|| reference.reference_branch_bool(&p));
        let (new, after) = measured(|| s.finite_domain_bool(&p));
        assert_eq!(new, old);
        eprintln!("分支 {new:?} 的翻译、代入、结构判定 {before:?} → {after:?}");
        (new, before, after)
    };
    let (new, before, cold) = run(&s, eq(x, 32));
    assert_eq!(new, Some(false));
    assert_eq!(before, [258 * 16, 259 * 16, 32]);
    assert_eq!(cold, [258, 32, 32]);
    // 不同谓词同一锚点，原有正反谓词缓存本身不能命中。
    assert_eq!(run(&s, eq(x, 33)).2, [0, 16, 16]);
    let (_, _, other_anchor) = run(&s, eq(y, 3));
    assert_eq!(other_anchor[0], 0);
    assert_eq!(run(&s, not(eq(y, 3))).0, Some(true));
    // 新增无关断言后只判一次相关性，旧相关断言和候选排除结论可复用。
    s.assert(Exp::Bool(true));
    let (answer, growth) = measured(|| s.finite_domain_bool(&eq(x, 34)));
    assert_eq!(answer, Some(false));
    assert_eq!(growth[0], 1);
    assert!(growth[1] <= 17 && growth[2] == 16);
    // 后加相关约束仍须逐候选判断。x=1 被排除后，两侧都与参照一致。
    s.assert(not(eq(x, 1)));
    let point = checkpoint(&mut s);
    let reference = Solver::from_checkpoint(&ctx, point);
    for p in [eq(x, 1), not(eq(x, 1)), eq(x, 0)] {
        assert_eq!(s.finite_domain_bool(&p), reference.reference_branch_bool(&p));
    }
}

#[test]
fn branch_prefix_matches_reference_across_guards_rebind_and_replay() {
    configure_tastic(Tactic::Qfaufbv);
    let ctx = Context::new(Config::new());
    let ctx2 = Context::new(Config::new());
    let info = SourceLoc::unknown();
    let mut s = Solver::<B64>::new(&ctx);
    let x = s.declare_bitvector(8, info);
    let y = s.declare_bitvector(8, info);
    let b = s.declare_const(Ty::Bool, info);
    let derived =
        s.define_bitvector(Exp::Ite(Box::new(Exp::Var(b)), Box::new(bits64(0, 8)), Box::new(bits64(1, 8))), info);
    let identity =
        s.define_bitvector(Exp::Ite(Box::new(Exp::Var(b)), Box::new(bits64(2, 8)), Box::new(bits64(2, 8))), info);
    s.assert(allowed(x, 2));
    let mut r = Solver::from_checkpoint(&ctx2, checkpoint(&mut s));
    let compare = |s: &Solver<'_, B64>, r: &Solver<'_, B64>, p: Exp<Sym>, expected| {
        assert_eq!(r.reference_branch_bool(&p), expected);
        assert_eq!(s.finite_domain_bool(&p), expected);
    };
    for solver in [&mut s, &mut r] {
        // 无关断言即使化简成假，旧分支排除也只检查代入改变了的断言。
        solver.assert(Exp::And(Box::new(Exp::Var(b)), Box::new(not(Exp::Var(b)))));
    }
    compare(&s, &r, not(eq(x, 4)), Some(true));
    compare(&s, &r, eq(identity, 2), Some(true));
    compare(&s, &r, eq(derived, 0), None);
    compare(&s, &r, eq(y, 0), None);
    compare(&s, &r, Exp::Or(Box::new(eq(y, 0)), Box::new(not(eq(x, 4)))), Some(true));
    let a = s.start_transaction_with_guard(Some(not(eq(x, 0))));
    let ar = r.start_transaction_with_guard(Some(not(eq(x, 0))));
    compare(&s, &r, eq(x, 1), Some(true));
    for solver in [&mut s, &mut r] {
        solver.assert(not(eq(x, 1)));
    }
    compare(&s, &r, eq(x, 1), Some(false));
    compare(&s, &r, not(eq(x, 1)), Some(false));
    s.rollback_transaction(a);
    r.rollback_transaction(ar);
    compare(&s, &r, eq(x, 0), None);
    let t = s.start_transaction();
    let tr = r.start_transaction();
    for solver in [&mut s, &mut r] {
        solver.add(Def::DefineConst(x, bits64(2, 8)));
    }
    compare(&s, &r, eq(x, 2), None);
    s.rollback_transaction(t);
    r.rollback_transaction(tr);
    for solver in [&mut s, &mut r] {
        solver.start_transaction_with_guard(Some(Exp::Var(b)));
        solver.assert(eq(x, 1));
        solver.commit_transaction();
    }
    compare(&s, &r, eq(x, 1), None);
}
