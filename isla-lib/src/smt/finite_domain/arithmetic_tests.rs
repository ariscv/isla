use super::*;
use crate::bitvector::b64::B64;
use Exp::*;

fn integer(value: u64) -> Exp<Sym> {
    bits64(value, 128)
}

fn eq(sym: Sym, value: u64) -> Exp<Sym> {
    Eq(Box::new(Var(sym)), Box::new(integer(value)))
}

fn numeric(domain: FiniteDomain) -> Vec<u64> {
    let (FiniteDomain::Known(values) | FiniteDomain::Bounded(values)) = domain else {
        panic!("表达式应有有限值域");
    };
    let mut values: Vec<_> = values
        .into_iter()
        .map(|value| match value {
            Bits(bits) => bits.iter().enumerate().fold(0, |n, (i, bit)| if *bit { n | (1 << i) } else { n }),
            _ => panic!("应为 128 位整数"),
        })
        .collect();
    values.sort_unstable();
    values
}

#[test]
fn finite_domain_arithmetic_correlates_slice_endpoints() {
    configure_tastic(Tactic::Qfaufbv);
    for no_smt in [true, false] {
        let mut config = Config::new();
        config.solver_options.finite_domain_enumeration = true;
        config.solver_options.no_smt = no_smt;
        let context = Context::new(config);
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let level = solver.declare_bitvector(8, info);
        solver.assert(
            (1..=4)
                .map(|n| Eq(Box::new(Var(level)), Box::new(bits64(n, 8))))
                .reduce(|lhs, rhs| Or(Box::new(lhs), Box::new(rhs)))
                .unwrap(),
        );
        let level = solver.define_const(ZeroExtend(120, Box::new(Var(level))), info);
        let mode = solver.declare_const(Ty::Bool, info);
        let size = solver.define_const(Ite(Box::new(Var(mode)), Box::new(integer(9)), Box::new(integer(10))), info);
        let next = solver.define_const(Bvadd(Box::new(Var(level)), Box::new(integer(1))), info);
        let end = solver.define_const(Bvmul(Box::new(Var(next)), Box::new(Var(size))), info);
        let hi = solver.define_const(Bvsub(Box::new(Var(end)), Box::new(integer(1))), info);
        let lo = solver.define_const(Bvmul(Box::new(Var(level)), Box::new(Var(size))), info);
        let start = test_query_count();
        let mut expected: Vec<_> =
            (1..=4).flat_map(|level| [9, 10].map(|size| ((level + 1) * size - 1, level * size))).collect();
        expected.sort_unstable();
        assert_eq!(numeric(solver.finite_domain(hi)), expected.iter().map(|pair| pair.0).collect::<Vec<_>>());
        let root = solver.start_transaction();
        for (high, low) in expected {
            let arm = solver.start_transaction_with_guard(Some(eq(hi, high)));
            assert_eq!(numeric(solver.finite_domain(lo)), [low]);
            solver.rollback_transaction(arm);
        }
        let impossible = Or(
            Box::new(Bvslt(Box::new(Var(lo)), Box::new(integer(0)))),
            Box::new(Bvsgt(Box::new(Var(lo)), Box::new(Var(hi)))),
        );
        assert_eq!(solver.finite_domain_predicate(&impossible), Some(false));
        let narrow = solver.start_transaction_with_guard(Some(Not(Box::new(eq(hi, 44)))));
        assert!(!numeric(solver.finite_domain(hi)).contains(&44));
        solver.rollback_transaction(narrow);
        solver.rollback_transaction(root);

        let unknown = solver.declare_bitvector(128, info);
        let unbounded = solver.define_const(Bvmul(Box::new(Var(hi)), Box::new(Var(unknown))), info);
        assert!(matches!(solver.finite_domain(unbounded), FiniteDomain::Unknown));
        assert_eq!(test_query_count() - start, 0);
    }
}

#[test]
fn finite_domain_arithmetic_keeps_all_combinations_and_folds_comparisons() {
    configure_tastic(Tactic::Qfaufbv);
    let mut config = Config::new();
    config.solver_options.finite_domain_enumeration = true;
    config.solver_options.no_smt = true;
    let context = Context::new(config);
    let mut solver = Solver::<B64>::new(&context);
    let info = SourceLoc::unknown();
    let x = solver.declare_bitvector(128, info);
    let y = solver.declare_bitvector(128, info);
    for sym in [x, y] {
        solver.assert((0..9).map(|n| eq(sym, n)).reduce(|a, b| Or(Box::new(a), Box::new(b))).unwrap());
    }
    let left = solver.define_const(Bvmul(Box::new(Var(x)), Box::new(integer(16))), info);
    let result = solver.define_const(Bvadd(Box::new(Var(left)), Box::new(Var(y))), info);
    let start = test_query_count();
    let expected: Vec<_> = (0..9).flat_map(|a| (0..9).map(move |b| a * 16 + b)).collect();
    let domain = solver.finite_domain(result);
    assert!(matches!(domain, FiniteDomain::Known(_)));
    assert_eq!(numeric(domain), expected);

    let relation = Bvult(Box::new(Var(x)), Box::new(Var(y)));
    let difference = Bvsub(Box::new(Var(y)), Box::new(Var(x)));
    let chosen = solver.define_const(Ite(Box::new(relation.clone()), Box::new(difference), Box::new(integer(0))), info);
    // 残余约束无法认证，但上界仍应覆盖所有可能取值。
    let unrelated = solver.declare_bitvector(128, info);
    solver.assert(Bvuge(Box::new(Var(unrelated)), Box::new(integer(7))));
    solver.assert(Not(Box::new(relation)));
    let domain = solver.finite_domain(chosen);
    assert!(matches!(domain, FiniteDomain::Bounded(_)));
    assert_eq!(numeric(domain), [0]);
    assert_eq!(test_query_count() - start, 0);
}

#[test]
fn i128_to_i64_roundtrip_skips_finite_search() {
    use crate::{ir::Val, primop::unary_primops};

    configure_tastic(Tactic::Qfaufbv);
    let mut config = Config::new();
    config.solver_options.finite_domain_enumeration = true;
    let context = Context::new(config);
    let mut solver = Solver::<B64>::new(&context);
    let info = SourceLoc::unknown();
    let ops = unary_primops();
    let a = solver.declare_const(Ty::Bool, info);
    let b = solver.declare_const(Ty::Bool, info);
    let choose = |g, x, y| Ite(Box::new(Var(g)), Box::new(x), Box::new(y));
    let width = solver.define_const(
        choose(a, bits64(i64::MIN as u64, 64), choose(b, bits64(i64::MAX as u64, 64), bits64(8, 64))),
        info,
    );
    solver.assert(Or(Box::new(Var(a)), Box::new(Var(b))));
    let wide = ops["%i64->%i"](Val::Symbolic(width), &mut solver, info).unwrap();
    BOUND_SEARCHES.set(0);
    AST_SIMPLIFY_CALLS.set(0);
    let before = test_query_count();
    let Val::Symbolic(result) = ops["%i->%i64"](wide, &mut solver, info).unwrap() else {
        panic!("宽度往返转换必须保留符号结果")
    };
    let searches = BOUND_SEARCHES.get();
    eprintln!("有符号往返转换的上界搜索 {} 次、化简 {} 次", searches, AST_SIMPLIFY_CALLS.get());
    assert_eq!(test_query_count(), before);
    assert_eq!(solver.check_sat_with(&Neq(Box::new(Var(result)), Box::new(Var(width))), info), SmtResult::Unsat);
    assert_eq!(searches, 0, "符号扩展后窄回原宽度，无需推导候选");
}
