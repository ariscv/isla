//! 不同位宽的分支共享程序守卫，各自保留 Sail 位向量的原生位宽。
use super::*;

/// SMT 也用位向量表示整数和构造子标签。用已有的 Sail 位向量标记区分这些值。
pub(crate) fn is_bits<B: BV>(value: &Val<B>, solver: &Solver<B>) -> bool {
    match value {
        Val::Bits(_) | Val::MixedBits(_) => true,
        Val::Symbolic(sym) => solver.is_sail_bitvector(*sym),
        Val::Guarded(_, values) => is_bits(&values.0, solver) && is_bits(&values.1, solver),
        _ => false,
    }
}

pub(super) fn merge<B: BV>(
    cond: Sym,
    left: &Val<B>,
    right: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Val<B> {
    fn collect<'a, B: BV>(value: &'a Val<B>, guard: Exp<Sym>, leaves: &mut Vec<(Exp<Sym>, &'a Val<B>)>) {
        if let Val::Guarded(condition, values) = value {
            let selected = Exp::Var(*condition);
            collect(&values.0, Exp::And(Box::new(guard.clone()), Box::new(selected.clone())), leaves);
            collect(&values.1, Exp::And(Box::new(guard), Box::new(Exp::Not(Box::new(selected)))), leaves);
        } else if let Some((existing, _)) = leaves.iter_mut().find(|(_, leaf)| *leaf == value) {
            *existing = Exp::Or(Box::new(std::mem::replace(existing, Exp::Bool(false))), Box::new(guard));
        } else {
            leaves.push((guard, value));
        }
    }

    let mut leaves = Vec::new();
    collect(left, Exp::Var(cond), &mut leaves);
    collect(right, Exp::Not(Box::new(Exp::Var(cond))), &mut leaves);
    // 各叶的守卫两两互斥并覆盖整个合并域。最后一叶使用前面守卫的补集。
    let (_, last) = leaves.pop().unwrap();
    leaves.into_iter().rev().fold(last.clone(), |rest, (predicate, leaf)| {
        let guard = solver.define_const(predicate, info);
        crate::executor::concrete_values::created();
        Val::Guarded(guard, Box::new((leaf.clone(), rest)))
    })
}
