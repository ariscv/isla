//! 判断守卫值的各个分支是否都是 Sail 位向量。
use super::*;

/// SMT 也用位向量表示整数和构造子标签。用已有的 Sail 位向量标记区分这些值。
pub(crate) fn is_bits<B: BV>(value: &Val<B>, solver: &Solver<B>) -> bool {
    is_bits_with(value, solver)
}

pub(super) fn is_bits_with<B: BV>(value: &Val<B>, solver: &dyn MergeTerms<B>) -> bool {
    match value {
        Val::Bits(_) | Val::MixedBits(_) | Val::SymBits { .. } => true,
        Val::Symbolic(sym) => solver.is_sail_bitvector(*sym),
        Val::Guarded(_, values) => is_bits_with(&values.0, solver) && is_bits_with(&values.1, solver),
        _ => false,
    }
}
