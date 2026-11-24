//! 用定长 SMT 位向量承载 Sail 变长位向量，长度以上的位始终为零。
use super::*;
use crate::primop_util::merge_terms::MergeTerms;

pub(crate) const LENGTH_BOUNDARY: &str = "sym_bits_length";

pub(crate) fn concrete_length<B: BV>(
    len: Sym,
    cap: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<u32, ExecError> {
    match concretize_proven_i128(Val::Symbolic(len), solver, info)? {
        Val::I128(len) => {
            let len = u32::try_from(len).expect("符号长度必须能表示为非负 u32");
            assert!(len <= cap, "符号长度超过容量");
            Ok(len)
        }
        Val::Symbolic(len) => Err(ExecError::SymbolicNatural {
            symbol: len,
            minimum: 0,
            maximum: cap,
            operation: LENGTH_BOUNDARY,
            location: info,
        }),
        _ => unreachable!("符号长度必须是整数"),
    }
}

/// 边界只拆分位宽，承载数据仍保留原有符号关系。
pub(crate) fn concretize<B: BV>(value: &mut Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<(), ExecError> {
    match value {
        Val::SymBits { data, len, cap } => {
            let length = concrete_length(*len, *cap, solver, info)?;
            *value = if length == 0 {
                Val::Bits(B::zeros(0))
            } else if length == *cap {
                Val::Symbolic(*data)
            } else {
                Val::Symbolic(solver.define_bitvector(Exp::Extract(length - 1, 0, Box::new(Exp::Var(*data))), info))
            };
        }
        Val::Guarded(_, values) => {
            concretize(&mut values.0, solver, info)?;
            concretize(&mut values.1, solver, info)?;
        }
        Val::Struct(fields) | Val::SymbolicCtor(_, fields) => {
            for value in fields.values_mut() {
                concretize(value, solver, info)?;
            }
        }
        Val::Vector(values) | Val::List(values) => {
            for value in values {
                concretize(value, solver, info)?;
            }
        }
        Val::Ctor(_, value) => concretize(value, solver, info)?,
        _ => (),
    }
    Ok(())
}

#[cfg(test)]
mod tests;

type Term = Exp<Sym>;
type BinaryTerm = fn(Box<Term>, Box<Term>) -> Term;

pub(crate) fn is_dynamic<B>(value: &Val<B>) -> bool {
    matches!(value, Val::SymBits { .. })
}

fn binary(op: BinaryTerm, left: Term, right: Term) -> Term {
    op(Box::new(left), Box::new(right))
}

fn choose(guard: Term, yes: Term, no: Term) -> Term {
    if yes == no {
        yes
    } else {
        Exp::Ite(Box::new(guard), Box::new(yes), Box::new(no))
    }
}

fn int(n: u32) -> Term {
    smt_i128(i128::from(n))
}

fn zero(width: u32) -> Term {
    if width <= 64 {
        smt_zeros(i128::from(width))
    } else {
        Exp::ZeroExtend(width - 1, Box::new(bits64(0, 1)))
    }
}

fn resize(data: Term, width: u32, target: u32) -> Term {
    assert!(target > 0);
    match width.cmp(&target) {
        std::cmp::Ordering::Less if width == 0 => zero(target),
        std::cmp::Ordering::Less => Exp::ZeroExtend(target - width, Box::new(data)),
        std::cmp::Ordering::Equal => data,
        std::cmp::Ordering::Greater => Exp::Extract(target - 1, 0, Box::new(data)),
    }
}

fn low_mask(cap: u32, len: Term) -> Term {
    let one = smt_u64_width(1, cap);
    // SMT 左移达到位宽时得到零，减一便是全一。smt_shift 会先处理过宽的移位量。
    let shifted = smt_shift(one.clone(), cap, len, 128, Exp::Bvshl, zero(cap));
    binary(Exp::Bvsub, shifted, one)
}

fn masked(data: Term, cap: u32, len: Term) -> Term {
    binary(Exp::Bvand, data, low_mask(cap, len))
}

struct Word {
    data: Term,
    len: Term,
    cap: u32,
}

impl Word {
    fn from_value<B: BV>(value: &Val<B>, solver: &dyn MergeTerms<B>, info: SourceLoc) -> Result<Self, ExecError> {
        if let Val::SymBits { data, len, cap } = value {
            return Ok(Self { data: Exp::Var(*data), len: Exp::Var(*len), cap: *cap });
        }
        if let Some(width) = merge_bit_width(value, solver, info)? {
            if matches!(value, Val::Bits(_) | Val::MixedBits(_) | Val::Symbolic(_)) {
                let data = if width == 0 { zero(1) } else { smt_value(value, info)? };
                return Ok(Self { data, len: int(width), cap: width.max(1) });
            }
        }
        Err(ExecError::Type(format!("需要位向量，实际为 {value:?}"), info))
    }

    fn low(&self, cap: u32) -> Term {
        resize(self.data.clone(), self.cap, cap)
    }

    fn sign(&self) -> Term {
        let index = binary(Exp::Bvsub, self.len.clone(), int(1));
        let shifted = smt_shift(self.data.clone(), self.cap, index, 128, Exp::Bvlshr, zero(self.cap));
        binary(Exp::Eq, Exp::Extract(0, 0, Box::new(shifted)), bits64(1, 1))
    }

    fn sign_extended(&self, cap: u32) -> Term {
        let data = self.low(cap);
        let fill = Exp::Bvnot(Box::new(low_mask(cap, self.len.clone())));
        binary(Exp::Bvor, data, choose(self.sign(), fill, zero(cap)))
    }
}

fn constant_length(len: &Term) -> Option<i128> {
    match len {
        Exp::Bits(bits) => i128_from_model_bits(bits),
        Exp::Bits64(bits) => Some(bits.signed()),
        _ => None,
    }
}

fn finish<B: BV>(
    data: Term,
    len: Term,
    cap: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let (constant, len) = match len {
        Exp::Var(sym) => (solver.structural_i128(sym), Some(sym)),
        other => match constant_length(&other) {
            Some(value) => (Some(value), None),
            None => {
                let sym = solver.define_const(other, info);
                (solver.structural_i128(sym), Some(sym))
            }
        },
    };
    if let Some(length) = constant {
        let length = u32::try_from(length).expect("已验证的位宽必须能表示为 u32");
        assert!(length <= cap, "已验证的位宽超过容量");
        return if length == 0 {
            Ok(Val::Bits(B::zeros(0)))
        } else {
            let data = resize(data, cap, length);
            if let Exp::Var(sym) = data {
                Ok(Val::Symbolic(sym))
            } else {
                solver.define_bitvector(data, info).into()
            }
        };
    }
    let data = match data {
        Exp::Var(sym) => sym,
        expr => solver.define_bitvector(expr, info),
    };
    Ok(Val::SymBits { data, len: len.expect("符号长度必须有定义"), cap })
}

fn require<B: BV>(condition: Term, operation: &str, solver: &mut Solver<B>, info: SourceLoc) -> Result<(), ExecError> {
    match solver.structural_bool(&condition) {
        Some(true) => return Ok(()),
        Some(false) => return Err(ExecError::Type(format!("{operation} 的长度或范围无效"), info)),
        None => (),
    }
    if solver.range_check_handled(&condition, info)
        || solver.check_sat_with_for_range(&Exp::Not(Box::new(condition.clone())), info).is_unsat()?
    {
        return Ok(());
    }
    if solver.check_sat_with_for_range(&condition, info).is_unsat()? {
        return Err(ExecError::Type(format!("{operation} 的长度或范围无效"), info));
    }
    Err(ExecError::RetryCondition(condition, info))
}

fn cap_for<B: BV>(len: &Term, solver: &Solver<B>) -> Option<(i128, u32)> {
    let (min, max) = match constant_length(len) {
        Some(value) => (value, value),
        None => solver.structural_int_bounds(len)?,
    };
    Some((min, u32::try_from(max).ok()?.max(1)))
}

pub(super) fn fill<B: BV>(
    len: &Val<B>,
    ones: bool,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if !solver.sym_bits_enabled() || !matches!(len, Val::Symbolic(_)) {
        return Ok(None);
    }
    let len = int_exp_128(len, solver, "位向量构造", info)?;
    let Some((min, cap)) = cap_for(&len, solver) else { return Ok(None) };
    if min < 0 {
        require(binary(Exp::Bvsge, len.clone(), int(0)), "位向量构造", solver, info)?;
    }
    let data = if ones { low_mask(cap, len.clone()) } else { zero(cap) };
    Ok(Some(finish(data, len, cap, solver, info)?))
}

pub(super) fn bit_not<B: BV>(value: &Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let word = Word::from_value(value, solver, info)?;
    finish(masked(Exp::Bvnot(Box::new(word.data)), word.cap, word.len.clone()), word.len, word.cap, solver, info)
}

pub(super) fn bit_binary<B: BV>(
    left: &Val<B>,
    right: &Val<B>,
    op: BinaryTerm,
    modular: bool,
    operation: &str,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let left = Word::from_value(left, solver, info)?;
    let right = Word::from_value(right, solver, info)?;
    if left.len != right.len {
        require(binary(Exp::Eq, left.len.clone(), right.len.clone()), operation, solver, info)?;
    }
    let cap = left.cap.max(right.cap);
    let data = binary(op, left.low(cap), right.low(cap));
    let data = if modular { masked(data, cap, left.len.clone()) } else { data };
    finish(data, left.len, cap, solver, info)
}

pub(super) fn compare<B: BV>(
    left: &Val<B>,
    right: &Val<B>,
    require_equal_width: bool,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let left = Word::from_value(left, solver, info)?;
    let right = Word::from_value(right, solver, info)?;
    let cap = left.cap.max(right.cap);
    let data_equal = binary(Exp::Eq, left.low(cap), right.low(cap));
    if left.len == right.len {
        return try_concretize_bool_exp(data_equal, solver, info);
    }
    let same_width = binary(Exp::Eq, left.len, right.len);
    let result = if require_equal_width {
        require(same_width, "eq_bits", solver, info)?;
        data_equal
    } else {
        binary(Exp::And, same_width, data_equal)
    };
    try_concretize_bool_exp(result, solver, info)
}

pub(super) fn extend<B: BV>(
    value: &Val<B>,
    len: &Val<B>,
    signed: bool,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if !is_dynamic(value) && (!solver.sym_bits_enabled() || !matches!(len, Val::Symbolic(_))) {
        return Ok(None);
    }
    let len = int_exp_128(len, solver, "extension", info)?;
    let Some((_, cap)) = cap_for(&len, solver) else { return Ok(None) };
    let word = Word::from_value(value, solver, info)?;
    if len != word.len {
        require(binary(Exp::Bvsge, len.clone(), word.len.clone()), "extension", solver, info)?;
    }
    let data = if signed { masked(word.sign_extended(cap), cap, len.clone()) } else { word.low(cap) };
    Ok(Some(finish(data, len, cap, solver, info)?))
}

pub(super) fn slice<B: BV>(
    value: &Val<B>,
    from: &Val<B>,
    len: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if !is_dynamic(value) && (!solver.sym_bits_enabled() || !matches!(len, Val::Symbolic(_))) {
        return Ok(None);
    }
    let len = int_exp_128(len, solver, "slice", info)?;
    let Some((min, cap)) = cap_for(&len, solver) else { return Ok(None) };
    if min < 0 {
        require(binary(Exp::Bvsge, len.clone(), int(0)), "slice", solver, info)?;
    }
    let word = Word::from_value(value, solver, info)?;
    let from = int_exp_128(from, solver, "slice", info)?;
    Ok(Some(extract(word, from, len, cap, solver, info)?))
}

fn extract<B: BV>(
    word: Word,
    from: Term,
    len: Term,
    cap: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let data = if constant_length(&from) == Some(0) {
        word.data
    } else {
        smt_shift(word.data, word.cap, from, 128, Exp::Bvlshr, zero(word.cap))
    };
    finish(masked(resize(data, word.cap, cap), cap, len.clone()), len, cap, solver, info)
}

pub(super) fn truncate_lsb<B: BV>(
    value: &Val<B>,
    len: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if !is_dynamic(value) && (!solver.sym_bits_enabled() || !matches!(len, Val::Symbolic(_))) {
        return Ok(None);
    }
    let word = Word::from_value(value, solver, info)?;
    let len = int_exp_128(len, solver, "sail_truncateLSB", info)?;
    let valid =
        binary(Exp::And, binary(Exp::Bvsge, len.clone(), int(0)), binary(Exp::Bvsle, len.clone(), word.len.clone()));
    require(valid, "sail_truncateLSB", solver, info)?;
    let cap = cap_for(&len, solver).map_or(word.cap, |(_, cap)| cap.min(word.cap));
    let from = binary(Exp::Bvsub, word.len.clone(), len.clone());
    Ok(Some(extract(word, from, len, cap, solver, info)?))
}

pub(super) fn subrange<B: BV>(
    value: &Val<B>,
    high: &Val<B>,
    low: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if !is_dynamic(value)
        && (!solver.sym_bits_enabled() || !matches!((high, low), (Val::Symbolic(_), _) | (_, Val::Symbolic(_))))
    {
        return Ok(None);
    }
    let word = Word::from_value(value, solver, info)?;
    let high = int_exp_128(high, solver, "subrange", info)?;
    let low = int_exp_128(low, solver, "subrange", info)?;
    let valid = binary(
        Exp::And,
        binary(Exp::Bvsge, low.clone(), int(0)),
        binary(
            Exp::And,
            binary(Exp::Bvsle, low.clone(), high.clone()),
            binary(Exp::Bvslt, high.clone(), word.len.clone()),
        ),
    );
    require(valid, "subrange", solver, info)?;
    let len = binary(Exp::Bvadd, binary(Exp::Bvsub, high, low.clone()), int(1));
    let cap = cap_for(&len, solver).map_or(word.cap, |(_, cap)| cap.min(word.cap));
    Ok(Some(extract(word, low, len, cap, solver, info)?))
}

pub(super) fn concat<B: BV>(
    left: &Val<B>,
    right: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let left = Word::from_value(left, solver, info)?;
    let right = Word::from_value(right, solver, info)?;
    let len = binary(Exp::Bvadd, left.len.clone(), right.len.clone());
    let cap = match (cap_for(&len, solver), left.cap.checked_add(right.cap)) {
        (Some((_, cap)), Some(sum)) => cap.min(sum),
        (Some((_, cap)), None) => cap,
        (None, Some(sum)) => sum,
        (None, None) => {
            require(binary(Exp::Bvsle, len.clone(), int(u32::MAX)), "append", solver, info)?;
            u32::MAX
        }
    };
    let shifted = smt_shift(left.low(cap), cap, right.len.clone(), 128, Exp::Bvshl, zero(cap));
    finish(binary(Exp::Bvor, shifted, right.low(cap)), len, cap, solver, info)
}

pub(super) fn add_int<B: BV>(
    bits: &Val<B>,
    n: &Val<B>,
    op: BinaryTerm,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let word = Word::from_value(bits, solver, info)?;
    let n = int_exp_128(n, solver, "位向量与整数的加减", info)?;
    let data = binary(op, word.data, smt_int_to_bits(n, word.cap));
    finish(masked(data, word.cap, word.len.clone()), word.len, word.cap, solver, info)
}

pub(super) fn to_int<B: BV>(
    value: &Val<B>,
    signed: bool,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let word = Word::from_value(value, solver, info)?;
    let data = if signed { word.sign_extended(word.cap) } else { word.data.clone() };
    // 容量较短时，符号扩展直接在 128 位结果中完成。
    let integer = if signed && word.cap < 128 { word.sign_extended(128) } else { resize(data.clone(), word.cap, 128) };
    let valid = if signed && word.cap > 128 {
        Some(binary(Exp::Eq, data, Exp::SignExtend(word.cap - 128, Box::new(integer.clone()))))
    } else if !signed && word.cap >= 128 {
        Some(binary(Exp::Eq, Exp::Extract(word.cap - 1, 127, Box::new(data)), zero(word.cap - 127)))
    } else {
        None
    };
    if let Some(valid) = valid {
        if solver.structural_bool(&valid) != Some(true)
            && !solver.range_check_handled(&valid, info)
            && solver.check_sat_with_for_range(&Exp::Not(Box::new(valid.clone())), info).is_sat()?
        {
            return if solver.check_sat_with_for_range(&valid, info).is_sat()? {
                Err(ExecError::IntegerConversion(valid, info))
            } else {
                Err(ExecError::Overflow)
            };
        }
    }
    solver.define_const(integer, info).into()
}

#[derive(Clone, Copy)]
pub(super) enum Shift {
    Left,
    Right,
    ArithmeticRight,
}

pub(super) fn shift<B: BV>(
    bits: &Val<B>,
    amount: &Val<B>,
    direction: Shift,
    bit_amount: bool,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let word = Word::from_value(bits, solver, info)?;
    let (amount, amount_width, signed) = match amount {
        Val::I128(_) | Val::I64(_) if !bit_amount => (int_exp_128(amount, solver, "移位", info)?, 128, true),
        Val::Symbolic(sym) if !bit_amount && !solver.is_sail_bitvector(*sym) => {
            let width = solver.length(*sym).expect("整数移位量必须是位向量");
            (Exp::Var(*sym), width, width == 128)
        }
        amount => {
            let amount = Word::from_value(amount, solver, info)?;
            (amount.data, amount.cap, false)
        }
    };
    let shift = |direction, amount: Term| {
        let (op, data, saturated): (BinaryTerm, _, _) = match direction {
            Shift::Left => (Exp::Bvshl, word.data.clone(), zero(word.cap)),
            Shift::Right => (Exp::Bvlshr, word.data.clone(), zero(word.cap)),
            Shift::ArithmeticRight => (
                Exp::Bvashr,
                word.sign_extended(word.cap),
                choose(word.sign(), Exp::Bvnot(Box::new(zero(word.cap))), zero(word.cap)),
            ),
        };
        let data = smt_shift(data, word.cap, amount, amount_width, op, saturated);
        if matches!(direction, Shift::Right) {
            data
        } else {
            masked(data, word.cap, word.len.clone())
        }
    };
    let positive = shift(direction, amount.clone());
    let data = if signed {
        let neg_dir = if matches!(direction, Shift::Left) { Shift::Right } else { Shift::Left };
        let negative = shift(neg_dir, Exp::Bvneg(Box::new(amount.clone())));
        choose(binary(Exp::Bvslt, amount, int(0)), negative, positive)
    } else {
        positive
    };
    finish(data, word.len, word.cap, solver, info)
}

pub(crate) fn merge<B: BV>(
    guard: Sym,
    left: &Val<B>,
    right: &Val<B>,
    solver: &mut dyn MergeTerms<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if left == right {
        return Ok(left.clone());
    }
    fn word<B: BV>(value: &Val<B>, solver: &dyn MergeTerms<B>, info: SourceLoc) -> Result<Word, ExecError> {
        if let Val::Guarded(guard, values) = value {
            let left = word(&values.0, solver, info)?;
            let right = word(&values.1, solver, info)?;
            Ok(select(*guard, left, right))
        } else {
            Word::from_value(value, solver, info)
        }
    }

    fn select(guard: Sym, left: Word, right: Word) -> Word {
        let cap = left.cap.max(right.cap);
        let data = choose(Exp::Var(guard), left.low(cap), right.low(cap));
        let len = choose(Exp::Var(guard), left.len, right.len);
        Word { data, len, cap }
    }

    let word = select(guard, word(left, solver, info)?, word(right, solver, info)?);
    if let Some(len) = constant_length(&word.len) {
        let len = u32::try_from(len).expect("合并后的位宽必须能表示为非负 u32");
        assert!(len <= word.cap);
        if len == 0 {
            return Ok(Val::Bits(B::zeros(0)));
        }
        return Ok(Val::Symbolic(solver.define_bitvector(word.low(len), info)));
    }
    let cap = word.cap;
    let len = solver.define_const(word.len, info);
    let data = solver.define_bitvector(word.data, info);
    Ok(Val::SymBits { data, len, cap })
}

/// 其余原语在执行前走同一个位宽具体化入口，包括字符串、RAM 和宿主向量。
pub(crate) fn supports_unary<B: BV>(f: Unary<B>) -> bool {
    [length::<B> as Unary<B>, not_bits, sail_unsigned, sail_signed]
        .iter()
        .any(|&candidate| std::ptr::fn_addr_eq(f, candidate))
}

pub(crate) fn supports_binary<B: BV>(f: Binary<B>) -> bool {
    [
        eq_bits::<B> as Binary<B>,
        neq_bits,
        eq_anything,
        neq_anything,
        and_bits,
        or_bits,
        xor_bits,
        add_bits,
        sub_bits,
        add_bits_int,
        sub_bits_int,
        zero_extend,
        sign_extend,
        sail_truncate,
        sail_truncate_lsb,
        append,
        shiftl,
        shiftr,
        arith_shiftr,
        shift_bits_left,
        shift_bits_right,
    ]
    .iter()
    .any(|&candidate| std::ptr::fn_addr_eq(f, candidate))
}

pub(crate) fn supports_variadic<B: BV>(f: Variadic<B>) -> bool {
    [super::slice::<B> as Variadic<B>, super::subrange].iter().any(|&candidate| std::ptr::fn_addr_eq(f, candidate))
}
