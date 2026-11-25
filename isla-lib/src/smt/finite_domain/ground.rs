//! 用 Isla 的位向量运算求值。查看原生 AST 时只读取节点和字面量，不构造代入式。
use super::*;
use crate::bitvector::b129::B129;
use std::hash::Hash;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Value {
    Bool(bool),
    Bits(B129),
}

impl Value {
    fn boolean(self) -> Option<bool> {
        match self {
            Self::Bool(value) => Some(value),
            _ => None,
        }
    }

    fn bits(self) -> Option<B129> {
        match self {
            Self::Bits(value) => Some(value),
            _ => None,
        }
    }
}

#[derive(Clone, Copy)]
enum Op {
    Not,
    And,
    Or,
    Eq,
    Neq,
    Ite,
    Bvnot,
    Bvneg,
    Bvand,
    Bvor,
    Bvxor,
    Bvnand,
    Bvnor,
    Bvxnor,
    Bvadd,
    Bvsub,
    Bvmul,
    Bvshl,
    Bvlshr,
    Bvashr,
    Bvult,
    Bvule,
    Bvugt,
    Bvuge,
    Bvslt,
    Bvsle,
    Bvsgt,
    Bvsge,
    Extract(u32, u32),
    ZeroExtend(u32),
    SignExtend(u32),
    Concat,
}

enum Term<K> {
    Constant(Value),
    Alias(K),
    Unary(Op, K),
    Binary(Op, K, K),
    Ternary(Op, K, K, K),
    Many(Op, Vec<K>),
}

enum Step<K> {
    Visit(K),
    Apply(K, Op, usize),
    Save(K),
}

fn evaluate<K: Copy, I: Hash + Eq>(
    root: K,
    key: impl Fn(K) -> I,
    mut term: impl FnMut(K) -> Option<Term<K>>,
) -> Option<Value> {
    let mut pending = vec![Step::Visit(root)];
    let mut values = Vec::new();
    let mut memo = ahash::AHashMap::<I, Option<Value>>::new();
    while let Some(step) = pending.pop() {
        match step {
            Step::Visit(node) => {
                if let Some(&value) = memo.get(&key(node)) {
                    values.push(value.expect("有限域求值的定义链含环"));
                    continue;
                }
                match term(node)? {
                    Term::Constant(value) => {
                        memo.insert(key(node), Some(value));
                        values.push(value);
                    }
                    Term::Alias(target) => {
                        memo.insert(key(node), None);
                        pending.push(Step::Save(node));
                        pending.push(Step::Visit(target));
                    }
                    Term::Unary(op, a) => {
                        pending.push(Step::Apply(node, op, 1));
                        pending.push(Step::Visit(a));
                    }
                    Term::Binary(op, a, b) => {
                        pending.push(Step::Apply(node, op, 2));
                        pending.push(Step::Visit(b));
                        pending.push(Step::Visit(a));
                    }
                    Term::Ternary(op, a, b, c) => {
                        pending.push(Step::Apply(node, op, 3));
                        pending.push(Step::Visit(c));
                        pending.push(Step::Visit(b));
                        pending.push(Step::Visit(a));
                    }
                    Term::Many(op, nodes) => {
                        pending.push(Step::Apply(node, op, nodes.len()));
                        pending.extend(nodes.into_iter().rev().map(Step::Visit));
                    }
                }
            }
            Step::Apply(node, op, count) => {
                let start = values.len() - count;
                let value = op.apply(&values[start..])?;
                values.truncate(start);
                memo.insert(key(node), Some(value));
                values.push(value);
            }
            Step::Save(node) => {
                memo.insert(key(node), Some(*values.last().unwrap()));
            }
        }
    }
    values.pop()
}

impl Op {
    fn apply(self, args: &[Value]) -> Option<Value> {
        use Op::*;
        if matches!(self, And | Or) {
            let absorbing = matches!(self, Or);
            let mut result = !absorbing;
            for arg in args {
                if arg.boolean()? == absorbing {
                    result = absorbing;
                }
            }
            return Some(Value::Bool(result));
        }
        if matches!(self, Not | Eq | Neq | Ite) {
            return Some(match self {
                Not => Value::Bool(!args[0].boolean()?),
                Eq => Value::Bool(args[0] == args[1]),
                Neq => Value::Bool(args[0] != args[1]),
                Ite => args[if args[0].boolean()? { 1 } else { 2 }],
                _ => unreachable!(),
            });
        }
        let a = args[0].bits()?;
        let width = a.len();
        match self {
            Bvnot => return Some(Value::Bits(!a)),
            Bvneg => return Some(Value::Bits(-a)),
            Extract(hi, lo) => return a.extract(hi, lo).map(Value::Bits),
            ZeroExtend(len) if width + len <= B129::MAX_WIDTH => return Some(Value::Bits(a.zero_extend(width + len))),
            SignExtend(len) if width + len <= B129::MAX_WIDTH => return Some(Value::Bits(a.sign_extend(width + len))),
            SignExtend(_) | ZeroExtend(_) => return None,
            Concat => {
                let mut result = a;
                for arg in &args[1..] {
                    result = result.append(arg.bits()?)?;
                }
                return Some(Value::Bits(result));
            }
            _ => (),
        }
        let b = args[1].bits()?;
        let unsigned = || a.unsigned_cmp(b);
        // 翻转符号位后，补码的有符号顺序与无符号顺序相同，包括 129 位。
        let sign = B129::BIT_ONE.zero_extend(width) << B129::new(u64::from(width - 1), width);
        let signed = || (a ^ sign).unsigned_cmp(b ^ sign);
        Some(match self {
            Bvand => Value::Bits(args[1..].iter().try_fold(a, |acc, arg| Some(acc & arg.bits()?))?),
            Bvor => Value::Bits(args[1..].iter().try_fold(a, |acc, arg| Some(acc | arg.bits()?))?),
            Bvxor => Value::Bits(args[1..].iter().try_fold(a, |acc, arg| Some(acc ^ arg.bits()?))?),
            Bvnand => Value::Bits(!(a & b)),
            Bvnor => Value::Bits(!(a | b)),
            Bvxnor => Value::Bits(!(a ^ b)),
            Bvadd => Value::Bits(args[1..].iter().try_fold(a, |acc, arg| Some(acc + arg.bits()?))?),
            Bvsub => Value::Bits(a - b),
            Bvmul => Value::Bits(args[1..].iter().try_fold(a, |acc, arg| Some(acc.wrapping_mul(arg.bits()?)))?),
            Bvshl => Value::Bits(a << b),
            Bvlshr => Value::Bits(a >> b),
            Bvashr => {
                if a & sign == B129::zeros(width) {
                    Value::Bits(a >> b)
                } else {
                    Value::Bits(!(!a >> b))
                }
            }
            Bvult => Value::Bool(unsigned().is_lt()),
            Bvule => Value::Bool(unsigned().is_le()),
            Bvugt => Value::Bool(unsigned().is_gt()),
            Bvuge => Value::Bool(unsigned().is_ge()),
            Bvslt => Value::Bool(signed().is_lt()),
            Bvsle => Value::Bool(signed().is_le()),
            Bvsgt => Value::Bool(signed().is_gt()),
            Bvsge => Value::Bool(signed().is_ge()),
            _ => unreachable!("应已处理此运算"),
        })
    }

    fn accepts_many(self) -> bool {
        matches!(
            self,
            Self::And | Self::Or | Self::Bvand | Self::Bvor | Self::Bvxor | Self::Bvadd | Self::Bvmul | Self::Concat
        )
    }
}

/// 使用本候选的符号赋值及已有定义。缺少具体输入时不产生判定。
pub(super) fn eval_assertion<'a>(
    exp: &'a Exp<Sym>,
    assignment: impl Fn(Sym) -> Option<&'a Exp<Sym>>,
    definition: impl Fn(Sym) -> Option<&'a Exp<Sym>>,
) -> Option<bool> {
    eval_value(exp, assignment, definition)?.boolean()
}

/// 投影需要保留布尔值和位向量的完整位宽，具体操作共用已有求值器。
pub(super) fn eval_projected<'a>(
    exp: &'a Exp<Sym>,
    assignment: impl Fn(Sym) -> Option<&'a Exp<Sym>>,
) -> Option<Exp<Sym>> {
    Some(match eval_value(exp, assignment, |_| None)? {
        Value::Bool(truth) => Exp::Bool(truth),
        Value::Bits(bits) => crate::primop_util::smt_sbits(bits),
    })
}

fn eval_value<'a>(
    exp: &'a Exp<Sym>,
    assignment: impl Fn(Sym) -> Option<&'a Exp<Sym>>,
    definition: impl Fn(Sym) -> Option<&'a Exp<Sym>>,
) -> Option<Value> {
    use Exp::*;
    evaluate(
        exp,
        |node| node as *const Exp<Sym>,
        |node| {
            let unary = |op, a: &'a Exp<Sym>| Some(Term::Unary(op, a));
            let binary = |op, a: &'a Exp<Sym>, b: &'a Exp<Sym>| Some(Term::Binary(op, a, b));
            match node {
                Var(sym) => Some(Term::Alias(assignment(*sym).or_else(|| definition(*sym))?)),
                Bool(b) => Some(Term::Constant(Value::Bool(*b))),
                Bits64(b) if !b.is_empty() => Some(Term::Constant(Value::Bits(B129::new(b.lower_u64(), b.len())))),
                Bits(bits) if (1..=129).contains(&bits.len()) => {
                    let low = bits.iter().take(128).rev().fold(0u128, |word, &bit| (word << 1) | u128::from(bit));
                    let value = B129::from_u128(low, bits.len() as u32);
                    let value = if bits.get(128) == Some(&true) { value.set_slice(128, B129::BIT_ONE) } else { value };
                    Some(Term::Constant(Value::Bits(value)))
                }
                Not(a) => unary(Op::Not, a),
                And(a, b) => binary(Op::And, a, b),
                Or(a, b) => binary(Op::Or, a, b),
                Eq(a, b) => binary(Op::Eq, a, b),
                Neq(a, b) => binary(Op::Neq, a, b),
                Ite(a, b, c) => Some(Term::Ternary(Op::Ite, a, b, c)),
                Bvnot(a) => unary(Op::Bvnot, a),
                Bvneg(a) => unary(Op::Bvneg, a),
                Bvand(a, b) => binary(Op::Bvand, a, b),
                Bvor(a, b) => binary(Op::Bvor, a, b),
                Bvxor(a, b) => binary(Op::Bvxor, a, b),
                Bvnand(a, b) => binary(Op::Bvnand, a, b),
                Bvnor(a, b) => binary(Op::Bvnor, a, b),
                Bvxnor(a, b) => binary(Op::Bvxnor, a, b),
                Bvadd(a, b) => binary(Op::Bvadd, a, b),
                Bvsub(a, b) => binary(Op::Bvsub, a, b),
                Bvmul(a, b) => binary(Op::Bvmul, a, b),
                Bvshl(a, b) => binary(Op::Bvshl, a, b),
                Bvlshr(a, b) => binary(Op::Bvlshr, a, b),
                Bvashr(a, b) => binary(Op::Bvashr, a, b),
                Bvult(a, b) => binary(Op::Bvult, a, b),
                Bvule(a, b) => binary(Op::Bvule, a, b),
                Bvugt(a, b) => binary(Op::Bvugt, a, b),
                Bvuge(a, b) => binary(Op::Bvuge, a, b),
                Bvslt(a, b) => binary(Op::Bvslt, a, b),
                Bvsle(a, b) => binary(Op::Bvsle, a, b),
                Bvsgt(a, b) => binary(Op::Bvsgt, a, b),
                Bvsge(a, b) => binary(Op::Bvsge, a, b),
                Extract(hi, lo, a) => unary(Op::Extract(*hi, *lo), a),
                ZeroExtend(n, a) => unary(Op::ZeroExtend(*n), a),
                SignExtend(n, a) => unary(Op::SignExtend(*n), a),
                Concat(a, b) => binary(Op::Concat, a, b),
                _ => None,
            }
        },
    )
}

// 读绑定时，其直接操作数已经翻译。只读取已存在的常量，不遍历长定义 DAG。
pub(in crate::smt) fn fold_shallow<'ctx>(input: &Ast<'ctx>) -> Option<Ast<'ctx>> {
    let z3 = input.ctx.z3_ctx;
    let evaluator = AstEvaluator::new(input.ctx);
    let value = unsafe {
        if evaluator.constant(input.z3_ast).is_some() {
            return Some(input.clone());
        }
        if Z3_get_ast_kind(z3, input.z3_ast) != AstKind::App {
            return None;
        }
        let app = Z3_to_app(z3, input.z3_ast);
        let arity = Z3_get_app_num_args(z3, app) as usize;
        if !(1..=3).contains(&arity) {
            return None;
        }
        let kind = rewrite::decl_kind_raw(z3, Z3_get_app_decl(z3, app));
        let arg = |i| Z3_get_app_arg(z3, app, i);
        if kind == DeclKind::EQ as u32 && arg(0) == arg(1) {
            return Some(Ast::mk_bool(input.ctx, true));
        }
        if kind == DeclKind::ITE as u32 {
            let chosen = if arg(1) == arg(2) {
                arg(1)
            } else {
                match evaluator.constant(arg(0)) {
                    Some(Value::Bool(true)) => arg(1),
                    Some(Value::Bool(false)) => arg(2),
                    _ => return None,
                }
            };
            // 选中的复合臂本身仍可能被原生化简，只有字面量可直接返回。
            evaluator.constant(chosen)?;
            Z3_inc_ref(z3, chosen);
            return Some(Ast { ctx: input.ctx, z3_ast: chosen });
        }
        let mut values = [Value::Bool(false); 3];
        for (i, value) in values[..arity].iter_mut().enumerate() {
            *value = evaluator.constant(Z3_get_app_arg(z3, app, i as u32))?;
        }
        let op = match evaluator.term(input.z3_ast)? {
            Term::Unary(op, _) | Term::Binary(op, _, _) | Term::Ternary(op, _, _, _) | Term::Many(op, _) => op,
            Term::Alias(_) | Term::Constant(_) => unreachable!("复合式必须有运算符"),
        };
        op.apply(&values[..arity])?
    };
    match value {
        Value::Bool(truth) => Some(Ast::mk_bool(input.ctx, truth)),
        Value::Bits(bits) if bits.len() <= 64 => Some(Ast::mk_bv_u64(input.ctx, bits.len(), bits.lower_u64())),
        Value::Bits(bits) => {
            let raw: Vec<_> = (0..bits.len()).map(|i| bits.slice(i, 1) == Some(B129::BIT_ONE)).collect();
            Some(Ast::mk_bv(input.ctx, bits.len(), &raw))
        }
    }
}

pub(super) struct AstEvaluator<'a> {
    ctx: &'a Context,
}

impl<'a> AstEvaluator<'a> {
    pub(super) fn new(ctx: &'a Context) -> Self {
        Self { ctx }
    }

    /// 原定义已经展开在 AST 中。按与 Z3 代入相同的节点身份匹配锚点。
    /// 第二个返回值表示是否命中了与原节点不同的替换值。
    pub(super) fn evaluate(&self, root: Z3_ast, replacements: &[(Z3_ast, Z3_ast)]) -> Option<(bool, bool)> {
        if !self.ctx.solver_options.finite_domain_ground_eval {
            return None;
        }
        for (i, (anchor, _)) in replacements.iter().enumerate() {
            if replacements[..i].iter().any(|(previous, _)| previous == anchor) {
                return None;
            }
        }
        let mut changed = false;
        let value = evaluate(
            root,
            |node| node,
            |node| unsafe {
                if let Some(&(_, value)) = replacements.iter().find(|&&(anchor, _)| anchor == node) {
                    // 同时替换以匹配的节点为边界，恒等替换也不向其子树继续代入。
                    changed |= value != node;
                    return self.constant(value).map(Term::Constant);
                }
                self.term(node)
            },
        )?;
        Some((value.boolean()?, changed))
    }

    unsafe fn constant(&self, node: Z3_ast) -> Option<Value> {
        let z3 = self.ctx.z3_ctx;
        let sort = Z3_get_sort(z3, node);
        match Z3_get_sort_kind(z3, sort) {
            SortKind::Bool => match Z3_get_bool_value(z3, node) {
                Z3_L_TRUE => Some(Value::Bool(true)),
                Z3_L_FALSE => Some(Value::Bool(false)),
                _ => None,
            },
            SortKind::BV if Z3_is_numeral_ast(z3, node) => {
                let width = Z3_get_bv_sort_size(z3, sort);
                let bits = match width {
                    1..=64 => {
                        let mut bits = 0;
                        assert!(Z3_get_numeral_uint64(z3, node, &mut bits));
                        B129::new(bits, width)
                    }
                    65..=128 => {
                        let bits = CStr::from_ptr(Z3_get_numeral_string(z3, node)).to_str().unwrap().parse().unwrap();
                        B129::from_u128(bits, width)
                    }
                    129 => {
                        let bits = num_bigint::BigUint::parse_bytes(
                            CStr::from_ptr(Z3_get_numeral_string(z3, node)).to_bytes(),
                            10,
                        )
                        .unwrap();
                        let mut words = bits.iter_u64_digits();
                        let low = u128::from(words.next().unwrap_or(0)) | (u128::from(words.next().unwrap_or(0)) << 64);
                        let value = B129::from_u128(low, width);
                        if words.next() == Some(1) {
                            value.set_slice(128, B129::BIT_ONE)
                        } else {
                            value
                        }
                    }
                    _ => return None,
                };
                Some(Value::Bits(bits))
            }
            _ => None,
        }
    }

    unsafe fn term(&self, node: Z3_ast) -> Option<Term<Z3_ast>> {
        let z3 = self.ctx.z3_ctx;
        match Z3_get_ast_kind(z3, node) {
            AstKind::Numeral => return self.constant(node).map(Term::Constant),
            AstKind::App => (),
            _ => return None,
        }
        let app = Z3_to_app(z3, node);
        let decl = Z3_get_app_decl(z3, app);
        let arg = |i| Z3_get_app_arg(z3, app, i);
        let parameter = |i| u32::try_from(Z3_get_decl_int_parameter(z3, decl, i)).expect("位宽参数应为非负数");
        macro_rules! operations {
            ($kind:expr, $( $decl:ident => $op:expr ),+ $(,)?) => {
                match $kind {
                    $(kind if kind == DeclKind::$decl as u32 => $op,)+
                    _ => return None,
                }
            };
        }
        let kind = rewrite::decl_kind_raw(z3, decl);
        if kind == DeclKind::TRUE as u32 || kind == DeclKind::FALSE as u32 {
            return Some(Term::Constant(Value::Bool(kind == DeclKind::TRUE as u32)));
        }
        let op = operations!(kind,
            NOT => Op::Not, AND => Op::And, OR => Op::Or, EQ => Op::Eq, IFF => Op::Eq, ITE => Op::Ite,
            BNOT => Op::Bvnot, BNEG => Op::Bvneg, BAND => Op::Bvand, BOR => Op::Bvor,
            BXOR => Op::Bvxor, BNAND => Op::Bvnand, BNOR => Op::Bvnor, BXNOR => Op::Bvxnor,
            BADD => Op::Bvadd, BSUB => Op::Bvsub, BMUL => Op::Bvmul,
            BSHL => Op::Bvshl, BLSHR => Op::Bvlshr, BASHR => Op::Bvashr,
            ULT => Op::Bvult, ULEQ => Op::Bvule, UGT => Op::Bvugt, UGEQ => Op::Bvuge,
            SLT => Op::Bvslt, SLEQ => Op::Bvsle, SGT => Op::Bvsgt, SGEQ => Op::Bvsge,
            EXTRACT => Op::Extract(parameter(0), parameter(1)),
            ZERO_EXT => Op::ZeroExtend(parameter(0)), SIGN_EXT => Op::SignExtend(parameter(0)),
            CONCAT => Op::Concat,
        );
        Some(match Z3_get_app_num_args(z3, app) {
            1 if matches!(
                op,
                Op::Not | Op::Bvnot | Op::Bvneg | Op::Extract(..) | Op::ZeroExtend(_) | Op::SignExtend(_)
            ) =>
            {
                Term::Unary(op, arg(0))
            }
            2 => Term::Binary(op, arg(0), arg(1)),
            3 if matches!(op, Op::Ite) => Term::Ternary(op, arg(0), arg(1), arg(2)),
            n if n >= 3 && op.accepts_many() => Term::Many(op, (0..n).map(arg).collect()),
            _ => return None,
        })
    }
}
