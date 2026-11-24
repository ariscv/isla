//! 从失败守卫与活动臂条件中传播布尔字面量。
use super::prefix_index::{slice_comparison, Slice};
use super::*;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Atom {
    Symbol(Sym),
    Bit(Slice),
    Expression(*const Exp<Sym>),
}

struct Facts<'a, 'p, B> {
    prefix: &'p PathConditions<'a, B>,
    values: HashMap<Atom, bool>,
    clauses: Vec<(&'a Exp<Sym>, bool)>,
    visits_left: usize,
}

impl<'a, B: BV> Facts<'a, '_, B> {
    fn spend(&mut self, depth: usize) -> bool {
        if depth == 0 || self.visits_left == 0 {
            return false;
        }
        self.visits_left -= 1;
        true
    }

    fn atom(&self, exp: &'a Exp<Sym>) -> (Atom, bool) {
        if let Exp::Var(sym) = exp {
            return (Atom::Symbol(*sym), true);
        }
        if let Exp::Eq(..) | Exp::Neq(..) = exp {
            if let Some((slice, value, equal)) =
                slice_comparison(exp, |exp| resolve(exp, self.prefix), |sym| self.prefix.definition(sym))
            {
                if value.len() == 1 {
                    return (Atom::Bit(slice), equal == (value == B64::BIT_ONE));
                }
            }
        }
        (Atom::Expression(exp), true)
    }

    // 只展开必须同时成立的分量。尚有选择的子句留待字面量登记之后检查。
    fn require(&mut self, exp: &'a Exp<Sym>, expected: bool, depth: usize) -> bool {
        if !self.spend(depth) {
            return false;
        }
        use Exp::*;
        let exp = resolve(exp, self.prefix);
        let child = depth - 1;
        match exp {
            Bool(value) => *value != expected,
            Not(inner) => self.require(inner, !expected, child),
            And(a, b) | Or(a, b) if matches!(exp, And(..)) == expected => {
                self.require(a, expected, child) || self.require(b, expected, child)
            }
            Ite(g, a, b) if matches!(resolve(a, self.prefix), Bool(value) if *value != expected) => {
                self.require(g, false, child) || self.require(b, expected, child)
            }
            Ite(g, a, b) if matches!(resolve(b, self.prefix), Bool(value) if *value != expected) => {
                self.require(g, true, child) || self.require(a, expected, child)
            }
            And(..) | Or(..) | Ite(..) => {
                self.clauses.push((exp, expected));
                false
            }
            _ => {
                let (atom, positive) = self.atom(exp);
                let value = expected == positive;
                self.values.insert(atom, value).is_some_and(|previous| previous != value)
            }
        }
    }

    fn evaluate(&mut self, exp: &'a Exp<Sym>, depth: usize) -> Option<bool> {
        if !self.spend(depth) {
            return None;
        }
        use Exp::*;
        let exp = resolve(exp, self.prefix);
        let child = depth - 1;
        match exp {
            Bool(value) => Some(*value),
            Not(inner) => self.evaluate(inner, child).map(|x| !x),
            And(a, b) | Or(a, b) => {
                let decisive = matches!(exp, Or(..));
                let a = self.evaluate(a, child);
                if a == Some(decisive) {
                    return a;
                }
                let b = self.evaluate(b, child);
                if b == Some(decisive) || a == b {
                    b
                } else {
                    None
                }
            }
            Ite(g, a, b) => match self.evaluate(g, child) {
                Some(value) => self.evaluate(if value { a } else { b }, child),
                None => {
                    let a = self.evaluate(a, child)?;
                    (self.evaluate(b, child)? == a).then_some(a)
                }
            },
            _ => {
                let (atom, positive) = self.atom(exp);
                self.values.get(&atom).map(|value| *value == positive)
            }
        }
    }
}

pub(super) fn contradiction<'a, B: BV>(
    prefix: &PathConditions<'a, B>,
    reach: &'a Exp<Sym>,
    guards: &'a [Exp<Sym>],
) -> bool {
    const DEPTH: usize = 64;
    let mut facts = Facts { prefix, values: HashMap::new(), clauses: Vec::new(), visits_left: 1024 };
    if std::iter::once(reach).chain(guards.iter().rev()).any(|exp| facts.require(exp, true, DEPTH)) {
        return true;
    }
    std::mem::take(&mut facts.clauses)
        .into_iter()
        .any(|(exp, expected)| facts.evaluate(exp, DEPTH).is_some_and(|value| value != expected))
}
