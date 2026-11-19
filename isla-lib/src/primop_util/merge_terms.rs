//! 值合并与符号初值共用的操作。计划器在登记前可以查询已有类型、记录待发布的定义。
use super::*;
use crate::smt::{EnumId, Event};

pub(crate) trait MergeTerms<B: BV> {
    fn sort(&self, symbol: Sym) -> Option<smtlib::Ty>;
    fn is_sail_bitvector(&self, symbol: Sym) -> bool;
    fn define(&mut self, exp: Exp<Sym>, bits: bool, info: SourceLoc) -> Sym;
    fn declare(&mut self, ty: smtlib::Ty, bits: bool, info: SourceLoc) -> Sym;
    fn get_enum(&mut self, name: Name, size: usize) -> EnumId;
    fn assert_region_input_fact(&mut self, exp: Exp<Sym>);
    fn assume_reg(&mut self, reg: Name, value: Val<B>);
    fn structural_bool(&self, exp: &Exp<Sym>) -> Option<bool>;
    fn record_guarded_value(&mut self);

    fn expression_sort(&self, exp: &Exp<Sym>) -> Option<smtlib::Ty> {
        use smtlib::{Exp::*, Ty};
        match exp {
            Var(sym) => self.sort(*sym),
            Bits(bits) => Some(Ty::BitVec(u32::try_from(bits.len()).unwrap())),
            Bits64(bits) => Some(Ty::BitVec(bits.len())),
            Bool(_) | Not(_) | Or(_, _) | And(_, _) | Eq(_, _) => Some(Ty::Bool),
            Enum(member) => Some(Ty::Enum(member.enum_id)),
            Ite(_, yes, _) => self.expression_sort(yes),
            Concat(left, right) => match (self.expression_sort(left)?, self.expression_sort(right)?) {
                (Ty::BitVec(left), Ty::BitVec(right)) => Some(Ty::BitVec(left + right)),
                _ => None,
            },
            _ => unreachable!("汇合只定义值、守卫和连接"),
        }
    }

    fn length(&self, symbol: Sym) -> Option<u32> {
        match self.sort(symbol)? {
            smtlib::Ty::BitVec(width) => Some(width),
            _ => None,
        }
    }

    fn define_const(&mut self, exp: Exp<Sym>, info: SourceLoc) -> Sym {
        self.define(exp, false, info)
    }

    fn define_bitvector(&mut self, exp: Exp<Sym>, info: SourceLoc) -> Sym {
        self.define(exp, true, info)
    }

    fn declare_const(&mut self, ty: smtlib::Ty, info: SourceLoc) -> Sym {
        self.declare(ty, false, info)
    }

    fn declare_bitvector(&mut self, width: u32, info: SourceLoc) -> Sym {
        self.declare(smtlib::Ty::BitVec(width), true, info)
    }
}

impl<B: BV> MergeTerms<B> for Solver<'_, B> {
    fn sort(&self, symbol: Sym) -> Option<smtlib::Ty> {
        self.scalar_sort(symbol)
    }

    fn is_sail_bitvector(&self, symbol: Sym) -> bool {
        self.is_sail_bitvector(symbol)
    }

    fn define(&mut self, exp: Exp<Sym>, bits: bool, info: SourceLoc) -> Sym {
        if bits {
            self.define_bitvector(exp, info)
        } else {
            self.define_const(exp, info)
        }
    }

    fn declare(&mut self, ty: smtlib::Ty, bits: bool, info: SourceLoc) -> Sym {
        match (bits, ty) {
            (true, smtlib::Ty::BitVec(width)) => self.declare_bitvector(width, info),
            (false, ty) => self.declare_const(ty, info),
            _ => unreachable!("位向量声明必须使用位向量 SMT 类型"),
        }
    }

    fn get_enum(&mut self, name: Name, size: usize) -> EnumId {
        self.get_enum(name, size)
    }

    fn assert_region_input_fact(&mut self, exp: Exp<Sym>) {
        self.assert_region_input_fact(exp)
    }

    fn assume_reg(&mut self, reg: Name, value: Val<B>) {
        self.add_event(Event::AssumeReg(reg, Vec::new(), value));
    }

    fn structural_bool(&self, exp: &Exp<Sym>) -> Option<bool> {
        self.structural_bool(exp)
    }

    fn record_guarded_value(&mut self) {
        crate::executor::concrete_values::created();
    }
}
