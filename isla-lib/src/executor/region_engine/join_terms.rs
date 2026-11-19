use super::*;
use crate::smt::EnumId;
use smtlib::{Def, Exp, Ty};

pub(in crate::executor) struct Terms<'a, 'ctx, B> {
    solver: &'a Solver<'ctx, B>,
    start: u32,
    symbols: Vec<(Option<Ty>, bool, Option<Arc<Exp<Sym>>>)>,
    operations: Vec<Operation<B>>,
}

pub(in crate::executor) enum Operation<B> {
    Define(Sym, Arc<Exp<Sym>>, bool, SourceLoc),
    Declare(Sym, Ty, bool, SourceLoc),
    Enum(Name, usize),
    Fact(Exp<Sym>),
    AssumeReg(Name, Val<B>),
    GuardedValue,
}

pub(in crate::executor) fn emit<B: BV>(operations: Vec<Operation<B>>, solver: &mut Solver<B>) {
    for operation in operations {
        match operation {
            Operation::Define(sym, exp, bits, loc) => {
                solver.add_join_definition(Def::DefineConst(sym, Arc::unwrap_or_clone(exp)), bits, loc);
            }
            Operation::Declare(sym, ty, bits, loc) => {
                solver.add_join_definition(Def::DeclareConst(sym, ty), bits, loc);
            }
            Operation::Enum(name, size) => {
                solver.get_enum(name, size);
            }
            Operation::Fact(exp) => solver.assert_region_input_fact(exp),
            Operation::AssumeReg(reg, value) => solver.add_event(Event::AssumeReg(reg, Vec::new(), value)),
            Operation::GuardedValue => super::super::concrete_values::created(),
        }
    }
}

impl<'a, 'ctx, B: BV> Terms<'a, 'ctx, B> {
    pub(super) fn new(solver: &'a Solver<'ctx, B>) -> Self {
        Self { solver, start: solver.next_join_symbol(), symbols: Vec::new(), operations: Vec::new() }
    }

    pub(super) fn mark(&self) -> usize {
        assert!(self.operations.is_empty());
        self.symbols.len()
    }

    pub(super) fn discard(&mut self, mark: usize) {
        self.symbols.truncate(mark);
        self.operations.clear();
    }

    pub(super) fn take_operations(&mut self) -> Vec<Operation<B>> {
        std::mem::take(&mut self.operations)
    }

    fn next(&self) -> u32 {
        self.start.checked_add(u32::try_from(self.symbols.len()).unwrap()).expect("汇合符号编号溢出")
    }

    pub(super) fn symbol_range(&self) -> (u32, u32) {
        (self.start, self.next())
    }

    fn index(&self, symbol: Sym) -> Option<usize> {
        symbol.as_u32().checked_sub(self.start).map(|index| index as usize)
    }
}

impl<B: BV> MergeTerms<B> for Terms<'_, '_, B> {
    fn sort(&self, symbol: Sym) -> Option<Ty> {
        match self.index(symbol) {
            Some(index) => self.symbols[index].0.clone(),
            None => self.solver.scalar_sort(symbol),
        }
    }

    fn is_sail_bitvector(&self, symbol: Sym) -> bool {
        match self.index(symbol) {
            Some(index) => self.symbols[index].1,
            None => self.solver.is_sail_bitvector(symbol),
        }
    }

    fn define(&mut self, exp: Exp<Sym>, bits: bool, info: SourceLoc) -> Sym {
        let sym = Sym::from_u32(self.next());
        let ty = self.expression_sort(&exp);
        let exp = Arc::new(exp);
        self.symbols.push((ty, bits, Some(exp.clone())));
        self.operations.push(Operation::Define(sym, exp, bits, info));
        sym
    }

    fn declare(&mut self, ty: Ty, bits: bool, info: SourceLoc) -> Sym {
        let sym = Sym::from_u32(self.next());
        self.symbols.push((Some(ty.clone()), bits, None));
        self.operations.push(Operation::Declare(sym, ty, bits, info));
        sym
    }

    fn get_enum(&mut self, name: Name, size: usize) -> EnumId {
        self.operations.push(Operation::Enum(name, size));
        EnumId::from_name(name)
    }

    fn assert_region_input_fact(&mut self, exp: Exp<Sym>) {
        self.operations.push(Operation::Fact(exp));
    }

    fn assume_reg(&mut self, reg: Name, value: Val<B>) {
        self.operations.push(Operation::AssumeReg(reg, value));
    }

    fn structural_bool(&self, exp: &Exp<Sym>) -> Option<bool> {
        let mut pending = exp.variables().into_iter().collect::<Vec<_>>();
        let mut definitions = std::collections::HashMap::new();
        while let Some(sym) = pending.pop() {
            if let Some(index) = self.index(sym) {
                if let std::collections::hash_map::Entry::Vacant(entry) = definitions.entry(sym) {
                    let definition = self.symbols[index].2.as_deref()?;
                    pending.extend(definition.variables());
                    entry.insert(definition);
                }
            }
        }
        if definitions.is_empty() {
            self.solver.structural_bool(exp)
        } else {
            self.solver.structural_bool(&exp.clone_expand(&definitions))
        }
    }

    fn record_guarded_value(&mut self) {
        self.operations.push(Operation::GuardedValue);
    }
}
