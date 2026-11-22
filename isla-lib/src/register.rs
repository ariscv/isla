// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
// Copyright (c) 2020 Brian Campbell
// Copyright (c) 2020 Dhruv Makwana
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// 1. Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

//! This model implements a map type [RegisterBindings], from register
//! names to their values. For sequentially consistent registers like
//! GPRs (X1, X2, etc. in Arm), this is equivalent to a simple
//! key-value map from register names to their values. System
//! registers on the other hand, may require a slightly more relaxed
//! semantics depending on the model.
//!
//! For these registers, we keep track of three things:
//!
//! 1. The last written value
//! 2. The last read value
//! 3. The set of all written values
//!
//! Additionally, all registers may be in an unitialised state.
//!
//! The semantics is as follows:
//!
//! * When we _read_ from a register, return the last read value if
//!   one exists. Otherwise return a symbolic value representing
//!   non-deterministic choice between all previously written values,
//!   and set the last read value to be this value.  If the register
//!   is uninitialised when we read it, we initialise it to an
//!   symbolic unknown value of the correct type, setting both the
//!   last read value and the last written value to that unknown
//!   value.
//!
//! * When we _write_ to a register we simply store the value as the
//!   last written value. We also set the last read value to the last
//!   written value: this is so registers appear to behave as regular
//!   variables within a single instruction, i.e.
//!   ```sail
//!   R = 0x0;
//!   print_bits("R = ", R);
//!   R = 0x1;
//!   print_bits("R = ", R);
//!   ```
//!   will print `R = 0x0` then `R = 0x1`, rather than `R = 0x0` twice.
//!
//! There are two additional operations. We can _forget_ the last
//! read, which allows another previously written value to be read by
//! subsequent reads. We can also _synchronize_ the register which
//! removes all the previously written values except the last, and
//! clears the last read value, forcing subsequent reads to see the
//! last written value.

use ahash;
use std::collections::{hash_map, HashMap, HashSet};
use std::sync::Arc;

use crate::bitvector::BV;
use crate::error::ExecError;
use crate::executor::stats::region_cost as cost;
use crate::ir::*;
use crate::primop_util::{ite_choice, symbolic};
use crate::smt::{smtlib::Exp, Solver, Sym};
use crate::source_loc::SourceLoc;
use crate::zencode;

#[derive(Clone, Debug)]
enum RelaxedVal<'ir, B> {
    Uninit(&'ir Ty<Name>),
    Init { last_write: Val<B>, last_read: Option<Val<B>>, old_writes: Vec<Val<B>> },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Initialization {
    Value,
    Reserved,
    Guarded(Sym),
}

#[derive(Clone, Debug)]
pub struct Register<'ir, B> {
    relaxed: bool,
    value: RelaxedVal<'ir, B>,
    initialization: Initialization,
}

impl<'ir, B: BV> RelaxedVal<'ir, B> {
    fn unwrap_last_write(&self) -> &Val<B> {
        if let RelaxedVal::Init { last_write, .. } = self {
            last_write
        } else {
            panic!("unwrap called on uninitialized relaxed value!")
        }
    }

    // Returns the value, which could be any value written,
    // initializing it if needed. Guarantees that repeated calls to
    // value in between calls to synchronize or forget_last_read will
    // return the same value.
    fn read<'a>(
        &'a mut self,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
        info: SourceLoc,
    ) -> Result<&'a Val<B>, ExecError> {
        match self {
            RelaxedVal::Uninit(ty) => {
                let sym = symbolic(ty, shared_state, solver, info)?;
                *self = RelaxedVal::Init { last_write: sym.clone(), last_read: Some(sym), old_writes: Vec::new() };
                Ok(self.unwrap_last_write())
            }
            RelaxedVal::Init { last_read: Some(v), .. } => Ok(v),
            RelaxedVal::Init { last_read, last_write, old_writes } => {
                let value = ite_choice(last_write, old_writes, solver, info)?;
                *last_read = Some(value);
                Ok(last_read.as_ref().unwrap())
            }
        }
    }

    // Read the last written value
    fn read_last<'a>(
        &'a mut self,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
        info: SourceLoc,
    ) -> Result<&'a Val<B>, ExecError> {
        match self {
            RelaxedVal::Uninit(ty) => {
                let sym = symbolic(ty, shared_state, solver, info)?;
                *self = RelaxedVal::Init { last_write: sym, last_read: None, old_writes: Vec::new() };
                Ok(self.unwrap_last_write())
            }
            RelaxedVal::Init { last_write, .. } => Ok(last_write),
        }
    }

    // When synchronization is performed on a relaxed value (e.g. by
    // an ISB in ARM), the last written value becomes the only value.
    fn synchronize(&mut self) {
        match self {
            RelaxedVal::Uninit(_) => (),
            RelaxedVal::Init { last_read, last_write: _, old_writes } => {
                *old_writes = Vec::new();
                *last_read = None
            }
        }
    }

    // Forget the last value read to the value, allowing read to
    // return any written value once again.
    fn forget_last_read(&mut self) {
        match self {
            RelaxedVal::Uninit(_) => (),
            RelaxedVal::Init { last_read, .. } => *last_read = None,
        }
    }

    fn write(&mut self, value: Val<B>) {
        match self {
            RelaxedVal::Uninit(_) => {
                *self = RelaxedVal::Init { last_write: value.clone(), last_read: Some(value), old_writes: Vec::new() };
            }
            RelaxedVal::Init { last_write, last_read, old_writes } => {
                old_writes.push(last_write.clone());
                *last_read = Some(value.clone());
                *last_write = value
            }
        }
    }

    fn write_last(&mut self, value: Val<B>) {
        match self {
            RelaxedVal::Uninit(_) => {
                *self = RelaxedVal::Init { last_write: value, last_read: None, old_writes: Vec::new() };
            }
            RelaxedVal::Init { last_write, .. } => *last_write = value,
        }
    }
}

impl<'ir, B: BV> Register<'ir, B> {
    pub(crate) fn remap_symbols(&mut self, remap: &crate::smt::SymRemap) {
        match &mut self.value {
            RelaxedVal::Uninit(_) => (),
            RelaxedVal::Init { last_write, last_read, old_writes } => {
                *last_write = last_write.remap_symbols(remap);
                *last_read = last_read.as_ref().map(|value| value.remap_symbols(remap));
                for value in old_writes {
                    *value = value.remap_symbols(remap);
                }
            }
        }
        if let Initialization::Guarded(symbol) = &mut self.initialization {
            *symbol = remap.get(*symbol);
        }
    }

    pub fn read<'a>(
        &'a mut self,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
        info: SourceLoc,
    ) -> Result<&'a Val<B>, ExecError> {
        self.initialization = Initialization::Value;
        if self.relaxed {
            self.value.read(shared_state, solver, info)
        } else {
            self.value.read_last(shared_state, solver, info)
        }
    }

    pub fn collect_symbolic_variables(&self, vars: &mut HashSet<Sym, ahash::RandomState>) {
        if let RelaxedVal::Init { last_write, last_read, old_writes } = &self.value {
            last_write.collect_symbolic_variables(vars);
            if let Some(last_read) = last_read {
                last_read.collect_symbolic_variables(vars)
            }
            for write in old_writes {
                write.collect_symbolic_variables(vars)
            }
        }
    }

    /// Read the last written value to the register if it is
    /// initialized. Returns None if the register is uninitialized.
    pub fn read_last_if_initialized(&self) -> Option<&Val<B>> {
        match &self.value {
            RelaxedVal::Init { last_write, .. } => Some(last_write),
            RelaxedVal::Uninit(_) => None,
        }
    }

    /// 取得读写语义上的初始化位。区域为另一臂预留的入口值仍可保持未初始化。
    pub fn initialization(&self) -> Val<B> {
        match self.initialization {
            Initialization::Value => Val::Bool(self.read_last_if_initialized().is_some()),
            Initialization::Reserved => Val::Bool(false),
            Initialization::Guarded(guard) => Val::Symbolic(guard),
        }
    }

    pub fn write(&mut self, value: Val<B>) {
        self.initialization = Initialization::Value;
        if self.relaxed {
            self.value.write(value)
        } else {
            self.value.write_last(value)
        }
    }

    pub fn synchronize(&mut self) {
        if self.relaxed {
            self.value.synchronize()
        }
    }

    pub fn forget_last_read(&mut self) {
        if self.relaxed {
            self.value.forget_last_read()
        }
    }
    pub fn read_old_if_initialized(&self) -> Option<&Vec<Val<B>>> {
        match &self.value {
            RelaxedVal::Init { old_writes, .. } => Some(old_writes),
            RelaxedVal::Uninit(_) => None,
        }
    }
    /// 读取寄存器的初始值（如果已初始化）。
    /// 对于 relaxed 寄存器，返回历史写入记录中的第一个值（最早的写入）；
    /// 如果没有历史写入记录，则返回当前的 last_write 值。
    /// 如果寄存器未初始化，返回 None。
    pub fn read_init_value_if_initialized(&self) -> Option<&Val<B>> {
        // 如果未初始化则返回None
        self.read_old_if_initialized().and_then(|value_vec| {
            // 条件：历史写入记录为空 → 返回当前值（这是唯一的写入）
            // 条件：历史写入记录非空 → 返回最早的值（初始值）
            match value_vec.is_empty() {
                true => self.read_last_if_initialized(),
                false => Some(&value_vec[0]),
            }
        })
    }
}

#[derive(Clone)]
pub struct RegisterBindings<'ir, B> {
    // 帧只改局部变量时，各臂继续共享只读寄存器表。
    map: Arc<HashMap<Name, Register<'ir, B>, ahash::RandomState>>,
}

/// An iterator over registers in a [RegisterBindings]
pub struct Iter<'a, 'ir, B> {
    iterator: hash_map::Iter<'a, Name, Register<'ir, B>>,
}

impl<'ir, B: BV> RegisterBindings<'ir, B> {
    pub(crate) fn remap_symbols(&mut self, remap: &crate::smt::SymRemap) {
        for register in cost::make_mut(&mut self.map).values_mut() {
            register.remap_symbols(remap);
        }
    }

    pub fn new() -> Self {
        RegisterBindings { map: Arc::default() }
    }

    pub fn insert(&mut self, id: Name, relaxed: bool, v: UVal<'ir, B>) {
        match v {
            UVal::Uninit(ty) => {
                cost::make_mut(&mut self.map).insert(
                    id,
                    Register { relaxed, value: RelaxedVal::Uninit(ty), initialization: Initialization::Value },
                );
            }
            UVal::Init(value) => {
                cost::make_mut(&mut self.map).insert(
                    id,
                    Register {
                        relaxed,
                        initialization: Initialization::Value,
                        value: RelaxedVal::Init { last_write: value, last_read: None, old_writes: Vec::new() },
                    },
                );
            }
        }
    }

    pub fn insert_register(&mut self, id: Name, v: Register<'ir, B>) {
        cost::make_mut(&mut self.map).insert(id, v);
    }

    pub fn get<'a>(
        &'a mut self,
        id: Name,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
        info: SourceLoc,
    ) -> Result<Option<&'a Val<B>>, ExecError> {
        let Some(register) = self.map.get(&id) else { return Ok(None) };
        if !register.relaxed
            && register.initialization == Initialization::Value
            && register.read_last_if_initialized().is_some()
        {
            return Ok(self.get_last_if_initialized(id));
        }
        let register = cost::make_mut(&mut self.map).get_mut(&id).unwrap();
        register.read(shared_state, solver, info).map(Some)
    }

    /// 无序区域只读取已写入的最新值。普通执行仍调用 get。
    pub(crate) fn get_latest<'a>(
        &'a mut self,
        id: Name,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
        info: SourceLoc,
    ) -> Result<Option<&'a Val<B>>, ExecError> {
        let Some(register) = self.map.get(&id) else { return Ok(None) };
        if register.initialization == Initialization::Value && register.read_last_if_initialized().is_some() {
            return Ok(self.get_last_if_initialized(id));
        }
        let register = cost::make_mut(&mut self.map).get_mut(&id).unwrap();
        register.initialization = Initialization::Value;
        register.value.read_last(shared_state, solver, info).map(Some)
    }

    pub(crate) fn merge_initial(
        &mut self,
        id: Name,
        shared: &SharedState<'ir, B>,
        terms: &mut dyn crate::primop_util::merge_terms::MergeTerms<B>,
        info: SourceLoc,
    ) -> Result<Val<B>, ExecError> {
        let initial = match &self.map[&id].value {
            RelaxedVal::Init { last_write, .. } => return Ok(last_write.clone()),
            RelaxedVal::Uninit(ty) => crate::primop_util::symbolic_terms(ty, shared.typedefs(), terms, info)?,
        };
        self.assign(id, initial.clone(), shared);
        Ok(initial)
    }

    pub(crate) fn reserve_initial(&mut self, id: Name, value: Val<B>) {
        let register = cost::make_mut(&mut self.map).get_mut(&id).expect("区域入口必须有寄存器");
        assert!(register.read_last_if_initialized().is_none());
        register.write(value);
        register.initialization = Initialization::Reserved;
    }

    pub(crate) fn merge_initialization(
        &mut self,
        id: Name,
        condition: Sym,
        left: &Self,
        right: &Self,
        solver: &mut dyn crate::primop_util::merge_terms::MergeTerms<B>,
        info: SourceLoc,
    ) {
        let terms = [left, right].map(|bindings| match bindings.map[&id].initialization() {
            Val::Bool(value) => Exp::Bool(value),
            Val::Symbolic(guard) => Exp::Var(guard),
            _ => unreachable!("初始化位必须是布尔值"),
        });
        let [a, b] = terms;
        let value = if a == b { a } else { Exp::Ite(Box::new(Exp::Var(condition)), Box::new(a), Box::new(b)).eval() };
        let initialization = match value {
            Exp::Bool(true) => Initialization::Value,
            Exp::Bool(false) => Initialization::Reserved,
            Exp::Var(guard) => Initialization::Guarded(guard),
            value => Initialization::Guarded(solver.define_const(value, info)),
        };
        if self.map[&id].initialization != initialization {
            cost::make_mut(&mut self.map).get_mut(&id).unwrap().initialization = initialization;
        }
    }

    /// 外层可能继续用普通的 relaxed 读。历史逐项带合并守卫，缺项重复同臂的最新值。
    pub(crate) fn merge_relaxed(
        &mut self,
        id: Name,
        condition: Sym,
        left: &Self,
        right: &Self,
        solver: &mut dyn crate::primop_util::merge_terms::MergeTerms<B>,
        info: SourceLoc,
    ) -> Result<(), ExecError> {
        use crate::primop_util::{ite_choice_terms, merge_val_mode};
        let entry = self.map.get(&id).expect("区域基帧必须有寄存器");
        assert!(entry.relaxed && left.map[&id].relaxed && right.map[&id].relaxed);
        let [left, right] = [&left.map[&id].value, &right.map[&id].value].map(|value| match value {
            RelaxedVal::Uninit(_) => &entry.value,
            _ => value,
        });
        let RelaxedVal::Init { last_write: a, last_read: ra, old_writes: ha } = left else {
            panic!("汇合前必须补齐惰性入口值")
        };
        let RelaxedVal::Init { last_write: b, last_read: rb, old_writes: hb } = right else {
            panic!("汇合前必须补齐惰性入口值")
        };
        let last_write = merge_val_mode::<B, false>(condition, a, b, solver, info)?;
        let last_read = if ra.is_some() || rb.is_some() {
            let ra = match ra {
                Some(read) => read.clone(),
                None => ite_choice_terms(a, ha, solver, info)?,
            };
            let rb = match rb {
                Some(read) => read.clone(),
                None => ite_choice_terms(b, hb, solver, info)?,
            };
            Some(merge_val_mode::<B, false>(condition, &ra, &rb, solver, info)?)
        } else {
            None
        };
        let old_writes = (0..ha.len().max(hb.len()))
            .map(|index| {
                merge_val_mode::<B, false>(
                    condition,
                    ha.get(index).unwrap_or(a),
                    hb.get(index).unwrap_or(b),
                    solver,
                    info,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        cost::make_mut(&mut self.map).get_mut(&id).unwrap().value =
            RelaxedVal::Init { last_write, last_read, old_writes };
        Ok(())
    }

    /// 在当前寄存器符号上施加 SMT 配置约束，允许引用具体的顶层 let。
    pub fn apply_constraints(
        &mut self,
        constraints: &[crate::smt::smtlib::Exp<Loc<String>>],
        lets: &Bindings<'ir, B>,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
        info: SourceLoc,
    ) -> Result<(), ExecError> {
        for constraint in constraints {
            let assertion = constraint.map_var(&mut |reference| {
                let loc = shared_state
                    .symtab
                    .get_loc(reference)
                    .ok_or_else(|| ExecError::Unreachable(format!("初态约束引用不存在的位置 {reference}")))?;
                let mut projections = Vec::new();
                let mut root = &loc;
                let name = loop {
                    match root {
                        Loc::Id(name) => break *name,
                        Loc::Field(parent, _) | Loc::Index(parent, _) => {
                            projections.push(root);
                            root = parent;
                        }
                        Loc::Addr(_) => panic!("初态约束不能读取地址位置"),
                    }
                };
                let (mut value, is_let) = match self.get(name, shared_state, solver, info)? {
                    Some(value) => (value, false),
                    None => match lets.get(&name) {
                        Some(UVal::Init(value)) => (value, true),
                        _ => {
                            return Err(ExecError::Unreachable(format!(
                                "初态约束需要寄存器或已初始化的顶层 let：{reference}"
                            )))
                        }
                    },
                };
                for projection in projections.into_iter().rev() {
                    value = match (projection, value) {
                        (Loc::Field(_, field), Val::Struct(members)) => members.get(field),
                        (Loc::Index(_, index), Val::Vector(values)) => values.get(*index as usize),
                        _ => None,
                    }
                    .ok_or_else(|| ExecError::Type(format!("初态约束引用无效字段或向量元素：{reference}"), info))?;
                }
                if is_let && value.is_symbolic() {
                    return Err(ExecError::Type(format!("初态约束需要具体的顶层 let：{reference}"), info));
                }
                crate::primop_util::smt_value(value, info)
            })?;
            solver.add_event(crate::smt::Event::Assume(constraint.clone()));
            solver.assert(assertion);
        }
        Ok(())
    }

    // A non-modifying way to inspect a register
    pub fn get_last_if_initialized(&self, id: Name) -> Option<&Val<B>> {
        if let Some(reg) = self.map.get(&id) {
            if let Some(val) = reg.read_last_if_initialized() {
                Some(val)
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn forget_last_reads(&mut self) {
        for reg in cost::make_mut(&mut self.map).values_mut() {
            reg.forget_last_read()
        }
    }

    pub fn synchronize(&mut self) {
        for reg in cost::make_mut(&mut self.map).values_mut() {
            reg.synchronize()
        }
    }

    pub fn synchronize_register(&mut self, id: Name) {
        if let Some(reg) = cost::make_mut(&mut self.map).get_mut(&id) {
            reg.synchronize()
        }
    }

    pub fn contains_key(&self, id: Name) -> bool {
        self.map.contains_key(&id)
    }

    pub fn is_relaxed(&self, id: Name) -> bool {
        self.map.get(&id).expect("register must exist").relaxed
    }

    pub fn has_old_writes(&self, id: Name) -> bool {
        matches!(self.map.get(&id).expect("register must exist").read_old_if_initialized(), Some(writes) if !writes.is_empty())
    }

    pub fn assign(&mut self, id: Name, v: Val<B>, shared_state: &SharedState<'ir, B>) {
        if let Some(reg) = cost::make_mut(&mut self.map).get_mut(&id) {
            reg.write(v)
        } else {
            let symbol = zencode::decode(shared_state.symtab.to_str(id));
            panic!("No relaxed value {} ({:?})", symbol, id)
        }
    }

    pub fn iter<'a>(&'a self) -> Iter<'a, 'ir, B> {
        Iter { iterator: self.map.iter() }
    }
}

impl<B: BV> Default for RegisterBindings<'_, B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, 'ir, B: BV> Iterator for Iter<'a, 'ir, B> {
    type Item = (&'a Name, &'a Register<'ir, B>);

    fn next(&mut self) -> Option<Self::Item> {
        self.iterator.next()
    }
}

impl<'a, 'ir, B: BV> IntoIterator for &'a RegisterBindings<'ir, B> {
    type Item = (&'a Name, &'a Register<'ir, B>);
    type IntoIter = Iter<'a, 'ir, B>;

    fn into_iter(self) -> Self::IntoIter {
        Iter { iterator: self.map.iter() }
    }
}

impl<B: BV> RegisterBindings<'_, B> {
    pub(crate) fn estimated_bytes(&self, seen: &mut HashSet<usize>) -> usize {
        use crate::executor::stats::memory_stats::{map_bytes, value_heap_bytes};
        if !seen.insert(Arc::as_ptr(&self.map) as usize) {
            return 0;
        }
        map_bytes::<Name, Register<B>>(self.map.capacity())
            + self
                .map
                .values()
                .map(|reg| match &reg.value {
                    RelaxedVal::Uninit(_) => 0,
                    RelaxedVal::Init { last_write, last_read, old_writes } => {
                        value_heap_bytes(last_write)
                            + last_read.as_ref().map_or(0, value_heap_bytes)
                            + old_writes.capacity() * std::mem::size_of::<Val<B>>()
                            + old_writes.iter().map(value_heap_bytes).sum::<usize>()
                    }
                })
                .sum::<usize>()
    }
}
