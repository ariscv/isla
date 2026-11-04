// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
// Copyright (c) 2020 Brian Campbell
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

//! This module implements utility functions used to construct
//! primitive operations, including converting IR values into SMT
//! equivalents.

use std::collections::{hash_map::Entry, HashMap, HashSet};

use crate::bitvector::b64::B64;
use crate::bitvector::BV;
use crate::error::ExecError;
use crate::ir::{Bindings, BitsSegment, Name, SharedState, Ty, Typedefs, UVal, Val};
use crate::register::RegisterBindings;
use crate::smt::smtlib::{self, bits64, Exp};
use crate::smt::{Solver, Sym};
use crate::source_loc::SourceLoc;

#[allow(clippy::needless_range_loop)]
pub fn smt_i128<V>(i: i128) -> Exp<V> {
    let mut bitvec = [false; 128];
    for n in 0..128 {
        if (i >> n & 1) == 1 {
            bitvec[n] = true
        }
    }
    Exp::Bits(bitvec.to_vec())
}

/// 将 128 位补码整数调整为位向量算术所需的宽度。
pub fn smt_int_to_bits<V>(value: Exp<V>, width: u32) -> Exp<V> {
    assert!(width > 0, "SMT 位向量宽度必须非零");
    if width > 128 {
        Exp::SignExtend(width - 128, Box::new(value))
    } else if width < 128 {
        Exp::Extract(width - 1, 0, Box::new(value))
    } else {
        value
    }
}

pub fn i128_from_bits(bitvec: &[bool]) -> i128 {
    let mut i = 0;
    for n in 0..128 {
        if bitvec[n] {
            i |= 1 << n
        }
    }
    i
}

pub fn smt_i64<V>(i: i64) -> Exp<V> {
    Exp::Bits64(B64::new(i as u64, 64))
}

pub fn smt_u8<V>(i: u8) -> Exp<V> {
    Exp::Bits64(B64::new(i as u64, 8))
}

pub fn smt_sbits<B: BV, V>(bv: B) -> Exp<V> {
    if let Ok(u) = bv.try_into() {
        bits64(u, bv.len())
    } else {
        Exp::Bits(bv.to_vec())
    }
}

/// Return the length of a concrete or symbolic bitvector, or return
/// [ExecError::Type] if the argument value is not a bitvector.
pub fn length_bits<B: BV>(bits: &Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<u32, ExecError> {
    match bits {
        Val::Bits(bits) => Ok(bits.len()),
        Val::Symbolic(bits) => match solver.length(*bits) {
            Some(len) => Ok(len),
            None => Err(ExecError::Type(format!("length_bits (solver cannot determine length) {:?}", &bits), info)),
        },
        Val::MixedBits(segments) => segments_length(segments, solver, info),
        _ => Err(ExecError::Type(format!("length_bits {:?}", &bits), info)),
    }
}

// If the argument is a mixed bitvector, concatenate neighbouring concrete
// sections, and if the result is a single concrete bitvector then return
// it as a normal bitvector.
fn flatten_mixed_bits<B: BV>(value: Val<B>) -> Val<B> {
    match value {
        Val::MixedBits(mut segments) => {
            let mut new_segments: Vec<BitsSegment<B>> = vec![];
            match segments.drain(..).fold(None, |acc: Option<B>, segment| match (acc, segment) {
                (Some(bv), BitsSegment::Concrete(bv2)) => bv.append(bv2).or_else(|| {
                    new_segments.push(BitsSegment::Concrete(bv));
                    Some(bv2)
                }),
                (None, BitsSegment::Concrete(bv)) => Some(bv),
                (Some(bv), segment) => {
                    new_segments.push(BitsSegment::Concrete(bv));
                    new_segments.push(segment);
                    None
                }
                (None, segment) => {
                    new_segments.push(segment);
                    None
                }
            }) {
                None => Val::MixedBits(new_segments),
                Some(bv) => {
                    if new_segments.is_empty() {
                        Val::Bits(bv)
                    } else {
                        new_segments.push(BitsSegment::Concrete(bv));
                        Val::MixedBits(new_segments)
                    }
                }
            }
        }
        value => value,
    }
}

/// If a value is a mixed symbolic/concrete bitvector, replace it with a
/// symbolic value and a suitable constraint.
pub fn replace_mixed_bits<B: BV>(value: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let value = flatten_mixed_bits(value);
    match value {
        Val::MixedBits(segments) => {
            let smt_exp = segments
                .iter()
                .map(|segment| match segment {
                    BitsSegment::Symbolic(v) => Exp::Var(*v),
                    BitsSegment::Concrete(bs) => smt_sbits(*bs),
                })
                .fold(None, |acc, next_exp| match (next_exp, acc) {
                    (Exp::Bits64(bv2), Some(Exp::Bits64(bv1))) => Some(
                        bv1.append(bv2)
                            .map(Exp::Bits64)
                            .unwrap_or_else(|| Exp::Concat(Box::new(Exp::Bits64(bv1)), Box::new(Exp::Bits64(bv2)))),
                    ),
                    (next_exp, Some(exp)) => Some(Exp::Concat(Box::new(exp), Box::new(next_exp))),
                    (next_exp, None) => Some(next_exp),
                })
                .ok_or_else(|| ExecError::Type("empty MixedBits".to_string(), info))?;
            let sym = solver.define_bitvector(smt_exp, info);
            Ok(Val::Symbolic(sym))
        }
        _ => Ok(value),
    }
}

pub fn mixed_bits_to_smt<B: BV>(value: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Exp<Sym>, ExecError> {
    match replace_mixed_bits(value, solver, info)? {
        Val::Symbolic(v) => Ok(Exp::Var(v)),
        Val::Bits(bv) => Ok(smt_sbits(bv)),
        _ => Err(ExecError::Type("mixed_bits_to_smt".to_string(), info)),
    }
}

pub fn segment_length<B: BV>(
    segment: &BitsSegment<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<u32, ExecError> {
    match segment {
        BitsSegment::Symbolic(v) => match solver.length(*v) {
            Some(len) => Ok(len),
            None => Err(ExecError::Type(format!("length (solver cannot determine length) {:?}", &v), info)),
        },
        BitsSegment::Concrete(bv) => Ok(bv.len()),
    }
}

pub fn segments_length<B: BV>(
    segments: &[BitsSegment<B>],
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<u32, ExecError> {
    segments.iter().try_fold(0, |n, segment| Ok(n + segment_length(segment, solver, info)?))
}

/// Convert base values into SMT equivalents.
pub fn smt_value<B: BV>(v: &Val<B>, info: SourceLoc) -> Result<Exp<Sym>, ExecError> {
    Ok(match v {
        Val::I128(n) => smt_i128(*n),
        Val::I64(n) => smt_i64(*n),
        Val::Bits(bv) => smt_sbits(*bv),
        Val::Bool(b) => Exp::Bool(*b),
        Val::Enum(e) => Exp::Enum(*e),
        Val::Symbolic(v) => Exp::Var(*v),
        Val::MixedBits(segments) => {
            let mut segments = segments.iter();
            let Some(first) = segments.next() else {
                return Err(ExecError::Type("smt_value empty MixedBits".to_string(), info));
            };
            let mut exp = match first {
                BitsSegment::Concrete(bv) => smt_sbits(*bv),
                BitsSegment::Symbolic(v) => Exp::Var(*v),
            };
            for segment in segments {
                let rhs = match segment {
                    BitsSegment::Concrete(bv) => smt_sbits(*bv),
                    BitsSegment::Symbolic(v) => Exp::Var(*v),
                };
                exp = Exp::Concat(Box::new(exp), Box::new(rhs));
            }
            exp
        }
        _ => return Err(ExecError::Type(format!("smt_value {:?}", &v), info)),
    })
}

// 整数在 SMT 中也表示为位向量；非位向量值由后续结构化合并处理。
pub(crate) fn merge_bit_width<B: BV>(
    value: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<u32>, ExecError> {
    Ok(match value {
        Val::Bits(_) | Val::MixedBits(_) => Some(length_bits(value, solver, info)?),
        Val::I64(_) => Some(64),
        Val::I128(_) => Some(128),
        Val::Symbolic(sym) => solver.length(*sym),
        _ => None,
    })
}

pub fn build_ite<B: BV>(
    b: Sym,
    lhs: &Val<B>,
    rhs: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    build_ite_with(b, lhs, rhs, solver, info, build_ite)
}

fn build_ite_with<B: BV>(
    b: Sym,
    lhs: &Val<B>,
    rhs: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
    merge_payload: fn(Sym, &Val<B>, &Val<B>, &mut Solver<B>, SourceLoc) -> Result<Val<B>, ExecError>,
) -> Result<Val<B>, ExecError> {
    if merge_bit_width(lhs, solver, info)? != merge_bit_width(rhs, solver, info)? {
        return Err(ExecError::IncompatibleMerge);
    }
    if lhs == rhs {
        return Ok(lhs.clone());
    }
    match (lhs, rhs) {
        (Val::Unit, Val::Unit) => Ok(Val::Unit),
        (Val::Vector(lhs), Val::Vector(rhs)) if lhs.len() == rhs.len() => lhs
            .iter()
            .zip(rhs)
            .map(|(l, r)| merge_payload(b, l, r, solver, info))
            .collect::<Result<Vec<_>, _>>()
            .map(Val::Vector),
        (Val::Vector(_), Val::Vector(_))
        | (Val::String(_), Val::String(_))
        | (Val::Ref(_), Val::Ref(_))
        | (Val::List(_), Val::List(_)) => Err(ExecError::NoSymbolicType),
        (Val::Struct(l_fields), Val::Struct(r_fields)) => {
            let fields: Result<_, _> = l_fields
                .iter()
                .map(|(k, l_val)| match r_fields.get(k) {
                    None => Err(ExecError::Type(format!("build_ite {:?}", &k), info)),
                    Some(r_val) => Ok((*k, merge_payload(b, l_val, r_val, solver, info)?)),
                })
                .collect();
            Ok(Val::Struct(fields?))
        }

        (Val::Ctor(l_id, lhs), Val::Ctor(r_id, rhs)) => {
            if l_id == r_id {
                Ok(Val::Ctor(*l_id, Box::new(merge_payload(b, lhs, rhs, solver, info)?)))
            } else {
                use smtlib::Exp::*;
                let sym_id =
                    solver.define_const(Ite(Box::new(Var(b)), Box::new(l_id.to_smt()), Box::new(r_id.to_smt())), info);

                let mut possibilities = HashMap::default();
                possibilities.insert(*l_id, lhs.as_ref().clone());
                possibilities.insert(*r_id, rhs.as_ref().clone());
                Ok(Val::SymbolicCtor(sym_id, possibilities))
            }
        }

        (Val::Ctor(l_id, lhs), Val::SymbolicCtor(r_id, rhs)) => {
            use smtlib::Exp::*;
            let sym_id =
                solver.define_const(Ite(Box::new(Var(b)), Box::new(l_id.to_smt()), Box::new(Var(*r_id))), info);

            let mut possibilities = rhs.clone();
            match possibilities.entry(*l_id) {
                Entry::Occupied(o) => *o.into_mut() = merge_payload(b, lhs, o.get(), solver, info)?,
                Entry::Vacant(v) => {
                    v.insert(lhs.as_ref().clone());
                }
            }

            Ok(Val::SymbolicCtor(sym_id, possibilities))
        }

        (Val::SymbolicCtor(_, _), Val::Ctor(_, _)) => {
            use smtlib::Exp::*;
            let not_b = solver.define_const(Not(Box::new(Var(b))), info);
            build_ite_with(not_b, rhs, lhs, solver, info, merge_payload)
        }

        (Val::SymbolicCtor(l_id, lhs), Val::SymbolicCtor(r_id, rhs)) => {
            use smtlib::Exp::*;
            let sym_id = solver.define_const(Ite(Box::new(Var(b)), Box::new(Var(*l_id)), Box::new(Var(*r_id))), info);

            let mut possibilities = lhs.clone();
            for (ctor, rhs_val) in rhs.iter() {
                match possibilities.entry(*ctor) {
                    Entry::Occupied(o) => *o.into_mut() = merge_payload(b, o.get(), rhs_val, solver, info)?,
                    Entry::Vacant(v) => {
                        v.insert(rhs_val.clone());
                    }
                }
            }

            Ok(Val::SymbolicCtor(sym_id, possibilities))
        }

        _ => {
            let exp = Exp::Ite(Box::new(Exp::Var(b)), Box::new(smt_value(lhs, info)?), Box::new(smt_value(rhs, info)?));
            let is_bits = |value: &Val<B>| match value {
                Val::Bits(_) | Val::MixedBits(_) => true,
                Val::Symbolic(sym) => solver.is_sail_bitvector(*sym),
                _ => false,
            };
            if is_bits(lhs) || is_bits(rhs) {
                solver.define_bitvector(exp, info).into()
            } else {
                solver.define_const(exp, info).into()
            }
        }
    }
}

#[cfg(test)]
mod build_ite_tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::smt::{Config, Context};

    #[test]
    fn different_bit_widths_are_rejected() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let condition = solver.declare_const(smtlib::Ty::Bool, info);
        let values = [
            Val::Bits(B64::new(1, 8)),
            Val::Bits(B64::new(2, 16)),
            Val::Symbolic(solver.declare_const(smtlib::Ty::BitVec(8), info)),
            Val::Symbolic(solver.declare_const(smtlib::Ty::BitVec(16), info)),
            Val::MixedBits(vec![BitsSegment::Concrete(B64::new(1, 8))]),
            Val::MixedBits(vec![BitsSegment::Concrete(B64::new(2, 16))]),
        ];
        for lhs in &values {
            for rhs in &values {
                if length_bits(lhs, &mut solver, info).unwrap() == length_bits(rhs, &mut solver, info).unwrap() {
                    continue;
                }
                assert!(matches!(build_ite(condition, lhs, rhs, &mut solver, info), Err(ExecError::IncompatibleMerge)));
                assert!(matches!(merge_val(condition, lhs, rhs, &mut solver, info), Err(ExecError::IncompatibleMerge)));
            }
        }
        for value in [Val::I64(1), Val::I128(1)] {
            assert!(build_ite(condition, &value, &value, &mut solver, info).is_ok());
            assert!(matches!(
                build_ite(condition, &value, &values[2], &mut solver, info),
                Err(ExecError::IncompatibleMerge)
            ));
        }
    }

    #[test]
    fn matching_ctor_merges_nested_payload() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let condition = solver.declare_const(smtlib::Ty::Bool, SourceLoc::unknown());
        let ctor = Name::from_u32(91);
        let lhs = Val::Ctor(ctor, Box::new(Val::Ctor(ctor, Box::new(Val::Unit))));
        let rhs = lhs.clone();
        assert_eq!(build_ite(condition, &lhs, &rhs, &mut solver, SourceLoc::unknown()).unwrap(), lhs);

        // 路径合流仍拒绝不同整数载荷，通用 ITE 则支持寄存器历史选择。
        let info = SourceLoc::unknown();
        let tag = solver.declare_const(smtlib::Ty::BitVec(32), info);
        let left_payload = Val::I128(8);
        let right_payload = Val::I128(16);
        let left_values = [
            Val::Ctor(ctor, Box::new(left_payload.clone())),
            Val::SymbolicCtor(tag, HashMap::from_iter([(ctor, left_payload)])),
        ];
        let right_values = [
            Val::Ctor(ctor, Box::new(right_payload.clone())),
            Val::SymbolicCtor(tag, HashMap::from_iter([(ctor, right_payload)])),
        ];
        for left in &left_values {
            for right in &right_values {
                assert!(matches!(
                    merge_val(condition, left, right, &mut solver, info),
                    Err(ExecError::IncompatibleMerge)
                ));
                assert!(build_ite(condition, left, right, &mut solver, info).is_ok());
            }
        }

        let mut left_fields = ahash::HashMap::default();
        left_fields.insert(ctor, Val::Unit);
        left_fields.insert(Name::from_u32(92), Val::Bool(false));
        let mut right_fields = ahash::HashMap::default();
        right_fields.insert(ctor, Val::Unit);
        right_fields.insert(Name::from_u32(92), Val::Bool(true));
        let left = Val::Ctor(ctor, Box::new(Val::Struct(left_fields)));
        let right = Val::Ctor(ctor, Box::new(Val::Struct(right_fields)));
        let merged = build_ite(condition, &left, &right, &mut solver, SourceLoc::unknown()).unwrap();
        let Val::Ctor(_, payload) = merged else {
            panic!("必须保持构造子");
        };
        let Val::Struct(fields) = *payload else {
            panic!("必须保持结构载荷");
        };
        assert_eq!(fields.get(&ctor), Some(&Val::Unit));
        assert!(matches!(fields.get(&Name::from_u32(92)), Some(Val::Symbolic(_))));
    }
}

pub fn ite<B: BV>(
    boolean: &Val<B>,
    lhs: &Val<B>,
    rhs: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match boolean {
        Val::Symbolic(b) => build_ite(*b, lhs, rhs, solver, info),
        Val::Bool(true) => Ok(lhs.clone()),
        Val::Bool(false) => Ok(rhs.clone()),
        _ => Err(ExecError::Type(format!("ite {:?} (expected boolean argument)", boolean), info)),
    }
}

pub fn ite_choice<B: BV>(
    v: &Val<B>,
    vs: &[Val<B>],
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if vs.is_empty() {
        Ok(v.clone())
    } else {
        let vr = ite_choice(&vs[0], &vs[1..], solver, info)?;
        let b = solver.declare_const(smtlib::Ty::Bool, info);
        build_ite(b, v, &vr, solver, info)
    }
}

pub fn ite_phi<B: BV>(
    v: &(Sym, Val<B>),
    vs: &[(Sym, Val<B>)],
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if vs.is_empty() {
        Ok(v.1.clone())
    } else {
        let vr = ite_phi(&vs[0], &vs[1..], solver, info)?;
        let b = v.0;
        build_ite(b, &v.1, &vr, solver, info)
    }
}

pub fn symbolic_from_typedefs<B: BV>(
    ty: &Ty<Name>,
    typedefs: Typedefs,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let smt_ty = match ty {
        Ty::Unit => return Ok(Val::Unit),
        Ty::Bits(0) => return Ok(Val::Bits(B::zeros(0))),

        Ty::I64 => smtlib::Ty::BitVec(64),
        Ty::I128 => smtlib::Ty::BitVec(128),
        Ty::Bits(sz) => return solver.declare_bitvector(*sz, info).into(),
        Ty::Bool => smtlib::Ty::Bool,
        Ty::Bit => return solver.declare_bitvector(1, info).into(),

        Ty::Struct(name) => {
            if let Some(field_types) = typedefs.structs.get(name) {
                let field_values = field_types
                    .iter()
                    .map(|(f, ty)| match symbolic_from_typedefs(ty, typedefs, solver, info) {
                        Ok(value) => Ok((*f, value)),
                        Err(error) => Err(error),
                    })
                    .collect::<Result<_, _>>()?;
                return Ok(Val::Struct(field_values));
            } else {
                return Err(ExecError::Unreachable(format!("Struct {:?} does not appear to exist!", name)));
            }
        }

        Ty::Enum(name) => {
            let enum_size = typedefs.enums.get(name).unwrap().len();
            let enum_id = solver.get_enum(*name, enum_size);
            return solver.declare_const(smtlib::Ty::Enum(enum_id), info).into();
        }

        Ty::Union(name) => {
            if let Some(ctor_types) = typedefs.unions.get(name) {
                use smtlib::Exp::*;

                let sym = solver.declare_const(Name::smt_ty(), info);
                let mut name_exp = Bool(false);
                let mut possibilities = HashMap::default();

                for (ctor, ty) in ctor_types {
                    name_exp = Or(Box::new(Eq(Box::new(Var(sym)), Box::new(ctor.to_smt()))), Box::new(name_exp));
                    let value = symbolic_from_typedefs(ty, typedefs, solver, info)?;
                    possibilities.insert(*ctor, value);
                }

                solver.assert(name_exp);
                return Ok(Val::SymbolicCtor(sym, possibilities));
            } else {
                return Err(ExecError::Unreachable(format!("Union {:?} does not appear to exist!", name)));
            }
        }

        Ty::FixedVector(sz, ty) => {
            let values =
                (0..*sz).map(|_| symbolic_from_typedefs(ty, typedefs, solver, info)).collect::<Result<_, _>>()?;
            return Ok(Val::Vector(values));
        }

        Ty::Float(f) => f.to_smt(),
        Ty::RoundingMode => smtlib::Ty::RoundingMode,

        // Some things we just can't represent symbolically, but we can continue in the hope that
        // they never actually get used.
        _ => return Ok(Val::Poison),
    };

    solver.declare_const(smt_ty, info).into()
}

/// Create a Symbolic value of a specified type. Can return a concrete value if the type only
/// permits a single value, such as for the unit type or the zero-length bitvector type (which is
/// ideal because SMT solvers don't allow zero-length bitvectors). Compound types like structs will
/// be a concrete structure with symbolic values for each field. Returns the `NoSymbolicType` error
/// if the type cannot be represented in the SMT solver.
pub fn symbolic<B: BV>(
    ty: &Ty<Name>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    symbolic_from_typedefs(ty, shared_state.typedefs(), solver, info)
}

pub fn merge_val<B: BV>(
    cond: Sym,
    val_a: &Val<B>,
    val_b: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if merge_bit_width(val_a, solver, info)? != merge_bit_width(val_b, solver, info)? {
        return Err(ExecError::IncompatibleMerge);
    }
    match (val_a, val_b) {
        (Val::Bool(_), Val::Bool(_)) | (Val::Bits(_), Val::Bits(_)) | (Val::Enum(_), Val::Enum(_)) => {
            if val_a == val_b {
                Ok(val_a.clone())
            } else {
                build_ite(cond, val_a, val_b, solver, info)
            }
        }

        (Val::Unit, Val::Unit) => Ok(Val::Unit),
        (Val::Poison, Val::Poison) => Ok(Val::Poison),

        (Val::Struct(a_fields), Val::Struct(b_fields)) => {
            if a_fields.len() != b_fields.len() {
                return Err(ExecError::Type("merge_val struct field mismatch".to_string(), info));
            }
            let fields: Result<_, _> = a_fields
                .iter()
                .map(|(field, a_val)| match b_fields.get(field) {
                    Some(b_val) => Ok((*field, merge_val(cond, a_val, b_val, solver, info)?)),
                    None => Err(ExecError::Type(format!("merge_val missing struct field {:?}", field), info)),
                })
                .collect();
            Ok(Val::Struct(fields?))
        }

        (Val::Ctor(a_id, a_val), Val::Ctor(b_id, b_val)) if a_id == b_id => {
            Ok(Val::Ctor(*a_id, Box::new(merge_val(cond, a_val, b_val, solver, info)?)))
        }

        (Val::Ctor(_, _), Val::Ctor(_, _))
        | (Val::Ctor(_, _), Val::SymbolicCtor(_, _))
        | (Val::SymbolicCtor(_, _), Val::Ctor(_, _))
        | (Val::SymbolicCtor(_, _), Val::SymbolicCtor(_, _)) => {
            // Unwrap 无法拆分符号标签的成功与失败路径，必须回滚合流并保留各自的错误域。
            Err(ExecError::IncompatibleMerge)
        }

        (Val::Symbolic(_), _) | (_, Val::Symbolic(_)) => build_ite(cond, val_a, val_b, solver, info),

        // I64 和 I128 都可能用于长度、索引和位宽计算；不同整数必须保留具体值。
        (Val::I64(_), Val::I64(_))
        | (Val::I128(_), Val::I128(_))
        | (Val::MixedBits(_), Val::MixedBits(_))
        | (Val::String(_), Val::String(_))
        | (Val::Ref(_), Val::Ref(_))
        | (Val::Vector(_), Val::Vector(_))
        | (Val::List(_), Val::List(_)) => {
            if val_a == val_b {
                Ok(val_a.clone())
            } else {
                Err(ExecError::IncompatibleMerge)
            }
        }

        _ => {
            if val_a == val_b {
                Ok(val_a.clone())
            } else {
                Err(ExecError::IncompatibleMerge)
            }
        }
    }
}

pub fn merge_val_nary<B: BV>(
    conditions: &[Sym],
    values: &[&Val<B>],
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if values.is_empty() {
        return Err(ExecError::Type("merge_val_nary requires at least one value".to_string(), info));
    }
    if conditions.len() + 1 != values.len() {
        return Err(ExecError::Type("merge_val_nary condition/value length mismatch".to_string(), info));
    }
    if values.iter().all(|value| *value == values[0]) {
        return Ok(values[0].clone());
    }

    if let Some(fields) = merge_struct_fields_nary(conditions, values, solver, info)? {
        return Ok(Val::Struct(fields));
    }

    let mut merged = values[values.len() - 1].clone();
    for index in (0..conditions.len()).rev() {
        merged = merge_val(conditions[index], values[index], &merged, solver, info)?;
    }
    Ok(merged)
}

fn merge_struct_fields_nary<B: BV>(
    conditions: &[Sym],
    values: &[&Val<B>],
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<HashMap<Name, Val<B>, ahash::RandomState>>, ExecError> {
    let mut structs = Vec::with_capacity(values.len());
    for value in values {
        match value {
            Val::Struct(fields) => structs.push(fields),
            _ => return Ok(None),
        }
    }

    let first_fields = structs[0];
    if structs.iter().any(|fields| fields.len() != first_fields.len()) {
        return Err(ExecError::Type("merge_val_nary struct field mismatch".to_string(), info));
    }

    let fields: Result<_, _> = first_fields
        .iter()
        .map(|(field, first_val)| {
            let mut field_values = Vec::with_capacity(structs.len());
            field_values.push(first_val);
            for fields in structs.iter().skip(1) {
                match fields.get(field) {
                    Some(value) => field_values.push(value),
                    None => {
                        return Err(ExecError::Type(format!("merge_val_nary missing struct field {:?}", field), info))
                    }
                }
            }
            Ok((*field, merge_val_nary(conditions, &field_values, solver, info)?))
        })
        .collect();
    Ok(Some(fields?))
}

pub fn merge_bindings_nary<'ir, B: BV>(
    conditions: &[Sym],
    bindings: &[&Bindings<'ir, B>],
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Bindings<'ir, B>, ExecError> {
    if bindings.is_empty() {
        return Ok(HashMap::default());
    }

    let keys = binding_keys(bindings);
    let mut merged = HashMap::default();
    for key in keys {
        let mut values = Vec::with_capacity(bindings.len());
        let mut all_uninit = true;
        let mut uninit = None;

        for binding in bindings {
            match binding.get(&key) {
                Some(UVal::Init(value)) => {
                    all_uninit = false;
                    values.push(value);
                }
                Some(UVal::Uninit(ty)) => uninit = Some(*ty),
                None => return Err(ExecError::Type(format!("merge_bindings_nary missing binding {:?}", key), info)),
            }
        }

        if all_uninit {
            if let Some(ty) = uninit {
                merged.insert(key, UVal::Uninit(ty));
            }
        } else if values.len() == bindings.len() {
            merged.insert(key, UVal::Init(merge_val_nary(conditions, &values, solver, info)?));
        } else {
            return Err(ExecError::Type(format!("merge_bindings_nary mixed init state {:?}", key), info));
        }
    }

    Ok(merged)
}

fn binding_keys<B: BV>(bindings: &[&Bindings<'_, B>]) -> HashSet<Name> {
    let mut keys = HashSet::new();
    for binding in bindings {
        keys.extend(binding.keys().copied());
    }
    keys
}

pub fn merge_register_bindings_nary<'ir, B: BV>(
    conditions: &[Sym],
    reg_bindings: &[&RegisterBindings<'ir, B>],
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<RegisterBindings<'ir, B>, ExecError> {
    if reg_bindings.is_empty() {
        return Ok(RegisterBindings::new());
    }
    if reg_bindings.len() == 1 {
        return Ok((*reg_bindings[0]).clone());
    }
    // 当前值的 ITE 无法保留 relaxed 寄存器的读取语义和历史写入。
    if reg_bindings.iter().any(|regs| regs.iter().any(|(key, _)| regs.is_relaxed(*key) || regs.has_old_writes(*key))) {
        return Err(ExecError::IncompatibleMerge);
    }

    let keys = register_binding_keys(reg_bindings);
    let mut merged = RegisterBindings::new();
    for key in keys {
        let mut values = Vec::with_capacity(reg_bindings.len());
        for regs in reg_bindings {
            match regs.get_last_if_initialized(key) {
                Some(value) => values.push(value),
                None => {
                    return Err(ExecError::Type(
                        format!("merge_register_bindings_nary missing initialized register {:?}", key),
                        info,
                    ))
                }
            }
        }
        merged.insert(key, false, UVal::Init(merge_val_nary(conditions, &values, solver, info)?));
    }

    Ok(merged)
}

fn register_binding_keys<B: BV>(reg_bindings: &[&RegisterBindings<'_, B>]) -> HashSet<Name> {
    let mut keys = HashSet::new();
    for regs in reg_bindings {
        keys.extend(regs.iter().map(|(key, _)| *key));
    }
    keys
}
