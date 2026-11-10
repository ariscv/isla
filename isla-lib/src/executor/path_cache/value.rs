//! 缓存的外部标签镜像；保留所有变体与字段，不改变核心执行类型。
use super::expr::Member;
use crate::ir::Name;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum BitsSegment<B> {
    Symbolic(u32),
    Concrete(B),
}
impl<B> From<crate::ir::BitsSegment<B>> for BitsSegment<B> {
    fn from(value: crate::ir::BitsSegment<B>) -> Self {
        match value {
            crate::ir::BitsSegment::Symbolic(field0) => BitsSegment::Symbolic(field0.id),
            crate::ir::BitsSegment::Concrete(field0) => BitsSegment::Concrete(field0),
        }
    }
}
impl<B> From<BitsSegment<B>> for crate::ir::BitsSegment<B> {
    fn from(value: BitsSegment<B>) -> Self {
        match value {
            BitsSegment::Symbolic(field0) => crate::ir::BitsSegment::Symbolic(crate::smt::Sym::from_u32(field0)),
            BitsSegment::Concrete(field0) => crate::ir::BitsSegment::Concrete(field0),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Val<B> {
    Symbolic(u32),
    I64(i64),
    I128(i128),
    Bool(bool),
    Bits(B),
    MixedBits(Vec<BitsSegment<B>>),
    String(String),
    Unit,
    Vector(Vec<Val<B>>),
    List(Vec<Val<B>>),
    Enum(Member),
    Struct(Vec<(Name, Val<B>)>),
    Ctor(Name, Box<Val<B>>),
    SymbolicCtor(u32, Vec<(Name, Val<B>)>),
    Ref(Name),
    Poison,
}
impl<B> From<crate::ir::Val<B>> for Val<B> {
    fn from(value: crate::ir::Val<B>) -> Self {
        match value {
            crate::ir::Val::Symbolic(field0) => Val::Symbolic(field0.id),
            crate::ir::Val::I64(field0) => Val::I64(field0),
            crate::ir::Val::I128(field0) => Val::I128(field0),
            crate::ir::Val::Bool(field0) => Val::Bool(field0),
            crate::ir::Val::Bits(field0) => Val::Bits(field0),
            crate::ir::Val::MixedBits(field0) => Val::MixedBits(field0.into_iter().map(|item| (item).into()).collect()),
            crate::ir::Val::String(field0) => Val::String(field0),
            crate::ir::Val::Unit => Val::Unit,
            crate::ir::Val::Vector(field0) => Val::Vector(field0.into_iter().map(|item| (item).into()).collect()),
            crate::ir::Val::List(field0) => Val::List(field0.into_iter().map(|item| (item).into()).collect()),
            crate::ir::Val::Enum(field0) => Val::Enum((field0).into()),
            crate::ir::Val::Struct(field0) => Val::Struct({
                let mut fields = field0.into_iter().map(|(key, value)| (key, value.into())).collect::<Vec<_>>();
                fields.sort_by_key(|(key, _)| *key);
                fields
            }),
            crate::ir::Val::Ctor(field0, field1) => Val::Ctor(field0, Box::new((*field1).into())),
            crate::ir::Val::SymbolicCtor(field0, field1) => Val::SymbolicCtor(field0.id, {
                let mut fields = field1.into_iter().map(|(key, value)| (key, value.into())).collect::<Vec<_>>();
                fields.sort_by_key(|(key, _)| *key);
                fields
            }),
            crate::ir::Val::Ref(field0) => Val::Ref(field0),
            crate::ir::Val::Poison => Val::Poison,
        }
    }
}
impl<B> From<Val<B>> for crate::ir::Val<B> {
    fn from(value: Val<B>) -> Self {
        match value {
            Val::Symbolic(field0) => crate::ir::Val::Symbolic(crate::smt::Sym::from_u32(field0)),
            Val::I64(field0) => crate::ir::Val::I64(field0),
            Val::I128(field0) => crate::ir::Val::I128(field0),
            Val::Bool(field0) => crate::ir::Val::Bool(field0),
            Val::Bits(field0) => crate::ir::Val::Bits(field0),
            Val::MixedBits(field0) => crate::ir::Val::MixedBits(field0.into_iter().map(|item| (item).into()).collect()),
            Val::String(field0) => crate::ir::Val::String(field0),
            Val::Unit => crate::ir::Val::Unit,
            Val::Vector(field0) => crate::ir::Val::Vector(field0.into_iter().map(|item| (item).into()).collect()),
            Val::List(field0) => crate::ir::Val::List(field0.into_iter().map(|item| (item).into()).collect()),
            Val::Enum(field0) => crate::ir::Val::Enum((field0).into()),
            Val::Struct(field0) => crate::ir::Val::Struct(
                field0.into_iter().map(|(key, value)| (key, value.into())).collect::<std::collections::HashMap<
                    _,
                    _,
                    ahash::RandomState,
                >>(),
            ),
            Val::Ctor(field0, field1) => crate::ir::Val::Ctor(field0, Box::new((*field1).into())),
            Val::SymbolicCtor(field0, field1) => crate::ir::Val::SymbolicCtor(
                crate::smt::Sym::from_u32(field0),
                field1.into_iter().map(|(key, value)| (key, value.into())).collect::<std::collections::HashMap<
                    _,
                    _,
                    ahash::RandomState,
                >>(),
            ),
            Val::Ref(field0) => crate::ir::Val::Ref(field0),
            Val::Poison => crate::ir::Val::Poison,
        }
    }
}
