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
    Guarded(u32, Box<(Val<B>, Val<B>)>),
    // 保留原型的标签和编号，供读端报告旧缓存中的内部值。
    #[serde(skip_serializing)]
    SymBits {
        data: u32,
        len: u32,
        cap: u32,
    },
}
impl<B> Val<B> {
    pub(super) fn legacy_sym_bits(&self) -> Option<(u32, u32, u32)> {
        match self {
            Val::SymBits { data, len, cap } => Some((*data, *len, *cap)),
            Val::Vector(values) | Val::List(values) => values.iter().find_map(Val::legacy_sym_bits),
            Val::Struct(fields) | Val::SymbolicCtor(_, fields) => {
                fields.iter().find_map(|(_, value)| value.legacy_sym_bits())
            }
            Val::Ctor(_, value) => value.legacy_sym_bits(),
            Val::Guarded(_, values) => values.0.legacy_sym_bits().or_else(|| values.1.legacy_sym_bits()),
            _ => None,
        }
    }
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
            crate::ir::Val::Guarded(guard, values) => {
                let (left, right) = *values;
                Val::Guarded(guard.id, Box::new((left.into(), right.into())))
            }
            crate::ir::Val::SymBits { .. } => panic!("未收束位宽的 SymBits 不能写入路径缓存"),
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
            Val::Guarded(guard, values) => {
                let (left, right) = *values;
                crate::ir::Val::Guarded(crate::smt::Sym::from_u32(guard), Box::new((left.into(), right.into())))
            }
            Val::SymBits { .. } => panic!("版本 7 路径缓存不能包含 SymBits"),
            Val::Poison => crate::ir::Val::Poison,
        }
    }
}

#[cfg(test)]
mod concrete_tests {
    use super::*;
    #[test]
    #[should_panic(expected = "不能写入路径缓存")]
    fn sym_bits_cache_capture_rejects_nested_values() {
        use crate::bitvector::b64::B64;
        use crate::smt::Sym;
        let (data, len) = (Sym::from_u32(7), Sym::from_u32(12));
        let original = crate::ir::Val::<B64>::SymBits { data, len, cap: 4 };
        let _ = Val::from(crate::ir::Val::Vector(vec![crate::ir::Val::List(vec![original])]));
    }

    #[test]
    fn sym_bits_cache_tag_is_read_only_in_both_encodings() {
        use crate::bitvector::b64::B64;
        let json = br#"{"SymBits":{"data":7,"len":12,"cap":4}}"#;
        // 原型在 Guarded 之后追加了 bincode 变体 17。
        let bin = [17u32, 7, 12, 4].into_iter().flat_map(u32::to_le_bytes).collect::<Vec<_>>();
        let legacy = Val::<B64>::SymBits { data: 7, len: 12, cap: 4 };
        assert_eq!(serde_json::from_slice::<Val<B64>>(json).unwrap(), legacy);
        assert_eq!(bincode::deserialize::<Val<B64>>(&bin).unwrap(), legacy);
        assert!(serde_json::to_vec(&legacy).is_err());
        assert!(bincode::serialize(&legacy).is_err());
    }

    #[test]
    fn region_concrete_values_guarded_cache_round_trip() {
        use crate::bitvector::b64::B64;
        let guard = crate::smt::Sym::from_u32(7);
        let original = crate::ir::Val::<B64>::Guarded(
            guard,
            Box::new((crate::ir::Val::String("左".into()), crate::ir::Val::String("右".into()))),
        );
        let dto = Val::from(original.clone());
        for bytes in [serde_json::to_vec(&dto).unwrap(), bincode::serialize(&dto).unwrap()] {
            let restored: Val<B64> = if bytes[0] == b'{' {
                serde_json::from_slice(&bytes).unwrap()
            } else {
                bincode::deserialize(&bytes).unwrap()
            };
            assert_eq!(original, restored.into());
        }
        assert!(original.symbolic_variables().contains(&guard));
    }
}
