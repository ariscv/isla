use crate::bitvector::BV;
use crate::error::ExecError;
use crate::ir::{BitsSegment, Name, SharedState, Val};
use crate::smt::smtlib::{Exp, Ty};
use crate::smt::{EnumMember, Model, ModelVal, Sym};
use crate::source_loc::SourceLoc;
use crate::zencode;

#[derive(Clone, Debug)]
pub struct BitVal {
    bits: Vec<bool>,
    len: usize,
    mask: Vec<bool>,
}

impl BitVal {
    fn new(bits: Vec<bool>, mask: Vec<bool>) -> Self {
        let len = bits.len();
        assert_eq!(mask.len(), len);
        Self { bits, len, mask }
    }

    fn concrete(bits: Vec<bool>) -> Self {
        let len = bits.len();
        Self::new(bits, vec![true; len])
    }

    fn from_bool(bit: bool) -> Self {
        Self::concrete(vec![bit])
    }

    pub fn is_arbitrary(&self) -> bool {
        if self.len == 0 {
            panic!("TODO: 当BitVal的位宽为0");
        }
        self.mask.iter().all(|m| *m == false)
    }

    fn arbitrary(len: u32) -> Self {
        let len = len as usize;
        Self::new(vec![false; len], vec![false; len])
    }

    fn from_bv<B: BV>(bv: B) -> Self {
        let len = bv.len() as usize;
        let bits = (0..len).map(|i| ((bv.lower_u64() >> i) & 1) == 1).collect();
        Self::concrete(bits)
    }

    fn concat(high: Self, low: Self) -> Self {
        let mut bits = low.bits;
        bits.extend(high.bits);
        let mut mask = low.mask;
        mask.extend(high.mask);
        Self::new(bits, mask)
    }

    fn grouped_digits(bits: &[bool], group: usize, one: char, zero: char) -> String {
        fn rec(bits: &[bool], group: usize, one: char, zero: char, out: &mut String) {
            if bits.is_empty() {
                return;
            }
            let take = bits.len() % group;
            let take = if take == 0 { group } else { take };
            let (head, tail) = bits.split_at(bits.len() - take);
            rec(head, group, one, zero, out);
            if !out.is_empty() {
                out.push('_');
            }
            for bit in tail.iter().rev() {
                out.push(if *bit { one } else { zero });
            }
        }

        let mut out = String::new();
        rec(bits, group, one, zero, &mut out);
        out
    }

    fn hex_digits(&self) -> String {
        let hex_len = self.len.div_ceil(4);
        let padded_len = hex_len * 4;
        let mut padded = self.bits.clone();
        padded.resize(padded_len, false);
        let digits: Vec<char> = (0..hex_len)
            .map(|i| {
                let nibble = (0..4).fold(0u8, |acc, j| acc | (u8::from(padded[i * 4 + j]) << j));
                char::from_digit(nibble as u32, 16).unwrap()
            })
            .collect();
        let raw: String = digits.into_iter().rev().collect();

        fn rec(chars: &[char], out: &mut String) {
            if chars.len() <= 4 {
                for ch in chars {
                    out.push(*ch);
                }
            } else {
                rec(&chars[..chars.len() - 4], out);
                out.push('_');
                for ch in &chars[chars.len() - 4..] {
                    out.push(*ch);
                }
            }
        }

        let chars: Vec<char> = raw.chars().collect();
        let mut out = String::new();
        rec(&chars, &mut out);
        out
    }

    fn mask_digits(&self) -> String {
        Self::grouped_digits(&self.mask, 4, '1', '0')
    }

    fn to_str(&self) -> String {
        let value = format!("{}'h{}", self.len, self.hex_digits());
        if self.mask.iter().all(|bit| *bit) {
            value
        } else {
            format!("{{{}, {}'b{}}}", value, self.len, self.mask_digits())
        }
    }
}

#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum FmtVal {
    Bits(BitVal),
    Enum(EnumMember),
}

// Convert concrete/model values into a uniform formatted representation.
impl FmtVal {
    fn from_bv<B: BV>(bv: B) -> Self {
        Self::Bits(BitVal::from_bv(bv))
    }

    fn from_bool(bit: bool) -> Self {
        Self::Bits(BitVal::from_bool(bit))
    }

    fn concat_bits(high: Option<Self>, low: Option<Self>) -> Option<Self> {
        match (high, low) {
            (Some(FmtVal::Bits(high)), Some(FmtVal::Bits(low))) => Some(FmtVal::Bits(BitVal::concat(high, low))),
            (Some(value), None) => Some(value),
            _ => None,
        }
    }

    fn from_segments<B: BV>(segments: &[BitsSegment<B>], model: &mut Model<'_, B>) -> Result<Option<Self>, ExecError> {
        let Some((head, tail)) = segments.split_first() else {
            return Ok(None);
        };

        let head = match head {
            BitsSegment::Concrete(bv) => Some(Self::from_bv(*bv)),
            BitsSegment::Symbolic(sym) => Self::from_model_val(&model.get_var(*sym)?),
        };
        let tail = Self::from_segments(tail, model)?;
        Ok(Self::concat_bits(head, tail))
    }

    fn from_single_field_struct<B: BV>(
        fields: &std::collections::HashMap<Name, Val<B>, ahash::RandomState>,
        model: &mut Model<'_, B>,
    ) -> Result<Option<Self>, ExecError> {
        if fields.len() != 1 {
            return Ok(None);
        }

        fields.values().next().map(|field| Self::from_val(field, model)).transpose()
    }

    pub fn from_exp(exp: &Exp<Sym>) -> Option<Self> {
        match exp {
            Exp::Bits(bits) => Some(FmtVal::Bits(BitVal::concrete(bits.clone()))),
            Exp::Bits64(bv) => Some(Self::from_bv(*bv)),
            Exp::Enum(member) => Some(FmtVal::Enum(*member)),
            Exp::Bool(bit) => Some(Self::from_bool(*bit)),
            _ => None,
        }
    }

    pub fn from_model_val(model_val: &ModelVal) -> Option<Self> {
        match model_val {
            ModelVal::Exp(exp) => Self::from_exp(exp),
            ModelVal::Arbitrary(Ty::BitVec(len)) => Some(FmtVal::Bits(BitVal::arbitrary(*len))),
            ModelVal::Arbitrary(Ty::Bool) => Some(FmtVal::Bits(BitVal::arbitrary(1))),
            _ => None,
        }
    }

    pub fn from_val<B: BV>(val: &Val<B>, model: &mut Model<'_, B>) -> Result<Self, ExecError> {
        let fmt_val = match val {
            Val::Symbolic(sym) => Self::from_model_val(&model.get_var(*sym)?),
            Val::Bits(bv) => Some(Self::from_bv(*bv)),
            Val::Bool(bit) => Some(Self::from_bool(*bit)),
            Val::Enum(member) => Some(FmtVal::Enum(*member)),
            Val::MixedBits(segments) => Self::from_segments(segments, model)?,
            Val::Struct(fields) => Self::from_single_field_struct(fields, model)?,
            Val::Ctor(_, inner) => Some(Self::from_val(inner, model)?),
            _ => None,
        };

        fmt_val
            .ok_or_else(|| ExecError::Type(format!("Cannot convert value to FmtVal: {:?}", val), SourceLoc::unknown()))
    }

    pub fn to_str<B: BV>(&self, shared_state: &SharedState<B>) -> String {
        match self {
            FmtVal::Bits(bit_val) => bit_val.to_str(),
            FmtVal::Enum(member) => zencode::decode(shared_state.symtab.to_str(member.to_name(shared_state))),
        }
    }

    pub fn is_arbitrary(&self) -> bool {
        match self {
            FmtVal::Bits(bit_val) => bit_val.is_arbitrary(),
            FmtVal::Enum(_) => false,
        }
    }
}

impl ModelVal {
    pub fn to_str(&self) -> String {
        FmtVal::from_model_val(self)
            .map(|fmt_val| match fmt_val {
                FmtVal::Bits(bit_val) => bit_val.to_str(),
                FmtVal::Enum(member) => format!("{:?}", member),
            })
            .unwrap_or_else(|| format!("{:?}", self))
    }
}

impl<'ctx, B: BV> Model<'ctx, B> {
    pub fn get_fmtval(&mut self, val: &Val<B>) -> Result<FmtVal, ExecError> {
        FmtVal::from_val(val, self)
    }
}
