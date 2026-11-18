//! 缓存的外部标签镜像；保留所有变体与字段，不改变核心执行类型。
use super::{expr::*, value::*};
use crate::{ir::Name, smt::Accessor, source_loc::SourceLoc};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Event<B> {
    Smt(Def, DefAttrs, SourceLoc),
    Fork(u64, u32, u32, SourceLoc),
    Merge(u32, u64, SourceLoc),
    Function {
        name: Name,
        call: bool,
    },
    Abstract {
        name: Name,
        primitive: bool,
        args: Vec<Val<B>>,
        return_value: Val<B>,
    },
    ReadReg(Name, Vec<Accessor>, Val<B>),
    WriteReg(Name, Vec<Accessor>, Val<B>),
    AssumeReg(Name, Vec<Accessor>, Val<B>),
    ReadMem {
        value: Val<B>,
        read_kind: Val<B>,
        address: Val<B>,
        bytes: u32,
        tag_value: Option<Val<B>>,
        opts: ReadOpts,
        region: String,
    },
    WriteMem {
        value: u32,
        write_kind: Val<B>,
        address: Val<B>,
        data: Val<B>,
        bytes: u32,
        tag_value: Option<Val<B>>,
        opts: WriteOpts,
        region: String,
    },
    MarkReg {
        regs: Vec<Name>,
        mark: String,
    },
    AddressAnnounce {
        address: Val<B>,
    },
    Branch {
        address: Val<B>,
    },
    Cycle,
    Instr(Val<B>),
    Assume(AssumeExp),
    AssumeFun {
        name: Name,
        args: Vec<Val<B>>,
        return_value: Val<B>,
    },
    UseFunAssumption {
        name: Name,
        args: Vec<Val<B>>,
        return_value: Val<B>,
    },
}
impl<B> From<crate::smt::Event<B>> for Event<B> {
    fn from(value: crate::smt::Event<B>) -> Self {
        match value {
            crate::smt::Event::Smt(field0, field1, field2) => Event::Smt((field0).into(), (field1).into(), field2),
            crate::smt::Event::Fork(field0, field1, field2, field3) => Event::Fork(field0, field1.id, field2, field3),
            crate::smt::Event::Merge(field0, field1, field2) => {
                Event::Merge(field0, field1.try_into().expect("缓存索引越界"), field2)
            }
            crate::smt::Event::Function { name, call } => Event::Function { name: name, call: call },
            crate::smt::Event::Abstract { name, primitive, args, return_value } => Event::Abstract {
                name: name,
                primitive: primitive,
                args: args.into_iter().map(|item| (item).into()).collect(),
                return_value: (return_value).into(),
            },
            crate::smt::Event::ReadReg(field0, field1, field2) => {
                Event::ReadReg(field0, field1.into_iter().map(|item| item).collect(), (field2).into())
            }
            crate::smt::Event::WriteReg(field0, field1, field2) => {
                Event::WriteReg(field0, field1.into_iter().map(|item| item).collect(), (field2).into())
            }
            crate::smt::Event::AssumeReg(field0, field1, field2) => {
                Event::AssumeReg(field0, field1.into_iter().map(|item| item).collect(), (field2).into())
            }
            crate::smt::Event::ReadMem { value, read_kind, address, bytes, tag_value, opts, region } => {
                Event::ReadMem {
                    value: (value).into(),
                    read_kind: (read_kind).into(),
                    address: (address).into(),
                    bytes: bytes,
                    tag_value: tag_value.map(|item| (item).into()),
                    opts: (opts).into(),
                    region: region.to_owned(),
                }
            }
            crate::smt::Event::WriteMem { value, write_kind, address, data, bytes, tag_value, opts, region } => {
                Event::WriteMem {
                    value: value.id,
                    write_kind: (write_kind).into(),
                    address: (address).into(),
                    data: (data).into(),
                    bytes: bytes,
                    tag_value: tag_value.map(|item| (item).into()),
                    opts: (opts).into(),
                    region: region.to_owned(),
                }
            }
            crate::smt::Event::MarkReg { regs, mark } => {
                Event::MarkReg { regs: regs.into_iter().map(|item| item).collect(), mark: mark }
            }
            crate::smt::Event::AddressAnnounce { address } => Event::AddressAnnounce { address: (address).into() },
            crate::smt::Event::Branch { address } => Event::Branch { address: (address).into() },
            crate::smt::Event::Cycle => Event::Cycle,
            crate::smt::Event::Instr(field0) => Event::Instr((field0).into()),
            crate::smt::Event::Assume(field0) => Event::Assume((field0).into()),
            crate::smt::Event::AssumeFun { name, args, return_value } => Event::AssumeFun {
                name: name,
                args: args.into_iter().map(|item| (item).into()).collect(),
                return_value: (return_value).into(),
            },
            crate::smt::Event::UseFunAssumption { name, args, return_value } => Event::UseFunAssumption {
                name: name,
                args: args.into_iter().map(|item| (item).into()).collect(),
                return_value: (return_value).into(),
            },
        }
    }
}
impl<B> From<Event<B>> for crate::smt::Event<B> {
    fn from(value: Event<B>) -> Self {
        match value {
            Event::Smt(field0, field1, field2) => crate::smt::Event::Smt((field0).into(), (field1).into(), field2),
            Event::Fork(field0, field1, field2, field3) => {
                crate::smt::Event::Fork(field0, crate::smt::Sym::from_u32(field1), field2, field3)
            }
            Event::Merge(field0, field1, field2) => {
                crate::smt::Event::Merge(field0, field1.try_into().expect("缓存索引越界"), field2)
            }
            Event::Function { name, call } => crate::smt::Event::Function { name: name, call: call },
            Event::Abstract { name, primitive, args, return_value } => crate::smt::Event::Abstract {
                name: name,
                primitive: primitive,
                args: args.into_iter().map(|item| (item).into()).collect(),
                return_value: (return_value).into(),
            },
            Event::ReadReg(field0, field1, field2) => {
                crate::smt::Event::ReadReg(field0, field1.into_iter().map(|item| item).collect(), (field2).into())
            }
            Event::WriteReg(field0, field1, field2) => {
                crate::smt::Event::WriteReg(field0, field1.into_iter().map(|item| item).collect(), (field2).into())
            }
            Event::AssumeReg(field0, field1, field2) => {
                crate::smt::Event::AssumeReg(field0, field1.into_iter().map(|item| item).collect(), (field2).into())
            }
            Event::ReadMem { value, read_kind, address, bytes, tag_value, opts, region } => {
                crate::smt::Event::ReadMem {
                    value: (value).into(),
                    read_kind: (read_kind).into(),
                    address: (address).into(),
                    bytes: bytes,
                    tag_value: tag_value.map(|item| (item).into()),
                    opts: (opts).into(),
                    region: super::intern_region(region),
                }
            }
            Event::WriteMem { value, write_kind, address, data, bytes, tag_value, opts, region } => {
                crate::smt::Event::WriteMem {
                    value: crate::smt::Sym::from_u32(value),
                    write_kind: (write_kind).into(),
                    address: (address).into(),
                    data: (data).into(),
                    bytes: bytes,
                    tag_value: tag_value.map(|item| (item).into()),
                    opts: (opts).into(),
                    region: super::intern_region(region),
                }
            }
            Event::MarkReg { regs, mark } => {
                crate::smt::Event::MarkReg { regs: regs.into_iter().map(|item| item).collect(), mark: mark }
            }
            Event::AddressAnnounce { address } => crate::smt::Event::AddressAnnounce { address: (address).into() },
            Event::Branch { address } => crate::smt::Event::Branch { address: (address).into() },
            Event::Cycle => crate::smt::Event::Cycle,
            Event::Instr(field0) => crate::smt::Event::Instr((field0).into()),
            Event::Assume(field0) => crate::smt::Event::Assume((field0).into()),
            Event::AssumeFun { name, args, return_value } => crate::smt::Event::AssumeFun {
                name: name,
                args: args.into_iter().map(|item| (item).into()).collect(),
                return_value: (return_value).into(),
            },
            Event::UseFunAssumption { name, args, return_value } => crate::smt::Event::UseFunAssumption {
                name: name,
                args: args.into_iter().map(|item| (item).into()).collect(),
                return_value: (return_value).into(),
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum RegionPoint {
    Instruction(u64),
    FunctionExit,
}
impl From<crate::ir::regions::RegionPoint> for RegionPoint {
    fn from(value: crate::ir::regions::RegionPoint) -> Self {
        match value {
            crate::ir::regions::RegionPoint::Instruction(field0) => {
                RegionPoint::Instruction(field0.try_into().expect("缓存索引越界"))
            }
            crate::ir::regions::RegionPoint::FunctionExit => RegionPoint::FunctionExit,
        }
    }
}
impl From<RegionPoint> for crate::ir::regions::RegionPoint {
    fn from(value: RegionPoint) -> Self {
        match value {
            RegionPoint::Instruction(field0) => {
                crate::ir::regions::RegionPoint::Instruction(field0.try_into().expect("缓存索引越界"))
            }
            RegionPoint::FunctionExit => crate::ir::regions::RegionPoint::FunctionExit,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct DefAttrs {
    pub bits: u8,
}
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ReadOpts {
    pub is_exclusive: bool,
    pub is_ifetch: bool,
}
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct WriteOpts {
    pub is_exclusive: bool,
}
