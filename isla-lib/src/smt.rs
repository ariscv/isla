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

//! This module defines an interface with the SMT solver, primarily
//! via the [Solver] type. It provides a safe abstraction over the
//! [z3_sys] crate. In addition, all the interaction with the SMT
//! solver is logged as a [Trace] in an SMTLIB-like format, expanded
//! with additional events marking e.g. memory events, the start and
//! end of processor cycles, etc (see the [Event] type). Points in
//! these traces can be snapshotted and shared between threads via the
//! [Checkpoint] type.
//!
//! Z3 timeout wrapper 集中在 `smt::z3_timeout`，本文件只保留调用点。

use ahash;
use libc::c_uint;
use serde::{Deserialize, Serialize};

#[cfg(feature = "smtperf")]
use petgraph::{
    graph::{Graph, NodeIndex},
    visit::Dfs,
    Directed,
};

use z3_sys::*;

use std::time::{Duration, Instant};

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::convert::TryInto;
use std::error::Error as StdError;
use std::ffi::{CStr, CString};
use std::fmt;
use std::io::Write;
use std::mem;
use std::path::Path;
use std::ptr;
use std::sync::{Arc, OnceLock};

use crate::bitvector::BV;
use crate::error::{ExecError, SmtError, Z3QueryFailure, Z3Timeout};
use crate::executor::stats::region_progress::{WorkKind, WorkTimer};
use crate::ir::{Loc, Name, Symtab, Val};
use crate::source_loc::SourceLoc;
use crate::timeout::SmtOperation;
use crate::zencode;
use crate::{bitvector::b64::B64, ir::SharedState};

/// A newtype wrapper for symbolic variables, which are `u32` under
/// the hood.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Sym {
    pub(crate) id: u32,
}

impl Sym {
    pub fn from_u32(id: u32) -> Self {
        Sym { id }
    }

    pub fn as_u32(self) -> u32 {
        self.id
    }
}

/// 跨 Context 导入远端区域臂时使用的确定性 alpha 重命名。
///
/// 未列出的符号属于入口前缀，保持原编号；列出的符号必须只映射一次，重复或
/// 目标冲突都是协议错误。
#[derive(Clone, Debug, Default)]
pub struct SymRemap {
    symbols: HashMap<Sym, Sym>,
}

impl SymRemap {
    pub fn from_pairs(pairs: impl IntoIterator<Item = (Sym, Sym)>) -> Self {
        let mut symbols = HashMap::new();
        let mut targets = HashSet::new();
        for (from, to) in pairs {
            assert!(symbols.insert(from, to).is_none(), "同一远端符号不得重复重命名");
            assert!(targets.insert(to), "两个远端符号不得映射到同一目标符号");
        }
        Self { symbols }
    }

    pub fn for_region_arms<R: Ord, A: Ord>(first_target: Sym, mut arms: Vec<(R, A, Vec<Sym>)>) -> Self {
        arms.sort_by(|(region_a, arm_a, _), (region_b, arm_b, _)| (region_a, arm_a).cmp(&(region_b, arm_b)));
        let mut next = first_target.id;
        let mut pairs = Vec::new();
        for (_, _, symbols) in arms {
            let mut previous: Option<Sym> = None;
            for source in symbols {
                assert!(previous.is_none_or(|prior| prior.id < source.id), "逻辑臂内符号必须按创建次序严格递增");
                previous = Some(source);
                let target = Sym::from_u32(next);
                next = next.checked_add(1).expect("区域臂符号编号溢出");
                pairs.push((source, target));
            }
        }
        Self::from_pairs(pairs)
    }

    pub fn get(&self, symbol: Sym) -> Sym {
        self.symbols.get(&symbol).copied().unwrap_or(symbol)
    }

    pub fn exp(&self, exp: &smtlib::Exp<Sym>) -> smtlib::Exp<Sym> {
        let mut mapped = exp.clone();
        mapped.modify(&mut |term| {
            if let smtlib::Exp::Var(symbol) | smtlib::Exp::App(symbol, _) = term {
                *symbol = self.get(*symbol);
            }
        });
        mapped
    }

    pub fn def(&self, definition: &smtlib::Def) -> smtlib::Def {
        use smtlib::Def;
        match definition {
            Def::DeclareConst(symbol, ty) => Def::DeclareConst(self.get(*symbol), ty.clone()),
            Def::DeclareFun(symbol, args, result) => Def::DeclareFun(self.get(*symbol), args.clone(), result.clone()),
            Def::DefineConst(symbol, exp) => Def::DefineConst(self.get(*symbol), self.exp(exp)),
            Def::DefineEnum(name, members) => Def::DefineEnum(*name, *members),
            Def::Assert(exp) => Def::Assert(self.exp(exp)),
        }
    }

    pub fn event<B: BV>(&self, event: &Event<B>) -> Event<B> {
        use Event::*;
        match event {
            Smt(definition, attributes, location) => Smt(self.def(definition), *attributes, *location),
            Fork(id, condition, branch, location) => Fork(*id, self.get(*condition), *branch, *location),
            Merge(id, paths, location) => Merge(*id, *paths, *location),
            Function { name, call } => Function { name: *name, call: *call },
            Abstract { name, primitive, args, return_value } => Abstract {
                name: *name,
                primitive: *primitive,
                args: args.iter().map(|value| value.remap_symbols(self)).collect(),
                return_value: return_value.remap_symbols(self),
            },
            ReadReg(name, accessors, value) => ReadReg(*name, accessors.clone(), value.remap_symbols(self)),
            WriteReg(name, accessors, value) => WriteReg(*name, accessors.clone(), value.remap_symbols(self)),
            AssumeReg(name, accessors, value) => AssumeReg(*name, accessors.clone(), value.remap_symbols(self)),
            ReadMem { value, read_kind, address, bytes, tag_value, opts, region } => ReadMem {
                value: value.remap_symbols(self),
                read_kind: read_kind.remap_symbols(self),
                address: address.remap_symbols(self),
                bytes: *bytes,
                tag_value: tag_value.as_ref().map(|value| value.remap_symbols(self)),
                opts: opts.clone(),
                region,
            },
            WriteMem { value, write_kind, address, data, bytes, tag_value, opts, region } => WriteMem {
                value: self.get(*value),
                write_kind: write_kind.remap_symbols(self),
                address: address.remap_symbols(self),
                data: data.remap_symbols(self),
                bytes: *bytes,
                tag_value: tag_value.as_ref().map(|value| value.remap_symbols(self)),
                opts: opts.clone(),
                region,
            },
            MarkReg { regs, mark } => MarkReg { regs: regs.clone(), mark: mark.clone() },
            AddressAnnounce { address } => AddressAnnounce { address: address.remap_symbols(self) },
            Branch { address } => Branch { address: address.remap_symbols(self) },
            Cycle => Cycle,
            Instr(value) => Instr(value.remap_symbols(self)),
            Assume(exp) => Assume(exp.clone()),
            AssumeFun { name, args, return_value } => AssumeFun {
                name: *name,
                args: args.iter().map(|value| value.remap_symbols(self)).collect(),
                return_value: return_value.remap_symbols(self),
            },
            UseFunAssumption { name, args, return_value } => UseFunAssumption {
                name: *name,
                args: args.iter().map(|value| value.remap_symbols(self)).collect(),
                return_value: return_value.remap_symbols(self),
            },
        }
    }
}

impl<B> From<Sym> for Result<Val<B>, ExecError> {
    fn from(sym: Sym) -> Self {
        Ok(Val::Symbolic(sym))
    }
}

impl fmt::Display for Sym {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.id)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct EnumId {
    id: Name,
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct EnumMember {
    pub enum_id: EnumId,
    pub member: usize,
}

impl EnumId {
    pub fn to_name(self) -> Name {
        self.id
    }

    /// Note that this function will not allocate a Z3 enumeration, so use with care
    pub fn from_name(id: Name) -> EnumId {
        EnumId { id }
    }

    pub fn first_member(self) -> EnumMember {
        EnumMember { enum_id: self, member: 0 }
    }
}

impl EnumMember {
    /// 从成员序号获取对应的符号表名称
    ///
    /// 返回枚举成员在符号表(symtab/type_info都可以，效果是一样的)中的 `Name`
    ///
    /// # 参数
    /// * `type_info` - 包含枚举类型信息的 `IRTypeInfo`
    ///
    /// # 返回
    /// * `Some(Name)` - 如果找到对应的枚举和成员
    /// * `None` - 如果枚举不存在或成员序号越界
    pub fn to_name<B>(&self, shared_state: &SharedState<B>) -> Name {
        shared_state
            .type_info
            .enums
            .get(&self.enum_id.to_name())
            .and_then(|members| members.get(self.member).copied())
            .unwrap_or_else(|| panic!("Can't find in typeinfo: {:?}", self))
    }

    /// 从符号表名称获取对应的枚举成员
    ///
    /// 返回 `EnumMember`，这是 `to_name` 的反向操作
    ///
    /// # 参数
    /// * `member_name` - 枚举成员在符号表中的 `Name`
    /// * `shared_state` - 包含类型信息的共享状态
    ///
    /// # 返回
    /// * `Some(EnumMember)` - 如果找到对应的枚举成员
    /// * `None` - 如果该名称不是任何枚举的成员
    pub fn from_name<B: BV>(member_name: Name, shared_state: &SharedState<B>) -> Self {
        shared_state
            .type_info
            .enum_members
            .get(&member_name)
            .map(|&(member, _, enum_name)| EnumMember { enum_id: EnumId::from_name(enum_name), member })
            .unwrap_or_else(|| {
                panic!("Can't find '{}' in typeinfo: {:?}", member_name.to_str(&shared_state), member_name)
            })
    }
}

impl fmt::Debug for EnumMember {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // 尝试从全局 SharedState 获取 Symtab 来解析名称
        if let Some(shared_state) = crate::ir::get_global_shared_state::<u32>() {
            let name = self.to_name(shared_state);
            let name_str: &str = &format!("{}|{}", &self.member, shared_state.symtab.to_str(name));
            // let name_str = zencode::decode(name_str);
            f.debug_struct("EnumMember").field("enum_id", &self.enum_id).field("member", &name_str).finish()
        } else {
            // 如果没有设置全局 SharedState，只显示 enum_id 和 member
            f.debug_struct("EnumMember").field("enum_id", &self.enum_id).field("member", &self.member).finish()
        }
    }
}
mod dump;
mod error_snapshot;
mod logical_arm;
mod proof_budget;
mod transaction;
mod witness;
mod witness_shadow;
pub(crate) use logical_arm::LogicalArm;
pub use transaction::SolverTransaction;
use transaction::{DeclarationUndo, SolverSavepoint};
pub use witness::WitnessRandomization;
mod dependencies;
pub mod smtlib;
mod tactic;
pub use tactic::Tactic;
mod dedup;
mod deferred_assertions;
pub(crate) use deferred_assertions::DeferredArmAssertions;
#[cfg(test)]
pub(crate) use deferred_assertions::{reset_test_mandatory_query_count, test_mandatory_query_count};
mod finite_domain;
pub(crate) use finite_domain::ArrivalFactSummary;
pub(crate) use finite_domain::{FiniteDomain, OperandBounds, ScalarChoice, ScalarLayout};
mod arm_error_replay;
pub mod no_smt;
mod query;
pub(crate) use query::ArmErrorQueries;
mod z3_timeout;
mod z3_version;
pub use dump::configure_slow_query_dump;
use dump::{timeout_dump_from_checkpoint, SmtDumpRequest, Z3SymbolNamer};
use smtlib::*;
use z3_timeout::{
    timeout_Z3_model_eval, timeout_Z3_solver_check, timeout_Z3_solver_check_assumptions,
    timeout_Z3_solver_check_deadline, timeout_error as z3_timeout_error, Z3TimeoutError,
};
use z3_version::MIN_Z3_VERSION;

/// Snapshot of interaction with underlying solver that can be
/// efficiently cloned and shared between threads.
#[derive(Clone, Default)]
pub struct Checkpoint<B> {
    num: usize,
    next_var: u32,
    trace: Arc<Option<Trace<B>>>,
    cycles: i128,
}

impl<B> Checkpoint<B> {
    pub fn new() -> Self {
        Checkpoint { num: 0, next_var: 0, trace: Arc::new(None), cycles: 0 }
    }

    pub fn trace(&self) -> &Option<Trace<B>> {
        &self.trace
    }
}

impl<B: BV> Checkpoint<B> {
    /// 辅助编码仅保留由指令字段和常量定义得到的原路径断言。
    pub fn with_instruction_assertions(&self, instruction: &Val<B>) -> Self {
        fn only_instruction_symbols(exp: &mut Exp<Sym>, pure_symbols: &HashSet<Sym>) -> bool {
            let mut pure = true;
            exp.modify(&mut |part| match part {
                Exp::Var(sym) if !pure_symbols.contains(sym) => pure = false,
                Exp::App(_, _) => pure = false,
                _ => (),
            });
            pure
        }

        let inputs = instruction.symbolic_variables();
        let mut pure_symbols = HashSet::new();
        let mut events = Vec::new();
        let mut event_guards = Vec::new();
        if let Some(trace) = self.trace.as_ref().as_ref() {
            let events_with_guards: Vec<_> = trace.events_with_guards_rev().collect();
            for (event, guard) in events_with_guards.into_iter().rev() {
                let mut event = event.clone();
                let keep = match &mut event {
                    Event::Smt(Def::DeclareConst(sym, _), _, _) => {
                        if inputs.contains(sym) {
                            pure_symbols.insert(*sym);
                        }
                        true
                    }
                    Event::Smt(Def::DefineConst(sym, exp), _, _) => {
                        pure_symbols.remove(sym);
                        if only_instruction_symbols(exp, &pure_symbols) {
                            pure_symbols.insert(*sym);
                        }
                        true
                    }
                    Event::Smt(Def::Assert(exp), _, _) => only_instruction_symbols(exp, &pure_symbols),
                    _ => true,
                };
                if keep {
                    if let Some(guard) = guard {
                        event_guards.push((events.len(), guard.clone()));
                    }
                    events.push(event);
                }
            }
        }
        Checkpoint {
            num: 1,
            next_var: self.next_var,
            trace: Arc::new(Some(Trace {
                checkpoints: 0,
                head: events,
                event_guards,
                head_prefix: None,
                projected: None,
                tail: Arc::new(None),
            })),
            cycles: 0,
        }
    }

    /// 将辅助 checkpoint 从 base 开始新增的事件接到完整执行 checkpoint。
    pub fn with_suffix_from(&self, base: &Self, candidate: &Self) -> Self {
        assert_eq!(self.next_var, base.next_var, "执行与辅助基点的符号编号不一致");
        assert!(candidate.next_var >= base.next_var, "候选符号编号回退");
        assert!(candidate.num >= base.num, "候选 checkpoint 早于辅助基点");
        let mut suffix = Vec::with_capacity(candidate.num - base.num);
        let mut cursor = candidate.trace.clone();
        while !Arc::ptr_eq(&cursor, &base.trace) {
            let segment = cursor.as_ref().as_ref().expect("候选 checkpoint 缺少辅助基点祖先");
            suffix.push((
                segment.head.clone(),
                segment.event_guards.clone(),
                segment.head_prefix.clone(),
                segment.projected.clone(),
            ));
            cursor = segment.tail.clone();
        }
        assert_eq!(suffix.len(), candidate.num - base.num, "候选 checkpoint 链长度不一致");
        let mut trace = self.trace.clone();
        let mut num = self.num;
        for (head, event_guards, head_prefix, projected) in suffix.into_iter().rev() {
            trace = Arc::new(Some(Trace { checkpoints: num, head, event_guards, head_prefix, projected, tail: trace }));
            num += 1;
        }
        Checkpoint { num, next_var: candidate.next_var, trace, cycles: candidate.cycles }
    }
}

/// For the concurrency models, register accesses must be logged at a
/// subfield level granularity (e.g. for PSTATE in ARM ASL), which is
/// what the Accessor type is for.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub enum Accessor {
    Field(Name),
}

impl Accessor {
    pub fn to_string(&self, symtab: &Symtab) -> String {
        match self {
            Accessor::Field(name) => format!("(_ field |{}|)", zencode::decode(symtab.to_str(*name))),
        }
    }

    pub fn pretty(&self, buf: &mut dyn Write, symtab: &Symtab) -> Result<(), Box<dyn StdError>> {
        match self {
            Accessor::Field(name) => write!(buf, ".{}", zencode::decode(symtab.to_str(*name)))?,
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Default)]
pub struct ReadOpts {
    pub is_exclusive: bool,
    pub is_ifetch: bool,
}

impl ReadOpts {
    pub fn ifetch() -> Self {
        ReadOpts { is_exclusive: false, is_ifetch: true }
    }

    pub fn exclusive() -> Self {
        ReadOpts { is_exclusive: true, is_ifetch: false }
    }
}

#[derive(Clone, Debug, Default)]
pub struct WriteOpts {
    is_exclusive: bool,
}

impl WriteOpts {
    pub fn exclusive() -> Self {
        WriteOpts { is_exclusive: true }
    }

    pub fn is_exclusive(&self) -> bool {
        self.is_exclusive
    }
}

#[derive(Copy, Clone, Debug, Default)]
pub struct DefAttrs {
    attrs: u8,
}

impl DefAttrs {
    /// An 'uninteresting' definition in the trace is one that is
    /// entirely determined by some other construct. For example, the
    /// `read_register_from_vector` construct constructs SMT to pick
    /// the required register value, but this SMT is always generated
    /// in the same way from information encoded in the `Abstract`
    /// trace element. This is used for presentation, as such elements
    /// can be hidden to give a more concise view of the trace.
    pub fn uninteresting() -> Self {
        DefAttrs { attrs: 1 }
    }

    /// 标记 Sail 位向量，区分同样编码为 BV128 的有符号整数。
    fn sail_bitvector(self) -> Self {
        DefAttrs { attrs: self.attrs | 2 }
    }

    pub fn is_uninteresting(self) -> bool {
        self.attrs & 1 > 0
    }
}

#[derive(Clone, Debug)]
pub enum Event<B> {
    Smt(Def, DefAttrs, SourceLoc),
    /// Fork ID, assertion, branch number, source location
    Fork(u64, Sym, u32, SourceLoc),
    /// Fork group ID, number of merged paths, source location
    Merge(u32, usize, SourceLoc),
    /// Used to delimit function calls and returns in the trace
    Function {
        name: Name,
        /// True for call, false for return
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
        region: &'static str,
    },
    WriteMem {
        value: Sym,
        write_kind: Val<B>,
        address: Val<B>,
        data: Val<B>,
        bytes: u32,
        tag_value: Option<Val<B>>,
        opts: WriteOpts,
        region: &'static str,
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
    Assume(Exp<Loc<String>>),
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

/// 远端区域臂交付的一个事务后缀事件。读取投影序号不属于 `Event` 本身，
/// 因而必须与事件一同移交，不能在 A 侧按到达顺序重新猜测。
#[derive(Clone, Debug)]
pub(crate) struct ArmSuffixEvent<B> {
    pub(crate) guard: Option<Exp<Sym>>,
    pub(crate) event: Event<B>,
    pub(crate) register_read_occurrence: Option<usize>,
    pub(crate) cycle: bool,
}

impl<B: BV> Event<B> {
    pub fn defines(&self) -> Option<Sym> {
        match self {
            Event::Smt(Def::DeclareConst(v, _), _, _) => Some(*v),
            Event::Smt(Def::DeclareFun(v, _, _), _, _) => Some(*v),
            Event::Smt(Def::DefineConst(v, _), _, _) => Some(*v),
            _ => None,
        }
    }

    pub fn collect_memory_symbolic_variables(&self, vars: &mut HashSet<Sym, ahash::RandomState>) {
        match self {
            Event::ReadMem { value, read_kind, address, tag_value, .. } => {
                value.collect_symbolic_variables(vars);
                read_kind.collect_symbolic_variables(vars);
                address.collect_symbolic_variables(vars);
                if let Some(tag_value) = tag_value {
                    tag_value.collect_symbolic_variables(vars)
                }
            }
            Event::WriteMem { value, write_kind, address, data, tag_value, .. } => {
                vars.insert(*value);
                write_kind.collect_symbolic_variables(vars);
                address.collect_symbolic_variables(vars);
                data.collect_symbolic_variables(vars);
                if let Some(tag_value) = tag_value {
                    tag_value.collect_symbolic_variables(vars)
                }
            }
            _ => (),
        }
    }

    pub fn is_smt(&self) -> bool {
        matches!(self, Event::Smt(..))
    }

    pub fn is_function(&self) -> bool {
        matches!(self, Event::Function { .. })
    }

    pub fn is_reg(&self) -> bool {
        matches!(self, Event::ReadReg(..) | Event::WriteReg(..) | Event::MarkReg { .. })
    }

    pub fn is_write_reg(&self) -> bool {
        matches!(self, Event::WriteReg(..))
    }

    pub fn is_read_reg(&self) -> bool {
        matches!(self, Event::ReadReg(..))
    }

    pub fn is_read_reg_of(&self, name: Name) -> bool {
        if let Event::ReadReg(reg, _, _) = self {
            *reg == name
        } else {
            false
        }
    }

    pub fn is_write_reg_of(&self, name: Name) -> bool {
        if let Event::WriteReg(reg, _, _) = self {
            *reg == name
        } else {
            false
        }
    }

    pub fn reg_value(&self) -> Option<&Val<B>> {
        match self {
            Event::ReadReg(_, _, value) => Some(value),
            Event::WriteReg(_, _, value) => Some(value),
            _ => None,
        }
    }

    pub fn is_cycle(&self) -> bool {
        matches!(self, Event::Cycle)
    }

    pub fn is_instr(&self) -> bool {
        matches!(self, Event::Instr(_))
    }

    pub fn is_address_announce(&self) -> bool {
        matches!(self, Event::AddressAnnounce { .. })
    }

    pub fn is_branch(&self) -> bool {
        matches!(self, Event::Branch { .. })
    }
    pub fn is_fork(&self) -> bool {
        matches!(self, Event::Fork(_, _, _, _))
    }

    pub fn is_merge(&self) -> bool {
        matches!(self, Event::Merge(_, _, _))
    }

    pub fn is_memory_read_or_write(&self) -> bool {
        matches!(self, Event::ReadMem { .. } | Event::WriteMem { .. })
    }

    pub fn is_memory_read(&self) -> bool {
        matches!(self, Event::ReadMem { .. })
    }

    pub fn is_memory_write(&self) -> bool {
        matches!(self, Event::WriteMem { .. })
    }

    pub fn is_exclusive(&self) -> bool {
        match self {
            Event::ReadMem { opts, .. } => opts.is_exclusive,
            Event::WriteMem { opts, .. } => opts.is_exclusive,
            _ => false,
        }
    }

    pub fn is_ifetch(&self) -> bool {
        match self {
            Event::ReadMem { opts, .. } => opts.is_ifetch,
            _ => false,
        }
    }

    pub fn is_abstract(&self) -> bool {
        matches!(self, Event::Abstract { .. })
    }

    pub fn in_region(&self, region_name: &str) -> bool {
        match self {
            Event::ReadMem { region, .. } => *region == region_name,
            Event::WriteMem { region, .. } => *region == region_name,
            _ => false,
        }
    }
}

/// turn a (Read|Write)Reg event
/// into a human-readable string like
/// "ESR_EL1.ISS"
pub fn register_name_string<B>(ev: &Event<B>, symtab: &Symtab) -> Option<String> {
    let pair = match ev {
        Event::WriteReg(name, accessors, _) => Some((name, accessors)),
        Event::ReadReg(name, accessors, _) => Some((name, accessors)),
        _ => None,
    };

    match pair {
        Some((name, accessors)) => {
            let regnamestr = zencode::decode(symtab.to_str(*name));
            let fieldnames: Vec<String> =
                accessors.iter().map(|Accessor::Field(n)| zencode::decode(symtab.to_str(*n))).collect();
            let fieldstr = fieldnames.join(".");

            if !fieldnames.is_empty() {
                Some(format!("{}.{}", regnamestr, fieldstr))
            } else {
                Some(regnamestr)
            }
        }
        None => None,
    }
}

pub type EvPath<B> = Vec<Event<B>>;

/// Abstractly represents a sequence of events in such a way that
/// checkpoints can be created and shared.
#[derive(Clone, Debug)]
pub struct Trace<B> {
    checkpoints: usize,
    head: Vec<Event<B>>,
    // 仅诊断开启时保存，按本段主迹位置排序，随检查点跨线程共享。
    event_guards: Vec<(usize, Exp<Sym>)>,
    // 同一逻辑段可由根事务共享的已发布事件和本叶事件组成。
    head_prefix: Option<Arc<TraceHead<B>>>,
    projected: Option<Arc<error_snapshot::Segment<B>>>,
    tail: Arc<Option<Trace<B>>>,
}

#[derive(Clone, Debug)]
pub(crate) struct TraceHead<B> {
    pub(crate) events: Vec<Event<B>>,
    event_guards: Vec<(usize, Exp<Sym>)>,
    memory_events_before_arm: usize,
}

impl<B> Trace<B> {
    fn local_events(&self) -> impl DoubleEndedIterator<Item = &Event<B>> {
        self.projected.iter().flat_map(|s| s.iter()).chain(&self.head)
    }

    fn local_len(&self) -> usize {
        self.projected.as_ref().map_or(0, |s| s.len) + self.head.len()
    }

    fn head_events(&self) -> impl DoubleEndedIterator<Item = &Event<B>> {
        self.head_prefix.as_ref().into_iter().flat_map(|prefix| &prefix.events).chain(self.local_events())
    }

    fn head_event(&self, mut index: usize) -> &Event<B> {
        if let Some(prefix) = &self.head_prefix {
            if index < prefix.events.len() {
                return &prefix.events[index];
            }
            index -= prefix.events.len();
        }
        if let Some(s) = &self.projected {
            if index < s.len {
                return s.event(index);
            }
            index -= s.len;
        }
        &self.head[index]
    }
}

impl<B: BV> Trace<B> {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Trace {
            checkpoints: 0,
            head: Vec::new(),
            event_guards: Vec::new(),
            head_prefix: None,
            projected: None,
            tail: Arc::new(None),
        }
    }

    pub fn checkpoint(&mut self, next_var: u32) -> Checkpoint<B> {
        let mut head = Vec::new();
        mem::swap(&mut self.head, &mut head);
        let tail = Arc::new(Some(Trace {
            checkpoints: self.checkpoints,
            head,
            event_guards: mem::take(&mut self.event_guards),
            head_prefix: self.head_prefix.take(),
            projected: self.projected.take(),
            tail: self.tail.clone(),
        }));
        self.checkpoints += 1;
        self.tail = tail.clone();
        Checkpoint { num: self.checkpoints, trace: tail, next_var, cycles: 0 }
    }

    fn events_rev(&self) -> impl Iterator<Item = &Event<B>> {
        std::iter::successors(Some(self), |trace| trace.tail.as_ref().as_ref())
            .flat_map(|trace| trace.head_events().rev())
    }

    fn record_event_guards(&mut self, offset: usize, events: &[(Option<Exp<Sym>>, Event<B>)]) {
        let register_reads = TRACE_EVENT_GUARDS.get().is_some();
        self.event_guards.extend(events.iter().enumerate().filter_map(|(index, (guard, event))| {
            if event.is_memory_read_or_write() || (register_reads && matches!(event, Event::ReadReg(..))) {
                guard.as_ref().map(|guard| (offset + index, guard.clone()))
            } else {
                None
            }
        }));
    }

    /// 返回逆时间顺序的主迹及已记录的事件条件。
    pub fn events_with_guards_rev(&self) -> impl Iterator<Item = (&Event<B>, Option<&Exp<Sym>>)> {
        fn guarded_rev<'a, B: 'a>(
            len: usize,
            events: impl DoubleEndedIterator<Item = &'a Event<B>> + 'a,
            guards: &'a [(usize, Exp<Sym>)],
        ) -> impl Iterator<Item = (&'a Event<B>, Option<&'a Exp<Sym>>)> {
            let mut guards = guards.iter().rev().peekable();
            (0..len).rev().zip(events.rev()).map(move |(index, event)| {
                let guard = if guards.peek().is_some_and(|(position, _)| *position == index) {
                    guards.next().map(|(_, guard)| guard)
                } else {
                    None
                };
                (event, guard)
            })
        }

        std::iter::successors(Some(self), |trace| trace.tail.as_ref().as_ref()).flat_map(|trace| {
            guarded_rev(trace.local_len(), trace.local_events(), &trace.event_guards).chain(
                trace
                    .head_prefix
                    .as_ref()
                    .into_iter()
                    .flat_map(|prefix| guarded_rev(prefix.events.len(), prefix.events.iter(), &prefix.event_guards)),
            )
        })
    }

    pub fn to_vec(&self) -> Vec<&Event<B>> {
        self.events_rev().collect()
    }
}

static TRACE_EVENT_GUARDS: OnceLock<()> = OnceLock::new();

/// 在启动 worker 前开启寄存器读取条件的诊断记录。访存条件始终保存。
pub fn enable_trace_event_guards() {
    TRACE_EVENT_GUARDS.get_or_init(|| ());
}

/// 求解选项；有限域识别和枚举沿用路径合并配置的缺省值。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SolverOptions {
    pub on_unknown: crate::config::PathFailureAction,
    pub skip_branch_checks: bool,
    pub skip_bool_proofs: bool,
    pub no_smt: bool,
    pub keep_bool_proofs: bool,
    pub finite_domain_enumeration: bool,
    pub incremental_choice_dag: bool,
    pub coi_query_slicing: bool,
    pub finite_domain_ground_eval: bool,
    pub bv_rewrite: rewrite::BvRewrite,
}

impl Default for SolverOptions {
    fn default() -> Self {
        let defaults = crate::config::PathMergeConfig::default();
        Self {
            on_unknown: Default::default(),
            skip_branch_checks: false,
            skip_bool_proofs: false,
            no_smt: false,
            keep_bool_proofs: false,
            finite_domain_enumeration: defaults.finite_domain_enumeration,
            incremental_choice_dag: false,
            coi_query_slicing: false,
            finite_domain_ground_eval: defaults.finite_domain_ground_eval,
            bv_rewrite: Default::default(),
        }
    }
}

static SOLVER_OPTIONS: OnceLock<SolverOptions> = OnceLock::new();

/// CLI 在启动 worker 前设置；单测通过 Config 独立设置，避免全局交叉影响。
pub fn configure_solver_options(options: SolverOptions) {
    assert_eq!(*SOLVER_OPTIONS.get_or_init(|| options), options, "求解选项不能在运行中改变");
}

/// Z3 配置及执行选项；释放时清理 Z3 配置句柄。
pub struct Config {
    pub solver_options: SolverOptions,
    pub(crate) validation: bool,
    z3_cfg: Z3_config,
    rlimit: Option<u32>,
    native_timeout: Option<Duration>,
}

impl Config {
    pub fn new() -> Self {
        let solver_options = SOLVER_OPTIONS.get().copied().unwrap_or_default();
        #[cfg(test)]
        let solver_options = test_queries::solver_options().unwrap_or(solver_options);
        unsafe {
            Config { z3_cfg: Z3_mk_config(), solver_options, validation: false, rlimit: None, native_timeout: None }
        }
    }
}

impl Drop for Config {
    fn drop(&mut self) {
        unsafe { Z3_del_config(self.z3_cfg) }
    }
}

impl Default for Config {
    fn default() -> Self {
        Self::new()
    }
}

impl Config {
    pub fn set_param_value(&mut self, id: &str, value: &str) {
        match id {
            "rlimit" => self.rlimit = value.parse::<u32>().ok().filter(|limit| *limit != 0),
            "timeout" => {
                self.native_timeout = value
                    .parse::<u32>()
                    .ok()
                    .filter(|limit| *limit != 0 && *limit != u32::MAX)
                    .map(|limit| Duration::from_millis(u64::from(limit)))
            }
            _ => (),
        }
        let id = CString::new(id).unwrap();
        let value = CString::new(value).unwrap();
        unsafe { Z3_set_param_value(self.z3_cfg, id.as_ptr(), value.as_ptr()) }
    }
}

fn fresh_random_seed() -> u32 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.subsec_nanos())
        .unwrap_or(1)
}

// 自定义全局改写参数可能限制单次化简。此时走原生路径。
static CUSTOM_Z3_GLOBAL_PARAMS: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

pub fn global_set_param_value(id: &str, value: &str) {
    CUSTOM_Z3_GLOBAL_PARAMS.store(true, std::sync::atomic::Ordering::Release);
    let id = CString::new(id).unwrap();
    let value = CString::new(value).unwrap();
    unsafe { Z3_global_param_set(id.as_ptr(), value.as_ptr()) }
}

/// Context is a wrapper around `Z3_context`.
pub struct Context {
    solver_options: SolverOptions,
    validation: bool,
    z3_ctx: Z3_context,
    rlimit: Option<u32>,
    native_timeout: Option<Duration>,
    enum_cache: RefCell<HashMap<EnumSortKey, Enum>>,
    structural_bools: RefCell<no_smt::StructuralBoolCache>,
    small_simplifications: RefCell<rewrite::SmallSimplifications>,
}

fn z3_version_supported(version: (c_uint, c_uint, c_uint, c_uint)) -> bool {
    version >= MIN_Z3_VERSION
}

impl Context {
    pub fn new(cfg: Config) -> Self {
        static VERSION_CHECK: std::sync::Once = std::sync::Once::new();
        VERSION_CHECK.call_once(|| {
            let (mut major, mut minor, mut build, mut revision) = (0, 0, 0, 0);
            unsafe { Z3_get_version(&mut major, &mut minor, &mut build, &mut revision) };
            let (min_major, min_minor, min_build, min_revision) = MIN_Z3_VERSION;
            assert!(z3_version_supported((major, minor, build, revision)),
                "运行时 Z3 版本 {major}.{minor}.{build}.{revision} 低于最低版本 {min_major}.{min_minor}.{min_build}.{min_revision}");
        });
        unsafe {
            Context {
                solver_options: cfg.solver_options,
                validation: cfg.validation,
                z3_ctx: Z3_mk_context_rc(cfg.z3_cfg),
                rlimit: cfg.rlimit,
                native_timeout: cfg.native_timeout,
                enum_cache: RefCell::new(HashMap::new()),
                structural_bools: RefCell::default(),
                small_simplifications: RefCell::default(),
            }
        }
    }

    fn has_unbounded_rewriting(&self) -> bool {
        self.rlimit.is_none()
            && self.native_timeout.is_none()
            && !CUSTOM_Z3_GLOBAL_PARAMS.load(std::sync::atomic::Ordering::Acquire)
    }

    fn error(&self) -> ExecError {
        unsafe {
            let code = Z3_get_error_code(self.z3_ctx);
            let msg = Z3_get_error_msg(self.z3_ctx, code);
            let str: String = CStr::from_ptr(msg).to_string_lossy().to_string();
            ExecError::Z3Error(str)
        }
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        for (_, enumeration) in self.enum_cache.get_mut().drain() {
            enumeration.dec_refs(self.z3_ctx);
        }
        self.structural_bools.get_mut().clear(self.z3_ctx);
        self.small_simplifications.get_mut().clear(self.z3_ctx);
        unsafe { Z3_del_context(self.z3_ctx) }
    }
}

#[derive(PartialEq, Eq, Hash)]
enum EnumSortKey {
    Int(i32),
    String(String),
}

#[derive(Clone)]
struct Enum {
    sort: Z3_sort,
    consts: Vec<Z3_func_decl>,
    testers: Vec<Z3_func_decl>,
}

impl Enum {
    fn inc_refs(&self, ctx: Z3_context) {
        unsafe {
            for i in 0..self.consts.len() {
                Z3_inc_ref(ctx, Z3_func_decl_to_ast(ctx, self.consts[i]));
                Z3_inc_ref(ctx, Z3_func_decl_to_ast(ctx, self.testers[i]));
            }
            Z3_inc_ref(ctx, Z3_sort_to_ast(ctx, self.sort));
        }
    }

    fn dec_refs(&self, ctx: Z3_context) {
        unsafe {
            for i in 0..self.consts.len() {
                Z3_dec_ref(ctx, Z3_func_decl_to_ast(ctx, self.consts[i]));
                Z3_dec_ref(ctx, Z3_func_decl_to_ast(ctx, self.testers[i]));
            }
            Z3_dec_ref(ctx, Z3_sort_to_ast(ctx, self.sort));
        }
    }
}

struct Enums<'ctx> {
    enums: HashMap<Name, Enum, ahash::RandomState>,
    ctx: &'ctx Context,
}

impl<'ctx> Enums<'ctx> {
    fn new(ctx: &'ctx Context) -> Self {
        Enums { enums: HashMap::default(), ctx }
    }

    fn add_enum(&mut self, name: Name, members: &[Sym], symbol_namer: &Z3SymbolNamer) {
        unsafe {
            let ctx = self.ctx.z3_ctx;
            let size = members.len();
            assert!(size > 0, "枚举类型至少需要一个成员");

            let z3_name = symbol_namer.enum_sort(self.ctx, name);
            let cache_key = match Z3_get_symbol_kind(ctx, z3_name) {
                SymbolKind::Int => EnumSortKey::Int(Z3_get_symbol_int(ctx, z3_name)),
                SymbolKind::String => {
                    EnumSortKey::String(CStr::from_ptr(Z3_get_symbol_string(ctx, z3_name)).to_str().unwrap().to_owned())
                }
            };
            if let Some(enumeration) = self.ctx.enum_cache.borrow().get(&cache_key) {
                assert_eq!(enumeration.consts.len(), size, "枚举类型的成员数量冲突");
                let enumeration = enumeration.clone();
                enumeration.inc_refs(ctx);
                self.enums.insert(name, enumeration);
                return;
            }
            let members: Vec<Z3_symbol> = members
                .iter()
                .enumerate()
                .map(|(member, symbol)| symbol_namer.enum_member(self.ctx, name, member, *symbol))
                .collect();

            let mut consts = mem::ManuallyDrop::new(Vec::with_capacity(size));
            let mut testers = mem::ManuallyDrop::new(Vec::with_capacity(size));

            let sort = Z3_mk_enumeration_sort(
                ctx,
                z3_name,
                size as c_uint,
                members.as_ptr(),
                consts.as_mut_ptr(),
                testers.as_mut_ptr(),
            );

            let consts = Vec::from_raw_parts(consts.as_mut_ptr(), size, size);
            let testers = Vec::from_raw_parts(testers.as_mut_ptr(), size, size);

            let enumeration = Enum { sort, consts, testers };
            enumeration.inc_refs(ctx);
            self.ctx.enum_cache.borrow_mut().insert(cache_key, enumeration.clone());
            enumeration.inc_refs(ctx);
            self.enums.insert(name, enumeration);
        }
    }
}

impl Drop for Enums<'_> {
    fn drop(&mut self) {
        let ctx = self.ctx.z3_ctx;
        for (_, e) in self.enums.drain() {
            e.dec_refs(ctx);
        }
    }
}

struct Sort<'ctx> {
    z3_sort: Z3_sort,
    ctx: &'ctx Context,
}

impl<'ctx> Sort<'ctx> {
    fn float(ctx: &'ctx Context, ebits: u32, sbits: u32) -> Self {
        assert!(ebits > 1 && sbits > 2);

        unsafe {
            let z3_sort = Z3_mk_fpa_sort(ctx.z3_ctx, ebits, sbits);
            Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, z3_sort));
            Sort { z3_sort, ctx }
        }
    }

    fn bitvec(ctx: &'ctx Context, sz: u32) -> Self {
        unsafe {
            let z3_sort = Z3_mk_bv_sort(ctx.z3_ctx, sz);
            Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, z3_sort));
            Sort { z3_sort, ctx }
        }
    }

    fn new(ctx: &'ctx Context, enums: &Enums<'ctx>, ty: &Ty) -> Self {
        unsafe {
            match ty {
                Ty::Bool => {
                    let z3_sort = Z3_mk_bool_sort(ctx.z3_ctx);
                    Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, z3_sort));
                    Sort { z3_sort, ctx }
                }
                Ty::BitVec(sz) => Self::bitvec(ctx, *sz),
                Ty::Enum(e) => {
                    let z3_sort = enums.enums[&e.id].sort;
                    Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, z3_sort));
                    Sort { z3_sort, ctx }
                }
                Ty::Array(dom, codom) => {
                    let dom_s = Self::new(ctx, enums, dom);
                    let codom_s = Self::new(ctx, enums, codom);
                    let z3_sort = Z3_mk_array_sort(ctx.z3_ctx, dom_s.z3_sort, codom_s.z3_sort);
                    Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, z3_sort));
                    Sort { z3_sort, ctx }
                }
                Ty::Float(ebits, sbits) => Self::float(ctx, *ebits, *sbits),
                Ty::RoundingMode => {
                    let z3_sort = Z3_mk_fpa_rounding_mode_sort(ctx.z3_ctx);
                    Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, z3_sort));
                    Sort { z3_sort, ctx }
                }
            }
        }
    }
}

impl Drop for Sort<'_> {
    fn drop(&mut self) {
        unsafe {
            let ctx = self.ctx.z3_ctx;
            Z3_dec_ref(ctx, Z3_sort_to_ast(ctx, self.z3_sort))
        }
    }
}

struct FuncDecl<'ctx> {
    z3_func_decl: Z3_func_decl,
    ctx: &'ctx Context,
}

impl<'ctx> FuncDecl<'ctx> {
    fn new(
        ctx: &'ctx Context,
        v: Sym,
        enums: &Enums<'ctx>,
        arg_tys: &[Ty],
        ty: &Ty,
        symbol_namer: &Z3SymbolNamer,
    ) -> Self {
        unsafe {
            let name = symbol_namer.symbol(ctx, v);
            let arg_sorts: Vec<Sort> = arg_tys.iter().map(|ty| Sort::new(ctx, enums, ty)).collect();
            let arg_z3_sorts: Vec<Z3_sort> = arg_sorts.iter().map(|s| s.z3_sort).collect();
            let args: u32 = arg_sorts.len() as u32;
            let z3_func_decl =
                Z3_mk_func_decl(ctx.z3_ctx, name, args, arg_z3_sorts.as_ptr(), Sort::new(ctx, enums, ty).z3_sort);
            Z3_inc_ref(ctx.z3_ctx, Z3_func_decl_to_ast(ctx.z3_ctx, z3_func_decl));
            FuncDecl { z3_func_decl, ctx }
        }
    }
}

impl Clone for FuncDecl<'_> {
    fn clone(&self) -> Self {
        unsafe { Z3_inc_ref(self.ctx.z3_ctx, Z3_func_decl_to_ast(self.ctx.z3_ctx, self.z3_func_decl)) };
        Self { z3_func_decl: self.z3_func_decl, ctx: self.ctx }
    }
}

impl Drop for FuncDecl<'_> {
    fn drop(&mut self) {
        unsafe {
            let ctx = self.ctx.z3_ctx;
            Z3_dec_ref(ctx, Z3_func_decl_to_ast(ctx, self.z3_func_decl))
        }
    }
}

struct Ast<'ctx> {
    z3_ast: Z3_ast,
    ctx: &'ctx Context,
}

impl Clone for Ast<'_> {
    fn clone(&self) -> Self {
        unsafe {
            let z3_ast = self.z3_ast;
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }
}

macro_rules! z3_nullary_op {
    ($i:ident, $ctx:ident) => {
        unsafe {
            let z3_ast = $i($ctx.z3_ctx);
            Z3_inc_ref($ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: $ctx }
        }
    };
}

macro_rules! z3_unary_op {
    ($i:ident, $arg:ident) => {
        unsafe {
            let z3_ast = $i($arg.ctx.z3_ctx, $arg.z3_ast);
            Z3_inc_ref($arg.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: $arg.ctx }
        }
    };
}

macro_rules! z3_binary_op {
    ($i:ident, $lhs:ident, $rhs:ident) => {
        unsafe {
            let z3_ast = $i($lhs.ctx.z3_ctx, $lhs.z3_ast, $rhs.z3_ast);
            Z3_inc_ref($lhs.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: $lhs.ctx }
        }
    };
}

macro_rules! z3_float_binary_op {
    ($i:ident, $rm:ident, $lhs:ident, $rhs:ident) => {
        unsafe {
            let z3_ast = $i($lhs.ctx.z3_ctx, $rm.z3_ast, $lhs.z3_ast, $rhs.z3_ast);
            Z3_inc_ref($lhs.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: $rm.ctx }
        }
    };
}

mod arithmetic;
mod arm_replay;
mod coi;
mod const_binding;
pub(crate) use arm_replay::ArmReplay;
use const_binding::ConstBinding;
pub mod rewrite;
#[cfg(test)]
mod rewrite_tests;

static PUSH_ITE_BV: &[u8] = b"push_ite_bv\0";
static BV_LE_EXTRA: &[u8] = b"bv_le_extra\0";
static BV_SORT_AC: &[u8] = b"bv_sort_ac\0";

#[cfg(test)]
thread_local! {
    static AST_SIMPLIFY_CALLS: Cell<usize> = const { Cell::new(0) };
}

impl<'ctx> Ast<'ctx> {
    /// 位向量排序的位宽；非位向量返回 None。
    pub(crate) fn bv_width(&self) -> Option<u32> {
        unsafe {
            let sort = Z3_get_sort(self.ctx.z3_ctx, self.z3_ast);
            (Z3_get_sort_kind(self.ctx.z3_ctx, sort) == SortKind::BV)
                .then(|| Z3_get_bv_sort_size(self.ctx.z3_ctx, sort))
        }
    }

    fn simplify(&mut self) {
        self.simplify_with_verified_fixpoint();
    }

    fn simplify_native(&mut self) {
        #[cfg(test)]
        AST_SIMPLIFY_CALLS.set(AST_SIMPLIFY_CALLS.get() + 1);
        let cost_scope =
            crate::executor::stats::region_cost::Scope::enter(crate::executor::stats::region_cost::Category::Simplify);
        let _ = &cost_scope;
        unsafe {
            if SMT_CONFIG.get().is_some_and(|config| config.tactic == Tactic::Default) {
                let z3_ast = Z3_simplify(self.ctx.z3_ctx, self.z3_ast);
                assert!(!z3_ast.is_null(), "Z3 化简未完成：{:?}", self.ctx.error());
                Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
                Z3_dec_ref(self.ctx.z3_ctx, self.z3_ast);
                self.z3_ast = z3_ast;
                return;
            }
            let z3_params = Z3_mk_params(self.ctx.z3_ctx);
            let push_ite_bv =
                Z3_mk_string_symbol(self.ctx.z3_ctx, CStr::from_bytes_with_nul_unchecked(PUSH_ITE_BV).as_ptr());
            let bv_le_extra =
                Z3_mk_string_symbol(self.ctx.z3_ctx, CStr::from_bytes_with_nul_unchecked(BV_LE_EXTRA).as_ptr());
            let bv_sort_ac =
                Z3_mk_string_symbol(self.ctx.z3_ctx, CStr::from_bytes_with_nul_unchecked(BV_SORT_AC).as_ptr());
            Z3_params_inc_ref(self.ctx.z3_ctx, z3_params);
            Z3_params_set_bool(self.ctx.z3_ctx, z3_params, push_ite_bv, true);
            Z3_params_set_bool(self.ctx.z3_ctx, z3_params, bv_le_extra, true);
            Z3_params_set_bool(self.ctx.z3_ctx, z3_params, bv_sort_ac, true);

            let z3_ast = Z3_simplify_ex(self.ctx.z3_ctx, self.z3_ast, z3_params);
            assert!(!z3_ast.is_null(), "Z3 化简未完成：{:?}", self.ctx.error());
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Z3_dec_ref(self.ctx.z3_ctx, self.z3_ast);
            self.z3_ast = z3_ast;

            Z3_params_dec_ref(self.ctx.z3_ctx, z3_params);
        }
    }

    fn mk_constant(fd: &FuncDecl<'ctx>) -> Self {
        unsafe {
            let z3_ast = Z3_mk_app(fd.ctx.z3_ctx, fd.z3_func_decl, 0, ptr::null());
            Z3_inc_ref(fd.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: fd.ctx }
        }
    }

    fn mk_app(fd: &FuncDecl<'ctx>, args: &[Ast<'ctx>]) -> Self {
        unsafe {
            let z3_args: Vec<Z3_ast> = args.iter().map(|ast| ast.z3_ast).collect();
            let len = z3_args.len() as u32;
            let z3_ast = Z3_mk_app(fd.ctx.z3_ctx, fd.z3_func_decl, len, z3_args.as_ptr());
            Z3_inc_ref(fd.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: fd.ctx }
        }
    }

    fn mk_enum_member(enums: &Enums<'ctx>, enum_id: EnumId, member: usize) -> Self {
        unsafe {
            let func_decl = enums.enums[&enum_id.id].consts[member];
            let z3_ast = Z3_mk_app(enums.ctx.z3_ctx, func_decl, 0, ptr::null());
            Z3_inc_ref(enums.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: enums.ctx }
        }
    }

    fn mk_bv_u64(ctx: &'ctx Context, sz: u32, bits: u64) -> Self {
        unsafe {
            let sort = Sort::bitvec(ctx, sz);
            let z3_ast = Z3_mk_unsigned_int64(ctx.z3_ctx, bits, sort.z3_sort);
            Z3_inc_ref(ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx }
        }
    }

    fn mk_bv(ctx: &'ctx Context, sz: u32, bits: &[bool]) -> Self {
        unsafe {
            let z3_ast = Z3_mk_bv_numeral(ctx.z3_ctx, sz, bits.as_ptr());
            Z3_inc_ref(ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx }
        }
    }

    fn mk_fpa_nan(ctx: &'ctx Context, ebits: u32, sbits: u32) -> Self {
        unsafe {
            let sort = Sort::float(ctx, ebits, sbits);
            let z3_ast = Z3_mk_fpa_nan(ctx.z3_ctx, sort.z3_sort);
            Z3_inc_ref(ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx }
        }
    }

    fn mk_fpa_zero(ctx: &'ctx Context, ebits: u32, sbits: u32, negative: bool) -> Self {
        unsafe {
            let sort = Sort::float(ctx, ebits, sbits);
            let z3_ast = Z3_mk_fpa_zero(ctx.z3_ctx, sort.z3_sort, negative);
            Z3_inc_ref(ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx }
        }
    }

    fn mk_fpa_inf(ctx: &'ctx Context, ebits: u32, sbits: u32, negative: bool) -> Self {
        unsafe {
            let sort = Sort::float(ctx, ebits, sbits);
            let z3_ast = Z3_mk_fpa_inf(ctx.z3_ctx, sort.z3_sort, negative);
            Z3_inc_ref(ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx }
        }
    }

    fn mk_bool(ctx: &'ctx Context, b: bool) -> Self {
        unsafe {
            let z3_ast = if b { Z3_mk_true(ctx.z3_ctx) } else { Z3_mk_false(ctx.z3_ctx) };
            Z3_inc_ref(ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx }
        }
    }

    fn mk_fpa_round_to_integral(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_fpa_round_to_integral, self, rhs)
    }

    fn mk_fpa_round_nearest_ties_to_even(ctx: &'ctx Context) -> Self {
        z3_nullary_op!(Z3_mk_fpa_round_nearest_ties_to_even, ctx)
    }

    fn mk_fpa_round_nearest_ties_to_away(ctx: &'ctx Context) -> Self {
        z3_nullary_op!(Z3_mk_fpa_round_nearest_ties_to_away, ctx)
    }

    fn mk_fpa_round_toward_positive(ctx: &'ctx Context) -> Self {
        z3_nullary_op!(Z3_mk_fpa_round_toward_positive, ctx)
    }

    fn mk_fpa_round_toward_negative(ctx: &'ctx Context) -> Self {
        z3_nullary_op!(Z3_mk_fpa_round_toward_negative, ctx)
    }

    fn mk_fpa_round_toward_zero(ctx: &'ctx Context) -> Self {
        z3_nullary_op!(Z3_mk_fpa_round_toward_zero, ctx)
    }

    fn mk_not(&self) -> Self {
        z3_unary_op!(Z3_mk_not, self)
    }

    fn mk_eq(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_eq, self, rhs)
    }

    fn mk_and(&self, rhs: &Ast<'ctx>) -> Self {
        unsafe {
            let z3_ast = Z3_mk_and(self.ctx.z3_ctx, 2, &[self.z3_ast, rhs.z3_ast] as *const Z3_ast);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn mk_or(&self, rhs: &Ast<'ctx>) -> Self {
        unsafe {
            let z3_ast = Z3_mk_or(self.ctx.z3_ctx, 2, &[self.z3_ast, rhs.z3_ast] as *const Z3_ast);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn extract(&self, hi: u32, lo: u32) -> Self {
        unsafe {
            let z3_ast = Z3_mk_extract(self.ctx.z3_ctx, hi, lo, self.z3_ast);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn zero_extend(&self, i: u32) -> Self {
        unsafe {
            let z3_ast = Z3_mk_zero_ext(self.ctx.z3_ctx, i, self.z3_ast);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn sign_extend(&self, i: u32) -> Self {
        unsafe {
            let z3_ast = Z3_mk_sign_ext(self.ctx.z3_ctx, i, self.z3_ast);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn ite(&self, true_exp: &Ast<'ctx>, false_exp: &Ast<'ctx>) -> Self {
        unsafe {
            let z3_ast = Z3_mk_ite(self.ctx.z3_ctx, self.z3_ast, true_exp.z3_ast, false_exp.z3_ast);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn mk_bvnot(&self) -> Self {
        z3_unary_op!(Z3_mk_bvnot, self)
    }

    fn mk_bvand(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvand, self, rhs)
    }

    fn mk_bvor(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvor, self, rhs)
    }

    fn mk_bvxor(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvxor, self, rhs)
    }

    fn mk_bvnand(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvnand, self, rhs)
    }

    fn mk_bvnor(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvnor, self, rhs)
    }

    fn mk_bvxnor(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvxnor, self, rhs)
    }

    fn mk_bvneg(&self) -> Self {
        z3_unary_op!(Z3_mk_bvneg, self)
    }

    fn mk_bvadd(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvadd, self, rhs)
    }

    fn mk_bvsub(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvsub, self, rhs)
    }

    fn mk_bvudiv(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvudiv, self, rhs)
    }

    fn mk_bvurem(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvurem, self, rhs)
    }

    fn mk_bvsmod(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvsmod, self, rhs)
    }

    fn mk_bvult(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvult, self, rhs)
    }

    fn mk_bvslt(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvslt, self, rhs)
    }

    fn mk_bvule(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvule, self, rhs)
    }

    fn mk_bvsle(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvsle, self, rhs)
    }

    fn mk_bvuge(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvuge, self, rhs)
    }

    fn mk_bvsge(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvsge, self, rhs)
    }

    fn mk_bvugt(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvugt, self, rhs)
    }

    fn mk_bvsgt(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvsgt, self, rhs)
    }

    fn mk_bvshl(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvshl, self, rhs)
    }

    fn mk_bvlshr(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvlshr, self, rhs)
    }

    fn mk_bvashr(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvashr, self, rhs)
    }

    fn mk_concat(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_concat, self, rhs)
    }

    fn mk_select(&self, index: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_select, self, index)
    }

    fn mk_fpa_abs(&self) -> Self {
        z3_unary_op!(Z3_mk_fpa_abs, self)
    }

    fn mk_fpa_neg(&self) -> Self {
        z3_unary_op!(Z3_mk_fpa_neg, self)
    }

    fn mk_fpa_add(&self, lhs: &Ast<'ctx>, rhs: &Ast<'ctx>) -> Self {
        z3_float_binary_op!(Z3_mk_fpa_add, self, lhs, rhs)
    }

    fn mk_fpa_div(&self, lhs: &Ast<'ctx>, rhs: &Ast<'ctx>) -> Self {
        z3_float_binary_op!(Z3_mk_fpa_div, self, lhs, rhs)
    }

    fn mk_fpa_eq(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_fpa_eq, self, rhs)
    }

    fn mk_fpa_fma(&self, t1: &Ast<'ctx>, t2: &Ast<'ctx>, t3: &Ast<'ctx>) -> Self {
        unsafe {
            let z3_ast = Z3_mk_fpa_fma(self.ctx.z3_ctx, self.z3_ast, t1.z3_ast, t2.z3_ast, t3.z3_ast);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn mk_fpa_geq(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_fpa_geq, self, rhs)
    }

    fn mk_fpa_gt(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_fpa_gt, self, rhs)
    }

    fn mk_fpa_leq(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_fpa_leq, self, rhs)
    }

    fn mk_fpa_lt(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_fpa_lt, self, rhs)
    }

    fn mk_fpa_rem(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_fpa_rem, self, rhs)
    }

    fn mk_fpa_max(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_fpa_max, self, rhs)
    }

    fn mk_fpa_min(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_fpa_min, self, rhs)
    }

    fn mk_fpa_mul(&self, lhs: &Ast<'ctx>, rhs: &Ast<'ctx>) -> Self {
        z3_float_binary_op!(Z3_mk_fpa_mul, self, lhs, rhs)
    }

    fn mk_fpa_sqrt(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_fpa_sqrt, self, rhs)
    }

    fn mk_fpa_sub(&self, lhs: &Ast<'ctx>, rhs: &Ast<'ctx>) -> Self {
        z3_float_binary_op!(Z3_mk_fpa_sub, self, lhs, rhs)
    }

    fn mk_fpa_is_normal(&self) -> Self {
        z3_unary_op!(Z3_mk_fpa_is_normal, self)
    }

    fn mk_fpa_is_subnormal(&self) -> Self {
        z3_unary_op!(Z3_mk_fpa_is_subnormal, self)
    }

    fn mk_fpa_is_zero(&self) -> Self {
        z3_unary_op!(Z3_mk_fpa_is_zero, self)
    }

    fn mk_fpa_is_infinite(&self) -> Self {
        z3_unary_op!(Z3_mk_fpa_is_infinite, self)
    }

    fn mk_fpa_is_nan_raw(&self) -> Self {
        z3_unary_op!(Z3_mk_fpa_is_nan, self)
    }

    fn mk_fpa_is_nan(&self) -> Self {
        unsafe {
            let ctx = self.ctx.z3_ctx;
            if Z3_get_ast_kind(ctx, self.z3_ast) == AstKind::App {
                let app = Z3_to_app(ctx, self.z3_ast);
                let declaration = Z3_get_app_decl(ctx, app);
                let name = Z3_get_decl_name(ctx, declaration);
                if Z3_get_symbol_kind(ctx, name) == SymbolKind::String
                    && CStr::from_ptr(Z3_get_symbol_string(ctx, name)).to_bytes() == b"fp.div"
                    && Z3_get_app_num_args(ctx, app) == 3
                {
                    let args = [Z3_get_app_arg(ctx, app, 0), Z3_get_app_arg(ctx, app, 1), Z3_get_app_arg(ctx, app, 2)];
                    if Z3_get_sort_kind(ctx, Z3_get_sort(ctx, args[0])) == SortKind::RoundingMode
                        && Z3_get_sort_kind(ctx, Z3_get_sort(ctx, args[1])) == SortKind::FloatingPoint
                        && Z3_is_eq_sort(ctx, Z3_get_sort(ctx, args[1]), Z3_get_sort(ctx, args[2]))
                    {
                        let [rounding, left, right] = args.map(|z3_ast| {
                            Z3_inc_ref(ctx, z3_ast);
                            Ast { z3_ast, ctx: self.ctx }
                        });
                        let builtin = rounding.mk_fpa_div(&left, &right);
                        // 用实际内建声明核对，不能把同名未解释函数当作浮点除法。
                        // z3-sys 0.5 的 DeclKind 数值与现用 Z3 不兼容，不能读取该 Rust 枚举。
                        if Z3_get_ast_kind(ctx, builtin.z3_ast) == AstKind::App
                            && Z3_is_eq_func_decl(
                                ctx,
                                declaration,
                                Z3_get_app_decl(ctx, Z3_to_app(ctx, builtin.z3_ast)),
                            )
                        {
                            // 对所有精度和舍入模式，NaN仅来自NaN输入、0/0或无穷/无穷。
                            // 数值结果仍使用原除法；分类查询无需构造其数值除法器。
                            let left_nan = left.mk_fpa_is_nan_raw();
                            let right_nan = right.mk_fpa_is_nan_raw();
                            let both_zero = left.mk_fpa_is_zero().mk_and(&right.mk_fpa_is_zero());
                            let both_infinite = left.mk_fpa_is_infinite().mk_and(&right.mk_fpa_is_infinite());
                            return left_nan.mk_or(&right_nan).mk_or(&both_zero).mk_or(&both_infinite);
                        }
                    }
                }
            }
        }
        self.mk_fpa_is_nan_raw()
    }

    fn mk_fpa_is_negative(&self) -> Self {
        z3_unary_op!(Z3_mk_fpa_is_negative, self)
    }

    fn mk_fpa_is_positive(&self) -> Self {
        z3_unary_op!(Z3_mk_fpa_is_positive, self)
    }

    fn mk_fpa_to_fp_bv(&self, ebits: u32, sbits: u32) -> Self {
        unsafe {
            let sort = Sort::float(self.ctx, ebits, sbits);
            let z3_ast = Z3_mk_fpa_to_fp_bv(self.ctx.z3_ctx, self.z3_ast, sort.z3_sort);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn mk_fpa_to_ieee_bv(&self) -> Self {
        z3_unary_op!(Z3_mk_fpa_to_ieee_bv, self)
    }

    fn mk_fpa_to_fp_float(&self, exp: &Ast<'ctx>, ebits: u32, sbits: u32) -> Self {
        unsafe {
            let sort = Sort::float(self.ctx, ebits, sbits);
            let z3_ast = Z3_mk_fpa_to_fp_float(self.ctx.z3_ctx, self.z3_ast, exp.z3_ast, sort.z3_sort);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn mk_fpa_to_fp_signed(&self, exp: &Ast<'ctx>, ebits: u32, sbits: u32) -> Self {
        unsafe {
            let sort = Sort::float(self.ctx, ebits, sbits);
            let z3_ast = Z3_mk_fpa_to_fp_signed(self.ctx.z3_ctx, self.z3_ast, exp.z3_ast, sort.z3_sort);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn mk_fpa_to_fp_unsigned(&self, exp: &Ast<'ctx>, ebits: u32, sbits: u32) -> Self {
        unsafe {
            let sort = Sort::float(self.ctx, ebits, sbits);
            let z3_ast = Z3_mk_fpa_to_fp_unsigned(self.ctx.z3_ctx, self.z3_ast, exp.z3_ast, sort.z3_sort);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn mk_fpa_to_sbv(&self, exp: &Ast<'ctx>, sz: u32) -> Self {
        unsafe {
            let z3_ast = Z3_mk_fpa_to_sbv(self.ctx.z3_ctx, self.z3_ast, exp.z3_ast, sz);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn mk_fpa_to_ubv(&self, exp: &Ast<'ctx>, sz: u32) -> Self {
        unsafe {
            let z3_ast = Z3_mk_fpa_to_ubv(self.ctx.z3_ctx, self.z3_ast, exp.z3_ast, sz);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn mk_store(&self, index: &Ast<'ctx>, val: &Ast<'ctx>) -> Self {
        unsafe {
            let z3_ast = Z3_mk_store(self.ctx.z3_ctx, self.z3_ast, index.z3_ast, val.z3_ast);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn mk_distinct(ctx: &'ctx Context, args: &[Ast<'ctx>]) -> Self {
        unsafe {
            let z3_args: Vec<Z3_ast> = args.iter().map(|ast| ast.z3_ast).collect();
            let len = z3_args.len() as u32;
            let z3_ast = Z3_mk_distinct(ctx.z3_ctx, len, z3_args.as_ptr());
            Z3_inc_ref(ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx }
        }
    }

    fn get_bool_value(&self) -> Option<bool> {
        unsafe {
            match Z3_get_bool_value(self.ctx.z3_ctx, self.z3_ast) {
                Z3_L_TRUE => Some(true),
                Z3_L_FALSE => Some(false),
                _ => None,
            }
        }
    }

    fn get_numeral_u64(&self) -> Result<u64, ExecError> {
        let mut v: u64 = 0;
        unsafe {
            if Z3_get_numeral_uint64(self.ctx.z3_ctx, self.z3_ast, &mut v) {
                Ok(v)
            } else {
                Err(self.ctx.error())
            }
        }
    }
}

impl Drop for Ast<'_> {
    fn drop(&mut self) {
        unsafe { Z3_dec_ref(self.ctx.z3_ctx, self.z3_ast) }
    }
}

#[cfg(not(feature = "smtperf"))]
#[derive(Clone)]
struct PerformanceInfo {}

#[cfg(feature = "smtperf")]
#[derive(Clone)]
struct PerformanceInfo {
    vars: Graph<(Sym, SourceLoc), (), Directed>,
    var_nodes: HashMap<Sym, NodeIndex, ahash::RandomState>,
    time_per_location: HashMap<SourceLoc, Duration, ahash::RandomState>,
    start: Instant,
}

impl PerformanceInfo {
    #[cfg(not(feature = "smtperf"))]
    fn new() -> Self {
        PerformanceInfo {}
    }

    #[cfg(feature = "smtperf")]
    fn new() -> Self {
        PerformanceInfo {
            vars: Graph::new(),
            var_nodes: HashMap::default(),
            time_per_location: HashMap::default(),
            start: Instant::now(),
        }
    }

    #[cfg(not(feature = "smtperf"))]
    fn add_var_node(&mut self, _: Sym, _: SourceLoc) {}

    #[cfg(feature = "smtperf")]
    fn add_var_node(&mut self, v: Sym, info: SourceLoc) {
        let index = self.vars.add_node((v, info));
        self.var_nodes.insert(v, index);
    }

    #[cfg(not(feature = "smtperf"))]
    fn add_var_edge(&mut self, _: &Sym, _: &Sym) {}

    #[cfg(feature = "smtperf")]
    fn add_var_edge(&mut self, v1: &Sym, v2: &Sym) {
        let Some(source) = self.var_nodes.get(v1) else { return };
        let Some(target) = self.var_nodes.get(v2) else { return };
        self.vars.update_edge(*source, *target, ());
    }

    #[cfg(not(feature = "smtperf"))]
    fn start(&mut self) {}

    #[cfg(feature = "smtperf")]
    fn start(&mut self) {
        self.start = Instant::now()
    }

    #[cfg(not(feature = "smtperf"))]
    fn assign_cost(&mut self, _: &Exp<Sym>) {}

    #[cfg(feature = "smtperf")]
    fn assign_cost(&mut self, exp: &Exp<Sym>) {
        let elapsed = self.start.elapsed();

        let mut edges = Vec::new();

        // Petgraph DFS requires a single root, so we add a dummy node
        // with edges to all the variables in the root expression.
        let root = self.vars.add_node((Sym::from_u32(u32::MAX), SourceLoc::unknown()));
        for var in exp.variables().iter() {
            let Some(in_frame) = self.var_nodes.get(&var) else { continue };
            edges.push(self.vars.update_edge(root, *in_frame, ()));
        }

        let mut dfs = Dfs::new(&self.vars, root);
        while let Some(node) = dfs.next(&self.vars) {
            if node != root {
                let (_, info) = self.vars.node_weight(node).unwrap();
                *self.time_per_location.entry(*info).or_insert(Duration::ZERO) += elapsed
            }
        }

        // Remove the edges and dummy root we added
        for edge in edges {
            self.vars.remove_edge(edge);
        }
        self.vars.remove_node(root);
    }

    #[cfg(not(feature = "smtperf"))]
    fn report_performance<P: AsRef<Path>>(&self, _: Option<P>, _: &[&str]) {}

    #[cfg(feature = "smtperf")]
    fn report_performance<P: AsRef<Path>>(&self, dir: Option<P>, files: &[&str]) {
        let mut times: Vec<(SourceLoc, Duration)> = Vec::new();

        for (&info, &duration) in self.time_per_location.iter() {
            if !info.is_unknown() {
                times.push((info, duration))
            }
        }

        times.sort_by(|(_, d1), (_, d2)| d2.cmp(d1));

        let mut msg = String::new();

        for (n, (info, duration)) in times.iter().enumerate() {
            if n >= 10 {
                break;
            }

            msg += &info.message(
                dir.as_ref(),
                files,
                &format!("#{} time: {}ms", n + 1, duration.as_millis()),
                false,
                true,
            );
            msg += "\n"
        }

        eprint!("{}", msg)
    }
}

#[cfg(test)]
thread_local! {
    pub(crate) static REPLAY_SOLVERS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static REPLAY_SMT_EVENTS: Cell<usize> = const { Cell::new(0) };
}

/// The Solver type handles all interaction with Z3. It mimics
/// interacting with Z3 via the subset of the SMTLIB 2.0 format we
/// care about.
///
/// For example:
/// ```
/// # use isla_lib::bitvector::b64::B64;
/// # use isla_lib::source_loc::SourceLoc;
/// # use isla_lib::smt::smtlib::Exp::*;
/// # use isla_lib::smt::smtlib::Def::*;
/// # use isla_lib::smt::smtlib::*;
/// # use isla_lib::smt::*;
/// # configure_tastic(Tactic::Qfaufbv);
/// # let x = Sym::from_u32(0);
/// let cfg = Config::new();
/// let ctx = Context::new(cfg);
/// let mut solver = Solver::<B64>::new(&ctx);
/// // (declare-const v0 Bool)
/// solver.add(DeclareConst(x, Ty::Bool));
/// // (assert v0)
/// solver.add(Assert(Var(x)));
/// // (check-sat)
/// assert!(solver.check_sat(SourceLoc::unknown()) == SmtResult::Sat)
/// ```
///
/// The other thing the Solver type does is maintain a trace of
/// interactions with Z3, which can be checkpointed and replayed by
/// another solver. This `Checkpoint` type is safe to be sent between
/// threads.
///
/// For example:
/// ```
/// # use isla_lib::bitvector::b64::B64;
/// # use isla_lib::source_loc::SourceLoc;
/// # use isla_lib::smt::smtlib::Exp::*;
/// # use isla_lib::smt::smtlib::Def::*;
/// # use isla_lib::smt::smtlib::*;
/// # use isla_lib::smt::*;
/// # configure_tastic(Tactic::Qfaufbv);
/// # let x = Sym::from_u32(0);
/// let point = {
///     let cfg = Config::new();
///     let ctx = Context::new(cfg);
///     let mut solver = Solver::<B64>::new(&ctx);
///     solver.add(DeclareConst(x, Ty::Bool));
///     solver.add(Assert(Var(x)));
///     solver.add(Assert(Not(Box::new(Var(x)))));
///     checkpoint(&mut solver)
/// };
/// let cfg = Config::new();
/// let ctx = Context::new(cfg);
/// let mut solver = Solver::from_checkpoint(&ctx, point);
/// assert!(solver.check_sat(SourceLoc::unknown()) == SmtResult::Unsat);
pub struct Solver<'ctx, B> {
    trace: Trace<B>,
    next_var: u32,
    def_attrs: DefAttrs,
    cycles: i128,
    decls: HashMap<Sym, ConstBinding<'ctx>>,
    sail_bitvectors: HashSet<Sym>,
    func_decls: HashMap<Sym, FuncDecl<'ctx>>,
    enums: Enums<'ctx>,
    z3_solver: Z3_solver,
    seed: Option<u32>,
    incremental_checks: bool,
    region_query: Option<query::RegionQuery<'ctx>>,
    floating_point_seen: Cell<bool>,
    ctx: &'ctx Context,
    symbol_namer: Z3SymbolNamer,
    performance_info: PerformanceInfo,
    /// 最后一次 check 以来新增的 `Def::Assert` 数量。用于判断 solver 里是否仍
    /// 持有"与当前断言集一致的 Sat 模型"（见 `take_stashed_model`）。
    asserts_since_check: usize,
    /// 最后一次 check（含 `check_sat_with` 的 assumption 查询）是否返回 Sat。
    last_check_sat: bool,
    knowledge: dedup::Knowledge,
    /// 活动区域尚未在出口验证；内部查询只允许返回 Unknown。
    deferred_region_queries: bool,
    ordinary_region_resume_queries: bool,
    boolean_proof_active: bool,
    deferred_assertions: Option<deferred_assertions::DeferredAssertions<B>>,
    /// 最近一次返回 Sat 的 check 所产生的模型（已 inc_ref）。断言集此后未变时
    /// 与当前状态一致，可直接取用而不必重解。注意 Z3 在后续 Unsat check 后会
    /// 丢弃自己的"最后模型"，所以必须由本侧缓存；`Def::Assert` 使其失效。
    stashed_model: Option<Z3_model>,
    shadow_witnesses: witness_shadow::Bank<'ctx>,
    savepoints: Vec<SolverSavepoint<'ctx, B>>,
    declaration_undo: Vec<DeclarationUndo<'ctx>>,
    // 批量错误叶认证独占的翻译器。每条断言在当时的符号绑定下冻结。
    replay_assertions: Option<Vec<Ast<'ctx>>>,
    // B 入口的可变断言后缀，在查询时与正文缓冲一起送入 Z3。
    arm_entry_assumptions: Vec<Ast<'ctx>>,
    replaying_arm_entry: bool,
    arm_body_enums: Option<Vec<Name>>,
    transaction_events: Vec<Event<B>>,
    finite_prefix: Option<finite_domain::PrefixIndex<'ctx>>,
    coi: Option<coi::Coi<'ctx>>,
    choice_dag: Option<finite_domain::IncrementalChoiceDag<'ctx>>,
    logical_arms: logical_arm::LogicalArms,
    // 与缓冲事件一一对应；不改变 Event，避免波及全部迹消费方。
    transaction_event_guards: Vec<Option<Exp<Sym>>>,
    committed_transaction_events: Vec<(Option<Exp<Sym>>, Event<B>)>,
    last_committed_transaction: Option<(SolverTransaction, usize)>,
    transaction_conditions: Vec<Exp<Sym>>,
    // 与条件栈对齐：None 已创建 native scope；Some 持有创建时绑定的延迟 guard。
    transaction_condition_scopes: Vec<Option<Ast<'ctx>>>,
}

impl<B> Drop for Solver<'_, B> {
    fn drop(&mut self) {
        unsafe {
            Z3_solver_dec_ref(self.ctx.z3_ctx, self.z3_solver);
            if let Some(model) = self.stashed_model.take() {
                Z3_model_dec_ref(self.ctx.z3_ctx, model);
            }
        }
    }
}

/// Interface for extracting information from Z3 models.
///
/// Model generation should be turned on in advance.  This is
/// currently Z3's default, but it's best to make sure:
///
/// ```
/// # use isla_lib::bitvector::b64::B64;
/// # use isla_lib::source_loc::SourceLoc;
/// # use isla_lib::smt::smtlib::Exp::*;
/// # use isla_lib::smt::smtlib::Def::*;
/// # use isla_lib::smt::smtlib::*;
/// # use isla_lib::smt::*;
/// # configure_tastic(Tactic::Qfaufbv);
/// # let x = Sym::from_u32(0);
/// let mut cfg = Config::new();
/// cfg.set_param_value("model", "true");
/// let ctx = Context::new(cfg);
/// let mut solver = Solver::<B64>::new(&ctx);
/// solver.add(DeclareConst(x, Ty::BitVec(4)));
/// solver.add(Assert(Bvsgt(Box::new(Var(x)), Box::new(Bits(vec![false,false,true,false])))));
/// assert!(solver.check_sat(SourceLoc::unknown()) == SmtResult::Sat);
/// let mut model = Model::new(&solver);
/// let var0 = model.get_var(x).unwrap().unwrap_exp();
/// ```
pub struct Model<'ctx, B> {
    z3_model: Z3_model,
    solver: &'ctx Solver<'ctx, B>,
    ctx: &'ctx Context,
    complete_model: bool,
    concrete_cache: HashMap<Sym, ModelVal>,
}

impl<B> Drop for Model<'_, B> {
    fn drop(&mut self) {
        unsafe {
            Z3_model_dec_ref(self.ctx.z3_ctx, self.z3_model);
        }
    }
}

// This implements Debug rather than Display because it displays the internal
// variable names (albeit with the same numbers that appear in the trace).
impl<B> fmt::Debug for Model<'_, B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unsafe {
            let z3_string = CStr::from_ptr(Z3_model_to_string(self.ctx.z3_ctx, self.z3_model));
            write!(f, "{}", z3_string.to_string_lossy())
        }
    }
}

#[derive(Clone, Debug)]
pub enum ModelVal {
    Arbitrary(Ty),
    Exp(Exp<Sym>),
}

impl ModelVal {
    pub fn unwrap_exp(self) -> Exp<Sym> {
        match self {
            ModelVal::Exp(e) => e,
            ModelVal::Arbitrary(_) => panic!("Attempting to unwrap arbitrary ModelVal"),
        }
    }

    pub fn is_arbitrary(&self) -> bool {
        matches!(self, ModelVal::Arbitrary(_))
    }
}

pub(crate) fn model_bits_to_bv<B: BV>(bits: &[bool]) -> Result<B, ExecError> {
    let width: u32 = bits.len().try_into().expect("模型位向量长度超出 u32");
    if width > B::MAX_WIDTH {
        return Err(ExecError::Type(
            format!("Cannot convert Bits with len={} to Val::Bits (exceeds MAX_WIDTH={})", width, B::MAX_WIDTH),
            SourceLoc::unknown(),
        ));
    }

    let mut bitvector = B::zeros(width);
    for (index, bit) in bits.iter().enumerate() {
        if *bit {
            bitvector = bitvector.set_slice(index.try_into().expect("模型位序超出 u32"), B::BIT_ONE);
        }
    }
    Ok(bitvector)
}

/// thread-interrupt wrapper 在 ModelEval 超时时构造最终 `SmtError::Z3Timeout`
/// 所需的调用边界信息。它不是另一套错误类型。
struct ModelEvalTimeoutContext {
    started: Instant,
    dump_request: SmtDumpRequest,
}

impl<'ctx, B: BV> Model<'ctx, B> {
    /// 借用当前断言集的缓存模型并持有独立引用，支持 Unsat 探测及保存点回滚后的取值。
    /// 调用前须有满足当前完整断言集的 Sat 见证，且尚未通过 take_stashed_model 取走缓存。
    /// 缺少模型是调用顺序错误，直接 panic，绝不向 Z3 索取可能已失效的最后模型。
    pub fn new(solver: &'ctx Solver<'ctx, B>) -> Self {
        unsafe {
            // 模型只能来自本侧缓存；Z3 的最后查询可能已被 Unsat 探测覆盖，
            // 保存点回滚也只恢复本侧引用。没有有效模型属于调用顺序错误。
            let z3_model = solver.stashed_model.expect("获取模型前必须完成 Sat 查询且未新增断言、未取走缓存");
            Z3_model_inc_ref(solver.ctx.z3_ctx, z3_model);
            Model { z3_model, solver, ctx: solver.ctx, complete_model: false, concrete_cache: HashMap::new() }
        }
    }

    pub fn set_complete_model(&mut self, b: bool) {
        if self.complete_model != b {
            self.concrete_cache.clear();
        }
        self.complete_model = b;
    }

    fn model_eval_timeout_error(&self, timeout: &ModelEvalTimeoutContext, limit: std::time::Duration) -> ExecError {
        let dump = timeout_dump_from_checkpoint(self.solver.checkpoint_snapshot(), timeout.dump_request.clone());
        ExecError::Smt(z3_timeout_error(
            SmtOperation::ModelEval,
            SourceLoc::unknown(),
            timeout.started.elapsed(),
            limit,
            dump,
        ))
    }

    fn eval_with_timeout(
        &self,
        ast: Z3_ast,
        model_completion: bool,
        result: &mut Z3_ast,
        timeout_context: &ModelEvalTimeoutContext,
    ) -> Result<bool, ExecError> {
        match timeout_Z3_model_eval(self.ctx.z3_ctx, self.z3_model, ast, model_completion, result, SourceLoc::unknown())
        {
            Ok(evaluated) => Ok(evaluated),
            Err(Z3TimeoutError::Interrupted(limit)) => Err(self.model_eval_timeout_error(timeout_context, limit)),
        }
    }

    #[allow(clippy::needless_range_loop)]
    fn get_large_bv_with_timeout(
        &mut self,
        ast: Ast,
        size: u32,
        timeout_context: &ModelEvalTimeoutContext,
    ) -> Result<Vec<bool>, ExecError> {
        let mut i = 0;
        let size = size.try_into().unwrap();
        let mut result = vec![false; size];
        while i < size {
            let hi = std::cmp::min(size, i + 64);
            let hi32: u32 = hi.try_into().unwrap();
            let extract_ast = ast.extract(hi32 - 1, i.try_into().unwrap());
            let result_ast: Ast;

            unsafe {
                let mut result_z3_ast: Z3_ast = ptr::null_mut();
                let evaluated =
                    self.eval_with_timeout(extract_ast.z3_ast, true, &mut result_z3_ast, timeout_context)?;
                if !evaluated {
                    return Err(self.ctx.error());
                }
                Z3_inc_ref(self.ctx.z3_ctx, result_z3_ast);
                result_ast = Ast { z3_ast: result_z3_ast, ctx: self.ctx };
            }
            let v = result_ast.get_numeral_u64()?;
            for j in i..hi {
                result[j] = (v >> (j - i) & 1) == 1;
            }
            i += 64;
        }
        Ok(result)
    }

    pub fn get_var(&mut self, var: Sym) -> Result<ModelVal, ExecError> {
        if let Some(value) = self.concrete_cache.get(&var) {
            return Ok(value.clone());
        }
        let var_ast = match self.solver.decls.get(&var) {
            None => return Err(ExecError::Type(format!("Unbound variable {:?}", &var), SourceLoc::unknown())),
            Some(binding) => binding.ast(),
        };
        let value = self.get_ast(var_ast, SmtDumpRequest::GetValues { expressions: vec![Exp::Var(var)] })?;
        if matches!(&value, ModelVal::Exp(Exp::Bits(_) | Exp::Bits64(_) | Exp::Bool(_) | Exp::Enum(_))) {
            self.concrete_cache.insert(var, value.clone());
        }
        Ok(value)
    }

    /// 只读取输出多样化支持的 enum、bool 和 bitvector；其它合法 SMT sort 不参与取值选择。
    pub fn get_finite_domain_var(&mut self, var: Sym) -> Result<Option<ModelVal>, ExecError> {
        let Some(binding) = self.solver.decls.get(&var) else {
            return Err(ExecError::Type(format!("Unbound variable {:?}", &var), SourceLoc::unknown()));
        };
        let sort_kind = unsafe { Z3_get_sort_kind(self.ctx.z3_ctx, binding.sort()) };

        match sort_kind {
            SortKind::Bool | SortKind::BV | SortKind::Datatype => {
                self.get_ast(binding.ast(), SmtDumpRequest::GetValues { expressions: vec![Exp::Var(var)] }).map(Some)
            }
            SortKind::Array | SortKind::FloatingPoint | SortKind::RoundingMode => Ok(None),
            _ => panic!("不支持的符号常量 sort: {:?}", sort_kind),
        }
    }

    pub fn get_exp(&mut self, exp: &Exp<Sym>) -> Result<ModelVal, ExecError> {
        let ast = self.solver.translate_exp(exp);
        self.get_ast(ast, SmtDumpRequest::GetValues { expressions: vec![exp.clone()] })
    }

    pub(crate) fn select_guarded<'a>(
        &mut self,
        guard: Sym,
        values: &'a (Val<B>, Val<B>),
    ) -> Result<&'a Val<B>, ExecError> {
        let Val::Bool(selected) = self.get_val(&Val::Symbolic(guard))? else {
            panic!("备选值的守卫必须为布尔值")
        };
        Ok(if selected { &values.0 } else { &values.1 })
    }

    pub fn get_val(&mut self, var: &Val<B>) -> Result<Val<B>, ExecError> {
        use crate::ir::Val::*;
        // 物化必须为自由变量补全模型，不能把未约简的 ITE 当作任意值。
        let complete_model = self.complete_model;
        self.complete_model = true;
        let result = (|| match var {
            SymBits { data, len, cap } => {
                let ModelVal::Exp(Exp::Bits(length)) = self.get_var(*len)? else {
                    panic!("符号长度必须是 128 位整数");
                };
                let length = crate::primop::i128_from_model_bits(&length).expect("长度必须能表示为整数");
                let length = usize::try_from(length).expect("长度必须非负");
                let bits = match self.get_var(*data)? {
                    ModelVal::Exp(Exp::Bits(bits)) => bits,
                    ModelVal::Exp(Exp::Bits64(bits)) => bits.to_vec(),
                    _ => panic!("符号长度位向量的承载数据必须是位向量"),
                };
                assert_eq!(bits.len(), *cap as usize);
                assert!(length <= bits.len() && bits[length..].iter().all(|bit| !bit));
                Ok(Val::from_bits_slice(&bits[..length]))
            }
            Guarded(guard, values) => {
                let selected = self.select_guarded(*guard, values)?;
                self.get_val(selected)
            }
            Symbolic(sym) => {
                let model_val = self.get_var(*sym)?;
                match model_val {
                    ModelVal::Exp(Exp::Bits64(bv)) => Ok(Val::Bits(B::new(bv.lower_u64(), bv.len()))),
                    ModelVal::Exp(Exp::Bool(b)) => Ok(Val::Bool(b)),
                    ModelVal::Exp(Exp::Enum(m)) => Ok(Val::Enum(m)),
                    ModelVal::Exp(Exp::Bits(bv)) => Ok(Val::from_bits_slice(&bv)),
                    ModelVal::Exp(exp) => {
                        // 对于其他复杂的表达式，返回错误
                        Err(ExecError::Type(
                            format!("Unsupported Exp type in get_val: {:?}", exp),
                            SourceLoc::unknown(),
                        ))
                    }
                    ModelVal::Arbitrary(ty) => match ty {
                        smtlib::Ty::BitVec(_) | smtlib::Ty::Bool => {
                            panic!("补全模型后仍无法物化标量：{sym:?}，{ty:?}")
                        }
                        smtlib::Ty::Enum(_) => Err(ExecError::Type(
                            format!("Cannot create default enum value for {:?}", ty),
                            SourceLoc::unknown(),
                        )),
                        _ => Err(ExecError::Type(
                            format!("Unsupported type in ModelVal::Arbitrary: {:?}", ty),
                            SourceLoc::unknown(),
                        )),
                    },
                }
            }
            I64(i) => Ok(I64(*i)),
            I128(i) => Ok(I128(*i)),
            Bool(b) => Ok(Bool(*b)),
            Bits(b) => Ok(Bits(*b)),
            String(s) => Ok(String(s.clone())),
            Unit => Ok(Unit),
            Enum(e) => Ok(Enum(*e)),
            Ref(n) => Ok(Ref(*n)),
            Poison => Ok(Poison),

            // 递归处理复合类型
            Vector(vals) => {
                let mut new_vals = Vec::with_capacity(vals.len());
                for val in vals {
                    new_vals.push(self.get_val(val)?);
                }
                Ok(Vector(new_vals))
            }

            List(vals) => {
                let mut new_vals = Vec::with_capacity(vals.len());
                for val in vals {
                    new_vals.push(self.get_val(val)?);
                }
                Ok(List(new_vals))
            }

            Struct(fields) => {
                let mut new_fields = ahash::HashMap::with_capacity_and_hasher(fields.len(), ahash::RandomState::new());
                for (name, val) in fields {
                    new_fields.insert(*name, self.get_val(&val)?);
                }
                Ok(Struct(new_fields))
            }

            Ctor(name, val) => Ok(Ctor(*name, Box::new(self.get_val(val)?))),

            MixedBits(segments) => {
                let mut new_segments = Vec::with_capacity(segments.len());
                for segment in segments {
                    match self.get_val(&Val::from(segment))? {
                        Bits(bv) => new_segments.push(crate::ir::BitsSegment::Concrete(bv)),
                        MixedBits(mut concrete) => new_segments.append(&mut concrete),
                        value => {
                            return Err(ExecError::Type(
                                format!("Unsupported value for BitsSegment: {:?}", value),
                                SourceLoc::unknown(),
                            ));
                        }
                    }
                }
                Ok(MixedBits(new_segments))
            }

            SymbolicCtor(sym, fields) => {
                let tag = match self.get_var(*sym)? {
                    ModelVal::Exp(Exp::Bits64(bits)) => {
                        assert_eq!(bits.len(), 32, "构造子标签必须为 32 位 Name");
                        bits.lower_u64() as u32
                    }
                    ModelVal::Exp(Exp::Bits(bits)) => {
                        assert_eq!(bits.len(), 32, "构造子标签必须为 32 位 Name");
                        bits.iter().enumerate().fold(0u32, |tag, (i, bit)| tag | (u32::from(*bit) << i))
                    }
                    value => panic!("构造子标签必须物化为 Name 位向量：{value:?}"),
                };
                let name = crate::ir::Name::from_u32(tag);
                let payload = fields.get(&name).expect("模型选择的构造子必须属于候选集");
                Ok(Ctor(name, Box::new(self.get_val(payload)?)))
            }
        })();
        self.complete_model = complete_model;
        result
    }

    // Requiring the model to be mutable as I expect Z3 will alter the underlying data
    fn get_ast(&mut self, var_ast: Ast, dump_request: SmtDumpRequest) -> Result<ModelVal, ExecError> {
        let started = Instant::now();
        let timeout_context = ModelEvalTimeoutContext { started, dump_request };
        self.get_ast_with_timeout(var_ast, &timeout_context)
    }

    fn get_ast_with_timeout(
        &mut self,
        var_ast: Ast,
        timeout_context: &ModelEvalTimeoutContext,
    ) -> Result<ModelVal, ExecError> {
        unsafe {
            let z3_ctx = self.ctx.z3_ctx;
            let mut z3_ast: Z3_ast = ptr::null_mut();
            let evaluated =
                self.eval_with_timeout(var_ast.z3_ast, self.complete_model, &mut z3_ast, timeout_context)?;
            if !evaluated {
                return Err(self.ctx.error());
            }
            Z3_inc_ref(z3_ctx, z3_ast);

            let ast = Ast { z3_ast, ctx: self.ctx };

            let sort = Z3_get_sort(z3_ctx, ast.z3_ast);
            Z3_inc_ref(z3_ctx, Z3_sort_to_ast(z3_ctx, sort));
            let sort_kind = Z3_get_sort_kind(z3_ctx, sort);

            let result = if sort_kind == SortKind::BV && Z3_is_numeral_ast(z3_ctx, z3_ast) {
                let size = Z3_get_bv_sort_size(z3_ctx, sort);
                if size > 64 {
                    let v = self.get_large_bv_with_timeout(ast, size, timeout_context)?;
                    Ok(ModelVal::Exp(Exp::Bits(v)))
                } else {
                    let result = ast.get_numeral_u64()?;
                    Ok(ModelVal::Exp(Exp::Bits64(B64::new(result, size))))
                }
            } else if sort_kind == SortKind::Bool {
                if let Some(b) = ast.get_bool_value() {
                    Ok(ModelVal::Exp(Exp::Bool(b)))
                } else {
                    // Model did not need to assign an interpretation to this variable
                    Ok(ModelVal::Arbitrary(Ty::Bool))
                }
            } else if sort_kind == SortKind::BV {
                let size = Z3_get_bv_sort_size(z3_ctx, sort);
                // Model did not need to assign an interpretation to this variable
                Ok(ModelVal::Arbitrary(Ty::BitVec(size)))
            } else if sort_kind == SortKind::Datatype {
                // Match enum constructors using the recognizer (tester) of
                // the MODEL VALUE'S OWN SORT — not from our registered enum.
                // This avoids all pointer-identity issues: the recognizer and
                // the value belong to the same sort object by construction.
                // We then map the constructor index back to our enum_id via
                // the deterministic Z3 sort symbol id.
                let n_ctors = Z3_get_datatype_sort_num_constructors(z3_ctx, sort);
                let mut ctor_idx: Option<usize> = None;

                for i in 0..n_ctors as usize {
                    let recognizer = Z3_get_datatype_sort_recognizer(z3_ctx, sort, i as c_uint);
                    let tester_app = Z3_mk_app(z3_ctx, recognizer, 1, &z3_ast);
                    Z3_inc_ref(z3_ctx, tester_app);
                    let mut eval_result: Z3_ast = ptr::null_mut();
                    let evaluated = match self.eval_with_timeout(tester_app, true, &mut eval_result, timeout_context) {
                        Ok(evaluated) => evaluated,
                        Err(error) => {
                            Z3_dec_ref(z3_ctx, tester_app);
                            return Err(error);
                        }
                    };
                    if !evaluated {
                        Z3_dec_ref(z3_ctx, tester_app);
                        continue;
                    }
                    Z3_dec_ref(z3_ctx, tester_app);
                    Z3_inc_ref(z3_ctx, eval_result);
                    let is_match = Z3_get_bool_value(z3_ctx, eval_result) == Z3_L_TRUE;
                    Z3_dec_ref(z3_ctx, eval_result);
                    if is_match {
                        ctor_idx = Some(i as usize);
                        break;
                    }
                }

                let result = match ctor_idx {
                    Some(idx) => {
                        // Map constructor index back to our EnumId via the
                        // deterministic Z3 sort symbol id.
                        let sort_name = Z3_get_sort_name(z3_ctx, sort);
                        if Z3_get_symbol_kind(z3_ctx, sort_name) != SymbolKind::Int {
                            let sort_str =
                                CStr::from_ptr(Z3_sort_to_string(z3_ctx, sort)).to_string_lossy().into_owned();
                            Err(ExecError::Type(
                                format!("get_ast: datatype sort has non-int symbol {}", sort_str),
                                SourceLoc::unknown(),
                            ))
                        } else {
                            let sort_id = Z3_get_symbol_int(z3_ctx, sort_name);
                            if sort_id < 0 {
                                Err(ExecError::Type(
                                    format!("get_ast: negative enum sort id {}", sort_id),
                                    SourceLoc::unknown(),
                                ))
                            } else {
                                let eid = Name::from_u32(sort_id as u32);
                                match self.solver.enums.enums.get(&eid) {
                                    Some(e) if idx < e.consts.len() => Ok(ModelVal::Exp(Exp::Enum(EnumMember {
                                        enum_id: EnumId { id: eid },
                                        member: idx,
                                    }))),
                                    Some(_) => Err(ExecError::Type(
                                        format!("get_ast: constructor {} out of range for enum {}", idx, eid),
                                        SourceLoc::unknown(),
                                    )),
                                    None => Err(ExecError::Type(
                                        format!("get_ast: no registered enum for sort id {}", sort_id),
                                        SourceLoc::unknown(),
                                    )),
                                }
                            }
                        }
                    }
                    None => {
                        let sort_str = CStr::from_ptr(Z3_sort_to_string(z3_ctx, sort)).to_string_lossy().into_owned();
                        Err(ExecError::Type(
                            format!("get_ast: no recognizer matched for sort={}", sort_str),
                            SourceLoc::unknown(),
                        ))
                    }
                };
                result
            } else {
                Err(ExecError::Type("get_ast: unsupported sort kind".to_string(), SourceLoc::unknown()))
            };

            Z3_dec_ref(z3_ctx, Z3_sort_to_ast(z3_ctx, sort));
            result
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SmtResult {
    Sat,
    Unsat,
    /// 可选证明或暂缓查询没有结论，调用方可以保留原符号表达式。
    Unproven(SmtError),
    Error(SmtError),
}

use SmtResult::*;

fn z3_query_error(
    source_loc: SourceLoc,
    wall: Duration,
    native_timeout: Option<Duration>,
    reason: String,
    rlimit_exhausted: bool,
) -> SmtError {
    let purpose = crate::executor::stats::region_progress::query_label();
    let mut query = Z3QueryFailure { source_loc, wall, limit: None, reason, purpose };
    match query.reason.trim() {
        "max. resource limit exceeded"
        | "(resource limits reached)"
        | "max. memory exceeded"
        | "out of memory"
        | "memout"
        | "max-conflicts-reached"
        | "max. scopes exceeded"
        | "max. steps exceeded"
        | "max. frames exceeded" => SmtError::Z3ResourceExhausted(query),
        "canceled" | "sat.canceled" if rlimit_exhausted => SmtError::Z3ResourceExhausted(query),
        "timeout" => {
            query.limit = native_timeout;
            SmtError::Z3Timeout(Z3Timeout::Native(query))
        }
        "interrupted" | "interrupted from keyboard" | "canceled" | "sat.canceled" => {
            SmtError::Z3Timeout(Z3Timeout::Native(query))
        }
        _ => SmtError::Z3Unknown(query),
    }
}

fn z3_reason_unknown(ctx: &Context, solver: Z3_solver) -> String {
    unsafe { CStr::from_ptr(Z3_solver_get_reason_unknown(ctx.z3_ctx, solver)).to_string_lossy().into_owned() }
}

#[cfg(test)]
pub(crate) mod test_queries {
    use super::{SolverOptions, SourceLoc};
    use std::cell::{Cell, RefCell};
    use std::collections::VecDeque;

    thread_local! {
        static OPTIONS: Cell<Option<SolverOptions>> = const { Cell::new(None) };
        static RESULTS: RefCell<VecDeque<Option<z3_sys::Z3_lbool>>> = const { RefCell::new(VecDeque::new()) };
        static OBSERVED_BRANCHES: RefCell<Option<ObservedBranches>> = const { RefCell::new(None) };
        static PURPOSES: RefCell<VecDeque<&'static str>> = const { RefCell::new(VecDeque::new()) };
    }

    pub(super) fn solver_options() -> Option<SolverOptions> {
        OPTIONS.get()
    }

    pub(crate) fn with_solver_options<T>(options: SolverOptions, run: impl FnOnce() -> T) -> T {
        struct Reset(Option<SolverOptions>);
        impl Drop for Reset {
            fn drop(&mut self) {
                OPTIONS.set(self.0);
            }
        }
        let _reset = Reset(OPTIONS.replace(Some(options)));
        run()
    }

    pub(crate) fn with_results<T>(
        results: impl IntoIterator<Item = Option<z3_sys::Z3_lbool>>,
        run: impl FnOnce() -> T,
    ) -> T {
        RESULTS.with(|slot| {
            assert!(slot.borrow().is_empty());
            slot.borrow_mut().extend(results);
        });
        struct Reset;
        impl Drop for Reset {
            fn drop(&mut self) {
                RESULTS.with(|slot| slot.borrow_mut().clear());
            }
        }
        let _reset = Reset;
        let result = run();
        RESULTS.with(|slot| assert!(slot.borrow().is_empty(), "部分注入查询未被消费"));
        result
    }

    pub(crate) fn with_unknown_purposes<T>(purposes: &[&'static str], run: impl FnOnce() -> T) -> T {
        PURPOSES.with(|slot| {
            assert!(slot.borrow().is_empty());
            slot.borrow_mut().extend(purposes);
        });
        struct Reset;
        impl Drop for Reset {
            fn drop(&mut self) {
                PURPOSES.with(|slot| slot.borrow_mut().clear());
            }
        }
        let _reset = Reset;
        let result = run();
        PURPOSES.with(|slot| assert!(slot.borrow().is_empty(), "部分注入查询未被消费：{:?}", slot.borrow()));
        result
    }

    #[derive(Default)]
    pub(crate) struct ObservedBranches {
        pub(crate) queried: Vec<SourceLoc>,
        pub(crate) rejected: Option<SourceLoc>,
        inject: Option<(usize, &'static str)>,
    }

    pub(crate) fn with_observed_branches<T>(inject: Option<usize>, run: impl FnOnce() -> T) -> (T, ObservedBranches) {
        with_observed_branch_failure(inject.map(|query| (query, "测试注入")), run)
    }

    pub(crate) fn with_observed_branch_failure<T>(
        inject: Option<(usize, &'static str)>,
        run: impl FnOnce() -> T,
    ) -> (T, ObservedBranches) {
        assert!(OBSERVED_BRANCHES.replace(Some(ObservedBranches { inject, ..Default::default() })).is_none());
        struct Reset;
        impl Drop for Reset {
            fn drop(&mut self) {
                OBSERVED_BRANCHES.take();
            }
        }
        let _reset = Reset;
        let result = run();
        (result, OBSERVED_BRANCHES.take().unwrap())
    }

    pub(super) fn take_unknown_reason(info: SourceLoc) -> Option<&'static str> {
        let label = crate::executor::stats::region_progress::query_label();
        if label == "branch_feasibility" && info != SourceLoc::unknown() {
            let reason = OBSERVED_BRANCHES.with_borrow_mut(|slot| {
                let observed = slot.as_mut()?;
                let sequence = observed.queried.len();
                observed.queried.push(info);
                let (_, reason) = observed.inject.filter(|(query, _)| *query == sequence)?;
                observed.rejected = Some(info);
                Some(reason)
            });
            if reason.is_some() {
                return reason;
            }
        }
        PURPOSES.with(|slot| {
            let mut list = slot.borrow_mut();
            if list.front().is_some_and(|purpose| *purpose == label) {
                list.pop_front();
                Some("测试注入")
            } else {
                None
            }
        })
    }

    pub(super) fn next() -> Option<z3_sys::Z3_lbool> {
        RESULTS.with(|slot| slot.borrow_mut().pop_front().flatten())
    }
}

impl SmtResult {
    pub fn is_sat(&self) -> Result<bool, ExecError> {
        match self {
            Sat => Ok(true),
            Unsat => Ok(false),
            Unproven(error) => Err(ExecError::Unproven(error.clone())),
            Error(error) => Err(ExecError::Smt(error.clone())),
        }
    }

    pub fn is_unsat(&self) -> Result<bool, ExecError> {
        match self {
            Sat => Ok(false),
            Unsat => Ok(true),
            Unproven(error) => Err(ExecError::Unproven(error.clone())),
            Error(error) => Err(ExecError::Smt(error.clone())),
        }
    }

    /// Z3 返回 UNDEF，且没有超时、中断或资源耗尽原因时为真。
    pub fn is_unknown(&self) -> bool {
        matches!(self, Unproven(SmtError::Z3Unknown(_)) | Error(SmtError::Z3Unknown(_)))
    }
}

struct SmtConfig {
    tactic: Tactic,
    seed_param: &'static CStr,
}

static SMT_CONFIG: OnceLock<SmtConfig> = OnceLock::new();

/// 在启动执行任务前显式初始化 SMT。相同配置可以重复传入，但只探测一次。
/// Z3 参数支持取决于版本及 tactic，因此按实际加载的库查询能力，不硬编码版本分界。
/// 不支持随机种子或试图更改已确定的 tactic 时直接终止。
pub fn configure_tastic(tactic: Tactic) {
    let config = SMT_CONFIG.get_or_init(|| {
        let version = z3_version();
        let ctx = Context::new(Config::new());
        unsafe {
            assert!(
                (0..Z3_get_num_tactics(ctx.z3_ctx))
                    .any(|i| CStr::from_ptr(Z3_get_tactic_name(ctx.z3_ctx, i)) == tactic.as_c_str()),
                "Z3 {version} 不存在 tactic {tactic:?}",
            );
            let solver = new_z3_solver(ctx.z3_ctx, tactic.as_c_str(), None);
            let descrs = Z3_solver_get_param_descrs(ctx.z3_ctx, solver);
            Z3_param_descrs_inc_ref(ctx.z3_ctx, descrs);
            let seed_param = [b"seed\0".as_slice(), b"random_seed\0".as_slice()]
                .into_iter()
                .map(|name| CStr::from_bytes_with_nul(name).unwrap())
                .find(|name| {
                    let exists = (0..Z3_param_descrs_size(ctx.z3_ctx, descrs)).any(|i| {
                        let symbol = Z3_param_descrs_get_name(ctx.z3_ctx, descrs, i);
                        Z3_get_symbol_kind(ctx.z3_ctx, symbol) == SymbolKind::String
                            && CStr::from_ptr(Z3_get_symbol_string(ctx.z3_ctx, symbol)) == *name
                    });
                    if !exists {
                        return false;
                    }
                    let symbol = Z3_mk_string_symbol(ctx.z3_ctx, name.as_ptr());
                    Z3_param_descrs_get_kind(ctx.z3_ctx, descrs, symbol) == ParamKind::UInt
                });
            Z3_param_descrs_dec_ref(ctx.z3_ctx, descrs);
            Z3_solver_dec_ref(ctx.z3_ctx, solver);
            let seed_param = seed_param
                .unwrap_or_else(|| panic!("Z3 {version} 的 tactic {tactic:?} 不支持随机种子参数 seed / random_seed"));
            SmtConfig { tactic, seed_param }
        }
    });
    assert_eq!(config.tactic, tactic, "SMT 已初始化，不能更改 tactic");
}

// 初始化能力探测与实际求解必须使用相同的 tactic 创建方式。
unsafe fn new_z3_solver(ctx: Z3_context, tactic: &CStr, seed: Option<(&CStr, u32)>) -> Z3_solver {
    let solver = if tactic == Tactic::Default.as_c_str() {
        let solver = Z3_mk_solver(ctx);
        Z3_solver_inc_ref(ctx, solver);
        solver
    } else {
        let solver_tactic = Z3_mk_tactic(ctx, tactic.as_ptr());
        Z3_tactic_inc_ref(ctx, solver_tactic);
        let solver = Z3_mk_solver_from_tactic(ctx, solver_tactic);
        Z3_solver_inc_ref(ctx, solver);
        Z3_tactic_dec_ref(ctx, solver_tactic);
        solver
    };
    if let Some((parameter, value)) = seed {
        let params = Z3_mk_params(ctx);
        Z3_params_inc_ref(ctx, params);
        Z3_params_set_uint(ctx, params, Z3_mk_string_symbol(ctx, parameter.as_ptr()), value);
        Z3_solver_set_params(ctx, solver, params);
        Z3_params_dec_ref(ctx, params);
    }
    solver
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    /// 同线程辅助求解可共享AST管理器；各Solver的断言仍相互独立。
    pub fn context(&self) -> &'ctx Context {
        self.ctx
    }

    pub fn new(ctx: &'ctx Context) -> Self {
        Self::new_with_symbol_namer(ctx, Z3SymbolNamer::Integer, None)
    }

    /// 为可复现的投影枚举显式设置种子；普通 Default 执行保留 Z3 默认参数。
    pub(crate) fn new_seeded(ctx: &'ctx Context, seed: u32) -> Self {
        Self::new_with_symbol_namer(ctx, Z3SymbolNamer::Integer, Some(seed))
    }

    fn new_with_symbol_namer(ctx: &'ctx Context, symbol_namer: Z3SymbolNamer, seed: Option<u32>) -> Self {
        #[cfg(test)]
        REPLAY_SOLVERS.set(REPLAY_SOLVERS.get() + 1);
        let config = SMT_CONFIG.get().expect("SMT 尚未初始化，请在程序启动时调用 smt::configure_tastic");
        unsafe {
            // Default 使用原生 solver，其余策略仍显式指定 tactic；均不按 logic 限制枚举支持。
            let seed = seed.or_else(|| (config.tactic != Tactic::Default).then(fresh_random_seed));
            let z3_solver =
                new_z3_solver(ctx.z3_ctx, config.tactic.as_c_str(), seed.map(|value| (config.seed_param, value)));

            Solver {
                ctx,
                z3_solver,
                seed,
                incremental_checks: false,
                region_query: None,
                floating_point_seen: Cell::new(false),
                next_var: 0,
                def_attrs: DefAttrs::default(),
                cycles: 0,
                trace: Trace::new(),
                decls: HashMap::new(),
                sail_bitvectors: HashSet::new(),
                func_decls: HashMap::new(),
                enums: Enums::new(ctx),
                symbol_namer,
                performance_info: PerformanceInfo::new(),
                asserts_since_check: 0,
                last_check_sat: false,
                knowledge: dedup::Knowledge::default(),
                deferred_region_queries: false,
                ordinary_region_resume_queries: false,
                boolean_proof_active: false,
                deferred_assertions: None,
                stashed_model: None,
                shadow_witnesses: witness_shadow::Bank::new(ctx),
                savepoints: Vec::new(),
                declaration_undo: Vec::new(),
                replay_assertions: None,
                arm_entry_assumptions: Vec::new(),
                replaying_arm_entry: false,
                arm_body_enums: None,
                transaction_events: Vec::new(),
                finite_prefix: ctx
                    .solver_options
                    .finite_domain_enumeration
                    .then(|| finite_domain::PrefixIndex::new(ctx)),
                coi: ctx.solver_options.coi_query_slicing.then(coi::Coi::default),
                choice_dag: ctx
                    .solver_options
                    .incremental_choice_dag
                    .then(|| finite_domain::IncrementalChoiceDag::new(ctx)),
                logical_arms: logical_arm::LogicalArms::default(),
                transaction_event_guards: Vec::new(),
                committed_transaction_events: Vec::new(),
                last_committed_transaction: None,
                transaction_conditions: Vec::new(),
                transaction_condition_scopes: Vec::new(),
            }
        }
    }

    pub fn report_performance<P: AsRef<Path>>(&self, dir: Option<P>, files: &[&str]) {
        self.performance_info.report_performance(dir, files)
    }

    pub fn fresh(&mut self) -> Sym {
        let n = self.next_var;
        self.next_var += 1;
        Sym { id: n }
    }

    pub(crate) fn arm_entry_checkpoint(&mut self) -> Checkpoint<B> {
        let mut entry = checkpoint(self);
        entry.cycles = self.cycles;
        entry
    }

    pub(crate) fn arm_context_options(&self) -> (SolverOptions, bool) {
        (self.ctx.solver_options, self.ctx.validation)
    }

    pub(crate) fn next_join_symbol(&self) -> u32 {
        self.next_var
    }

    /// 计划完成后预留定义编号，发布各步时可与正常事务产生的编号交错。
    pub(crate) fn reserve_join_symbols(&mut self, start: u32, end: u32) {
        assert_eq!(self.next_var, start, "汇合计划期间不得修改求解器");
        assert!(end >= start);
        self.next_var = end;
    }

    pub(crate) fn add_join_definition(&mut self, def: Def, bits: bool, info: SourceLoc) {
        if bits {
            self.with_def_attrs(self.def_attrs.sail_bitvector(), |solver| solver.add_with_location(def, info));
        } else {
            self.add_with_location(def, info);
        }
    }

    /// 翻译两个位向量操作数，位宽不同则在交给 Z3 之前 panic，并报出算子名、
    /// 两个位宽和被翻译的表达式（Z3 自身的 C 错误只给出排序，且直接结束进程）。
    fn translate_same_width_pair(&self, op: &str, lhs: &Exp<Sym>, rhs: &Exp<Sym>) -> (Ast<'ctx>, Ast<'ctx>) {
        let (left, right) = (self.translate_exp(lhs), self.translate_exp(rhs));
        let (left_width, right_width) = (left.bv_width(), right.bv_width());
        if left_width != right_width {
            panic!(
                "位向量操作数位宽不一致：{op} 的左操作数位宽 {left_width:?}，右操作数位宽 {right_width:?}；\
                 左 {:.300}；右 {:.300}",
                format!("{lhs:?}"),
                format!("{rhs:?}")
            );
        }
        (left, right)
    }

    fn translate_exp(&self, exp: &Exp<Sym>) -> Ast<'ctx> {
        let cost_scope =
            crate::executor::stats::region_cost::Scope::enter(crate::executor::stats::region_cost::Category::Translate);
        let _ = &cost_scope;
        crate::executor::stats::region_cost::count(crate::executor::stats::region_cost::Category::Translate, 1, 0);
        use Exp::*;
        if matches!(
            exp,
            FPConstant(..)
                | FPRoundingMode(..)
                | FPUnary(..)
                | FPRoundingUnary(..)
                | FPBinary(..)
                | FPRoundingBinary(..)
                | FPfma(..)
        ) {
            self.floating_point_seen.set(true);
        }
        let ast = match exp {
            Var(v) => match self.decls.get(v) {
                None => panic!("Could not get Z3 func_decl {}", *v),
                Some(binding) if self.replaying_arm_entry => return binding.raw_ast(),
                Some(binding) => binding.ast(),
            },
            Bits(bv) => Ast::mk_bv(self.ctx, bv.len().try_into().unwrap(), bv),
            Bits64(bv) => Ast::mk_bv_u64(self.ctx, bv.len(), bv.lower_u64()),
            Enum(e) => Ast::mk_enum_member(&self.enums, e.enum_id, e.member),
            Bool(b) => Ast::mk_bool(self.ctx, *b),
            Not(exp) => Ast::mk_not(&self.translate_exp(exp)),
            Eq(lhs, rhs) => Ast::mk_eq(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Neq(lhs, rhs) => {
                let equality = self.translate_exp(lhs).mk_eq(&self.translate_exp(rhs));
                rewrite::apply(equality, self.ctx.solver_options.bv_rewrite).mk_not()
            }
            And(lhs, rhs) => Ast::mk_and(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Or(lhs, rhs) => Ast::mk_or(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvnot(exp) => Ast::mk_bvnot(&self.translate_exp(exp)),
            Bvand(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvand", lhs, rhs);
                Ast::mk_bvand(&lhs, &rhs)
            }
            Bvor(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvor", lhs, rhs);
                Ast::mk_bvor(&lhs, &rhs)
            }
            Bvxor(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvxor", lhs, rhs);
                Ast::mk_bvxor(&lhs, &rhs)
            }
            Bvnand(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvnand", lhs, rhs);
                Ast::mk_bvnand(&lhs, &rhs)
            }
            Bvnor(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvnor", lhs, rhs);
                Ast::mk_bvnor(&lhs, &rhs)
            }
            Bvxnor(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvxnor", lhs, rhs);
                Ast::mk_bvxnor(&lhs, &rhs)
            }
            Bvneg(exp) => Ast::mk_bvneg(&self.translate_exp(exp)),
            Bvadd(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvadd", lhs, rhs);
                Ast::mk_bvadd(&lhs, &rhs)
            }
            Bvsub(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvsub", lhs, rhs);
                Ast::mk_bvsub(&lhs, &rhs)
            }
            Bvmul(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvmul", lhs, rhs);
                Ast::mk_bvmul(&lhs, &rhs)
            }
            Bvudiv(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvudiv", lhs, rhs);
                Ast::mk_bvudiv(&lhs, &rhs)
            }
            Bvsdiv(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvsdiv", lhs, rhs);
                Ast::mk_bvsdiv(&lhs, &rhs)
            }
            Bvurem(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvurem", lhs, rhs);
                Ast::mk_bvurem(&lhs, &rhs)
            }
            Bvsrem(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvsrem", lhs, rhs);
                Ast::mk_bvsrem(&lhs, &rhs)
            }
            Bvsmod(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvsmod", lhs, rhs);
                Ast::mk_bvsmod(&lhs, &rhs)
            }
            Bvult(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvult", lhs, rhs);
                Ast::mk_bvult(&lhs, &rhs)
            }
            Bvslt(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvslt", lhs, rhs);
                Ast::mk_bvslt(&lhs, &rhs)
            }
            Bvule(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvule", lhs, rhs);
                Ast::mk_bvule(&lhs, &rhs)
            }
            Bvsle(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvsle", lhs, rhs);
                Ast::mk_bvsle(&lhs, &rhs)
            }
            Bvuge(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvuge", lhs, rhs);
                Ast::mk_bvuge(&lhs, &rhs)
            }
            Bvsge(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvsge", lhs, rhs);
                Ast::mk_bvsge(&lhs, &rhs)
            }
            Bvugt(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvugt", lhs, rhs);
                Ast::mk_bvugt(&lhs, &rhs)
            }
            Bvsgt(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvsgt", lhs, rhs);
                Ast::mk_bvsgt(&lhs, &rhs)
            }
            Extract(hi, lo, bv) => self.translate_exp(bv).extract(*hi, *lo),
            ZeroExtend(i, bv) => self.translate_exp(bv).zero_extend(*i),
            SignExtend(i, bv) => self.translate_exp(bv).sign_extend(*i),
            Bvshl(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvshl", lhs, rhs);
                Ast::mk_bvshl(&lhs, &rhs)
            }
            Bvlshr(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvlshr", lhs, rhs);
                Ast::mk_bvlshr(&lhs, &rhs)
            }
            Bvashr(lhs, rhs) => {
                let (lhs, rhs) = self.translate_same_width_pair("bvashr", lhs, rhs);
                Ast::mk_bvashr(&lhs, &rhs)
            }
            Concat(lhs, rhs) => Ast::mk_concat(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Ite(cond, t, f) => self.translate_exp(cond).ite(&self.translate_exp(t), &self.translate_exp(f)),
            App(f, args) => {
                let args_ast: Vec<_> = args.iter().map(|arg| self.translate_exp(arg)).collect();
                match self.func_decls.get(f) {
                    None => panic!("Could not get Z3 func_decl {}", *f),
                    Some(fd) => Ast::mk_app(fd, &args_ast),
                }
            }
            Select(array, index) => Ast::mk_select(&self.translate_exp(array), &self.translate_exp(index)),
            Store(array, index, val) => {
                Ast::mk_store(&self.translate_exp(array), &self.translate_exp(index), &self.translate_exp(val))
            }
            Distinct(exps) => {
                let exps_ast: Vec<_> = exps.iter().map(|exp| self.translate_exp(exp)).collect();
                Ast::mk_distinct(self.ctx, &exps_ast)
            }
            &FPConstant(c, ebits, sbits) => {
                use smtlib::FPConstant::*;
                match c {
                    NaN => Ast::mk_fpa_nan(self.ctx, ebits, sbits),
                    Inf { negative } => Ast::mk_fpa_inf(self.ctx, ebits, sbits, negative),
                    Zero { negative } => Ast::mk_fpa_zero(self.ctx, ebits, sbits, negative),
                }
            }
            FPRoundingMode(rm) => {
                use smtlib::FPRoundingMode::*;
                match rm {
                    RoundNearestTiesToEven => Ast::mk_fpa_round_nearest_ties_to_even(self.ctx),
                    RoundNearestTiesToAway => Ast::mk_fpa_round_nearest_ties_to_away(self.ctx),
                    RoundTowardPositive => Ast::mk_fpa_round_toward_positive(self.ctx),
                    RoundTowardNegative => Ast::mk_fpa_round_toward_negative(self.ctx),
                    RoundTowardZero => Ast::mk_fpa_round_toward_zero(self.ctx),
                }
            }
            FPUnary(op, exp) => {
                use smtlib::FPUnary::*;
                match op {
                    Abs => Ast::mk_fpa_abs(&self.translate_exp(exp)),
                    Neg => Ast::mk_fpa_neg(&self.translate_exp(exp)),
                    IsNormal => Ast::mk_fpa_is_normal(&self.translate_exp(exp)),
                    IsSubnormal => Ast::mk_fpa_is_subnormal(&self.translate_exp(exp)),
                    IsZero => Ast::mk_fpa_is_zero(&self.translate_exp(exp)),
                    IsInfinite => Ast::mk_fpa_is_infinite(&self.translate_exp(exp)),
                    IsNaN => Ast::mk_fpa_is_nan(&self.translate_exp(exp)),
                    IsNegative => Ast::mk_fpa_is_negative(&self.translate_exp(exp)),
                    IsPositive => Ast::mk_fpa_is_positive(&self.translate_exp(exp)),
                    FromIEEE(ebits, sbits) => Ast::mk_fpa_to_fp_bv(&self.translate_exp(exp), *ebits, *sbits),
                    ToIEEE(..) => Ast::mk_fpa_to_ieee_bv(&self.translate_exp(exp)),
                }
            }
            FPRoundingUnary(op, rm, exp) => {
                use smtlib::FPRoundingUnary::*;
                match op {
                    Sqrt => Ast::mk_fpa_sqrt(&self.translate_exp(rm), &self.translate_exp(exp)),
                    RoundToIntegral => Ast::mk_fpa_round_to_integral(&self.translate_exp(rm), &self.translate_exp(exp)),
                    Convert(ebits, sbits) => {
                        Ast::mk_fpa_to_fp_float(&self.translate_exp(rm), &self.translate_exp(exp), *ebits, *sbits)
                    }
                    FromSigned(ebits, sbits) => {
                        Ast::mk_fpa_to_fp_signed(&self.translate_exp(rm), &self.translate_exp(exp), *ebits, *sbits)
                    }
                    FromUnsigned(ebits, sbits) => {
                        Ast::mk_fpa_to_fp_unsigned(&self.translate_exp(rm), &self.translate_exp(exp), *ebits, *sbits)
                    }
                    ToSigned(sz) => Ast::mk_fpa_to_sbv(&self.translate_exp(rm), &self.translate_exp(exp), *sz),
                    ToUnsigned(sz) => Ast::mk_fpa_to_ubv(&self.translate_exp(rm), &self.translate_exp(exp), *sz),
                }
            }
            FPBinary(op, lhs, rhs) => {
                use smtlib::FPBinary::*;
                match op {
                    Rem => Ast::mk_fpa_rem(&self.translate_exp(lhs), &self.translate_exp(rhs)),
                    Min => Ast::mk_fpa_min(&self.translate_exp(lhs), &self.translate_exp(rhs)),
                    Max => Ast::mk_fpa_max(&self.translate_exp(lhs), &self.translate_exp(rhs)),
                    Leq => Ast::mk_fpa_leq(&self.translate_exp(lhs), &self.translate_exp(rhs)),
                    Lt => Ast::mk_fpa_lt(&self.translate_exp(lhs), &self.translate_exp(rhs)),
                    Geq => Ast::mk_fpa_geq(&self.translate_exp(lhs), &self.translate_exp(rhs)),
                    Gt => Ast::mk_fpa_gt(&self.translate_exp(lhs), &self.translate_exp(rhs)),
                    Eq => Ast::mk_fpa_eq(&self.translate_exp(lhs), &self.translate_exp(rhs)),
                }
            }
            FPRoundingBinary(op, rm, lhs, rhs) => {
                use smtlib::FPRoundingBinary::*;
                match op {
                    Add => Ast::mk_fpa_add(&self.translate_exp(rm), &self.translate_exp(lhs), &self.translate_exp(rhs)),
                    Sub => Ast::mk_fpa_sub(&self.translate_exp(rm), &self.translate_exp(lhs), &self.translate_exp(rhs)),
                    Mul => Ast::mk_fpa_mul(&self.translate_exp(rm), &self.translate_exp(lhs), &self.translate_exp(rhs)),
                    Div => Ast::mk_fpa_div(&self.translate_exp(rm), &self.translate_exp(lhs), &self.translate_exp(rhs)),
                }
            }
            FPfma(rm, x, y, z) => Ast::mk_fpa_fma(
                &self.translate_exp(rm),
                &self.translate_exp(x),
                &self.translate_exp(y),
                &self.translate_exp(z),
            ),
        };
        rewrite::apply(ast, self.ctx.solver_options.bv_rewrite)
    }

    fn z3_assert(&mut self, exp: &Exp<Sym>) {
        let cost_scope = crate::executor::stats::region_cost::Scope::enter(
            crate::executor::stats::region_cost::Category::ReplayAssert,
        );
        let _ = &cost_scope;
        crate::executor::stats::region_cost::count(crate::executor::stats::region_cost::Category::ReplayAssert, 1, 0);
        let mut ast = self.translate_exp(exp);
        // B 臂的入口只需恢复等价的断言。原生求解器在消费这些 AST 时处理它们。
        if !self.replaying_arm_entry || self.replay_assertions.is_none() {
            ast.simplify();
        }
        if let Some(assertions) = &mut self.replay_assertions {
            assertions.push(ast);
        } else {
            unsafe { Z3_solver_assert(self.ctx.z3_ctx, self.z3_solver, ast.z3_ast) };
        }
    }

    pub fn get_enum(&mut self, id: Name, size: usize) -> EnumId {
        if let Some(enumeration) = self.enums.enums.get(&id) {
            assert_eq!(enumeration.consts.len(), size, "枚举类型的成员数量冲突");
        } else {
            self.add(Def::DefineEnum(id, size));
        }
        EnumId { id }
    }

    fn add_internal(&mut self, def: &Def, info: SourceLoc) {
        let cost_scope = crate::executor::stats::region_cost::Scope::enter(
            crate::executor::stats::region_cost::Category::Definitions,
        );
        let _ = &cost_scope;
        match &def {
            Def::Assert(exp) => {
                self.knowledge.constrain();
                self.asserts_since_check += 1;
                self.clear_stashed_model();
                if cfg!(feature = "smtperf") {
                    let vars = exp.variables();
                    for v1 in vars.iter() {
                        for v2 in vars.iter() {
                            if v1 != v2 {
                                self.performance_info.add_var_edge(v1, v2)
                            }
                        }
                    }
                }
                // 活动保存点只缓冲断言，查询通过 assumptions 看到它们；
                // Z3 push/pop 只承载臂条件，回滚不会留下臂内约束。
                if self.savepoints.is_empty() {
                    self.z3_assert(exp)
                }
            }
            Def::DeclareConst(v, ty) => {
                if query::floating_type(ty) {
                    self.floating_point_seen.set(true);
                }
                self.performance_info.add_var_node(*v, info);
                let fd = FuncDecl::new(self.ctx, *v, &self.enums, &[], ty, &self.symbol_namer);
                self.bind_constant(*v, ConstBinding::new(Ast::mk_constant(&fd), false, false));
                if self.def_attrs.attrs & 2 != 0 {
                    self.tag_bitvector(*v);
                }
            }
            Def::DeclareFun(v, arg_tys, result_ty) => {
                if arg_tys.iter().any(query::floating_type) || query::floating_type(result_ty) {
                    self.floating_point_seen.set(true);
                }
                if cfg!(feature = "smtperf") {
                    self.performance_info.add_var_node(*v, info);
                }
                let fd = FuncDecl::new(self.ctx, *v, &self.enums, arg_tys, result_ty, &self.symbol_namer);
                let previous = self.func_decls.insert(*v, fd);
                if previous.is_some() {
                    self.knowledge.constrain();
                    self.clear_stashed_model();
                }
                if self.tracks_declarations() {
                    self.declaration_undo.push(DeclarationUndo::Function(*v, previous));
                }
            }
            Def::DefineConst(v, exp) => {
                // DefineConst 将定义时翻译的表达式绑定到符号表，臂退出后仍可读取。
                // 提交发布定义日志，检查点重放按同样方式重建绑定。
                if cfg!(feature = "smtperf") {
                    self.performance_info.add_var_node(*v, info);
                    for used in exp.variables().iter() {
                        self.performance_info.add_var_edge(v, used);
                        self.performance_info.add_var_edge(used, v)
                    }
                }
                // 翻译时冻结操作数的绑定，重放保留未折叠的原始表达式。
                let ast = self.translate_exp(exp);
                let keep_replay = self.replaying_arm_entry && self.replay_assertions.is_some();
                let binding = ConstBinding::new(ast, true, keep_replay);
                self.bind_constant(*v, binding);
                if self.def_attrs.attrs & 2 != 0 {
                    self.tag_bitvector(*v);
                }
            }
            Def::DefineEnum(name, size) => {
                assert!(*size > 0, "枚举类型至少需要一个成员");
                if let Some(enumeration) = self.enums.enums.get(name) {
                    assert_eq!(enumeration.consts.len(), *size, "枚举类型的成员数量冲突");
                } else {
                    // Keep enum sort names deterministic across checkpoint replay.
                    // Member constructor names do not need to be stable: get_ast
                    // matches constructors through recognizers from the model
                    // value's own sort.
                    let members: Vec<Sym> = (0..*size).map(|_| self.fresh()).collect();
                    self.enums.add_enum(*name, &members, &self.symbol_namer);
                    if self.replay_assertions.is_some() {
                        self.declaration_undo.push(DeclarationUndo::ReplayEnum(*name));
                    } else if let Some(enums) = &mut self.arm_body_enums {
                        enums.push(*name);
                    }
                }
            }
        }
    }

    pub fn length(&self, v: Sym) -> Option<u32> {
        let sort = self.decls.get(&v)?.sort();
        let ctx = self.ctx.z3_ctx;
        unsafe { (Z3_get_sort_kind(ctx, sort) == SortKind::BV).then(|| Z3_get_bv_sort_size(ctx, sort)) }
    }

    pub fn is_bool(&self, v: Sym) -> bool {
        let sort = self.decls.get(&v).expect("布尔类型查询必须引用已声明符号").sort();
        unsafe { Z3_get_sort_kind(self.ctx.z3_ctx, sort) == SortKind::Bool }
    }

    /// 只读查询标量 sort，供原语准入和复合值结构检查复用。
    pub(crate) fn scalar_sort(&self, v: Sym) -> Option<Ty> {
        let sort = self.decls.get(&v)?.sort();
        unsafe {
            let ctx = self.ctx.z3_ctx;
            match Z3_get_sort_kind(ctx, sort) {
                SortKind::Bool => Some(Ty::Bool),
                SortKind::BV => Some(Ty::BitVec(Z3_get_bv_sort_size(ctx, sort))),
                SortKind::FloatingPoint => Some(Ty::Float(Z3_fpa_get_ebits(ctx, sort), Z3_fpa_get_sbits(ctx, sort))),
                SortKind::RoundingMode => Some(Ty::RoundingMode),
                SortKind::Datatype => self.enums.enums.iter().find_map(|(name, enumeration)| {
                    (enumeration.sort == sort).then_some(Ty::Enum(EnumId::from_name(*name)))
                }),
                _ => None,
            }
        }
    }

    pub fn is_bitvector(&mut self, v: Sym) -> bool {
        self.decls
            .get(&v)
            .is_some_and(|binding| unsafe { Z3_get_sort_kind(self.ctx.z3_ctx, binding.sort()) == SortKind::BV })
    }

    pub fn with_def_attrs<F, A>(&mut self, attrs: DefAttrs, f: F) -> A
    where
        F: FnOnce(&mut Self) -> A,
    {
        let old_attrs = self.def_attrs;
        self.def_attrs = attrs;
        let x = f(self);
        self.def_attrs = old_attrs;
        x
    }

    pub fn set_def_attrs(&mut self, attrs: DefAttrs) {
        self.def_attrs = attrs
    }

    pub fn clear_def_attrs(&mut self) {
        self.def_attrs = DefAttrs::default()
    }

    pub fn add(&mut self, def: Def) {
        self.add_with_location(def, SourceLoc::unknown());
    }

    pub fn add_with_location(&mut self, def: Def, info: SourceLoc) {
        self.add_event(Event::Smt(def, self.def_attrs, info));
    }

    pub fn declare_const(&mut self, ty: Ty, info: SourceLoc) -> Sym {
        let sym = self.fresh();
        self.add_with_location(Def::DeclareConst(sym, ty), info);
        sym
    }

    pub fn define_const(&mut self, exp: Exp<Sym>, info: SourceLoc) -> Sym {
        let sym = self.fresh();
        self.add_with_location(Def::DefineConst(sym, exp), info);
        sym
    }

    pub fn declare_bitvector(&mut self, width: u32, info: SourceLoc) -> Sym {
        self.with_def_attrs(self.def_attrs.sail_bitvector(), |solver| solver.declare_const(Ty::BitVec(width), info))
    }

    pub fn define_bitvector(&mut self, exp: Exp<Sym>, info: SourceLoc) -> Sym {
        self.with_def_attrs(self.def_attrs.sail_bitvector(), |solver| solver.define_const(exp, info))
    }

    fn tracks_declarations(&self) -> bool {
        !self.savepoints.is_empty() || self.replay_assertions.is_some()
    }

    fn bind_constant(&mut self, sym: Sym, binding: ConstBinding<'ctx>) {
        // 改绑可能改变缓冲断言的含义，清除已有见证。
        let previous = self.decls.insert(sym, binding);
        if previous.is_some() {
            self.knowledge.constrain();
            self.clear_stashed_model();
        }
        if self.tracks_declarations() {
            self.declaration_undo.push(DeclarationUndo::Constant(sym, previous));
        }
    }

    fn tag_bitvector(&mut self, sym: Sym) {
        if self.sail_bitvectors.insert(sym) && self.tracks_declarations() {
            self.declaration_undo.push(DeclarationUndo::Bitvector(sym));
        }
    }

    /// 标记已有位向量，并同步定义属性，使检查点重放保留类别。
    pub fn mark_bitvector(&mut self, sym: Sym) {
        assert!(self.length(sym).is_some(), "只能标记已定义的位向量");
        if self.is_sail_bitvector(sym) {
            return;
        }
        let defines_sym = |event: &Event<B>| matches!(event, Event::Smt(Def::DefineConst(v, _) | Def::DeclareConst(v, _), _, _) if *v == sym);
        if let Some(savepoint) = self.savepoints.last_mut() {
            if let Some(offset) = self.transaction_events[savepoint.events_len..].iter().rposition(defines_sym) {
                let index = savepoint.events_len + offset;
                self.invalidate_error_snapshot(index);
                let Event::Smt(_, attrs, _) = &mut self.transaction_events[index] else { unreachable!() };
                *attrs = attrs.sail_bitvector();
                self.tag_bitvector(sym);
            } else {
                // 不支持改写本层之外的定义属性：这会修改父层或已发布的日志，
                // 无法通过本层缓冲回滚。因此保留 invalid，而非拒绝普通 Assert。
                savepoint.invalid = true;
            }
            return;
        }
        let mut trace = &mut self.trace;
        loop {
            if let Some(Event::Smt(_, attrs, _)) = trace.head.iter_mut().rev().find(|event| defines_sym(event)) {
                *attrs = attrs.sail_bitvector();
                break;
            }
            if trace.projected.iter().flat_map(|s| s.iter()).any(defines_sym) {
                // 回放后的属性改写只作用于这条迹；其余错误叶仍持有冻结段。
                let mut head: Vec<_> = trace.projected.take().unwrap().iter().cloned().collect();
                let Event::Smt(_, attrs, _) = head.iter_mut().rev().find(|e| defines_sym(e)).unwrap() else {
                    unreachable!()
                };
                *attrs = attrs.sail_bitvector();
                head.append(&mut trace.head);
                trace.head = head;
                break;
            }
            if let Some(prefix) = &mut trace.head_prefix {
                if let Some(index) = prefix.events.iter().rposition(defines_sym) {
                    let Event::Smt(_, attrs, _) = &mut Arc::make_mut(prefix).events[index] else { unreachable!() };
                    *attrs = attrs.sail_bitvector();
                    break;
                }
            }
            trace = Arc::make_mut(&mut trace.tail).as_mut().expect("已定义符号必须存在于轨迹中");
        }
        self.tag_bitvector(sym);
    }

    pub fn is_sail_bitvector(&self, sym: Sym) -> bool {
        self.sail_bitvectors.contains(&sym)
    }

    pub fn choice(&mut self, exp1: Exp<Sym>, exp2: Exp<Sym>, info: SourceLoc) -> Sym {
        use Exp::*;
        let b = self.declare_const(Ty::Bool, info);
        self.define_const(Ite(Box::new(Var(b)), Box::new(exp1), Box::new(exp2)), info)
    }

    pub fn assert_eq(&mut self, lhs: Exp<Sym>, rhs: Exp<Sym>) {
        self.add(Def::Assert(Exp::Eq(Box::new(lhs), Box::new(rhs))))
    }

    pub fn assert(&mut self, exp: Exp<Sym>) {
        self.add(Def::Assert(exp))
    }

    pub fn cycle_count(&mut self) {
        self.cycles += 1;
        self.add_event(Event::Cycle);
        self.logical_arms.mark_cycle(self.transaction_events.len());
    }

    pub fn get_cycle_count(&self) -> i128 {
        self.cycles
    }

    fn add_event_internal(&mut self, event: &Event<B>) {
        if let Event::Smt(def, attrs, info) = event {
            #[cfg(test)]
            REPLAY_SMT_EVENTS.set(REPLAY_SMT_EVENTS.get() + 1);
            self.with_def_attrs(*attrs, |solver| solver.add_internal(def, *info))
        };
    }

    /// 保存点内的全部事件共用缓冲出口；只有最外层提交才发布到迹。
    pub fn add_event(&mut self, event: Event<B>) {
        let cost_scope = crate::executor::stats::region_cost::Scope::enter(
            crate::executor::stats::region_cost::Category::EventBuffer,
        );
        let _ = &cost_scope;
        self.add_event_internal(&event);
        if self.savepoints.is_empty() {
            if let Some(prefix) = &mut self.finite_prefix {
                prefix.push(self.trace.checkpoints, self.trace.head.len(), &event);
            }
            self.trace.head.push(event);
        } else if !matches!(&event, Event::Smt(..))
            || !self.transaction_invalid()
            || matches!(&event, Event::Smt(Def::DefineEnum(..), ..))
        {
            if let Some(prefix) = &mut self.finite_prefix {
                prefix.push(finite_domain::BUFFERED, self.transaction_events.len(), &event);
            }
            self.transaction_events.push(event);
            self.transaction_event_guards.push(None);
            self.logical_arms.record_event();
        } else if let Some(prefix) = &mut self.finite_prefix {
            // 即使失效保存点不记录 SMT 事件，add_event_internal 仍可能修改符号绑定。
            prefix.invalidate_candidates();
        }
    }

    pub fn trace_call(&mut self, name: Name) {
        self.add_event(Event::Function { name, call: true })
    }

    pub fn trace_return(&mut self, name: Name) {
        self.add_event(Event::Function { name, call: false })
    }

    // pub fn reset(&mut self, mut vars: HashSet<Sym, ahash::RandomState>) {
    //     let start = std::time::Instant::now();
    //     unsafe {
    //         Z3_solver_reset(self.ctx.z3_ctx, self.z3_solver)
    //     }

    //     let mut edges = Vec::new();
    //     let root = self.vars.add_node(Sym::from_u32(u32::MAX));
    //     for var in vars.iter().cloned().chain(self.memory_vars.iter().cloned()) {
    //         let Some(in_frame) = self.var_nodes.get(&var) else { continue };
    //         edges.push(self.vars.update_edge(root, *in_frame, ()));
    //     }

    //     let mut dfs = Dfs::new(&self.vars, root);
    //     while let Some(node) = dfs.next(&self.vars) {
    //         vars.insert(*self.vars.node_weight(node).unwrap());
    //     }

    //     let mut current_head = &self.trace.head;
    //     let mut current_tail = self.trace.tail.as_ref();
    //     let mut total = 0;
    //     let mut removed = 0;
    //     let mut totalv = 0;
    //     let mut removedv = 0;
    //     loop {
    //         'outer: for def in current_head.iter().rev() {
    //             match def {
    //                 Event::Smt(Def::Assert(exp), _, _) => {
    //                     total += 1;
    //                     for var in exp.variables() {
    //                         if vars.contains(&var) {
    //                             let ast = self.translate_exp(exp);
    //                             unsafe {
    //                                 Z3_solver_assert(self.ctx.z3_ctx, self.z3_solver, ast.z3_ast);
    //                             }
    //                             continue 'outer
    //                         }
    //                     }
    //                     removed += 1;
    //                 }
    //                 Event::Smt(Def::DeclareConst(v, _), _, _) => {
    //                     totalv += 1;
    //                     if !vars.contains(v) {
    //                         self.func_decls.remove(v);
    //                         removedv += 1;
    //                     }
    //                 }
    //                 _ => (),
    //             }
    //         }
    //         match current_tail {
    //             Some(trace) => {
    //                 current_head = &trace.head;
    //                 current_tail = trace.tail.as_ref();
    //             }
    //             None => break,
    //         }
    //     };

    //     for edge in edges {
    //         self.vars.remove_edge(edge);
    //     }
    //     self.vars.remove_node(root);

    //     self.reset_duration = self.reset_duration + start.elapsed();
    //     log!(log::VERBOSE, format!("Spent {:?} resetting {} {}", self.reset_duration, removed as f32 / total as f32, removedv as f32 / totalv as f32));
    // }

    fn replay(&mut self, num: usize, trace: Arc<Option<Trace<B>>>) {
        // Some extra work would be required to replay on top of
        // another trace, so until we need to do that we'll check it's
        // empty:
        assert!(self.trace.checkpoints == 0 && self.trace.head.is_empty());
        let mut checkpoints = Vec::with_capacity(num);
        let mut next = &*trace;
        loop {
            match next {
                None => break,
                Some(tr) => {
                    checkpoints.push(tr);
                    next = &*tr.tail
                }
            }
        }
        assert!(checkpoints.len() == num);
        for (segment, trace) in checkpoints.into_iter().rev().enumerate() {
            for (offset, event) in trace.head_events().enumerate() {
                self.add_event_internal(event);
                if let Some(prefix) = &mut self.finite_prefix {
                    prefix.push(segment, offset, event);
                }
            }
        }
        self.trace.checkpoints = num;
        self.trace.tail = trace
    }

    pub fn from_checkpoint(ctx: &'ctx Context, point: Checkpoint<B>) -> Self {
        Self::restore_checkpoint(ctx, point, false)
    }

    pub(crate) fn from_arm_checkpoint(ctx: &'ctx Context, point: Checkpoint<B>) -> Self {
        Self::restore_checkpoint(ctx, point, true)
    }

    fn restore_checkpoint(
        ctx: &'ctx Context,
        Checkpoint { num, next_var, trace, cycles }: Checkpoint<B>,
        arm_entry: bool,
    ) -> Self {
        let mut solver = Solver::new(ctx);
        // 入口重放只需恢复等价绑定与断言。臂开始后，仍在首次取值时化简定义。
        solver.replaying_arm_entry = arm_entry;
        solver.replay(num, trace);
        solver.replaying_arm_entry = false;
        solver.next_var = next_var;
        solver.cycles = cycles;
        solver
    }

    pub fn exploration_on_unknown(&self) -> Option<crate::config::PathFailureAction> {
        (!self.ctx.validation).then_some(self.ctx.solver_options.on_unknown)
    }

    pub fn branch_checks_skipped(&self) -> bool {
        self.ctx.solver_options.skip_branch_checks || self.no_smt()
    }

    pub fn check_sat_with(&mut self, exp: &Exp<Sym>, info: SourceLoc) -> SmtResult {
        self.check_sat_with_strategy(exp, info, query::QueryPurpose::General)
    }

    /// 已处理的范围条件无需立即发出反例查询。
    pub(crate) fn range_check_handled(&mut self, condition: &Exp<Sym>, info: SourceLoc) -> bool {
        matches!(condition, Exp::Bool(true))
            || self.defer_safety_check(
                condition,
                crate::config::RegionOptions::current().defer_range_proofs,
                "range_obligation",
                info,
            )
            || self.no_smt_safety(condition, info)
    }

    /// 整数转换及向量边界证明复用完整查询与超时机制；default使用同Config/种子的新solver。
    /// 活动臂条件、已发布断言和缓冲断言全部保留，Sat也仍是原上下文的反例。
    pub(crate) fn check_sat_with_for_range(&mut self, exp: &Exp<Sym>, info: SourceLoc) -> SmtResult {
        self.check_sat_with_strategy(exp, info, query::QueryPurpose::RangeProof)
    }

    /// 布尔恒值及推演可行性证明：复杂目标按成本选择完整快照，其余复用原查询。
    pub(crate) fn check_sat_with_for_bool(&mut self, exp: &Exp<Sym>, info: SourceLoc) -> SmtResult {
        if self.ctx.solver_options.skip_bool_proofs || (self.no_smt() && !self.ctx.solver_options.keep_bool_proofs) {
            return Unproven(SmtError::DeferredQuery { source_loc: info, purpose: "boolean_proof" });
        }
        let previous = self.deferred_region_queries;
        let active = self.boolean_proof_active;
        if self.no_smt() {
            self.deferred_region_queries = false;
            self.boolean_proof_active = true;
        }
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.check_sat_with_strategy(exp, info, query::QueryPurpose::BooleanProof)
        }));
        self.deferred_region_queries = previous;
        self.boolean_proof_active = active;
        match result {
            Ok(value) => value,
            Err(error) => std::panic::resume_unwind(error),
        }
    }

    fn check_sat_with_strategy(&mut self, exp: &Exp<Sym>, info: SourceLoc, purpose: query::QueryPurpose) -> SmtResult {
        let label = match purpose {
            query::QueryPurpose::General => "general",
            query::QueryPurpose::RangeProof => "range_proof",
            query::QueryPurpose::BooleanProof => "boolean_proof",
            query::QueryPurpose::BranchFeasibility => "branch_feasibility",
        };
        if self.no_smt() && !matches!(purpose, query::QueryPurpose::BooleanProof) {
            return Error(self.no_smt_cannot_continue("mandatory_query", info));
        }
        if self.deferred_region_queries
            && (!self.ordinary_region_resume_queries || matches!(purpose, query::QueryPurpose::BooleanProof))
        {
            if !matches!(purpose, query::QueryPurpose::BooleanProof) {
                self.note_deferred_mandatory_query(label, info, true);
            }
            return Unproven(SmtError::DeferredQuery { source_loc: info, purpose: label });
        }
        let query_scope = crate::executor::stats::region_progress::QueryScope::fallback(label);
        #[cfg(test)]
        if let Some(reason) = test_queries::take_unknown_reason(info) {
            return Error(z3_query_error(info, Duration::ZERO, None, reason.into(), false));
        }

        let proof_limit = if matches!(&purpose, query::QueryPurpose::BooleanProof) && self.transaction_depth() > 0 {
            proof_budget::limit()
        } else {
            None
        };
        let started = Instant::now();
        self.performance_info.start();

        // 先做无上下文的等价化简，恒假目标不必反复求解整个路径。
        // 恒真目标仍检查当前断言集，不能把不可满足的路径当作 Sat。
        let translation = WorkTimer::start(WorkKind::TargetTranslate);
        let mut ast = self.translate_exp(exp);
        ast.simplify();
        drop(translation);
        if let Some(value) = ast.get_bool_value().filter(|value| !*value || proof_limit.is_none()) {
            let result = if value {
                self.check_sat(info)
            } else {
                self.last_check_sat = false;
                self.asserts_since_check = 0;
                Unsat
            };
            self.performance_info.assign_cost(exp);
            return result;
        }

        // 已有见证满足当前全部已发布及缓冲断言。仅在同一见证把新增条件
        // 求值为 true 时复用 Sat；false 或非具体结果仍走完整求解，绝不据此判 Unsat。
        {
            match self.cached_bool_value(exp) {
                Ok(Some(true)) => {
                    self.last_check_sat = true;
                    self.asserts_since_check = 0;
                    self.performance_info.assign_cost(exp);
                    return Sat;
                }
                Ok(_) => (),
                Err(ExecError::Smt(error)) => return Error(error),
                Err(error) => panic!("布尔条件模型求值失败: {error}"),
            }
        }

        let pending = self.transaction_assertions();
        let mut assumptions: Vec<_> = pending.iter().map(|ast| ast.z3_ast).collect();
        assumptions.push(ast.z3_ast);
        if self.witness_fast_sat(&assumptions) {
            self.knowledge.literal = dedup::literal(exp);
            self.performance_info.assign_cost(exp);
            return Sat;
        }
        let query = if let Some(limit) = proof_limit {
            let setup = WorkTimer::start(WorkKind::QuerySetup);
            let query = self.independent_query(&assumptions, Some(limit));
            drop(setup);
            query
        } else {
            self.query_solver(&assumptions, purpose.requests_snapshot(self, &ast))
        };
        let diagnostic_dump = self.diagnostic_query_dump(exp);
        let diagnostic_pair = diagnostic_dump.as_ref().is_some_and(dump::wants_same_context_pair);
        let diagnostic_before = diagnostic_pair.then(|| self.diagnostic_solver_stats(query.z3_solver));
        let shadow = self.shadow_probe(query.z3_solver, query.assumptions(&assumptions));
        let budget_profile = if matches!(&purpose, query::QueryPurpose::BooleanProof) && self.transaction_depth() > 0 {
            proof_budget::Token::begin(self.ctx, query.z3_solver, proof_limit)
        } else {
            None
        };
        let diagnostic_started = diagnostic_dump.as_ref().map(|_| Instant::now());
        let slow_query = self.slow_query_begin(query.z3_solver);
        let resource_budget = query.resource_budget(proof_limit);
        let check_started = Instant::now();
        let z3_result = match timeout_Z3_solver_check_assumptions(
            self.ctx.z3_ctx,
            query.z3_solver,
            query.assumptions(&assumptions),
            info,
        ) {
            Ok(result) => result,
            Err(Z3TimeoutError::Interrupted(limit)) => {
                if let Some(profile) = budget_profile {
                    profile.finish(Z3_L_UNDEF);
                }
                if let Some(shadow) = shadow {
                    shadow.finish(Z3_L_UNDEF);
                }
                // 超时中断不改断言集：既有缓存模型（若有）仍满足当前断言，保持有效。
                self.last_check_sat = false;
                self.asserts_since_check = 0;
                let dump =
                    timeout_dump_from_checkpoint(self.checkpoint_snapshot(), SmtDumpRequest::CheckSatWith(exp.clone()));
                return Error(z3_timeout_error(SmtOperation::CheckSatAssuming, info, started.elapsed(), limit, dump));
            }
        };
        let check_elapsed = check_started.elapsed();
        self.slow_query_finish(slow_query, query.z3_solver, Some(exp), info, z3_result);
        if let Some(profile) = budget_profile {
            profile.finish(z3_result);
        }
        if let Some(shadow) = shadow {
            shadow.finish(z3_result);
        }
        if let Some(mut point) = diagnostic_dump {
            point["kind"] = serde_json::json!("query_replay_result");
            point["check_milliseconds"] =
                serde_json::json!(diagnostic_started.unwrap().elapsed().as_secs_f64() * 1000.0);
            point["result"] = serde_json::json!(if z3_result == Z3_L_TRUE {
                "sat"
            } else if z3_result == Z3_L_FALSE {
                "unsat"
            } else {
                "unknown"
            });
            if diagnostic_pair {
                point["original_statistics_before"] = diagnostic_before.unwrap();
                point["original_statistics_after"] = self.diagnostic_solver_stats(query.z3_solver);
                point["original_uses_main_solver"] = serde_json::json!(query.z3_solver == self.z3_solver);
                point["fresh_same_context"] =
                    self.diagnostic_fresh_query(query.z3_solver, query.assumptions(&assumptions), 1000);
            }
            eprintln!("{point}");
        }
        let result = if z3_result == Z3_L_TRUE {
            Sat
        } else if z3_result == Z3_L_FALSE {
            Unsat
        } else {
            let error = query.failure(info, check_elapsed, resource_budget);
            // 显式限额只约束可选折叠，耗尽时保留原布尔表达式。
            if proof_limit.is_some() {
                Unproven(error)
            } else {
                Error(error)
            }
        };

        self.record_check_result(&result, query.z3_solver);
        if matches!(result, Sat) {
            self.knowledge.literal = dedup::literal(exp);
        }
        self.performance_info.assign_cost(exp);
        drop(query_scope);
        result
    }

    pub fn trace(&self) -> &Trace<B> {
        &self.trace
    }

    pub fn check_sat(&mut self, info: SourceLoc) -> SmtResult {
        if self.no_smt() && !self.boolean_proof_active {
            return Error(self.no_smt_cannot_continue("model_or_general_query", info));
        }
        if self.deferred_region_queries && !self.ordinary_region_resume_queries {
            self.note_deferred_mandatory_query("model_or_general", info, true);
            return Unproven(SmtError::DeferredQuery { source_loc: info, purpose: "model_or_general" });
        }
        let query_scope = crate::executor::stats::region_progress::QueryScope::fallback("arm_close_or_general");
        // 模型缓存由新增断言、臂条件及提交/回滚统一维护，仍有效即有 Sat 见证。
        if self.has_stashed_model() {
            self.last_check_sat = true;
            self.asserts_since_check = 0;
            return Sat;
        }
        let started = Instant::now();
        let pending = self.transaction_assertions();
        let assumptions: Vec<_> = pending.iter().map(|ast| ast.z3_ast).collect();
        if self.witness_fast_sat(&assumptions) {
            return Sat;
        }
        let query = self.query_solver(&assumptions, false);
        let shadow = self.shadow_probe(query.z3_solver, query.assumptions(&assumptions));
        let slow_query = self.slow_query_begin(query.z3_solver);
        let resource_budget = query.resource_budget(None);
        let check_started = Instant::now();
        let z3_result =
            match timeout_Z3_solver_check(self.ctx.z3_ctx, query.z3_solver, query.assumptions(&assumptions), info) {
                Ok(result) => result,
                Err(Z3TimeoutError::Interrupted(limit)) => {
                    if let Some(shadow) = shadow {
                        shadow.finish(Z3_L_UNDEF);
                    }
                    // 超时中断不改断言集：既有缓存模型（若有）仍满足当前断言，保持有效。
                    self.last_check_sat = false;
                    self.asserts_since_check = 0;
                    let dump = timeout_dump_from_checkpoint(self.checkpoint_snapshot(), SmtDumpRequest::CheckSat);
                    return Error(z3_timeout_error(SmtOperation::CheckSat, info, started.elapsed(), limit, dump));
                }
            };
        if let Some(shadow) = shadow {
            shadow.finish(z3_result);
        }
        let result = if z3_result == Z3_L_TRUE {
            Sat
        } else if z3_result == Z3_L_FALSE {
            Unsat
        } else {
            Error(query.failure(info, check_started.elapsed(), resource_budget))
        };
        self.slow_query_finish(slow_query, query.z3_solver, None, info, z3_result);
        self.record_check_result(&result, query.z3_solver);
        drop(query_scope);
        result
    }

    /// 记录一次 check 的结果：Sat 时缓存其模型（断言未变前可复用，见
    /// `take_stashed_model`）；同时重置断言计数。Unsat/Unknown 不会让既有
    /// 缓存失效——缓存模型满足的是当前断言集（自缓存以来没有新增
    /// `Def::Assert`），与这次探测的假设和结果无关。
    fn record_check_result(&mut self, result: &SmtResult, queried_solver: Z3_solver) {
        self.last_check_sat = matches!(result, Sat);
        self.asserts_since_check = 0;
        if self.last_check_sat {
            self.knowledge.sat = true;
            unsafe {
                let model = Z3_solver_get_model(self.ctx.z3_ctx, queried_solver);
                if !model.is_null() {
                    Z3_model_inc_ref(self.ctx.z3_ctx, model);
                    self.clear_stashed_model();
                    self.stashed_model = Some(model);
                    if witness_shadow::enabled() {
                        self.shadow_witnesses.remember(model);
                    }
                }
            }
        }
    }

    fn clear_stashed_model(&mut self) {
        if let Some(model) = self.stashed_model.take() {
            unsafe { Z3_model_dec_ref(self.ctx.z3_ctx, model) }
        }
    }

    /// 最后一次 check 以来新增的 `Def::Assert` 数量（诊断/日志用）。
    pub fn asserts_since_check(&self) -> usize {
        self.asserts_since_check
    }

    /// 是否持有满足当前完整断言集的 Sat 见证；提交弱化约束时也可以保留。
    pub fn has_stashed_model(&self) -> bool {
        self.stashed_model.is_some()
    }

    /// 当前完整断言集的有效见证对布尔条件的取值；未解释变量不是假命题。
    pub(crate) fn cached_bool_value(&self, exp: &Exp<Sym>) -> Result<Option<bool>, ExecError> {
        if !self.has_stashed_model() {
            return Ok(None);
        }
        Ok(match Model::new(self).get_exp(exp)? {
            ModelVal::Exp(Exp::Bool(value)) => Some(value),
            _ => None,
        })
    }

    /// 最后一次 check 是否返回 Sat（诊断/日志用）。
    pub fn last_check_was_sat(&self) -> bool {
        self.last_check_sat
    }

    /// 取出缓存的"最近一次 Sat check"模型（所有权转移，取出后缓存为空）。
    ///
    /// 自那次 Sat check 后没有新增 `Def::Assert` 时，该模型满足当前全部
    /// 断言（`check_sat_with` 的 assumption 只会额外收紧），可直接用于取值
    /// 而不必重解。这是 `Z3_solver_get_model` 语义的强化版：后续 Unsat 探测
    /// （如 `__monomorphize` 的唯一性探测）会让 Z3 丢弃它自己的"最后模型"，
    /// 但不会使本缓存失效。
    pub fn take_stashed_model(&mut self) -> Option<Model<'_, B>> {
        // Z3_model 是裸指针（Copy），必须用 take() 真正移出，避免字段残留导致
        // 重复取出、双重 dec_ref。
        let model = self.stashed_model.take()?;
        Some(Model {
            z3_model: model,
            solver: &*self,
            ctx: self.ctx,
            complete_model: false,
            concrete_cache: HashMap::new(),
        })
    }

    /// 带独立时间盒的 `check_sat`：deadline 到期后软中断 Z3 并返回超时错误。
    ///
    /// 与 `--smt-timeout` 的全局单次 operation 上限相互独立，供"路径终值
    /// 物化"这类需要单独预算的查询使用。未启用 `smt-thread-interrupt`
    /// feature 时无法中断 Z3，退化为普通 `check_sat`（deadline 不生效，
    /// 与 `--smt-timeout` 在该构建下的既有行为一致）。
    pub fn check_sat_deadline(&mut self, info: SourceLoc, deadline: Duration) -> SmtResult {
        if self.no_smt() && !self.boolean_proof_active {
            return Error(self.no_smt_cannot_continue("model_query_deadline", info));
        }
        if self.deferred_region_queries && !self.ordinary_region_resume_queries {
            self.note_deferred_mandatory_query("model_or_general", info, true);
            return Unproven(SmtError::DeferredQuery { source_loc: info, purpose: "model_or_general" });
        }
        let started = Instant::now();
        let pending = self.transaction_assertions();
        let assumptions: Vec<_> = pending.iter().map(|ast| ast.z3_ast).collect();
        if self.witness_fast_sat(&assumptions) {
            return Sat;
        }
        let query = self.query_solver(&assumptions, false);
        let shadow = self.shadow_probe(query.z3_solver, query.assumptions(&assumptions));
        let _query_scope = crate::executor::stats::region_progress::QueryScope::fallback("terminal_model");
        let resource_budget = query.resource_budget(None);
        let check_started = Instant::now();
        let z3_result = match timeout_Z3_solver_check_deadline(
            self.ctx.z3_ctx,
            query.z3_solver,
            query.assumptions(&assumptions),
            info,
            deadline,
        ) {
            Ok(result) => result,
            Err(Z3TimeoutError::Interrupted(limit)) => {
                if let Some(shadow) = shadow {
                    shadow.finish(Z3_L_UNDEF);
                }
                // 超时中断不改断言集：既有缓存模型（若有）仍满足当前断言，保持有效。
                self.last_check_sat = false;
                self.asserts_since_check = 0;
                let dump = timeout_dump_from_checkpoint(self.checkpoint_snapshot(), SmtDumpRequest::CheckSat);
                return Error(z3_timeout_error(SmtOperation::CheckSat, info, started.elapsed(), limit, dump));
            }
        };
        if let Some(shadow) = shadow {
            shadow.finish(z3_result);
        }
        let result = if z3_result == Z3_L_TRUE {
            Sat
        } else if z3_result == Z3_L_FALSE {
            Unsat
        } else {
            Error(query.failure(info, check_started.elapsed(), resource_budget))
        };
        self.record_check_result(&result, query.z3_solver);
        result
    }

    /// 输出当前求解器的声明与断言，供外部工具重放。
    pub fn write_smtlib(&self, mut output: impl Write) -> std::io::Result<()> {
        unsafe {
            let text = Z3_solver_to_string(self.ctx.z3_ctx, self.z3_solver);
            output.write_all(CStr::from_ptr(text).to_bytes())
        }
    }

    pub fn dump_solver(&mut self, filename: &str) {
        let file = std::fs::File::create(filename).expect("Failed to open solver dump file");
        self.write_smtlib(file).expect("Failed to write solver dump");
    }

    pub fn dump_solver_with(&mut self, filename: &str, exp: &Exp<Sym>) {
        let mut file = std::fs::File::create(filename).expect("Failed to open solver dump file");
        unsafe {
            let s = Z3_solver_to_string(self.ctx.z3_ctx, self.z3_solver);
            let cs = CStr::from_ptr(s);
            file.write_all(cs.to_bytes()).expect("Failed to write solver dump");
            writeln!(file, "{}", self.exp_to_str(exp)).expect("Failed to write exp");
        }
    }

    pub fn exp_to_str(&mut self, exp: &Exp<Sym>) -> String {
        let ast = self.translate_exp(exp);
        let cs;
        unsafe {
            let s = Z3_ast_to_string(ast.ctx.z3_ctx, ast.z3_ast);
            cs = CStr::from_ptr(s);
        }
        cs.to_string_lossy().to_string()
    }
}

/// 清空当前线程的路径级 SMT 统计。
pub fn reset_path_smt_stats() {
    z3_timeout::reset_path_smt_stats()
}

/// 当前线程正在执行的这条路径迄今为止的 SMT 调用统计。
pub fn path_smt_stats() -> crate::timeout::SmtCallStats {
    z3_timeout::path_smt_stats()
}

/// 恢复某条已调度路径的 SMT 统计快照。
pub fn restore_path_smt_stats(stats: crate::timeout::SmtCallStats) {
    z3_timeout::restore_path_smt_stats(stats)
}

/// 单次 SMT 调用的实际限时。线程中断构建缺省 60 秒，直接调用构建无单次限时。
pub fn configured_smt_operation_timeout() -> Option<std::time::Duration> {
    z3_timeout::configured_operation_timeout()
}

pub(crate) fn take_smtperf_report() -> Option<String> {
    #[cfg(feature = "smtperf")]
    {
        Some(z3_timeout::take_smtperf_report())
    }
    #[cfg(not(feature = "smtperf"))]
    None
}

pub fn checkpoint<B: BV>(solver: &mut Solver<B>) -> Checkpoint<B> {
    assert!(solver.savepoints.is_empty(), "普通任务检查点需要关闭全部保存点");
    solver.last_committed_transaction = None;
    solver.committed_transaction_events.clear();
    solver.trace.checkpoint(solver.next_var)
}

/// This function just calls Z3_finalize_memory(). It's useful because
/// by calling it before we exit, we can check whether we are leaking
/// memory while interacting with Z3 objects.
///
/// # Safety
///
/// Shoud only be called just before exiting.
pub unsafe fn finalize_solver() {
    Z3_finalize_memory()
}

pub fn z3_version() -> String {
    let cs;
    unsafe {
        let s = Z3_get_full_version();
        cs = CStr::from_ptr(s);
    }
    cs.to_string_lossy().to_string()
}

#[cfg(test)]
mod arithmetic_tests;
#[cfg(test)]
mod division_tests;
#[cfg(test)]
mod multiplication_tests;
#[cfg(test)]
mod query_tests;

#[cfg(test)]
mod tests {
    #[test]
    fn native_default_uses_plain_solver_and_models() {
        const CHILD: &str = "ISLA_NATIVE_DEFAULT_TEST_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "smt::tests::native_default_uses_plain_solver_and_models", "--nocapture"])
                .env(CHILD, "1")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            return;
        }
        configure_tastic(Tactic::Default);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let found = unsafe {
            let descriptors = Z3_solver_get_param_descrs(context.z3_ctx, solver.z3_solver);
            Z3_param_descrs_inc_ref(context.z3_ctx, descriptors);
            let native = (0..Z3_param_descrs_size(context.z3_ctx, descriptors)).any(|i| {
                let name = Z3_param_descrs_get_name(context.z3_ctx, descriptors, i);
                Z3_get_symbol_kind(context.z3_ctx, name) == SymbolKind::String
                    && CStr::from_ptr(Z3_get_symbol_string(context.z3_ctx, name)).to_bytes() == b"solver2_timeout"
            });
            Z3_param_descrs_dec_ref(context.z3_ctx, descriptors);
            native
        };
        assert!(found, "Default必须是Z3原生solver，而不是同名tactic包装器");
        let info = SourceLoc::unknown();
        let enum_id = solver.get_enum(Name::from_u32(40000), 2);
        let tag = solver.declare_const(smtlib::Ty::Enum(enum_id), info);
        let byte = solver.declare_bitvector(8, info);
        let member = EnumMember { enum_id, member: 1 };
        solver.assert(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(tag)), Box::new(smtlib::Exp::Enum(member))));
        solver.assert(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(byte)), Box::new(smtlib::bits64(0x5a, 8))));
        assert!(solver.check_sat(info).is_sat().unwrap());
        let mut model = Model::new(&solver);
        assert_eq!(model.get_var(tag).unwrap().unwrap_exp(), smtlib::Exp::Enum(member));
        assert_eq!(model.get_var(byte).unwrap().unwrap_exp(), smtlib::bits64(0x5a, 8));
    }

    #[test]
    fn fp_div_nan_classification_avoids_arithmetic_and_matches_ieee() {
        configure_tastic(Tactic::Qfaufbv);
        for (exponent, significand) in [(3, 3), (5, 11), (8, 24), (11, 53)] {
            let context = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&context);
            let info = SourceLoc::unknown();
            let left = solver.declare_const(smtlib::Ty::Float(exponent, significand), info);
            let right = solver.declare_const(smtlib::Ty::Float(exponent, significand), info);
            let rounding = solver.declare_const(smtlib::Ty::RoundingMode, info);
            let quotient = solver.define_const(
                smtlib::Exp::FPRoundingBinary(
                    smtlib::FPRoundingBinary::Div,
                    Box::new(smtlib::Exp::Var(rounding)),
                    Box::new(smtlib::Exp::Var(left)),
                    Box::new(smtlib::Exp::Var(right)),
                ),
                info,
            );
            // 穿过DefineConst引用，覆盖真实原语调用产生的表达式形式。
            let value = solver.translate_exp(&smtlib::Exp::Var(quotient));
            let classified = solver
                .translate_exp(&smtlib::Exp::FPUnary(smtlib::FPUnary::IsNaN, Box::new(smtlib::Exp::Var(quotient))));
            let mut pending = vec![classified.z3_ast];
            let mut visited = HashSet::new();
            while let Some(ast) = pending.pop() {
                if !visited.insert(ast) {
                    continue;
                }
                unsafe {
                    if Z3_get_ast_kind(context.z3_ctx, ast) != AstKind::App {
                        continue;
                    }
                    let app = Z3_to_app(context.z3_ctx, ast);
                    let symbol = Z3_get_decl_name(context.z3_ctx, Z3_get_app_decl(context.z3_ctx, app));
                    if Z3_get_symbol_kind(context.z3_ctx, symbol) == SymbolKind::String {
                        assert_ne!(
                            CStr::from_ptr(Z3_get_symbol_string(context.z3_ctx, symbol)).to_bytes(),
                            b"fp.div",
                            "仅分类NaN的查询不应构造数值除法器"
                        );
                    }
                    pending.extend(
                        (0..Z3_get_app_num_args(context.z3_ctx, app)).map(|i| Z3_get_app_arg(context.z3_ctx, app, i)),
                    );
                }
            }
            // 小格式用原始Z3 API证明全部位型／RM；f64全域证明另存实测证据，单测覆盖IEEE边界。
            use smtlib::FPRoundingMode::*;
            if exponent == 11 {
                let bits = [
                    0,
                    0x8000000000000000,
                    1,
                    0x8000000000000001,
                    0x0010000000000000,
                    0x3ff0000000000000,
                    0xbff0000000000000,
                    0x7fefffffffffffff,
                    0x7ff0000000000000,
                    0xfff0000000000000,
                    0x7ff8000000000000,
                    0x7ff0000000000001,
                ];
                for mode in [
                    RoundNearestTiesToEven,
                    RoundNearestTiesToAway,
                    RoundTowardPositive,
                    RoundTowardNegative,
                    RoundTowardZero,
                ] {
                    for a in bits {
                        for b in bits {
                            let operand = |bits| {
                                smtlib::Exp::FPUnary(
                                    smtlib::FPUnary::FromIEEE(11, 53),
                                    Box::new(smtlib::bits64(bits, 64)),
                                )
                            };
                            let value = solver.translate_exp(&smtlib::Exp::FPRoundingBinary(
                                smtlib::FPRoundingBinary::Div,
                                Box::new(smtlib::Exp::FPRoundingMode(mode)),
                                Box::new(operand(a)),
                                Box::new(operand(b)),
                            ));
                            let reference = z3_unary_op!(Z3_mk_fpa_is_nan, value);
                            let mut agreement = value.mk_fpa_is_nan().mk_eq(&reference);
                            agreement.simplify();
                            assert!(unsafe {
                                Z3_is_eq_ast(context.z3_ctx, agreement.z3_ast, Ast::mk_bool(&context, true).z3_ast)
                            });
                        }
                    }
                }
                continue;
            }
            let modes = [None];
            for mode in modes {
                let value = match mode {
                    None => value.clone(),
                    Some(mode) => solver.translate_exp(&smtlib::Exp::FPRoundingBinary(
                        smtlib::FPRoundingBinary::Div,
                        Box::new(smtlib::Exp::FPRoundingMode(mode)),
                        Box::new(smtlib::Exp::Var(left)),
                        Box::new(smtlib::Exp::Var(right)),
                    )),
                };
                let reference = z3_unary_op!(Z3_mk_fpa_is_nan, value);
                let different = value.mk_fpa_is_nan().mk_eq(&reference).mk_not();
                unsafe {
                    let proof = new_z3_solver(context.z3_ctx, Tactic::Qffp.as_c_str(), None);
                    // 仅独立证明使用保护预算，不参与生产求解器配置。
                    let parameters = Z3_mk_params(context.z3_ctx);
                    Z3_params_inc_ref(context.z3_ctx, parameters);
                    let timeout = CString::new("timeout").unwrap();
                    Z3_params_set_uint(
                        context.z3_ctx,
                        parameters,
                        Z3_mk_string_symbol(context.z3_ctx, timeout.as_ptr()),
                        15000,
                    );
                    Z3_solver_set_params(context.z3_ctx, proof, parameters);
                    Z3_params_dec_ref(context.z3_ctx, parameters);
                    Z3_solver_assert(context.z3_ctx, proof, different.z3_ast);
                    assert_eq!(
                        Z3_solver_check(context.z3_ctx, proof),
                        Z3_L_FALSE,
                        "全部浮点位型必须等价：{exponent}/{significand}，{mode:?}"
                    );
                    Z3_solver_dec_ref(context.z3_ctx, proof);
                }
            }
        }
    }

    #[test]
    fn fp_nan_does_not_rewrite_same_named_uninterpreted_function() {
        configure_tastic(Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        for concrete in [false, true] {
            let mut solver = Solver::<B64>::new(&context);
            let info = SourceLoc::unknown();
            let left = solver.declare_const(smtlib::Ty::Float(11, 53), info);
            let right = solver.declare_const(smtlib::Ty::Float(11, 53), info);
            let rounding = solver.declare_const(smtlib::Ty::RoundingMode, info);
            let args = if concrete {
                [
                    Ast::mk_fpa_round_toward_zero(&context),
                    Ast::mk_fpa_zero(&context, 11, 53, false),
                    Ast::mk_fpa_zero(&context, 11, 53, false),
                ]
            } else {
                [
                    solver.translate_exp(&smtlib::Exp::Var(rounding)),
                    solver.translate_exp(&smtlib::Exp::Var(left)),
                    solver.translate_exp(&smtlib::Exp::Var(right)),
                ]
            };
            unsafe {
                let ctx = context.z3_ctx;
                let name = CString::new("fp.div").unwrap();
                let domain = args.each_ref().map(|arg| Z3_get_sort(ctx, arg.z3_ast));
                let declaration =
                    Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, name.as_ptr()), 3, domain.as_ptr(), domain[1]);
                let declaration_ast = Z3_func_decl_to_ast(ctx, declaration);
                Z3_inc_ref(ctx, declaration_ast);
                let arguments = args.each_ref().map(|arg| arg.z3_ast);
                let application = Z3_mk_app(ctx, declaration, 3, arguments.as_ptr());
                Z3_inc_ref(ctx, application);
                let value = Ast { z3_ast: application, ctx: &context };
                Z3_dec_ref(ctx, declaration_ast);
                let expected = value.mk_fpa_is_nan_raw();
                assert!(
                    Z3_is_eq_ast(ctx, value.mk_fpa_is_nan().z3_ast, expected.z3_ast),
                    "同名同签名的未解释函数必须保持原有NaN判定"
                );
            }
        }
    }

    #[test]
    fn z3_version_comparison_covers_lower_equal_and_higher() {
        for version in [(4, 99, 99, 99), (5, 3, 9, 9), (5, 4, 0, 0), (5, 4, 0, 1), (6, 0, 0, 0)] {
            assert_eq!(z3_version_supported(version), version >= (5, 4, 0, 0));
        }
    }

    #[test]
    fn runtime_z3_version_accepts_installed_library() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<crate::bitvector::b64::B64>::new(&context);
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
    }

    #[test]
    fn simplified_boolean_query_keeps_context_and_avoids_false_solver_calls() {
        use smtlib::Exp::*;
        configure_tastic(Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let x = solver.declare_const(smtlib::Ty::BitVec(64), info);
        let equal = Eq(Box::new(Var(x)), Box::new(Var(x)));
        reset_path_smt_stats();
        assert_eq!(solver.check_sat_with(&Not(Box::new(equal.clone())), info), SmtResult::Unsat);
        assert_eq!(path_smt_stats().calls, 0, "恒假目标无需重解全部路径约束");
        solver.assert(Bool(false));
        assert_eq!(solver.check_sat_with(&equal, info), SmtResult::Unsat, "目标恒真不能掩盖当前上下文不可满足");
        assert!(!solver.last_check_was_sat());
    }

    #[test]
    fn cached_sat_witness_avoids_rechecking_and_respects_transactions() {
        use smtlib::Exp::*;
        configure_tastic(Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let x = solver.declare_const(smtlib::Ty::Bool, info);
        assert_eq!(solver.check_sat_with(&Var(x), info), SmtResult::Sat);
        reset_path_smt_stats();
        assert_eq!(solver.check_sat(info), SmtResult::Sat);
        assert_eq!(path_smt_stats().calls, 0, "现有见证已满足全部断言");
        assert_eq!(solver.check_sat_with(&Var(x), info), SmtResult::Sat);
        assert_eq!(path_smt_stats().slowest.unwrap().operation, SmtOperation::ModelEval);
        assert_eq!(
            solver.check_sat_with(&Not(Box::new(Var(x))), info),
            SmtResult::Sat,
            "一个见证不满足条件不能说明条件不可满足"
        );
        let tx = solver.start_transaction_with_guard(Some(Var(x)));
        solver.assert(Not(Box::new(Var(x))));
        assert_eq!(solver.check_sat(info), SmtResult::Unsat, "缓冲断言必须使旧模型失效");
        solver.rollback_transaction(tx);
        reset_path_smt_stats();
        assert_eq!(solver.check_sat(info), SmtResult::Sat, "回滚恢复有效见证");
        assert_eq!(path_smt_stats().calls, 0);
        solver.assert(Var(x));
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(x))), info), SmtResult::Unsat);
    }

    #[test]
    fn count增量查询退出后恢复原求解器与模型缓存() {
        use crate::bitvector::b64::B64;
        use smtlib::Exp::*;
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let guard = solver.declare_const(smtlib::Ty::Bool, SourceLoc::unknown());
        let fixed = solver.declare_const(smtlib::Ty::Bool, SourceLoc::unknown());
        solver.assert(Var(fixed));
        assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
        let original = solver.z3_solver;
        let before = solver.trace().to_vec().len();
        let tx = solver.start_transaction();
        let result: Result<(), ()> = solver.with_incremental_checks(|solver| {
            assert_ne!(solver.z3_solver, original);
            assert!(solver.check_sat_with(&Not(Box::new(Var(fixed))), SourceLoc::unknown()).is_unsat().unwrap());
            assert!(solver.check_sat_with(&Var(guard), SourceLoc::unknown()).is_sat().unwrap());
            let mut model = Model::new(solver);
            assert!(matches!(model.get_exp(&Var(guard)).unwrap().unwrap_exp(), Bool(true)));
            drop(model);
            assert!(solver.check_sat_with(&Not(Box::new(Var(guard))), SourceLoc::unknown()).is_sat().unwrap());
            Err(())
        });
        assert_eq!(result, Err(()));
        assert_eq!(solver.z3_solver, original);
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            solver.with_incremental_checks(|solver| {
                assert!(solver.check_sat_with(&Var(guard), SourceLoc::unknown()).is_sat().unwrap());
                panic!("验证增量查询展开后的资源恢复");
            });
        }));
        assert!(panic.is_err());
        assert_eq!(solver.z3_solver, original);
        assert!(solver.has_stashed_model());
        solver.rollback_transaction(tx);
        assert!(solver.has_stashed_model());
        assert_eq!(solver.transaction_depth(), 0);
        assert_eq!(solver.trace().to_vec().len(), before);
        assert!(solver.check_sat_with(&Var(guard), SourceLoc::unknown()).is_sat().unwrap());
        assert!(solver.check_sat_with(&Not(Box::new(Var(guard))), SourceLoc::unknown()).is_sat().unwrap());
    }

    #[cfg(feature = "smtperf")]
    #[test]
    fn review12_transaction_performance_graph_leak() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        for _ in 0..32 {
            let tx = solver.start_transaction();
            solver.declare_const(Ty::Bool, SourceLoc::unknown());
            solver.rollback_transaction(tx);
        }
        eprintln!(
            "回滚后：声明={}，性能图节点={}，性能图符号={}",
            solver.decls.len(),
            solver.performance_info.vars.node_count(),
            solver.performance_info.var_nodes.len()
        );
        assert_eq!(solver.performance_info.vars.node_count(), 0, "事务回滚必须释放推测分配的性能图节点");
    }

    #[cfg(feature = "smtperf")]
    #[test]
    fn review12_transaction_preserves_existing_performance_graph() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let root = solver.declare_const(Ty::Bool, info);
        let old = solver.define_const(Not(Box::new(Var(root))), info);
        let nodes = solver.performance_info.var_nodes.clone();
        let edges = solver.performance_info.vars.edge_count();
        for _ in 0..32 {
            let tx = solver.start_transaction();
            let new = solver.define_const(And(Box::new(Var(root)), Box::new(Var(old))), info);
            solver.define_const(Not(Box::new(Var(new))), info);
            solver.rollback_transaction(tx);
            assert_eq!(solver.performance_info.var_nodes, nodes);
            assert_eq!(solver.performance_info.vars.node_count(), nodes.len());
            assert_eq!(solver.performance_info.vars.edge_count(), edges);
            for (sym, index) in &nodes {
                assert_eq!(solver.performance_info.vars[*index].0, *sym);
            }
        }
        let tx = solver.start_transaction();
        let committed = solver.define_const(Not(Box::new(Var(root))), info);
        solver.commit_transaction();
        assert!(solver.performance_info.var_nodes.contains_key(&committed));
    }

    use std::sync::Arc;
    use std::time::Duration;

    use crate::bitvector::b64::B64;
    use crate::timeout::{SmtDumpSource, SmtOperation, SmtTimeout, TimeoutSmtDump};

    use super::Def::*;
    use super::Exp::*;
    use super::*;

    #[cfg(not(feature = "smtperf"))]
    #[test]
    fn arm_replay_appends_assertions_without_repeated_simplification_or_push() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let info = SourceLoc::unknown();
        let mut parent = Solver::<B64>::new(&ctx);
        let input = parent.declare_const(Ty::Bool, info);
        let selector = parent.declare_const(Ty::Bool, info);
        parent.assert(Or(Box::new(Var(input)), Box::new(Var(selector))));
        let prefix = parent.arm_entry_checkpoint();
        let branch = |side: bool| {
            let mut parent = Solver::from_checkpoint(&ctx, prefix.clone());
            parent.assert_eq(Var(selector), Bool(side));
            parent.arm_entry_checkpoint()
        };
        let left = branch(true);
        let right = branch(false);
        let mut replay = ArmReplay::new(&ctx);
        let scopes = |solver: &Solver<B64>| unsafe { Z3_solver_get_num_scopes(ctx.z3_ctx, solver.z3_solver) };
        let before = AST_SIMPLIFY_CALLS.get();
        let (solver, _) = replay.restore(prefix);
        let prefix_scopes = scopes(solver);
        assert_eq!(prefix_scopes, 0, "可变的断言后缀应留在查询假设中");
        let initial_simplifications = AST_SIMPLIFY_CALLS.get() - before;
        replay.finish();
        let before = AST_SIMPLIFY_CALLS.get();
        let (solver, _) = replay.restore(left);
        let append_scopes = scopes(solver);
        let append_simplifications = AST_SIMPLIFY_CALLS.get() - before;
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(input))), info), Sat);
        replay.finish();
        let (solver, _) = replay.restore(right);
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(input))), info), Unsat);
        assert_eq!(solver.check_sat_with(&Var(input), info), Sat);
        replay.finish();

        assert_eq!(append_scopes, prefix_scopes, "短后缀应追加到当前原生作用域");
        assert_eq!(initial_simplifications + append_simplifications, 0, "入口只构造断言，交由求解器处理");
    }

    #[test]
    fn arm_replay_rewinds_sibling_assertions_rebindings_and_enums() {
        configure_tastic(Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let info = SourceLoc::unknown();
        let mut parent = Solver::<B64>::new(&context);
        let input = parent.declare_const(Ty::Bool, info);
        let rebound = parent.define_const(Var(input), info);
        let mut chain = input;
        for _ in 0..256 {
            chain = parent.define_const(Not(Box::new(Var(chain))), info);
        }
        let entry = checkpoint(&mut parent);

        let sibling = |left: bool| {
            let mut solver = Solver::from_checkpoint(&context, entry.clone());
            solver.add(DefineConst(rebound, Bool(left)));
            solver.assert(if left { Var(chain) } else { Not(Box::new(Var(chain))) });
            let enumeration = solver.get_enum(Name::from_u32(if left { 900 } else { 901 }), 2);
            let symbol = solver.declare_const(Ty::Enum(enumeration), info);
            solver.assert_eq(Var(symbol), Enum(enumeration.first_member()));
            solver.cycle_count();
            if left {
                solver.cycle_count();
            }
            solver.arm_entry_checkpoint()
        };
        let left = sibling(true);
        let right = sibling(false);
        let mut visits = Vec::new();
        let mut replay = ArmReplay::new(&context);
        for (point, side) in [(&left, true), (&right, false), (&left, true), (&left, true)] {
            let before = REPLAY_SMT_EVENTS.get();
            let (solver, _) = replay.restore(point.clone());
            visits.push(REPLAY_SMT_EVENTS.get() - before);
            assert_eq!(solver.get_cycle_count(), if side { 2 } else { 1 });
            assert_eq!(solver.next_join_symbol(), point.next_var);
            assert_eq!(solver.structural_bool(&Var(rebound)), Some(side));
            assert_eq!(solver.check_sat_with(&Var(input), info), if side { Sat } else { Unsat });
            assert_eq!(solver.check_sat_with(&Not(Box::new(Var(input))), info), if side { Unsat } else { Sat });
            assert_eq!(solver.enums.enums.len(), 1);
            assert!(solver.enums.enums.contains_key(&Name::from_u32(if side { 900 } else { 901 })));
            let root = solver.start_transaction();
            solver.add(DefineConst(rebound, Bool(!side)));
            solver.get_enum(Name::from_u32(902), 3);
            solver.rollback_transaction(root);
            replay.finish();
        }
        assert!(visits[0] >= 256);
        assert_eq!(visits[1..], [5, 5, 0], "同一前缀的兄弟臂只需重放后缀");
    }

    #[test]
    fn checkpoint_replay_preserves_each_assertion_without_simplifying_each_binding() {
        use z3_sys::{
            Z3_ast_vector_dec_ref, Z3_ast_vector_get, Z3_ast_vector_inc_ref, Z3_ast_vector_size,
            Z3_solver_get_assertions,
        };

        configure_tastic(Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut original = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let input = original.declare_const(Ty::BitVec(16), info);
        AST_SIMPLIFY_CALLS.set(0);
        let mut tail = input;
        for index in 1..=192 {
            tail = original.define_const(Bvadd(Box::new(Var(tail)), Box::new(smtlib::bits64(1, 16))), info);
            if index % 48 == 0 {
                original.assert(Eq(Box::new(Var(tail)), Box::new(smtlib::bits64(index + 7, 16))));
                checkpoint(&mut original);
            }
        }
        let original_calls = AST_SIMPLIFY_CALLS.get();
        AST_SIMPLIFY_CALLS.set(0);
        let mut replayed = Solver::from_arm_checkpoint(&context, checkpoint(&mut original));
        let replay_calls = AST_SIMPLIFY_CALLS.get();

        unsafe {
            let ctx = context.z3_ctx;
            let before = Z3_solver_get_assertions(ctx, original.z3_solver);
            Z3_ast_vector_inc_ref(ctx, before);
            let after = Z3_solver_get_assertions(ctx, replayed.z3_solver);
            Z3_ast_vector_inc_ref(ctx, after);
            let proof = new_z3_solver(ctx, Tactic::Default.as_c_str(), None);
            assert_eq!(Z3_ast_vector_size(ctx, before), 4);
            assert_eq!(Z3_ast_vector_size(ctx, after), 4);
            for index in 0..4 {
                let lhs = Z3_ast_vector_get(ctx, before, index);
                let rhs = Z3_ast_vector_get(ctx, after, index);
                let equality = Z3_mk_eq(ctx, lhs, rhs);
                let difference = Z3_mk_not(ctx, equality);
                Z3_solver_assert(ctx, proof, difference);
                assert_eq!(Z3_solver_check(ctx, proof), Z3_L_FALSE, "第 {index} 条断言必须双向蕴含");
                Z3_solver_reset(ctx, proof);
            }
            Z3_solver_dec_ref(ctx, proof);
            Z3_ast_vector_dec_ref(ctx, after);
            Z3_ast_vector_dec_ref(ctx, before);
        }

        let constant =
            replayed.define_const(Bvadd(Box::new(smtlib::bits64(3, 16)), Box::new(smtlib::bits64(4, 16))), info);
        let before = AST_SIMPLIFY_CALLS.get();
        assert_eq!(replayed.translate_exp(&Var(constant)).get_numeral_u64().unwrap(), 7);
        assert_eq!(AST_SIMPLIFY_CALLS.get(), before, "新定义的已知常量可直接求值");
        eprintln!("重放／原执行的化简次数：{replay_calls}／{original_calls}");
        assert!(replay_calls * 10 < original_calls, "重放／原执行的化简次数：{replay_calls}／{original_calls}");
    }

    #[test]
    fn transaction_keeps_trace_and_solver_state_isolated() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let before = solver.trace.head.len();
        let tx = solver.start_transaction();
        let speculative = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        solver.add_event(Event::Cycle);
        solver.assert(Exp::Bool(false));
        assert!(!solver.transaction_invalid());
        assert_eq!(solver.trace.head.len(), before);
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Unsat);
        solver.rollback_transaction(tx);
        assert!(!solver.decls.contains_key(&speculative));
        assert!(solver.fresh().id > speculative.id);
        assert!(!solver.has_stashed_model());
        assert_eq!(solver.trace.head.len(), before);
    }

    #[test]
    fn committed_transaction_replays_buffered_events() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let tx = solver.start_transaction();
        let symbol = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        solver.add_event(Event::Cycle);
        solver.add_event(Event::ReadReg(Name::from_u32(0), Vec::new(), Val::Symbolic(symbol)));
        solver.add_event(Event::ReadReg(Name::from_u32(0), Vec::new(), Val::Symbolic(symbol)));
        assert_eq!(solver.trace.head.len(), tx.head_len);
        solver.commit_transaction();
        assert_eq!(solver.trace.head.len(), tx.head_len + 4);
        assert!(matches!(&solver.trace.head[tx.head_len], Event::Smt(Def::DeclareConst(v, _), _, _) if *v == symbol));
    }

    #[test]
    fn review34_推测臂条件必须隔离且不得进入提交或回滚后的路径() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        for commit in [false, true] {
            let mut solver = Solver::<B64>::new(&ctx);
            let flag = solver.declare_const(Ty::Bool, SourceLoc::unknown());
            let before = solver.trace.head.len();
            let tx = solver.start_transaction();
            for condition in [Var(flag), Not(Box::new(Var(flag)))] {
                solver.with_transaction_condition(&condition, |solver| {
                    assert_eq!(solver.check_sat(SourceLoc::unknown()), Sat);
                    assert_eq!(solver.check_sat_with(&Not(Box::new(condition.clone())), SourceLoc::unknown()), Unsat);
                    assert_eq!(solver.check_sat_with(&condition, SourceLoc::unknown()), Sat);
                });
                assert!(!solver.has_stashed_model(), "臂模型不能泄漏到前缀");
                assert!(!solver.transaction_invalid());
            }
            if commit {
                solver.commit_transaction();
            } else {
                solver.rollback_transaction(tx);
            }
            assert_eq!(solver.trace.head.len(), before);
            assert_eq!(solver.check_sat_with(&Var(flag), SourceLoc::unknown()), Sat);
            assert_eq!(solver.check_sat_with(&Not(Box::new(Var(flag))), SourceLoc::unknown()), Sat);
            let point = checkpoint(&mut solver);
            let mut replayed = Solver::from_checkpoint(&ctx, point);
            assert_eq!(replayed.check_sat_with(&Var(flag), SourceLoc::unknown()), Sat);
            assert_eq!(replayed.check_sat_with(&Not(Box::new(Var(flag))), SourceLoc::unknown()), Sat);
        }
    }

    macro_rules! bv {
        ( $bv_string:expr ) => {{
            let mut vec = Vec::new();
            for c in $bv_string.chars().rev() {
                if c == '1' {
                    vec.push(true)
                } else if c == '0' {
                    vec.push(false)
                } else {
                    ()
                }
            }
            Bits(vec)
        }};
    }

    fn var(id: u32) -> Exp<Sym> {
        Var(Sym::from_u32(id))
    }

    struct FixedDump;

    impl SmtDumpSource for FixedDump {
        fn materialize(&self) -> Result<String, String> {
            Ok("(check-sat)\n".to_string())
        }
    }

    #[test]
    fn path_smt_stats_accumulate_protected_z3_calls_with_their_source_location() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        reset_path_smt_stats();
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let x = solver.declare_const(smtlib::Ty::BitVec(8), SourceLoc::unknown());
        let check_sat_loc = SourceLoc::new(1, 30, 2, 30, 40);
        let check_sat_with_loc = SourceLoc::new(1, 41, 6, 41, 20);

        assert_eq!(solver.check_sat(check_sat_loc), SmtResult::Sat);
        let one_call = path_smt_stats();
        assert_eq!(one_call.calls, 1);
        assert_eq!(one_call.timeouts, 0);
        let slowest = one_call.slowest.expect("check_sat 应当被记录");
        assert_eq!(slowest.operation, SmtOperation::CheckSat);
        assert_eq!(slowest.source_loc, check_sat_loc);

        // check_sat_with 的位置来自调用点的 SourceLoc，用于定位最慢的那次求解。
        let exp = Eq(Box::new(Var(x)), Box::new(bits64(0, 8)));
        assert_eq!(solver.check_sat_with(&exp, check_sat_with_loc), SmtResult::Sat);
        let two_calls = path_smt_stats();
        // 空模型没有给 x 赋值：先做一次模型求值，再完整求解新条件。
        assert_eq!(two_calls.calls, 3);
        assert!(two_calls.wall >= one_call.wall);
        assert!(matches!(
            two_calls.slowest.map(|slowest| slowest.source_loc),
            Some(location) if location == check_sat_loc || location == check_sat_with_loc
        ));

        // 路径开始执行时清零，统计才是"这条路径的"。
        reset_path_smt_stats();
        assert_eq!(path_smt_stats(), crate::timeout::SmtCallStats::empty());
    }

    fn timeout_artifact() -> Arc<SmtTimeout> {
        Arc::new(SmtTimeout {
            source_loc: SourceLoc::new(0, 1, 0, 1, 1),
            operation: SmtOperation::CheckSat,
            query_purpose: "unclassified",
            limit: Duration::from_secs(10),
            operation_wall: Duration::from_secs(11),
            dump: Arc::new(TimeoutSmtDump::new(Arc::new(FixedDump))),
        })
    }

    #[test]
    fn configured_tastic_is_used_by_solver() {
        configure_tastic(Tactic::Qfaufbv);
        assert_eq!(SMT_CONFIG.get().unwrap().tactic, Tactic::Qfaufbv);

        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        assert_eq!(solver.check_sat(SourceLoc::unknown()), Sat);
    }

    #[test]
    fn smt_timeout_result_preserves_error_artifact_identity() {
        let timeout = timeout_artifact();
        let same = SmtResult::Error(SmtError::Z3Timeout(Z3Timeout::Interrupted(timeout.clone())));
        let same_again = SmtResult::Error(SmtError::Z3Timeout(Z3Timeout::Interrupted(timeout.clone())));
        let different = SmtResult::Error(SmtError::Z3Timeout(Z3Timeout::Interrupted(timeout_artifact())));

        assert_eq!(same, same_again);
        assert_ne!(same, different);
        match same.is_sat() {
            Err(ExecError::Smt(SmtError::Z3Timeout(Z3Timeout::Interrupted(error)))) => {
                assert!(Arc::ptr_eq(&error, &timeout))
            }
            result => panic!("unexpected timeout conversion: {:?}", result),
        }
    }

    #[test]
    fn bv_macro() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        solver.add(Assert(Eq(Box::new(bv!("0110")), Box::new(bv!("1001")))));
        assert!(solver.check_sat(SourceLoc::unknown()) == Unsat);
    }

    #[test]
    fn get_const() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        solver.add(DeclareConst(Sym::from_u32(0), Ty::BitVec(4)));
        solver.add(DeclareConst(Sym::from_u32(1), Ty::BitVec(1)));
        solver.add(DeclareConst(Sym::from_u32(2), Ty::BitVec(5)));
        solver.add(DeclareConst(Sym::from_u32(3), Ty::BitVec(5)));
        solver.add(DeclareConst(Sym::from_u32(4), Ty::BitVec(257)));
        solver.add(Assert(Eq(Box::new(bv!("0110")), Box::new(var(0)))));
        solver.add(Assert(Eq(Box::new(var(2)), Box::new(var(3)))));
        let big_bv = Box::new(SignExtend(251, Box::new(Bits(vec![true, false, false, true, false, true]))));
        solver.add(Assert(Eq(Box::new(var(4)), big_bv)));
        assert!(solver.check_sat(SourceLoc::unknown()) == Sat);
        let (v0, v2, v3, v4);
        {
            let mut model = Model::new(&solver);
            v0 = model.get_var(Sym::from_u32(0)).unwrap().unwrap_exp();
            assert!(model.get_var(Sym::from_u32(1)).unwrap().is_arbitrary());
            v2 = model.get_var(Sym::from_u32(2)).unwrap().unwrap_exp();
            v3 = model.get_var(Sym::from_u32(3)).unwrap().unwrap_exp();
            v4 = model.get_var(Sym::from_u32(4)).unwrap().unwrap_exp();
        }
        solver.add(Assert(Eq(Box::new(var(0)), Box::new(v0))));
        solver.add(Assert(Eq(Box::new(var(2)), Box::new(v2))));
        solver.add(Assert(Eq(Box::new(var(3)), Box::new(v3))));
        solver.add(Assert(Eq(Box::new(var(4)), Box::new(v4))));
        match solver.check_sat(SourceLoc::unknown()) {
            Sat => (),
            _ => panic!("Round-trip failed, trace {:?}", solver.trace()),
        }
    }

    #[test]
    fn model_get_var_reuses_concrete_typed_values_and_mixed_segments() {
        use crate::bitvector::b129::B129;
        use crate::ir::BitsSegment;

        configure_tastic(Tactic::Qfaufbv);
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B129>::new(&ctx);
        let loc = SourceLoc::unknown();
        let bits64 = solver.declare_const(Ty::BitVec(64), loc);
        let bits129 = solver.declare_const(Ty::BitVec(129), loc);
        let boolean = solver.declare_const(Ty::Bool, loc);
        let enum_id = solver.get_enum(Name::from_u32(777), 3);
        let enumeration = solver.declare_const(Ty::Enum(enum_id), loc);
        let member = EnumMember { enum_id, member: 2 };
        let wide_bits: Vec<bool> = (0..129).map(|i| i == 0 || i == 64 || i == 128).collect();
        solver.assert_eq(Var(bits64), Bits64(B64::new(0x1234_5678_9abc_def0, 64)));
        solver.assert_eq(Var(bits129), Bits(wide_bits.clone()));
        solver.assert_eq(Var(boolean), Bool(true));
        solver.assert_eq(Var(enumeration), Enum(member));
        assert_eq!(solver.check_sat(loc), Sat);

        let mut model = Model::new(&solver);
        for (sym, expected) in [
            (bits64, Bits64(B64::new(0x1234_5678_9abc_def0, 64))),
            (bits129, Bits(wide_bits)),
            (boolean, Bool(true)),
            (enumeration, Enum(member)),
        ] {
            assert_eq!(model.get_var(sym).unwrap().unwrap_exp(), expected);
            reset_path_smt_stats();
            assert_eq!(model.get_var(sym).unwrap().unwrap_exp(), expected);
            assert_eq!(path_smt_stats().calls, 0, "相同 Model 内的具体 get_var 不应再次调用 Z3");
        }

        let wide =
            B129::zeros(129).set_slice(0, B129::BIT_ONE).set_slice(64, B129::BIT_ONE).set_slice(128, B129::BIT_ONE);
        let value = Val::MixedBits(vec![BitsSegment::Symbolic(bits129), BitsSegment::Concrete(B129::new(5, 3))]);
        reset_path_smt_stats();
        assert_eq!(
            model.get_val(&value).unwrap(),
            Val::MixedBits(vec![BitsSegment::Concrete(wide), BitsSegment::Concrete(B129::new(5, 3))])
        );
        assert_eq!(path_smt_stats().calls, 0, "MixedBits 应复用同一个符号的具体值");

        reset_path_smt_stats();
        assert_eq!(model.get_exp(&Var(bits129)).unwrap().unwrap_exp(), Bits(wide.to_vec()));
        assert!(path_smt_stats().calls > 0, "get_exp 应保留原有求值路径");
    }

    #[test]
    fn model_get_var_cache_is_local_and_cleared_on_completion_switch() {
        configure_tastic(Tactic::Qfaufbv);
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let loc = SourceLoc::unknown();
        let sym = solver.declare_const(Ty::BitVec(8), loc);
        solver.assert_eq(Var(sym), Bits64(B64::new(0xa5, 8)));
        assert_eq!(solver.check_sat(loc), Sat);

        let mut model = Model::new(&solver);
        assert_eq!(model.get_var(sym).unwrap().unwrap_exp(), Bits64(B64::new(0xa5, 8)));
        reset_path_smt_stats();
        model.get_var(sym).unwrap();
        assert_eq!(path_smt_stats().calls, 0);

        model.set_complete_model(true);
        reset_path_smt_stats();
        assert_eq!(model.get_var(sym).unwrap().unwrap_exp(), Bits64(B64::new(0xa5, 8)));
        assert!(path_smt_stats().calls > 0, "切换到 completion 后须重新求值");

        model.set_complete_model(false);
        reset_path_smt_stats();
        assert_eq!(model.get_var(sym).unwrap().unwrap_exp(), Bits64(B64::new(0xa5, 8)));
        assert!(path_smt_stats().calls > 0, "切换回非 completion 后须重新求值");

        let mut fresh = Model::new(&solver);
        reset_path_smt_stats();
        assert_eq!(fresh.get_var(sym).unwrap().unwrap_exp(), Bits64(B64::new(0xa5, 8)));
        assert!(path_smt_stats().calls > 0, "新 Model 不应继承另一实例的缓存");
    }

    #[test]
    fn model_get_var_does_not_cache_arbitrary_or_errors() {
        configure_tastic(Tactic::Qfaufbv);
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let loc = SourceLoc::unknown();
        let arbitrary = solver.declare_const(Ty::BitVec(8), loc);
        let unsupported = solver.declare_const(Ty::Array(Box::new(Ty::BitVec(8)), Box::new(Ty::BitVec(8))), loc);
        assert_eq!(solver.check_sat(loc), Sat);

        let mut model = Model::new(&solver);
        assert!(model.get_var(arbitrary).unwrap().is_arbitrary());
        assert!(model.concrete_cache.is_empty());
        reset_path_smt_stats();
        assert!(model.get_var(arbitrary).unwrap().is_arbitrary());
        assert!(path_smt_stats().calls > 0, "Arbitrary 不应跳过再次求值");
        assert!(model.concrete_cache.is_empty());

        model.set_complete_model(true);
        assert_eq!(model.get_exp(&Var(arbitrary)).unwrap().unwrap_exp(), Bits64(B64::new(0, 8)));
        model.set_complete_model(false);
        assert_eq!(model.get_var(arbitrary).unwrap().unwrap_exp(), Bits64(B64::new(0, 8)));
        reset_path_smt_stats();
        model.get_var(arbitrary).unwrap();
        assert_eq!(path_smt_stats().calls, 0, "completion 后得到的具体值可在当前模式下复用");

        let invalid = Sym::from_u32(9999);
        assert!(matches!(model.get_var(invalid), Err(ExecError::Type(_, _))));
        assert!(matches!(model.get_var(invalid), Err(ExecError::Type(_, _))));
        assert!(!model.concrete_cache.contains_key(&invalid));
        assert!(matches!(model.get_var(unsupported), Err(ExecError::Type(_, _))));
        assert!(matches!(model.get_var(unsupported), Err(ExecError::Type(_, _))));
        assert!(!model.concrete_cache.contains_key(&unsupported));
    }

    #[test]
    fn local_model_debug_preserves_original_model_text_semantics() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        solver.add(DeclareConst(Sym::from_u32(0), Ty::Bool));
        solver.add(Assert(Var(Sym::from_u32(0))));
        assert_eq!(solver.check_sat(SourceLoc::unknown()), Sat);

        let model = Model::new(&solver);
        let text = format!("{:?}", model);

        assert!(text.contains("true"), "unexpected model text:\n{}", text);
    }

    #[test]
    fn get_enum_const() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let e = solver.get_enum(Name::from_u32(0), 3);
        let v0 = solver.declare_const(Ty::Enum(e), SourceLoc::unknown());
        let v1 = solver.declare_const(Ty::Enum(e), SourceLoc::unknown());
        let _v2 = solver.declare_const(Ty::Enum(e), SourceLoc::unknown());
        solver.assert_eq(Var(v0), Var(v1));
        assert!(solver.check_sat(SourceLoc::unknown()) == Sat);
        let (m0, m1) = {
            let mut model = Model::new(&solver);
            (model.get_var(v0).unwrap().unwrap_exp(), model.get_var(v1).unwrap().unwrap_exp())
        };
        solver.assert_eq(Var(v0), m0);
        solver.assert_eq(Var(v1), m1);
        match solver.check_sat(SourceLoc::unknown()) {
            Sat => (),
            _ => panic!("Round-trip failed, trace {:?}", solver.trace()),
        }
    }

    #[test]
    fn get_single_member_enum_const_after_checkpoint_replay() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let e = solver.get_enum(Name::from_u32(11), 1);
        let v = solver.declare_const(Ty::Enum(e), SourceLoc::unknown());
        solver.assert_eq(Var(v), Enum(e.first_member()));

        let checkpoint = checkpoint(&mut solver);
        let mut replayed = Solver::from_checkpoint(&ctx, checkpoint);
        assert!(unsafe { Z3_is_eq_sort(ctx.z3_ctx, solver.enums.enums[&e.id].sort, replayed.enums.enums[&e.id].sort) });
        assert_eq!(replayed.check_sat(SourceLoc::unknown()), Sat);

        let mut model = Model::new(&replayed);
        assert_eq!(model.get_var(v).unwrap().unwrap_exp(), Enum(e.first_member()));
    }

    #[test]
    fn get_multi_member_enum_const_after_checkpoint_replay() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let e = solver.get_enum(Name::from_u32(12), 4);
        let v = solver.declare_const(Ty::Enum(e), SourceLoc::unknown());
        let member = EnumMember { enum_id: e, member: 2 };
        solver.assert_eq(Var(v), Enum(member));

        let checkpoint = checkpoint(&mut solver);
        let mut replayed = Solver::from_checkpoint(&ctx, checkpoint);
        assert!(unsafe { Z3_is_eq_sort(ctx.z3_ctx, solver.enums.enums[&e.id].sort, replayed.enums.enums[&e.id].sort) });
        assert_eq!(replayed.check_sat(SourceLoc::unknown()), Sat);

        let mut model = Model::new(&replayed);
        assert_eq!(model.get_var(v).unwrap().unwrap_exp(), Enum(member));
    }

    #[test]
    fn enum_checkpoint_replays_after_all_solvers_drop() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let loc = SourceLoc::unknown();
        let (point, small_var, large_var, small_member, large_member) = {
            let mut source = Solver::<B64>::new(&ctx);
            let small = source.get_enum(Name::from_u32(30), 1);
            let large = source.get_enum(Name::from_u32(31), 4);
            let small_var = source.declare_const(Ty::Enum(small), loc);
            let large_var = source.declare_const(Ty::Enum(large), loc);
            let small_member = small.first_member();
            let large_member = EnumMember { enum_id: large, member: 3 };
            source.assert_eq(Var(small_var), Enum(small_member));
            source.assert_eq(Var(large_var), Enum(large_member));
            (checkpoint(&mut source), small_var, large_var, small_member, large_member)
        };

        for _ in 0..3 {
            let mut replayed = Solver::from_checkpoint(&ctx, point.clone());
            assert_eq!(replayed.check_sat(loc), Sat);
            let mut model = Model::new(&replayed);
            assert_eq!(model.get_var(small_var).unwrap().unwrap_exp(), Enum(small_member));
            assert_eq!(model.get_var(large_var).unwrap().unwrap_exp(), Enum(large_member));
        }

        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let other_ctx = Context::new(Config::new());
        let mut replayed = Solver::from_checkpoint(&other_ctx, point);
        assert_eq!(replayed.check_sat(loc), Sat);
        let mut model = Model::new(&replayed);
        assert_eq!(model.get_var(small_var).unwrap().unwrap_exp(), Enum(small_member));
        assert_eq!(model.get_var(large_var).unwrap().unwrap_exp(), Enum(large_member));
    }

    #[test]
    #[should_panic(expected = "枚举类型的成员数量冲突")]
    fn get_enum_rejects_conflicting_member_count() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        solver.get_enum(Name::from_u32(32), 2);
        solver.get_enum(Name::from_u32(32), 3);
    }

    #[test]
    #[should_panic(expected = "枚举类型的成员数量冲突")]
    fn get_enum_rejects_conflicting_member_count_across_solvers() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        Solver::<B64>::new(&ctx).get_enum(Name::from_u32(33), 2);
        Solver::<B64>::new(&ctx).get_enum(Name::from_u32(33), 3);
    }

    #[test]
    #[should_panic(expected = "枚举类型的成员数量冲突")]
    fn define_enum_rejects_conflicting_member_count() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let name = Name::from_u32(35);
        solver.add(DefineEnum(name, 2));
        solver.add(DefineEnum(name, 3));
    }

    #[test]
    fn different_enums_keep_distinct_sorts_when_members_share_symbols() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let loc = SourceLoc::unknown();
        let mut first = Solver::<B64>::new(&ctx);
        let mut second = Solver::<B64>::new(&ctx);
        let first_enum = first.get_enum(Name::from_u32(36), 2);
        let second_enum = second.get_enum(Name::from_u32(37), 2);
        assert!(!unsafe {
            Z3_is_eq_sort(ctx.z3_ctx, first.enums.enums[&first_enum.id].sort, second.enums.enums[&second_enum.id].sort)
        });
        let first_var = first.declare_const(Ty::Enum(first_enum), loc);
        let second_var = second.declare_const(Ty::Enum(second_enum), loc);
        let first_member = EnumMember { enum_id: first_enum, member: 1 };
        let second_member = EnumMember { enum_id: second_enum, member: 1 };
        first.assert_eq(Var(first_var), Enum(first_member));
        second.assert_eq(Var(second_var), Enum(second_member));
        assert_eq!(first.check_sat(loc), Sat);
        assert_eq!(second.check_sat(loc), Sat);
        assert_eq!(Model::new(&first).get_var(first_var).unwrap().unwrap_exp(), Enum(first_member));
        assert_eq!(Model::new(&second).get_var(second_var).unwrap().unwrap_exp(), Enum(second_member));
    }

    #[test]
    #[should_panic(expected = "枚举类型至少需要一个成员")]
    fn get_enum_rejects_empty_enumeration() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        Solver::<B64>::new(&ctx).get_enum(Name::from_u32(34), 0);
    }

    #[test]
    fn isolated_checkpoint_preserves_definitions_and_rebases_only_new_constraints() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut execution = Solver::<B64>::new(&ctx);
        let loc = SourceLoc::unknown();
        let enum_id = execution.get_enum(Name::from_u32(214), 2);
        let choice = execution.declare_const(Ty::Bool, loc);
        let derived = execution.define_const(Var(choice), loc);
        let enum_value = execution.declare_const(Ty::Enum(enum_id), loc);
        execution.assert(Var(choice));
        execution.trace_call(Name::from_u32(215));
        let full = checkpoint(&mut execution);

        let isolated = full.with_instruction_assertions(&Val::Unit);
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let helper_ctx = Context::new(Config::new());
        let mut helper = Solver::from_checkpoint(&helper_ctx, isolated.clone());
        assert_eq!(helper.check_sat(loc), Sat);
        helper.assert(Not(Box::new(Var(derived))));
        assert_eq!(helper.check_sat(loc), Sat);
        helper.trace_call(Name::from_u32(216));
        let _intermediate = checkpoint(&mut helper);
        let new_symbol = helper.declare_const(Ty::Bool, loc);
        assert_ne!(new_symbol, choice);
        assert_ne!(new_symbol, derived);
        assert_ne!(new_symbol, enum_value);
        let new_enum = helper.get_enum(Name::from_u32(217), 2);
        let enum_symbol = helper.declare_const(Ty::Enum(new_enum), loc);
        helper.assert_eq(Var(enum_symbol), Enum(new_enum.first_member()));
        helper.assert(Var(new_symbol));
        let candidate = checkpoint(&mut helper);

        let combined = full.with_suffix_from(&isolated, &candidate);
        let events = combined.trace().as_ref().unwrap().to_vec();
        assert_eq!(events.iter().filter(|event| matches!(event, Event::Function { call: true, .. })).count(), 2);
        assert_eq!(events.iter().filter(|event| matches!(event, Event::Smt(Def::Assert(_), _, _))).count(), 4);
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let verified_ctx = Context::new(Config::new());
        let mut verified = Solver::from_checkpoint(&verified_ctx, combined);
        assert_eq!(verified.check_sat(loc), Unsat);

        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let next_helper_ctx = Context::new(Config::new());
        let mut helper = Solver::from_checkpoint(&next_helper_ctx, isolated.clone());
        helper.assert(Var(derived));
        helper.assert_eq(Enum(enum_id.first_member()), Var(enum_value));
        let combined = full.with_suffix_from(&isolated, &checkpoint(&mut helper));
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let next_verified_ctx = Context::new(Config::new());
        let mut verified = Solver::from_checkpoint(&next_verified_ctx, combined);
        assert_eq!(verified.check_sat(loc), Sat);
    }

    #[test]
    fn instruction_checkpoint_keeps_only_instruction_derived_assertions() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut execution = Solver::<B64>::new(&ctx);
        let loc = SourceLoc::unknown();
        let op = execution.declare_const(Ty::Bool, loc);
        let fpr = execution.declare_const(Ty::BitVec(32), loc);
        let first = execution.define_const(Var(op), loc);
        let second = execution.define_const(Var(first), loc);
        let mixed = execution
            .define_const(And(Box::new(Var(second)), Box::new(Eq(Box::new(Var(fpr)), Box::new(bits64(0, 32))))), loc);
        let function = execution.fresh();
        execution.add(DeclareFun(function, vec![Ty::Bool], Ty::Bool));
        let unknown = execution.define_const(App(function, vec![Var(op)]), loc);
        execution.assert(Var(op));
        execution.assert(Var(second));
        execution.assert_eq(Var(fpr), bits64(0, 32));
        execution.assert(Var(mixed));
        execution.assert(Var(unknown));
        execution.assert(Bool(true));
        let full = checkpoint(&mut execution);

        let instruction = Val::<B64>::Symbolic(op);
        let isolated = full.with_instruction_assertions(&instruction);
        let kept: Vec<_> = isolated
            .trace()
            .as_ref()
            .unwrap()
            .to_vec()
            .into_iter()
            .filter_map(|event| if let Event::Smt(Def::Assert(exp), _, _) = event { Some(exp.clone()) } else { None })
            .collect();
        assert_eq!(kept.len(), 3);
        assert!(kept.contains(&Var(op)));
        assert!(kept.contains(&Var(second)));
        assert!(kept.contains(&Bool(true)));

        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let helper_ctx = Context::new(Config::new());
        let mut helper = Solver::from_checkpoint(&helper_ctx, isolated.clone());
        assert_eq!(helper.check_sat(loc), Sat);
        assert_eq!(helper.check_sat_with(&Not(Box::new(Var(op))), loc), Unsat);
        assert_eq!(helper.check_sat_with(&Neq(Box::new(Var(fpr)), Box::new(bits64(0, 32))), loc), Sat);
        helper.assert_eq(Var(fpr), bits64(1, 32));
        let combined = full.with_suffix_from(&isolated, &checkpoint(&mut helper));
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let verified_ctx = Context::new(Config::new());
        let mut verified = Solver::from_checkpoint(&verified_ctx, combined);
        assert_eq!(verified.check_sat(loc), Unsat);
    }

    #[test]
    fn get_struct_with_enum_field_after_checkpoint_replay() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);

        let enum_id = solver.get_enum(Name::from_u32(13), 3);
        let enum_sym = solver.declare_const(Ty::Enum(enum_id), SourceLoc::unknown());
        let bits_sym = solver.declare_const(Ty::BitVec(8), SourceLoc::unknown());
        let enum_member = EnumMember { enum_id, member: 2 };
        solver.assert_eq(Var(enum_sym), Enum(enum_member));
        solver.assert_eq(Var(bits_sym), bv!("10101010"));

        let enum_field = Name::from_u32(100);
        let bits_field = Name::from_u32(101);
        let mut fields = ahash::HashMap::with_capacity_and_hasher(2, ahash::RandomState::new());
        fields.insert(enum_field, Val::Symbolic(enum_sym));
        fields.insert(bits_field, Val::Symbolic(bits_sym));
        let value = Val::Struct(fields);

        let checkpoint = checkpoint(&mut solver);
        let mut replayed = Solver::from_checkpoint(&ctx, checkpoint);
        assert_eq!(replayed.check_sat(SourceLoc::unknown()), Sat);

        let mut model = Model::new(&replayed);
        let resolved = model.get_val(&value).unwrap();

        let mut expected_fields = ahash::HashMap::with_capacity_and_hasher(2, ahash::RandomState::new());
        expected_fields.insert(enum_field, Val::Enum(enum_member));
        expected_fields.insert(bits_field, Val::Bits(B64::new(0b10101010, 8)));
        assert_eq!(resolved, Val::Struct(expected_fields));
    }

    #[test]
    fn smt_func() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        solver.add(DeclareFun(Sym::from_u32(0), vec![Ty::BitVec(2), Ty::BitVec(4)], Ty::BitVec(8)));
        solver.add(DeclareConst(Sym::from_u32(1), Ty::BitVec(8)));
        solver.add(DeclareConst(Sym::from_u32(2), Ty::BitVec(2)));
        solver
            .add(Assert(Eq(Box::new(App(Sym::from_u32(0), vec![bv!("10"), bv!("0110")])), Box::new(bv!("01011011")))));
        solver.add(Assert(Eq(Box::new(App(Sym::from_u32(0), vec![var(2), bv!("0110")])), Box::new(var(1)))));
        solver.add(Assert(Eq(Box::new(var(2)), Box::new(bv!("10")))));
        assert!(solver.check_sat(SourceLoc::unknown()) == Sat);
        let mut model = Model::new(&solver);
        let val = model.get_var(Sym::from_u32(1)).unwrap().unwrap_exp();
        assert!(match val {
            Bits64(bv) if bv == B64::new(0b01011011, 8) => true,
            _ => false,
        });
    }

    #[test]
    fn array() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        solver.add(DeclareConst(Sym::from_u32(0), Ty::Array(Box::new(Ty::BitVec(3)), Box::new(Ty::BitVec(4)))));
        solver.add(DeclareConst(Sym::from_u32(1), Ty::BitVec(3)));
        solver.add(Assert(Neq(
            Box::new(Select(
                Box::new(Store(Box::new(var(0)), Box::new(var(1)), Box::new(bv!("0101")))),
                Box::new(var(1)),
            )),
            Box::new(bv!("0101")),
        )));
        assert!(solver.check_sat(SourceLoc::unknown()) == Unsat);
    }

    /// `take_stashed_model` 是"跳过终值重解"的依据：Sat check 后缓存模型，
    /// 新增 `Def::Assert` 使缓存失效。关键语义：后续 **Unsat 探测**
    /// （check_sat_with 探针，如 `__monomorphize` 的唯一性探测）不能让缓存
    /// 失效——Z3 自己会丢弃"最后模型"，但缓存模型满足的当前断言集没变。
    #[test]
    fn 模型缓存跟踪新增断言且不被unsat探测失效() {
        let cfg = Config::new();
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        solver.add(DeclareConst(Sym::from_u32(0), Ty::Bool));

        assert!(solver.take_stashed_model().is_none(), "从未 check 过的 solver 无缓存模型");

        // Unsat 的 check 不产生缓存
        solver.add(Assert(Bool(false)));
        assert_eq!(solver.check_sat(SourceLoc::unknown()), Unsat);
        assert!(solver.take_stashed_model().is_none());

        // Sat 后缓存可用
        let cfg2 = Config::new();
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx2 = Context::new(cfg2);
        let mut solver = Solver::<B64>::new(&ctx2);
        solver.add(DeclareConst(Sym::from_u32(0), Ty::Bool));
        // 钉住 var0 = true（此断言先使缓存失效，随后重新 Sat 产生新缓存）
        solver.add(Assert(Var(Sym::from_u32(0))));
        assert_eq!(solver.check_sat(SourceLoc::unknown()), Sat);
        assert!(solver.take_stashed_model().is_some(), "Sat check 后应缓存模型");
        assert!(solver.take_stashed_model().is_none(), "取出后缓存应转移为空");

        // 重新 Sat 恢复缓存
        assert_eq!(solver.check_sat(SourceLoc::unknown()), Sat);
        assert!(solver.has_stashed_model());

        // Unsat 探测（var0 已钉成 true，取反必 Unsat）不清空缓存
        assert_eq!(solver.check_sat_with(&Not(Box::new(Var(Sym::from_u32(0)))), SourceLoc::unknown()), Unsat);
        assert!(solver.take_stashed_model().is_some(), "Unsat 探测不应使缓存失效");

        // check_sat_with 的 Sat 查询同样刷新缓存（assumption 只收紧约束）
        assert_eq!(solver.check_sat_with(&Var(Sym::from_u32(0)), SourceLoc::unknown()), Sat);
        assert!(solver.take_stashed_model().is_some());

        // 新增 Assert 后缓存失效（即使是语义上恒真的断言）
        solver.add(Assert(Bool(true)));
        assert!(solver.take_stashed_model().is_none(), "新增断言后缓存必须失效");
        assert_eq!(solver.check_sat(SourceLoc::unknown()), Sat);
        assert!(solver.take_stashed_model().is_some());
    }

    /// 复用缓存模型与重解取模型结果一致：断言集未变时，缓存模型满足当前
    /// 全部断言，跳过重解不改变物化值的可用性。
    #[test]
    fn 复用缓存模型与重解结果一致() {
        let cfg = Config::new();
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        solver.add(DeclareConst(Sym::from_u32(0), Ty::BitVec(8)));
        solver.add(Assert(Bvugt(Box::new(var(0)), Box::new(bv!("00000101")))));
        assert_eq!(solver.check_sat(SourceLoc::unknown()), Sat);

        // 模拟 __monomorphize 的唯一性探测：Unsat 的 check_sat_with 之后再取缓存
        assert_eq!(
            solver.check_sat_with(&Bvult(Box::new(var(0)), Box::new(bv!("00000010"))), SourceLoc::unknown()),
            Unsat
        );
        let reused = {
            let mut model = solver.take_stashed_model().expect("Unsat 探测后缓存应仍可用");
            match model.get_var(Sym::from_u32(0)).unwrap() {
                ModelVal::Exp(Bits64(value)) => value,
                other => panic!("期望位向量模型值，实际 {:?}", other),
            }
        };
        assert!(reused.lower_u64() > 5, "缓存模型应满足既有约束 x > 5，实际 {}", reused.lower_u64());

        // 重解一次取模型，值同样满足约束（两个模型可以不同，但都必须满足约束）
        assert_eq!(solver.check_sat(SourceLoc::unknown()), Sat);
        let resolved = {
            let mut model = Model::new(&solver);
            match model.get_var(Sym::from_u32(0)).unwrap() {
                ModelVal::Exp(Bits64(value)) => value,
                other => panic!("期望位向量模型值，实际 {:?}", other),
            }
        };
        assert!(resolved.lower_u64() > 5, "重解模型应满足既有约束 x > 5，实际 {}", resolved.lower_u64());
    }

    /// deadline 查询可在限时内完成，也可返回 CheckSat 超时错误；两种结果
    /// 都不应破坏同一 solver 后续的正常查询。watchdog 的确定性中断另有专测。
    #[cfg(feature = "smt-thread-interrupt")]
    #[test]
    fn deadline查询完成或中断后仍可重用() {
        let cfg = Config::new();
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        // 64 位乘法逆运算用于触发限时调用；具体求解器可能很快找到解。
        let p = Sym::from_u32(0);
        let q = Sym::from_u32(1);
        solver.add(DeclareConst(p, Ty::BitVec(64)));
        solver.add(DeclareConst(q, Ty::BitVec(64)));
        solver.add(DeclareConst(Sym::from_u32(2), Ty::BitVec(64)));
        solver.add(Assert(Eq(Box::new(Bvmul(Box::new(Var(p)), Box::new(Var(q)))), Box::new(Var(Sym::from_u32(2))))));
        // 固定乘积，让两次查询使用相同断言。
        let prime_bits: Vec<bool> = (0..64).rev().map(|i| (0xC71CA6CBB5F1B7AEu64 >> i) & 1 == 1).collect();
        solver.add(Assert(Eq(Box::new(Var(Sym::from_u32(2))), Box::new(Bits(prime_bits)))));

        let result = solver.check_sat_deadline(SourceLoc::unknown(), Duration::from_millis(1));
        match result {
            Sat => (),
            SmtResult::Error(smt_error) => {
                let message = format!("{}", smt_error);
                assert!(message.contains("CheckSat"), "超时错误应标记 CheckSat 操作，实际 {}", message);
            }
            other => panic!("1ms deadline 下应返回 Sat 或超时，实际 {:?}", other),
        }

        // 给足时间后同一 solver 状态可正常求解（软中断不破坏 solver 状态的后续使用）
        let result = solver.check_sat_deadline(SourceLoc::unknown(), Duration::from_secs(60));
        assert_eq!(result, Sat);
    }
}

pub use z3_timeout::configure_z3_timeout;

#[cfg(test)]
mod transaction_tests;

// 私有属性只通过缓存镜像受控进出，不向调用方暴露核心字段。
impl From<DefAttrs> for crate::executor::path_cache::event::DefAttrs {
    fn from(value: DefAttrs) -> Self {
        Self { bits: value.attrs }
    }
}
impl From<crate::executor::path_cache::event::DefAttrs> for DefAttrs {
    fn from(value: crate::executor::path_cache::event::DefAttrs) -> Self {
        assert_eq!(value.bits & !3, 0, "缓存定义属性包含未知位");
        Self { attrs: value.bits }
    }
}
impl From<ReadOpts> for crate::executor::path_cache::event::ReadOpts {
    fn from(value: ReadOpts) -> Self {
        Self { is_exclusive: value.is_exclusive, is_ifetch: value.is_ifetch }
    }
}
impl From<crate::executor::path_cache::event::ReadOpts> for ReadOpts {
    fn from(value: crate::executor::path_cache::event::ReadOpts) -> Self {
        Self { is_exclusive: value.is_exclusive, is_ifetch: value.is_ifetch }
    }
}
impl From<WriteOpts> for crate::executor::path_cache::event::WriteOpts {
    fn from(value: WriteOpts) -> Self {
        Self { is_exclusive: value.is_exclusive }
    }
}
impl From<crate::executor::path_cache::event::WriteOpts> for WriteOpts {
    fn from(value: crate::executor::path_cache::event::WriteOpts) -> Self {
        Self { is_exclusive: value.is_exclusive }
    }
}

impl<B> Checkpoint<B> {
    pub(crate) fn path_cache_parts(&self) -> (usize, u32, &Arc<Option<Trace<B>>>) {
        (self.num, self.next_var, &self.trace)
    }
    pub(crate) fn from_path_cache_parts(num: usize, next_var: u32, trace: Arc<Option<Trace<B>>>) -> Self {
        Self { num, next_var, trace, cycles: 0 }
    }
}
impl<B> Trace<B> {
    pub(crate) fn path_cache_parts(&self) -> (usize, impl Iterator<Item = &Event<B>>, &Arc<Option<Trace<B>>>) {
        (self.checkpoints, self.head_events(), &self.tail)
    }
    pub(crate) fn path_cache_head(&self) -> (usize, impl Iterator<Item = &Event<B>>, Option<&Arc<TraceHead<B>>>) {
        (self.local_len(), self.local_events(), self.head_prefix.as_ref())
    }
    pub(crate) fn path_cache_prefix(events: Vec<Event<B>>) -> Arc<TraceHead<B>> {
        Arc::new(TraceHead { events, event_guards: Vec::new(), memory_events_before_arm: 0 })
    }
    pub(crate) fn from_path_cache_parts(
        checkpoints: usize,
        head: Vec<Event<B>>,
        head_prefix: Option<Arc<TraceHead<B>>>,
        tail: Arc<Option<Trace<B>>>,
    ) -> Self {
        Self { checkpoints, head, event_guards: Vec::new(), head_prefix, projected: None, tail }
    }
}

/// 仅单测使用的当前线程求解查询次数，不进入生产路径。
#[cfg(test)]
pub(crate) fn test_query_count() -> usize {
    z3_timeout::test_query_count()
}

#[cfg(test)]
impl<B: BV> Solver<'_, B> {
    /// 在独立求解器中核对活动路径的位宽和数据，包括事务内的守卫。
    pub(crate) fn assert_test_bitvector(&self, value: &Val<B>, expected: B) {
        use smtlib::Exp::{Bits, Neq, Or, Var};

        let info = SourceLoc::unknown();
        let mut config = Config::new();
        config.solver_options.no_smt = false;
        let context = Context::new(config);
        let mut verification = Solver::from_checkpoint(&context, self.checkpoint_snapshot());
        assert!(verification.check_sat(info).is_sat().unwrap(), "要验证的路径必须可达");
        let unequal = |actual, expected| Neq(Box::new(actual), Box::new(expected));
        let width = expected.len();
        let different = match value {
            Val::Bits(actual) => {
                assert_eq!(*actual, expected);
                return;
            }
            Val::Symbolic(data) => {
                assert_eq!(verification.length(*data), Some(width));
                unequal(Var(*data), Bits(expected.to_vec()))
            }
            Val::SymBits { data, len, cap } => {
                assert_eq!(verification.length(*data), Some(*cap));
                assert_eq!(verification.length(*len), Some(128));
                assert!(width <= *cap);
                let mut padded = expected.to_vec();
                padded.resize(*cap as usize, false);
                Or(
                    Box::new(unequal(Var(*len), smtlib::bits64(u64::from(width), 128))),
                    Box::new(unequal(Var(*data), Bits(padded))),
                )
            }
            _ => panic!("预期位向量，实际 {value:?}"),
        };
        assert!(verification.check_sat_with(&different, info).is_unsat().unwrap(), "{value:?} 与 {expected:?} 不同");
    }
}

// 只在显式内存采样时遍历；不创建 checkpoint、不翻译表达式、不查询 Z3。
impl<B: BV> Checkpoint<B> {
    pub fn estimated_bytes(&self, seen: &mut HashSet<usize>) -> usize {
        std::mem::size_of_val(self) + estimated_tail_bytes(&self.trace, seen)
    }
}
fn estimated_tail_bytes<B: BV>(tail: &Arc<Option<Trace<B>>>, seen: &mut HashSet<usize>) -> usize {
    let mut bytes = 0;
    let mut tail = tail;
    loop {
        if !seen.insert(Arc::as_ptr(tail) as usize) {
            break;
        }
        bytes += std::mem::size_of::<Option<Trace<B>>>();
        let Some(trace) = tail.as_ref() else {
            break;
        };
        bytes += trace.head.capacity() * std::mem::size_of::<Event<B>>()
            + trace.head.iter().map(crate::executor::stats::memory_stats::event_heap_bytes).sum::<usize>();
        if let Some(projected) = &trace.projected {
            bytes += error_snapshot::Segment::estimated_bytes(projected, seen);
        }
        if let Some(prefix) = &trace.head_prefix {
            if seen.insert(Arc::as_ptr(prefix) as usize) {
                bytes += std::mem::size_of::<TraceHead<B>>()
                    + prefix.events.capacity() * std::mem::size_of::<Event<B>>()
                    + prefix.events.iter().map(crate::executor::stats::memory_stats::event_heap_bytes).sum::<usize>()
                    + prefix.event_guards.capacity() * std::mem::size_of::<(usize, Exp<Sym>)>()
                    + prefix
                        .event_guards
                        .iter()
                        .map(|(_, guard)| crate::executor::stats::memory_stats::exp_heap_bytes(guard))
                        .sum::<usize>();
            }
        }
        tail = &trace.tail;
    }
    bytes
}
impl<B: BV> Solver<'_, B> {
    pub fn estimated_trace_bytes(&self, seen: &mut HashSet<usize>) -> usize {
        std::mem::size_of_val(&self.trace)
            + self.trace.head.capacity() * std::mem::size_of::<Event<B>>()
            + self.trace.head.iter().map(crate::executor::stats::memory_stats::event_heap_bytes).sum::<usize>()
            + estimated_tail_bytes(&self.trace.tail, seen)
    }
}

// 有界短探针的只读逐查询诊断。
pub(crate) use z3_timeout::{probe_query_event, probe_query_timings_enabled, thread_smt_check_count, ArmErrorSmtCall};

#[cfg(test)]
mod coi_tests;
