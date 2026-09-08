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

#[cfg(feature = "smtperf")]
use std::time::Duration;
use std::time::Instant;

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
use crate::error::{ExecError, SmtError};
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
            .map(|&(member, enum_size, enum_name)| EnumMember { enum_id: EnumId::from_name(enum_name), member })
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
pub mod smtlib;
mod z3_timeout;
use dump::{timeout_dump_from_checkpoint, SmtDumpRequest, Z3SymbolNamer};
use smtlib::*;
use z3_timeout::{
    timeout_Z3_model_eval, timeout_Z3_solver_check, timeout_Z3_solver_check_assumptions,
    timeout_error as z3_timeout_error, Z3TimeoutError,
};

/// Snapshot of interaction with underlying solver that can be
/// efficiently cloned and shared between threads.
#[derive(Clone, Default)]
pub struct Checkpoint<B> {
    num: usize,
    next_var: u32,
    trace: Arc<Option<Trace<B>>>,
}

impl<B> Checkpoint<B> {
    pub fn new() -> Self {
        Checkpoint { num: 0, next_var: 0, trace: Arc::new(None) }
    }

    pub fn trace(&self) -> &Option<Trace<B>> {
        &self.trace
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

    pub fn is_uninteresting(self) -> bool {
        self.attrs & 1 > 0
    }
}

#[derive(Clone, Debug)]
pub enum Event<B> {
    Smt(Def, DefAttrs, SourceLoc),
    /// Fork ID, assertion, branch number, source location
    Fork(u32, Sym, u32, SourceLoc),
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
#[derive(Debug)]
pub struct Trace<B> {
    checkpoints: usize,
    head: Vec<Event<B>>,
    tail: Arc<Option<Trace<B>>>,
}

impl<B: BV> Trace<B> {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Trace { checkpoints: 0, head: Vec::new(), tail: Arc::new(None) }
    }

    pub fn checkpoint(&mut self, next_var: u32) -> Checkpoint<B> {
        let mut head = Vec::new();
        mem::swap(&mut self.head, &mut head);
        let tail = Arc::new(Some(Trace { checkpoints: self.checkpoints, head, tail: self.tail.clone() }));
        self.checkpoints += 1;
        self.tail = tail.clone();
        Checkpoint { num: self.checkpoints, trace: tail, next_var }
    }

    pub fn to_vec<'a>(&'a self) -> Vec<&'a Event<B>> {
        let mut vec: Vec<&'a Event<B>> = Vec::new();

        let mut current_head = &self.head;
        let mut current_tail = self.tail.as_ref();
        loop {
            for def in current_head.iter().rev() {
                vec.push(def)
            }
            match current_tail {
                Some(trace) => {
                    current_head = &trace.head;
                    current_tail = trace.tail.as_ref();
                }
                None => return vec,
            }
        }
    }
}

/// Config is a wrapper around the `Z3_config` type from the C
/// API. `Z3_del_config` is called when it is dropped.
pub struct Config {
    z3_cfg: Z3_config,
}

impl Config {
    pub fn new() -> Self {
        unsafe { Config { z3_cfg: Z3_mk_config() } }
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

pub fn global_set_param_value(id: &str, value: &str) {
    let id = CString::new(id).unwrap();
    let value = CString::new(value).unwrap();
    unsafe { Z3_global_param_set(id.as_ptr(), value.as_ptr()) }
}

/// Context is a wrapper around `Z3_context`.
pub struct Context {
    z3_ctx: Z3_context,
}

impl Context {
    pub fn new(cfg: Config) -> Self {
        unsafe { Context { z3_ctx: Z3_mk_context_rc(cfg.z3_cfg) } }
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
        unsafe { Z3_del_context(self.z3_ctx) }
    }
}

struct Enum {
    sort: Z3_sort,
    consts: Vec<Z3_func_decl>,
    testers: Vec<Z3_func_decl>,
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

            let z3_name = symbol_namer.enum_sort(self.ctx, name);
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

            for i in 0..size {
                Z3_inc_ref(ctx, Z3_func_decl_to_ast(ctx, consts[i]));
                Z3_inc_ref(ctx, Z3_func_decl_to_ast(ctx, testers[i]))
            }
            Z3_inc_ref(ctx, Z3_sort_to_ast(ctx, sort));

            self.enums.insert(name, Enum { sort, consts, testers });
        }
    }
}

impl Drop for Enums<'_> {
    fn drop(&mut self) {
        unsafe {
            let ctx = self.ctx.z3_ctx;
            for (_, e) in self.enums.drain() {
                for i in 0..e.consts.len() {
                    Z3_dec_ref(ctx, Z3_func_decl_to_ast(ctx, e.consts[i]));
                    Z3_dec_ref(ctx, Z3_func_decl_to_ast(ctx, e.testers[i]))
                }
                Z3_dec_ref(ctx, Z3_sort_to_ast(ctx, e.sort))
            }
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

static PUSH_ITE_BV: &[u8] = b"push_ite_bv\0";
static BV_LE_EXTRA: &[u8] = b"bv_le_extra\0";
static BV_SORT_AC: &[u8] = b"bv_sort_ac\0";

impl<'ctx> Ast<'ctx> {
    fn simplify(&mut self) {
        unsafe {
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

    fn mk_bvmul(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvmul, self, rhs)
    }

    fn mk_bvudiv(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvudiv, self, rhs)
    }

    fn mk_bvsdiv(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvsdiv, self, rhs)
    }

    fn mk_bvurem(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvurem, self, rhs)
    }

    fn mk_bvsrem(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvsrem, self, rhs)
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

    fn mk_fpa_is_nan(&self) -> Self {
        z3_unary_op!(Z3_mk_fpa_is_nan, self)
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
struct PerformanceInfo {}

#[cfg(feature = "smtperf")]
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
    decls: HashMap<Sym, Ast<'ctx>>,
    func_decls: HashMap<Sym, FuncDecl<'ctx>>,
    enums: Enums<'ctx>,
    z3_solver: Z3_solver,
    ctx: &'ctx Context,
    symbol_namer: Z3SymbolNamer,
    performance_info: PerformanceInfo,
}

impl<B> Drop for Solver<'_, B> {
    fn drop(&mut self) {
        unsafe {
            Z3_solver_dec_ref(self.ctx.z3_ctx, self.z3_solver);
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

fn model_bits_to_bv<B: BV>(bits: &[bool]) -> Result<B, ExecError> {
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

/// thread-interrupt wrapper 在 ModelEval 超时时构造最终 `SmtError::Timeout`
/// 所需的调用边界信息。它不是另一套错误类型。
struct ModelEvalTimeoutContext {
    started: Instant,
    dump_request: SmtDumpRequest,
}

impl<'ctx, B: BV> Model<'ctx, B> {
    pub fn new(solver: &'ctx Solver<'ctx, B>) -> Self {
        unsafe {
            let z3_model = Z3_solver_get_model(solver.ctx.z3_ctx, solver.z3_solver);
            Z3_model_inc_ref(solver.ctx.z3_ctx, z3_model);
            Model { z3_model, solver, ctx: solver.ctx, complete_model: false }
        }
    }

    pub fn set_complete_model(&mut self, b: bool) {
        self.complete_model = b;
    }

    fn model_eval_timeout_error(&self, timeout: &ModelEvalTimeoutContext) -> ExecError {
        let dump = timeout_dump_from_checkpoint(self.solver.checkpoint_snapshot(), timeout.dump_request.clone());
        ExecError::Smt(z3_timeout_error(SmtOperation::ModelEval, SourceLoc::unknown(), timeout.started.elapsed(), dump))
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
            Err(Z3TimeoutError::Interrupted) => Err(self.model_eval_timeout_error(timeout_context)),
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
        let var_ast = match self.solver.decls.get(&var) {
            None => return Err(ExecError::Type(format!("Unbound variable {:?}", &var), SourceLoc::unknown())),
            Some(ast) => ast.clone(),
        };
        self.get_ast(var_ast, SmtDumpRequest::GetValues { expressions: vec![Exp::Var(var)] })
    }

    /// 只读取输出多样化支持的 enum、bool 和 bitvector；其它合法 SMT sort 不参与取值选择。
    pub fn get_finite_domain_var(&mut self, var: Sym) -> Result<Option<ModelVal>, ExecError> {
        let var_ast = match self.solver.decls.get(&var) {
            None => return Err(ExecError::Type(format!("Unbound variable {:?}", &var), SourceLoc::unknown())),
            Some(ast) => ast.clone(),
        };
        let sort_kind = unsafe {
            let sort = Z3_get_sort(self.ctx.z3_ctx, var_ast.z3_ast);
            Z3_inc_ref(self.ctx.z3_ctx, Z3_sort_to_ast(self.ctx.z3_ctx, sort));
            let sort_kind = Z3_get_sort_kind(self.ctx.z3_ctx, sort);
            Z3_dec_ref(self.ctx.z3_ctx, Z3_sort_to_ast(self.ctx.z3_ctx, sort));
            sort_kind
        };

        match sort_kind {
            SortKind::Bool | SortKind::BV | SortKind::Datatype => {
                self.get_ast(var_ast, SmtDumpRequest::GetValues { expressions: vec![Exp::Var(var)] }).map(Some)
            }
            SortKind::Array | SortKind::FloatingPoint | SortKind::RoundingMode => Ok(None),
            _ => panic!("不支持的符号常量 sort: {:?}", sort_kind),
        }
    }

    pub fn get_exp(&mut self, exp: &Exp<Sym>) -> Result<ModelVal, ExecError> {
        let ast = self.solver.translate_exp(exp);
        self.get_ast(ast, SmtDumpRequest::GetValues { expressions: vec![exp.clone()] })
    }

    pub fn get_val(&mut self, var: &Val<B>) -> Result<Val<B>, ExecError> {
        use crate::ir::Val::*;
        match var {
            Symbolic(sym) => {
                let model_val = self.get_var(*sym)?;
                match model_val {
                    ModelVal::Exp(Exp::Bits64(bv)) => Ok(Val::Bits(B::new(bv.lower_u64(), bv.len()))),
                    ModelVal::Exp(Exp::Bool(b)) => Ok(Val::Bool(b)),
                    ModelVal::Exp(Exp::Enum(m)) => Ok(Val::Enum(m)),
                    ModelVal::Exp(Exp::Bits(bv)) => Ok(Val::Bits(model_bits_to_bv(&bv)?)),
                    ModelVal::Exp(exp) => {
                        // 对于其他复杂的表达式，返回错误
                        Err(ExecError::Type(
                            format!("Unsupported Exp type in get_val: {:?}", exp),
                            SourceLoc::unknown(),
                        ))
                    }
                    ModelVal::Arbitrary(ty) => match ty {
                        smtlib::Ty::BitVec(len) => Ok(Val::Bits(B::new(0, len))),
                        smtlib::Ty::Bool => Ok(Val::Bool(false)),
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
                    match segment {
                        crate::ir::BitsSegment::Symbolic(sym) => {
                            let model_val = self.get_var(*sym)?;
                            match model_val {
                                ModelVal::Exp(Exp::Bits64(bv)) => {
                                    new_segments
                                        .push(crate::ir::BitsSegment::Concrete(B::new(bv.lower_u64(), bv.len())));
                                }
                                ModelVal::Exp(Exp::Bits(bv)) => {
                                    new_segments.push(crate::ir::BitsSegment::Concrete(model_bits_to_bv(&bv)?));
                                }
                                ModelVal::Arbitrary(smtlib::Ty::BitVec(len)) => {
                                    new_segments.push(crate::ir::BitsSegment::Concrete(B::new(0, len)));
                                }
                                _ => {
                                    return Err(ExecError::Type(
                                        format!("Unsupported model value for BitsSegment: {:?}", model_val),
                                        SourceLoc::unknown(),
                                    ));
                                }
                            }
                        }
                        crate::ir::BitsSegment::Concrete(bv) => {
                            new_segments.push(crate::ir::BitsSegment::Concrete(*bv));
                        }
                    }
                }
                Ok(MixedBits(new_segments))
            }

            SymbolicCtor(sym, fields) => {
                // 对于符号构造器，获取其枚举成员并递归处理字段
                let model_val = self.get_var(*sym)?;
                match model_val {
                    ModelVal::Exp(Exp::Enum(enum_member)) => {
                        let mut new_fields =
                            ahash::HashMap::with_capacity_and_hasher(fields.len(), ahash::RandomState::new());
                        for (name, val) in fields {
                            new_fields.insert(*name, self.get_val(&val)?);
                        }
                        // 这里需要确定枚举成员对应的 Name
                        // 假设我们可以从 enum_member 获取对应的名称
                        Err(ExecError::Type(
                            format!("SymbolicCtor resolution not fully implemented for {:?}", enum_member),
                            SourceLoc::unknown(),
                        ))
                    }
                    _ => Err(ExecError::Type(
                        format!("Expected enum member for SymbolicCtor, got: {:?}", model_val),
                        SourceLoc::unknown(),
                    )),
                }
            }
        }
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
    Unknown,
    Error(SmtError),
}

use SmtResult::*;

impl SmtResult {
    pub fn is_sat(&self) -> Result<bool, ExecError> {
        match self {
            Sat => Ok(true),
            Unsat => Ok(false),
            Unknown => Err(ExecError::Z3Unknown),
            Error(error) => Err(ExecError::Smt(error.clone())),
        }
    }

    pub fn is_unsat(&self) -> Result<bool, ExecError> {
        match self {
            Sat => Ok(false),
            Unsat => Ok(true),
            Unknown => Err(ExecError::Z3Unknown),
            Error(error) => Err(ExecError::Smt(error.clone())),
        }
    }

    pub fn is_unknown(&self) -> bool {
        matches!(self, Unknown)
    }
}

static DEFAULT_TASTIC_STR: &[u8] = b"default\0";
static TASTIC_STR: OnceLock<CString> = OnceLock::new();
static SEED_STR: &[u8] = b"seed\0";
static RANDOM_SEED_STR: &[u8] = b"random_seed\0";

pub fn configure_tastic(tastic: Option<&str>) {
    let Some(tastic) = tastic else { return };
    assert!(!tastic.is_empty(), "--tastic 不能为空");
    let tastic = CString::new(tastic).expect("--tastic 不能包含 NUL 字节");

    if let Some(configured) = TASTIC_STR.get() {
        assert_eq!(configured, &tastic, "--tastic 被重复配置为不同值");
    } else {
        TASTIC_STR.set(tastic).expect("--tastic 配置发生并发冲突");
    }
}

fn tastic() -> &'static CStr {
    match TASTIC_STR.get() {
        Some(tastic) => tastic.as_c_str(),
        None => unsafe { CStr::from_bytes_with_nul_unchecked(DEFAULT_TASTIC_STR) },
    }
}

// 不同 Z3 solver 暴露的随机种子参数名不同，按实际参数表选择。
unsafe fn z3_seed_param_name(ctx: Z3_context, solver: Z3_solver) -> &'static [u8] {
    let param_descrs = Z3_solver_get_param_descrs(ctx, solver);
    Z3_param_descrs_inc_ref(ctx, param_descrs);
    let mut seed_param_name = RANDOM_SEED_STR;
    for i in 0..Z3_param_descrs_size(ctx, param_descrs) {
        let symbol = Z3_param_descrs_get_name(ctx, param_descrs, i);
        if Z3_get_symbol_kind(ctx, symbol) == SymbolKind::String {
            let name = CStr::from_ptr(Z3_get_symbol_string(ctx, symbol)).to_bytes();
            if name == &SEED_STR[..SEED_STR.len() - 1] {
                seed_param_name = SEED_STR;
                break;
            }
        }
    }
    Z3_param_descrs_dec_ref(ctx, param_descrs);
    seed_param_name
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    pub fn new(ctx: &'ctx Context) -> Self {
        Self::new_with_symbol_namer(ctx, Z3SymbolNamer::Integer)
    }

    fn new_with_symbol_namer(ctx: &'ctx Context, symbol_namer: Z3SymbolNamer) -> Self {
        unsafe {
            // 始终通过 tactic 创建 solver，既允许命令行切换 tactic，也避免按 logic 名称创建
            // QF_AUFBV solver 时枚举支持不完整而导致 Z3 崩溃。
            let solver_tactic = Z3_mk_tactic(ctx.z3_ctx, tastic().as_ptr());
            Z3_tactic_inc_ref(ctx.z3_ctx, solver_tactic);
            let z3_solver = Z3_mk_solver_from_tactic(ctx.z3_ctx, solver_tactic);
            Z3_solver_inc_ref(ctx.z3_ctx, z3_solver);
            Z3_tactic_dec_ref(ctx.z3_ctx, solver_tactic);

            let z3_params = Z3_mk_params(ctx.z3_ctx);
            Z3_params_inc_ref(ctx.z3_ctx, z3_params);

            let seed_symbol = Z3_mk_string_symbol(
                ctx.z3_ctx,
                CStr::from_bytes_with_nul_unchecked(z3_seed_param_name(ctx.z3_ctx, z3_solver)).as_ptr(),
            );
            Z3_params_set_uint(ctx.z3_ctx, z3_params, seed_symbol, fresh_random_seed());
            Z3_solver_set_params(ctx.z3_ctx, z3_solver, z3_params);

            Z3_params_dec_ref(ctx.z3_ctx, z3_params);

            Solver {
                ctx,
                z3_solver,
                next_var: 0,
                def_attrs: DefAttrs::default(),
                cycles: 0,
                trace: Trace::new(),
                decls: HashMap::new(),
                func_decls: HashMap::new(),
                enums: Enums::new(ctx),
                symbol_namer,
                performance_info: PerformanceInfo::new(),
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

    fn translate_exp(&self, exp: &Exp<Sym>) -> Ast<'ctx> {
        use Exp::*;
        match exp {
            Var(v) => match self.decls.get(v) {
                None => panic!("Could not get Z3 func_decl {}", *v),
                Some(ast) => ast.clone(),
            },
            Bits(bv) => Ast::mk_bv(self.ctx, bv.len().try_into().unwrap(), bv),
            Bits64(bv) => Ast::mk_bv_u64(self.ctx, bv.len(), bv.lower_u64()),
            Enum(e) => Ast::mk_enum_member(&self.enums, e.enum_id, e.member),
            Bool(b) => Ast::mk_bool(self.ctx, *b),
            Not(exp) => Ast::mk_not(&self.translate_exp(exp)),
            Eq(lhs, rhs) => Ast::mk_eq(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Neq(lhs, rhs) => Ast::mk_not(&Ast::mk_eq(&self.translate_exp(lhs), &self.translate_exp(rhs))),
            And(lhs, rhs) => Ast::mk_and(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Or(lhs, rhs) => Ast::mk_or(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvnot(exp) => Ast::mk_bvnot(&self.translate_exp(exp)),
            Bvand(lhs, rhs) => Ast::mk_bvand(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvor(lhs, rhs) => Ast::mk_bvor(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvxor(lhs, rhs) => Ast::mk_bvxor(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvnand(lhs, rhs) => Ast::mk_bvnand(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvnor(lhs, rhs) => Ast::mk_bvnor(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvxnor(lhs, rhs) => Ast::mk_bvxnor(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvneg(exp) => Ast::mk_bvneg(&self.translate_exp(exp)),
            Bvadd(lhs, rhs) => Ast::mk_bvadd(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvsub(lhs, rhs) => Ast::mk_bvsub(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvmul(lhs, rhs) => Ast::mk_bvmul(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvudiv(lhs, rhs) => Ast::mk_bvudiv(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvsdiv(lhs, rhs) => Ast::mk_bvsdiv(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvurem(lhs, rhs) => Ast::mk_bvurem(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvsrem(lhs, rhs) => Ast::mk_bvsrem(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvsmod(lhs, rhs) => Ast::mk_bvsmod(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvult(lhs, rhs) => Ast::mk_bvult(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvslt(lhs, rhs) => Ast::mk_bvslt(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvule(lhs, rhs) => Ast::mk_bvule(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvsle(lhs, rhs) => Ast::mk_bvsle(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvuge(lhs, rhs) => Ast::mk_bvuge(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvsge(lhs, rhs) => Ast::mk_bvsge(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvugt(lhs, rhs) => Ast::mk_bvugt(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvsgt(lhs, rhs) => Ast::mk_bvsgt(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Extract(hi, lo, bv) => self.translate_exp(bv).extract(*hi, *lo),
            ZeroExtend(i, bv) => self.translate_exp(bv).zero_extend(*i),
            SignExtend(i, bv) => self.translate_exp(bv).sign_extend(*i),
            Bvshl(lhs, rhs) => Ast::mk_bvshl(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvlshr(lhs, rhs) => Ast::mk_bvlshr(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvashr(lhs, rhs) => Ast::mk_bvashr(&self.translate_exp(lhs), &self.translate_exp(rhs)),
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
        }
    }

    fn z3_assert(&mut self, exp: &Exp<Sym>) {
        let mut ast = self.translate_exp(exp);
        ast.simplify();
        unsafe {
            Z3_solver_assert(self.ctx.z3_ctx, self.z3_solver, ast.z3_ast);
        }
    }

    pub fn get_enum(&mut self, id: Name, size: usize) -> EnumId {
        if !self.enums.enums.contains_key(&id) {
            self.add(Def::DefineEnum(id, size))
        };
        EnumId { id }
    }

    fn add_internal(&mut self, def: &Def, info: SourceLoc) {
        match &def {
            Def::Assert(exp) => {
                let vars = exp.variables();
                if cfg!(feature = "smtperf") {
                    for v1 in vars.iter() {
                        for v2 in vars.iter() {
                            if v1 != v2 {
                                self.performance_info.add_var_edge(v1, v2)
                            }
                        }
                    }
                }
                self.z3_assert(exp)
            }
            Def::DeclareConst(v, ty) => {
                self.performance_info.add_var_node(*v, info);
                let fd = FuncDecl::new(self.ctx, *v, &self.enums, &[], ty, &self.symbol_namer);
                self.decls.insert(*v, Ast::mk_constant(&fd));
            }
            Def::DeclareFun(v, arg_tys, result_ty) => {
                if cfg!(feature = "smtperf") {
                    self.performance_info.add_var_node(*v, info);
                }
                let fd = FuncDecl::new(self.ctx, *v, &self.enums, arg_tys, result_ty, &self.symbol_namer);
                self.func_decls.insert(*v, fd);
            }
            Def::DefineConst(v, exp) => {
                if cfg!(feature = "smtperf") {
                    self.performance_info.add_var_node(*v, info);
                    for used in exp.variables().iter() {
                        self.performance_info.add_var_edge(v, used);
                        self.performance_info.add_var_edge(used, v)
                    }
                }
                let mut ast = self.translate_exp(exp);
                ast.simplify();
                self.decls.insert(*v, ast);
            }
            Def::DefineEnum(name, size) => {
                if !self.enums.enums.contains_key(name) {
                    // Keep enum sort names deterministic across checkpoint replay.
                    // Member constructor names do not need to be stable: get_ast
                    // matches constructors through recognizers from the model
                    // value's own sort.
                    let members: Vec<Sym> = (0..*size).map(|_| self.fresh()).collect();
                    self.enums.add_enum(*name, &members, &self.symbol_namer)
                }
            }
        }
    }

    pub fn length(&mut self, v: Sym) -> Option<u32> {
        match self.decls.get(&v) {
            Some(ast) => unsafe {
                let z3_ctx = self.ctx.z3_ctx;
                let z3_sort = Z3_get_sort(z3_ctx, ast.z3_ast);
                Z3_inc_ref(z3_ctx, Z3_sort_to_ast(z3_ctx, z3_sort));
                if Z3_get_sort_kind(z3_ctx, z3_sort) == SortKind::BV {
                    let sz = Z3_get_bv_sort_size(z3_ctx, z3_sort);
                    Z3_dec_ref(z3_ctx, Z3_sort_to_ast(z3_ctx, z3_sort));
                    Some(sz)
                } else {
                    Z3_dec_ref(z3_ctx, Z3_sort_to_ast(z3_ctx, z3_sort));
                    None
                }
            },
            None => None,
        }
    }

    pub fn is_bitvector(&mut self, v: Sym) -> bool {
        match self.decls.get(&v) {
            Some(ast) => unsafe {
                let z3_ctx = self.ctx.z3_ctx;
                let z3_sort = Z3_get_sort(z3_ctx, ast.z3_ast);
                Z3_inc_ref(z3_ctx, Z3_sort_to_ast(z3_ctx, z3_sort));
                let result = Z3_get_sort_kind(z3_ctx, z3_sort) == SortKind::BV;
                Z3_dec_ref(z3_ctx, Z3_sort_to_ast(z3_ctx, z3_sort));
                result
            },
            None => false,
        }
    }

    pub fn with_def_attrs<F, A>(&mut self, attrs: DefAttrs, f: F) -> A
    where
        F: Fn(&mut Self) -> A,
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
        self.add_internal(&def, SourceLoc::unknown());
        self.trace.head.push(Event::Smt(def, self.def_attrs, SourceLoc::unknown()))
    }

    pub fn add_with_location(&mut self, def: Def, info: SourceLoc) {
        self.add_internal(&def, info);
        self.trace.head.push(Event::Smt(def, self.def_attrs, info))
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
        self.add_event(Event::Cycle)
    }

    pub fn get_cycle_count(&self) -> i128 {
        self.cycles
    }

    fn add_event_internal(&mut self, event: &Event<B>) {
        if let Event::Smt(def, _, info) = event {
            self.add_internal(def, *info)
        };
    }

    pub fn add_event(&mut self, event: Event<B>) {
        self.add_event_internal(&event);
        self.trace.head.push(event)
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
        let mut checkpoints: Vec<&[Event<B>]> = Vec::with_capacity(num);
        let mut next = &*trace;
        loop {
            match next {
                None => break,
                Some(tr) => {
                    checkpoints.push(&tr.head);
                    next = &*tr.tail
                }
            }
        }
        assert!(checkpoints.len() == num);
        for events in checkpoints.iter().rev() {
            for event in *events {
                self.add_event_internal(event)
            }
        }
        self.trace.checkpoints = num;
        self.trace.tail = trace
    }

    pub fn from_checkpoint(ctx: &'ctx Context, Checkpoint { num, next_var, trace }: Checkpoint<B>) -> Self {
        let mut solver = Solver::new(ctx);
        solver.replay(num, trace);
        solver.next_var = next_var;
        solver
    }

    pub fn check_sat_with(&mut self, exp: &Exp<Sym>, info: SourceLoc) -> SmtResult {
        let started = Instant::now();
        self.performance_info.start();

        let ast = self.translate_exp(exp);
        let assumptions = [ast.z3_ast];
        let z3_result = match timeout_Z3_solver_check_assumptions(self.ctx.z3_ctx, self.z3_solver, &assumptions, info) {
            Ok(result) => result,
            Err(Z3TimeoutError::Interrupted) => {
                let dump =
                    timeout_dump_from_checkpoint(self.checkpoint_snapshot(), SmtDumpRequest::CheckSatWith(exp.clone()));
                return Error(z3_timeout_error(SmtOperation::CheckSatAssuming, info, started.elapsed(), dump));
            }
        };
        let result = if z3_result == Z3_L_TRUE {
            Sat
        } else if z3_result == Z3_L_FALSE {
            Unsat
        } else {
            Unknown
        };

        self.performance_info.assign_cost(exp);
        result
    }

    pub fn trace(&self) -> &Trace<B> {
        &self.trace
    }

    pub fn check_sat(&mut self, info: SourceLoc) -> SmtResult {
        let started = Instant::now();
        let z3_result = match timeout_Z3_solver_check(self.ctx.z3_ctx, self.z3_solver, info) {
            Ok(result) => result,
            Err(Z3TimeoutError::Interrupted) => {
                let dump = timeout_dump_from_checkpoint(self.checkpoint_snapshot(), SmtDumpRequest::CheckSat);
                return Error(z3_timeout_error(SmtOperation::CheckSat, info, started.elapsed(), dump));
            }
        };
        let result = if z3_result == Z3_L_TRUE {
            Sat
        } else if z3_result == Z3_L_FALSE {
            Unsat
        } else {
            Unknown
        };
        result
    }

    pub fn dump_solver(&mut self, filename: &str) {
        let mut file = std::fs::File::create(filename).expect("Failed to open solver dump file");
        unsafe {
            let s = Z3_solver_to_string(self.ctx.z3_ctx, self.z3_solver);
            let cs = CStr::from_ptr(s);
            file.write_all(cs.to_bytes()).expect("Failed to write solver dump");
        }
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

/// 已配置的单次 SMT operation deadline（`--smt-timeout`）。
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
mod tests {
    use std::sync::Arc;
    use std::time::Duration;

    use crate::bitvector::b64::B64;
    use crate::timeout::{SmtDumpSource, SmtOperation, SmtTimeout, TimeoutSmtDump};

    use super::Def::*;
    use super::Exp::*;
    use super::*;

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
        assert_eq!(two_calls.calls, 2);
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
            limit: Duration::from_secs(10),
            operation_wall: Duration::from_secs(11),
            dump: Arc::new(TimeoutSmtDump::new(Arc::new(FixedDump))),
        })
    }

    #[test]
    fn configured_tastic_is_used_by_solver() {
        configure_tastic(Some("qfaufbv"));
        assert_eq!(tastic().to_bytes(), b"qfaufbv");

        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        assert_eq!(solver.check_sat(SourceLoc::unknown()), Sat);
    }

    #[test]
    fn smt_timeout_result_preserves_error_artifact_identity() {
        let timeout = timeout_artifact();
        let same = SmtResult::Error(SmtError::Timeout(timeout.clone()));
        let same_again = SmtResult::Error(SmtError::Timeout(timeout.clone()));
        let different = SmtResult::Error(SmtError::Timeout(timeout_artifact()));

        assert_eq!(same, same_again);
        assert_ne!(same, different);
        match same.is_sat() {
            Err(ExecError::Smt(SmtError::Timeout(error))) => assert!(Arc::ptr_eq(&error, &timeout)),
            result => panic!("unexpected timeout conversion: {:?}", result),
        }
    }

    #[test]
    fn bv_macro() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        solver.add(Assert(Eq(Box::new(bv!("0110")), Box::new(bv!("1001")))));
        assert!(solver.check_sat(SourceLoc::unknown()) == Unsat);
    }

    #[test]
    fn get_const() {
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
    fn local_model_debug_preserves_original_model_text_semantics() {
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
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let e = solver.get_enum(Name::from_u32(11), 1);
        let v = solver.declare_const(Ty::Enum(e), SourceLoc::unknown());
        solver.assert_eq(Var(v), Enum(e.first_member()));

        let checkpoint = checkpoint(&mut solver);
        let mut replayed = Solver::from_checkpoint(&ctx, checkpoint);
        assert_eq!(replayed.check_sat(SourceLoc::unknown()), Sat);

        let mut model = Model::new(&replayed);
        assert_eq!(model.get_var(v).unwrap().unwrap_exp(), Enum(e.first_member()));
    }

    #[test]
    fn get_multi_member_enum_const_after_checkpoint_replay() {
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
        assert_eq!(replayed.check_sat(SourceLoc::unknown()), Sat);

        let mut model = Model::new(&replayed);
        assert_eq!(model.get_var(v).unwrap().unwrap_exp(), Enum(member));
    }

    #[test]
    fn get_struct_with_enum_field_after_checkpoint_replay() {
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
}

pub use z3_timeout::configure_z3_timeout;
