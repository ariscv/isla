// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
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

use std::error::Error;
use std::fmt;
use std::sync::Arc;

use crate::ir::Name;
use crate::source_loc::SourceLoc;
use crate::timeout::SmtTimeout;

pub trait IslaError {
    fn source_loc(&self) -> SourceLoc;
}

#[derive(Debug)]
pub enum VoidError {}

impl fmt::Display for VoidError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "void error")
    }
}

impl IslaError for VoidError {
    fn source_loc(&self) -> SourceLoc {
        SourceLoc::unknown()
    }
}

#[derive(Clone, Debug)]
pub enum SmtError {
    Timeout(Arc<SmtTimeout>),
}

impl SmtError {
    pub fn source_loc(&self) -> SourceLoc {
        match self {
            SmtError::Timeout(timeout) => timeout.source_loc(),
        }
    }
}

impl PartialEq for SmtError {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (SmtError::Timeout(lhs), SmtError::Timeout(rhs)) => Arc::ptr_eq(lhs, rhs),
        }
    }
}

impl Eq for SmtError {}

impl fmt::Display for SmtError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtError::Timeout(timeout) => write!(
                f,
                "SMT timeout during {:?} at {:?} after {:?} (operation wall {:?})",
                timeout.operation, timeout.source_loc, timeout.limit, timeout.operation_wall
            ),
        }
    }
}

impl Error for SmtError {}

#[derive(Debug)]
pub enum ExecError {
    /// 推演控制信号，区别于正常返回和异常终止；不是普通路径错误。
    /// 后续集成的推演边界必须捕获并回滚，禁止交给普通调度器或路径收尾。
    SpeculativeReject {
        reason: crate::executor::SpeculativeRejectReason,
        function: Name,
        pc: usize,
        location: SourceLoc,
    },
    Type(String, SourceLoc),
    VariableNotFound(String, SourceLoc),
    Unimplemented,
    AssertionFailure(Option<String>, SourceLoc),
    NoFunction(String, SourceLoc),
    Overflow,
    /// 内部整数转换需要由执行器保留可表示与溢出两条路径。
    IntegerConversion(crate::smt::smtlib::Exp<crate::smt::Sym>, SourceLoc),
    /// 消费者需要按条件分叉后重试，保留成功和错误路径。
    RetryCondition(crate::smt::smtlib::Exp<crate::smt::Sym>, SourceLoc),
    /// SMTLIB only supports fixed-length bitvectors. This error is
    /// raised if a bitvector width would become symbolic.
    SymbolicLength(&'static str, SourceLoc),
    /// Returned when there is no symbolic representation for a
    /// specific type. Certain types like strings are always assumed
    /// to be concrete.
    NoSymbolicType,
    /// Used for cases that should be unreachable (i.e. are definite
    /// errors).
    Unreachable(String),
    /// Used when we try to access memory that does not have any
    /// defined semantics.
    Unmapped,
    BadRead(&'static str),
    BadWrite(&'static str),
    NoElfEntry,
    OutOfBounds(&'static str),
    MatchFailure(SourceLoc),
    Timeout,
    Smt(SmtError),
    NoModel,
    Z3Error(String),
    Z3Unknown,
    /// Execution stopped because this function is in the stop_functions set
    Stopped(String),
    PCLimitReached(u64),
    BranchLimitReached(Name, usize),
    LoopLimitReached(Name, usize),
    DepthLimitReached,
    InconsistentRegisterReset,
    BadInterrupt(&'static str),
    IncompatibleMerge,
}

impl IslaError for ExecError {
    fn source_loc(&self) -> SourceLoc {
        use ExecError::*;
        match self {
            SpeculativeReject { location: info, .. }
            | Type(_, info)
            | AssertionFailure(_, info)
            | NoFunction(_, info)
            | RetryCondition(_, info)
            | IntegerConversion(_, info)
            | SymbolicLength(_, info)
            | VariableNotFound(_, info)
            | MatchFailure(info) => *info,
            Smt(error) => error.source_loc(),
            BranchLimitReached(_, _) | LoopLimitReached(_, _) | DepthLimitReached => SourceLoc::unknown(),
            Unimplemented
            | Overflow
            | NoSymbolicType
            | Unreachable(_)
            | Unmapped
            | BadRead(_)
            | BadWrite(_)
            | NoElfEntry
            | OutOfBounds(_)
            | Timeout
            | NoModel
            | Z3Error(_)
            | Z3Unknown
            | Stopped(_)
            | PCLimitReached(_)
            | InconsistentRegisterReset
            | BadInterrupt(_)
            | IncompatibleMerge => SourceLoc::unknown(),
        }
    }
}

impl ExecError {
    /// 普通调度和路径收尾不能接收推演控制信号；必须在任何日志、求模或收集之前调用。
    pub fn assert_normal_execution(&self) {
        if let Self::SpeculativeReject { .. } = self {
            panic!("推演拒绝泄漏到普通执行边界：{self:?}");
        }
    }
}

impl fmt::Display for ExecError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ExecError::*;
        match self {
            Type(msg, _) => write!(f, "Type error: {}", msg),
            VariableNotFound(v, _) => write!(f, "Variable {} not found", v),
            Unimplemented => write!(f, "Unimplemented"),
            SpeculativeReject { reason, function, pc, location } => {
                write!(f, "拒绝推演: {}，函数 {:?}，pc {}，位置 {:?}", reason, function, pc, location)
            }
            AssertionFailure(None, _) => write!(f, "Assertion failure"),
            AssertionFailure(Some(msg), _) => write!(f, "Assertion failure: {}", msg),
            NoFunction(func, _) => write!(f, "Function {} does not exist", func),
            Overflow => write!(f, "Integer overflow"),
            RetryCondition(_, _) => write!(f, "消费者需要按条件分叉重试"),
            IntegerConversion(_, _) => write!(f, "整数转换需要分叉检查范围"),
            SymbolicLength(func, _) => write!(f, "Symbolic (bit)vector length in {}", func),
            NoSymbolicType => write!(f, "No symbolic representation for type"),
            Unreachable(msg) => write!(f, "Unreachable: {}", msg),
            Unmapped => write!(f, "Unmapped memory"),
            BadRead(msg) => write!(f, "Bad read {}", msg),
            BadWrite(msg) => write!(f, "Bad write {}", msg),
            NoElfEntry => write!(f, "No entry point specified"),
            OutOfBounds(func) => write!(f, "Out of bounds error in {}", func),
            MatchFailure(_) => write!(f, "Pattern match failure"),
            Timeout => write!(f, "Timeout"),
            Smt(error) => write!(f, "{}", error),
            NoModel => write!(f, "No SMT model found"),
            Z3Error(msg) => write!(f, "SMT solver error: {}", msg),
            Z3Unknown => write!(f, "SMT solver returned unknown"),
            Stopped(func) => write!(f, "Execution stopped at {}", func),
            PCLimitReached(pc_value) => write!(f, "Executed instruction at {} more than specified limit", pc_value),
            BranchLimitReached(func, pc_value) => {
                write!(f, "Executed branch in {} at {} more than specified limit", func, pc_value)
            }
            LoopLimitReached(func, pc_value) => {
                write!(f, "Executed loop in {} at {} more than specified limit", func, pc_value)
            }
            DepthLimitReached => write!(f, "Execution depth limit reached"),
            InconsistentRegisterReset => write!(f, "Inconsistent register reset constraints"),
            BadInterrupt(msg) => write!(f, "Bad task interrupt: {}", msg),
            IncompatibleMerge => write!(f, "Incompatible merge"),
        }
    }
}

impl Error for ExecError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}
