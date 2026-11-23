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
use std::time::Duration;

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

// 从枚举声明生成标签，包含载荷的变体只匹配其判别类型。
macro_rules! qualified_reason_enum {
    ($(#[$enum_attr:meta])* $vis:vis enum $name:ident {
        $($(#[$attr:meta])* $variant:ident $(($($tuple:tt)*))? $({$($fields:tt)*})?,)*
    }) => {
        $(#[$enum_attr])*
        $vis enum $name {
            $($(#[$attr])* $variant $(($($tuple)*))? $({$($fields)*})?,)*
        }

        impl $name {
            pub(crate) const fn reason_name(&self) -> &'static str {
                match self {
                    $(qualified_reason_enum!(@pattern $variant $(($($tuple)*))? $({$($fields)*})?) =>
                        qualified_reason_enum!(@name $name, $variant),)*
                }
            }
        }
    };
    (@pattern $variant:ident) => { Self::$variant };
    (@pattern $variant:ident ($($tuple:tt)*)) => { Self::$variant(..) };
    (@pattern $variant:ident {$($fields:tt)*}) => { Self::$variant { .. } };
    (@name $name:ident, $variant:ident) => { concat!(stringify!($name), "::", stringify!($variant)) };
}
pub(crate) use qualified_reason_enum;

qualified_reason_enum! {
    #[derive(Clone, Debug)]
    pub enum SmtError {
        FiniteDomain { source_loc: SourceLoc, symbol: crate::smt::Sym, width: u32, candidates: Option<Vec<String>> },
        DeferredQuery { source_loc: SourceLoc, purpose: &'static str },
        NoSmt { reason: &'static str, source_loc: SourceLoc },
        Z3Timeout(Z3Timeout),
        Z3ResourceExhausted(Z3QueryFailure),
        Z3Unknown(Z3QueryFailure),
    }
}

#[derive(Clone, Debug)]
pub enum Z3Timeout {
    Interrupted(Arc<SmtTimeout>),
    Native(Z3QueryFailure),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Z3QueryFailure {
    pub reason: String,
    pub source_loc: SourceLoc,
    pub purpose: &'static str,
    pub wall: Duration,
    pub limit: Option<Duration>,
}

impl SmtError {
    pub fn reject_reason(&self) -> crate::executor::SpeculativeRejectReason {
        use crate::executor::SpeculativeRejectReason::*;
        match self {
            Self::FiniteDomain { .. } => UnknownFiniteDomain,
            Self::Z3Timeout(_) => Z3Timeout,
            Self::Z3ResourceExhausted(_) => Z3ResourceExhausted,
            Self::Z3Unknown(_) => UnknownZ3,
            Self::DeferredQuery { .. } | Self::NoSmt { .. } => UnknownDeferredMode,
        }
    }

    /// Z3 原生返回 UNDEF 时的诊断。线程中断另外携带可回放的转储。
    pub(crate) fn z3_query_failure(&self) -> Option<&Z3QueryFailure> {
        match self {
            Self::Z3Timeout(Z3Timeout::Native(query)) | Self::Z3ResourceExhausted(query) | Self::Z3Unknown(query) => {
                Some(query)
            }
            _ => None,
        }
    }

    pub fn diagnostic(&self) -> serde_json::Value {
        use serde_json::json;
        let mut details = match self {
            Self::FiniteDomain { symbol, width, candidates, .. } => {
                json!({"purpose":"symbolic_value_enumeration","symbol":symbol.as_u32(),"width":width,"candidates":candidates})
            }
            Self::DeferredQuery { purpose, .. } => json!({"purpose":purpose}),
            Self::NoSmt { reason, .. } => json!({"purpose":reason,"no_smt":true}),
            Self::Z3Timeout(Z3Timeout::Native(Z3QueryFailure { reason, purpose, wall, limit, .. }))
            | Self::Z3ResourceExhausted(Z3QueryFailure { reason, purpose, wall, limit, .. })
            | Self::Z3Unknown(Z3QueryFailure { reason, purpose, wall, limit, .. }) => json!({
                "purpose":purpose,"reason_unknown":reason,"seconds":wall.as_secs_f64(),
                "limit_seconds":limit.map(|duration| duration.as_secs_f64())
            }),
            Self::Z3Timeout(Z3Timeout::Interrupted(timeout)) => {
                json!({"purpose":timeout.query_purpose,"operation":format!("{:?}",timeout.operation),
                "seconds":timeout.operation_wall.as_secs_f64(),"limit_seconds":timeout.limit.as_secs_f64()})
            }
        };
        details["reason"] = json!(self.reason_name());
        details
    }

    pub fn source_loc(&self) -> SourceLoc {
        match self {
            Self::Z3Timeout(Z3Timeout::Interrupted(timeout)) => timeout.source_loc(),
            Self::Z3Timeout(Z3Timeout::Native(query)) | Self::Z3ResourceExhausted(query) | Self::Z3Unknown(query) => {
                query.source_loc
            }
            Self::FiniteDomain { source_loc, .. }
            | Self::DeferredQuery { source_loc, .. }
            | Self::NoSmt { source_loc, .. } => *source_loc,
        }
    }
}

impl PartialEq for SmtError {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::FiniteDomain { source_loc: a, symbol: x, width: w, candidates: c },
                Self::FiniteDomain { source_loc: b, symbol: y, width: v, candidates: d },
            ) => (a, x, w, c) == (b, y, v, d),
            (Self::DeferredQuery { source_loc: a, purpose: x }, Self::DeferredQuery { source_loc: b, purpose: y }) => {
                (a, x) == (b, y)
            }
            (Self::Z3Timeout(Z3Timeout::Interrupted(lhs)), Self::Z3Timeout(Z3Timeout::Interrupted(rhs))) => {
                Arc::ptr_eq(lhs, rhs)
            }
            (SmtError::NoSmt { reason: a, source_loc: x }, SmtError::NoSmt { reason: b, source_loc: y }) => {
                a == b && x == y
            }
            (Self::Z3Timeout(Z3Timeout::Native(lhs)), Self::Z3Timeout(Z3Timeout::Native(rhs)))
            | (Self::Z3ResourceExhausted(lhs), Self::Z3ResourceExhausted(rhs))
            | (Self::Z3Unknown(lhs), Self::Z3Unknown(rhs)) => lhs == rhs,
            _ => false,
        }
    }
}

impl Eq for SmtError {}

impl fmt::Display for SmtError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let variant = self.reason_name();
        let query = match self {
            Self::FiniteDomain { source_loc, symbol, width, candidates } => {
                return write!(
                    f,
                    "{variant}: v{} ({} 位)，候选 {:?}，位置 {:?}",
                    symbol.as_u32(),
                    width,
                    candidates,
                    source_loc
                );
            }
            Self::DeferredQuery { source_loc, purpose } => {
                return write!(f, "{variant}: {purpose}，位置 {source_loc:?}");
            }
            Self::NoSmt { reason, source_loc } => {
                return write!(f, "{variant}: 无 SMT 无法继续：{reason}，位置{source_loc:?}");
            }
            Self::Z3Timeout(Z3Timeout::Interrupted(timeout)) => {
                return write!(
                    f,
                    "{variant}: Z3 调用 {:?} 在 {:?} 中断，限时 {:?}，耗时 {:?}",
                    timeout.operation, timeout.source_loc, timeout.limit, timeout.operation_wall
                );
            }
            Self::Z3Timeout(Z3Timeout::Native(query)) | Self::Z3ResourceExhausted(query) | Self::Z3Unknown(query) => {
                query
            }
        };
        write!(
            f,
            "{variant}: Z3 返回 {:?}，用途 {}，位置 {:?}，耗时 {:?}",
            query.reason, query.purpose, query.source_loc, query.wall
        )
    }
}

impl Error for SmtError {}

#[derive(Clone, Debug)]
pub enum ExecError {
    /// 推演控制信号，区别于正常返回和异常终止；不是普通路径错误。
    /// 后续集成的推演边界必须捕获并回滚，禁止交给普通调度器或路径收尾。
    SpeculativeReject {
        cause: Option<Box<SmtError>>,
        reason: crate::executor::SpeculativeRejectReason,
        function: Name,
        pc: usize,
        location: SourceLoc,
    },
    Type(String, SourceLoc),
    VariableNotFound(String, SourceLoc),
    Unimplemented,
    AssertionFailure(Option<String>, SourceLoc),
    ReachableExecutionError {
        message: String,
        location: String,
    },
    NoFunction(String, SourceLoc),
    Overflow,
    /// 内部整数转换需要由执行器保留可表示与溢出两条路径。
    IntegerConversion(crate::smt::smtlib::Exp<crate::smt::Sym>, SourceLoc),
    /// 消费者需要按条件分叉后重试，保留成功和错误路径。
    RetryCondition(crate::smt::smtlib::Exp<crate::smt::Sym>, SourceLoc),
    /// 具体消费者要求按候选值的守卫重试。
    ConcreteChoice(crate::smt::Sym, SourceLoc),
    /// SMTLIB only supports fixed-length bitvectors. This error is
    /// raised if a bitvector width would become symbolic.
    SymbolicLength(&'static str, SourceLoc),
    /// 原语需要一个具体的自然数，且能接纳范围内的每个候选。
    SymbolicNatural {
        symbol: crate::smt::Sym,
        minimum: u32,
        maximum: u32,
        operation: &'static str,
        location: SourceLoc,
    },
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
    Unproven(SmtError),
    /// 候选与剩余约束均不可继续，由探索循环转为 Run::Dead。
    SolverDroppedPath,
    /// Execution stopped because this function is in the stop_functions set
    Stopped(String),
    /// 样本输出会话的正常停止，由枚举器收尾，不是执行失败。
    SampleOutputStopped(&'static str),
    PCLimitReached(u64),
    BranchLimitReached(Name, usize),
    LoopLimitReached(Name, usize),
    DepthLimitReached,
    InconsistentRegisterReset,
    BadInterrupt(&'static str),
    IncompatibleMerge,
    IncompatibleUnionPayload,
}

impl IslaError for ExecError {
    fn source_loc(&self) -> SourceLoc {
        use ExecError::*;
        match self {
            SpeculativeReject { location: info, .. }
            | SymbolicNatural { location: info, .. }
            | Type(_, info)
            | AssertionFailure(_, info)
            | NoFunction(_, info)
            | ConcreteChoice(_, info)
            | RetryCondition(_, info)
            | IntegerConversion(_, info)
            | SymbolicLength(_, info)
            | VariableNotFound(_, info)
            | MatchFailure(info) => *info,
            Smt(error) | Unproven(error) => error.source_loc(),
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
            | SolverDroppedPath
            | SampleOutputStopped(_)
            | Stopped(_)
            | PCLimitReached(_)
            | InconsistentRegisterReset
            | BadInterrupt(_)
            | IncompatibleMerge
            | ReachableExecutionError { .. }
            | IncompatibleUnionPayload => SourceLoc::unknown(),
        }
    }
}

impl ExecError {
    pub fn query_failure(&self) -> Option<&SmtError> {
        match self {
            Self::SpeculativeReject { cause, .. } => cause.as_deref(),
            Self::Smt(cause) | Self::Unproven(cause) => Some(cause),
            _ => None,
        }
    }

    pub fn rejection_reason(&self) -> Option<crate::executor::SpeculativeRejectReason> {
        match self {
            Self::SpeculativeReject { reason, .. } => Some(*reason),
            Self::Smt(error) | Self::Unproven(error) => Some(error.reject_reason()),
            Self::Timeout => Some(crate::executor::SpeculativeRejectReason::PathTimeout),
            _ => None,
        }
    }

    /// 远端区域臂到达汇合者前，重写错误载荷中的符号。
    pub(crate) fn remap_symbols(&self, remap: &crate::smt::SymRemap) -> Self {
        match self {
            Self::IntegerConversion(exp, location) => Self::IntegerConversion(remap.exp(exp), *location),
            Self::RetryCondition(exp, location) => Self::RetryCondition(remap.exp(exp), *location),
            Self::ConcreteChoice(symbol, location) => Self::ConcreteChoice(remap.get(*symbol), *location),
            Self::SymbolicNatural { symbol, minimum, maximum, operation, location } => Self::SymbolicNatural {
                symbol: remap.get(*symbol),
                minimum: *minimum,
                maximum: *maximum,
                operation,
                location: *location,
            },
            _ => {
                let mut error = self.clone();
                let cause = match &mut error {
                    Self::SpeculativeReject { cause, .. } => cause.as_deref_mut(),
                    Self::Smt(cause) | Self::Unproven(cause) => Some(cause),
                    _ => None,
                };
                if let Some(SmtError::FiniteDomain { symbol, .. }) = cause {
                    *symbol = remap.get(*symbol);
                }
                error
            }
        }
    }

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
            SpeculativeReject { reason, function, pc, location, cause } => {
                write!(f, "拒绝推演: {}，函数 {:?}，pc {}，位置 {:?}", reason, function, pc, location)?;
                if let Some(cause) = cause {
                    write!(f, "，{cause}")?;
                }
                Ok(())
            }
            AssertionFailure(None, _) => write!(f, "Assertion failure"),
            AssertionFailure(Some(msg), _) => write!(f, "Assertion failure: {}", msg),
            ReachableExecutionError { message, location } => write!(f, "可达执行错误叶子：{message}（{location}）"),
            NoFunction(func, _) => write!(f, "Function {} does not exist", func),
            Overflow => write!(f, "Integer overflow"),
            ConcreteChoice(_, _) => write!(f, "消费者需要拆分具体候选值"),
            RetryCondition(_, _) => write!(f, "消费者需要按条件分叉重试"),
            IntegerConversion(_, _) => write!(f, "整数转换需要分叉检查范围"),
            SymbolicLength(func, _) | SymbolicNatural { operation: func, .. } => {
                write!(f, "Symbolic (bit)vector length in {}", func)
            }
            NoSymbolicType => write!(f, "No symbolic representation for type"),
            Unreachable(msg) => write!(f, "Unreachable: {}", msg),
            Unmapped => write!(f, "Unmapped memory"),
            BadRead(msg) => write!(f, "Bad read {}", msg),
            BadWrite(msg) => write!(f, "Bad write {}", msg),
            NoElfEntry => write!(f, "No entry point specified"),
            OutOfBounds(func) => write!(f, "Out of bounds error in {}", func),
            MatchFailure(_) => write!(f, "Pattern match failure"),
            Timeout => fmt::Display::fmt(&crate::executor::SpeculativeRejectReason::PathTimeout, f),
            Smt(error) => write!(f, "{}", error),
            NoModel => write!(f, "No SMT model found"),
            Z3Error(msg) => write!(f, "SMT solver error: {}", msg),
            Unproven(error) => write!(f, "{error}"),
            SolverDroppedPath => write!(f, "求解器未判定，路径已丢弃"),
            SampleOutputStopped(reason) => write!(f, "样本输出会话正常停止：{reason}"),
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
            IncompatibleUnionPayload => write!(f, "联合标签的载荷无法合并"),
        }
    }
}

impl Error for ExecError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}
