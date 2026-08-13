// BSD 2-Clause License
//
// Copyright (c) 2019-2024 Alasdair Armstrong
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

use ahash;

use std::collections::{HashMap, HashSet};
use std::mem;
use std::sync::Arc;

use crate::bitvector::BV;
use crate::error::{ExecError, SmtError};
use crate::executor::execution_limits::ExecutionLimitPathState;
use crate::executor::path_timing::{PathTimeTotals, PathTiming};
use crate::executor::task::{Task, TaskId, TaskState};
use crate::fraction::Fraction;
use crate::ir::*;
use crate::memory::Memory;
use crate::register::RegisterBindings;
use crate::smt::{Checkpoint, Solver, Sym};
use crate::timeout::{SmtCallStats, SmtDumpNames};
#[cfg(feature = "tracetool")]
use crate::tracetool::itrace::ItracePerPath;

#[derive(Clone)]
pub struct LocalDebugProbes {
    pub probe_this_function: bool,
}

#[derive(Clone)]
pub struct LocalState<'ir, B> {
    pub(super) vars: Bindings<'ir, B>,
    pub(super) regs: RegisterBindings<'ir, B>,
    pub(super) lets: Bindings<'ir, B>,
    pub(super) probes: LocalDebugProbes,
}

impl<'ir, B: BV> LocalState<'ir, B> {
    pub fn should_probe(&self, shared_state: &SharedState<'ir, B>, id: &Name) -> bool {
        if !self.probes.probe_this_function {
            return false;
        }

        shared_state.probes.contains(id)
    }

    pub fn collect_symbolic_variables(&self, vars: &mut HashSet<Sym, ahash::RandomState>) {
        for (_, var) in self.vars.iter().chain(self.lets.iter()) {
            if let UVal::Init(value) = var {
                value.collect_symbolic_variables(vars)
            }
        }
        for (_, reg) in self.regs.iter() {
            reg.collect_symbolic_variables(vars)
        }
    }
}

/// The callstack is implemented as a closure that restores the
/// caller's stack frame. It additionally takes the shared state as
/// input also to avoid ownership issues when creating the closure.
pub(super) type Stack<'ir, B> = Option<
    Arc<
        dyn 'ir
            + Send
            + Sync
            + Fn(Val<B>, &mut LocalFrame<'ir, B>, &SharedState<'ir, B>, &mut Solver<B>) -> Result<(), ExecError>,
    >,
>;

pub type Backtrace = Vec<(Name, usize)>;

pub fn backtrace_string<'ir>(backtrace: &[(Name, usize)], symtab: &Symtab<'ir>) -> String {
    let mut formatted = String::new();
    for (name, _) in backtrace {
        formatted.push_str(symtab.to_str(*name));
        formatted.push('\n')
    }
    formatted
}

/// A `Frame` is an immutable snapshot of the program state while it
/// is being symbolically executed.
#[derive(Clone)]
pub struct Frame<'ir, B> {
    pub(super) path_time_totals: PathTimeTotals,
    pub(super) path_smt_stats: SmtCallStats,
    pub(super) function_name: Name,
    pub(super) pc: usize,
    pub(super) execution_limit_state: Arc<ExecutionLimitPathState>,
    pub(super) local_state: Arc<LocalState<'ir, B>>,
    pub(super) memory: Arc<Memory<B>>,
    pub(super) instrs: &'ir [Instr<Name, B>],
    pub(super) stack_vars: Arc<Vec<Bindings<'ir, B>>>,
    pub(super) stack_call: Stack<'ir, B>,
    pub(super) backtrace: Arc<Backtrace>,
    pub(super) function_assumptions: Arc<HashMap<Name, Vec<(Vec<Val<B>>, Val<B>)>>>,
    pub(super) pc_counts: Arc<HashMap<B, usize>>,
    pub(super) taken_interrupts: Arc<Vec<(TaskId, u8)>>,
    /*
     * ATTENTION git-block:
     * 不要恢复旧字段 `pub(super) branch_conditions: Vec<crate::smt::smtlib::Exp<crate::smt::Sym>>,`。
     * 该字段来自 origin/dev-isarch-pathmerge；字段本身由 dea623a
     * `feat(executor): add ForkTreeNode + StateSerialize trait + IR merge annotation stub` 引入。
     * 真正需要它的是 38923e3 `feat(executor): add N-way merge_frames with write-set-aware constraint diffing`，
     * 用途是 `merge_frames` 通过 `branch_conditions[fork_depth..]` 计算执行语义级路径条件；
     * 更早的 9d561d1 也出现过 `frame.branch_conditions.push(...)` 的 exec-around 实验逻辑。
     * 分支条件是 itrace/path 级别的观测元数据，必须保存在 itrace_path 内部。
     * 这里故意保留一个被注释掉且带说明的旧字段形状，方便当前 review 识别并忽略；
     * 将来合并旧分支时，如果旧字段被带回到这个位置，应优先触发人工 review，而不是直接恢复字段。
     */
    // pub(super) branch_conditions: Vec<crate::smt::smtlib::Exp<crate::smt::Sym>>, // git-block: use itrace_path
    #[cfg(feature = "tracetool")]
    pub(super) itrace_path: Arc<ItracePerPath>,
}

pub fn unfreeze_frame<'ir, B: BV>(frame: &Frame<'ir, B>) -> LocalFrame<'ir, B> {
    LocalFrame {
        path_timing: PathTiming::from_snapshot(frame.path_time_totals),
        path_smt_stats: frame.path_smt_stats.clone(),
        function_name: frame.function_name,
        pc: frame.pc,
        execution_limit_state: (*frame.execution_limit_state).clone(),
        local_state: (*frame.local_state).clone(),
        memory: (*frame.memory).clone(),
        instrs: frame.instrs,
        stack_vars: (*frame.stack_vars).clone(),
        stack_call: frame.stack_call.clone(),
        backtrace: (*frame.backtrace).clone(),
        function_assumptions: (*frame.function_assumptions).clone(),
        pc_counts: (*frame.pc_counts).clone(),
        taken_interrupts: (*frame.taken_interrupts).clone(),
        #[cfg(feature = "tracetool")]
        itrace_path: (*frame.itrace_path).clone(),
    }
}

/// A `LocalFrame` is a mutable frame which is used by a currently
/// executing thread. It is turned into an immutable `Frame` when the
/// control flow forks on a choice, which can be shared by threads.
pub struct LocalFrame<'ir, B> {
    pub(super) path_timing: PathTiming,
    pub(super) path_smt_stats: SmtCallStats,
    pub(super) function_name: Name,
    pub(super) pc: usize,
    pub(super) execution_limit_state: ExecutionLimitPathState,
    pub(super) local_state: LocalState<'ir, B>,
    pub(super) memory: Memory<B>,
    pub(super) instrs: &'ir [Instr<Name, B>],
    pub(super) stack_vars: Vec<Bindings<'ir, B>>,
    pub(super) stack_call: Stack<'ir, B>,
    pub(super) backtrace: Backtrace,
    pub(super) function_assumptions: HashMap<Name, Vec<(Vec<Val<B>>, Val<B>)>>,
    pub(super) pc_counts: HashMap<B, usize>,
    pub(super) taken_interrupts: Vec<(TaskId, u8)>,
    /*
     * ATTENTION git-block:
     * 不要恢复旧字段 `pub(super) branch_conditions: Vec<crate::smt::smtlib::Exp<crate::smt::Sym>>,`。
     * 该字段来自 origin/dev-isarch-pathmerge；字段本身由 dea623a
     * `feat(executor): add ForkTreeNode + StateSerialize trait + IR merge annotation stub` 引入。
     * 真正需要它的是 38923e3 `feat(executor): add N-way merge_frames with write-set-aware constraint diffing`，
     * 用途是 `merge_frames` 通过 `branch_conditions[fork_depth..]` 计算执行语义级路径条件；
     * 更早的 9d561d1 也出现过 `frame.branch_conditions.push(...)` 的 exec-around 实验逻辑。
     * 分支条件属于当前 itrace path 的输出上下文，不属于 executor 的可执行状态。
     * 这里故意保留一个被注释掉且带说明的旧字段形状，方便当前 review 识别并忽略；
     * 将来合并旧分支时，如果旧字段被带回到这个位置，应优先触发人工 review，而不是直接恢复字段。
     */
    // pub(super) branch_conditions: Vec<crate::smt::smtlib::Exp<crate::smt::Sym>>, // git-block: use itrace_path
    #[cfg(feature = "tracetool")]
    pub(super) itrace_path: ItracePerPath,
}

pub fn freeze_frame<'ir, B: BV>(frame: &LocalFrame<'ir, B>) -> Frame<'ir, B> {
    Frame {
        // A frozen frame is a scheduler-safe snapshot: it stores accumulated
        // totals, never an absolute wall or thread-CPU clock. If this snapshot
        // is taken at a fork while the parent remains active, both paths inherit
        // exactly the timing prefix observed at this point and diverge afterwards.
        path_time_totals: frame.path_timing.fork_snapshot(),
        path_smt_stats: frame.path_smt_stats.clone(),
        function_name: frame.function_name,
        pc: frame.pc,
        execution_limit_state: Arc::new(frame.execution_limit_state.clone()),
        local_state: Arc::new(frame.local_state.clone()),
        memory: Arc::new(frame.memory.clone()),
        instrs: frame.instrs,
        stack_vars: Arc::new(frame.stack_vars.clone()),
        stack_call: frame.stack_call.clone(),
        backtrace: Arc::new(frame.backtrace.clone()),
        function_assumptions: Arc::new(frame.function_assumptions.clone()),
        pc_counts: Arc::new(frame.pc_counts.clone()),
        taken_interrupts: Arc::new(frame.taken_interrupts.clone()),
        #[cfg(feature = "tracetool")]
        itrace_path: Arc::new(frame.itrace_path.clone()),
    }
}

impl<'ir, B: BV> LocalFrame<'ir, B> {
    /// 在把当前路径交给调度器前，固定它已累计的 SMT 调用统计。
    pub(super) fn capture_path_smt_stats(&mut self) {
        self.path_smt_stats = crate::smt::path_smt_stats();
    }

    pub fn path_time_snapshot(&self) -> crate::timeout::PathTimeSnapshot {
        self.path_timing.snapshot()
    }

    pub fn collect_symbolic_variables(&self, vars: &mut HashSet<Sym, ahash::RandomState>) {
        self.local_state.collect_symbolic_variables(vars);

        for (_, var) in self.stack_vars.iter().flat_map(|frame| frame.iter()) {
            if let UVal::Init(value) = var {
                value.collect_symbolic_variables(vars)
            }
        }
    }

    fn add_value_dump_names(names: &mut SmtDumpNames, name: Name, value: &Val<B>) {
        let mut symbols = HashSet::default();
        value.collect_symbolic_variables(&mut symbols);
        for symbol in symbols {
            names.bind_symbol_to_ir_name(symbol.id, name.as_u32());
        }
    }

    fn add_binding_dump_names(names: &mut SmtDumpNames, bindings: &Bindings<'ir, B>) {
        for (name, value) in bindings {
            if let UVal::Init(value) = value {
                Self::add_value_dump_names(names, *name, value);
            }
        }
    }

    pub(crate) fn smt_dump_names(&self, shared_state: &SharedState<'ir, B>) -> SmtDumpNames {
        let mut names = SmtDumpNames::from_shared_state(shared_state);
        Self::add_binding_dump_names(&mut names, &self.local_state.vars);
        Self::add_binding_dump_names(&mut names, &self.local_state.lets);
        for bindings in &self.stack_vars {
            Self::add_binding_dump_names(&mut names, bindings);
        }
        for (name, register) in self.local_state.regs.iter() {
            let mut symbols = HashSet::default();
            register.collect_symbolic_variables(&mut symbols);
            for symbol in symbols {
                names.bind_symbol_to_ir_name(symbol.id, name.as_u32());
            }
        }
        names
    }

    pub fn configure_timeout_smt_dump(&self, error: &ExecError, shared_state: &SharedState<'ir, B>) {
        let dump = match error {
            ExecError::Smt(SmtError::Timeout(timeout)) => &timeout.dump,
            _ => return,
        };
        dump.configure_names(self.smt_dump_names(shared_state));
    }

    pub fn vars_mut(&mut self) -> &mut Bindings<'ir, B> {
        &mut self.local_state.vars
    }

    pub fn vars(&self) -> &Bindings<'ir, B> {
        &self.local_state.vars
    }

    pub fn backtrace(&self) -> &Backtrace {
        &self.backtrace
    }

    pub fn forks(&self) -> u32 {
        self.execution_limit_state.total_forks()
    }

    /// 这条路径的身份签名：每个 fork 点按选择的方向推进，兄弟路径必然不同，且只由本
    /// 路径自己的分叉序列决定（与线程数、调度顺序无关）。需要"不同路径给出不同具体值"
    /// 的地方（受限分支的具体化抽样、用例生成时给未约束字段取值）用它当种子。
    pub fn path_signature(&self) -> u64 {
        self.execution_limit_state.path_signature()
    }

    pub fn regs_mut(&mut self) -> &mut RegisterBindings<'ir, B> {
        &mut self.local_state.regs
    }

    pub fn regs(&self) -> &RegisterBindings<'ir, B> {
        &self.local_state.regs
    }

    pub fn add_regs(&mut self, regs: &RegisterBindings<'ir, B>) -> &mut Self {
        for (k, v) in regs {
            self.local_state.regs.insert_register(*k, v.clone())
        }
        self
    }

    pub fn lets_mut(&mut self) -> &mut Bindings<'ir, B> {
        &mut self.local_state.lets
    }

    pub fn lets(&self) -> &Bindings<'ir, B> {
        &self.local_state.lets
    }

    pub fn add_lets(&mut self, lets: &Bindings<'ir, B>) -> &mut Self {
        for (k, v) in lets {
            self.local_state.lets.insert(*k, v.clone());
        }
        self
    }

    pub fn get_exception(&self) -> Option<(&Val<B>, &str)> {
        if let Some(UVal::Init(Val::Bool(true))) = self.lets().get(&HAVE_EXCEPTION) {
            if let Some(UVal::Init(val)) = self.lets().get(&CURRENT_EXCEPTION) {
                let loc = match self.lets().get(&THROW_LOCATION) {
                    Some(UVal::Init(Val::String(s))) => s,
                    Some(UVal::Init(_)) => "location has wrong type",
                    _ => "missing location",
                };
                Some((val, loc))
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn memory(&self) -> &Memory<B> {
        &self.memory
    }

    pub fn memory_mut(&mut self) -> &mut Memory<B> {
        &mut self.memory
    }

    pub fn set_memory(&mut self, memory: Memory<B>) -> &mut Self {
        self.memory = memory;
        self
    }

    pub fn new(
        name: Name,
        args: &[(Name, &'ir Ty<Name>)],
        ret_ty: &'ir Ty<Name>,
        vals: Option<&[Val<B>]>,
        instrs: &'ir [Instr<Name, B>],
    ) -> Self {
        let mut vars = HashMap::default();
        vars.insert(RETURN, UVal::Uninit(ret_ty));
        match vals {
            Some(vals) => {
                for ((id, _), val) in args.iter().zip(vals) {
                    vars.insert(*id, UVal::Init(val.clone()));
                }
            }
            None => {
                for (id, ty) in args {
                    vars.insert(*id, UVal::Uninit(ty));
                }
            }
        }

        let mut lets = HashMap::default();
        lets.insert(HAVE_EXCEPTION, UVal::Init(Val::Bool(false)));
        lets.insert(CURRENT_EXCEPTION, UVal::Uninit(&Ty::Union(SAIL_EXCEPTION)));
        lets.insert(THROW_LOCATION, UVal::Uninit(&Ty::String));
        lets.insert(NULL, UVal::Init(Val::List(Vec::new())));

        let regs = RegisterBindings::new();

        let probe_this_function = false;
        let probes = LocalDebugProbes { probe_this_function };

        LocalFrame {
            path_timing: PathTiming::default(),
            path_smt_stats: SmtCallStats::empty(),
            function_name: name,
            pc: 0,
            execution_limit_state: ExecutionLimitPathState::default(),
            local_state: LocalState { vars, regs, lets, probes },
            memory: Memory::new(),
            instrs,
            stack_vars: Vec::new(),
            stack_call: None,
            backtrace: Vec::new(),
            function_assumptions: HashMap::new(),
            pc_counts: HashMap::new(),
            taken_interrupts: Vec::new(),
            #[cfg(feature = "tracetool")]
            itrace_path: ItracePerPath::default(),
        }
    }

    pub fn new_call(
        &self,
        name: Name,
        args: &[(Name, &'ir Ty<Name>)],
        ret_ty: &'ir Ty<Name>,
        vals: Option<&[Val<B>]>,
        instrs: &'ir [Instr<Name, B>],
    ) -> Self {
        let mut new_frame = LocalFrame::new(name, args, ret_ty, vals, instrs);
        new_frame.path_timing = self.path_timing.clone();
        new_frame.path_smt_stats = self.path_smt_stats.clone();
        new_frame.execution_limit_state = self.execution_limit_state.clone();
        new_frame.local_state.regs = self.local_state.regs.clone();
        new_frame.local_state.lets = self.local_state.lets.clone();
        new_frame.memory = self.memory.clone();
        #[cfg(feature = "tracetool")]
        {
            new_frame.itrace_path = self.itrace_path.clone();
        }
        new_frame
    }

    pub fn task_with_checkpoint<'task>(
        &self,
        task_id: TaskId,
        state: &'task TaskState<B>,
        checkpoint: Checkpoint<B>,
    ) -> Task<'ir, 'task, B> {
        Task {
            id: task_id,
            fraction: Fraction::one(),
            frame: freeze_frame(self),
            checkpoint,
            fork_cond: None,
            state,
            stop_conditions: None,
        }
    }

    pub fn task<'task>(&self, task_id: TaskId, state: &'task TaskState<B>) -> Task<'ir, 'task, B> {
        self.task_with_checkpoint(task_id, state, Checkpoint::new())
    }

    pub fn set_probes(&mut self, shared_state: &SharedState<'ir, B>) {
        let should_probe_here = if shared_state.probe_functions.is_empty() {
            true
        } else {
            self.backtrace.iter().any(|(n, _)| shared_state.probe_functions.contains(n))
        };

        self.local_state.probes.probe_this_function = should_probe_here
    }
}

impl<'ir, B: BV> Frame<'ir, B> {
    pub fn path_time_snapshot(&self) -> crate::timeout::PathTimeSnapshot {
        self.path_time_totals
    }

    pub fn backtrace(&self) -> &Backtrace {
        &self.backtrace
    }

    pub fn forks(&self) -> u32 {
        self.execution_limit_state.total_forks()
    }
}

pub(super) fn push_call_stack<B: BV>(frame: &mut LocalFrame<'_, B>) {
    let mut vars = HashMap::default();
    mem::swap(&mut vars, frame.vars_mut());
    frame.stack_vars.push(vars)
}

pub(super) fn pop_call_stack<B: BV>(frame: &mut LocalFrame<'_, B>) {
    if let Some(mut vars) = frame.stack_vars.pop() {
        mem::swap(&mut vars, frame.vars_mut())
    }
}

#[cfg(test)]
mod timing_tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::source_loc::SourceLoc;
    use crate::timeout::{SmtCallStats, SmtOperation};
    use std::time::{Duration, Instant};

    #[test]
    fn frozen_frames_store_only_settled_path_timing_totals() {
        let instrs: Vec<Instr<Name, B64>> = vec![];
        let local = LocalFrame::new(Name::from_u32(0), &[], &Ty::Unit, None, &instrs);
        let base = Instant::now();
        local.path_timing.start_active_at(base, Duration::from_millis(10));
        local.path_timing.pause_active_at(base + Duration::from_millis(25), Duration::from_millis(15));

        let frozen = freeze_frame(&local);
        assert_eq!(frozen.path_time_snapshot().active_wall, Duration::from_millis(25));
        assert_eq!(frozen.path_time_snapshot().executor_cpu, Duration::from_millis(5));

        let resumed = unfreeze_frame(&frozen);
        assert!(!resumed.path_timing.is_active());
        assert_eq!(resumed.path_time_snapshot(), frozen.path_time_snapshot());
    }

    #[test]
    fn forked_frames_restore_the_path_smt_statistics_prefix() {
        let mut prefix = SmtCallStats::empty();
        prefix.record(SmtOperation::CheckSat, SourceLoc::new(1, 10, 0, 10, 4), Duration::from_millis(12), false);
        prefix.record(SmtOperation::ModelEval, SourceLoc::new(1, 11, 0, 11, 4), Duration::from_millis(3), false);

        let instrs: Vec<Instr<Name, B64>> = vec![];
        let mut local = LocalFrame::new(Name::from_u32(0), &[], &Ty::Unit, None, &instrs);
        crate::smt::restore_path_smt_stats(prefix.clone());
        local.capture_path_smt_stats();
        let first_child = freeze_frame(&local);
        let second_child = freeze_frame(&local);

        crate::smt::reset_path_smt_stats();
        for child in [&first_child, &second_child] {
            let resumed = unfreeze_frame(child);
            crate::smt::restore_path_smt_stats(resumed.path_smt_stats);
            assert_eq!(crate::smt::path_smt_stats(), prefix);
        }
        crate::smt::reset_path_smt_stats();
    }

    #[test]
    fn dump_names_recover_ir_binding_names_from_shared_state() {
        let local_text = crate::zencode::encode("local_value");
        let function_text = crate::zencode::encode("test_function");
        let mut symtab = Symtab::new();
        let local_name = symtab.intern(&local_text);
        let function_name = symtab.intern(&function_text);
        let shared_state: SharedState<B64> = SharedState::empty(symtab);
        let instrs: Vec<Instr<Name, B64>> = vec![];
        let mut frame = LocalFrame::new(function_name, &[], &Ty::Unit, None, &instrs);

        frame.vars_mut().insert(local_name, UVal::Init(Val::Symbolic(Sym::from_u32(17))));

        let names = frame.smt_dump_names(&shared_state);
        assert_eq!(names.symbol_name(17), "isla_local_value__s17");
    }
}

#[cfg(all(test, feature = "tracetool"))]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;

    #[test]
    fn itrace_fork_paths_grow_independently() {
        let instrs: Vec<Instr<Name, B64>> = vec![];
        let instrs_ref: &[Instr<Name, B64>] = &instrs;

        let mut local = LocalFrame::new(Name::from_u32(0), &[], &Ty::Unit, None, instrs_ref);

        local.itrace_path.record(Name::from_u32(1), vec![(Name::from_u32(10), 1)], 10);
        local.itrace_path.record(Name::from_u32(2), vec![(Name::from_u32(20), 2)], 20);
        assert_eq!(local.itrace_path.records().len(), 2);

        let frozen = freeze_frame(&local);
        assert_eq!(frozen.itrace_path.records().len(), 2);

        let mut fork_a = unfreeze_frame(&frozen);
        let mut fork_b = unfreeze_frame(&frozen);

        fork_a.itrace_path.record(Name::from_u32(3), vec![(Name::from_u32(30), 3)], 30);
        fork_b.itrace_path.record(Name::from_u32(4), vec![(Name::from_u32(40), 4)], 40);
        fork_b.itrace_path.record(Name::from_u32(5), vec![(Name::from_u32(50), 5)], 50);

        assert_eq!(fork_a.itrace_path.records().len(), 3);
        assert_eq!(fork_b.itrace_path.records().len(), 4);
        assert_eq!(local.itrace_path.records().len(), 2);

        assert_eq!(fork_a.itrace_path.records()[2].function_name, Name::from_u32(3));
        assert_eq!(fork_a.itrace_path.records()[2].pc, 30);
        assert_eq!(fork_a.itrace_path.records()[2].backtrace, vec![(Name::from_u32(30), 3)]);
        assert!(fork_a.itrace_path.records()[2].summary.is_none());

        assert_eq!(fork_b.itrace_path.records()[2].function_name, Name::from_u32(4));
        assert_eq!(fork_b.itrace_path.records()[2].pc, 40);
        assert_eq!(fork_b.itrace_path.records()[2].backtrace, vec![(Name::from_u32(40), 4)]);
        assert!(fork_b.itrace_path.records()[2].summary.is_none());

        assert_eq!(fork_b.itrace_path.records()[3].function_name, Name::from_u32(5));
        assert_eq!(fork_b.itrace_path.records()[3].pc, 50);
        assert_eq!(fork_b.itrace_path.records()[3].backtrace, vec![(Name::from_u32(50), 5)]);
        assert!(fork_b.itrace_path.records()[3].summary.is_none());
    }

    #[test]
    fn freeze_unfreeze_independent_path_state() {
        itrace_fork_paths_grow_independently();
    }

    #[test]
    fn new_frame_has_default_itrace_path() {
        let instrs: Vec<Instr<Name, B64>> = vec![];
        let local = LocalFrame::new(Name::from_u32(0), &[], &Ty::Unit, None, &instrs);
        assert!(local.itrace_path.records().is_empty());
    }

    #[test]
    fn new_call_carries_itrace_path() {
        let instrs: Vec<Instr<Name, B64>> = vec![];
        let mut local = LocalFrame::new(Name::from_u32(0), &[], &Ty::Unit, None, &instrs);
        local.itrace_path.record(Name::from_u32(1), vec![], 10);

        let callee = local.new_call(Name::from_u32(99), &[], &Ty::Unit, None, &instrs);
        assert_eq!(callee.itrace_path.records().len(), 1);
        assert_eq!(callee.itrace_path.records()[0].pc, 10);
    }
}
