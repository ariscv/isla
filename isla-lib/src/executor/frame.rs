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
use crate::executor::task::{Task, TaskId, TaskState, WriteSet};
use crate::executor::SpeculationMode;
use crate::fraction::Fraction;
use crate::ir::*;
use crate::memory::Memory;
use crate::register::RegisterBindings;
use crate::smt::{Checkpoint, Solver, Sym};
use crate::timeout::{SmtCallStats, SmtDumpNames};
#[cfg(feature = "tracetool")]
use crate::tracetool::TracePerPath;

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
    // 记录输出或枚举开启时保存路径上纯计算的符号区间，随分叉、调用和保存点一起复制。
    pub(super) pure_definitions: Vec<(u32, u32)>,
    pub(super) enumerate_merges: bool,
    pub(super) speculative_access: Option<super::region_merge::AccessLog<B>>,
    // 表达式地址在 IR 生命周期内稳定；缓存只跨同一条指令的分叉重试。
    pub(super) expression_values: HashMap<usize, Val<B>>,
    pub(super) expression_retry_operands: Option<Vec<Val<B>>>,
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
        for value in self.expression_values.values() {
            value.collect_symbolic_variables(vars);
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
    // ATTENTION git-block: 不要恢复旧字段 branch_conditions。
    // 分支约束已经作为 SMT Assert 保存在 solver 的 trace/checkpoint 中；Frame 只保存执行状态。
    // 若在 Frame 中再缓存一份条件，fork、事务回滚和 checkpoint 恢复时可能出现两份约束不一致。
    pub(super) path_time_totals: PathTimeTotals,
    pub(super) path_smt_stats: SmtCallStats,
    pub(super) function_name: Name,
    pub(super) pc: usize,
    pub(super) speculation_mode: SpeculationMode,
    // 符号悲观断言拒绝后，按普通分叉重跑到原区域汇合点。
    pub(super) region_replay: Option<(usize, crate::ir::regions::RegionPoint)>,
    pub(super) region_execution: Option<super::region_merge::RegionExecution>,
    pub(super) region_merge_records: Vec<super::RegionMergeRecord<B>>,
    pub(super) pending_retry_operand: Option<(usize, Val<B>)>,
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
     * 分支条件是 itrace/path 级别的观测元数据，必须保存在 trace_path 内部。
     * 这里故意保留一个被注释掉且带说明的旧字段形状，方便当前 review 识别并忽略；
     * 将来合并旧分支时，如果旧字段被带回到这个位置，应优先触发人工 review，而不是直接恢复字段。
     */
    // pub(super) branch_conditions: Vec<crate::smt::smtlib::Exp<crate::smt::Sym>>, // git-block: use trace_path
    #[cfg(feature = "tracetool")]
    pub(super) trace_path: Arc<TracePerPath>,
}

pub fn unfreeze_frame<'ir, B: BV>(frame: &Frame<'ir, B>) -> LocalFrame<'ir, B> {
    LocalFrame {
        path_timing: PathTiming::from_snapshot(frame.path_time_totals),
        path_smt_stats: frame.path_smt_stats.clone(),
        function_name: frame.function_name,
        pc: frame.pc,
        speculation_mode: frame.speculation_mode,
        region_execution: frame.region_execution.clone(),
        region_replay: frame.region_replay,
        region_merge_records: frame.region_merge_records.clone(),
        pending_retry_operand: frame.pending_retry_operand.clone(),
        execution_limit_state: Arc::clone(&frame.execution_limit_state),
        local_state: Arc::clone(&frame.local_state),
        memory: Memory::fork_for_frame(&frame.memory),
        instrs: frame.instrs,
        stack_vars: Arc::clone(&frame.stack_vars),
        stack_call: frame.stack_call.clone(),
        backtrace: Arc::clone(&frame.backtrace),
        function_assumptions: Arc::clone(&frame.function_assumptions),
        pc_counts: Arc::clone(&frame.pc_counts),
        taken_interrupts: Arc::clone(&frame.taken_interrupts),
        #[cfg(feature = "tracetool")]
        trace_path: Arc::clone(&frame.trace_path),
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
    pub(super) speculation_mode: SpeculationMode,
    // 符号悲观断言拒绝后，按普通分叉重跑到原区域汇合点。
    pub(super) region_replay: Option<(usize, crate::ir::regions::RegionPoint)>,
    pub(super) region_execution: Option<super::region_merge::RegionExecution>,
    pub(super) region_merge_records: Vec<super::RegionMergeRecord<B>>,
    // 使用 Vector 保存同一条 primop 的全部已求值操作数，重试时不能重新生成 Undefined。
    pub(super) pending_retry_operand: Option<(usize, Val<B>)>,
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
     * 分支条件属于当前 itrace path 的输出上下文，不属于 executor 的可执行状态。
     * 这里故意保留一个被注释掉且带说明的旧字段形状，方便当前 review 识别并忽略；
     * 将来合并旧分支时，如果旧字段被带回到这个位置，应优先触发人工 review，而不是直接恢复字段。
     */
    // pub(super) branch_conditions: Vec<crate::smt::smtlib::Exp<crate::smt::Sym>>, // git-block: use trace_path
    #[cfg(feature = "tracetool")]
    pub(super) trace_path: Arc<TracePerPath>,
}

// 内存读取可能通过内部可变性更新路径状态，不能直接派生共享 Arc 的 Clone。
impl<'ir, B: Clone> Clone for LocalFrame<'ir, B> {
    fn clone(&self) -> Self {
        Self {
            path_timing: self.path_timing.clone(),
            path_smt_stats: self.path_smt_stats.clone(),
            function_name: self.function_name,
            pc: self.pc,
            speculation_mode: self.speculation_mode,
            region_replay: self.region_replay,
            region_execution: self.region_execution.clone(),
            region_merge_records: self.region_merge_records.clone(),
            pending_retry_operand: self.pending_retry_operand.clone(),
            execution_limit_state: self.execution_limit_state.clone(),
            local_state: self.local_state.clone(),
            memory: Memory::fork_for_frame(&self.memory),
            instrs: self.instrs,
            stack_vars: self.stack_vars.clone(),
            stack_call: self.stack_call.clone(),
            backtrace: self.backtrace.clone(),
            function_assumptions: self.function_assumptions.clone(),
            pc_counts: self.pc_counts.clone(),
            taken_interrupts: self.taken_interrupts.clone(),
            #[cfg(feature = "tracetool")]
            trace_path: self.trace_path.clone(),
        }
    }
}

pub fn freeze_frame<'ir, B: BV>(frame: &LocalFrame<'ir, B>) -> Frame<'ir, B> {
    Frame {
        path_time_totals: frame.path_timing.fork_snapshot(),
        path_smt_stats: frame.path_smt_stats.clone(),
        function_name: frame.function_name,
        pc: frame.pc,
        speculation_mode: frame.speculation_mode,
        region_execution: frame.region_execution.clone(),
        region_replay: frame.region_replay,
        region_merge_records: frame.region_merge_records.clone(),
        pending_retry_operand: frame.pending_retry_operand.clone(),
        execution_limit_state: Arc::clone(&frame.execution_limit_state),
        local_state: Arc::clone(&frame.local_state),
        memory: Memory::fork_for_frame(&frame.memory),
        instrs: frame.instrs,
        stack_vars: Arc::clone(&frame.stack_vars),
        stack_call: frame.stack_call.clone(),
        backtrace: Arc::clone(&frame.backtrace),
        function_assumptions: Arc::clone(&frame.function_assumptions),
        pc_counts: Arc::clone(&frame.pc_counts),
        taken_interrupts: Arc::clone(&frame.taken_interrupts),
        #[cfg(feature = "tracetool")]
        trace_path: Arc::clone(&frame.trace_path),
    }
}

impl<'ir, B: BV> LocalFrame<'ir, B> {
    pub fn region_merge_records(&self) -> &[super::RegionMergeRecord<B>] {
        &self.region_merge_records
    }

    pub fn speculation_mode(&self) -> SpeculationMode {
        self.speculation_mode
    }

    pub fn set_speculation_mode(&mut self, mode: SpeculationMode) -> &mut Self {
        self.speculation_mode = mode;
        self
    }

    /// 在把当前路径交给调度器前，固定它已累计的 SMT 调用统计。
    pub(super) fn capture_path_smt_stats(&mut self) {
        self.path_smt_stats = crate::smt::path_smt_stats();
    }

    pub fn path_time_snapshot(&self) -> crate::timeout::PathTimeSnapshot {
        self.path_timing.snapshot()
    }

    pub fn collect_symbolic_variables(&self, vars: &mut HashSet<Sym, ahash::RandomState>) {
        self.local_state.collect_symbolic_variables(vars);
        if let Some((_, operand)) = &self.pending_retry_operand {
            operand.collect_symbolic_variables(vars);
        }

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
        for bindings in self.stack_vars.iter() {
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
        &mut Arc::make_mut(&mut self.local_state).vars
    }

    pub fn vars(&self) -> &Bindings<'ir, B> {
        &self.local_state.vars
    }

    pub fn backtrace(&self) -> &Backtrace {
        &self.backtrace
    }

    pub fn function_name(&self) -> Name {
        self.function_name
    }

    pub fn pc(&self) -> usize {
        self.pc
    }

    pub fn has_sampled_branch(&self) -> bool {
        self.execution_limit_state.has_sampled_branch()
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
        &mut Arc::make_mut(&mut self.local_state).regs
    }

    pub fn regs(&self) -> &RegisterBindings<'ir, B> {
        &self.local_state.regs
    }

    pub fn add_regs(&mut self, regs: &RegisterBindings<'ir, B>) -> &mut Self {
        for (k, v) in regs {
            Arc::make_mut(&mut self.local_state).regs.insert_register(*k, v.clone())
        }
        self
    }

    pub fn lets_mut(&mut self) -> &mut Bindings<'ir, B> {
        &mut Arc::make_mut(&mut self.local_state).lets
    }

    pub fn lets(&self) -> &Bindings<'ir, B> {
        &self.local_state.lets
    }

    pub fn add_lets(&mut self, lets: &Bindings<'ir, B>) -> &mut Self {
        for (k, v) in lets {
            Arc::make_mut(&mut self.local_state).lets.insert(*k, v.clone());
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
        Arc::make_mut(&mut self.memory)
    }

    pub fn set_memory(&mut self, memory: Memory<B>) -> &mut Self {
        self.memory = Arc::new(memory);
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
            speculation_mode: SpeculationMode::Off,
            region_execution: None,
            region_replay: None,
            region_merge_records: Vec::new(),
            pending_retry_operand: None,
            execution_limit_state: Arc::new(ExecutionLimitPathState::default()),
            local_state: Arc::new(LocalState {
                vars,
                regs,
                lets,
                probes,
                speculative_access: None,
                pure_definitions: Vec::new(),
                enumerate_merges: false,
                expression_values: HashMap::new(),
                expression_retry_operands: None,
            }),
            memory: Arc::new(Memory::new()),
            instrs,
            stack_vars: Arc::new(Vec::new()),
            stack_call: None,
            backtrace: Arc::new(Vec::new()),
            function_assumptions: Arc::new(HashMap::new()),
            pc_counts: Arc::new(HashMap::new()),
            taken_interrupts: Arc::new(Vec::new()),
            #[cfg(feature = "tracetool")]
            trace_path: Arc::new(TracePerPath::default()),
        }
    }

    pub fn write_set_mut(&mut self) -> Option<&mut WriteSet> {
        Arc::make_mut(&mut self.local_state).speculative_access.as_mut().map(|access| &mut access.writes)
    }

    pub fn write_set(&self) -> Option<&WriteSet> {
        self.local_state.speculative_access.as_ref().map(|access| &access.writes)
    }

    /// ExecuteAs 等以检查点重建帧的入口必须同时携带本路径合并历史。
    pub fn merge_history(&self) -> (Vec<super::RegionMergeRecord<B>>, Vec<(u32, u32)>) {
        (self.region_merge_records.clone(), self.local_state.pure_definitions.clone())
    }

    pub fn restore_merge_history(&mut self, history: (Vec<super::RegionMergeRecord<B>>, Vec<(u32, u32)>)) {
        assert!(
            self.region_merge_records.is_empty() && self.local_state.pure_definitions.is_empty(),
            "只向新帧恢复合并历史"
        );
        (self.region_merge_records, Arc::make_mut(&mut self.local_state).pure_definitions) = history;
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
        new_frame.speculation_mode = self.speculation_mode;
        new_frame.region_execution = self.region_execution.clone();
        new_frame.region_replay = self.region_replay;
        new_frame.region_merge_records = self.region_merge_records.clone();
        Arc::make_mut(&mut new_frame.local_state).speculative_access = self.local_state.speculative_access.clone();
        Arc::make_mut(&mut new_frame.local_state).pure_definitions = self.local_state.pure_definitions.clone();
        Arc::make_mut(&mut new_frame.local_state).enumerate_merges = self.local_state.enumerate_merges;
        new_frame.path_timing = self.path_timing.clone();
        new_frame.path_smt_stats = self.path_smt_stats.clone();
        new_frame.execution_limit_state = self.execution_limit_state.clone();
        Arc::make_mut(&mut new_frame.local_state).regs = self.local_state.regs.clone();
        Arc::make_mut(&mut new_frame.local_state).lets = self.local_state.lets.clone();
        new_frame.memory = Memory::fork_for_frame(&self.memory);
        #[cfg(feature = "tracetool")]
        {
            new_frame.trace_path = self.trace_path.clone();
        }
        new_frame
    }

    pub fn task_with_checkpoint<'task>(
        &self,
        task_id: TaskId,
        state: &'task TaskState<B>,
        checkpoint: Checkpoint<B>,
    ) -> Task<'ir, 'task, B> {
        let mut frame = freeze_frame(self);
        Arc::make_mut(&mut frame.local_state).enumerate_merges =
            state.execution_limits.as_ref().is_some_and(|limits| limits.merge_enumeration.enabled);
        Task {
            id: task_id,
            fraction: Fraction::one(),
            frame,
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

        Arc::make_mut(&mut self.local_state).probes.probe_this_function = should_probe_here
    }
}

impl<'ir, B: BV> Frame<'ir, B> {
    pub fn path_time_snapshot(&self) -> crate::timeout::PathTimeSnapshot {
        self.path_time_totals
    }

    pub fn backtrace(&self) -> &Backtrace {
        &self.backtrace
    }

    pub fn has_sampled_branch(&self) -> bool {
        self.execution_limit_state.has_sampled_branch()
    }

    pub fn forks(&self) -> u32 {
        self.execution_limit_state.total_forks()
    }
}

pub(super) fn push_call_stack<B: BV>(frame: &mut LocalFrame<'_, B>) {
    let mut vars = HashMap::default();
    mem::swap(&mut vars, frame.vars_mut());
    Arc::make_mut(&mut frame.stack_vars).push(vars)
}

pub(super) fn pop_call_stack<B: BV>(frame: &mut LocalFrame<'_, B>) {
    if let Some(mut vars) = Arc::make_mut(&mut frame.stack_vars).pop() {
        mem::swap(&mut vars, frame.vars_mut())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::source_loc::SourceLoc;
    use crate::timeout::{SmtCallStats, SmtOperation};
    use std::time::{Duration, Instant};

    #[test]
    fn frozen_and_resumed_frames_share_heavy_state_until_written() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Frame<'static, B64>>();
        assert_send_sync::<LocalFrame<'static, B64>>();

        let instrs: Vec<Instr<Name, B64>> = vec![];
        let mut parent = LocalFrame::new(Name::from_u32(0), &[], &Ty::Unit, None, &instrs);
        let variable = Name::from_u32(42);
        parent.vars_mut().insert(variable, UVal::Init(Val::Bool(false)));
        let snapshot = freeze_frame(&parent);
        let mut first = unfreeze_frame(&snapshot);
        let second = unfreeze_frame(&snapshot);

        assert!(Arc::ptr_eq(&parent.execution_limit_state, &snapshot.execution_limit_state));
        assert!(Arc::ptr_eq(&parent.local_state, &snapshot.local_state));
        assert!(Arc::ptr_eq(&parent.memory, &snapshot.memory));
        assert!(Arc::ptr_eq(&parent.stack_vars, &snapshot.stack_vars));
        assert!(Arc::ptr_eq(&parent.backtrace, &snapshot.backtrace));
        assert!(Arc::ptr_eq(&parent.function_assumptions, &snapshot.function_assumptions));
        assert!(Arc::ptr_eq(&parent.pc_counts, &snapshot.pc_counts));
        assert!(Arc::ptr_eq(&parent.taken_interrupts, &snapshot.taken_interrupts));
        #[cfg(feature = "tracetool")]
        assert!(Arc::ptr_eq(&parent.trace_path, &snapshot.trace_path));

        assert!(Arc::ptr_eq(&snapshot.execution_limit_state, &first.execution_limit_state));
        assert!(std::ptr::eq(&*snapshot.local_state, &*first.local_state));
        assert!(std::ptr::eq(&*snapshot.local_state, &*second.local_state));
        assert!(std::ptr::eq(&*snapshot.memory, &*first.memory));
        assert!(std::ptr::eq(&*snapshot.stack_vars, &*first.stack_vars));
        assert!(std::ptr::eq(&*snapshot.backtrace, &*first.backtrace));
        assert!(std::ptr::eq(&*snapshot.function_assumptions, &*first.function_assumptions));
        assert!(std::ptr::eq(&*snapshot.pc_counts, &*first.pc_counts));
        assert!(std::ptr::eq(&*snapshot.taken_interrupts, &*first.taken_interrupts));
        #[cfg(feature = "tracetool")]
        assert!(Arc::ptr_eq(&snapshot.trace_path, &first.trace_path));

        first.vars_mut().insert(variable, UVal::Init(Val::Bool(true)));
        assert!(!std::ptr::eq(&*snapshot.local_state, &*first.local_state));
        assert!(matches!(parent.vars().get(&variable), Some(UVal::Init(Val::Bool(false)))));
        assert!(matches!(second.vars().get(&variable), Some(UVal::Init(Val::Bool(false)))));
        assert!(matches!(snapshot.local_state.vars.get(&variable), Some(UVal::Init(Val::Bool(false)))));

        first.memory_mut().add_symbolic_region(0..8);
        assert_eq!(first.memory().regions().len(), 1);
        assert!(parent.memory().regions().is_empty());
        assert!(second.memory().regions().is_empty());
        assert!(!Arc::ptr_eq(&snapshot.memory, &first.memory));

        push_call_stack(&mut first);
        assert_eq!(first.stack_vars.len(), 1);
        assert!(snapshot.stack_vars.is_empty());
        assert!(second.stack_vars.is_empty());
        assert!(!Arc::ptr_eq(&snapshot.stack_vars, &first.stack_vars));
    }

    #[test]
    fn unique_local_frame_writes_in_place() {
        let instrs: Vec<Instr<Name, B64>> = vec![];
        let mut local = LocalFrame::new(Name::from_u32(0), &[], &Ty::Unit, None, &instrs);
        let state_ptr = Arc::as_ptr(&local.local_state);
        let memory_ptr = Arc::as_ptr(&local.memory);

        local.vars_mut().insert(Name::from_u32(42), UVal::Init(Val::Bool(true)));
        local.memory_mut().add_symbolic_region(0..8);

        assert_eq!(state_ptr, Arc::as_ptr(&local.local_state));
        assert_eq!(memory_ptr, Arc::as_ptr(&local.memory));
    }

    #[derive(Debug, Default)]
    struct CountingReader(std::sync::atomic::AtomicU64);

    impl Clone for CountingReader {
        fn clone(&self) -> Self {
            Self(std::sync::atomic::AtomicU64::new(self.0.load(std::sync::atomic::Ordering::SeqCst)))
        }
    }

    impl crate::memory::CustomRegion<B64> for CountingReader {
        fn read(&self, _: Val<B64>, _: u64, _: u32, _: &mut Solver<B64>, _: bool) -> Result<Val<B64>, ExecError> {
            Ok(Val::Bits(B64::new(self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst), 64)))
        }
        fn write(
            &mut self,
            _: Val<B64>,
            _: u64,
            _: Val<B64>,
            _: &mut Solver<B64>,
            _: Option<Val<B64>>,
        ) -> Result<Val<B64>, ExecError> {
            panic!("本测试不写设备")
        }
        fn initial_value(&self, _: u64, _: u32) -> Option<B64> {
            None
        }
        fn region_name(&self) -> &'static str {
            "读计数设备"
        }
        fn clone_dyn(&self) -> Box<dyn Send + Sync + crate::memory::CustomRegion<B64>> {
            Box::new(self.clone())
        }
    }

    #[test]
    fn 非纯读设备触发内存克隆时仍共享具体字节直到写入() {
        use crate::memory::Region;

        let mut memory = Memory::<B64>::new();
        memory.add_concrete_region(0x1000..0x2000, HashMap::from([(0x1000, 42)]));
        memory.add_concrete_region(0x2000..0x3000, HashMap::from([(0x2000, 7)]));
        memory.add_region(Region::Custom(0x3000..0x3008, Box::new(CountingReader::default())));
        let parent = Arc::new(memory);
        let mut child = Memory::fork_for_frame(&parent);
        let sibling = Memory::fork_for_frame(&parent);

        assert!(!Arc::ptr_eq(&parent, &child));
        assert!(!Arc::ptr_eq(&parent, &sibling));
        for index in 0..2 {
            let Region::Concrete(_, parent_bytes) = &parent.regions()[index] else { panic!("预期具体区域") };
            let Region::Concrete(_, child_bytes) = &child.regions()[index] else { panic!("预期具体区域") };
            let Region::Concrete(_, sibling_bytes) = &sibling.regions()[index] else { panic!("预期具体区域") };
            assert!(Arc::ptr_eq(parent_bytes, child_bytes));
            assert!(Arc::ptr_eq(parent_bytes, sibling_bytes));
        }

        Arc::make_mut(&mut child).write_byte(0x1000, 99);
        assert_eq!(child.read_initial(0x1000, 1).unwrap(), Val::Bits(B64::new(99, 8)));
        assert_eq!(parent.read_initial(0x1000, 1).unwrap(), Val::Bits(B64::new(42, 8)));
        assert_eq!(sibling.read_initial(0x1000, 1).unwrap(), Val::Bits(B64::new(42, 8)));
        let Region::Concrete(_, parent_bytes) = &parent.regions()[0] else { panic!("预期具体区域") };
        let Region::Concrete(_, child_bytes) = &child.regions()[0] else { panic!("预期具体区域") };
        let Region::Concrete(_, sibling_bytes) = &sibling.regions()[0] else { panic!("预期具体区域") };
        assert!(!Arc::ptr_eq(parent_bytes, child_bytes));
        assert!(Arc::ptr_eq(parent_bytes, sibling_bytes));
        let Region::Concrete(_, parent_bytes) = &parent.regions()[1] else { panic!("预期具体区域") };
        let Region::Concrete(_, child_bytes) = &child.regions()[1] else { panic!("预期具体区域") };
        assert!(Arc::ptr_eq(parent_bytes, child_bytes));
    }

    impl crate::memory::MemoryCallbacks<B64> for CountingReader {
        fn handles_concrete_reads(&self) -> bool {
            true
        }
        fn symbolic_read(
            &self,
            _: &[crate::memory::Region<B64>],
            solver: &mut Solver<B64>,
            value: &Val<B64>,
            _: &Val<B64>,
            _: &Val<B64>,
            _: u32,
            _: &Option<Val<B64>>,
            _: &crate::smt::ReadOpts,
        ) -> bool {
            let Val::Symbolic(value) = value else { panic!("回调必须收到符号读值") };
            let count = self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            solver.assert_eq(crate::smt::smtlib::Exp::Var(*value), crate::smt::smtlib::bits64(count, 64));
            false
        }
        fn symbolic_write(
            &mut self,
            _: &[crate::memory::Region<B64>],
            _: &mut Solver<B64>,
            _: Sym,
            _: &Val<B64>,
            _: &Val<B64>,
            _: &Val<B64>,
            _: u32,
            _: &Option<Val<B64>>,
            _: &crate::smt::WriteOpts,
        ) -> bool {
            panic!("本测试不写数组内存")
        }
        fn symbolic_write_tag(
            &mut self,
            _: &[crate::memory::Region<B64>],
            _: &mut Solver<B64>,
            _: Sym,
            _: &Val<B64>,
            _: &Val<B64>,
            _: &Val<B64>,
        ) {
            panic!("本测试不写标签")
        }
    }

    fn assert_counting_read(frame: &LocalFrame<B64>, expected: u64) {
        use crate::smt::smtlib::{bits64, Exp};
        let ctx = crate::smt::Context::new(crate::smt::Config::new());
        let mut solver = Solver::new(&ctx);
        let value = frame
            .memory()
            .read(
                Val::Unit,
                Val::Bits(B64::new(0, 64)),
                Val::I128(8),
                &mut solver,
                false,
                crate::smt::ReadOpts::default(),
            )
            .unwrap();
        match value {
            Val::Bits(bits) => assert_eq!(bits.lower_u64(), expected),
            Val::Symbolic(value) => {
                assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
                assert!(solver
                    .check_sat_with(
                        &Exp::Neq(Box::new(Exp::Var(value)), Box::new(bits64(expected, 64))),
                        SourceLoc::unknown()
                    )
                    .is_unsat()
                    .unwrap());
            }
            _ => panic!("预期位向量读取"),
        }
    }

    #[test]
    fn impure_readers_keep_path_state_across_all_frame_copy_entries() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        for custom_region in [true, false] {
            let instrs = vec![];
            let mut parent = LocalFrame::new(Name::from_u32(0), &[], &Ty::Unit, None, &instrs);
            if custom_region {
                parent
                    .memory_mut()
                    .add_region(crate::memory::Region::Custom(0..8, Box::new(CountingReader::default())));
            } else {
                parent.memory_mut().add_symbolic_region(0..8);
                parent.memory_mut().set_client_info(Box::new(CountingReader::default()));
            }
            assert_counting_read(&parent, 0);
            let frozen = freeze_frame(&parent);
            let cloned = parent.clone();
            let called = parent.new_call(Name::from_u32(1), &[], &Ty::Unit, None, &instrs);
            assert_counting_read(&parent, 1);
            let first = unfreeze_frame(&frozen);
            let second = unfreeze_frame(&frozen);
            for child in [&first, &second, &cloned, &called] {
                assert_counting_read(child, 1);
                assert_counting_read(child, 2);
            }
            assert_counting_read(&parent, 2);
            assert_counting_read(&unfreeze_frame(&frozen.clone()), 1);
        }
    }

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
mod trace_tests {
    use super::*;
    use crate::bitvector::b64::B64;

    #[test]
    fn itrace_fork_paths_grow_independently() {
        let instrs: Vec<Instr<Name, B64>> = vec![];
        let instrs_ref: &[Instr<Name, B64>] = &instrs;

        let mut local = LocalFrame::new(Name::from_u32(0), &[], &Ty::Unit, None, instrs_ref);

        Arc::make_mut(&mut local.trace_path).record(Name::from_u32(1), vec![(Name::from_u32(10), 1)], 10);
        Arc::make_mut(&mut local.trace_path).record(Name::from_u32(2), vec![(Name::from_u32(20), 2)], 20);
        assert_eq!(local.trace_path.record_count(), 2);

        let frozen = freeze_frame(&local);
        assert_eq!(frozen.trace_path.record_count(), 2);
        assert!(
            std::ptr::eq(local.trace_path.records().next().unwrap(), frozen.trace_path.records().next().unwrap()),
            "真实 freeze 必须共享 itrace payload"
        );

        let mut fork_a = unfreeze_frame(&frozen);
        let mut fork_b = unfreeze_frame(&frozen);

        Arc::make_mut(&mut fork_a.trace_path).record(Name::from_u32(3), vec![(Name::from_u32(30), 3)], 30);
        Arc::make_mut(&mut fork_b.trace_path).record(Name::from_u32(4), vec![(Name::from_u32(40), 4)], 40);
        Arc::make_mut(&mut fork_b.trace_path).record(Name::from_u32(5), vec![(Name::from_u32(50), 5)], 50);

        assert_eq!(fork_a.trace_path.record_count(), 3);
        assert_eq!(fork_b.trace_path.record_count(), 4);
        assert_eq!(local.trace_path.record_count(), 2);

        assert_eq!(fork_a.trace_path.records().nth(2).unwrap().function_name, Name::from_u32(3));
        assert_eq!(fork_a.trace_path.records().nth(2).unwrap().pc, 30);
        assert_eq!(fork_a.trace_path.records().nth(2).unwrap().backtrace, vec![(Name::from_u32(30), 3)]);
        assert!(fork_a.trace_path.records().nth(2).unwrap().summary.is_none());

        assert_eq!(fork_b.trace_path.records().nth(2).unwrap().function_name, Name::from_u32(4));
        assert_eq!(fork_b.trace_path.records().nth(2).unwrap().pc, 40);
        assert_eq!(fork_b.trace_path.records().nth(2).unwrap().backtrace, vec![(Name::from_u32(40), 4)]);
        assert!(fork_b.trace_path.records().nth(2).unwrap().summary.is_none());

        assert_eq!(fork_b.trace_path.records().nth(3).unwrap().function_name, Name::from_u32(5));
        assert_eq!(fork_b.trace_path.records().nth(3).unwrap().pc, 50);
        assert_eq!(fork_b.trace_path.records().nth(3).unwrap().backtrace, vec![(Name::from_u32(50), 5)]);
        assert!(fork_b.trace_path.records().nth(3).unwrap().summary.is_none());
    }

    #[test]
    fn itrace_sharing_real_frame_fork_and_submission() {
        use crate::smt::smtlib;
        use crate::tracetool::TraceHandler;
        let mut symtab = Symtab::new();
        let function = symtab.intern("zsharing_frame");
        let caller = symtab.intern("zsharing_caller");
        let instrs: Vec<Instr<Name, B64>> = Vec::new();
        let mut parent = LocalFrame::new(function, &[], &Ty::Unit, None, &instrs);
        Arc::make_mut(&mut parent.trace_path).record_summary(function, vec![(caller, 8)], 0, "parent-summary");
        Arc::make_mut(&mut parent.trace_path).push_branch_condition(smtlib::Exp::Bool(true));
        Arc::make_mut(&mut parent.trace_path).record_branch_edge(function, vec![(caller, 8)], 0, 7, true);
        let identity = parent.trace_path.prefix_identity_for_test();
        assert!(identity.iter().all(|pointer| !pointer.is_null()));
        let frozen = freeze_frame(&parent);
        let mut left = unfreeze_frame(&frozen);
        let mut right = unfreeze_frame(&frozen);
        for path in [&*frozen.trace_path, &left.trace_path, &right.trace_path] {
            assert_eq!(path.prefix_identity_for_test(), identity);
        }
        Arc::make_mut(&mut left.trace_path).record_summary(function, vec![(caller, 9)], 7, "left-summary");
        Arc::make_mut(&mut left.trace_path).push_branch_condition(smtlib::Exp::Bool(false));
        Arc::make_mut(&mut left.trace_path).record_branch_edge(function, vec![(caller, 9)], 7, 8, false);
        Arc::make_mut(&mut right.trace_path).record_summary(function, vec![(caller, 10)], 7, "right-summary");
        Arc::make_mut(&mut right.trace_path).push_branch_condition(smtlib::Exp::Bool(true));
        Arc::make_mut(&mut right.trace_path).record_branch_edge(function, vec![(caller, 10)], 7, 12, true);
        let filename = std::env::temp_dir().join(format!("itrace_shared_frame_{}.txt", std::process::id()));
        let handler = TraceHandler::default();
        handler.set_path(Some(filename.clone()));
        handler.submit_path(&parent.trace_path, &symtab);
        handler.submit_path(&left.trace_path, &symtab);
        handler.submit_path(&right.trace_path, &symtab);
        handler.dump();
        let text = std::fs::read_to_string(&filename).unwrap();
        assert_eq!(text.matches("parent-summary").count(), 3);
        assert_eq!(text.matches("left-summary").count(), 1);
        assert_eq!(text.matches("right-summary").count(), 1);
        assert!(text.contains("branch_true_false):"));
        assert!(text.contains("branch_true_true):"));
        assert_eq!(text.matches("context=[zsharing_caller:8]").count(), 3);
        assert_eq!(text.matches("context=[zsharing_caller:9]").count(), 1);
        assert_eq!(text.matches("context=[zsharing_caller:10]").count(), 1);
        assert_eq!(parent.trace_path.record_count(), 1);
        assert_eq!(frozen.trace_path.record_count(), 1);
        assert_eq!(left.trace_path.record_count(), 2);
        assert_eq!(right.trace_path.record_count(), 2);
        for path in [&parent.trace_path, &*frozen.trace_path, &left.trace_path, &right.trace_path] {
            assert_eq!(path.prefix_identity_for_test(), identity, "追加及提交后共享前缀身份不变");
        }
        if let Ok(out) = std::env::var("ITRACE_SHARING_EVIDENCE") {
            std::fs::write(std::path::PathBuf::from(out).join("frame-submission.txt"), text).unwrap();
        }
        std::fs::remove_file(filename).unwrap();
    }

    #[test]
    fn freeze_unfreeze_independent_path_state() {
        itrace_fork_paths_grow_independently();
    }

    #[test]
    fn new_frame_has_default_trace_path() {
        let instrs: Vec<Instr<Name, B64>> = vec![];
        let local = LocalFrame::new(Name::from_u32(0), &[], &Ty::Unit, None, &instrs);
        assert!(local.trace_path.record_count() == 0);
    }

    #[test]
    fn new_call_carries_trace_path() {
        let instrs: Vec<Instr<Name, B64>> = vec![];
        let mut local = LocalFrame::new(Name::from_u32(0), &[], &Ty::Unit, None, &instrs);
        Arc::make_mut(&mut local.trace_path).record(Name::from_u32(1), vec![], 10);

        let callee = local.new_call(Name::from_u32(99), &[], &Ty::Unit, None, &instrs);
        assert_eq!(callee.trace_path.record_count(), 1);
        assert_eq!(callee.trace_path.records().nth(0).unwrap().pc, 10);
    }
}
