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

use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use crate::concrete_function::ConcreteFunctionConfig;
use crate::executor::frame::{Backtrace, Frame};
use crate::fraction::Fraction;
use crate::ir::{Loc, Name, Reset, SharedState};
use crate::smt::{smtlib, Checkpoint, Event};
use crate::zencode;

static TASK_COUNTER: AtomicUsize = AtomicUsize::new(0);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct TaskId {
    id: usize,
}

impl TaskId {
    pub fn from_usize(id: usize) -> Self {
        TaskId { id }
    }

    pub fn as_usize(self) -> usize {
        self.id
    }

    pub fn fresh() -> Self {
        TaskId { id: TASK_COUNTER.fetch_add(1, Ordering::SeqCst) }
    }
}

pub struct TaskInterrupt<B> {
    pub(super) id: u8,
    pub(super) trigger_register: Name,
    pub(super) trigger_value: B,
    pub(super) reset: HashMap<Loc<Name>, Reset<B>>,
}

impl<B> TaskInterrupt<B> {
    pub fn new(id: u8, trigger_register: Name, trigger_value: B, reset: HashMap<Loc<Name>, Reset<B>>) -> Self {
        TaskInterrupt { id, trigger_register, trigger_value, reset }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LimitBehavior {
    Truncate,
    Concretize,
}

#[derive(Clone, Debug)]
pub struct ExecutionLimits {
    pub max_forks_per_branch: Option<u32>,
    pub max_total_forks: Option<u32>,
    pub max_backjumps_per_loop: Option<u32>,
    pub max_path_depth: Option<u64>,
    /// 单个分支点的 fork 数占全局 fork 总数的比例上限 (0.0~1.0)。
    /// 超过此比例时触发 concretize，与 KLEE 的 MaxStaticForkPct 一致。
    pub max_fork_pct_per_branch: Option<f64>,
    /// 在全局 fork 总数未达到此值之前，跳过百分比检查（热身期）。
    /// 避免初始阶段 total_forks 过小导致任何分支点占比都接近 100% 而误杀。
    pub max_fork_pct_check_delay: Option<u32>,
    pub on_limit_reached: LimitBehavior,
}

impl Default for ExecutionLimits {
    fn default() -> Self {
        ExecutionLimits {
            max_forks_per_branch: None,
            max_total_forks: None,
            max_backjumps_per_loop: None,
            max_path_depth: None,
            max_fork_pct_per_branch: None,
            max_fork_pct_check_delay: None,
            on_limit_reached: LimitBehavior::Truncate,
        }
    }
}

impl ExecutionLimits {
    pub fn with_max_forks_per_branch(self, max_forks_per_branch: u32) -> Self {
        ExecutionLimits { max_forks_per_branch: Some(max_forks_per_branch), ..self }
    }

    pub fn with_max_total_forks(self, max_total_forks: u32) -> Self {
        ExecutionLimits { max_total_forks: Some(max_total_forks), ..self }
    }

    pub fn with_max_backjumps_per_loop(self, max_backjumps_per_loop: u32) -> Self {
        ExecutionLimits { max_backjumps_per_loop: Some(max_backjumps_per_loop), ..self }
    }

    pub fn with_max_path_depth(self, max_path_depth: u64) -> Self {
        ExecutionLimits { max_path_depth: Some(max_path_depth), ..self }
    }

    pub fn with_limit_behavior(self, on_limit_reached: LimitBehavior) -> Self {
        ExecutionLimits { on_limit_reached, ..self }
    }

    pub fn with_max_fork_pct_per_branch(self, max_fork_pct_per_branch: f64) -> Self {
        ExecutionLimits { max_fork_pct_per_branch: Some(max_fork_pct_per_branch), ..self }
    }

    pub fn with_max_fork_pct_check_delay(self, max_fork_pct_check_delay: u32) -> Self {
        ExecutionLimits { max_fork_pct_check_delay: Some(max_fork_pct_check_delay), ..self }
    }
}

#[derive(Debug)]
pub struct ExecutionLimitsState {
    branch_fork_counts: Arc<Mutex<HashMap<(Name, usize), u32>>>,
    total_forks: AtomicU32,
}

impl ExecutionLimitsState {
    pub fn new() -> Self {
        ExecutionLimitsState {
            branch_fork_counts: Arc::new(Mutex::new(HashMap::new())),
            total_forks: AtomicU32::new(0),
        }
    }

    pub fn increment_branch_fork(&self, function_name: Name, pc: usize) -> u32 {
        let mut counts = self.branch_fork_counts.lock().unwrap();
        let count = counts.entry((function_name, pc)).or_insert(0);
        *count += 1;
        self.total_forks.fetch_add(1, Ordering::Relaxed);
        *count
    }

    pub fn get_branch_fork_count(&self, function_name: Name, pc: usize) -> u32 {
        self.branch_fork_counts.lock().unwrap().get(&(function_name, pc)).copied().unwrap_or(0)
    }

    pub fn total_forks(&self) -> u32 {
        self.total_forks.load(Ordering::Relaxed)
    }
}

pub struct TaskState<B> {
    pub(super) reset_registers: HashMap<Loc<Name>, Reset<B>>,
    pub(super) pc_limit: Option<(Name, usize)>,
    pub(super) execution_limits: Option<ExecutionLimits>,
    pub(super) limits_state: Arc<ExecutionLimitsState>,
    pub(super) zero_announce_exit: bool,
    pub(super) interrupts: Vec<TaskInterrupt<B>>,
    pub concrete_function_config: Option<ConcreteFunctionConfig>,
}

impl<B> TaskState<B> {
    pub fn new() -> Self {
        TaskState {
            reset_registers: HashMap::new(),
            pc_limit: None,
            execution_limits: None,
            limits_state: Arc::new(ExecutionLimitsState::new()),
            zero_announce_exit: true,
            interrupts: Vec::new(),
            concrete_function_config: None,
        }
    }

    pub fn with_reset_registers(self, reset_registers: HashMap<Loc<Name>, Reset<B>>) -> Self {
        TaskState { reset_registers, ..self }
    }

    pub fn with_pc_limit(self, pc: Name, limit: usize) -> Self {
        TaskState { pc_limit: Some((pc, limit)), ..self }
    }

    pub fn with_execution_limits(self, limits: ExecutionLimits) -> Self {
        TaskState { execution_limits: Some(limits), ..self }
    }

    pub fn with_zero_announce_exit(self, b: bool) -> Self {
        TaskState { zero_announce_exit: b, ..self }
    }

    pub fn with_concrete_function_config(self, config: ConcreteFunctionConfig) -> Self {
        TaskState { concrete_function_config: Some(config), ..self }
    }

    pub fn add_interrupt(&mut self, interrupt: TaskInterrupt<B>) -> &mut Self {
        self.interrupts.push(interrupt);
        self
    }
}

impl<B> Default for TaskState<B> {
    fn default() -> Self {
        Self::new()
    }
}

/// A collection of simple conditions under which to stop the execution
/// of path. The conditions are formed of the name of a function to
/// stop at, with an optional second name that must appear in the
/// backtrace.
#[derive(Clone, Default)]
pub struct StopConditions {
    stops: HashMap<Name, (HashMap<Name, StopAction>, Option<StopAction>)>,
}

#[derive(Clone, Copy)]
pub enum StopAction {
    Kill,     // Remove entire trace
    Abstract, // Keep trace, put abstract call at end
}

impl StopConditions {
    pub fn new() -> Self {
        StopConditions { stops: HashMap::new() }
    }

    pub fn add(&mut self, function: Name, context: Option<Name>, action: StopAction) {
        let fn_entry = self.stops.entry(function).or_insert((HashMap::new(), None));
        if let Some(ctx) = context {
            fn_entry.0.insert(ctx, action);
        } else {
            fn_entry.1 = Some(action);
        }
    }

    pub fn union(&self, other: &StopConditions) -> Self {
        let mut dest: StopConditions = self.clone();
        for (f, (ctx, direct)) in &other.stops {
            if let Some(action) = direct {
                dest.add(*f, None, *action);
            }
            for (context, action) in ctx {
                dest.add(*f, Some(*context), *action);
            }
        }
        dest
    }

    pub fn should_stop(&self, callee: Name, caller: Name, backtrace: &Backtrace) -> Option<StopAction> {
        if let Some((ctx, direct)) = self.stops.get(&callee) {
            for (name, action) in ctx {
                if *name == caller || backtrace.iter().any(|(bt_name, _)| *name == *bt_name) {
                    return Some(*action);
                }
            }
            *direct
        } else {
            None
        }
    }

    fn parse_function_name<B>(f: &str, shared_state: &SharedState<B>) -> Name {
        let fz = zencode::encode(f);
        shared_state
            .symtab
            .get(&fz)
            .or_else(|| shared_state.symtab.get(f))
            .unwrap_or_else(|| panic!("Function {} not found", f))
    }

    pub fn parse<B>(args: Vec<String>, shared_state: &SharedState<B>, action: StopAction) -> StopConditions {
        let mut conds = StopConditions::new();
        for arg in args {
            let mut names = arg.split(',');
            if let Some(f) = names.next() {
                if let Some(ctx) = names.next() {
                    if names.next().is_none() {
                        conds.add(
                            StopConditions::parse_function_name(f, shared_state),
                            Some(StopConditions::parse_function_name(ctx, shared_state)),
                            action,
                        );
                    } else {
                        panic!("Bad stop condition: {}", arg);
                    }
                } else {
                    conds.add(StopConditions::parse_function_name(f, shared_state), None, action);
                }
            } else {
                panic!("Bad stop condition: {}", arg);
            }
        }
        conds
    }
}

/// A `Task` is a suspended point in the symbolic execution of a
/// program. It consists of a frame, which is a snapshot of the
/// program variables, a checkpoint which allows us to reconstruct the
/// SMT solver state, and finally an option SMTLIB definiton which is
/// added to the solver state when the task is resumed.
pub struct Task<'ir, 'task, B> {
    pub(crate) id: TaskId,
    pub(crate) fraction: Fraction,
    pub(crate) frame: Frame<'ir, B>,
    pub(crate) checkpoint: Checkpoint<B>,
    pub(crate) fork_cond: Option<(smtlib::Def, Event<B>)>,
    pub(crate) state: &'task TaskState<B>,
    pub(crate) stop_conditions: Option<&'task StopConditions>,
}

impl<'task, B> Task<'_, 'task, B> {
    pub fn set_stop_conditions(&mut self, new_fns: &'task StopConditions) {
        self.stop_conditions = Some(new_fns);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Name;

    #[test]
    fn test_execution_limits_default() {
        let limits = ExecutionLimits::default();
        assert!(limits.max_forks_per_branch.is_none());
        assert!(limits.max_total_forks.is_none());
        assert!(limits.max_backjumps_per_loop.is_none());
        assert!(limits.max_path_depth.is_none());
        assert!(matches!(limits.on_limit_reached, LimitBehavior::Truncate));
    }

    #[test]
    fn test_execution_limits_builder() {
        let limits = ExecutionLimits::default()
            .with_max_forks_per_branch(3)
            .with_max_backjumps_per_loop(5)
            .with_max_path_depth(100)
            .with_limit_behavior(LimitBehavior::Concretize);
        assert_eq!(limits.max_forks_per_branch, Some(3));
        assert_eq!(limits.max_backjumps_per_loop, Some(5));
        assert_eq!(limits.max_path_depth, Some(100));
        assert!(matches!(limits.on_limit_reached, LimitBehavior::Concretize));
    }

    #[test]
    fn test_limits_state_increment() {
        let state = ExecutionLimitsState::new();
        let name = Name::from_u32(42);
        let pc: usize = 10;

        assert_eq!(state.get_branch_fork_count(name, pc), 0);
        assert_eq!(state.increment_branch_fork(name, pc), 1);
        assert_eq!(state.increment_branch_fork(name, pc), 2);
        assert_eq!(state.increment_branch_fork(name, pc), 3);
        assert_eq!(state.get_branch_fork_count(name, pc), 3);
    }

    #[test]
    fn test_limits_state_different_keys() {
        let state = ExecutionLimitsState::new();
        let name1 = Name::from_u32(1);
        let name2 = Name::from_u32(2);

        state.increment_branch_fork(name1, 10);
        state.increment_branch_fork(name1, 10);
        state.increment_branch_fork(name2, 20);

        assert_eq!(state.get_branch_fork_count(name1, 10), 2);
        assert_eq!(state.get_branch_fork_count(name2, 20), 1);
        assert_eq!(state.get_branch_fork_count(name1, 20), 0);
    }

    #[test]
    fn test_limit_behavior_equality() {
        assert_eq!(LimitBehavior::Truncate, LimitBehavior::Truncate);
        assert_eq!(LimitBehavior::Concretize, LimitBehavior::Concretize);
        assert_ne!(LimitBehavior::Truncate, LimitBehavior::Concretize);
    }
}
