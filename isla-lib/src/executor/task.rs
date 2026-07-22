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

use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use crate::executor::frame::{Backtrace, Frame};
use crate::fraction::Fraction;
use crate::ir::{Loc, Name, Reset, SharedState};
use crate::smt::{smtlib, Checkpoint, Event};
use crate::source_loc::SourceLoc;
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

/// branch/loop 限制的局部选择器。
///
/// 同一 selector 内的字段按 AND 匹配，多个 selector 之间按 OR 匹配。SourceLoc
/// 使用精确匹配；同一 Sail 源码表达式生成的多个 IR 控制流点通常共享该 SourceLoc，
/// 因而可以作为最小粒度的源码 region。
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExecutionLimitRegion {
    function_name: Option<Name>,
    source_locations: Vec<SourceLoc>,
}

impl ExecutionLimitRegion {
    pub fn for_function(function_name: Name) -> Self {
        ExecutionLimitRegion { function_name: Some(function_name), source_locations: Vec::new() }
    }

    pub fn at_source_location(source_location: SourceLoc) -> Self {
        ExecutionLimitRegion { function_name: None, source_locations: vec![source_location] }
    }

    pub fn with_source_location(mut self, source_location: SourceLoc) -> Self {
        self.source_locations.push(source_location);
        self
    }

    fn matches(&self, function_name: Name, source_location: SourceLoc) -> bool {
        self.function_name.map_or(true, |selected| selected == function_name)
            && (self.source_locations.is_empty() || self.source_locations.contains(&source_location))
    }
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
    /// 限制只作用于匹配的源码 region；为空时作用于全部控制流点。
    pub regions: Vec<ExecutionLimitRegion>,
    /// branch/loop 计数 key 保留的最近调用点数量。
    pub call_context_depth: usize,
    /// 受限分支具体化时使用的可复现抽样 seed。
    pub branch_sampling_seed: u64,
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
            regions: Vec::new(),
            call_context_depth: 2,
            branch_sampling_seed: 0x4953_4c41_5f4c_494d,
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

    pub fn with_limit_region(mut self, region: ExecutionLimitRegion) -> Self {
        self.regions.push(region);
        self
    }

    pub fn with_call_context_depth(self, call_context_depth: usize) -> Self {
        ExecutionLimits { call_context_depth, ..self }
    }

    pub fn with_branch_sampling_seed(self, branch_sampling_seed: u64) -> Self {
        ExecutionLimits { branch_sampling_seed, ..self }
    }

    pub(super) fn applies_to(&self, scope: &ControlFlowScope) -> bool {
        self.regions.is_empty()
            || self.regions.iter().any(|region| region.matches(scope.function_name, scope.source_location))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct ControlFlowScope {
    function_name: Name,
    pc: usize,
    call_context: Vec<(Name, usize)>,
    source_location: SourceLoc,
}

impl ControlFlowScope {
    pub(super) fn new(
        function_name: Name,
        pc: usize,
        backtrace: &[(Name, usize)],
        source_location: SourceLoc,
        call_context_depth: usize,
    ) -> Self {
        let first = backtrace.len().saturating_sub(call_context_depth);
        ControlFlowScope { function_name, pc, call_context: backtrace[first..].to_vec(), source_location }
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct ExecutionLimitCounts {
    pub attempted: u32,
    pub actual: u32,
    pub sampled: u32,
    pub concretized: u32,
    pub concretized_true: u32,
    pub concretized_false: u32,
}

#[derive(Debug, Default)]
struct ExecutionLimitCounters {
    branches: HashMap<ControlFlowScope, ExecutionLimitCounts>,
    total: ExecutionLimitCounts,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub(super) enum BranchLimitReason {
    MaxTotalForks { actual: u32, max: u32 },
    MaxForksPerBranch { actual: u32, max: u32 },
    MaxForkPctPerBranch { branch_actual: u32, total_actual: u32, max_pct: f64, check_delay: u32 },
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub(super) struct BranchAttempt {
    pub sample_ordinal: Option<u32>,
    pub limit: Option<BranchLimitReason>,
}

#[derive(Debug, Default)]
pub struct ExecutionLimitsState {
    counters: Mutex<ExecutionLimitCounters>,
}

impl ExecutionLimitsState {
    pub fn new() -> Self {
        ExecutionLimitsState { counters: Mutex::new(ExecutionLimitCounters::default()) }
    }

    /// 兼容原有内部测试/API：此处的 fork 指实际创建的 child。
    pub fn increment_branch_fork(&self, function_name: Name, pc: usize) -> u32 {
        let scope = ControlFlowScope::new(function_name, pc, &[], SourceLoc::unknown(), 0);
        self.begin_branch_attempt(scope.clone(), &ExecutionLimits::default());
        self.branch_counts(&scope).actual
    }

    pub fn get_branch_fork_count(&self, function_name: Name, pc: usize) -> u32 {
        let scope = ControlFlowScope::new(function_name, pc, &[], SourceLoc::unknown(), 0);
        self.branch_counts(&scope).actual
    }

    pub fn total_forks(&self) -> u32 {
        self.counts().actual
    }

    pub fn counts(&self) -> ExecutionLimitCounts {
        self.counters.lock().unwrap().total
    }

    pub(super) fn begin_branch_attempt(&self, scope: ControlFlowScope, limits: &ExecutionLimits) -> BranchAttempt {
        let mut counters = self.counters.lock().unwrap();
        counters.total.attempted += 1;
        let total_actual = counters.total.actual;
        let branch_actual = {
            let branch = counters.branches.entry(scope.clone()).or_default();
            branch.attempted += 1;
            branch.actual
        };

        let limit = if let Some(max) = limits.max_total_forks {
            if total_actual >= max {
                Some(BranchLimitReason::MaxTotalForks { actual: total_actual, max })
            } else {
                None
            }
        } else {
            None
        }
        .or_else(|| {
            limits.max_forks_per_branch.and_then(|max| {
                (branch_actual >= max).then_some(BranchLimitReason::MaxForksPerBranch { actual: branch_actual, max })
            })
        })
        .or_else(|| {
            limits.max_fork_pct_per_branch.and_then(|max_pct| {
                let check_delay = limits.max_fork_pct_check_delay.unwrap_or(0);
                (total_actual > check_delay && (branch_actual as f64) > (total_actual as f64) * max_pct).then_some(
                    BranchLimitReason::MaxForkPctPerBranch { branch_actual, total_actual, max_pct, check_delay },
                )
            })
        });

        let sample_ordinal = if limit.is_some() && limits.on_limit_reached == LimitBehavior::Concretize {
            counters.total.sampled += 1;
            let branch = counters.branches.entry(scope.clone()).or_default();
            let ordinal = branch.sampled;
            branch.sampled += 1;
            Some(ordinal)
        } else {
            None
        };

        if limit.is_none() {
            counters.total.actual += 1;
            counters.branches.entry(scope).or_default().actual += 1;
        }

        BranchAttempt { sample_ordinal, limit }
    }

    pub(super) fn begin_concretization_attempt(&self, scope: ControlFlowScope) -> u32 {
        let mut counters = self.counters.lock().unwrap();
        counters.total.attempted += 1;
        counters.total.sampled += 1;
        let branch = counters.branches.entry(scope).or_default();
        branch.attempted += 1;
        let sample_ordinal = branch.sampled;
        branch.sampled += 1;
        sample_ordinal
    }

    pub(super) fn record_concretized(&self, scope: &ControlFlowScope, concrete_value: bool) {
        let mut counters = self.counters.lock().unwrap();
        counters.total.concretized += 1;
        if concrete_value {
            counters.total.concretized_true += 1;
        } else {
            counters.total.concretized_false += 1;
        }
        let branch = counters.branches.entry(scope.clone()).or_default();
        branch.concretized += 1;
        if concrete_value {
            branch.concretized_true += 1;
        } else {
            branch.concretized_false += 1;
        }
    }

    pub(super) fn preferred_branch(&self, scope: &ControlFlowScope, sample_ordinal: u32, seed: u64) -> bool {
        let pair_ordinal = sample_ordinal / 2;
        let mut hasher = DefaultHasher::new();
        seed.hash(&mut hasher);
        scope.hash(&mut hasher);
        pair_ordinal.hash(&mut hasher);
        let first = splitmix64(hasher.finish()) & 1 == 1;
        if sample_ordinal % 2 == 0 {
            first
        } else {
            !first
        }
    }

    fn branch_counts(&self, scope: &ControlFlowScope) -> ExecutionLimitCounts {
        self.counters.lock().unwrap().branches.get(scope).copied().unwrap_or_default()
    }
}

fn splitmix64(mut value: u64) -> u64 {
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

pub struct TaskState<B> {
    pub(super) reset_registers: HashMap<Loc<Name>, Reset<B>>,
    // We might want to avoid loops in the assembly by requiring that
    // any unique program counter (pc) is only visited a fixed number
    // of times. Note that this is the architectural PC, not the isla
    // IR program counter in the frame.
    pub(super) pc_limit: Option<(Name, usize)>,
    pub(super) execution_limits: Option<ExecutionLimits>,
    pub(super) limits_state: Arc<ExecutionLimitsState>,
    // Exit if we ever announce an instruction with all bits set to zero
    pub(super) zero_announce_exit: bool,
    pub(super) interrupts: Vec<TaskInterrupt<B>>,
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

    pub fn execution_limit_counts(&self) -> ExecutionLimitCounts {
        self.limits_state.counts()
    }

    pub fn with_zero_announce_exit(self, b: bool) -> Self {
        TaskState { zero_announce_exit: b, ..self }
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
    use crate::source_loc::SourceLoc;

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

    #[test]
    fn test_limit_region_matches_function_and_source_location() {
        let function = Name::from_u32(7);
        let other_function = Name::from_u32(8);
        let selected = SourceLoc::new(1, 10, 0, 10, 4);
        let other = SourceLoc::new(1, 11, 0, 11, 4);
        let region = ExecutionLimitRegion::for_function(function).with_source_location(selected);

        assert!(region.matches(function, selected));
        assert!(!region.matches(function, other));
        assert!(!region.matches(other_function, selected));
    }

    #[test]
    fn test_control_flow_scope_separates_function_and_call_context() {
        let info = SourceLoc::new(1, 10, 0, 10, 4);
        let caller_a = Name::from_u32(1);
        let caller_b = Name::from_u32(2);
        let function = Name::from_u32(3);
        let other_function = Name::from_u32(4);
        let context_a = vec![(caller_a, 10), (caller_b, 20)];
        let context_b = vec![(caller_a, 11), (caller_b, 20)];

        let a = ControlFlowScope::new(function, 30, &context_a, info, 2);
        let b = ControlFlowScope::new(function, 30, &context_b, info, 2);
        let other = ControlFlowScope::new(other_function, 30, &context_a, info, 2);
        let last_frame_only = ControlFlowScope::new(function, 30, &context_a, info, 1);
        let same_last_frame = ControlFlowScope::new(function, 30, &context_b, info, 1);

        assert_ne!(a, b);
        assert_ne!(a, other);
        assert_eq!(last_frame_only, same_last_frame);
    }

    #[test]
    fn test_limits_state_separates_attempted_actual_and_concretized() {
        let state = ExecutionLimitsState::new();
        let scope = ControlFlowScope::new(
            Name::from_u32(3),
            30,
            &[(Name::from_u32(1), 10)],
            SourceLoc::new(1, 10, 0, 10, 4),
            2,
        );
        let limits = ExecutionLimits::default().with_max_total_forks(0).with_limit_behavior(LimitBehavior::Concretize);

        let attempt = state.begin_branch_attempt(scope.clone(), &limits);
        assert!(attempt.limit.is_some());
        assert_eq!(state.counts().attempted, 1);
        assert_eq!(state.counts().actual, 0);
        assert_eq!(state.counts().sampled, 1);
        assert_eq!(state.counts().concretized, 0);

        state.record_concretized(&scope, true);
        assert_eq!(state.counts().attempted, 1);
        assert_eq!(state.counts().actual, 0);
        assert_eq!(state.counts().concretized, 1);
        assert_eq!(state.counts().concretized_true, 1);
        assert_eq!(state.counts().concretized_false, 0);

        let allowed = ControlFlowScope::new(Name::from_u32(3), 31, &[], SourceLoc::unknown(), 2);
        let attempt = state.begin_branch_attempt(allowed, &ExecutionLimits::default());
        assert!(attempt.limit.is_none());
        assert_eq!(state.counts().attempted, 2);
        assert_eq!(state.counts().actual, 1);
        assert_eq!(state.counts().concretized, 1);
    }

    #[test]
    fn test_sampling_sequence_is_seeded_reproducible_and_pair_balanced() {
        let state = ExecutionLimitsState::new();
        let scope = ControlFlowScope::new(
            Name::from_u32(3),
            30,
            &[(Name::from_u32(1), 10)],
            SourceLoc::new(1, 10, 0, 10, 4),
            2,
        );
        let sequence = |seed| {
            (0..32).map(|sample_ordinal| state.preferred_branch(&scope, sample_ordinal, seed)).collect::<Vec<_>>()
        };

        let first = sequence(0x1234_5678);
        let replay = sequence(0x1234_5678);
        let different_seed = sequence(0x8765_4321);

        assert_eq!(first, replay);
        assert_ne!(first, different_seed);
        for pair in first.chunks_exact(2) {
            assert_ne!(pair[0], pair[1]);
        }
        assert_eq!(first.iter().filter(|choice| **choice).count(), 16);
    }

    #[test]
    fn test_percentage_limit_uses_actual_forks_not_attempts() {
        let state = ExecutionLimitsState::new();
        let hot = ControlFlowScope::new(Name::from_u32(3), 30, &[], SourceLoc::new(1, 10, 0, 10, 4), 2);
        let cold = ControlFlowScope::new(Name::from_u32(3), 31, &[], SourceLoc::new(1, 11, 0, 11, 4), 2);
        let concretize =
            ExecutionLimits::default().with_max_total_forks(0).with_limit_behavior(LimitBehavior::Concretize);
        let unlimited = ExecutionLimits::default();

        for _ in 0..100 {
            let attempt = state.begin_branch_attempt(hot.clone(), &concretize);
            assert!(attempt.limit.is_some());
            state.record_concretized(&hot, true);
        }
        for _ in 0..9 {
            let attempt = state.begin_branch_attempt(cold.clone(), &unlimited);
            assert!(attempt.limit.is_none());
        }
        let attempt = state.begin_branch_attempt(hot.clone(), &unlimited);
        assert!(attempt.limit.is_none());

        let percentage = ExecutionLimits::default().with_max_fork_pct_per_branch(0.2).with_max_fork_pct_check_delay(0);
        let next = state.begin_branch_attempt(hot, &percentage);

        assert!(next.limit.is_none(), "hot 分支的 actual 占比只有 10%，attempted 不应触发百分比限制");
    }
}
