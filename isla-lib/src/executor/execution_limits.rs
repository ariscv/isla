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
// 1. Redistributions of source code must retain the above copyright notice,
//    this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright notice,
//    this list of conditions and the following disclaimer in the documentation
//    and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
// CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.

use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use crate::config::{ExecutionLimitsConfig, LimitBehaviorConfig};
use crate::ir::{Name, Symtab};
use crate::source_loc::{SourceLoc, SourceRegion, SourceRegionSpec};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LimitBehavior {
    Truncate,
    Concretize,
}

#[derive(Clone, Debug)]
pub struct ExecutionLimits {
    pub max_forks_per_branch: Option<u32>,
    /// 一条路径从根节点到当前位置累计经历的 executor fork 数上限。
    pub max_forks_per_path: Option<u32>,
    pub max_backjumps_per_loop: Option<u32>,
    pub max_path_depth: Option<u64>,
    /// 当前路径内，单个分支点的 fork 数占该路径全部 fork 数的比例上限。
    /// 判定使用本次 fork 发生前的路径状态。
    pub max_fork_pct_per_branch: Option<f64>,
    /// 当前路径累计 fork 数未超过此值时跳过百分比检查。
    pub max_fork_pct_check_delay: Option<u32>,
    /// branch-local 和 loop 限制只作用于匹配的源码 region。
    /// `None` 表示不设置 region 过滤，`Some(empty)` 表示显式匹配不到任何源码位置。
    /// path fork/depth 限制不受 region 过滤。
    pub regions: Option<Vec<SourceRegion>>,
    /// branch/loop 计数 key 保留的最近调用点数量；`None` 时不复制或哈希调用上下文。
    pub call_context_depth: Option<usize>,
    /// 受限分支具体化时使用的可复现抽样 seed。
    pub branch_sampling_seed: u64,
    pub on_limit_reached: LimitBehavior,
}

impl Default for ExecutionLimits {
    fn default() -> Self {
        ExecutionLimits {
            max_forks_per_branch: None,
            max_forks_per_path: None,
            max_backjumps_per_loop: None,
            max_path_depth: None,
            max_fork_pct_per_branch: None,
            max_fork_pct_check_delay: None,
            regions: None,
            call_context_depth: None,
            branch_sampling_seed: 0x4953_4c41_5f4c_494d,
            on_limit_reached: LimitBehavior::Truncate,
        }
    }
}

impl ExecutionLimits {
    pub fn with_max_forks_per_branch(self, max_forks_per_branch: u32) -> Self {
        ExecutionLimits { max_forks_per_branch: Some(max_forks_per_branch), ..self }
    }

    pub fn with_max_forks_per_path(self, max_forks_per_path: u32) -> Self {
        ExecutionLimits { max_forks_per_path: Some(max_forks_per_path), ..self }
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
        assert!(
            max_fork_pct_per_branch.is_finite() && (0.0..=1.0).contains(&max_fork_pct_per_branch),
            "max_fork_pct_per_branch must be a finite value in 0.0..=1.0"
        );
        ExecutionLimits { max_fork_pct_per_branch: Some(max_fork_pct_per_branch), ..self }
    }

    pub fn with_max_fork_pct_check_delay(self, max_fork_pct_check_delay: u32) -> Self {
        ExecutionLimits { max_fork_pct_check_delay: Some(max_fork_pct_check_delay), ..self }
    }

    pub fn with_limit_region(mut self, region: SourceRegion) -> Self {
        self.regions.get_or_insert_with(Vec::new).push(region);
        self
    }

    pub fn with_limit_regions(mut self, regions: Vec<SourceRegion>) -> Self {
        self.regions = Some(regions);
        self
    }

    /// 在符号执行开始前，将文件名形式的 region 配置解析成运行时文件编号。
    pub fn with_region_specs(self, region_specs: &[SourceRegionSpec], symtab: &Symtab) -> Self {
        self.with_limit_regions(region_specs.iter().filter_map(|region| region.resolve(symtab.files())).collect())
    }

    /// 将配置 DTO 覆盖到运行时策略，并在这里一次性解析配置中的源码 region。
    pub fn with_config(mut self, config: &ExecutionLimitsConfig, symtab: &Symtab) -> Self {
        if config.enabled == Some(false) {
            return ExecutionLimits::default();
        }

        if let Some(value) = config.max_forks_per_branch {
            self = self.with_max_forks_per_branch(value);
        }
        if let Some(value) = config.max_forks_per_path {
            self = self.with_max_forks_per_path(value);
        }
        if let Some(value) = config.max_backjumps_per_loop {
            self = self.with_max_backjumps_per_loop(value);
        }
        if let Some(value) = config.max_path_depth {
            self = self.with_max_path_depth(value);
        }
        if let Some(value) = config.max_fork_pct_per_branch {
            self = self.with_max_fork_pct_per_branch(value);
        }
        if let Some(value) = config.max_fork_pct_check_delay {
            self = self.with_max_fork_pct_check_delay(value);
        }
        if let Some(value) = config.call_context_depth {
            self = self.with_call_context_depth(value);
        }
        if let Some(value) = config.branch_sampling_seed {
            self = self.with_branch_sampling_seed(value);
        }
        if let Some(value) = config.on_limit_reached {
            self = self.with_limit_behavior(match value {
                LimitBehaviorConfig::Truncate => LimitBehavior::Truncate,
                LimitBehaviorConfig::Concretize => LimitBehavior::Concretize,
            });
        }
        if let Some(region_specs) = &config.regions {
            self = self.with_region_specs(region_specs, symtab);
        }

        self
    }

    pub fn with_call_context_depth(self, call_context_depth: impl Into<Option<usize>>) -> Self {
        ExecutionLimits { call_context_depth: call_context_depth.into(), ..self }
    }

    pub fn with_branch_sampling_seed(self, branch_sampling_seed: u64) -> Self {
        ExecutionLimits { branch_sampling_seed, ..self }
    }

    fn applies_to(&self, scope: &ControlFlowScope) -> bool {
        self.regions
            .as_ref()
            .map_or(true, |regions| regions.iter().any(|region| region.selects_ir_location(scope.source_location)))
    }

    fn tracks_branch_forks(&self) -> bool {
        self.max_forks_per_branch.is_some() || self.max_fork_pct_per_branch.is_some()
    }

    pub(super) fn is_active(&self) -> bool {
        self.max_forks_per_branch.is_some()
            || self.max_forks_per_path.is_some()
            || self.max_backjumps_per_loop.is_some()
            || self.max_path_depth.is_some()
            || self.max_fork_pct_per_branch.is_some()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ControlFlowScope {
    function_name: Name,
    pc: usize,
    call_context: Option<Vec<(Name, usize)>>,
    source_location: SourceLoc,
}

impl ControlFlowScope {
    fn new(
        function_name: Name,
        pc: usize,
        backtrace: &[(Name, usize)],
        source_location: SourceLoc,
        call_context_depth: Option<usize>,
    ) -> Self {
        let call_context = call_context_depth.map(|depth| {
            let first = backtrace.len().saturating_sub(depth);
            backtrace[first..].to_vec()
        });
        ControlFlowScope { function_name, pc, call_context, source_location }
    }
}

/// 每条执行路径的私有限制状态，存储在 `Frame` 中。
///
/// 跟踪控制流步数、累计 fork 数、每个循环 scope 的回跳次数、每个分支 scope 的
/// fork 次数，以及采样序号（用于确定性偏好计算）。每次 fork 时路径状态被 clone，
/// 因此各路径独立演化。
#[derive(Clone, Debug, Default)]
pub(super) struct ExecutionLimitPathState {
    control_flow_steps: u32,
    total_forks: u32,
    loop_counts: HashMap<ControlFlowScope, u32>,
    branch_forks: HashMap<ControlFlowScope, u32>,
    sample_ordinals: HashMap<ControlFlowScope, u32>,
}

impl ExecutionLimitPathState {
    pub(super) fn total_forks(&self) -> u32 {
        self.total_forks
    }

    /// 这条路径迄今执行过的控制流步数（jump/goto/call）。
    pub(super) fn control_flow_steps(&self) -> u32 {
        self.control_flow_steps
    }

    pub(super) fn advance_control_flow(&mut self) -> u32 {
        self.control_flow_steps = self.control_flow_steps.checked_add(1).expect("control-flow step count overflow");
        self.control_flow_steps
    }

    pub(super) fn record_fork(&mut self) -> u32 {
        let fork_id = self.total_forks;
        self.total_forks = self.total_forks.checked_add(1).expect("path fork count overflow");
        fork_id
    }

    fn branch_forks(&self, scope: &ControlFlowScope) -> u32 {
        self.branch_forks.get(scope).copied().unwrap_or(0)
    }

    fn sample_ordinal(&self, scope: &ControlFlowScope) -> u32 {
        self.sample_ordinals.get(scope).copied().unwrap_or(0)
    }

    fn commit_sample(&mut self, sample: &BranchSample) {
        let ordinal = self.sample_ordinals.entry(sample.scope.clone()).or_insert(0);
        assert_eq!(*ordinal, sample.ordinal, "branch sample ordinal changed before commit");
        *ordinal = ordinal.checked_add(1).expect("branch sample ordinal overflow");
    }
}

/// 执行限制触发的具体原因，携带当前值与阈值，用于构造 `ExecError` 和 itrace 记录。
#[derive(Copy, Clone, Debug, PartialEq)]
pub(super) enum ExecutionLimitReason {
    MaxForksPerPath { actual: u32, max: u32 },
    MaxForksPerBranch { actual: u32, max: u32 },
    MaxForkPctPerBranch { branch_actual: u32, path_actual: u32, max_pct: f64, check_delay: u32 },
    MaxBackjumpsPerLoop { target: usize, actual: u32, max: u32 },
    MaxPathDepth { actual: u64, max: u64 },
}

/// 一次具体化采样的偏好信息。
///
/// `scope` 标识逻辑分支点（函数 + IR PC + 调用上下文 + 源码位置），`ordinal` 是该
/// scope 的单调采样序号，`preferred` 由采样种子和序号确定性计算得出，使相邻两次
/// 采样偏好相反方向，避免长期偏向同一侧。
#[derive(Clone, Debug, PartialEq)]
pub(super) struct BranchSample {
    scope: ControlFlowScope,
    ordinal: u32,
    preferred: bool,
}

impl BranchSample {
    pub(super) fn preferred(&self) -> bool {
        self.preferred
    }
}

/// 执行限制判定结果。调用者根据此决策决定控制流走向：
/// - `Continue`：未触发任何限制，正常执行。
/// - `Fork`：允许创建新的执行路径，返回分配的 fork ID。
/// - `Truncate`：限制触发且行为为截断，应立即终止当前路径。
/// - `ConcretizeBranch`：限制触发且行为为具体化，应将符号分支固定到采样方向。
/// - `KeepCurrentModel`：monomorphize 时限制触发且行为为具体化，保留当前模型值。
#[derive(Clone, Debug, PartialEq)]
pub(super) enum ExecutionLimitDecision {
    Continue,
    Fork { fork_id: u32 },
    Truncate(ExecutionLimitReason),
    ConcretizeBranch { reason: ExecutionLimitReason, sample: BranchSample },
    KeepCurrentModel { reason: ExecutionLimitReason },
}

/// 无状态的执行限制处理器。配置由 `TaskState` 持有，所有路径私有状态通过
/// `ExecutionLimitPathState` 参数传入。
#[derive(Copy, Clone, Debug)]
pub(super) struct ExecutionLimitHandler<'config> {
    config: &'config ExecutionLimits,
}

impl<'config> ExecutionLimitHandler<'config> {
    pub(super) fn new(config: &'config ExecutionLimits) -> Self {
        ExecutionLimitHandler { config }
    }

    pub(super) fn on_conditional_jump(
        &self,
        path: &mut ExecutionLimitPathState,
        function_name: Name,
        pc: usize,
        target: usize,
        backtrace: &[(Name, usize)],
        source_location: SourceLoc,
    ) -> ExecutionLimitDecision {
        if let Some(reason) = self.advance_control_flow(path) {
            return self.conditional_limit(path, function_name, pc, backtrace, source_location, reason);
        }

        if let Some(max) = self.config.max_backjumps_per_loop {
            if target <= pc {
                let loop_scope = self.loop_scope(function_name, target, backtrace, source_location);
                if self.config.applies_to(&loop_scope) {
                    let actual = {
                        let count = path.loop_counts.entry(loop_scope).or_insert(0);
                        *count = count.checked_add(1).expect("loop backjump count overflow");
                        *count
                    };
                    if actual > max {
                        return self.conditional_limit(
                            path,
                            function_name,
                            pc,
                            backtrace,
                            source_location,
                            ExecutionLimitReason::MaxBackjumpsPerLoop { target, actual, max },
                        );
                    }
                }
            }
        }

        ExecutionLimitDecision::Continue
    }

    pub(super) fn on_goto(
        &self,
        path: &mut ExecutionLimitPathState,
        function_name: Name,
        pc: usize,
        target: usize,
        backtrace: &[(Name, usize)],
    ) -> ExecutionLimitDecision {
        if let Some(reason) = self.advance_control_flow(path) {
            return ExecutionLimitDecision::Truncate(reason);
        }

        if let Some(max) = self.config.max_backjumps_per_loop {
            if target <= pc {
                // Goto 没有 SourceLoc；配置源码 region 时不会命中，region 为空时仍按全局限制处理。
                let loop_scope = self.loop_scope(function_name, target, backtrace, SourceLoc::unknown());
                if self.config.applies_to(&loop_scope) {
                    let actual = {
                        let count = path.loop_counts.entry(loop_scope).or_insert(0);
                        *count = count.checked_add(1).expect("loop backjump count overflow");
                        *count
                    };
                    if actual > max {
                        return ExecutionLimitDecision::Truncate(ExecutionLimitReason::MaxBackjumpsPerLoop {
                            target,
                            actual,
                            max,
                        });
                    }
                }
            }
        }

        ExecutionLimitDecision::Continue
    }

    pub(super) fn on_call(&self, path: &mut ExecutionLimitPathState) -> ExecutionLimitDecision {
        if let Some(reason) = self.advance_control_flow(path) {
            ExecutionLimitDecision::Truncate(reason)
        } else {
            ExecutionLimitDecision::Continue
        }
    }

    pub(super) fn on_branch_fork(
        &self,
        path: &mut ExecutionLimitPathState,
        function_name: Name,
        pc: usize,
        backtrace: &[(Name, usize)],
        source_location: SourceLoc,
    ) -> ExecutionLimitDecision {
        if let Some(reason) = self.path_fork_limit(path) {
            let scope = self.branch_scope(function_name, pc, backtrace, source_location);
            return self.branch_limit(path, scope, reason);
        }

        let branch_scope = if self.config.tracks_branch_forks() {
            let scope = self.branch_scope(function_name, pc, backtrace, source_location);
            if self.config.applies_to(&scope) {
                let branch_actual = path.branch_forks(&scope);
                if let Some(max) = self.config.max_forks_per_branch {
                    if branch_actual >= max {
                        return self.branch_limit(
                            path,
                            scope,
                            ExecutionLimitReason::MaxForksPerBranch { actual: branch_actual, max },
                        );
                    }
                }
                if let Some(max_pct) = self.config.max_fork_pct_per_branch {
                    let path_actual = path.total_forks;
                    let check_delay = self.config.max_fork_pct_check_delay.unwrap_or(0);
                    if path_actual > check_delay && (branch_actual as f64) > (path_actual as f64) * max_pct {
                        return self.branch_limit(
                            path,
                            scope,
                            ExecutionLimitReason::MaxForkPctPerBranch {
                                branch_actual,
                                path_actual,
                                max_pct,
                                check_delay,
                            },
                        );
                    }
                }
                Some(scope)
            } else {
                None
            }
        } else {
            None
        };

        let fork_id = Self::record_path_fork(path);
        if let Some(scope) = branch_scope {
            let count = path.branch_forks.entry(scope).or_insert(0);
            *count = count.checked_add(1).expect("branch fork count overflow");
        }
        ExecutionLimitDecision::Fork { fork_id }
    }

    pub(super) fn on_monomorphize_fork(&self, path: &mut ExecutionLimitPathState) -> ExecutionLimitDecision {
        if let Some(reason) = self.path_fork_limit(path) {
            return match self.config.on_limit_reached {
                LimitBehavior::Truncate => ExecutionLimitDecision::Truncate(reason),
                LimitBehavior::Concretize => ExecutionLimitDecision::KeepCurrentModel { reason },
            };
        }

        ExecutionLimitDecision::Fork { fork_id: Self::record_path_fork(path) }
    }

    pub(super) fn commit_sample(&self, path: &mut ExecutionLimitPathState, sample: &BranchSample) {
        path.commit_sample(sample)
    }

    fn advance_control_flow(&self, path: &mut ExecutionLimitPathState) -> Option<ExecutionLimitReason> {
        let actual = path.advance_control_flow() as u64;
        self.config
            .max_path_depth
            .and_then(|max| (actual > max).then_some(ExecutionLimitReason::MaxPathDepth { actual, max }))
    }

    fn record_path_fork(path: &mut ExecutionLimitPathState) -> u32 {
        path.record_fork()
    }

    fn path_fork_limit(&self, path: &ExecutionLimitPathState) -> Option<ExecutionLimitReason> {
        self.config.max_forks_per_path.and_then(|max| {
            (path.total_forks >= max).then_some(ExecutionLimitReason::MaxForksPerPath { actual: path.total_forks, max })
        })
    }

    fn conditional_limit(
        &self,
        path: &ExecutionLimitPathState,
        function_name: Name,
        pc: usize,
        backtrace: &[(Name, usize)],
        source_location: SourceLoc,
        reason: ExecutionLimitReason,
    ) -> ExecutionLimitDecision {
        match self.config.on_limit_reached {
            LimitBehavior::Truncate => ExecutionLimitDecision::Truncate(reason),
            LimitBehavior::Concretize => {
                let scope = self.branch_scope(function_name, pc, backtrace, source_location);
                ExecutionLimitDecision::ConcretizeBranch { reason, sample: self.branch_sample(path, scope) }
            }
        }
    }

    fn branch_limit(
        &self,
        path: &ExecutionLimitPathState,
        scope: ControlFlowScope,
        reason: ExecutionLimitReason,
    ) -> ExecutionLimitDecision {
        match self.config.on_limit_reached {
            LimitBehavior::Truncate => ExecutionLimitDecision::Truncate(reason),
            LimitBehavior::Concretize => {
                ExecutionLimitDecision::ConcretizeBranch { reason, sample: self.branch_sample(path, scope) }
            }
        }
    }

    fn branch_sample(&self, path: &ExecutionLimitPathState, scope: ControlFlowScope) -> BranchSample {
        let ordinal = path.sample_ordinal(&scope);
        let pair_ordinal = ordinal / 2;
        let mut hasher = DefaultHasher::new();
        self.config.branch_sampling_seed.hash(&mut hasher);
        scope.hash(&mut hasher);
        pair_ordinal.hash(&mut hasher);
        let first = splitmix64(hasher.finish()) & 1 == 1;
        let preferred = if ordinal % 2 == 0 { first } else { !first };
        BranchSample { scope, ordinal, preferred }
    }

    fn branch_scope(
        &self,
        function_name: Name,
        pc: usize,
        backtrace: &[(Name, usize)],
        source_location: SourceLoc,
    ) -> ControlFlowScope {
        ControlFlowScope::new(function_name, pc, backtrace, source_location, self.config.call_context_depth)
    }

    fn loop_scope(
        &self,
        function_name: Name,
        target: usize,
        backtrace: &[(Name, usize)],
        source_location: SourceLoc,
    ) -> ControlFlowScope {
        ControlFlowScope::new(function_name, target, backtrace, source_location, self.config.call_context_depth)
    }
}

fn splitmix64(mut value: u64) -> u64 {
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scope() -> ControlFlowScope {
        ControlFlowScope::new(Name::from_u32(3), 30, &[(Name::from_u32(1), 10)], SourceLoc::new(1, 10, 0, 10, 4), None)
    }

    fn branch(handler: &ExecutionLimitHandler, path: &mut ExecutionLimitPathState) -> ExecutionLimitDecision {
        handler.on_branch_fork(path, Name::from_u32(3), 30, &[(Name::from_u32(1), 10)], SourceLoc::new(1, 10, 0, 10, 4))
    }

    #[test]
    fn path_state_reports_control_flow_steps() {
        let mut path = ExecutionLimitPathState::default();

        assert_eq!(path.control_flow_steps(), 0);
        path.advance_control_flow();
        path.advance_control_flow();
        assert_eq!(path.control_flow_steps(), 2);
    }

    #[test]
    fn execution_limits_default_and_builder_use_path_semantics() {
        assert_eq!(ExecutionLimits::default().call_context_depth, None);
        assert_eq!(ExecutionLimits::default().with_call_context_depth(None).call_context_depth, None);
        assert_eq!(ExecutionLimits::default().with_call_context_depth(0).call_context_depth, Some(0));

        let limits = ExecutionLimits::default()
            .with_max_forks_per_branch(3)
            .with_max_forks_per_path(7)
            .with_max_backjumps_per_loop(5)
            .with_max_path_depth(100)
            .with_call_context_depth(2)
            .with_limit_behavior(LimitBehavior::Concretize);

        assert_eq!(limits.max_forks_per_branch, Some(3));
        assert_eq!(limits.max_forks_per_path, Some(7));
        assert_eq!(limits.max_backjumps_per_loop, Some(5));
        assert_eq!(limits.max_path_depth, Some(100));
        assert_eq!(limits.call_context_depth, Some(2));
        assert_eq!(limits.on_limit_reached, LimitBehavior::Concretize);
    }

    #[test]
    fn execution_limits_only_activate_when_a_limit_is_configured() {
        assert!(!ExecutionLimits::default().is_active());
        assert!(!ExecutionLimits::default().with_call_context_depth(2).is_active());
        assert!(!ExecutionLimits::default().with_limit_region(SourceRegion::new(1, (10, 0), (11, 0))).is_active());
        assert!(ExecutionLimits::default().with_max_forks_per_branch(1).is_active());
        assert!(ExecutionLimits::default().with_max_forks_per_path(1).is_active());
        assert!(ExecutionLimits::default().with_max_backjumps_per_loop(1).is_active());
        assert!(ExecutionLimits::default().with_max_path_depth(1).is_active());
        assert!(ExecutionLimits::default().with_max_fork_pct_per_branch(0.5).is_active());
    }

    #[test]
    #[should_panic(expected = "max_fork_pct_per_branch must be a finite value in 0.0..=1.0")]
    fn fork_percentage_rejects_nan() {
        let _ = ExecutionLimits::default().with_max_fork_pct_per_branch(f64::NAN);
    }

    #[test]
    fn limit_region_uses_source_range_selection() {
        let limits = ExecutionLimits::default().with_limit_region(SourceRegion::new(1, (10, 5), (20, 8)));
        let inside = ControlFlowScope::new(Name::from_u32(7), 30, &[], SourceLoc::new(1, 12, 0, 19, 100), None);
        let same_location_in_other_function =
            ControlFlowScope::new(Name::from_u32(8), 40, &[], SourceLoc::new(1, 12, 0, 19, 100), None);
        let overlaps_start = ControlFlowScope::new(Name::from_u32(7), 30, &[], SourceLoc::new(1, 9, 0, 10, 6), None);
        let touches_start = ControlFlowScope::new(Name::from_u32(7), 30, &[], SourceLoc::new(1, 9, 0, 10, 5), None);
        let enclosing = ControlFlowScope::new(Name::from_u32(7), 30, &[], SourceLoc::new(1, 9, 0, 21, 0), None);
        let before = ControlFlowScope::new(Name::from_u32(7), 30, &[], SourceLoc::new(1, 9, 0, 10, 4), None);
        let after = ControlFlowScope::new(Name::from_u32(7), 30, &[], SourceLoc::new(1, 20, 9, 21, 0), None);

        assert!(limits.applies_to(&inside));
        assert!(limits.applies_to(&same_location_in_other_function));
        assert!(limits.applies_to(&overlaps_start));
        assert!(!limits.applies_to(&touches_start));
        assert!(!limits.applies_to(&enclosing));
        assert!(!limits.applies_to(&before));
        assert!(!limits.applies_to(&after));
    }

    #[test]
    fn explicitly_empty_region_filter_matches_no_source_location() {
        let limits = ExecutionLimits::default().with_limit_regions(Vec::new());
        let location = ControlFlowScope::new(Name::from_u32(7), 30, &[], SourceLoc::new(1, 12, 0, 19, 100), None);

        assert!(!limits.applies_to(&location));
    }

    #[test]
    fn control_flow_scope_separates_function_and_call_context() {
        let info = SourceLoc::new(1, 10, 0, 10, 4);
        let caller_a = Name::from_u32(1);
        let caller_b = Name::from_u32(2);
        let function = Name::from_u32(3);
        let other_function = Name::from_u32(4);
        let context_a = vec![(caller_a, 10), (caller_b, 20)];
        let context_b = vec![(caller_a, 11), (caller_b, 20)];

        let a = ControlFlowScope::new(function, 30, &context_a, info, Some(2));
        let b = ControlFlowScope::new(function, 30, &context_b, info, Some(2));
        let other = ControlFlowScope::new(other_function, 30, &context_a, info, Some(2));
        let last_frame_only = ControlFlowScope::new(function, 30, &context_a, info, Some(1));
        let same_last_frame = ControlFlowScope::new(function, 30, &context_b, info, Some(1));

        assert_ne!(a, b);
        assert_ne!(a, other);
        assert_eq!(last_frame_only, same_last_frame);
    }

    #[test]
    fn control_flow_scope_omits_call_context_when_disabled() {
        let info = SourceLoc::new(1, 10, 0, 10, 4);
        let function = Name::from_u32(3);
        let context_a = [(Name::from_u32(1), 10)];
        let context_b = [(Name::from_u32(2), 20)];

        let a = ControlFlowScope::new(function, 30, &context_a, info, None);
        let b = ControlFlowScope::new(function, 30, &context_b, info, None);
        let zero_depth = ControlFlowScope::new(function, 30, &context_a, info, Some(0));

        assert_eq!(a, b);
        assert!(a.call_context.is_none());
        assert_eq!(zero_depth.call_context, Some(Vec::new()));
        assert_ne!(a, zero_depth);
    }

    #[test]
    fn sampling_is_path_local_pair_balanced_and_two_phase() {
        let limits =
            ExecutionLimits::default().with_max_forks_per_branch(0).with_limit_behavior(LimitBehavior::Concretize);
        let handler = ExecutionLimitHandler::new(&limits);
        let mut first_path = ExecutionLimitPathState::default();
        let second_path = first_path.clone();
        let first = match branch(&handler, &mut first_path) {
            ExecutionLimitDecision::ConcretizeBranch { sample, .. } => sample,
            decision => panic!("unexpected decision: {:?}", decision),
        };
        let uncommitted = match branch(&handler, &mut first_path) {
            ExecutionLimitDecision::ConcretizeBranch { sample, .. } => sample,
            decision => panic!("unexpected decision: {:?}", decision),
        };
        assert_eq!(first, uncommitted);

        handler.commit_sample(&mut first_path, &first);
        let next = match branch(&handler, &mut first_path) {
            ExecutionLimitDecision::ConcretizeBranch { sample, .. } => sample,
            decision => panic!("unexpected decision: {:?}", decision),
        };
        let sibling = match branch(&handler, &mut second_path.clone()) {
            ExecutionLimitDecision::ConcretizeBranch { sample, .. } => sample,
            decision => panic!("unexpected decision: {:?}", decision),
        };

        assert_ne!(first.preferred(), next.preferred());
        assert_eq!(first.preferred(), sibling.preferred());
    }

    #[test]
    fn sibling_branch_budgets_are_path_local() {
        let limits = ExecutionLimits::default().with_max_forks_per_branch(1);
        let handler = ExecutionLimitHandler::new(&limits);
        let original = ExecutionLimitPathState::default();
        let mut first = original.clone();
        let mut second = original;

        assert!(matches!(branch(&handler, &mut first), ExecutionLimitDecision::Fork { fork_id: 0 }));
        assert!(matches!(branch(&handler, &mut second), ExecutionLimitDecision::Fork { fork_id: 0 }));
        assert!(matches!(
            branch(&handler, &mut first),
            ExecutionLimitDecision::Truncate(ExecutionLimitReason::MaxForksPerBranch { actual: 1, max: 1 })
        ));
        assert!(matches!(
            branch(&handler, &mut second),
            ExecutionLimitDecision::Truncate(ExecutionLimitReason::MaxForksPerBranch { actual: 1, max: 1 })
        ));
    }

    #[test]
    fn branch_percentage_uses_only_current_path_counts() {
        let limits = ExecutionLimits::default().with_max_fork_pct_per_branch(0.5).with_max_fork_pct_check_delay(0);
        let handler = ExecutionLimitHandler::new(&limits);
        let selected_scope = scope();
        let mut selected_path = ExecutionLimitPathState::default();
        selected_path.total_forks = 10;
        selected_path.branch_forks.insert(selected_scope.clone(), 6);
        let mut sibling_path = selected_path.clone();
        sibling_path.total_forks = 1000;
        sibling_path.branch_forks.insert(selected_scope, 1);

        assert!(matches!(
            branch(&handler, &mut selected_path),
            ExecutionLimitDecision::Truncate(ExecutionLimitReason::MaxForkPctPerBranch { .. })
        ));
        assert!(matches!(branch(&handler, &mut sibling_path), ExecutionLimitDecision::Fork { .. }));
    }

    #[test]
    fn default_handler_only_tracks_path_forks() {
        let limits = ExecutionLimits::default();
        let handler = ExecutionLimitHandler::new(&limits);
        let mut path = ExecutionLimitPathState::default();

        assert!(matches!(branch(&handler, &mut path), ExecutionLimitDecision::Fork { fork_id: 0 }));
        assert_eq!(path.total_forks, 1);
        assert!(path.branch_forks.is_empty());
    }

    #[test]
    fn monomorphize_forks_are_only_in_the_percentage_denominator() {
        let limits = ExecutionLimits::default().with_max_fork_pct_per_branch(0.5).with_max_fork_pct_check_delay(0);
        let handler = ExecutionLimitHandler::new(&limits);
        let mut path = ExecutionLimitPathState::default();

        assert!(matches!(handler.on_monomorphize_fork(&mut path), ExecutionLimitDecision::Fork { fork_id: 0 }));
        assert!(matches!(branch(&handler, &mut path), ExecutionLimitDecision::Fork { fork_id: 1 }));
        assert!(matches!(branch(&handler, &mut path), ExecutionLimitDecision::Fork { fork_id: 2 }));
        assert!(matches!(
            branch(&handler, &mut path),
            ExecutionLimitDecision::Truncate(ExecutionLimitReason::MaxForkPctPerBranch {
                branch_actual: 2,
                path_actual: 3,
                ..
            })
        ));
    }

    #[test]
    fn branch_percentage_uses_pre_fork_ratio_and_strict_greater_than() {
        let limits = ExecutionLimits::default().with_max_fork_pct_per_branch(0.5).with_max_fork_pct_check_delay(0);
        let handler = ExecutionLimitHandler::new(&limits);
        let selected_scope = scope();
        let mut path = ExecutionLimitPathState::default();
        path.total_forks = 10;
        path.branch_forks.insert(selected_scope, 5);

        assert!(matches!(branch(&handler, &mut path), ExecutionLimitDecision::Fork { fork_id: 10 }));
        assert!(matches!(
            branch(&handler, &mut path),
            ExecutionLimitDecision::Truncate(ExecutionLimitReason::MaxForkPctPerBranch {
                branch_actual: 6,
                path_actual: 11,
                ..
            })
        ));
    }

    #[test]
    fn branch_percentage_check_delay_uses_current_path_total() {
        let limits = ExecutionLimits::default().with_max_fork_pct_per_branch(0.5).with_max_fork_pct_check_delay(4);
        let handler = ExecutionLimitHandler::new(&limits);
        let selected_scope = scope();
        let mut path = ExecutionLimitPathState::default();
        path.total_forks = 4;
        path.branch_forks.insert(selected_scope, 4);

        assert!(matches!(branch(&handler, &mut path), ExecutionLimitDecision::Fork { fork_id: 4 }));
        assert!(matches!(
            branch(&handler, &mut path),
            ExecutionLimitDecision::Truncate(ExecutionLimitReason::MaxForkPctPerBranch {
                branch_actual: 5,
                path_actual: 5,
                check_delay: 4,
                ..
            })
        ));
    }

    #[test]
    fn path_fork_limit_counts_branch_and_monomorphize_forks() {
        let limits = ExecutionLimits::default().with_max_forks_per_path(2);
        let handler = ExecutionLimitHandler::new(&limits);
        let mut path = ExecutionLimitPathState::default();

        assert!(matches!(branch(&handler, &mut path), ExecutionLimitDecision::Fork { fork_id: 0 }));
        assert!(matches!(handler.on_monomorphize_fork(&mut path), ExecutionLimitDecision::Fork { fork_id: 1 }));
        assert!(matches!(
            branch(&handler, &mut path),
            ExecutionLimitDecision::Truncate(ExecutionLimitReason::MaxForksPerPath { actual: 2, max: 2 })
        ));
    }

    #[test]
    fn region_does_not_gate_path_fork_accounting() {
        let limits = ExecutionLimits::default()
            .with_max_forks_per_path(1)
            .with_limit_region(SourceRegion::from_source_loc(SourceLoc::new(2, 20, 0, 30, 0)));
        let handler = ExecutionLimitHandler::new(&limits);
        let mut path = ExecutionLimitPathState::default();

        assert!(matches!(branch(&handler, &mut path), ExecutionLimitDecision::Fork { fork_id: 0 }));
        assert!(matches!(
            branch(&handler, &mut path),
            ExecutionLimitDecision::Truncate(ExecutionLimitReason::MaxForksPerPath { actual: 1, max: 1 })
        ));
    }

    #[test]
    fn branch_local_limit_only_applies_inside_selected_region() {
        let limits = ExecutionLimits::default()
            .with_max_forks_per_branch(0)
            .with_limit_region(SourceRegion::from_source_loc(SourceLoc::new(1, 20, 0, 30, 0)));
        let handler = ExecutionLimitHandler::new(&limits);
        let mut outside = ExecutionLimitPathState::default();
        let mut inside = ExecutionLimitPathState::default();

        assert!(matches!(branch(&handler, &mut outside), ExecutionLimitDecision::Fork { fork_id: 0 }));
        assert!(matches!(
            handler.on_branch_fork(&mut inside, Name::from_u32(99), 30, &[], SourceLoc::new(1, 25, 0, 25, 4)),
            ExecutionLimitDecision::Truncate(ExecutionLimitReason::MaxForksPerBranch { actual: 0, max: 0 })
        ));
    }

    #[test]
    fn sibling_loop_counts_are_path_local() {
        let limits = ExecutionLimits::default().with_max_backjumps_per_loop(0);
        let handler = ExecutionLimitHandler::new(&limits);
        let original = ExecutionLimitPathState::default();
        let mut first = original.clone();
        let mut second = original;

        assert!(matches!(
            handler.on_goto(&mut first, Name::from_u32(3), 10, 10, &[]),
            ExecutionLimitDecision::Truncate(ExecutionLimitReason::MaxBackjumpsPerLoop {
                target: 10,
                actual: 1,
                max: 0,
            })
        ));
        assert!(matches!(
            handler.on_goto(&mut second, Name::from_u32(3), 10, 10, &[]),
            ExecutionLimitDecision::Truncate(ExecutionLimitReason::MaxBackjumpsPerLoop {
                target: 10,
                actual: 1,
                max: 0,
            })
        ));
    }

    #[test]
    fn goto_without_source_location_does_not_match_source_region() {
        let selected = SourceLoc::new(1, 10, 0, 10, 4);
        let limits = ExecutionLimits::default()
            .with_max_backjumps_per_loop(0)
            .with_limit_region(SourceRegion::from_source_loc(selected));
        let source_only = ExecutionLimitHandler::new(&limits);
        let mut source_path = ExecutionLimitPathState::default();

        assert_eq!(
            source_only.on_goto(&mut source_path, Name::from_u32(3), 10, 10, &[]),
            ExecutionLimitDecision::Continue
        );
    }

    #[test]
    fn path_depth_precedes_loop_limit_for_conditional_jump() {
        let limits = ExecutionLimits::default().with_max_path_depth(0).with_max_backjumps_per_loop(0);
        let handler = ExecutionLimitHandler::new(&limits);
        let mut path = ExecutionLimitPathState::default();

        assert!(matches!(
            handler.on_conditional_jump(&mut path, Name::from_u32(3), 10, 10, &[], SourceLoc::unknown(),),
            ExecutionLimitDecision::Truncate(ExecutionLimitReason::MaxPathDepth { actual: 1, max: 0 })
        ));
        assert!(path.loop_counts.is_empty());
    }
}
