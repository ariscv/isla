//! 查询资源边界：事务内复用完整约束前缀，事务外保留既有策略及显式增量范围。
use super::*;

pub(super) enum QueryPurpose {
    General,
    RangeProof,
    BooleanProof,
    BranchFeasibility,
    EntryBranchFeasibility,
}

impl QueryPurpose {
    pub(super) fn requests_snapshot<B: BV>(&self, solver: &Solver<B>, ast: &Ast) -> bool {
        match self {
            Self::General | Self::EntryBranchFeasibility => false,
            Self::RangeProof => true,
            Self::BooleanProof | Self::BranchFeasibility => {
                if SMT_CONFIG.get().unwrap().tactic != Tactic::Default || solver.incremental_checks {
                    return false;
                }
                // 成本启发式只选调用形态，不改变前提、结果或资源预算。
                // 访问翻译后的DAG，穿过DefineConst内联；节点及边合计访问256次即选快照。
                let mut pending = vec![ast.z3_ast];
                let mut visited = HashSet::new();
                let mut work = 0;
                while let Some(node) = pending.pop() {
                    if !visited.insert(node) {
                        continue;
                    }
                    work += 1;
                    if work >= 256 {
                        return true;
                    }
                    unsafe {
                        if Z3_get_ast_kind(solver.ctx.z3_ctx, node) == AstKind::App {
                            let app = Z3_to_app(solver.ctx.z3_ctx, node);
                            for index in 0..Z3_get_app_num_args(solver.ctx.z3_ctx, app) {
                                work += 1;
                                if work >= 256 {
                                    return true;
                                }
                                pending.push(Z3_get_app_arg(solver.ctx.z3_ctx, app, index));
                            }
                        }
                    }
                }
                false
            }
        }
    }
}

pub(super) fn floating_type(ty: &smtlib::Ty) -> bool {
    match ty {
        smtlib::Ty::Float(..) | smtlib::Ty::RoundingMode => true,
        smtlib::Ty::Array(index, value) => floating_type(index) || floating_type(value),
        _ => false,
    }
}

/// 完整约束的可重用查询上下文；固化基础为单个合取断言，可撤销后缀按共同前缀逐项pop。
/// 不修改执行solver的scope／缓冲／迹，模型仍通过既有record_check_result管理。
pub(super) struct RegionQuery<'ctx> {
    ctx: &'ctx Context,
    z3_solver: Z3_solver,
    prefix: Vec<Ast<'ctx>>,
    /// 逻辑前缀的前base_len项已合取为基础层，不能逐项pop。
    base_len: usize,
}

impl Drop for RegionQuery<'_> {
    fn drop(&mut self) {
        unsafe { Z3_solver_dec_ref(self.ctx.z3_ctx, self.z3_solver) };
    }
}

pub(super) struct QuerySolver<'ctx> {
    ctx: &'ctx Context,
    pub(super) z3_solver: Z3_solver,
    independent: bool,
}

pub(crate) struct ArmErrorQueries<'ctx, B> {
    replay: arm_error_replay::ArmErrorReplay<'ctx, B>,
    ctx: &'ctx Context,
    active: Option<QuerySolver<'ctx>>,
    batch_size: usize,
    checked: usize,
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    /// 只对可增量回放的叶启动私有 Context。慢查询文件编号继续由单线程按序分配。
    pub(crate) fn arm_error_worker_config(&self) -> Option<impl Fn() -> Config + 'static> {
        if !self.validates_candidates()
            || SMT_CONFIG.get().unwrap().tactic != Tactic::Default
            || dump::dumps_slow_queries()
        {
            return None;
        }
        let (options, validation) = self.arm_context_options();
        let timeout = self.ctx.native_timeout;
        let rlimit = self.ctx.rlimit;
        Some(move || {
            let mut config = Config::new();
            (config.solver_options, config.validation) = (options, validation);
            if let Some(timeout) = timeout {
                config.set_param_value("timeout", &timeout.as_millis().to_string());
            }
            if let Some(rlimit) = rlimit {
                config.set_param_value("rlimit", &rlimit.to_string());
            }
            config
        })
    }

    pub(crate) fn arm_error_queries(&self, count: usize) -> Option<ArmErrorQueries<'ctx, B>> {
        let config = SMT_CONFIG.get().unwrap();
        (count > 1 && self.validates_candidates() && config.tactic == Tactic::Default).then(|| ArmErrorQueries {
            replay: arm_error_replay::ArmErrorReplay::new(self.ctx),
            ctx: self.ctx,
            active: None,
            batch_size: crate::config::RegionOptions::current().arm_error_batch_size.get(),
            checked: 0,
        })
    }
}

impl<B: BV> ArmErrorQueries<'_, B> {
    pub(super) fn check(&mut self, point: &Checkpoint<B>, target: &Exp<Sym>, info: SourceLoc) -> SmtResult {
        let verifier = self.replay.restore(point);
        let active = self.active.get_or_insert_with(|| {
            let ctx = self.ctx;
            let z3_solver = unsafe { new_z3_solver(ctx.z3_ctx, Tactic::Default.as_c_str(), None) };
            QuerySolver { ctx, z3_solver, independent: false }
        });
        let result = active.check_arm_error(verifier, target, info);
        self.checked += 1;
        if self.checked == self.batch_size {
            self.active = None;
            self.checked = 0;
        }
        result
    }
}

pub(super) struct ResourceBudget {
    limit: u32,
    before: u64,
}

impl QuerySolver<'_> {
    pub(super) fn resource_budget(&self, override_limit: Option<u32>) -> Option<ResourceBudget> {
        let limit = override_limit.or(self.ctx.rlimit)?;
        let before = unsafe { proof_budget::resource_count(self.ctx, self.z3_solver).unwrap_or(0) };
        Some(ResourceBudget { limit, before })
    }

    pub(super) fn failure(&self, info: SourceLoc, elapsed: Duration, budget: Option<ResourceBudget>) -> SmtError {
        let reason = z3_reason_unknown(self.ctx, self.z3_solver);
        // 策略型查询耗尽 rlimit 时也可能只返回 canceled。只有计数触及限额才归到资源耗尽。
        let rlimit_exhausted = matches!(reason.trim(), "canceled" | "sat.canceled")
            && budget.is_some_and(|budget| unsafe {
                proof_budget::resource_count(self.ctx, self.z3_solver)
                    .is_some_and(|after| after.saturating_sub(budget.before) >= u64::from(budget.limit))
            });
        z3_query_error(info, elapsed, self.ctx.native_timeout, reason, rlimit_exhausted)
    }

    /// 每个选择器只启用自己冻结的完整公式。其它选择器可以全为假，因此两条错误域无需相容。
    fn check_arm_error<B: BV>(&self, verifier: &Solver<B>, target: &Exp<Sym>, info: SourceLoc) -> SmtResult {
        let native = self.z3_solver;
        let ctx = self.ctx;
        let _scope = crate::executor::stats::region_progress::QueryScope::fallback("arm_error");
        let goal = verifier.translate_exp(target);
        let selector = unsafe {
            let mut terms: Vec<_> = verifier.replay_assertions.as_ref().unwrap().iter().map(|a| a.z3_ast).collect();
            terms.push(goal.z3_ast);
            let formula = Z3_mk_and(ctx.z3_ctx, terms.len().try_into().unwrap(), terms.as_ptr());
            Z3_inc_ref(ctx.z3_ctx, formula);
            let formula = Ast { ctx, z3_ast: formula };
            let flag = Z3_mk_fresh_const(ctx.z3_ctx, c"isla_arm_error".as_ptr(), Z3_mk_bool_sort(ctx.z3_ctx));
            Z3_inc_ref(ctx.z3_ctx, flag);
            let selector = Ast { ctx, z3_ast: flag };
            Z3_solver_assert(ctx.z3_ctx, native, Z3_mk_implies(ctx.z3_ctx, flag, formula.z3_ast));
            selector
        };
        let slow = verifier.slow_query_begin(native);
        let resource_budget = self.resource_budget(None);
        let started = Instant::now();
        let result = match timeout_Z3_solver_check_assumptions(ctx.z3_ctx, native, &[selector.z3_ast], info) {
            Ok(result) => result,
            Err(Z3TimeoutError::Interrupted(limit)) => {
                let dump = timeout_dump_from_checkpoint(
                    verifier.checkpoint_snapshot(),
                    SmtDumpRequest::CheckSatWith(target.clone()),
                );
                return Error(z3_timeout_error(SmtOperation::CheckSatAssuming, info, started.elapsed(), limit, dump));
            }
        };
        let elapsed = started.elapsed();
        verifier.slow_query_finish(slow, native, Some(target), info, result);
        match result {
            Z3_L_TRUE => Sat,
            Z3_L_FALSE => Unsat,
            _ => Error(self.failure(info, elapsed, resource_budget)),
        }
    }
}

#[cfg(test)]
impl<B> ArmErrorQueries<'_, B> {
    pub(crate) fn used_for_last_check(&self) -> bool {
        self.active.as_ref().is_some_and(|batch| z3_timeout::last_solver_query().0 == batch.z3_solver as usize)
    }

    pub(crate) fn batch_released(&self) -> bool {
        self.active.is_none()
    }
}

impl QuerySolver<'_> {
    pub(super) fn assumptions<'a>(&self, conditions: &'a [Z3_ast]) -> &'a [Z3_ast] {
        if self.independent {
            &[]
        } else {
            conditions
        }
    }
}

impl Drop for QuerySolver<'_> {
    fn drop(&mut self) {
        unsafe { Z3_solver_dec_ref(self.ctx.z3_ctx, self.z3_solver) };
    }
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    pub(super) fn query_solver(&mut self, assumptions: &[Z3_ast], snapshot_requested: bool) -> QuerySolver<'ctx> {
        if crate::executor::stats::region_progress::needs_footprint() {
            self.profile_query_footprint(assumptions);
        }
        let setup = WorkTimer::start(WorkKind::QuerySetup);
        let config = SMT_CONFIG.get().expect("查询前必须初始化SMT");
        // 实验性的原生快照边界：同一完整公式在首次check前批量装入，不预先push。
        // 只改变求解调用形态；结果及模型仍须满足全部已发布/缓冲/活动臂前提。
        let native_snapshot = snapshot_requested && crate::config::RegionOptions::current().native_snapshot;
        if config.tactic == Tactic::Default
            && !native_snapshot
            && (snapshot_requested || self.floating_point_seen.get())
            && !self.incremental_checks
            && self.transaction_depth() > 0
        {
            // 小查询原来已经在主solver上增量执行，不另建上下文。
            // 只复用原来会新建快照的查询；主solver全部断言（含活动臂）＋全部缓冲断言及本次条件。
            // 不做切片、不删约束；目标条件也是可撤销的最后一层，不能泄漏到下次查询。
            unsafe {
                let (complete, _) = self.region_query_complete(assumptions, prefix_compaction_enabled());
                let reusable = self.region_query.get_or_insert_with(|| RegionQuery {
                    ctx: self.ctx,
                    z3_solver: new_z3_solver(
                        self.ctx.z3_ctx,
                        config.tactic.as_c_str(),
                        self.seed.map(|seed| (config.seed_param, seed)),
                    ),
                    prefix: Vec::new(),
                    base_len: 0,
                });
                // 同一Context中AST已驻留，旧前缀持有引用，指针相等就是同一公式。
                let mut common =
                    reusable.prefix.iter().zip(&complete).take_while(|(old, new)| old.z3_ast == **new).count();
                if common < reusable.base_len {
                    // 已固化前提因回滚或符号改绑而变化；旧基础不能局部pop，完整重建当前查询。
                    let fresh = new_z3_solver(
                        self.ctx.z3_ctx,
                        config.tactic.as_c_str(),
                        self.seed.map(|seed| (config.seed_param, seed)),
                    );
                    Z3_solver_dec_ref(self.ctx.z3_ctx, reusable.z3_solver);
                    reusable.z3_solver = fresh;
                    reusable.prefix.clear();
                    reusable.base_len = 0;
                    common = 0;
                }
                let remove = reusable.prefix.len() - common;
                if remove > 0 {
                    Z3_solver_pop(
                        self.ctx.z3_ctx,
                        reusable.z3_solver,
                        remove.try_into().expect("查询断言层数超出Z3接口"),
                    );
                }
                reusable.prefix.truncate(common);
                for z3_ast in &complete[common..] {
                    Z3_solver_push(self.ctx.z3_ctx, reusable.z3_solver);
                    Z3_solver_assert(self.ctx.z3_ctx, reusable.z3_solver, *z3_ast);
                    // 旧接口只返回裸AST；在下一次prefix比较之前必须保有其引用。
                    Z3_inc_ref(self.ctx.z3_ctx, *z3_ast);
                    reusable.prefix.push(Ast { ctx: self.ctx, z3_ast: *z3_ast });
                }
                Z3_solver_inc_ref(self.ctx.z3_ctx, reusable.z3_solver);
                // 全部假设已逐项断言；外层不再以assumptions重复提交。
                drop(setup);
                return QuerySolver { ctx: self.ctx, z3_solver: reusable.z3_solver, independent: true };
            }
        }

        // 普通BV深路径保留增量学习。数值范围和复杂布尔证明是反例或可行性查询，真实公式显示
        // 首次普通check显著快于增量假设；仍复制全部前提，不弱化证明。
        let independent = config.tactic == Tactic::Default
            && (snapshot_requested || self.floating_point_seen.get())
            && !self.incremental_checks;
        unsafe {
            if !independent {
                Z3_solver_inc_ref(self.ctx.z3_ctx, self.z3_solver);
                drop(setup);
                return QuerySolver { ctx: self.ctx, z3_solver: self.z3_solver, independent };
            }
            let query = self.independent_query(assumptions, None);
            drop(setup);
            query
        }
    }

    pub(super) fn query_from_assertions(&self, assertions: &[Z3_ast]) -> QuerySolver<'ctx> {
        let _setup = WorkTimer::start(WorkKind::QuerySetup);
        let config = SMT_CONFIG.get().expect("查询前必须初始化SMT");
        unsafe {
            let z3_solver = new_z3_solver(
                self.ctx.z3_ctx,
                config.tactic.as_c_str(),
                self.seed.map(|seed| (config.seed_param, seed)),
            );
            for &assertion in assertions {
                Z3_solver_assert(self.ctx.z3_ctx, z3_solver, assertion);
            }
            QuerySolver { ctx: self.ctx, z3_solver, independent: true }
        }
    }

    /// 同Context、同配置／种子，复制完整逻辑式。资源上限只存在此独立查询中。
    pub(super) fn independent_query(&self, assumptions: &[Z3_ast], limit: Option<u32>) -> QuerySolver<'ctx> {
        let config = SMT_CONFIG.get().expect("查询前必须初始化SMT");
        unsafe {
            let z3_solver = new_z3_solver(
                self.ctx.z3_ctx,
                config.tactic.as_c_str(),
                self.seed.map(|seed| (config.seed_param, seed)),
            );
            let query = QuerySolver { ctx: self.ctx, z3_solver, independent: true };
            // 当前solver包括活动臂条件；缓冲断言与本次条件由调用方补齐。
            let assertions = Z3_solver_get_assertions(self.ctx.z3_ctx, self.z3_solver);
            Z3_ast_vector_inc_ref(self.ctx.z3_ctx, assertions);
            for index in 0..Z3_ast_vector_size(self.ctx.z3_ctx, assertions) {
                Z3_solver_assert(self.ctx.z3_ctx, z3_solver, Z3_ast_vector_get(self.ctx.z3_ctx, assertions, index));
            }
            Z3_ast_vector_dec_ref(self.ctx.z3_ctx, assertions);
            for assumption in assumptions {
                Z3_solver_assert(self.ctx.z3_ctx, z3_solver, *assumption);
            }
            if let Some(limit) = limit {
                let params = Z3_mk_params(self.ctx.z3_ctx);
                Z3_params_inc_ref(self.ctx.z3_ctx, params);
                Z3_params_set_uint(
                    self.ctx.z3_ctx,
                    params,
                    Z3_mk_string_symbol(self.ctx.z3_ctx, b"rlimit\0".as_ptr().cast()),
                    limit,
                );
                Z3_solver_set_params(self.ctx.z3_ctx, z3_solver, params);
                Z3_params_dec_ref(self.ctx.z3_ctx, params);
            }
            query
        }
    }

    /// 每条回边之间只采第一条真实查询；复用已经翻译的断言，不额外translate或check。
    fn profile_query_footprint(&self, assumptions: &[Z3_ast]) {
        let timer = WorkTimer::start(WorkKind::Profiling);
        let mut buffered = 0;
        let mut expression_nodes = 0;
        let mut expression_bytes = 0;
        for event in &self.transaction_events {
            if let Event::Smt(Def::Assert(exp), ..) = event {
                let (nodes, heap) = crate::executor::stats::memory_stats::exp_stats(exp);
                buffered += 1;
                expression_nodes += nodes;
                expression_bytes += std::mem::size_of_val(exp) + heap;
            }
        }
        assert!(assumptions.len() >= buffered, "查询必须包含全部缓冲断言");
        unsafe {
            let assertions = Z3_solver_get_assertions(self.ctx.z3_ctx, self.z3_solver);
            Z3_ast_vector_inc_ref(self.ctx.z3_ctx, assertions);
            let active = Z3_ast_vector_size(self.ctx.z3_ctx, assertions);
            let mut context =
                (0..active).map(|i| Z3_ast_vector_get(self.ctx.z3_ctx, assertions, i)).collect::<Vec<_>>();
            context.extend_from_slice(&assumptions[..buffered]);
            let (context_nodes, context_truncated) = self.profile_ast_nodes(context);
            let (goal_nodes, goal_truncated) = self.profile_ast_nodes(assumptions[buffered..].to_vec());
            crate::executor::stats::region_progress::footprint(serde_json::json!({
                "active_assertions":active,"buffered_assertions":buffered,
                "buffered_expression_nodes":expression_nodes,"buffered_expression_bytes":expression_bytes,
                "context_ast_dag_nodes":context_nodes,"context_ast_truncated":context_truncated,
                "goal_ast_dag_nodes":goal_nodes,"goal_ast_truncated":goal_truncated,
                "note":"每轮第一条真实查询之前；bytes为Rust表达式载荷，nodes分别为原始树/展开DAG；不等于Z3/RSS字节"}));
            Z3_ast_vector_dec_ref(self.ctx.z3_ctx, assertions);
        }
        drop(timer);
    }

    unsafe fn profile_ast_nodes(&self, mut pending: Vec<Z3_ast>) -> (usize, bool) {
        let mut seen = HashSet::new();
        while let Some(node) = pending.pop() {
            if !seen.insert(node as usize) {
                continue;
            }
            if seen.len() >= 100_000 {
                return (seen.len(), true);
            }
            match Z3_get_ast_kind(self.ctx.z3_ctx, node) {
                AstKind::App => {
                    let app = Z3_to_app(self.ctx.z3_ctx, node);
                    for i in 0..Z3_get_app_num_args(self.ctx.z3_ctx, app) {
                        pending.push(Z3_get_app_arg(self.ctx.z3_ctx, app, i));
                    }
                }
                AstKind::Quantifier => pending.push(Z3_get_quantifier_body(self.ctx.z3_ctx, node)),
                _ => (),
            }
        }
        (seen.len(), false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;

    // SMT配置在进程内固定；沿用隔离子进程测试，避免其他回归先选Qfaufbv。
    fn default_tactic_child(name: &str) -> bool {
        if std::env::var("ISLA_REGION_QUERY_LIFETIME_TEST").as_deref() == Ok(name) {
            return true;
        }
        let status = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", name, "--nocapture", "--test-threads=1"])
            .env("ISLA_REGION_QUERY_LIFETIME_TEST", name)
            .status()
            .unwrap();
        assert!(status.success(), "默认策略的资源生命周期子测试失败");
        false
    }

    #[test]
    fn region_query_released_after_outer_commit() {
        if !default_tactic_child("smt::query::tests::region_query_released_after_outer_commit") {
            return;
        }
        configure_tastic(Tactic::Default);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let value = solver.declare_const(Ty::Bool, info);
        solver.start_transaction();
        solver.assert(Exp::Var(value));
        assert!(solver.check_sat_with_for_range(&Exp::Var(value), info).is_sat().unwrap());
        assert!(solver.region_query.is_some());
        solver.commit_transaction();
        assert!(solver.region_query.is_none(), "区域已结束，临时查询不能继续持有前缀");
        assert!(solver.check_sat_with(&Exp::Not(Box::new(Exp::Var(value))), info).is_unsat().unwrap());
    }

    #[test]
    fn region_query_released_after_outer_rollback_but_not_inner_rollback() {
        if !default_tactic_child("smt::query::tests::region_query_released_after_outer_rollback_but_not_inner_rollback")
        {
            return;
        }
        configure_tastic(Tactic::Default);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let value = solver.declare_const(Ty::Bool, info);
        let outer = solver.start_transaction();
        let inner = solver.start_transaction();
        solver.assert(Exp::Var(value));
        assert!(solver.check_sat_with_for_range(&Exp::Var(value), info).is_sat().unwrap());
        assert!(solver.region_query.is_some());
        solver.rollback_transaction(inner);
        assert!(solver.region_query.is_some(), "活动外层仍可复用查询资源");
        solver.rollback_transaction(outer);
        assert!(solver.region_query.is_none(), "回滚必须释放已废弃的查询前缀");
        assert!(solver.check_sat_with(&Exp::Not(Box::new(Exp::Var(value))), info).is_sat().unwrap());
    }

    #[test]
    fn temporary_guard_restores_unchanged_caller_witness() {
        configure_tastic(Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let value = solver.declare_const(Ty::Bool, info);
        solver.assert(Exp::Var(value));
        assert!(solver.check_sat(info).is_sat().unwrap());
        let tx = solver.start_transaction();
        let before = test_query_count();
        solver.with_transaction_condition(&Exp::Not(Box::new(Exp::Var(value))), |solver| {
            assert_eq!(solver.cached_bool_value(&Exp::Var(value)).unwrap(), None, "调用者见证不能用于临时的相反条件");
            solver.define_const(Exp::Var(value), info);
        });
        assert_eq!(
            solver.cached_bool_value(&Exp::Var(value)).unwrap(),
            Some(true),
            "仅新增定义并退出临时条件后，调用者的完整见证仍然有效"
        );
        assert!(solver.check_sat(info).is_sat().unwrap());
        assert_eq!(test_query_count(), before, "只读范围结束不应重查同一前提");
        solver.rollback_transaction(tx);
    }

    #[test]
    fn z3_failure_reason_classifies_native_results() {
        for (native_reason, expected) in [
            ("timeout", "SpeculativeRejectReason::Z3Timeout"),
            ("interrupted", "SpeculativeRejectReason::Z3Timeout"),
            ("interrupted from keyboard", "SpeculativeRejectReason::Z3Timeout"),
            ("canceled", "SpeculativeRejectReason::Z3Timeout"),
            ("sat.canceled", "SpeculativeRejectReason::Z3Timeout"),
            ("max. resource limit exceeded", "SpeculativeRejectReason::Z3ResourceExhausted"),
            ("(resource limits reached)", "SpeculativeRejectReason::Z3ResourceExhausted"),
            ("max. memory exceeded", "SpeculativeRejectReason::Z3ResourceExhausted"),
            ("out of memory", "SpeculativeRejectReason::Z3ResourceExhausted"),
            ("memout", "SpeculativeRejectReason::Z3ResourceExhausted"),
            ("max-conflicts-reached", "SpeculativeRejectReason::Z3ResourceExhausted"),
            ("max. scopes exceeded", "SpeculativeRejectReason::Z3ResourceExhausted"),
            ("max. steps exceeded", "SpeculativeRejectReason::Z3ResourceExhausted"),
            ("max. frames exceeded", "SpeculativeRejectReason::Z3ResourceExhausted"),
            ("(incomplete (theory arithmetic))", "SpeculativeRejectReason::UnknownZ3"),
            ("", "SpeculativeRejectReason::UnknownZ3"),
        ] {
            let error = z3_query_error(SourceLoc::unknown(), Duration::ZERO, None, native_reason.into(), false);
            assert_eq!(error.reject_reason().to_string(), expected, "{native_reason:?}");
            assert_eq!(error.diagnostic()["reason_unknown"], native_reason);
            assert_eq!(Error(error).is_unknown(), expected == "SpeculativeRejectReason::UnknownZ3");
        }
        for native_reason in ["canceled", "sat.canceled"] {
            let error = z3_query_error(SourceLoc::unknown(), Duration::ZERO, None, native_reason.into(), true);
            assert_eq!(
                error.reject_reason().to_string(),
                "SpeculativeRejectReason::Z3ResourceExhausted",
                "{native_reason}"
            );
        }
    }

    #[test]
    fn boolean_proof_rlimit_unknown_does_not_limit_range_branch_or_terminal() {
        if !default_tactic_child(
            "smt::query::tests::boolean_proof_rlimit_unknown_does_not_limit_range_branch_or_terminal",
        ) {
            return;
        }
        crate::config::RegionOptions { bool_proof_rlimit: 1, ..Default::default() }.configure();
        configure_tastic(Tactic::Default);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let x = solver.declare_const(Ty::BitVec(64), info);
        let goal = Exp::Eq(
            Box::new(Exp::Bvmul(Box::new(Exp::Var(x)), Box::new(Exp::Var(x)))),
            Box::new(Exp::Bits64(B64::new(9, 64))),
        );
        let tx = solver.start_transaction();
        assert!(
            matches!(solver.check_sat_with_for_bool(&goal, info), Unproven(SmtError::Z3ResourceExhausted(query)) if !query.reason.is_empty()),
            "只限制可选的布尔证明"
        );
        assert!(
            solver.check_sat_with_for_branch(&goal, info, true).unwrap().is_sat().unwrap(),
            "区域分支不是可选布尔化简，不能继承预算"
        );
        solver.clear_stashed_model();
        assert!(solver.check_sat_with_for_range(&goal, info).is_sat().unwrap(), "范围证明不受限");
        solver.clear_stashed_model();
        assert!(solver.check_sat_with(&goal, info).is_sat().unwrap(), "普通分支查询不受限");
        solver.assert(goal.clone());
        assert!(solver.check_sat_deadline(info, Duration::from_secs(5)).is_sat().unwrap(), "终态求解不继承rlimit");
        solver.rollback_transaction(tx);
        solver.clear_stashed_model();
        assert!(solver.check_sat_with_for_bool(&goal, info).is_sat().unwrap(), "事务外不受此区域上限影响");
    }
    #[test]
    fn boolean_proof_rlimit_unknown_keeps_exact_symbolic_relation() {
        if !default_tactic_child("smt::query::tests::boolean_proof_rlimit_unknown_keeps_exact_symbolic_relation") {
            return;
        }
        crate::config::RegionOptions { bool_proof_rlimit: 1, ..Default::default() }.configure();
        configure_tastic(Tactic::Default);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let x = solver.declare_const(Ty::BitVec(64), info);
        solver.assert(Exp::Eq(Box::new(Exp::Var(x)), Box::new(Exp::Bits64(B64::new(0, 64)))));
        let tx = solver.start_transaction();
        let result = crate::primop::lt_bits_u(
            crate::ir::Val::Symbolic(x),
            crate::ir::Val::Bits(B64::new(8, 64)),
            &mut solver,
            info,
        )
        .unwrap();
        let crate::ir::Val::Symbolic(value) = result else {
            panic!("资源耗尽必须保留布尔符号，不冒充已证明常量");
        };
        assert!(solver.check_sat_with(&Exp::Var(value), info).is_sat().unwrap());
        assert!(
            solver.check_sat_with(&Exp::Not(Box::new(Exp::Var(value))), info).is_unsat().unwrap(),
            "定义必须保留原表达式的精确关系"
        );
        solver.rollback_transaction(tx);
    }
    #[test]
    fn witness_native_sat_refreshes_pool_after_fast_miss() {
        if !default_tactic_child("smt::query::tests::witness_native_sat_refreshes_pool_after_fast_miss") {
            return;
        }
        crate::config::RegionOptions { witness_eval: true, ..Default::default() }.configure();
        configure_tastic(Tactic::Default);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let x = solver.declare_const(Ty::BitVec(8), info);
        let old = Exp::Eq(Box::new(Exp::Var(x)), Box::new(Exp::Bits64(B64::new(0, 8))));
        assert!(solver.check_sat_with(&old, info).is_sat().unwrap());
        let tx = solver.start_transaction();
        let goal = Exp::Eq(
            Box::new(Exp::Bvmul(Box::new(Exp::Var(x)), Box::new(Exp::Var(x)))),
            Box::new(Exp::Bits64(B64::new(9, 8))),
        );
        let before = test_query_count();
        assert!(solver.check_sat_with(&goal, info).is_sat().unwrap());
        assert_eq!(test_query_count(), before + 1, "快路未证明时确实交回原搜索");
        assert_eq!(solver.cached_bool_value(&goal).unwrap(), Some(true), "真实SAT更新当前见证");
        let ast = solver.translate_exp(&goal);
        assert_eq!(solver.shadow_witnesses.evaluate(&[ast.z3_ast])["method"], "retained", "新模型确实回写见证池");
        solver.clear_stashed_model();
        assert!(solver.check_sat_with(&goal, info).is_sat().unwrap());
        assert_eq!(test_query_count(), before + 1, "清除当前缓存后也能从池取回刚才的新模型");
        solver.rollback_transaction(tx);
    }
    #[test]
    fn witness_eval_fast_sat_keeps_symbolic_both_arms_and_never_skips_unsat() {
        if !default_tactic_child(
            "smt::query::tests::witness_eval_fast_sat_keeps_symbolic_both_arms_and_never_skips_unsat",
        ) {
            return;
        }
        crate::config::RegionOptions { witness_eval: true, ..Default::default() }.configure();
        configure_tastic(Tactic::Default);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let x = solver.declare_const(Ty::BitVec(8), info);
        let zero = Exp::Eq(Box::new(Exp::Var(x)), Box::new(Exp::Bits64(B64::new(0, 8))));
        assert!(solver.check_sat_with(&zero, info).is_sat().unwrap());
        let tx = solver.start_transaction();
        solver.assert(Exp::Bool(true));
        // 不建立诊断上下文，快路也必须生效。
        let goal = Exp::Eq(Box::new(Exp::Extract(4, 3, Box::new(Exp::Var(x)))), Box::new(Exp::Bits64(B64::new(1, 2))));
        let before = test_query_count();
        assert!(solver.check_sat_with_for_bool(&goal, info).is_sat().unwrap());
        assert_eq!(test_query_count(), before, "满足完整前提的见证应避免SAT搜索");
        assert_eq!(solver.cached_bool_value(&goal).unwrap(), Some(true), "快路必须交付满足目标的真实模型");
        assert!(solver.check_sat_with_for_bool(&Exp::Not(Box::new(goal.clone())), info).is_sat().unwrap());
        assert_eq!(test_query_count(), before, "另一臂也必须保留，前态不能被第一次见证钉死");
        solver.assert(goal.clone());
        assert!(solver.check_sat_with_for_bool(&Exp::Not(Box::new(goal)), info).is_unsat().unwrap());
        assert_eq!(test_query_count(), before + 1, "见证未证明时仍必须由原Z3判UNSAT");
        solver.rollback_transaction(tx);
    }

    #[test]
    fn witness_eval_rechecks_current_assertions_after_symbol_rebinding() {
        if !default_tactic_child("smt::query::tests::witness_eval_rechecks_current_assertions_after_symbol_rebinding") {
            return;
        }
        crate::config::RegionOptions { witness_eval: true, ..Default::default() }.configure();
        configure_tastic(Tactic::Default);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let parent = solver.declare_const(Ty::Bool, info);
        let x = solver.declare_const(Ty::Bool, info);
        let g = solver.declare_const(Ty::Bool, info);
        solver.assert(Exp::Var(parent));
        assert!(solver.check_sat(info).is_sat().unwrap());
        let tx = solver.start_transaction();
        solver.assert(Exp::Var(x));
        let mut progress = crate::executor::stats::region_progress::AttemptGuard::start(
            serde_json::json!({"function":"unit_witness","pc":0}),
        );
        assert!(solver.check_sat_with_for_bool(&Exp::Var(g), info).is_sat().unwrap());
        solver.add(Def::DefineConst(x, Exp::Bool(false)));
        let before = test_query_count();
        assert!(solver.check_sat_with_for_bool(&Exp::Var(g), info).is_unsat().unwrap());
        assert_eq!(test_query_count(), before + 1, "旧见证不能忽略改绑后的假前提");
        solver.rollback_transaction(tx);
        assert!(solver.check_sat(info).is_sat().unwrap());
        assert_eq!(solver.cached_bool_value(&Exp::Var(parent)).unwrap(), Some(true));
        progress.finish("test_complete");
    }

    #[test]
    fn region_prefix_compaction_keeps_full_model_and_bounds_scopes() {
        if !default_tactic_child("smt::query::tests::region_prefix_compaction_keeps_full_model_and_bounds_scopes") {
            return;
        }
        crate::config::RegionOptions { prefix_compact: true, ..Default::default() }.configure();
        configure_tastic(Tactic::Default);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let parent = solver.declare_const(Ty::Bool, info);
        let target = solver.declare_const(Ty::Bool, info);
        let symbols = (0..24).map(|_| solver.declare_const(Ty::Bool, info)).collect::<Vec<_>>();
        solver.assert(Exp::Var(parent));
        let tx = solver.start_transaction();
        for x in &symbols {
            solver.assert(Exp::Var(*x));
        }
        assert!(solver.check_sat_with_for_range(&Exp::Var(target), info).is_sat().unwrap());
        solver.compact_region_query_prefix();
        let pending = solver.transaction_assertions();
        let goal = solver.translate_exp(&Exp::Var(target));
        let mut assumptions = pending.iter().map(|a| a.z3_ast).collect::<Vec<_>>();
        assumptions.push(goal.z3_ast);
        let query = solver.query_solver(&assumptions, true);
        assert!(
            unsafe { Z3_solver_get_num_scopes(context.z3_ctx, query.z3_solver) } <= 1,
            "25条已提交前提应固化为一个基础断言，只给当前目标保留scope"
        );
        drop(query);
        for x in std::iter::once(&parent).chain(symbols.iter()) {
            assert!(solver.check_sat_with_for_range(&Exp::Not(Box::new(Exp::Var(*x))), info).is_unsat().unwrap());
        }
        assert!(solver.check_sat_with_for_range(&Exp::Var(target), info).is_sat().unwrap());
        for x in std::iter::once(&parent).chain(symbols.iter()).chain(std::iter::once(&target)) {
            assert_eq!(solver.cached_bool_value(&Exp::Var(*x)).unwrap(), Some(true));
        }
        let nested = solver.start_transaction();
        solver.assert(Exp::Not(Box::new(Exp::Var(symbols[0]))));
        assert!(solver.check_sat_for_arm(info).unwrap().is_unsat().unwrap());
        solver.rollback_transaction(nested);
        assert!(solver.check_sat(info).is_sat().unwrap());
        solver.rollback_transaction(tx);
        assert!(solver.region_query.is_none());
    }

    #[test]
    fn region_prefix_compaction_preserves_guard_polarity_and_invalidates_changed_base() {
        if !default_tactic_child(
            "smt::query::tests::region_prefix_compaction_preserves_guard_polarity_and_invalidates_changed_base",
        ) {
            return;
        }
        crate::config::RegionOptions { prefix_compact: true, ..Default::default() }.configure();
        configure_tastic(Tactic::Default);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let guard = solver.declare_const(Ty::Bool, info);
        let x = solver.declare_const(Ty::Bool, info);
        let tx = solver.start_transaction();
        solver.start_transaction_with_guard(Some(Exp::Var(guard)));
        solver.assert(Exp::Var(x));
        solver.commit_transaction();
        assert!(solver.check_sat_with_for_range(&Exp::Var(guard), info).is_sat().unwrap());
        solver.compact_region_query_prefix();
        assert!(
            solver.check_sat_with_for_range(&Exp::Not(Box::new(Exp::Var(guard))), info).is_sat().unwrap(),
            "临时臂条件不能固化成跨臂前提"
        );
        let contradiction = Exp::And(Box::new(Exp::Var(guard)), Box::new(Exp::Not(Box::new(Exp::Var(x)))));
        assert!(solver.check_sat_with_for_range(&contradiction, info).is_unsat().unwrap());
        solver.add(Def::DefineConst(x, Exp::Bool(false)));
        assert!(
            solver.check_sat_with_for_range(&Exp::Var(guard), info).is_unsat().unwrap(),
            "改绑导致已固化前缀变化时必须丢弃旧基础并完整重建"
        );
        assert!(solver.check_sat_with_for_range(&Exp::Not(Box::new(Exp::Var(guard))), info).is_sat().unwrap());
        solver.rollback_transaction(tx);
    }

    #[test]
    fn same_context_diagnostic_replay_keeps_buffer_and_leaves_original_untouched() {
        configure_tastic(Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let x = solver.declare_const(Ty::Bool, info);
        let guard = solver.declare_const(Ty::Bool, info);
        solver.assert(Exp::Var(x));
        let tx = solver.start_transaction_with_guard(Some(Exp::Var(guard)));
        solver.assert(Exp::Not(Box::new(Exp::Var(x))));
        let pending = solver.transaction_assertions();
        let assumptions = pending.iter().map(|ast| ast.z3_ast).collect::<Vec<_>>();
        let query = solver.query_solver(&assumptions, false);
        let before = solver.diagnostic_solver_stats(query.z3_solver);
        let replay = solver.diagnostic_fresh_query(query.z3_solver, query.assumptions(&assumptions), 1000);
        assert_eq!(replay["result"], "unsat", "缓冲断言不得漏掉");
        assert_eq!(replay["assertions"], 3, "父断言、活动臂、缓冲断言都必须复制");
        assert_eq!(replay["scopes"], 0, "新solver应在首次check前完整装配且不push");
        let after = solver.diagnostic_solver_stats(query.z3_solver);
        assert_eq!(before["assertions"], after["assertions"]);
        assert_eq!(before["scopes"], after["scopes"]);
        drop(query);
        solver.rollback_transaction(tx);
        assert!(solver.check_sat(info).is_sat().unwrap(), "诊断不得污染原solver");
    }

    #[test]
    fn temporary_guard_changed_constraints_never_restore_caller_witness() {
        configure_tastic(Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let x = solver.declare_const(Ty::Bool, info);
        let y = solver.declare_const(Ty::Bool, info);
        solver.assert(Exp::Var(x));
        solver.assert(Exp::Not(Box::new(Exp::Var(y))));
        assert!(solver.check_sat(info).is_sat().unwrap());
        let tx = solver.start_transaction();
        solver.with_transaction_condition(&Exp::Var(x), |solver| solver.assert(Exp::Var(y)));
        assert_eq!(solver.cached_bool_value(&Exp::Var(x)).unwrap(), None);
        assert!(solver.check_sat(info).is_unsat().unwrap(), "新断言必须生效，不能沿用旧SAT");
        solver.rollback_transaction(tx);
        assert!(solver.check_sat(info).is_sat().unwrap());
        let tx = solver.start_transaction();
        solver.with_transaction_condition(&Exp::Var(x), |solver| {
            solver.add(Def::DefineConst(x, Exp::Bool(false)));
        });
        assert_eq!(solver.cached_bool_value(&Exp::Var(x)).unwrap(), None, "符号改绑即使不新增逻辑断言也必须清见证");
        solver.rollback_transaction(tx);
    }

    #[test]
    fn native_region_snapshot_has_no_scopes_and_preserves_complete_model() {
        if !default_tactic_child("smt::query::tests::native_region_snapshot_has_no_scopes_and_preserves_complete_model")
        {
            return;
        }
        crate::config::RegionOptions { native_snapshot: true, ..Default::default() }.configure();
        configure_tastic(Tactic::Default);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let parent = solver.declare_const(Ty::Bool, info);
        let guard = solver.declare_const(Ty::Bool, info);
        let buffered = solver.declare_const(Ty::Bool, info);
        let target = solver.declare_const(Ty::Bool, info);
        solver.assert(Exp::Var(parent));
        let tx = solver.start_transaction_with_guard(Some(Exp::Var(guard)));
        solver.assert(Exp::Var(buffered));
        let pending = solver.transaction_assertions();
        let goal = solver.translate_exp(&Exp::Var(target));
        let mut assumptions = pending.iter().map(|a| a.z3_ast).collect::<Vec<_>>();
        assumptions.push(goal.z3_ast);
        let query = solver.query_solver(&assumptions, true);
        assert_eq!(
            unsafe { Z3_solver_get_num_scopes(context.z3_ctx, query.z3_solver) },
            0,
            "原生快照必须在第一条check前批量装入全部断言，不能预先进入push路径"
        );
        drop(query);
        assert!(solver.region_query.is_none());
        for symbol in [parent, guard, buffered] {
            assert!(
                solver.check_sat_with_for_range(&Exp::Not(Box::new(Exp::Var(symbol))), info).is_unsat().unwrap(),
                "快照不得丢父前提、缓冲断言或当前臂条件"
            );
        }
        assert!(solver.check_sat_with_for_range(&Exp::Var(target), info).is_sat().unwrap());
        for symbol in [parent, guard, buffered, target] {
            assert_eq!(
                solver.cached_bool_value(&Exp::Var(symbol)).unwrap(),
                Some(true),
                "查询返回的模型必须满足完整前提和目标"
            );
        }
        solver.rollback_transaction(tx);
        assert!(solver.check_sat_with(&Exp::Not(Box::new(Exp::Var(guard))), info).is_sat().unwrap());
    }
}

fn prefix_compaction_enabled() -> bool {
    crate::config::RegionOptions::current().prefix_compact
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    /// 辅助查询的完整前提；实验开启时先放稳定断言，再放当前臂和目标。
    /// 活动guard必须留在可撤销后缀，不能被固化成跨臂事实。
    pub(super) fn region_query_complete(&self, assumptions: &[Z3_ast], stable_order: bool) -> (Vec<Z3_ast>, usize) {
        unsafe {
            let assertions = Z3_solver_get_assertions(self.ctx.z3_ctx, self.z3_solver);
            Z3_ast_vector_inc_ref(self.ctx.z3_ctx, assertions);
            let published = (0..Z3_ast_vector_size(self.ctx.z3_ctx, assertions))
                .map(|i| Z3_ast_vector_get(self.ctx.z3_ctx, assertions, i))
                .collect::<Vec<_>>();
            let mut complete = Vec::with_capacity(published.len() + assumptions.len());
            let stable_len;
            if stable_order {
                let guards = self.transaction_condition_scopes.iter().filter(|scope| scope.is_none()).count();
                assert!(published.len() >= guards, "每个活动guard必须对应一个主solver断言");
                let buffered = self.arm_entry_assumptions.len()
                    + self
                        .transaction_events
                        .iter()
                        .filter(|event| matches!(event, Event::Smt(Def::Assert(_), ..)))
                        .count();
                assert!(assumptions.len() >= buffered, "区域查询不能缺缓冲断言");
                let parent = published.len() - guards;
                complete.extend_from_slice(&published[..parent]);
                complete.extend_from_slice(&assumptions[..buffered]);
                stable_len = complete.len();
                complete.extend_from_slice(&published[parent..]);
                complete.extend_from_slice(&assumptions[buffered..]);
            } else {
                complete.extend_from_slice(&published);
                complete.extend_from_slice(assumptions);
                stable_len = complete.len();
            }
            Z3_ast_vector_dec_ref(self.ctx.z3_ctx, assertions);
            (complete, stable_len)
        }
    }

    /// 只在成功提交的迭代合并边界调用；辅助solver的逻辑前提不变，执行solver/trace不变。
    pub(crate) fn compact_region_query_prefix(&mut self) {
        if !prefix_compaction_enabled() || self.region_query.is_none() {
            return;
        }
        assert!(self.transaction_depth() > 0, "前缀固化只用于活动区域");
        let pending = self.transaction_assertions();
        let assumptions = pending.iter().map(|a| a.z3_ast).collect::<Vec<_>>();
        let (complete, stable_len) = self.region_query_complete(&assumptions, true);
        let config = SMT_CONFIG.get().expect("查询前必须初始化SMT");
        unsafe {
            let before_scopes =
                Z3_solver_get_num_scopes(self.ctx.z3_ctx, self.region_query.as_ref().unwrap().z3_solver);
            let fresh = new_z3_solver(
                self.ctx.z3_ctx,
                config.tactic.as_c_str(),
                self.seed.map(|seed| (config.seed_param, seed)),
            );
            if stable_len > 0 {
                let base =
                    Z3_mk_and(self.ctx.z3_ctx, stable_len.try_into().expect("基础断言数超出Z3接口"), complete.as_ptr());
                Z3_solver_assert(self.ctx.z3_ctx, fresh, base);
            }
            let prefix = complete[..stable_len]
                .iter()
                .map(|a| {
                    Z3_inc_ref(self.ctx.z3_ctx, *a);
                    Ast { ctx: self.ctx, z3_ast: *a }
                })
                .collect();
            self.region_query = Some(RegionQuery { ctx: self.ctx, z3_solver: fresh, prefix, base_len: stable_len });
            if crate::executor::stats::region_progress::enabled() {
                use std::sync::atomic::{AtomicUsize, Ordering};
                static ROWS: AtomicUsize = AtomicUsize::new(0);
                if ROWS.fetch_add(1, Ordering::Relaxed) < 2048 {
                    eprintln!(
                        "{}",
                        serde_json::json!({"kind":"region_prefix_compact","base_assertions":stable_len,"before_scopes":before_scopes,"after_scopes":Z3_solver_get_num_scopes(self.ctx.z3_ctx,fresh)})
                    );
                }
            }
        }
    }
}
