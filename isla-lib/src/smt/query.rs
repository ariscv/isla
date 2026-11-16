//! 查询资源边界：事务内复用完整约束前缀，事务外保留既有策略及显式增量范围。
use super::*;

pub(super) enum QueryPurpose {
    General,
    RangeProof,
    BooleanProof,
}

impl QueryPurpose {
    pub(super) fn requests_snapshot<B: BV>(&self, solver: &Solver<B>, ast: &Ast) -> bool {
        match self {
            Self::General => false,
            Self::RangeProof => true,
            Self::BooleanProof => {
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

/// 完整约束的可重用查询上下文；每条断言占一层，按共同前缀撤销变化后缀。
/// 不修改执行solver的scope／缓冲／迹，模型仍通过既有record_check_result管理。
pub(super) struct RegionQuery<'ctx> {
    ctx: &'ctx Context,
    z3_solver: Z3_solver,
    prefix: Vec<Ast<'ctx>>,
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
        static NATIVE_SNAPSHOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        let native_snapshot = snapshot_requested
            && *NATIVE_SNAPSHOT.get_or_init(|| std::env::var("ISLA_REGION_NATIVE_SNAPSHOT").as_deref() == Ok("1"));
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
                let reusable = self.region_query.get_or_insert_with(|| RegionQuery {
                    ctx: self.ctx,
                    z3_solver: new_z3_solver(
                        self.ctx.z3_ctx,
                        config.tactic.as_c_str(),
                        self.seed.map(|seed| (config.seed_param, seed)),
                    ),
                    prefix: Vec::new(),
                });
                let assertions = Z3_solver_get_assertions(self.ctx.z3_ctx, self.z3_solver);
                Z3_ast_vector_inc_ref(self.ctx.z3_ctx, assertions);
                let mut complete = (0..Z3_ast_vector_size(self.ctx.z3_ctx, assertions))
                    .map(|index| Z3_ast_vector_get(self.ctx.z3_ctx, assertions, index))
                    .collect::<Vec<_>>();
                complete.extend_from_slice(assumptions);
                // 同一Context中AST已驻留，旧前缀持有引用，指针相等就是同一公式。
                let common = reusable.prefix.iter().zip(&complete).take_while(|(old, new)| old.z3_ast == **new).count();
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
                Z3_ast_vector_dec_ref(self.ctx.z3_ctx, assertions);
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
            // 同一Context沿用Config；同一有效种子沿用调用者设置，不重新随机化。
            let z3_solver = new_z3_solver(
                self.ctx.z3_ctx,
                config.tactic.as_c_str(),
                self.seed.map(|seed| (config.seed_param, seed)),
            );
            let query = QuerySolver { ctx: self.ctx, z3_solver, independent };
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
            drop(setup);
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
        std::env::set_var("ISLA_REGION_NATIVE_SNAPSHOT", "1");
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
