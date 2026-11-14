//! 查询资源边界：default浮点、数值范围及复杂布尔证明做首次普通check，其余查询保留增量学习。
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
    pub(super) fn query_solver(&self, assumptions: &[Z3_ast], snapshot_requested: bool) -> QuerySolver<'ctx> {
        let config = SMT_CONFIG.get().expect("查询前必须初始化SMT");
        // 普通BV深路径保留增量学习。数值范围和复杂布尔证明是反例或可行性查询，真实公式显示
        // 首次普通check显著快于增量假设；仍复制全部前提，不弱化证明。
        let independent = config.tactic == Tactic::Default
            && (snapshot_requested || self.floating_point_seen.get())
            && !self.incremental_checks;
        unsafe {
            if !independent {
                Z3_solver_inc_ref(self.ctx.z3_ctx, self.z3_solver);
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
            query
        }
    }
}
