//! 未认证的候选关系构造。保留 Z3 AST 后端，但不把未检查登记为 SAT。
use super::*;
use std::collections::BTreeMap;
use std::sync::Mutex;

static COUNTS: OnceLock<Mutex<BTreeMap<(String, String), u64>>> = OnceLock::new();

pub(super) fn record(kind: &str, info: SourceLoc) {
    let source = serde_json::to_string(&info).unwrap();
    let count = {
        let mut counts = COUNTS.get_or_init(Default::default).lock().unwrap();
        let count = counts.entry((kind.into(), source)).or_default();
        *count += 1;
        *count
    };
    if count <= 4 || count.is_power_of_two() {
        eprintln!(
            "{}",
            serde_json::json!({"kind":"no_smt_event","category":kind,"source":info,"count":count,"certification":"uncertified"})
        );
    }
}

pub fn diagnostics() -> serde_json::Value {
    let counts = COUNTS.get_or_init(Default::default).lock().unwrap();
    serde_json::json!({"kind":"no_smt_summary", "certification":"uncertified",
        "sites":counts.iter().map(|((kind, source), count)| serde_json::json!({"category":kind,"source":serde_json::from_str::<serde_json::Value>(source).unwrap(),"count":count})).collect::<Vec<_>>()})
}

pub fn options() -> SolverOptions {
    SOLVER_OPTIONS.get().copied().unwrap_or_default()
}

impl<B: BV> Solver<'_, B> {
    pub fn no_smt(&self) -> bool {
        self.ctx.solver_options.no_smt
    }

    /// 候选验证返回 None 表示未查询、未认证；Some(Unknown) 仍是真实查询失败。
    /// 复用 SmtResult，不把未判定候选伪装成 Sat，也不放行必需查询。
    pub fn check_candidate_sat(&mut self, info: SourceLoc) -> Option<SmtResult> {
        self.validates_candidates().then(|| self.check_sat(info))
    }

    pub fn check_candidate_sat_with(&mut self, condition: &Exp<Sym>, info: SourceLoc) -> Option<SmtResult> {
        self.validates_candidates().then(|| self.check_sat_with(condition, info))
    }

    pub(crate) fn validates_candidates(&self) -> bool {
        !self.no_smt()
    }

    pub(crate) fn defer_region_checks(&self) -> bool {
        self.no_smt() || self.region_queries_deferred() || crate::config::RegionOptions::current().defer_exit_check
    }

    pub fn no_smt_cannot_continue(&self, reason: &'static str, info: SourceLoc) -> SmtError {
        record(reason, info);
        SmtError::NoSmt { reason, source_loc: info }
    }

    /// 只用表达式本身，不使用路径可满足性或模型；上限递推不会把回绕当成数学加法。
    pub(crate) fn structural_bool(&self, exp: &Exp<Sym>) -> Option<bool> {
        let mut ast = self.translate_exp(exp);
        if let Some(value) = unsafe { structural_comparison(self.ctx, ast.z3_ast) } {
            return Some(value);
        }
        ast.simplify();
        ast.get_bool_value().or_else(|| unsafe { structural_comparison(self.ctx, ast.z3_ast) })
    }

    /// 返回 true 仅表示实验模式已经处理；未证明时明确计数并加入安全前提。
    pub(crate) fn no_smt_safety(&mut self, condition: &Exp<Sym>, info: SourceLoc) -> bool {
        if !self.no_smt() {
            return false;
        }
        if self.structural_bool(condition) == Some(true) {
            record("structurally_proved_checks", info);
        } else {
            record("assumed_safe_checks", info);
            self.assert(condition.clone());
        }
        true
    }

    /// 判定层统一选择立即验证或登记义务；常量 false 仍由调用方的死臂路径处理。
    pub(crate) fn defer_symbolic_assertion(&mut self, condition: Exp<Sym>, info: SourceLoc) -> bool {
        if !self.no_smt() && !self.deferred_region_queries {
            return false;
        }
        if self.no_smt() {
            record("unverified_assertions", info);
        }
        if self.deferred_region_queries {
            self.defer_assertion(condition, info);
        } else {
            // 失败条件定义保留在同一条迹，不能冒充已经证明不可达。
            self.define_const(Exp::Not(Box::new(condition.clone())), info);
            self.assert(condition);
        }
        true
    }

    pub(crate) fn structural_scalar(&mut self, sym: Sym, ty: &crate::ir::Ty<Name>) -> Option<Val<B>> {
        if matches!(ty, crate::ir::Ty::Bool) {
            return self.structural_bool(&Exp::Var(sym)).map(Val::Bool);
        }
        let value = self.structural_i128(sym)?;
        match ty {
            crate::ir::Ty::I128 => Some(Val::I128(value)),
            crate::ir::Ty::I64 => Some(Val::I64(i64::try_from(value).ok()?)),
            crate::ir::Ty::Bits(_) | crate::ir::Ty::AnyBits => {
                let width = self.length(sym)?;
                if width <= 64 {
                    Some(Val::Bits(B::new(value as u64, width)))
                } else if B::MAX_WIDTH >= 128 {
                    Some(Val::Bits(B::from_bytes(&(value as u128).to_be_bytes()).slice(0, width)?))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub(crate) fn structural_i128(&mut self, sym: Sym) -> Option<i128> {
        let mut ast = self.translate_exp(&Exp::Var(sym));
        ast.simplify();
        let bits = unsafe { numeral(self.ctx, ast.z3_ast)? };
        let width = self.length(sym)?;
        if width == 128 {
            Some(bits as i128)
        } else {
            Some(((bits << (128 - width)) as i128) >> (128 - width))
        }
    }
}

unsafe fn numeral(ctx: &Context, ast: Z3_ast) -> Option<u128> {
    if !Z3_is_numeral_ast(ctx.z3_ctx, ast) {
        return None;
    }
    let sort = Z3_get_sort(ctx.z3_ctx, ast);
    if Z3_get_sort_kind(ctx.z3_ctx, sort) != SortKind::BV {
        return None;
    }
    let width = Z3_get_bv_sort_size(ctx.z3_ctx, sort);
    if width > 128 {
        return None;
    }
    let mut value = 0;
    if width <= 64 {
        return Z3_get_numeral_uint64(ctx.z3_ctx, ast, &mut value).then_some(value as u128);
    }
    let text = CStr::from_ptr(Z3_get_numeral_string(ctx.z3_ctx, ast)).to_str().ok()?;
    text.parse().ok()
}

unsafe fn unsigned_upper(ctx: &Context, ast: Z3_ast, budget: &mut usize) -> Option<u128> {
    if *budget == 0 {
        return None;
    }
    *budget -= 1;
    if let Some(value) = numeral(ctx, ast) {
        return Some(value);
    }
    let sort = Z3_get_sort(ctx.z3_ctx, ast);
    if Z3_get_sort_kind(ctx.z3_ctx, sort) != SortKind::BV {
        return None;
    }
    let width = Z3_get_bv_sort_size(ctx.z3_ctx, sort);
    if width > 128 {
        return None;
    }
    let full = if width == 128 { u128::MAX } else { (1u128 << width) - 1 };
    if Z3_get_ast_kind(ctx.z3_ctx, ast) != AstKind::App {
        return Some(full);
    }
    let app = Z3_to_app(ctx.z3_ctx, ast);
    let decl = Z3_get_app_decl(ctx.z3_ctx, app);
    let arg = |i| Z3_get_app_arg(ctx.z3_ctx, app, i);
    match Z3_get_decl_kind(ctx.z3_ctx, decl) {
        DeclKind::ITE => Some(unsigned_upper(ctx, arg(1), budget)?.max(unsigned_upper(ctx, arg(2), budget)?)),
        DeclKind::ZERO_EXT => unsigned_upper(ctx, arg(0), budget),
        DeclKind::EXTRACT => {
            let low = u32::try_from(Z3_get_decl_int_parameter(ctx.z3_ctx, decl, 1)).ok()?;
            Some((unsigned_upper(ctx, arg(0), budget)? >> low).min(full))
        }
        DeclKind::BAND => Some(unsigned_upper(ctx, arg(0), budget)?.min(unsigned_upper(ctx, arg(1), budget)?)),
        DeclKind::CONCAT => {
            let mut bound = 0u128;
            for i in 0..Z3_get_app_num_args(ctx.z3_ctx, app) {
                let part = arg(i);
                let part_width = Z3_get_bv_sort_size(ctx.z3_ctx, Z3_get_sort(ctx.z3_ctx, part));
                let next = unsigned_upper(ctx, part, budget)?;
                if part_width == 128 {
                    if bound != 0 {
                        return None;
                    }
                    bound = next;
                } else {
                    bound = bound.checked_shl(part_width)? | next;
                }
            }
            Some(bound.min(full))
        }
        DeclKind::BADD => {
            let mut bound = 0u128;
            for i in 0..Z3_get_app_num_args(ctx.z3_ctx, app) {
                let next = unsigned_upper(ctx, arg(i), budget)?;
                let Some(sum) = bound.checked_add(next).filter(|sum| *sum <= full) else {
                    return Some(full);
                };
                bound = sum;
            }
            Some(bound)
        }
        _ => Some(full),
    }
}

unsafe fn structural_comparison(ctx: &Context, ast: Z3_ast) -> Option<bool> {
    if Z3_get_ast_kind(ctx.z3_ctx, ast) != AstKind::App {
        return None;
    }
    let app = Z3_to_app(ctx.z3_ctx, ast);
    let decl = Z3_get_app_decl(ctx.z3_ctx, app);
    if Z3_get_app_num_args(ctx.z3_ctx, app) != 2 {
        return None;
    }
    let kind = Z3_get_decl_kind(ctx.z3_ctx, decl);
    if !matches!(kind, DeclKind::ULT | DeclKind::ULEQ) {
        return None;
    }
    let left = Z3_get_app_arg(ctx.z3_ctx, app, 0);
    let right = Z3_get_app_arg(ctx.z3_ctx, app, 1);
    let mut budget = 256;
    let bound = unsigned_upper(ctx, left, &mut budget)?;
    let limit = numeral(ctx, right)?;
    match kind {
        DeclKind::ULT if bound < limit => Some(true),
        DeclKind::ULEQ if bound <= limit => Some(true),
        _ => None,
    }
}
