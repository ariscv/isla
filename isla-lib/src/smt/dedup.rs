//! 有界查询证明记录。定义不增加约束；断言、改绑及臂条件改变证明版本。
use super::*;

#[derive(Clone, Copy, Default)]
pub(super) struct Knowledge {
    pub version: u64,
    pub constraints: u64,
    pub sat: bool,
    pub both: Option<(Sym, u64)>,
    pub literal: Option<(Sym, bool)>,
}
impl Knowledge {
    pub fn change(&mut self) {
        self.version = self.version.checked_add(1).expect("断言版本溢出");
        self.both = None;
        self.literal = None;
    }
    pub fn constrain(&mut self) {
        self.change();
        self.constraints = self.constraints.checked_add(1).expect("约束版本溢出");
        self.sat = false;
    }
}
pub(super) fn literal(exp: &Exp<Sym>) -> Option<(Sym, bool)> {
    match exp {
        Exp::Var(v) => Some((*v, true)),
        Exp::Not(inner) => match &**inner {
            Exp::Var(v) => Some((*v, false)),
            _ => None,
        },
        _ => None,
    }
}
impl<B: BV> Solver<'_, B> {
    pub(crate) fn region_queries_deferred(&self) -> bool {
        self.deferred_region_queries
    }

    pub(crate) fn check_sat_with_for_branch(
        &mut self,
        exp: &Exp<Sym>,
        info: SourceLoc,
        speculative: bool,
    ) -> Option<SmtResult> {
        let deferred = self.deferred_region_queries && !self.ordinary_region_resume_queries;
        let skip_query = deferred || self.branch_checks_skipped();
        // 延后或关闭查询时也要排除表达式恒假的分支。恒真只说明本条件，
        // 当前路径仍须由原有的出口检查或认证入口判定。
        if skip_query && self.branch_structural_bool(exp) == Some(false) {
            return Some(Unsat);
        }
        if self.finite_domain_enabled() && self.finite_domain_bool(exp) == Some(false) {
            self.note_finite_domain_use("finite_domain_dead_condition", info);
            return Some(Unsat);
        }
        // 这里只回答可行性，不承诺交付模型。普通查询与最终取值仍用原接口。
        if skip_query {
            if deferred {
                self.note_deferred_mandatory_query("branch_feasibility", info, false);
            }
            return None;
        }
        if literal(exp).is_some_and(|(sym, _)| self.knowledge.both == Some((sym, self.knowledge.version))) {
            return Some(Sat);
        }
        if self.transaction_depth() == 0 && self.coi.is_some() && !matches!(self.cached_bool_value(exp), Ok(Some(true)))
        {
            if let Some(result) = self.coi_feasibility(&[], Some(exp), info, "branch_feasibility") {
                if result == Sat {
                    self.knowledge.sat = true;
                    self.knowledge.literal = literal(exp);
                }
                return Some(result);
            }
        }
        Some(if speculative {
            // 分支可行性必须完整判定；仅复用复杂查询策略，不复用可选常量证明预算。
            self.check_sat_with_strategy(exp, info, query::QueryPurpose::BranchFeasibility)
        } else if self.transaction_depth() == 0 {
            self.check_sat_with_strategy(exp, info, query::QueryPurpose::EntryBranchFeasibility)
        } else {
            self.check_sat_with(exp, info)
        })
    }
    pub(crate) fn note_bool_proof(&mut self, sym: Sym, both: bool) {
        self.knowledge.both = both.then_some((sym, self.knowledge.version));
    }
    pub(crate) fn note_jump_results(&mut self, sym: Sym, a: bool, b: bool) {
        if !self.deferred_region_queries && !self.branch_checks_skipped() && a && b {
            self.knowledge.both = Some((sym, self.knowledge.version));
        }
    }
    pub(crate) fn check_sat_for_arm(&mut self, info: SourceLoc) -> Option<SmtResult> {
        if self.deferred_region_queries || !self.validates_candidates() {
            return None;
        }
        // 入口已证可行之后，仅新增定义与纯定义提交不会缩小解集。
        // 真正断言、符号改绑与带约束的嵌套提交均清除此标记。
        if self.knowledge.sat {
            return Some(Sat);
        }
        Some(self.check_sat(info))
    }
    pub(super) fn guard_known_sat(&self, guard: &Exp<Sym>) -> bool {
        literal(guard).is_some_and(|lit| {
            self.knowledge.literal == Some(lit) || self.knowledge.both == Some((lit.0, self.knowledge.version))
        })
    }
}

#[cfg(test)]
mod tests;
