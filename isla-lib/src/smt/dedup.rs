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

    /// 推演可嵌套；错误和 panic 均恢复父作用域，不能把延迟状态带入普通执行。
    pub(crate) fn with_deferred_region_queries<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let previous = self.deferred_region_queries;
        self.deferred_region_queries = true;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(self)));
        self.deferred_region_queries = previous;
        match result {
            Ok(value) => value,
            Err(error) => std::panic::resume_unwind(error),
        }
    }

    pub(crate) fn check_sat_with_for_branch(
        &mut self,
        exp: &Exp<Sym>,
        info: SourceLoc,
        speculative: bool,
    ) -> SmtResult {
        // 这里只回答可行性，不承诺交付模型。普通查询与最终取值仍用原接口。
        if self.deferred_region_queries {
            return Unknown;
        }
        if literal(exp).is_some_and(|(sym, _)| self.knowledge.both == Some((sym, self.knowledge.version))) {
            return Sat;
        }
        if speculative {
            self.check_sat_with_for_bool(exp, info)
        } else {
            self.check_sat_with(exp, info)
        }
    }
    pub(crate) fn note_bool_proof(&mut self, sym: Sym, both: bool) {
        self.knowledge.both = both.then_some((sym, self.knowledge.version));
    }
    pub(crate) fn note_jump_results(&mut self, sym: Sym, a: bool, b: bool) {
        if !self.deferred_region_queries && a && b {
            self.knowledge.both = Some((sym, self.knowledge.version));
        }
    }
    pub(crate) fn check_sat_for_arm(&mut self, info: SourceLoc) -> SmtResult {
        // 入口已证可行之后，仅新增定义与纯定义提交不会缩小解集。
        // 真正断言、符号改绑与带约束的嵌套提交均清除此标记。
        if self.knowledge.sat {
            return Sat;
        }
        self.check_sat(info)
    }
    pub(super) fn guard_known_sat(&self, guard: &Exp<Sym>) -> bool {
        literal(guard).is_some_and(|lit| {
            self.knowledge.literal == Some(lit) || self.knowledge.both == Some((lit.0, self.knowledge.version))
        })
    }
}

#[cfg(test)]
mod tests;
