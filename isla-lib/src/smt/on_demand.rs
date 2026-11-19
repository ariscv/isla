//! 真实查询才创建原生 solver。定义 AST、保存点和执行迹沿用共同实现。
use super::*;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::OnceLock;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SolverMode {
    #[default]
    Incremental,
    OnDemand,
}

impl std::str::FromStr for SolverMode {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "incremental" => Ok(Self::Incremental),
            "on_demand" => Ok(Self::OnDemand),
            _ => Err("solver_mode 必须是 incremental 或 on_demand".into()),
        }
    }
}

static MODE: OnceLock<SolverMode> = OnceLock::new();

impl SolverMode {
    pub(crate) fn configure(mode: Self) {
        assert_eq!(*MODE.get_or_init(|| mode), mode, "不能更改已初始化的求解器模式");
    }

    pub(crate) fn current() -> Self {
        #[cfg(test)]
        {
            // libtest 的保留筛选标记只在库测试中生效。
            static TEST_ON_DEMAND: OnceLock<bool> = OnceLock::new();
            if cfg!(feature = "test-on-demand")
                || *TEST_ON_DEMAND
                    .get_or_init(|| std::env::args().any(|arg| arg == "--skip=isla_solver_mode_on_demand"))
            {
                return Self::OnDemand;
            }
        }
        MODE.get().copied().unwrap_or_default()
    }
}

struct Cached<'ctx> {
    terms: Vec<Ast<'ctx>>,
    model: Option<Z3_model>,
    ctx: &'ctx Context,
}

impl Drop for Cached<'_> {
    fn drop(&mut self) {
        if let Some(model) = self.model {
            unsafe { Z3_model_dec_ref(self.ctx.z3_ctx, model) };
        }
    }
}

#[derive(Default)]
pub(super) struct State<'ctx> {
    pub(super) published: Vec<Ast<'ctx>>,
    cache: VecDeque<Cached<'ctx>>,
}

static LOOKUPS: AtomicU64 = AtomicU64::new(0);
static HITS: AtomicU64 = AtomicU64::new(0);

pub(crate) fn metrics() -> serde_json::Value {
    serde_json::json!({
        "cache_lookups": LOOKUPS.load(Ordering::Relaxed),
        "cache_hits": HITS.load(Ordering::Relaxed),
    })
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    /// 只缓存同一 Context 中的完整约束集，持有 AST 引用防止指针复用。
    pub(super) fn on_demand_key(&self, assumptions: &[Z3_ast]) -> Option<Vec<Ast<'ctx>>> {
        self.on_demand.as_ref()?;
        Some(self.with_assertion_terms(assumptions, |terms| {
            let mut key = terms.to_vec();
            key.sort_unstable_by_key(|term| *term as usize);
            key.dedup();
            key.into_iter()
                .map(|z3_ast| {
                    unsafe { Z3_inc_ref(self.ctx.z3_ctx, z3_ast) };
                    Ast { ctx: self.ctx, z3_ast }
                })
                .collect()
        }))
    }

    pub(super) fn on_demand_lookup(&mut self, key: Option<&[Ast<'ctx>]>) -> Option<SmtResult> {
        let key = key?;
        let track = crate::executor::stats::region_progress::enabled();
        if track {
            LOOKUPS.fetch_add(1, Ordering::Relaxed);
        }
        let state = self.on_demand.as_mut().unwrap();
        let index = state.cache.iter().position(|entry| {
            entry.terms.len() == key.len()
                && entry.terms.iter().zip(key).all(|(left, right)| left.z3_ast == right.z3_ast)
        })?;
        let entry = state.cache.remove(index).unwrap();
        if track {
            HITS.fetch_add(1, Ordering::Relaxed);
        }
        self.last_check_sat = entry.model.is_some();
        self.asserts_since_check = 0;
        if let Some(model) = entry.model {
            unsafe { Z3_model_inc_ref(self.ctx.z3_ctx, model) };
            self.clear_stashed_model();
            self.stashed_model = Some(model);
            self.knowledge.sat = true;
            if witness_shadow::enabled() {
                self.shadow_witnesses.remember(model);
            }
        }
        let result = if self.last_check_sat { Sat } else { Unsat };
        self.on_demand.as_mut().unwrap().cache.push_back(entry);
        Some(result)
    }

    pub(super) fn on_demand_remember(
        &mut self,
        key: Option<Vec<Ast<'ctx>>>,
        result: &SmtResult,
        fresh_model: Option<Z3_model>,
    ) {
        let Some(terms) = key else { return };
        let model = match result {
            Sat => {
                let Some(model) = fresh_model else { return };
                unsafe { Z3_model_inc_ref(self.ctx.z3_ctx, model) };
                Some(model)
            }
            Unsat => None,
            Unknown | Error(_) => return,
        };
        let state = self.on_demand.as_mut().unwrap();
        if state.cache.len() == 16 {
            state.cache.pop_front();
        }
        state.cache.push_back(Cached { terms, model, ctx: self.ctx });
    }
}
