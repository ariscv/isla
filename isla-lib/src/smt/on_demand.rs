//! 按需求解：保留定义AST和持久执行迹，真实check才创建无scope临时solver。
//! 缓存只在同一Context内按完整AST集合复用，不缓存Unknown和超时。
use super::*;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::OnceLock;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum SolverMode {
    #[default]
    Incremental,
    OnDemand,
}
impl std::str::FromStr for SolverMode {
    type Err = String;
    fn from_str(value: &str) -> Result<Self, String> {
        match value {
            "incremental" => Ok(Self::Incremental),
            "on_demand" => Ok(Self::OnDemand),
            _ => Err("solver_mode 必须是 incremental 或 on_demand".into()),
        }
    }
}
static MODE: OnceLock<SolverMode> = OnceLock::new();
impl SolverMode {
    pub fn configure(mode: Self) {
        assert_eq!(*MODE.get_or_init(|| mode), mode, "不能更改已初始化的求解器模式");
    }
    pub fn current() -> Self {
        MODE.get().copied().unwrap_or_default()
    }
}

struct Assertion<'ctx> {
    ast: Ast<'ctx>,
    previous: Option<Arc<Assertion<'ctx>>>,
}
impl Drop for Assertion<'_> {
    fn drop(&mut self) {
        // 长路径释放不能依赖宿主递归栈；共享前缀由最后持有者释放。
        let mut tail = self.previous.take();
        while let Some(node) = tail {
            match Arc::try_unwrap(node) {
                Ok(mut node) => tail = node.previous.take(),
                Err(_) => break,
            }
        }
    }
}
struct Cached<'ctx> {
    terms: Vec<Ast<'ctx>>,
    sat: bool,
    model: Option<Z3_model>,
    ctx: &'ctx Context,
}
impl Drop for Cached<'_> {
    fn drop(&mut self) {
        if let Some(model) = self.model.take() {
            unsafe { Z3_model_dec_ref(self.ctx.z3_ctx, model) };
        }
    }
}
pub(super) struct State<'ctx> {
    published: Option<Arc<Assertion<'ctx>>>,
    cache: VecDeque<Cached<'ctx>>,
    pub(super) checks: u64,
    pub(super) hits: u64,
}
impl<'ctx> State<'ctx> {
    pub(super) fn new() -> Self {
        Self { published: None, cache: VecDeque::new(), checks: 0, hits: 0 }
    }
    pub(super) fn publish(&mut self, ast: Ast<'ctx>) {
        self.published = Some(Arc::new(Assertion { ast, previous: self.published.take() }));
    }
}

static LOOKUPS: AtomicU64 = AtomicU64::new(0);
static HITS: AtomicU64 = AtomicU64::new(0);
static BUILDS: AtomicU64 = AtomicU64::new(0);
static BUILD_NS: AtomicU64 = AtomicU64::new(0);
static CHECKS: AtomicU64 = AtomicU64::new(0);
static CHECK_NS: AtomicU64 = AtomicU64::new(0);
static PUSHES: AtomicU64 = AtomicU64::new(0);
static PUSH_NS: AtomicU64 = AtomicU64::new(0);
static LAST_REPORT: AtomicU64 = AtomicU64::new(0);
fn diagnostic_enabled() -> bool {
    crate::config::RegionOptions::current().progress
}
fn periodic_report() {
    if !diagnostic_enabled() {
        return;
    }
    static START: OnceLock<Instant> = OnceLock::new();
    let second = START.get_or_init(Instant::now).elapsed().as_secs();
    let old = LAST_REPORT.load(Ordering::Relaxed);
    if second >= old + 2 && LAST_REPORT.compare_exchange(old, second, Ordering::Relaxed, Ordering::Relaxed).is_ok() {
        report();
    }
}
pub fn report() {
    if !diagnostic_enabled() {
        return;
    }
    eprintln!(
        "{}",
        serde_json::json!({"kind":"solver_mode_stats","mode":format!("{:?}",SolverMode::current()),
        "lookups":LOOKUPS.load(Ordering::Relaxed),"cache_hits":HITS.load(Ordering::Relaxed),
        "builds":BUILDS.load(Ordering::Relaxed),"build_ns":BUILD_NS.load(Ordering::Relaxed),
        "checks":CHECKS.load(Ordering::Relaxed),"check_ns":CHECK_NS.load(Ordering::Relaxed),
        "pushes":PUSHES.load(Ordering::Relaxed),"push_ns":PUSH_NS.load(Ordering::Relaxed)})
    );
}
pub(super) unsafe fn native_push(ctx: Z3_context, solver: Z3_solver) {
    if !diagnostic_enabled() {
        Z3_solver_push(ctx, solver);
        return;
    }
    let start = Instant::now();
    Z3_solver_push(ctx, solver);
    PUSHES.fetch_add(1, Ordering::Relaxed);
    PUSH_NS.fetch_add(start.elapsed().as_nanos() as u64, Ordering::Relaxed);
    periodic_report();
}
pub(super) struct CheckTimer(Option<Instant>);
impl CheckTimer {
    pub(super) fn new() -> Self {
        Self(diagnostic_enabled().then(Instant::now))
    }
}
impl Drop for CheckTimer {
    fn drop(&mut self) {
        if let Some(start) = self.0 {
            record_native_check(start.elapsed());
        }
    }
}
fn record_native_check(elapsed: Duration) {
    if !diagnostic_enabled() {
        return;
    }
    CHECKS.fetch_add(1, Ordering::Relaxed);
    CHECK_NS.fetch_add(elapsed.as_nanos() as u64, Ordering::Relaxed);
    periodic_report();
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    pub(super) fn on_demand_check(
        &mut self,
        goal: Option<&Exp<Sym>>,
        info: SourceLoc,
        deadline: Option<Duration>,
        limit: Option<u32>,
    ) -> SmtResult {
        let started = Instant::now();
        let setup = WorkTimer::start(WorkKind::QuerySetup);
        let mut terms = self.transaction_assertions();
        let mut node = self.on_demand.as_ref().unwrap().published.as_deref();
        while let Some(assertion) = node {
            terms.push(assertion.ast.clone());
            node = assertion.previous.as_deref();
        }
        if let Some(exp) = goal {
            terms.push(self.translate_exp(exp));
        }
        // Z3同Context的AST已hash-cons；保留引用，使指针在缓存存活期内不会复用。
        terms.sort_unstable_by_key(|ast| ast.z3_ast as usize);
        terms.dedup_by_key(|ast| ast.z3_ast as usize);
        LOOKUPS.fetch_add(1, Ordering::Relaxed);
        let state = self.on_demand.as_mut().unwrap();
        let hit = state.cache.iter().position(|entry| {
            entry.terms.len() == terms.len() && entry.terms.iter().zip(&terms).all(|(a, b)| a.z3_ast == b.z3_ast)
        });
        if let Some(index) = hit {
            let entry = state.cache.remove(index).unwrap();
            state.hits += 1;
            HITS.fetch_add(1, Ordering::Relaxed);
            if let Some(model) = entry.model {
                unsafe { Z3_model_inc_ref(self.ctx.z3_ctx, model) };
                self.clear_stashed_model();
                self.stashed_model = Some(model);
                self.knowledge.sat = true;
            }
            let result = if entry.sat { Sat } else { Unsat };
            self.last_check_sat = entry.sat;
            self.asserts_since_check = 0;
            self.on_demand.as_mut().unwrap().cache.push_back(entry);
            drop(setup);
            periodic_report();
            return result;
        }
        state.checks += 1;
        let config = SMT_CONFIG.get().unwrap();
        let build_started = Instant::now();
        let query = unsafe {
            let native =
                new_z3_solver(self.ctx.z3_ctx, config.tactic.as_c_str(), self.seed.map(|s| (config.seed_param, s)));
            for ast in &terms {
                Z3_solver_assert(self.ctx.z3_ctx, native, ast.z3_ast);
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
                Z3_solver_set_params(self.ctx.z3_ctx, native, params);
                Z3_params_dec_ref(self.ctx.z3_ctx, params);
            }
            query::QuerySolver::owned(self.ctx, native)
        };
        BUILDS.fetch_add(1, Ordering::Relaxed);
        BUILD_NS.fetch_add(build_started.elapsed().as_nanos() as u64, Ordering::Relaxed);
        drop(setup);
        let budget = proof_budget::Token::begin(self.ctx, query.z3_solver, limit);
        let slow = self.slow_query_begin(query.z3_solver);
        let result = match deadline {
            Some(deadline) => timeout_Z3_solver_check_deadline(self.ctx.z3_ctx, query.z3_solver, &[], info, deadline),
            None => timeout_Z3_solver_check(self.ctx.z3_ctx, query.z3_solver, &[], info),
        };
        let native = match result {
            Ok(native) => native,
            Err(Z3TimeoutError::Interrupted) => {
                if let Some(budget) = budget {
                    budget.finish(Z3_L_UNDEF);
                }
                self.last_check_sat = false;
                self.asserts_since_check = 0;
                let request = goal.map_or(SmtDumpRequest::CheckSat, |exp| SmtDumpRequest::CheckSatWith(exp.clone()));
                let dump = timeout_dump_from_checkpoint(self.checkpoint_snapshot(), request);
                return Error(z3_timeout_error(SmtOperation::CheckSat, info, started.elapsed(), dump));
            }
        };
        if let Some(budget) = budget {
            budget.finish(native);
        }
        self.slow_query_finish(slow, query.z3_solver, goal, info, native);
        let result = if native == Z3_L_TRUE {
            Sat
        } else if native == Z3_L_FALSE {
            Unsat
        } else {
            Unknown
        };
        self.record_check_result(&result, query.z3_solver);
        if matches!(result, Sat | Unsat) {
            let model = if matches!(result, Sat) { self.stashed_model } else { None };
            if let Some(model) = model {
                unsafe { Z3_model_inc_ref(self.ctx.z3_ctx, model) };
            }
            let state = self.on_demand.as_mut().unwrap();
            if state.cache.len() == 16 {
                state.cache.pop_front();
            }
            state.cache.push_back(Cached { terms, sat: matches!(result, Sat), model, ctx: self.ctx });
        }
        periodic_report();
        result
    }

    /// 显式枚举作用域在新模式中逐次按需查询；不创建跨查询native栈。
    pub(super) fn with_on_demand_checks<T>(&mut self, query: impl FnOnce(&mut Self) -> T) -> T {
        let model = self.stashed_model.take();
        let last = self.last_check_sat;
        let asserts = self.asserts_since_check;
        let depth = self.transaction_depth();
        let events = self.transaction_events.len();
        self.last_check_sat = false;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| query(self)));
        self.clear_stashed_model();
        self.stashed_model = model;
        self.last_check_sat = last;
        self.asserts_since_check = asserts;
        assert_eq!(self.transaction_depth(), depth, "按需枚举不得遗留保存点");
        assert_eq!(self.transaction_events.len(), events, "按需枚举不得修改执行迹");
        match result {
            Ok(value) => value,
            Err(panic) => std::panic::resume_unwind(panic),
        }
    }
}
