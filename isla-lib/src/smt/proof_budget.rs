//! 可选布尔常量证明的确定性资源上限；Unknown沿用原符号定义，不限制路径判定。
use super::*;

pub(super) fn limit() -> Option<u32> {
    static LIMIT: OnceLock<u32> = OnceLock::new();
    let value = *LIMIT.get_or_init(|| {
        std::env::var("ISLA_REGION_BOOL_PROOF_RLIMIT")
            .unwrap_or_else(|_| "0".into())
            .parse()
            .expect("布尔证明rlimit必须为非负32位整数")
    });
    (value != 0).then_some(value)
}
fn profiling() -> bool {
    static PROFILE: OnceLock<bool> = OnceLock::new();
    *PROFILE.get_or_init(|| std::env::var("ISLA_REGION_BOOL_PROOF_PROFILE").as_deref() == Ok("1"))
}
unsafe fn resource_count(ctx: &Context, solver: Z3_solver) -> Option<u64> {
    let stats = Z3_solver_get_statistics(ctx.z3_ctx, solver);
    Z3_stats_inc_ref(ctx.z3_ctx, stats);
    let mut result = None;
    for i in 0..Z3_stats_size(ctx.z3_ctx, stats) {
        let key = CStr::from_ptr(Z3_stats_get_key(ctx.z3_ctx, stats, i)).to_bytes();
        if key == b"rlimit count" || key == b"rlimit-count" {
            assert!(Z3_stats_is_uint(ctx.z3_ctx, stats, i), "Z3资源计数必须为整数");
            result = Some(u64::from(Z3_stats_get_uint_value(ctx.z3_ctx, stats, i)));
            break;
        }
    }
    Z3_stats_dec_ref(ctx.z3_ctx, stats);
    result
}
pub(super) struct Token<'ctx> {
    ctx: &'ctx Context,
    solver: Z3_solver,
    before: u64,
    metadata: serde_json::Value,
    limit: Option<u32>,
    started: Instant,
}
impl<'ctx> Token<'ctx> {
    pub fn begin(ctx: &'ctx Context, solver: Z3_solver, limit: Option<u32>) -> Option<Self> {
        if !profiling() {
            return None;
        }
        let metadata = crate::executor::stats::region_progress::query_metadata()?;
        let before = unsafe { resource_count(ctx, solver).unwrap_or(0) };
        Some(Self { ctx, solver, before, metadata, limit, started: Instant::now() })
    }
    pub fn finish(self, result: Z3_lbool) {
        let milliseconds = self.started.elapsed().as_secs_f64() * 1000.0;
        unsafe {
            let after = resource_count(self.ctx, self.solver);
            let reason = (result == Z3_L_UNDEF).then(|| {
                CStr::from_ptr(Z3_solver_get_reason_unknown(self.ctx.z3_ctx, self.solver))
                    .to_string_lossy()
                    .into_owned()
            });
            eprintln!(
                "{}",
                serde_json::json!({"kind":"region_boolean_proof","query":self.metadata,"limit":self.limit,"result":if result==Z3_L_TRUE{"sat"}else if result==Z3_L_FALSE{"unsat"}else{"unknown"},"reason_unknown":reason,"resource_units":after.map(|n|n.checked_sub(self.before).expect("同Context资源计数不得倒退")),"milliseconds":milliseconds})
            );
        }
    }
}
