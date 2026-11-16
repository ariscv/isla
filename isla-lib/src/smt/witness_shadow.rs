//! 独立模型副本的见证求值；只有完整前提为真才证明SAT，不能据此判断UNSAT。
use super::*;

pub(super) struct Bank<'ctx> {
    ctx: &'ctx Context,
    models: Vec<Z3_model>,
}
impl<'ctx> Bank<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        Self { ctx, models: Vec::new() }
    }
    pub fn remember(&mut self, model: Z3_model) {
        if self.models.last() == Some(&model) {
            return;
        }
        unsafe {
            Z3_model_inc_ref(self.ctx.z3_ctx, model);
        }
        self.models.push(model);
        if self.models.len() > 4 {
            let old = self.models.remove(0);
            unsafe {
                Z3_model_dec_ref(self.ctx.z3_ctx, old);
            }
        }
    }
    pub fn evaluate(&self, terms: &[Z3_ast]) -> serde_json::Value {
        self.prove(terms).0
    }
    fn prove(&self, terms: &[Z3_ast]) -> (serde_json::Value, Option<ModelCopy<'ctx>>) {
        let started = Instant::now();
        let mut attempts = 0;
        let mut partial_false = 0;
        let mut unsupported_functions = 0;
        let mut missing = 0;
        unsafe {
            let root = Z3_mk_and(self.ctx.z3_ctx, terms.len().try_into().expect("见证前提过多"), terms.as_ptr());
            Z3_inc_ref(self.ctx.z3_ctx, root);
            let root = Ast { ctx: self.ctx, z3_ast: root };
            for source in self.models.iter().rev() {
                attempts += 1;
                let partial = evaluate_bool(self.ctx, *source, root.z3_ast, false);
                match partial {
                    Some(true) => {
                        Z3_model_inc_ref(self.ctx.z3_ctx, *source);
                        return (
                            serde_json::json!({"sat_claim":true,"method":"retained","attempts":attempts,"pool_size":self.models.len(),"eval_milliseconds":started.elapsed().as_secs_f64()*1000.0}),
                            Some(ModelCopy { ctx: self.ctx, model: *source }),
                        );
                    }
                    Some(false) => {
                        partial_false += 1;
                    }
                    None => (),
                }
                if Z3_model_get_num_funcs(self.ctx.z3_ctx, *source) > 0 {
                    unsupported_functions += 1;
                    continue;
                }
                if partial != Some(false) {
                    for ones in [false, true] {
                        let model = copy_constants(self.ctx, *source);
                        if ones {
                            let Some(declarations) = missing_scalars(self.ctx, *source, root.z3_ast) else {
                                continue;
                            };
                            missing += declarations.len();
                            for decl in declarations {
                                let sort = Z3_get_range(self.ctx.z3_ctx, decl);
                                let mut value = match Z3_get_sort_kind(self.ctx.z3_ctx, sort) {
                                    SortKind::Bool => {
                                        let ast = Z3_mk_true(self.ctx.z3_ctx);
                                        Z3_inc_ref(self.ctx.z3_ctx, ast);
                                        Ast { ctx: self.ctx, z3_ast: ast }
                                    }
                                    SortKind::BV => {
                                        let zero = Z3_mk_numeral(self.ctx.z3_ctx, b"0\0".as_ptr().cast(), sort);
                                        Z3_inc_ref(self.ctx.z3_ctx, zero);
                                        let zero = Ast { ctx: self.ctx, z3_ast: zero };
                                        let ast = Z3_mk_bvnot(self.ctx.z3_ctx, zero.z3_ast);
                                        Z3_inc_ref(self.ctx.z3_ctx, ast);
                                        Ast { ctx: self.ctx, z3_ast: ast }
                                    }
                                    _ => unreachable!("只列出缺失的Bool/BV标量"),
                                };
                                value.simplify();
                                Z3_add_const_interp(self.ctx.z3_ctx, model.model, decl, value.z3_ast);
                            }
                        }
                        attempts += 1;
                        if evaluate_bool(self.ctx, model.model, root.z3_ast, true) == Some(true) {
                            return (
                                serde_json::json!({"sat_claim":true,"method":if ones{"extend_ones"}else{"extend_zero"},"attempts":attempts,"pool_size":self.models.len(),"missing_scalar_assignments":missing,"eval_milliseconds":started.elapsed().as_secs_f64()*1000.0}),
                                Some(model),
                            );
                        }
                    }
                }
                if let Some(target) = terms.last() {
                    if let Some(model) = repair_equality(self.ctx, *source, *target) {
                        attempts += 1;
                        if evaluate_bool(self.ctx, model.model, root.z3_ast, true) == Some(true) {
                            return (
                                serde_json::json!({"sat_claim":true,"method":"repair_eq_field","attempts":attempts,"pool_size":self.models.len(),"eval_milliseconds":started.elapsed().as_secs_f64()*1000.0}),
                                Some(model),
                            );
                        }
                    }
                }
            }
        }
        (
            serde_json::json!({"sat_claim":false,"reason":if self.models.is_empty(){"no_model"}else{"no_valid_witness"},"partial_false":partial_false,"unsupported_functions":unsupported_functions,"missing_scalar_assignments":missing,"attempts":attempts,"pool_size":self.models.len(),"eval_milliseconds":started.elapsed().as_secs_f64()*1000.0}),
            None,
        )
    }
}
impl Drop for Bank<'_> {
    fn drop(&mut self) {
        for model in self.models.drain(..) {
            unsafe {
                Z3_model_dec_ref(self.ctx.z3_ctx, model);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    #[test]
    fn shadow_witness_extends_bv128_in_copy_without_search_or_model_mutation() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let p = solver.declare_const(Ty::Bool, info);
        solver.assert(Exp::Var(p));
        assert!(solver.check_sat(info).is_sat().unwrap());
        let model = solver.stashed_model.unwrap();
        let mut bank = Bank::new(&ctx);
        bank.remember(model);
        let y = solver.declare_const(Ty::BitVec(128), info);
        let y = solver.translate_exp(&Exp::Var(y));
        let parent = solver.translate_exp(&Exp::Var(p));
        unsafe {
            let sort = Z3_mk_bv_sort(ctx.z3_ctx, 128);
            let zero = Z3_mk_numeral(ctx.z3_ctx, b"0\0".as_ptr().cast(), sort);
            Z3_inc_ref(ctx.z3_ctx, zero);
            let one = Z3_mk_numeral(ctx.z3_ctx, b"1\0".as_ptr().cast(), sort);
            Z3_inc_ref(ctx.z3_ctx, one);
            let shift = Z3_mk_numeral(ctx.z3_ctx, b"127\0".as_ptr().cast(), sort);
            Z3_inc_ref(ctx.z3_ctx, shift);
            let negative = Z3_mk_bvslt(ctx.z3_ctx, y.z3_ast, zero);
            Z3_inc_ref(ctx.z3_ctx, negative);
            let shifted = Z3_mk_bvlshr(ctx.z3_ctx, y.z3_ast, shift);
            Z3_inc_ref(ctx.z3_ctx, shifted);
            let high = Z3_mk_eq(ctx.z3_ctx, shifted, one);
            Z3_inc_ref(ctx.z3_ctx, high);
            let decl = Z3_get_app_decl(ctx.z3_ctx, Z3_to_app(ctx.z3_ctx, y.z3_ast));
            assert!(!Z3_model_has_interp(ctx.z3_ctx, model, decl));
            let before = path_smt_stats().calls;
            let result = bank.evaluate(&[parent.z3_ast, negative, high]);
            eprintln!("影子128位补值结果：{result}");
            assert_eq!(result["sat_claim"], true, "全1补值应构成128位负数且逻辑右移127位为1的见证");
            assert_eq!(path_smt_stats().calls, before, "影子求值不能启动SMT搜索");
            assert!(!Z3_model_has_interp(ctx.z3_ctx, model, decl), "不得用completion修改真实模型");
            let fresh = Z3_mk_solver(ctx.z3_ctx);
            Z3_solver_inc_ref(ctx.z3_ctx, fresh);
            for a in [parent.z3_ast, negative, high] {
                Z3_solver_assert(ctx.z3_ctx, fresh, a);
            }
            assert_eq!(Z3_solver_check(ctx.z3_ctx, fresh), Z3_L_TRUE);
            Z3_solver_dec_ref(ctx.z3_ctx, fresh);
            for a in [zero, one, shift, negative, shifted, high] {
                Z3_dec_ref(ctx.z3_ctx, a);
            }
        }
    }
    #[test]
    fn shadow_witness_repairs_interior_bitfield_value_and_rechecks_prefix() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let x = solver.declare_const(Ty::BitVec(8), info);
        let old = Exp::Eq(Box::new(Exp::Var(x)), Box::new(Exp::Bits64(B64::new(0, 8))));
        assert!(solver.check_sat_with(&old, info).is_sat().unwrap());
        let source = solver.stashed_model.unwrap();
        let mut bank = Bank::new(&ctx);
        bank.remember(source);
        let value = solver.translate_exp(&Exp::Var(x));
        let old = solver.translate_exp(&old);
        unsafe {
            let field = owned_ast(&ctx, Z3_mk_extract(ctx.z3_ctx, 4, 3, value.z3_ast));
            let sort = Z3_mk_bv_sort(ctx.z3_ctx, 2);
            let one = owned_ast(&ctx, Z3_mk_numeral(ctx.z3_ctx, b"1\0".as_ptr().cast(), sort));
            let goal = owned_ast(&ctx, Z3_mk_eq(ctx.z3_ctx, field.z3_ast, one.z3_ast));
            let result = bank.evaluate(&[goal.z3_ast]);
            assert_eq!(result["sat_claim"], true, "当前值0和全1都不等于内部位域值1，需要定向试值");
            assert_eq!(bank.evaluate(&[old.z3_ast, goal.z3_ast])["sat_claim"], false, "修补不能破坏旧前提");
            let decl = Z3_get_app_decl(ctx.z3_ctx, Z3_to_app(ctx.z3_ctx, value.z3_ast));
            let unchanged = Z3_model_get_const_interp(ctx.z3_ctx, source, decl);
            assert_eq!(
                CStr::from_ptr(Z3_get_numeral_string(ctx.z3_ctx, unchanged)).to_str().unwrap(),
                "0",
                "不能修改原模型赋值"
            );
        }
    }

    #[test]
    fn shadow_witness_never_claims_sat_for_stale_model_with_contradictory_prefix() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let p = solver.declare_const(Ty::Bool, info);
        solver.assert(Exp::Var(p));
        assert!(solver.check_sat(info).is_sat().unwrap());
        let mut bank = Bank::new(&ctx);
        bank.remember(solver.stashed_model.unwrap());
        let yes = solver.translate_exp(&Exp::Var(p));
        let no = solver.translate_exp(&Exp::Not(Box::new(Exp::Var(p))));
        assert_eq!(bank.evaluate(&[yes.z3_ast, no.z3_ast])["sat_claim"], false, "必须验证全部当前前提，不能只验证目标");
    }
}

pub(super) fn enabled() -> bool {
    shadow_enabled() || fast_enabled()
}
fn fast_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("ISLA_REGION_WITNESS_EVAL").as_deref() == Ok("1"))
}
fn shadow_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("ISLA_REGION_WITNESS_SHADOW").as_deref() == Ok("1"))
}
struct ModelCopy<'ctx> {
    ctx: &'ctx Context,
    model: Z3_model,
}
impl Drop for ModelCopy<'_> {
    fn drop(&mut self) {
        if !self.model.is_null() {
            unsafe {
                Z3_model_dec_ref(self.ctx.z3_ctx, self.model);
            }
        }
    }
}
unsafe fn copy_constants(ctx: &Context, source: Z3_model) -> ModelCopy<'_> {
    let model = Z3_mk_model(ctx.z3_ctx);
    Z3_model_inc_ref(ctx.z3_ctx, model);
    for i in 0..Z3_model_get_num_consts(ctx.z3_ctx, source) {
        let decl = Z3_model_get_const_decl(ctx.z3_ctx, source, i);
        let value = Z3_model_get_const_interp(ctx.z3_ctx, source, decl);
        assert!(!value.is_null(), "已枚举的模型常量必须有解释");
        Z3_add_const_interp(ctx.z3_ctx, model, decl, value);
    }
    ModelCopy { ctx, model }
}
unsafe fn evaluate_bool(ctx: &Context, model: Z3_model, ast: Z3_ast, completion: bool) -> Option<bool> {
    let mut result = std::ptr::null_mut();
    if !Z3_model_eval(ctx.z3_ctx, model, ast, completion, &mut result) {
        return None;
    }
    assert!(!result.is_null(), "模型求值成功必须给出AST");
    match Z3_get_bool_value(ctx.z3_ctx, result) {
        Z3_L_TRUE => Some(true),
        Z3_L_FALSE => Some(false),
        _ => None,
    }
}
unsafe fn missing_scalars(ctx: &Context, model: Z3_model, root: Z3_ast) -> Option<Vec<Z3_func_decl>> {
    let mut pending = vec![root];
    let mut seen = HashSet::new();
    let mut decls = Vec::new();
    while let Some(node) = pending.pop() {
        if !seen.insert(node as usize) {
            continue;
        }
        if seen.len() > 100_000 {
            return None;
        }
        if Z3_get_ast_kind(ctx.z3_ctx, node) != AstKind::App {
            continue;
        }
        let app = Z3_to_app(ctx.z3_ctx, node);
        let n = Z3_get_app_num_args(ctx.z3_ctx, app);
        for i in 0..n {
            pending.push(Z3_get_app_arg(ctx.z3_ctx, app, i));
        }
        if n != 0 {
            continue;
        }
        let decl = Z3_get_app_decl(ctx.z3_ctx, app);
        let name = Z3_get_decl_name(ctx.z3_ctx, decl);
        if Z3_get_symbol_kind(ctx.z3_ctx, name) != SymbolKind::Int || Z3_model_has_interp(ctx.z3_ctx, model, decl) {
            continue;
        }
        if matches!(Z3_get_sort_kind(ctx.z3_ctx, Z3_get_range(ctx.z3_ctx, decl)), SortKind::Bool | SortKind::BV) {
            decls.push(decl);
        }
    }
    Some(decls)
}
pub(super) struct Token {
    metadata: serde_json::Value,
    evaluation: serde_json::Value,
    started: Instant,
}
impl Token {
    pub fn finish(self, result: Z3_lbool) {
        let claim = self.evaluation["sat_claim"].as_bool().unwrap();
        let row = serde_json::json!({"kind":"region_witness_shadow","query":self.metadata,"evaluation":self.evaluation,"native_result":if result==Z3_L_TRUE{"sat"}else if result==Z3_L_FALSE{"unsat"}else{"unknown"},"native_milliseconds":self.started.elapsed().as_secs_f64()*1000.0,"false_sat":claim && result==Z3_L_FALSE});
        eprintln!("{row}");
        assert!(!(claim && result == Z3_L_FALSE), "影子见证判SAT而原Z3判UNSAT，必须停止实验");
    }
}
impl<'ctx, B: BV> Solver<'ctx, B> {
    /// 不使用旧模型的有效标记：每次重新核验真实断言及全部缓冲条件。
    pub(super) fn witness_fast_sat(&mut self, assumptions: &[Z3_ast]) -> bool {
        if !fast_enabled() || self.transaction_depth() == 0 {
            return false;
        }
        let metadata = crate::executor::stats::region_progress::query_metadata();
        unsafe {
            let assertions = Z3_solver_get_assertions(self.ctx.z3_ctx, self.z3_solver);
            Z3_ast_vector_inc_ref(self.ctx.z3_ctx, assertions);
            let mut terms = (0..Z3_ast_vector_size(self.ctx.z3_ctx, assertions))
                .map(|i| Z3_ast_vector_get(self.ctx.z3_ctx, assertions, i))
                .collect::<Vec<_>>();
            terms.extend_from_slice(assumptions);
            let (evaluation, model) = self.shadow_witnesses.prove(&terms);
            Z3_ast_vector_dec_ref(self.ctx.z3_ctx, assertions);
            let Some(mut model) = model else {
                return false;
            };
            self.clear_stashed_model();
            self.stashed_model = Some(model.model);
            self.shadow_witnesses.remember(model.model);
            model.model = std::ptr::null_mut();
            self.knowledge.sat = true;
            self.last_check_sat = true;
            self.asserts_since_check = 0;
            if let Some(metadata) = metadata {
                eprintln!(
                    "{}",
                    serde_json::json!({"kind":"region_witness_fast","query":metadata,"evaluation":evaluation})
                );
            }
            true
        }
    }
    pub(super) fn shadow_probe(&self, solver: Z3_solver, assumptions: &[Z3_ast]) -> Option<Token> {
        if !shadow_enabled() {
            return None;
        }
        let metadata = crate::executor::stats::region_progress::query_metadata()?;
        unsafe {
            let assertions = Z3_solver_get_assertions(self.ctx.z3_ctx, solver);
            Z3_ast_vector_inc_ref(self.ctx.z3_ctx, assertions);
            let mut terms = (0..Z3_ast_vector_size(self.ctx.z3_ctx, assertions))
                .map(|i| Z3_ast_vector_get(self.ctx.z3_ctx, assertions, i))
                .collect::<Vec<_>>();
            terms.extend_from_slice(assumptions);
            let evaluation = self.shadow_witnesses.evaluate(&terms);
            Z3_ast_vector_dec_ref(self.ctx.z3_ctx, assertions);
            Some(Token { metadata, evaluation, started: Instant::now() })
        }
    }
}

unsafe fn owned_ast(ctx: &Context, ast: Z3_ast) -> Ast<'_> {
    Z3_inc_ref(ctx.z3_ctx, ast);
    Ast { ctx, z3_ast: ast }
}

/// 只识别简单BV等式/不等式，不做搜索；试值后仍必须验证完整前提。
unsafe fn repair_equality<'ctx>(ctx: &'ctx Context, source: Z3_model, target: Z3_ast) -> Option<ModelCopy<'ctx>> {
    if evaluate_bool(ctx, source, target, false) == Some(true) {
        return None;
    }
    let mut goal = target;
    let mut positive = true;
    for _ in 0..4 {
        let app = application_named(ctx, goal, "not");
        if let Some(app) = app {
            if Z3_get_app_num_args(ctx.z3_ctx, app) != 1 {
                return None;
            }
            goal = Z3_get_app_arg(ctx.z3_ctx, app, 0);
            positive = !positive;
        } else {
            break;
        }
    }
    let eq = application_named(ctx, goal, "=")?;
    if Z3_get_app_num_args(ctx.z3_ctx, eq) != 2 {
        return None;
    }
    let a = Z3_get_app_arg(ctx.z3_ctx, eq, 0);
    let b = Z3_get_app_arg(ctx.z3_ctx, eq, 1);
    let (field, literal) = if Z3_is_numeral_ast(ctx.z3_ctx, b) {
        (a, b)
    } else if Z3_is_numeral_ast(ctx.z3_ctx, a) {
        (b, a)
    } else {
        return None;
    };
    let (decl, lo, hi) = bitfield(ctx, field, 0)?;
    let sort = Z3_get_range(ctx.z3_ctx, decl);
    let width = Z3_get_bv_sort_size(ctx.z3_ctx, sort);
    let literal_sort = Z3_get_sort(ctx.z3_ctx, literal);
    if Z3_get_sort_kind(ctx.z3_ctx, literal_sort) != SortKind::BV
        || Z3_get_bv_sort_size(ctx.z3_ctx, literal_sort) != hi - lo + 1
    {
        return None;
    }
    let base = Z3_model_get_const_interp(ctx.z3_ctx, source, decl);
    let base = if base.is_null() {
        owned_ast(ctx, Z3_mk_numeral(ctx.z3_ctx, b"0\0".as_ptr().cast(), sort))
    } else {
        owned_ast(ctx, base)
    };
    let mut value = if positive {
        owned_ast(ctx, literal)
    } else {
        let zero = owned_ast(ctx, Z3_mk_numeral(ctx.z3_ctx, b"0\0".as_ptr().cast(), literal_sort));
        if CStr::from_ptr(Z3_get_numeral_string(ctx.z3_ctx, literal)).to_bytes() == b"0" {
            owned_ast(ctx, Z3_mk_bvnot(ctx.z3_ctx, zero.z3_ast))
        } else {
            zero
        }
    };
    if lo > 0 {
        let low = owned_ast(ctx, Z3_mk_extract(ctx.z3_ctx, lo - 1, 0, base.z3_ast));
        value = owned_ast(ctx, Z3_mk_concat(ctx.z3_ctx, value.z3_ast, low.z3_ast));
    }
    if hi + 1 < width {
        let high = owned_ast(ctx, Z3_mk_extract(ctx.z3_ctx, width - 1, hi + 1, base.z3_ast));
        value = owned_ast(ctx, Z3_mk_concat(ctx.z3_ctx, high.z3_ast, value.z3_ast));
    }
    value.simplify();
    if !Z3_is_numeral_ast(ctx.z3_ctx, value.z3_ast) {
        return None;
    }
    let copy = copy_constants(ctx, source);
    Z3_add_const_interp(ctx.z3_ctx, copy.model, decl, value.z3_ast);
    Some(copy)
}
unsafe fn application_named(ctx: &Context, ast: Z3_ast, name: &str) -> Option<Z3_app> {
    if Z3_get_ast_kind(ctx.z3_ctx, ast) != AstKind::App {
        return None;
    }
    let app = Z3_to_app(ctx.z3_ctx, ast);
    let decl = Z3_get_app_decl(ctx.z3_ctx, app);
    let symbol = Z3_get_decl_name(ctx.z3_ctx, decl);
    if Z3_get_symbol_kind(ctx.z3_ctx, symbol) != SymbolKind::String {
        return None;
    }
    (CStr::from_ptr(Z3_get_symbol_string(ctx.z3_ctx, symbol)).to_bytes() == name.as_bytes()).then_some(app)
}
unsafe fn bitfield(ctx: &Context, ast: Z3_ast, depth: usize) -> Option<(Z3_func_decl, u32, u32)> {
    if depth >= 16 || Z3_get_ast_kind(ctx.z3_ctx, ast) != AstKind::App {
        return None;
    }
    let app = Z3_to_app(ctx.z3_ctx, ast);
    let decl = Z3_get_app_decl(ctx.z3_ctx, app);
    if Z3_get_app_num_args(ctx.z3_ctx, app) == 0 {
        let symbol = Z3_get_decl_name(ctx.z3_ctx, decl);
        let sort = Z3_get_range(ctx.z3_ctx, decl);
        if Z3_get_symbol_kind(ctx.z3_ctx, symbol) == SymbolKind::Int
            && Z3_get_sort_kind(ctx.z3_ctx, sort) == SortKind::BV
        {
            return Some((decl, 0, Z3_get_bv_sort_size(ctx.z3_ctx, sort) - 1));
        }
        return None;
    }
    application_named(ctx, ast, "extract")?;
    if Z3_get_decl_num_parameters(ctx.z3_ctx, decl) != 2 || Z3_get_app_num_args(ctx.z3_ctx, app) != 1 {
        return None;
    }
    let hi = u32::try_from(Z3_get_decl_int_parameter(ctx.z3_ctx, decl, 0)).ok()?;
    let lo = u32::try_from(Z3_get_decl_int_parameter(ctx.z3_ctx, decl, 1)).ok()?;
    let (base, start, end) = bitfield(ctx, Z3_get_app_arg(ctx.z3_ctx, app, 0), depth + 1)?;
    if lo > hi || hi > end - start {
        return None;
    }
    Some((base, start.checked_add(lo)?, start.checked_add(hi)?))
}
