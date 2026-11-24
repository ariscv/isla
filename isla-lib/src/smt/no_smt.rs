//! 未认证的候选关系构造。保留 Z3 AST 后端，但不把未检查登记为 SAT。
use super::*;
use std::collections::BTreeMap;
use std::sync::Mutex;

static COUNTS: OnceLock<Mutex<BTreeMap<(String, String), u64>>> = OnceLock::new();

pub(crate) fn record(kind: &str, info: SourceLoc) {
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

    /// 候选验证返回 None 表示未查询、未认证；Some 保留实际判定或未完成查询的原因。
    /// 复用 SmtResult，不把未判定候选伪装成 Sat，也不放行必需查询。
    pub fn check_candidate_sat(&mut self, info: SourceLoc) -> Option<SmtResult> {
        self.validates_candidates().then(|| self.check_sat(info))
    }

    pub fn check_candidate_sat_with(&mut self, condition: &Exp<Sym>, info: SourceLoc) -> Option<SmtResult> {
        self.validates_candidates().then(|| self.check_sat_with(condition, info))
    }

    pub(crate) fn check_region_prefix_candidate(&mut self, guard: &Exp<Sym>, info: SourceLoc) -> SmtResult {
        self.with_region_resume_queries(|solver| {
            solver.check_candidate_sat_with(guard, info).expect("区域前缀必须经过求解器认证")
        })
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

    /// 先化简表达式，再用已启用的有限域前缀证明蕴含，不查询 SMT 或读取模型。
    pub(crate) fn structural_bool(&self, exp: &Exp<Sym>) -> Option<bool> {
        self.branch_structural_bool(exp).or_else(|| self.finite_domain_bool(exp))
    }

    pub(super) fn branch_structural_bool(&self, exp: &Exp<Sym>) -> Option<bool> {
        let mut value = self.translate_exp(exp);
        if dedup::literal(exp).is_some() && self.ctx.has_unbounded_rewriting() && value.is_open_branch_atom() {
            return None;
        }
        value.structural_bool()
    }

    /// 结构范围只依赖位宽与定义，有无 SMT 都使用同一判定。
    pub(crate) fn structural_fits_i64(&self, sym: Sym) -> bool {
        let value = self.translate_exp(&Exp::Var(sym));
        unsafe { bitvector_range(self.ctx, value.z3_ast) }
            .is_some_and(|range| i64::try_from(range.min).is_ok() && i64::try_from(range.max).is_ok())
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

// 每个 Context 独占表。键区分原生默认参数与 Isla 的三项 BV 参数。
#[derive(Default)]
pub(super) struct StructuralBoolCache {
    entries: ahash::AHashMap<(Z3_ast, bool), (Option<bool>, Z3_ast)>,
}

impl StructuralBoolCache {
    pub(super) fn clear(&mut self, z3: Z3_context) {
        for ((input, _), (_, output)) in self.entries.drain() {
            unsafe {
                Z3_dec_ref(z3, input);
                Z3_dec_ref(z3, output);
            }
        }
    }
}

impl Ast<'_> {
    pub(super) fn structural_bool(&mut self) -> Option<bool> {
        #[cfg(test)]
        finite_domain::STRUCTURAL_BOOLS.set(finite_domain::STRUCTURAL_BOOLS.get() + 1);
        if !self.ctx.has_unbounded_rewriting() {
            return self.structural_bool_uncached();
        }

        let default_params = SMT_CONFIG.get().is_some_and(|config| config.tactic == Tactic::Default);
        let key = (self.z3_ast, default_params);
        let z3 = self.ctx.z3_ctx;
        let mut cache = self.ctx.structural_bools.borrow_mut();
        if let Some(&(truth, residual)) = cache.entries.get(&key) {
            unsafe {
                Z3_inc_ref(z3, residual);
                Z3_dec_ref(z3, self.z3_ast);
            }
            self.z3_ast = residual;
            return truth;
        }

        // 化简可能释放输入。先保活原 AST；失败退出时也由 Ast 释放。
        let input = self.clone();
        let truth = self.structural_bool_uncached();
        if self.ctx.has_unbounded_rewriting() {
            // 每个 Context 只保留近期精确输入，限制键和值最多持有 32,768 个引用。
            // 一个长根可产生大量唯一残余，不能把它们保留至整个 Context 退出。
            const MAX_ENTRIES: usize = 16_384;
            if cache.entries.len() >= MAX_ENTRIES {
                cache.clear(z3);
            }
            unsafe { Z3_inc_ref(z3, self.z3_ast) };
            std::mem::forget(input);
            cache.entries.insert(key, (truth, self.z3_ast));
        }
        truth
    }

    pub(super) fn structural_bool_uncached(&mut self) -> Option<bool> {
        if let Some(value) = unsafe { structural_comparison(self.ctx, self.z3_ast) } {
            return Some(value);
        }
        if self.ctx.has_unbounded_rewriting() {
            if let Some(value) = self.get_bool_value() {
                return Some(value);
            }
            if let Some(value) = self.boolean_constant_rewrite() {
                *self = Ast::mk_bool(self.ctx, value);
                return Some(value);
            }
        }
        // 原生 Z3 在超时、步数耗尽或中断时报告失败。此处只有成功返回才入表。
        self.simplify();
        self.get_bool_value().or_else(|| unsafe { structural_comparison(self.ctx, self.z3_ast) })
    }

    #[cfg(test)]
    pub(super) fn reference_structural_bool(&mut self) -> Option<bool> {
        if let Some(value) = unsafe { structural_comparison(self.ctx, self.z3_ast) } {
            return Some(value);
        }
        self.simplify_native();
        self.get_bool_value().or_else(|| unsafe { structural_comparison(self.ctx, self.z3_ast) })
    }

    fn boolean_constant_rewrite(&self) -> Option<bool> {
        // 这些规则的原生残余必为 true/false。即使另一侧含符号值也可判定。
        unsafe {
            let z3 = self.ctx.z3_ctx;
            if Z3_get_ast_kind(z3, self.z3_ast) != AstKind::App {
                return None;
            }
            let app = Z3_to_app(z3, self.z3_ast);
            let kind = rewrite::decl_kind_raw(z3, Z3_get_app_decl(z3, app));
            let arg = |i| Z3_get_app_arg(z3, app, i);
            let truth = |i| match Z3_get_bool_value(z3, arg(i)) {
                Z3_L_TRUE => Some(true),
                Z3_L_FALSE => Some(false),
                _ => None,
            };
            if kind == DeclKind::EQ as u32 {
                return (arg(0) == arg(1)).then_some(true);
            }
            if kind == DeclKind::NOT as u32 {
                return truth(0).map(|value| !value);
            }
            if kind == DeclKind::AND as u32 || kind == DeclKind::OR as u32 {
                let absorbing = kind == DeclKind::OR as u32;
                return (0..Z3_get_app_num_args(z3, app)).any(|i| truth(i) == Some(absorbing)).then_some(absorbing);
            }
            None
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

#[derive(Clone, Copy)]
struct BitvectorRange {
    min: i128,
    max: i128,
    unsigned_upper: u128,
}

impl BitvectorRange {
    fn from_upper(upper: u128, mask: u128) -> Self {
        let signed_max = (mask >> 1) as i128;
        Self {
            min: if upper <= signed_max as u128 { 0 } else { !signed_max },
            max: upper.min(signed_max as u128) as i128,
            unsigned_upper: upper,
        }
    }

    fn intersect_signed(self, min: i128, max: i128, mask: u128) -> Self {
        let min = self.min.max(min);
        let max = self.max.min(max);
        let upper = if min < 0 && max >= 0 { mask } else { (max as u128) & mask };
        Self { min, max, unsigned_upper: self.unsigned_upper.min(upper) }
    }
}

unsafe fn bv_width(z3: Z3_context, ast: Z3_ast) -> Option<u32> {
    let sort = Z3_get_sort(z3, ast);
    (Z3_get_sort_kind(z3, sort) == SortKind::BV).then(|| Z3_get_bv_sort_size(z3, sort))
}

unsafe fn bv_application(z3: Z3_context, ast: Z3_ast) -> Option<(Z3_app, Z3_func_decl)> {
    (Z3_get_ast_kind(z3, ast) == AstKind::App).then(|| {
        let app = Z3_to_app(z3, ast);
        (app, Z3_get_app_decl(z3, app))
    })
}

unsafe fn bitvector_range(ctx: &Context, root: Z3_ast) -> Option<BitvectorRange> {
    let z3 = ctx.z3_ctx;
    let mut bounds = HashMap::new();
    let mut pending = vec![(root, false)];
    // Z3 在本次查询持有整棵 AST；共享子式可直接用 AST 指针为键。
    while let Some((ast, children_ready)) = pending.pop() {
        if bounds.contains_key(&ast) {
            continue;
        }
        let Some(width) = bv_width(z3, ast).filter(|&width| width <= 128) else {
            bounds.insert(ast, None);
            continue;
        };
        let mask = u128::MAX >> (128 - width);
        let from_upper = |upper| BitvectorRange::from_upper(upper, mask);
        let full = from_upper(mask);
        let with_signed = |(min, max)| full.intersect_signed(min, max, mask);
        if let Some(value) = numeral(ctx, ast) {
            let signed = ((value << (128 - width)) as i128) >> (128 - width);
            bounds.insert(ast, Some(with_signed((signed, signed))));
            continue;
        }
        let Some((app, decl)) = bv_application(z3, ast) else {
            bounds.insert(ast, Some(full));
            continue;
        };
        let kind = rewrite::decl_kind_raw(z3, decl);
        let arg = |index| Z3_get_app_arg(z3, app, index);
        let arity = Z3_get_app_num_args(z3, app);
        let sign_concat = if kind == DeclKind::CONCAT as u32 && numeral(ctx, arg(0)).is_none() {
            Z3_inc_ref(z3, ast);
            let ast = Ast { ctx, z3_ast: ast };
            ast.sign_extension_parts().map(|(base, _)| base.z3_ast)
        } else {
            None
        };
        if let Some(base) = sign_concat {
            // base 是根 AST 的子节点，遍历期间由根引用保活。
            if !children_ready {
                pending.push((ast, true));
                pending.push((base, false));
            } else {
                let range: BitvectorRange = bounds[&base].unwrap();
                bounds.insert(ast, Some(with_signed((range.min, range.max))));
            }
            continue;
        }
        let negated = if kind == DeclKind::BMUL as u32 && arity == 2 {
            (0..2).find(|&index| numeral(ctx, arg(1 - index)) == Some(mask))
        } else {
            None
        };
        let args = match kind {
            k if k == DeclKind::ITE as u32 => 1..3,
            k if [DeclKind::ZERO_EXT, DeclKind::SIGN_EXT, DeclKind::EXTRACT, DeclKind::BNEG]
                .map(|d| d as u32)
                .contains(&k) =>
            {
                0..1
            }
            k if [DeclKind::BAND, DeclKind::CONCAT, DeclKind::BADD, DeclKind::BSUB].map(|d| d as u32).contains(&k) => {
                0..arity
            }
            _ if negated.is_some() => {
                let index = negated.unwrap();
                index..index + 1
            }
            _ => {
                bounds.insert(ast, Some(full));
                continue;
            }
        };
        if !children_ready {
            pending.push((ast, true));
            pending.extend(args.rev().map(|index| (arg(index), false)));
            continue;
        }

        let operand = |index| bounds[&arg(index)];
        let range = (|| {
            if negated.is_some() || kind == DeclKind::BNEG as u32 {
                let value = operand(args.start)?;
                let (min, max) = (value.max.checked_neg()?, value.min.checked_neg()?);
                return (min >= full.min && max <= full.max).then(|| with_signed((min, max)));
            }
            match kind {
                k if k == DeclKind::SIGN_EXT as u32 => {
                    let value = operand(args.start)?;
                    Some(with_signed((value.min, value.max)))
                }
                k if k == DeclKind::ITE as u32 => {
                    let (a, b) = (operand(1)?, operand(2)?);
                    Some(from_upper(a.unsigned_upper.max(b.unsigned_upper)).intersect_signed(
                        a.min.min(b.min),
                        a.max.max(b.max),
                        mask,
                    ))
                }
                k if k == DeclKind::ZERO_EXT as u32 => Some(from_upper(operand(0)?.unsigned_upper)),
                k if k == DeclKind::EXTRACT as u32 => {
                    let low = u32::try_from(Z3_get_decl_int_parameter(z3, decl, 1)).unwrap();
                    Some(operand(0).map_or(full, |value| from_upper((value.unsigned_upper >> low).min(mask))))
                }
                k if k == DeclKind::BAND as u32 => {
                    let upper =
                        args.map(operand).try_fold(mask, |upper, value| Some(upper.min(value?.unsigned_upper)))?;
                    Some(from_upper(upper))
                }
                k if k == DeclKind::CONCAT as u32 => {
                    let mut upper = 0u128;
                    for index in args {
                        let width = bv_width(z3, arg(index)).unwrap();
                        upper = (upper.checked_shl(width).unwrap_or(0)) | operand(index)?.unsigned_upper;
                    }
                    Some(from_upper(upper))
                }
                k if k == DeclKind::BADD as u32 => {
                    let upper = args
                        .clone()
                        .map(operand)
                        .try_fold(0u128, |upper, value| upper.checked_add(value?.unsigned_upper))
                        .filter(|&upper| upper <= mask)
                        .unwrap_or(mask);
                    let unsigned = from_upper(upper);
                    let signed = args.map(operand).try_fold((0i128, 0i128), |(min, max), value| {
                        let value = value?;
                        Some((min.checked_add(value.min)?, max.checked_add(value.max)?))
                    });
                    Some(
                        signed
                            .filter(|&(min, max)| min >= full.min && max <= full.max)
                            .map_or(unsigned, |(min, max)| unsigned.intersect_signed(min, max, mask)),
                    )
                }
                k if k == DeclKind::BSUB as u32 => {
                    let (a, b) = (operand(0)?, operand(1)?);
                    let (min, max) = (a.min.checked_sub(b.max)?, a.max.checked_sub(b.min)?);
                    (min >= full.min && max <= full.max).then(|| with_signed((min, max)))
                }
                _ => unreachable!("范围递推只访问已识别的运算"),
            }
        })();
        // 位向量越过本身的有符号边界时会回绕，未经证明不能沿用数学区间。
        bounds.insert(ast, Some(range.unwrap_or(full)));
    }
    bounds[&root]
}

unsafe fn structural_comparison(ctx: &Context, ast: Z3_ast) -> Option<bool> {
    let z3 = ctx.z3_ctx;
    let mut ast = ast;
    let mut negated = false;
    let (app, kind) = loop {
        let (app, decl) = bv_application(z3, ast)?;
        let kind = rewrite::decl_kind_raw(z3, decl);
        if kind != DeclKind::NOT as u32 {
            break (app, kind);
        }
        negated = !negated;
        ast = Z3_get_app_arg(z3, app, 0);
    };
    if Z3_get_app_num_args(z3, app) != 2 {
        return None;
    }
    let left = Z3_get_app_arg(z3, app, 0);
    let right = Z3_get_app_arg(z3, app, 1);
    let result = match kind {
        k if k == DeclKind::ULT as u32 || k == DeclKind::ULEQ as u32 => {
            let limit = numeral(ctx, right)?;
            let bound = bitvector_range(ctx, left)?.unsigned_upper;
            (bound < limit || (k == DeclKind::ULEQ as u32 && bound == limit)).then_some(true)
        }
        k if [DeclKind::SLT, DeclKind::SLEQ, DeclKind::SGT, DeclKind::SGEQ].map(|d| d as u32).contains(&k) => {
            // 常量阈值与有符号区间比较。区间跨过阈值或运算可能回绕时保留未决分支。
            if !Z3_is_numeral_ast(z3, left) && !Z3_is_numeral_ast(z3, right) {
                return None;
            }
            let (a, b) =
                if k == DeclKind::SGT as u32 || k == DeclKind::SGEQ as u32 { (right, left) } else { (left, right) };
            let (a, b) = (bitvector_range(ctx, a)?, bitvector_range(ctx, b)?);
            let inclusive = k == DeclKind::SLEQ as u32 || k == DeclKind::SGEQ as u32;
            if a.max < b.min || (inclusive && a.max == b.min) {
                Some(true)
            } else if a.min > b.max || (!inclusive && a.min == b.max) {
                Some(false)
            } else {
                None
            }
        }
        _ => None,
    };
    result.map(|value| value != negated)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;

    #[test]
    fn define_const_simplifies_only_when_value_is_read() {
        configure_tastic(Tactic::Qfaufbv);
        let info = SourceLoc::unknown();
        for no_smt in [true, false] {
            let mut config = Config::new();
            config.solver_options.no_smt = no_smt;
            let context = Context::new(config);
            let mut solver = Solver::<B64>::new(&context);
            let input = solver.define_const(bits64(2, 8), info);
            let add = |amount| Exp::Bvadd(Box::new(Exp::Var(input)), Box::new(bits64(amount, 8)));

            // 参照原路径，在定义时解析绑定并立即化简。
            let mut expected: Vec<_> = (0..16).map(|amount| solver.translate_exp(&add(amount))).collect();
            for value in &mut expected {
                value.simplify();
            }

            let before = AST_SIMPLIFY_CALLS.get();
            let derived: Vec<_> = (0..16).map(|amount| solver.define_const(add(amount), info)).collect();
            for &symbol in &derived {
                assert_eq!(solver.length(symbol), Some(8));
                assert_eq!(solver.scalar_sort(symbol), Some(Ty::BitVec(8)));
                assert!(solver.is_bitvector(symbol));
                assert!(!solver.is_bool(symbol));
            }
            assert_eq!(AST_SIMPLIFY_CALLS.get(), before, "未读值的定义和类型查询无需 Z3 化简");

            let tx = solver.start_transaction();
            solver.add(Def::DefineConst(input, bits64(100, 8)));
            for (index, &symbol) in derived.iter().enumerate() {
                let before = AST_SIMPLIFY_CALLS.get();
                let value = solver.translate_exp(&Exp::Var(symbol));
                assert_eq!(value.z3_ast, expected[index].z3_ast, "延迟化简必须保留定义时的绑定");
                assert_eq!(value.get_numeral_u64().unwrap(), index as u64 + 2);
                assert_eq!(AST_SIMPLIFY_CALLS.get(), before, "读取前已知操作数全为字面量");
                assert_eq!(solver.translate_exp(&Exp::Var(symbol)).z3_ast, value.z3_ast);
                assert_eq!(AST_SIMPLIFY_CALLS.get(), before, "重复读值须复用已化简表达式");
            }
            solver.rollback_transaction(tx);
            assert_eq!(solver.translate_exp(&Exp::Var(input)).get_numeral_u64().unwrap(), 2);
        }
    }

    #[test]
    fn deep_shared_bounds_and_wrapping_arithmetic() {
        configure_tastic(Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let condition = solver.declare_const(Ty::Bool, info);
        let mut value = solver.define_const(
            Exp::Ite(Box::new(Exp::Var(condition)), Box::new(bits64(1, 16)), Box::new(bits64(2, 16))),
            info,
        );
        for _ in 0..512 {
            value = solver.define_const(Exp::Bvadd(Box::new(Exp::Var(value)), Box::new(bits64(1, 16))), info);
        }
        for _ in 0..64 {
            let masked = Exp::Bvand(Box::new(Exp::Var(value)), Box::new(bits64(0xfffe, 16)));
            value = solver.define_const(
                Exp::Ite(Box::new(Exp::Var(condition)), Box::new(Exp::Var(value)), Box::new(masked)),
                info,
            );
        }
        let compare = |value, limit| Exp::Bvult(Box::new(Exp::Var(value)), Box::new(bits64(limit, 16)));
        let ast = solver.translate_exp(&compare(value, 515));
        assert_eq!(unsafe { structural_comparison(&context, ast.z3_ast) }, Some(true));

        let wrapped = solver.define_const(Exp::Bvadd(Box::new(Exp::Var(value)), Box::new(bits64(65022, 16))), info);
        let ast = solver.translate_exp(&compare(wrapped, 515));
        assert_eq!(unsafe { structural_comparison(&context, ast.z3_ast) }, None);
    }
}
