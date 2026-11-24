//! 不依赖路径前提的 AST 等价改写，有 SMT 与无 SMT 共用。
use super::*;
use serde::{Deserialize, Deserializer};
use std::sync::atomic::{AtomicU64, Ordering};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BvRewrite(u8);

impl Default for BvRewrite {
    fn default() -> Self {
        Self::ALL
    }
}

impl BvRewrite {
    const NONE: Self = Self(0);
    const ALL: Self = Self(7);

    pub fn enabled(self) -> bool {
        self.0 != 0
    }
    pub fn parse(value: &str) -> Result<Self, String> {
        match value {
            "true" => Ok(Self::ALL),
            "false" => Ok(Self::NONE),
            _ => {
                let mut bits = 0;
                for rule in value.split(',') {
                    bits |= match rule {
                        "data-ite-eq" => 1,
                        "mask-and" => 2,
                        "sign-bound" => 4,
                        _ => {
                            return Err(format!(
                                "未知 bv_rewrite 规则 {rule}；支持 data-ite-eq,mask-and,sign-bound 或 true/false"
                            ))
                        }
                    };
                }
                Ok(Self(bits))
            }
        }
    }
}

impl<'de> Deserialize<'de> for BvRewrite {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Setting {
            Bool(bool),
            Rules(Vec<String>),
        }
        match Setting::deserialize(d)? {
            Setting::Bool(b) => Ok(if b { Self::ALL } else { Self::NONE }),
            Setting::Rules(rules) if rules.is_empty() => Ok(Self::NONE),
            Setting::Rules(rules) => Self::parse(&rules.join(",")).map_err(serde::de::Error::custom),
        }
    }
}

static HITS: [AtomicU64; 3] = [AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0)];
fn hit(index: usize) {
    HITS[index].fetch_add(1, Ordering::Relaxed);
}
pub fn diagnostics() -> serde_json::Value {
    serde_json::json!({"kind":"bv_rewrite_hits", "data-ite-eq":HITS[0].load(Ordering::Relaxed),
        "mask-and":HITS[1].load(Ordering::Relaxed), "sign-bound":HITS[2].load(Ordering::Relaxed)})
}

// 现用 Z3 在新运算加入后存在 z3-sys 未覆盖的枚举值。通过整数读取避免
// 对未解释函数等节点构造无效的 Rust enum；这里只匹配稳定的基础运算编号。
extern "C" {
    #[link_name = "Z3_get_decl_kind"]
    pub(super) fn decl_kind_raw(ctx: Z3_context, decl: Z3_func_decl) -> u32;
}

impl<'ctx> Ast<'ctx> {
    fn rewrite_decl_kind(&self) -> Option<u32> {
        unsafe {
            let ctx = self.ctx.z3_ctx;
            // 这些改写只匹配运算符。Z3_is_app 也接纳数值，随后的声明种类检查会排除它们。
            Z3_is_app(ctx, self.z3_ast).then(|| decl_kind_raw(ctx, Z3_get_app_decl(ctx, Z3_to_app(ctx, self.z3_ast))))
        }
    }

    pub(super) fn rewrite_kind(&self, kind: DeclKind) -> bool {
        self.rewrite_decl_kind() == Some(kind as u32)
    }

    fn rewrite_args(&self) -> Vec<Self> {
        unsafe {
            let app = Z3_to_app(self.ctx.z3_ctx, self.z3_ast);
            (0..Z3_get_app_num_args(self.ctx.z3_ctx, app))
                .map(|i| {
                    let node = Z3_get_app_arg(self.ctx.z3_ctx, app, i);
                    Z3_inc_ref(self.ctx.z3_ctx, node);
                    Ast { ctx: self.ctx, z3_ast: node }
                })
                .collect()
        }
    }
    fn rewrite_width(&self) -> u32 {
        unsafe { Z3_get_bv_sort_size(self.ctx.z3_ctx, Z3_get_sort(self.ctx.z3_ctx, self.z3_ast)) }
    }

    /// 返回扩展前的值和符号位，也识别 Z3 化简生成的重复位拼接。
    pub(super) fn sign_extension_parts(&self) -> Option<(Self, Self)> {
        if self.rewrite_kind(DeclKind::SIGN_EXT) {
            let base = self.rewrite_args().remove(0);
            if self.rewrite_width() == base.rewrite_width() {
                return None;
            }
            let top = base.rewrite_width() - 1;
            let mut sign = base.extract(top, top);
            sign.simplify();
            return Some((base, sign));
        }
        if !self.rewrite_kind(DeclKind::CONCAT) {
            return None;
        }
        let mut pending = self.rewrite_args();
        let mut parts = Vec::new();
        while let Some(part) = pending.pop() {
            if part.rewrite_kind(DeclKind::CONCAT) {
                pending.extend(part.rewrite_args());
            } else {
                parts.push(part);
            }
        }
        let mut parts = parts.into_iter();
        let base = parts.next().expect("拼接应有操作数");
        let top = base.rewrite_width() - 1;
        let mut sign = base.extract(top, top);
        sign.simplify();
        parts.all(|part| part.z3_ast == sign.z3_ast).then_some((base, sign))
    }
}

/// 只访问新构造节点。子节点已从同一个翻译入口通过，DefineConst 的 AST
/// 也保留这些结果；不反复遍历展开后的历史 DAG。只有分配 ITE 相等判断时
/// 访问其数据 DAG，记忆化键为两操作数的 AST，结果持有引用直到整次展开结束。
pub(super) fn apply(ast: Ast<'_>, rules: BvRewrite) -> Ast<'_> {
    if !rules.enabled() {
        return ast;
    }
    let kind = ast.rewrite_decl_kind();
    if rules.0 & 1 != 0 && kind == Some(DeclKind::EQ as u32) {
        let args = ast.rewrite_args();
        let sort = unsafe { Z3_get_sort_kind(ast.ctx.z3_ctx, Z3_get_sort(ast.ctx.z3_ctx, args[0].z3_ast)) };
        // 只分配有限数据相等判断，避免任意位向量 ITE 比较的交叉乘积。
        if sort == SortKind::Datatype && (args[0].rewrite_kind(DeclKind::ITE) || args[1].rewrite_kind(DeclKind::ITE)) {
            let mut memo = HashMap::new();
            let result = data_equal(&args[0], &args[1], &mut memo);
            hit(0);
            return result;
        }
    }
    if rules.0 & 2 != 0 && kind == Some(DeclKind::BNOT as u32) {
        let inner = ast.rewrite_args().remove(0);
        if inner.rewrite_kind(DeclKind::BOR) {
            let terms = inner.rewrite_args();
            if terms.len() == 2 {
                for (not, xor) in [(&terms[0], &terms[1]), (&terms[1], &terms[0])] {
                    if not.rewrite_kind(DeclKind::BNOT) && xor.rewrite_kind(DeclKind::BXOR) {
                        let a = not.rewrite_args().remove(0);
                        let xs = xor.rewrite_args();
                        if xs.len() == 2 {
                            for i in 0..2 {
                                if xs[i].z3_ast == a.z3_ast {
                                    hit(1);
                                    return a.mk_bvand(&xs[1 - i]);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    if rules.0 & 4 != 0 && kind == Some(DeclKind::ULEQ as u32) {
        let args = ast.rewrite_args();
        let value = &args[0];
        let constant = &args[1];
        if unsafe { Z3_is_numeral_ast(ast.ctx.z3_ctx, constant.z3_ast) } {
            if let Some((base, sign)) = value.sign_extension_parts() {
                let m = base.rewrite_width();
                let n = value.rewrite_width();
                // 用任意精度整数核对常量，不引入额外 SMT 查询。
                let c = unsafe { CStr::from_ptr(Z3_get_numeral_string(ast.ctx.z3_ctx, constant.z3_ast)) };
                let c = num_bigint::BigUint::parse_bytes(c.to_bytes(), 10).expect("位向量常量应为十进制整数");
                let one = num_bigint::BigUint::from(1u8);
                let lower = (&one << (m - 1)) - &one;
                let top = &one << (n - 1);
                if lower <= c && c < top {
                    hit(2);
                    return sign.mk_eq(&Ast::mk_bv_u64(ast.ctx, 1, 0));
                }
            }
        }
    }
    ast
}

fn data_equal<'ctx>(a: &Ast<'ctx>, b: &Ast<'ctx>, memo: &mut HashMap<(Z3_ast, Z3_ast), Ast<'ctx>>) -> Ast<'ctx> {
    let key = (a.z3_ast, b.z3_ast);
    if let Some(value) = memo.get(&key) {
        return value.clone();
    }
    let value = if a.rewrite_kind(DeclKind::ITE) {
        let xs = a.rewrite_args();
        xs[0].ite(&data_equal(&xs[1], b, memo), &data_equal(&xs[2], b, memo))
    } else if b.rewrite_kind(DeclKind::ITE) {
        let xs = b.rewrite_args();
        xs[0].ite(&data_equal(a, &xs[1], memo), &data_equal(a, &xs[2], memo))
    } else {
        if a.ctx.has_unbounded_rewriting() && is_enum_member(a) && is_enum_member(b) {
            Ast::mk_bool(a.ctx, a.z3_ast == b.z3_ast)
        } else {
            let mut eq = a.mk_eq(b);
            eq.simplify_small();
            eq
        }
    };
    memo.insert(key, value.clone());
    value
}

// Datatype 等号的两侧若均为零元构造子，Z3 只检查构造子身份。
fn is_enum_member(ast: &Ast<'_>) -> bool {
    unsafe {
        let z3 = ast.ctx.z3_ctx;
        Z3_get_ast_kind(z3, ast.z3_ast) == AstKind::App
            && Z3_get_app_num_args(z3, Z3_to_app(z3, ast.z3_ast)) == 0
            && ast.rewrite_kind(DeclKind::DT_CONSTRUCTOR)
    }
}

#[derive(Default)]
pub(super) struct SmallSimplifications {
    entries: ahash::AHashMap<(Z3_ast, bool), Z3_ast>,
    // 原生输出由 entries 持有。复验过同一输出且结构恒等后才标记。
    outputs: ahash::AHashMap<(Z3_ast, bool), bool>,
    uninterpreted_kind: Option<u32>,
}

impl SmallSimplifications {
    fn uninterpreted_kind(&mut self, z3: Z3_context) -> u32 {
        // z3-sys 的编号早于当前 libz3，通过未解释常量读取本库的实际值。
        *self.uninterpreted_kind.get_or_insert_with(|| unsafe {
            let sort = Z3_mk_bool_sort(z3);
            let constant = Z3_mk_fresh_const(z3, ptr::null(), sort);
            decl_kind_raw(z3, Z3_get_app_decl(z3, Z3_to_app(z3, constant)))
        })
    }

    pub(super) fn clear(&mut self, z3: Z3_context) {
        self.outputs.clear();
        for ((input, _), output) in self.entries.drain() {
            unsafe {
                Z3_dec_ref(z3, input);
                Z3_dec_ref(z3, output);
            }
        }
    }
}

impl Ast<'_> {
    // 对可独立取真、假的原子与其否定，两侧都无须先化简来判定为非恒值。
    pub(super) fn is_open_branch_atom(&self) -> bool {
        let z3 = self.ctx.z3_ctx;
        unsafe {
            let app = |term| (Z3_get_ast_kind(z3, term) == AstKind::App).then(|| Z3_to_app(z3, term));
            let kind = |node| decl_kind_raw(z3, Z3_get_app_decl(z3, node));
            let Some(mut node) = app(self.z3_ast) else { return false };
            if kind(node) == DeclKind::NOT as u32 {
                let Some(inner) = app(Z3_get_app_arg(z3, node, 0)) else { return false };
                node = inner;
            }
            let is_variable = |node| {
                Z3_get_app_num_args(z3, node) == 0
                    && kind(node) == self.ctx.small_simplifications.borrow_mut().uninterpreted_kind(z3)
            };
            if Z3_get_app_num_args(z3, node) == 0 {
                return Z3_get_sort_kind(z3, Z3_get_sort(z3, self.z3_ast)) == SortKind::Bool && is_variable(node);
            }
            if kind(node) != DeclKind::EQ as u32 {
                return false;
            }
            let lhs = Z3_get_app_arg(z3, node, 0);
            let rhs = Z3_get_app_arg(z3, node, 1);
            if lhs == rhs || !matches!(Z3_get_sort_kind(z3, Z3_get_sort(z3, lhs)), SortKind::Bool | SortKind::BV) {
                return false;
            }
            let lhs_var = app(lhs).is_some_and(is_variable);
            let rhs_var = app(rhs).is_some_and(is_variable);
            let literal = |term| Z3_is_numeral_ast(z3, term) || Z3_get_bool_value(z3, term) != Z3_L_UNDEF;
            (lhs_var && (rhs_var || literal(rhs))) || (rhs_var && literal(lhs))
        }
    }

    pub(super) fn simplify_with_verified_fixpoint(&mut self) {
        if !self.ctx.has_unbounded_rewriting() {
            self.simplify_native();
            return;
        }
        let default_params = SMT_CONFIG.get().is_some_and(|config| config.tactic == Tactic::Default);
        let key = (self.z3_ast, default_params);
        let verified = self.ctx.small_simplifications.borrow().outputs.get(&key).copied();
        if verified == Some(true) {
            return;
        }
        self.simplify_native();
        if verified == Some(false) && self.z3_ast == key.0 {
            self.ctx.small_simplifications.borrow_mut().outputs.insert(key, true);
        }
    }

    /// 在首次读定义、数据相等和扩展检查中共用小式子的精确输入。
    pub(super) fn simplify_small(&mut self) {
        if !self.ctx.has_unbounded_rewriting() {
            self.simplify_native();
            return;
        }
        let default_params = SMT_CONFIG.get().is_some_and(|config| config.tactic == Tactic::Default);
        let key = (self.z3_ast, default_params);
        let z3 = self.ctx.z3_ctx;
        let mut table = self.ctx.small_simplifications.borrow_mut();
        if let Some(&result) = table.entries.get(&key) {
            unsafe {
                Z3_inc_ref(z3, result);
                Z3_dec_ref(z3, self.z3_ast);
            }
            self.z3_ast = result;
            return;
        }
        let uninterpreted_kind = table.uninterpreted_kind(z3);
        if !small_rewrite_input(z3, self.z3_ast, uninterpreted_kind) {
            self.simplify_native();
            return;
        }
        let original = self.clone();
        self.simplify_native();
        // 保留至多 8,192 对小输入和结果。大图仍走原生入口，避免占用长根的缓存空间。
        const SMALL_REWRITE_LIMIT: usize = 8_192;
        if table.entries.len() >= SMALL_REWRITE_LIMIT {
            table.clear(z3);
        }
        unsafe { Z3_inc_ref(z3, self.z3_ast) };
        std::mem::forget(original);
        table.entries.insert(key, self.z3_ast);
        let output = (self.z3_ast, default_params);
        if let Some(unchanged) = table.outputs.get_mut(&key) {
            *unchanged |= key == output;
        }
        if small_rewrite_input(z3, self.z3_ast, uninterpreted_kind) {
            table.outputs.entry(output).or_insert(false);
        }
    }
}

// 只允许无需依赖共享引用数即可化简的小型 BV／布尔式。排除 ITE、除法、
// 绑定器及非原子数据项，避免重用受 Z3 引用数启发式影响的结构。
fn small_rewrite_input(z3: Z3_context, root: Z3_ast, uninterpreted_kind: u32) -> bool {
    use DeclKind::*;
    let mut pending = [root; 16];
    let mut count = 1;
    // 只检查少量节点。失败后沿用同一个化简调用，预算和表达式结果保持原有语义。
    for _ in 0..pending.len() {
        if count == 0 {
            return true;
        }
        count -= 1;
        let term = pending[count];
        unsafe {
            if Z3_get_ast_kind(z3, term) == AstKind::Numeral {
                if Z3_get_sort_kind(z3, Z3_get_sort(z3, term)) != SortKind::BV {
                    return false;
                }
                continue;
            }
            if Z3_get_ast_kind(z3, term) != AstKind::App {
                return false;
            }
            let app = Z3_to_app(z3, term);
            let arity = Z3_get_app_num_args(z3, app) as usize;
            let kind = decl_kind_raw(z3, Z3_get_app_decl(z3, app));
            let sort = Z3_get_sort_kind(z3, Z3_get_sort(z3, term));
            match kind {
                k if k == DT_CONSTRUCTOR as u32 => {
                    if arity != 0 {
                        return false;
                    }
                }
                k if k == uninterpreted_kind => {
                    if arity != 0 || !matches!(sort, SortKind::Bool | SortKind::BV | SortKind::Datatype) {
                        return false;
                    }
                }
                k if [
                    TRUE, FALSE, NOT, AND, OR, EQ, BADD, BSUB, BMUL, BNOT, BAND, BOR, BXOR, CONCAT, EXTRACT, ZERO_EXT,
                    SIGN_EXT, ULEQ, ULT, SLEQ, SLT,
                ]
                .into_iter()
                .any(|op| k == op as u32) =>
                {
                    if count + arity > pending.len() {
                        return false;
                    }
                    for i in 0..arity {
                        pending[count + i] = Z3_get_app_arg(z3, app, i as u32);
                    }
                    count += arity;
                }
                _ => return false,
            }
        }
    }
    count == 0
}
