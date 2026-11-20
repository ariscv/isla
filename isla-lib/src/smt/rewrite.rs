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
    pub(super) fn rewrite_kind(&self, kind: DeclKind) -> bool {
        unsafe {
            Z3_get_ast_kind(self.ctx.z3_ctx, self.z3_ast) == AstKind::App
                && decl_kind_raw(
                    self.ctx.z3_ctx,
                    Z3_get_app_decl(self.ctx.z3_ctx, Z3_to_app(self.ctx.z3_ctx, self.z3_ast)),
                ) == kind as u32
        }
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
    if rules.0 & 1 != 0 && ast.rewrite_kind(DeclKind::EQ) {
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
    if rules.0 & 2 != 0 && ast.rewrite_kind(DeclKind::BNOT) {
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
    if rules.0 & 4 != 0 && ast.rewrite_kind(DeclKind::ULEQ) {
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
        let mut eq = a.mk_eq(b);
        eq.simplify();
        eq
    };
    memo.insert(key, value.clone());
    value
}
