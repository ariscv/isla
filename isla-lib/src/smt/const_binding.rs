//! 常量绑定保存定义时的表达式，首次取值时化简并保留结果。
use super::{finite_domain::ground, Ast, Context, Z3_ast, Z3_dec_ref, Z3_get_sort, Z3_inc_ref, Z3_sort};
use std::cell::Cell;

pub(super) struct ConstBinding<'ctx> {
    ctx: &'ctx Context,
    value: Cell<Z3_ast>,
    pending: Cell<bool>,
    replay_ast: Option<Ast<'ctx>>,
}

impl<'ctx> ConstBinding<'ctx> {
    pub(super) fn new(value: Ast<'ctx>, pending: bool, keep_replay: bool) -> Self {
        let replay_ast = keep_replay.then(|| value.clone());
        // 定义时仅折叠已可确定的浅层值。复杂表达式仍在首次消费时化简。
        let folded = (pending && value.ctx.has_unbounded_rewriting()).then(|| ground::fold_shallow(&value)).flatten();
        let pending = pending && folded.is_none();
        let value = folded.unwrap_or(value);
        let binding = Self { ctx: value.ctx, value: Cell::new(value.z3_ast), pending: Cell::new(pending), replay_ast };
        // 将 AST 引用移交给绑定，保存点移动绑定时也一并移交。
        std::mem::forget(value);
        binding
    }

    pub(super) fn raw_ast(&self) -> Ast<'ctx> {
        self.replay_ast.clone().unwrap_or_else(|| self.current_ast())
    }

    fn current_ast(&self) -> Ast<'ctx> {
        let z3_ast = self.value.get();
        // 绑定与调用方各自持有一个引用，化简可以独立替换任一引用。
        unsafe { Z3_inc_ref(self.ctx.z3_ctx, z3_ast) };
        Ast { ctx: self.ctx, z3_ast }
    }

    pub(super) fn ast(&self) -> Ast<'ctx> {
        let mut ast = self.current_ast();
        if self.pending.replace(false) {
            if let Some(choice) = ast.simplify_terminal_choice() {
                ast = choice;
            } else {
                ast.simplify_small();
            }
            unsafe {
                Z3_inc_ref(self.ctx.z3_ctx, ast.z3_ast);
                Z3_dec_ref(self.ctx.z3_ctx, self.value.replace(ast.z3_ast));
            }
        }
        ast
    }

    pub(super) fn sort(&self) -> Z3_sort {
        // Z3 sort 由绑定持有的 AST 保活，化简不会改变 sort。
        unsafe { Z3_get_sort(self.ctx.z3_ctx, self.value.get()) }
    }
}

impl Drop for ConstBinding<'_> {
    fn drop(&mut self) {
        unsafe { Z3_dec_ref(self.ctx.z3_ctx, self.value.get()) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::{configure_tastic, Config, Tactic};

    #[test]
    fn literal_binding_is_ready_at_definition_time() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let value = Ast::mk_bv_u64(&ctx, 8, 10);
        let raw = value.mk_bvadd(&Ast::mk_bv_u64(&ctx, 8, 0));
        let binding = ConstBinding::new(raw.clone(), true, true);
        assert!(!binding.pending.get());
        assert_eq!(binding.raw_ast().z3_ast, raw.z3_ast);
        assert_eq!(binding.ast().z3_ast, value.z3_ast);
    }
}
