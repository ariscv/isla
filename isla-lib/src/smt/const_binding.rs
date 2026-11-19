//! 常量绑定保存定义时的表达式，首次取值时化简并保留结果。
use super::{Ast, Context, Z3_ast, Z3_dec_ref, Z3_get_sort, Z3_inc_ref, Z3_sort};
use std::cell::Cell;

pub(super) struct ConstBinding<'ctx> {
    ctx: &'ctx Context,
    value: Cell<Z3_ast>,
    pending: Cell<bool>,
}

impl<'ctx> ConstBinding<'ctx> {
    pub(super) fn new(value: Ast<'ctx>, pending: bool) -> Self {
        let binding = Self { ctx: value.ctx, value: Cell::new(value.z3_ast), pending: Cell::new(pending) };
        // 将 AST 引用移交给绑定，保存点移动绑定时也一并移交。
        std::mem::forget(value);
        binding
    }

    pub(super) fn ast(&self) -> Ast<'ctx> {
        let z3_ast = self.value.get();
        // 绑定与调用方各自持有一个引用，化简可以独立替换任一引用。
        unsafe { Z3_inc_ref(self.ctx.z3_ctx, z3_ast) };
        let mut ast = Ast { ctx: self.ctx, z3_ast };
        if self.pending.replace(false) {
            ast.simplify();
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
