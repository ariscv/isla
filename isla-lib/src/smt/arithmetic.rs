//! 在已有AST编码入口化简除法/余数，不依赖路径前提。
use super::*;

impl Ast<'_> {
    fn is_power_of_two_or_zero(&self) -> bool {
        unsafe {
            let ctx = self.ctx.z3_ctx;
            let width = Z3_get_bv_sort_size(ctx, Z3_get_sort(ctx, self.z3_ast));
            let zero = Ast::mk_bv_u64(self.ctx, width, 0);
            let one = Ast::mk_bv_u64(self.ctx, width, 1);
            let shift = zero.mk_bvshl(&zero);
            let choice = Ast::mk_bool(self.ctx, false).ite(&zero, &one);
            let shift_decl = Z3_get_app_decl(ctx, Z3_to_app(ctx, shift.z3_ast));
            let choice_decl = Z3_get_app_decl(ctx, Z3_to_app(ctx, choice.z3_ast));
            let mut pending = vec![self.z3_ast];
            // 只限制优化识别成本，不限制执行或求解；未识别的表达式沿用原编码。
            for _ in 0..32 {
                let Some(node) = pending.pop() else { return true };
                if Z3_is_numeral_ast(ctx, node) {
                    Z3_inc_ref(ctx, node);
                    let constant = Ast { z3_ast: node, ctx: self.ctx };
                    let mut masked = constant.mk_bvand(&constant.mk_bvsub(&one));
                    masked.simplify();
                    if !Z3_is_eq_ast(ctx, masked.z3_ast, zero.z3_ast) {
                        return false;
                    }
                } else if Z3_get_ast_kind(ctx, node) == AstKind::App {
                    let app = Z3_to_app(ctx, node);
                    let declaration = Z3_get_app_decl(ctx, app);
                    // 核对实际内建声明，不能把同名未解释函数当移位或条件表达式；
                    // 现用Z3与z3-sys的DeclKind枚举不兼容，沿用内建声明比较。
                    if Z3_is_eq_func_decl(ctx, declaration, shift_decl) {
                        pending.push(Z3_get_app_arg(ctx, app, 0));
                    } else if Z3_is_eq_func_decl(ctx, declaration, choice_decl) {
                        pending.push(Z3_get_app_arg(ctx, app, 1));
                        pending.push(Z3_get_app_arg(ctx, app, 2));
                    } else {
                        return false;
                    }
                } else {
                    return false;
                }
            }
            pending.is_empty()
        }
    }
}

impl<'ctx> Ast<'ctx> {
    pub(super) fn mk_bvsrem(&self, divisor: &Self) -> Self {
        if !divisor.is_power_of_two_or_zero() {
            return z3_binary_op!(Z3_mk_bvsrem, self, divisor);
        }
        let width = unsafe { Z3_get_bv_sort_size(self.ctx.z3_ctx, Z3_get_sort(self.ctx.z3_ctx, self.z3_ast)) };
        let zero = Ast::mk_bv_u64(self.ctx, width, 0);
        let one = Ast::mk_bv_u64(self.ctx, width, 1);
        let mask = divisor.mk_bvsub(&one);
        // srem符号跟随被除数：先对绝对值取低位，再恢复符号。
        // 最高位置位的负除数同样有效；除数零时mask全一，结果仍为被除数。
        // 最小负数的取负按位向量模算术保持原值，也满足此恒等式。
        let positive = self.mk_bvand(&mask);
        let negative = self.mk_bvneg().mk_bvand(&mask).mk_bvneg();
        self.mk_bvslt(&zero).ite(&negative, &positive)
    }
}

impl<'ctx> Ast<'ctx> {
    fn extended_source_width(&self, signed: bool) -> Option<u32> {
        unsafe {
            let ctx = self.ctx.z3_ctx;
            if Z3_get_ast_kind(ctx, self.z3_ast) != AstKind::App {
                return None;
            }
            let app = Z3_to_app(ctx, self.z3_ast);
            let count = Z3_get_app_num_args(ctx, app);
            if count == 0 {
                return None;
            }
            let child = Z3_get_app_arg(ctx, app, count - 1);
            let child_sort = Z3_get_sort(ctx, child);
            if Z3_get_sort_kind(ctx, child_sort) != SortKind::BV {
                return None;
            }
            let source = Z3_get_bv_sort_size(ctx, child_sort);
            let width = Z3_get_bv_sort_size(ctx, Z3_get_sort(ctx, self.z3_ast));
            // 一位有符号数的除零结果+1无法在一位内表示，保留原编码。
            if source < 2 || source >= width {
                return None;
            }
            Z3_inc_ref(ctx, child);
            let child = Ast { z3_ast: child, ctx: self.ctx };
            let mut rebuilt =
                if signed { child.sign_extend(width - source) } else { child.zero_extend(width - source) };
            if Z3_is_eq_ast(ctx, self.z3_ast, rebuilt.z3_ast) {
                return Some(source);
            }
            // DefineConst已把sign_extend化成concat并传播extract到ITE。
            // 以同一原生化简器重建后严格比较AST，不按操作符显示名猜测类型/值域。
            rebuilt.simplify_small();
            Z3_is_eq_ast(ctx, self.z3_ast, rebuilt.z3_ast).then_some(source)
        }
    }

    pub(super) fn mk_bvmul(&self, rhs: &Self) -> Self {
        assert_eq!(self.ctx.z3_ctx, rhs.ctx.z3_ctx, "乘法操作数必须属于同一上下文");
        let width = unsafe { Z3_get_bv_sort_size(self.ctx.z3_ctx, Z3_get_sort(self.ctx.z3_ctx, self.z3_ast)) };
        let rhs_width = unsafe { Z3_get_bv_sort_size(self.ctx.z3_ctx, Z3_get_sort(self.ctx.z3_ctx, rhs.z3_ast)) };
        assert_eq!(width, rhs_width, "乘法操作数位宽必须一致");
        let left = self
            .extended_source_width(true)
            .map(|w| (w, true))
            .or_else(|| self.extended_source_width(false).map(|w| (w, false)));
        let right = rhs
            .extended_source_width(true)
            .map(|w| (w, true))
            .or_else(|| rhs.extended_source_width(false).map(|w| (w, false)));
        let (Some((left_source, left_signed)), Some((right_source, right_signed))) = (left, right) else {
            return z3_binary_op!(Z3_mk_bvmul, self, rhs);
        };
        if left_source >= width - right_source {
            return z3_binary_op!(Z3_mk_bvmul, self, rhs);
        }
        let product_width = left_source + right_source;
        let left = self.extract(product_width - 1, 0);
        let right = rhs.extract(product_width - 1, 0);
        let product = z3_binary_op!(Z3_mk_bvmul, left, right);
        // n位与m位的完整乘积在n+m位内表示；混合有/无符号时仍满足此界。
        // 保留全部乘积位后再扩展，让后续范围证明直接化简，避免求解宽乘法的高位。
        if left_signed || right_signed {
            product.sign_extend(width - product_width)
        } else {
            product.zero_extend(width - product_width)
        }
    }

    pub(super) fn mk_bvsdiv(&self, rhs: &Self) -> Self {
        assert_eq!(self.ctx.z3_ctx, rhs.ctx.z3_ctx, "有符号除法操作数必须属于同一上下文");
        let width = unsafe { Z3_get_bv_sort_size(self.ctx.z3_ctx, Z3_get_sort(self.ctx.z3_ctx, self.z3_ast)) };
        let rhs_width = unsafe { Z3_get_bv_sort_size(self.ctx.z3_ctx, Z3_get_sort(self.ctx.z3_ctx, rhs.z3_ast)) };
        assert_eq!(width, rhs_width, "有符号除法操作数位宽必须一致");
        let (Some(left_source), Some(right_source)) =
            (self.extended_source_width(true), rhs.extended_source_width(true))
        else {
            return z3_binary_op!(Z3_mk_bvsdiv, self, rhs);
        };
        let source = left_source.max(right_source);
        let left = self.extract(source - 1, 0);
        let right = rhs.extract(source - 1, 0);
        let one = Ast::mk_bv_u64(self.ctx, source, 1);
        let shift = Ast::mk_bv_u64(self.ctx, source, u64::from(source - 1));
        let minimum = one.mk_bvshl(&shift);
        let minus_one = one.mk_bvneg();
        let overflow = left.mk_eq(&minimum).mk_and(&right.mk_eq(&minus_one));
        let positive =
            Ast::mk_bv_u64(self.ctx, width, 1).mk_bvshl(&Ast::mk_bv_u64(self.ctx, width, u64::from(source - 1)));
        // 宽除法的MIN/-1为正的2^(n-1)，不能先在n位溢出再符号扩展。
        // 其余商（含SMT除零的±1）都能在n>=2位表示，故窄除法后符号扩展恒等。
        let quotient = z3_binary_op!(Z3_mk_bvsdiv, left, right).sign_extend(width - source);
        overflow.ite(&positive, &quotient)
    }
}
