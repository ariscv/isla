//! 有限域枚举完成赋值后，分别读取各布尔表达式的真值。
use super::*;

pub(super) fn assigned_bools(roots: &[&Ast<'_>]) -> Vec<bool> {
    // 这里的节点已经得到本次枚举的全部输入。只取布尔值，残余 AST 不进入缓存或前缀。
    let mut result = Vec::with_capacity(roots.len());
    for group in roots.chunks(32) {
        let ctx = group[0].ctx;
        if !ctx.has_unbounded_rewriting() {
            result.extend(
                group.iter().map(|root| (*root).clone().structural_bool().expect("已求值的布尔节点必须为常量")),
            );
            continue;
        }
        let mut pending = Vec::new();
        for root in group {
            let truth = root.get_bool_value();
            if truth.is_none() {
                pending.push((result.len(), *root));
            }
            result.push(truth.unwrap_or(false));
        }
        if pending.len() == 1 {
            let (index, root) = pending[0];
            result[index] = root.clone().structural_bool().expect("已求值的布尔节点必须为常量");
        } else if !pending.is_empty() {
            // 新鲜的未解释声明固定参数顺序。它和包装 AST 只在一次调用中保活。
            let z3 = ctx.z3_ctx;
            let args: Vec<_> = pending.iter().map(|(_, root)| root.z3_ast).collect();
            unsafe {
                let boolean = Z3_get_sort(z3, args[0]);
                let sorts = vec![boolean; args.len()];
                let arity = args.len() as u32;
                let decl = Z3_mk_fresh_func_decl(z3, c"f_batch".as_ptr(), arity, sorts.as_ptr(), boolean);
                let wrapper = Z3_mk_app(z3, decl, arity, args.as_ptr());
                Z3_inc_ref(z3, wrapper);
                let mut batch = Ast { ctx, z3_ast: wrapper };
                batch.simplify_native();
                let app = Z3_to_app(z3, batch.z3_ast);
                assert_eq!(Z3_get_app_decl(z3, app), decl, "化简必须保留未解释的批量包装");
                for (i, (index, root)) in pending.iter().enumerate() {
                    let value = Z3_get_app_arg(z3, app, i as u32);
                    result[*index] = match Z3_get_bool_value(z3, value) {
                        Z3_L_TRUE => true,
                        Z3_L_FALSE => false,
                        // 原入口还可用位向量范围证明已赋值谓词，保留这次判定。
                        _ => (*root).clone().structural_bool().expect("已求值的布尔节点必须为常量"),
                    };
                }
            }
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assigned_boolean_roots_keep_order_with_one_native_call_per_group() {
        configure_tastic(Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let proof = Context::new(Config::new());
        let mut rng = 0xf010_9c21_u32;
        for _ in 0..24 {
            let shared = Ast::mk_bv_u64(&ctx, 32, u64::from(rng)).mk_bvadd(&Ast::mk_bv_u64(&ctx, 32, 7));
            let mut expected = Vec::new();
            let roots: Vec<_> = (0..32)
                .map(|_| {
                    rng ^= rng << 13;
                    rng ^= rng >> 17;
                    rng ^= rng << 5;
                    let n = Ast::mk_bv_u64(&ctx, 32, u64::from(rng));
                    let truth = rng & 1 != 0;
                    expected.push(truth);
                    let lhs = shared.mk_bvadd(&n);
                    let rhs = n.mk_bvadd(&shared);
                    let equal = lhs.mk_eq(&rhs);
                    if truth {
                        equal
                    } else {
                        equal.mk_not()
                    }
                })
                .collect();
            let before = AST_SIMPLIFY_CALLS.get();
            let actual = assigned_bools(&roots.iter().collect::<Vec<_>>());
            let calls = AST_SIMPLIFY_CALLS.get() - before;
            assert_eq!(actual, expected);
            // 逐位置与独立 Context 的原式比较。若任一真值有误，析取即可满足。
            unsafe {
                let z3 = proof.z3_ctx;
                let check = Z3_mk_solver(z3);
                Z3_solver_inc_ref(z3, check);
                let mut mismatch = Ast::mk_bool(&proof, false);
                for (root, truth) in roots.iter().zip(actual) {
                    let copied = Z3_translate(ctx.z3_ctx, root.z3_ast, z3);
                    Z3_inc_ref(z3, copied);
                    let original = Ast { ctx: &proof, z3_ast: copied };
                    mismatch = mismatch.mk_or(&original.mk_eq(&Ast::mk_bool(&proof, truth)).mk_not());
                }
                Z3_solver_assert(z3, check, mismatch.z3_ast);
                let result = Z3_solver_check(z3, check);
                Z3_solver_dec_ref(z3, check);
                assert_eq!(result, Z3_L_FALSE);
            }
            assert_eq!(calls, 1, "32 个尚未折叠的已赋值布尔根应共用一次原生化简");
        }
    }
}
