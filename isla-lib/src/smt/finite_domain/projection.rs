//! 单锚点投影的依赖索引、稀疏代入和布尔常量折叠。
use super::*;
use prefix_index::ProjectionAsts;

#[derive(Default)]
pub(super) struct AnchorProjection {
    dependencies: HashMap<Z3_ast, bool>,
    // 仅持久保留通向锚点的节点，均由已登记的断言或臂条件保活。
    affected: HashSet<Z3_ast>,
}

#[derive(Clone, Copy)]
pub(super) struct ProjectedFact {
    pub(super) truth: Option<bool>,
    pub(super) literal: Option<Z3_ast>,
    pub(super) unchanged: bool,
}

impl AnchorProjection {
    pub(super) fn contains_anchor(
        &mut self,
        root: Z3_ast,
        anchor: &Ast,
        probe: &Ast,
        independent: &mut HashSet<Z3_ast>,
    ) -> bool {
        if let Some(&found) = self.dependencies.get(&root) {
            return found;
        }
        let ctx = anchor.ctx;
        let z3 = ctx.z3_ctx;
        let mut pending = vec![(root, false)];
        while let Some((node, expanded)) = pending.pop() {
            if independent.contains(&node) || self.affected.contains(&node) {
                continue;
            }
            let found = if node == anchor.z3_ast {
                true
            } else {
                unsafe {
                    match Z3_get_ast_kind(z3, node) {
                        AstKind::Numeral | AstKind::Var => false,
                        AstKind::App => {
                            let app = Z3_to_app(z3, node);
                            let mut children = (0..Z3_get_app_num_args(z3, app)).map(|i| Z3_get_app_arg(z3, app, i));
                            if !expanded {
                                pending.push((node, true));
                                pending.extend(children.map(|child| (child, false)));
                                continue;
                            }
                            children.any(|child| self.affected.contains(&child))
                        }
                        // 带绑定器的子树由 Z3 处理绑定深度及量词模式。
                        _ => {
                            Z3_inc_ref(z3, node);
                            (Ast { ctx, z3_ast: node }).substitute(anchor, probe).z3_ast != node
                        }
                    }
                }
            };
            if found {
                self.affected.insert(node);
            } else {
                independent.insert(node);
            }
        }
        let found = self.affected.contains(&root);
        self.dependencies.insert(root, found);
        found
    }

    pub(super) fn project_assertion<'ctx>(
        &mut self,
        asts: &ProjectionAsts<'ctx>,
        root: Z3_ast,
        anchor: &Ast<'ctx>,
        value: &Ast<'ctx>,
        rebuilt: &mut HashMap<Z3_ast, (Ast<'ctx>, Option<bool>)>,
    ) -> ProjectedFact {
        let replacement = [(anchor.z3_ast, value.z3_ast)];
        let replacements = if value.z3_ast == anchor.z3_ast { &replacement[..0] } else { &replacement };
        if let Some((truth, changed)) = ground::AstEvaluator::new(asts.ctx).evaluate(root, replacements) {
            return ProjectedFact { truth: Some(truth), literal: None, unchanged: !changed };
        }
        let (mut residual, folded) = if value.z3_ast == anchor.z3_ast {
            (asts.get(root), None)
        } else {
            self.rebuild(root, anchor, value, rebuilt)
        };
        let unchanged = residual.z3_ast == root;
        let truth = folded.or_else(|| residual.structural_bool());
        // DeclareConst 的布尔字面量只可能是零元应用或其否定。复杂残余
        // 只记“非字面量”，缓存不保活其表达式。字面量仍在每次调用按当前声明查找。
        let literal = (truth.is_none() && is_literal_shape(&residual)).then(|| asts.keep(residual));
        ProjectedFact { truth, literal, unchanged }
    }

    // 同一候选的断言共用重建的子式。复杂残余继续使用精确的原始结构。
    fn rebuild<'ctx>(
        &self,
        root: Z3_ast,
        anchor: &Ast<'ctx>,
        value: &Ast<'ctx>,
        rebuilt: &mut HashMap<Z3_ast, (Ast<'ctx>, Option<bool>)>,
    ) -> (Ast<'ctx>, Option<bool>) {
        let ctx = anchor.ctx;
        let z3 = ctx.z3_ctx;
        let mut pending = vec![(root, false)];
        while let Some((node, expanded)) = pending.pop() {
            if rebuilt.contains_key(&node) {
                continue;
            }
            if node == anchor.z3_ast {
                rebuilt.insert(node, (value.clone(), value.get_bool_value()));
                continue;
            }
            unsafe {
                if Z3_get_ast_kind(z3, node) != AstKind::App {
                    Z3_inc_ref(z3, node);
                    let residual = (Ast { ctx, z3_ast: node }).substitute(anchor, value);
                    rebuilt.insert(node, (residual, None));
                    continue;
                }
                let app = Z3_to_app(z3, node);
                let children = (0..Z3_get_app_num_args(z3, app)).map(|i| Z3_get_app_arg(z3, app, i));
                if !expanded {
                    pending.push((node, true));
                    pending.extend(children.filter(|k| self.affected.contains(k)).map(|k| (k, false)));
                    continue;
                }
                let args: Vec<_> = children.map(|k| rebuilt.get(&k).map_or(k, |(a, _)| a.z3_ast)).collect();
                let folded = fold_bool(z3, app, &args, rebuilt);
                let replacement = Z3_update_term(z3, node, args.len().try_into().unwrap(), args.as_ptr());
                Z3_inc_ref(z3, replacement);
                rebuilt.insert(node, (Ast { ctx, z3_ast: replacement }, folded));
            }
        }
        rebuilt[&root].clone()
    }

    pub(super) fn heap_bytes(&self) -> usize {
        use crate::executor::stats::memory_stats::map_bytes;
        map_bytes::<Z3_ast, bool>(self.dependencies.capacity()) + map_bytes::<Z3_ast, ()>(self.affected.capacity())
    }
}

fn is_literal_shape(ast: &Ast) -> bool {
    unsafe {
        let z3 = ast.ctx.z3_ctx;
        let atom =
            if ast.rewrite_kind(DeclKind::NOT) { Z3_get_app_arg(z3, Z3_to_app(z3, ast.z3_ast), 0) } else { ast.z3_ast };
        Z3_get_ast_kind(z3, atom) == AstKind::App && Z3_get_app_num_args(z3, Z3_to_app(z3, atom)) == 0
    }
}

// 只折叠 Z3 化简器直接消去的常量布尔运算。未判定时返回原始代入式，
// 保留 structural_bool 的比较识别能力以及化简后的字面量。
unsafe fn fold_bool(
    z3: Z3_context,
    app: Z3_app,
    args: &[Z3_ast],
    rebuilt: &HashMap<Z3_ast, (Ast<'_>, Option<bool>)>,
) -> Option<bool> {
    let kind = rewrite::decl_kind_raw(z3, Z3_get_app_decl(z3, app));
    let child = |i: usize| {
        let original = Z3_get_app_arg(z3, app, i as u32);
        rebuilt.get(&original).and_then(|(_, b)| *b).or_else(|| match Z3_get_bool_value(z3, args[i]) {
            Z3_L_TRUE => Some(true),
            Z3_L_FALSE => Some(false),
            _ => None,
        })
    };
    if kind == DeclKind::EQ as u32 {
        if args[0] == args[1] {
            return Some(true);
        }
        if Z3_is_numeral_ast(z3, args[0])
            && Z3_is_numeral_ast(z3, args[1])
            && Z3_get_sort_kind(z3, Z3_get_sort(z3, args[0])) == SortKind::BV
        {
            return Some(false);
        }
    } else if kind == DeclKind::NOT as u32 {
        return child(0).map(|b| !b);
    } else if kind == DeclKind::ITE as u32 {
        return child(if child(0)? { 1 } else { 2 });
    } else if kind == DeclKind::AND as u32 || kind == DeclKind::OR as u32 {
        let absorbing = kind == DeclKind::OR as u32;
        let mut all_constant = true;
        for i in 0..args.len() {
            match child(i) {
                Some(b) if b == absorbing => return Some(b),
                None => all_constant = false,
                _ => (),
            }
        }
        return all_constant.then_some(!absorbing);
    }
    None
}
