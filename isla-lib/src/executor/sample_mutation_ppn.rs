//! 分页变异的取值偏好；只改变求解输入，不改变模型或差异规则。
use super::*;

impl<B: BV> PathMutator<B> {
    pub(super) fn leaf_ppn_preferences(&self) -> Vec<(usize, Exp<Sym>, Exp<Sym>)> {
        self.fields
            .iter()
            .enumerate()
            .filter_map(|(i, field)| {
                // 当前分页 LOAD/STORE 的 PTE 是参与守卫判定的 64 位读取；
                // 普通数据读取只进入结果，不参与这些守卫，不能施加 PTE 偏好。
                if !field.name.starts_with("read.")
                    || field.width != Some(64)
                    || !field.atoms.iter().any(|atoms| self.guard_atoms.iter().any(|guard| !atoms.is_disjoint(guard)))
                {
                    return None;
                }
                let leaf = conjunction([
                    field.active.clone(),
                    Exp::Eq(Box::new(Exp::Extract(0, 0, Box::new(field.expression.clone()))), Box::new(bits64(1, 1))),
                    Exp::Neq(Box::new(Exp::Extract(2, 1, Box::new(field.expression.clone()))), Box::new(bits64(2, 2))),
                    Exp::Neq(
                        Box::new(Exp::Bvand(Box::new(field.expression.clone()), Box::new(bits64(0xa, 64)))),
                        Box::new(bits64(0, 64)),
                    ),
                ]);
                let preference = Exp::Or(
                    Box::new(Exp::Not(Box::new(leaf.clone()))),
                    Box::new(Exp::Eq(
                        Box::new(Exp::Extract(53, 46, Box::new(field.expression.clone()))),
                        Box::new(bits64(0, 8)),
                    )),
                );
                Some((i, leaf, preference))
            })
            .collect()
    }
}
