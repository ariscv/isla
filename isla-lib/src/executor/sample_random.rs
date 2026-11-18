//! 样本求解模型中完全无约束的标量由 Isla 随机填值。
use super::*;
use crate::smt::{smtlib::Def, ModelVal};

/// 先读取非补全模型，固定随机相位见证并填充任意变量，最后只检查一次。
/// 调用者须使用独立导出求解器，并已在 condition 下取得 Sat 模型。
pub fn fill_arbitrary_inputs<B: BV>(
    solver: &mut Solver<B>,
    condition: &Exp<Sym>,
    random: &mut impl FnMut() -> u64,
) -> Result<(), ExecError> {
    let mut equalities = Vec::new();
    let mut model = Model::new(solver);
    // 事件声明序稳定，且每个声明只填一次；别名与派生表达式由最终模型重新计算。
    for event in solver.trace().to_vec().into_iter().rev() {
        let (symbol, declared) = match event {
            Event::Smt(Def::DeclareConst(symbol, _), ..) => (*symbol, true),
            Event::Smt(Def::DefineConst(symbol, _), ..) => (*symbol, false),
            _ => continue,
        };
        if !matches!(solver.scalar_sort(symbol), Some(crate::smt::smtlib::Ty::Bool | crate::smt::smtlib::Ty::BitVec(_)))
        {
            continue;
        }
        let concrete = match model.get_var(symbol)? {
            // 保留首次随机相位产生的见证，包括数组读取的标量结果。
            // 否则最终检查会重新选模型，受到模型读取过程中 AST 分配的影响。
            ModelVal::Exp(value) => value,
            // 任意派生表达式可能与其它字段共用输入；只随机填底层声明。
            ModelVal::Arbitrary(_) if !declared => continue,
            ModelVal::Arbitrary(ty) => match ty {
                crate::smt::smtlib::Ty::Bool => Exp::Bool(random() & 1 != 0),
                crate::smt::smtlib::Ty::BitVec(width) => {
                    let mut bits = Vec::with_capacity(width as usize);
                    while bits.len() < width as usize {
                        let word = random();
                        let count = (width as usize - bits.len()).min(64);
                        bits.extend((0..count).map(|bit| (word >> bit) & 1 != 0));
                    }
                    Exp::Bits(bits)
                }
                ty => panic!("任意标量类型不符：{ty:?}"),
            },
        };
        equalities.push(Exp::Eq(Box::new(Exp::Var(symbol)), Box::new(concrete)));
    }
    drop(model);
    solver.assert(condition.clone());
    for equality in equalities {
        solver.assert(equality);
    }
    assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat, "无约束变量填值不得破坏路径与所属类约束");
    Ok(())
}
