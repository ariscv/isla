//! class_cap=1 的规范见证：按固定顺序选择满足原类约束的最小有限域值。
use super::*;

/// 在已固定的前缀下选最小标量。每次只增加由 SAT 证明可行的见证约束。
/// 位向量按无符号数序（含任意位宽），布尔 false 优先，枚举按声明成员序。
pub(super) fn canonical_value<B: BV>(
    solver: &mut Solver<B>,
    expression: Formula<Sym>,
    condition: &mut Formula<Sym>,
    shared: &SharedState<B>,
) -> Result<(), ExecError> {
    use Formula::*;
    assert!(satisfiable(solver, condition)?, "规范见证的前缀必须可满足");
    let mut model = Model::new(solver);
    model.set_complete_model(true);
    let witness = model.get_exp(&expression)?.unwrap_exp();
    drop(model);
    let equality = |value| Eq(Box::new(expression.clone()), Box::new(value));
    let extend = |condition: &Formula<Sym>, value| And(Box::new(condition.clone()), Box::new(value));
    let minimum = match &witness {
        Bool(_) => Bool(false),
        Bits64(bits) => Bits(vec![false; bits.len() as usize]),
        Bits(bits) => Bits(vec![false; bits.len()]),
        Enum(member) => Enum(crate::smt::EnumMember { enum_id: member.enum_id, member: 0 }),
        value => panic!("规范见证必须为有限域标量：{value:?}"),
    };
    if witness == minimum || satisfiable(solver, &extend(condition, equality(minimum.clone())))? {
        *condition = extend(condition, equality(minimum));
        return Ok(());
    }
    // 多数状态受原约束唯一确定；先证明唯一，避免逐位查询具体寄存器和地址。
    if !satisfiable(solver, &extend(condition, Not(Box::new(equality(witness.clone())))))? {
        *condition = extend(condition, equality(witness));
        return Ok(());
    }
    if let Enum(member) = witness {
        for index in 1..shared.type_info.enums[&member.enum_id.to_name()].len() {
            let value = Enum(crate::smt::EnumMember { enum_id: member.enum_id, member: index });
            if satisfiable(solver, &extend(condition, equality(value.clone())))? {
                *condition = extend(condition, equality(value));
                return Ok(());
            }
        }
        unreachable!("可满足枚举必须存在成员");
    }
    if matches!(witness, Bool(true)) {
        *condition = extend(condition, equality(Bool(true)));
        return Ok(());
    }
    let mut bits = bits_text(&witness).as_bytes()[2..].iter().map(|bit| *bit == b'1').collect::<Vec<_>>();
    let width = bits.len();
    for index in 0..width {
        if bits[index] {
            let mut prefix = bits[..=index].to_vec();
            prefix[index] = false;
            prefix.reverse();
            let zero = Eq(
                Box::new(Extract(width as u32 - 1, (width - index - 1) as u32, Box::new(expression.clone()))),
                Box::new(Bits(prefix)),
            );
            if satisfiable(solver, &extend(condition, zero))? {
                let mut model = Model::new(solver);
                model.set_complete_model(true);
                bits = bits_text(&model.get_exp(&expression)?.unwrap_exp()).as_bytes()[2..]
                    .iter()
                    .map(|bit| *bit == b'1')
                    .collect();
            }
        }
    }
    bits.reverse();
    *condition = extend(condition, equality(Bits(bits)));
    Ok(())
}
