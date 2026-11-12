//! 有限全域查表和 exclusive 前缀计数。接口只描述数学运算，表由调用者提供。
use super::*;

/// K位无符号索引选择2^K项中的一项，vector下标0对应索引0。
/// 要求K>0、表长恰为2^K、表项为同一正位宽；域不匹配直接报类型错误。
/// 直接按索引位建立平衡选择树，不经过Sail整数转换或索引范围查询。
pub(super) fn lookup_bits<B: BV>(
    index: Val<B>,
    table: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let index = expect_bits_arg(index, "lookup_bits index", solver, info)?;
    let width = length_bits(&index, solver, info)?;
    let Val::Vector(table) = table else {
        return Err(ExecError::Type("lookup_bits requires a vector table".to_string(), info));
    };
    if width == 0 || width >= usize::BITS || table.len() != (1usize << width) {
        return Err(ExecError::Type(
            "lookup_bits requires exactly 2^K entries for a positive K-bit index".to_string(),
            info,
        ));
    }
    let mut values = table
        .into_iter()
        .map(|value| expect_bits_arg(value, "lookup_bits entry", solver, info))
        .collect::<Result<Vec<_>, _>>()?;
    let output_width = length_bits(&values[0], solver, info)?;
    if output_width == 0 {
        return Err(ExecError::Type("lookup_bits requires positive-width entries".to_string(), info));
    }
    for value in &values[1..] {
        if length_bits(value, solver, info)? != output_width {
            return Err(ExecError::Type("lookup_bits requires equal-width entries".to_string(), info));
        }
    }
    if let Val::Bits(index) = index {
        return Ok(values.swap_remove(index.lower_u64() as usize));
    }
    let index = smt_value(&index, info)?;
    for bit in 0..width {
        let cond = solver.define_const(
            Exp::Eq(Box::new(Exp::Extract(bit, bit, Box::new(index.clone()))), Box::new(smt_u64_width(1, 1))),
            info,
        );
        values = values
            .chunks_exact(2)
            .map(|pair| {
                if pair[0] == pair[1] {
                    Ok(pair[0].clone())
                } else {
                    Ok(Val::Symbolic(solver.define_bitvector(
                        Exp::Ite(
                            Box::new(Exp::Var(cond)),
                            Box::new(smt_value(&pair[1], info)?),
                            Box::new(smt_value(&pair[0], info)?),
                        ),
                        info,
                    )))
                }
            })
            .collect::<Result<Vec<_>, ExecError>>()?;
    }
    Ok(values.pop().expect("全域二叉选择最终恰有一个结果"))
}

/// 输出p[i]=sum(q[0..i]) mod 2^M（不包含q[i]）。q可以是零宽，M必须为正。
/// 共享ceil(log2(N+1))位前缀；只在输出处截断或零扩展，不添加输入约束。
pub(super) fn prefix_popcount<B: BV>(
    bits: Val<B>,
    output_width: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let bits = expect_bits_arg(bits, "prefix_popcount", solver, info)?;
    let output_width = expect_i128_arg(&output_width, "prefix_popcount output width", solver, info)?;
    let output_width = u32::try_from(output_width)
        .ok()
        .filter(|width| *width > 0)
        .ok_or_else(|| ExecError::Type("prefix_popcount requires a positive output width".to_string(), info))?;
    let n = length_bits(&bits, solver, info)?;
    let mut result = Vec::with_capacity(n as usize);
    if let Val::Bits(bits) = bits {
        let mut count = 0u64;
        for i in 0..n {
            if output_width <= B::MAX_WIDTH {
                let truncated = if output_width < 64 { count & (u64::MAX >> (64 - output_width)) } else { count };
                result.push(Val::Bits(B::new(truncated, output_width)));
            } else {
                result.push(Val::Symbolic(
                    solver
                        .define_bitvector(Exp::ZeroExtend(output_width - 32, Box::new(smt_u64_width(count, 32))), info),
                ));
            }
            count += bits.slice(i, 1).expect("已检查前缀输入位宽").lower_u64();
        }
    } else if n > 0 {
        let count_width = (u32::BITS - n.leading_zeros()).max(1);
        let input = smt_value(&bits, info)?;
        let mut count = solver.define_bitvector(smt_zeros(count_width.into()), info);
        for i in 0..n {
            let output = if output_width < count_width {
                Exp::Extract(output_width - 1, 0, Box::new(Exp::Var(count)))
            } else if output_width > count_width {
                Exp::ZeroExtend(output_width - count_width, Box::new(Exp::Var(count)))
            } else {
                Exp::Var(count)
            };
            result.push(Val::Symbolic(solver.define_bitvector(output, info)));
            if i + 1 < n {
                let bit = Exp::Extract(i, i, Box::new(input.clone()));
                let increment = if count_width == 1 { bit } else { Exp::ZeroExtend(count_width - 1, Box::new(bit)) };
                count = solver.define_bitvector(Exp::Bvadd(Box::new(Exp::Var(count)), Box::new(increment)), info);
            }
        }
    }
    Ok(Val::Vector(result))
}
