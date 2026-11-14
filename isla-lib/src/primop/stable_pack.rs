//! 保序打包：选中元素按原下标连续放在低下标，尾部保留old。
use super::*;

pub(super) fn stable_pack<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if args.len() != 3 {
        return Err(ExecError::Type("stable_pack requires mask, source and old vectors".to_string(), info));
    }
    let mut args = args.into_iter();
    let mask = expect_bits_arg(args.next().unwrap(), "stable_pack mask", solver, info)?;
    let (Val::Vector(source), Val::Vector(old)) = (args.next().unwrap(), args.next().unwrap()) else {
        return Err(ExecError::Type("stable_pack requires vectors".to_string(), info));
    };
    let n = length_bits(&mask, solver, info)?;
    if source.len() != n as usize || old.len() != n as usize {
        return Err(ExecError::Type("stable_pack requires matching mask and vector lengths".to_string(), info));
    }
    if n == 0 {
        return Ok(Val::Vector(Vec::new()));
    }
    let source = source
        .into_iter()
        .map(|x| expect_bits_arg(x, "stable_pack source", solver, info))
        .collect::<Result<Vec<_>, _>>()?;
    let old =
        old.into_iter().map(|x| expect_bits_arg(x, "stable_pack old", solver, info)).collect::<Result<Vec<_>, _>>()?;
    let width = length_bits(&source[0], solver, info)?;
    if width == 0 {
        return Err(ExecError::Type("stable_pack requires positive-width elements".to_string(), info));
    }
    for value in source.iter().chain(old.iter()) {
        if length_bits(value, solver, info)? != width {
            return Err(ExecError::Type("stable_pack requires equal-width elements".to_string(), info));
        }
    }
    let total = n
        .checked_mul(width)
        .ok_or_else(|| ExecError::Type("stable_pack result width exceeds u32".to_string(), info))?;
    if let Val::Bits(mask) = mask {
        let mut result: Vec<_> = source
            .into_iter()
            .enumerate()
            .filter(|(i, _)| mask.slice(*i as u32, 1).unwrap().lower_u64() != 0)
            .map(|(_, x)| x)
            .collect();
        result.extend(old.into_iter().skip(result.len()));
        return Ok(Val::Vector(result));
    }
    let mask = smt_value(&mask, info)?;
    let count_width = u32::BITS - n.leading_zeros();
    let resize_count = |count, target| {
        if target > count_width {
            Exp::ZeroExtend(target - count_width, Box::new(Exp::Var(count)))
        } else if target < count_width {
            Exp::Extract(target - 1, 0, Box::new(Exp::Var(count)))
        } else {
            Exp::Var(count)
        }
    };
    // 每块的低count*W位是连续有效数据，其余位为零。
    let mut blocks = Vec::with_capacity(n as usize);
    for (i, value) in source.iter().enumerate() {
        let bit = Exp::Extract(i as u32, i as u32, Box::new(mask.clone()));
        let count = solver.define_bitvector(
            if count_width == 1 { bit.clone() } else { Exp::ZeroExtend(count_width - 1, Box::new(bit.clone())) },
            info,
        );
        let data = solver.define_bitvector(
            Exp::Ite(
                Box::new(Exp::Eq(Box::new(bit), Box::new(smt_u64_width(1, 1)))),
                Box::new(smt_value(value, info)?),
                Box::new(smt_zeros(width.into())),
            ),
            info,
        );
        blocks.push((data, count, width));
    }
    while blocks.len() > 1 {
        let mut next = Vec::with_capacity(blocks.len().div_ceil(2));
        for pair in blocks.chunks(2) {
            if pair.len() == 1 {
                next.push(pair[0]);
                continue;
            }
            let (left, left_count, left_width) = pair[0];
            let (right, right_count, right_width) = pair[1];
            let block_width = left_width + right_width;
            let shift = Exp::Bvmul(
                Box::new(resize_count(left_count, block_width)),
                Box::new(smt_u64_width(width as u64, block_width)),
            );
            let joined = Exp::Bvor(
                Box::new(Exp::ZeroExtend(right_width, Box::new(Exp::Var(left)))),
                Box::new(Exp::Bvshl(Box::new(Exp::ZeroExtend(left_width, Box::new(Exp::Var(right)))), Box::new(shift))),
            );
            let data = solver.define_bitvector(joined, info);
            let count = solver
                .define_bitvector(Exp::Bvadd(Box::new(Exp::Var(left_count)), Box::new(Exp::Var(right_count))), info);
            next.push((data, count, block_width));
        }
        blocks = next;
    }
    let (packed, count, packed_width) = blocks.pop().unwrap();
    assert_eq!(packed_width, total, "递归打包宽度必须守恒");
    let mut old_bits = smt_value(old.last().unwrap(), info)?;
    for value in old.iter().rev().skip(1) {
        old_bits = Exp::Concat(Box::new(old_bits), Box::new(smt_value(value, info)?));
    }
    let tail = Exp::Bvshl(
        Box::new(smt_ones(total.into())),
        Box::new(Exp::Bvmul(Box::new(resize_count(count, total)), Box::new(smt_u64_width(width as u64, total)))),
    );
    let result = solver.define_bitvector(
        Exp::Bvor(Box::new(Exp::Var(packed)), Box::new(Exp::Bvand(Box::new(old_bits), Box::new(tail)))),
        info,
    );
    Ok(Val::Vector(
        (0..n)
            .map(|i| {
                Val::Symbolic(
                    solver.define_bitvector(
                        Exp::Extract((i + 1) * width - 1, i * width, Box::new(Exp::Var(result))),
                        info,
                    ),
                )
            })
            .collect(),
    ))
}
