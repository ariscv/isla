//! 步骤3–4：通过注册入口核对有限查表及共享 exclusive 前缀。
use super::*;
use crate::bitvector::b129::B129;

fn context() -> Context {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let mut config = Config::new();
    config.set_param_value("timeout", "10000");
    Context::new(config)
}

#[test]
fn vector_bits_registration_is_pure() {
    for name in ["lookup_bits", "prefix_popcount"] {
        assert!(binary_primops::<B129>().contains_key(name));
        assert_eq!(effect(name), Some(Effect::Pure));
    }
}

#[test]
fn vector_bits_lookup_concrete_and_invalid_domains() -> Result<(), ExecError> {
    let ctx = context();
    let mut solver = Solver::<B129>::new(&ctx);
    let info = SourceLoc::unknown();
    let lookup = binary_primops::<B129>()["lookup_bits"];
    for index_width in [1, 3, 5, 8] {
        let table: Vec<_> = (0..1 << index_width).map(|i| Val::Bits(B129::new(i * 7, 16))).collect();
        for index in 0..table.len() {
            assert_eq!(
                lookup(Val::Bits(B129::new(index as u64, index_width)), Val::Vector(table.clone()), &mut solver, info)?,
                table[index]
            );
        }
    }
    for table in
        [vec![], vec![Val::Bits(B129::zeros(8)); 3], vec![Val::Bits(B129::zeros(8)), Val::Bits(B129::zeros(16))]]
    {
        assert!(lookup(Val::Bits(B129::zeros(1)), Val::Vector(table), &mut solver, info).is_err());
    }
    assert!(lookup(Val::Bits(B129::zeros(0)), Val::Vector(vec![Val::Bits(B129::zeros(8))]), &mut solver, info).is_err());
    Ok(())
}

#[test]
fn vector_bits_lookup_symbolic_matches_linear_selection() -> Result<(), ExecError> {
    let ctx = context();
    let info = SourceLoc::unknown();
    let lookup = binary_primops::<B64>()["lookup_bits"];
    for (index_width, output_width) in [(1, 8), (3, 128), (5, 32), (8, 8)] {
        let mut solver = Solver::<B64>::new(&ctx);
        let index = solver.declare_bitvector(index_width, info);
        let table: Vec<_> =
            (0..1 << index_width).map(|_| Val::Symbolic(solver.declare_bitvector(output_width, info))).collect();
        let result = lookup(Val::Symbolic(index), Val::Vector(table.clone()), &mut solver, info)?;
        // 旧vector_access的合法索引域：整数索引零扩展到128位。
        let old_index = solver.define_bitvector(Exp::ZeroExtend(128 - index_width, Box::new(Exp::Var(index))), info);
        let reference = vector_access(Val::Vector(table.clone()), Val::Symbolic(old_index), &mut solver, info)?;
        assert_eq!(
            solver.check_sat_with(
                &Exp::Neq(Box::new(smt_value(&result, info)?), Box::new(smt_value(&reference, info)?)),
                info
            ),
            SmtResult::Unsat
        );
        // 具体/符号拼接索引也走相同顺序。
        if index_width > 1 {
            let mixed = Val::MixedBits(vec![
                BitsSegment::Concrete(B64::zeros(1)),
                BitsSegment::Symbolic(
                    solver.define_bitvector(Exp::Extract(index_width - 2, 0, Box::new(Exp::Var(index))), info),
                ),
            ]);
            let mixed_result = lookup(mixed, Val::Vector(table.clone()), &mut solver, info)?;
            let masked = solver.define_bitvector(
                Exp::Bvand(
                    Box::new(Exp::Var(index)),
                    Box::new(smt_u64_width((1 << (index_width - 1)) - 1, index_width)),
                ),
                info,
            );
            let expected = lookup(Val::Symbolic(masked), Val::Vector(table), &mut solver, info)?;
            assert_eq!(
                solver.check_sat_with(
                    &Exp::Neq(Box::new(smt_value(&mixed_result, info)?), Box::new(smt_value(&expected, info)?)),
                    info
                ),
                SmtResult::Unsat
            );
        }
    }
    Ok(())
}

#[test]
fn vector_bits_prefix_exhaustive_and_truncation() -> Result<(), ExecError> {
    let ctx = context();
    let info = SourceLoc::unknown();
    let mut solver = Solver::<B129>::new(&ctx);
    let prefix = binary_primops::<B129>()["prefix_popcount"];
    for n in 0..=8 {
        for input in 0..1u64 << n {
            for width in [1, 4, 8, 16, 64] {
                let Val::Vector(result) =
                    prefix(Val::Bits(B129::new(input, n)), Val::I128(width.into()), &mut solver, info)?
                else {
                    panic!("前缀结果必须是vector")
                };
                let mut sum = 0;
                assert_eq!(result.len(), n as usize);
                for i in 0..n {
                    assert_eq!(result[i as usize], Val::Bits(B129::new(sum & (u64::MAX >> (64 - width)), width)));
                    sum += (input >> i) & 1;
                }
            }
        }
    }
    assert!(prefix(Val::Bits(B129::zeros(8)), Val::I128(0), &mut solver, info).is_err());
    Ok(())
}

#[test]
fn vector_bits_prefix_symbolic_old_integer_invariant_and_mask() -> Result<(), ExecError> {
    let ctx = context();
    let info = SourceLoc::unknown();
    for n in [1, 2, 4, 8, 16, 32, 64, 128] {
        for width in [1, 4, 8, 16, 32, 64, 128] {
            let mut solver = Solver::<B64>::new(&ctx);
            let source = solver.declare_bitvector(n, info);
            let mask = solver.declare_bitvector(n, info);
            let active =
                solver.define_bitvector(Exp::Bvand(Box::new(Exp::Var(source)), Box::new(Exp::Var(mask))), info);
            let Val::Vector(result) = binary_primops::<B64>()["prefix_popcount"](
                Val::Symbolic(active),
                Val::I128(width.into()),
                &mut solver,
                info,
            )?
            else {
                panic!("前缀结果必须是vector")
            };
            let mut sum = solver.define_bitvector(smt_zeros(128), info);
            let old = solver.declare_bitvector(width, info);
            for i in 0..n {
                let expected =
                    if width == 128 { Exp::Var(sum) } else { Exp::Extract(width - 1, 0, Box::new(Exp::Var(sum))) };
                let cond =
                    Exp::Eq(Box::new(Exp::Extract(i, i, Box::new(Exp::Var(mask)))), Box::new(smt_u64_width(1, 1)));
                let actual = Exp::Ite(
                    Box::new(cond.clone()),
                    Box::new(smt_value(&result[i as usize], info)?),
                    Box::new(Exp::Var(old)),
                );
                let expected = Exp::Ite(Box::new(cond.clone()), Box::new(expected), Box::new(Exp::Var(old)));
                assert_eq!(
                    solver.check_sat_with(&Exp::Neq(Box::new(actual), Box::new(expected)), info),
                    SmtResult::Unsat,
                    "N={n},M={width},i={i}"
                );
                // 原Sail在活动位置、源位为1时才增加128位整数sum。
                let bit = Exp::Bvand(
                    Box::new(Exp::Extract(i, i, Box::new(Exp::Var(source)))),
                    Box::new(Exp::Extract(i, i, Box::new(Exp::Var(mask)))),
                );
                sum = solver.define_bitvector(
                    Exp::Bvadd(Box::new(Exp::Var(sum)), Box::new(Exp::ZeroExtend(127, Box::new(bit)))),
                    info,
                );
            }
        }
    }
    Ok(())
}

fn stable_pack_call(args: Vec<Val<B129>>, solver: &mut Solver<B129>) -> Result<Val<B129>, ExecError> {
    let mut frame = LocalFrame::new(crate::ir::Name::from_u32(0), &[], &crate::ir::Ty::Unit, None, &[]);
    variadic_primops::<B129>()["stable_pack"](args, solver, &mut frame, SourceLoc::unknown())
}

#[test]
fn vector_stable_pack_exhaustive_masks_and_domains() -> Result<(), ExecError> {
    assert_eq!(effect("stable_pack"), Some(Effect::Pure));
    let ctx = context();
    let mut solver = Solver::<B129>::new(&ctx);
    for n in 0..=8 {
        let src: Vec<_> = (0..n).map(|i| Val::Bits(B129::new(i as u64 + 1, 8))).collect();
        let old: Vec<_> = (0..n).map(|i| Val::Bits(B129::new(i as u64 + 0x80, 8))).collect();
        for mask in 0..1u64 << n {
            let mut expected: Vec<_> = (0..n).filter(|i| mask >> i & 1 == 1).map(|i| src[i as usize].clone()).collect();
            expected.extend_from_slice(&old[expected.len()..]);
            assert_eq!(
                stable_pack_call(
                    vec![Val::Bits(B129::new(mask, n)), Val::Vector(src.clone()), Val::Vector(old.clone())],
                    &mut solver
                )?,
                Val::Vector(expected)
            );
        }
    }
    assert!(stable_pack_call(vec![Val::Bits(B129::zeros(1)), Val::Vector(vec![]), Val::Vector(vec![])], &mut solver)
        .is_err());
    assert!(stable_pack_call(
        vec![
            Val::Bits(B129::zeros(1)),
            Val::Vector(vec![Val::Bits(B129::zeros(8))]),
            Val::Vector(vec![Val::Bits(B129::zeros(16))])
        ],
        &mut solver
    )
    .is_err());
    Ok(())
}

#[test]
fn vector_stable_pack_symbolic_matches_old_scatter() -> Result<(), ExecError> {
    let ctx = context();
    let loc = SourceLoc::unknown();
    for n in [1, 2, 3, 4, 8] {
        let mut solver = Solver::<B129>::new(&ctx);
        let q = solver.declare_bitvector(n, loc);
        let src: Vec<_> = (0..n).map(|_| Val::Symbolic(solver.declare_bitvector(8, loc))).collect();
        let old: Vec<_> = (0..n).map(|_| Val::Symbolic(solver.declare_bitvector(8, loc))).collect();
        let Val::Vector(result) =
            stable_pack_call(vec![Val::Symbolic(q), Val::Vector(src.clone()), Val::Vector(old.clone())], &mut solver)?
        else {
            panic!("pack必须返回vector")
        };
        let mut expected: Vec<_> = old.iter().map(|x| smt_value(x, loc)).collect::<Result<_, _>>()?;
        let mut count = solver.define_bitvector(smt_zeros(128), loc);
        for j in 0..n {
            let bit = Exp::Extract(j, j, Box::new(Exp::Var(q)));
            for i in 0..n {
                let selected = Exp::And(
                    Box::new(Exp::Eq(Box::new(bit.clone()), Box::new(smt_u64_width(1, 1)))),
                    Box::new(Exp::Eq(Box::new(Exp::Var(count)), Box::new(smt_u64_width(i as u64, 128)))),
                );
                expected[i as usize] = Exp::Ite(
                    Box::new(selected),
                    Box::new(smt_value(&src[j as usize], loc)?),
                    Box::new(expected[i as usize].clone()),
                );
            }
            count = solver.define_bitvector(
                Exp::Bvadd(Box::new(Exp::Var(count)), Box::new(Exp::ZeroExtend(127, Box::new(bit)))),
                loc,
            );
        }
        for i in 0..n as usize {
            assert_eq!(
                solver.check_sat_with(
                    &Exp::Neq(Box::new(smt_value(&result[i], loc)?), Box::new(expected[i].clone())),
                    loc
                ),
                SmtResult::Unsat,
                "N={n},i={i}"
            );
        }
    }
    Ok(())
}

#[test]
fn vector_stable_pack_maximum_shape_and_tail() -> Result<(), ExecError> {
    let ctx = context();
    let loc = SourceLoc::unknown();
    let n = 128;
    let mut solver = Solver::<B129>::new(&ctx);
    let q = solver.declare_bitvector(n, loc);
    let src: Vec<_> = (0..n).map(|_| Val::Symbolic(solver.declare_bitvector(8, loc))).collect();
    let old: Vec<_> = (0..n).map(|_| Val::Symbolic(solver.declare_bitvector(8, loc))).collect();
    let Val::Vector(result) =
        stable_pack_call(vec![Val::Symbolic(q), Val::Vector(src.clone()), Val::Vector(old.clone())], &mut solver)?
    else {
        panic!("pack必须返回vector")
    };
    let cp = crate::smt::checkpoint(&mut solver);
    assert!(cp.trace().as_ref().unwrap().to_vec().len() < 12 * n as usize + 10, "最大构造的定义数量应为线性");
    for mask in [0u128, u128::MAX, 1u128 << 127, 0xaaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa] {
        let tx = solver.start_transaction();
        let bits = B129::from_str(&format!("#b{mask:0128b}")).unwrap();
        solver.assert_eq(Exp::Var(q), smt_value(&Val::Bits(bits), loc)?);
        let selected: Vec<_> = (0..n as usize).filter(|i| mask >> i & 1 == 1).map(|i| src[i].clone()).collect();
        for i in 0..n as usize {
            let expected = if i < selected.len() { &selected[i] } else { &old[i] };
            assert_eq!(
                solver.check_sat_with(
                    &Exp::Neq(Box::new(smt_value(&result[i], loc)?), Box::new(smt_value(expected, loc)?)),
                    loc
                ),
                SmtResult::Unsat,
                "mask={mask:x},i={i}"
            );
        }
        solver.rollback_transaction(tx);
    }
    Ok(())
}

#[test]
fn vector_stable_pack_merge_invariant_at_actual_shapes() {
    let ctx = context();
    let loc = SourceLoc::unknown();
    for width in [8u32, 16, 32, 64] {
        for n in [2u32, 4, 8, 16, 32, 64, 128] {
            if n * width > 1024 {
                continue;
            }
            let mut solver = Solver::<B129>::new(&ctx);
            let cw = u32::BITS - n.leading_zeros();
            let half = n / 2;
            let part = half * width;
            let total = n * width;
            let cl = solver.declare_bitvector(cw, loc);
            let cr = solver.declare_bitvector(cw, loc);
            let i = solver.declare_bitvector(cw, loc);
            solver.assert(Exp::Bvule(Box::new(Exp::Var(cl)), Box::new(smt_u64_width(half as u64, cw))));
            solver.assert(Exp::Bvule(Box::new(Exp::Var(cr)), Box::new(smt_u64_width(half as u64, cw))));
            solver.assert(Exp::Bvult(Box::new(Exp::Var(i)), Box::new(smt_u64_width(n as u64, cw))));
            let resize = |x, target| Exp::ZeroExtend(target - cw, Box::new(Exp::Var(x)));
            let offset =
                |x, target| Exp::Bvmul(Box::new(resize(x, target)), Box::new(smt_u64_width(width as u64, target)));
            let left_input = solver.declare_bitvector(part, loc);
            let right_input = solver.declare_bitvector(part, loc);
            let left = solver.define_bitvector(
                Exp::Bvand(
                    Box::new(Exp::Var(left_input)),
                    Box::new(Exp::Bvnot(Box::new(Exp::Bvshl(
                        Box::new(smt_ones(part.into())),
                        Box::new(offset(cl, part)),
                    )))),
                ),
                loc,
            );
            let right = solver.define_bitvector(
                Exp::Bvand(
                    Box::new(Exp::Var(right_input)),
                    Box::new(Exp::Bvnot(Box::new(Exp::Bvshl(
                        Box::new(smt_ones(part.into())),
                        Box::new(offset(cr, part)),
                    )))),
                ),
                loc,
            );
            let joined = solver.define_bitvector(
                Exp::Bvor(
                    Box::new(Exp::ZeroExtend(part, Box::new(Exp::Var(left)))),
                    Box::new(Exp::Bvshl(
                        Box::new(Exp::ZeroExtend(part, Box::new(Exp::Var(right)))),
                        Box::new(offset(cl, total)),
                    )),
                ),
                loc,
            );
            let actual = Exp::Extract(
                width - 1,
                0,
                Box::new(Exp::Bvlshr(Box::new(Exp::Var(joined)), Box::new(offset(i, total)))),
            );
            let from_left = Exp::Extract(
                width - 1,
                0,
                Box::new(Exp::Bvlshr(
                    Box::new(Exp::ZeroExtend(part, Box::new(Exp::Var(left)))),
                    Box::new(offset(i, total)),
                )),
            );
            let right_offset = Exp::Bvmul(
                Box::new(Exp::Bvsub(Box::new(resize(i, total)), Box::new(resize(cl, total)))),
                Box::new(smt_u64_width(width as u64, total)),
            );
            let from_right = Exp::Extract(
                width - 1,
                0,
                Box::new(Exp::Bvlshr(
                    Box::new(Exp::ZeroExtend(part, Box::new(Exp::Var(right)))),
                    Box::new(right_offset),
                )),
            );
            let within_left = Exp::Bvult(Box::new(Exp::Var(i)), Box::new(Exp::Var(cl)));
            let sum = Exp::Bvadd(Box::new(Exp::Var(cl)), Box::new(Exp::Var(cr)));
            let within_total = Exp::Bvult(Box::new(Exp::Var(i)), Box::new(sum));
            let otherwise = Exp::Ite(Box::new(within_total), Box::new(from_right), Box::new(smt_zeros(width.into())));
            let expected = Exp::Ite(Box::new(within_left), Box::new(from_left), Box::new(otherwise));
            assert_eq!(
                solver.check_sat_with(&Exp::Neq(Box::new(actual), Box::new(expected)), loc),
                SmtResult::Unsat,
                "merge N={n},W={width}"
            );
        }
    }
}

#[test]
fn vector_stable_pack_active_mask_matches_old_loop_for_all_vl() -> Result<(), ExecError> {
    let ctx = context();
    let loc = SourceLoc::unknown();
    for n in [1u32, 2, 4, 8, 16, 32, 64, 128] {
        let mut solver = Solver::<B129>::new(&ctx);
        let vl = solver.declare_bitvector(64, loc);
        let source = solver.declare_bitvector(n, loc);
        let limit = solver.define_bitvector(Exp::ZeroExtend(64, Box::new(Exp::Var(vl))), loc);
        let end = solver.define_bitvector(Exp::Bvsub(Box::new(Exp::Var(limit)), Box::new(smt_u64_width(1, 128))), loc);
        let shifted = shiftl(Val::Bits(B129::ones(n)), Val::Symbolic(limit), &mut solver, loc)?;
        let mask = solver.define_bitvector(
            Exp::Bvand(Box::new(Exp::Var(source)), Box::new(Exp::Bvnot(Box::new(smt_value(&shifted, loc)?)))),
            loc,
        );
        for i in 0..n {
            let actual = Exp::Extract(i, i, Box::new(Exp::Var(mask)));
            let expected = Exp::Ite(
                Box::new(Exp::Bvsle(Box::new(smt_u64_width(i as u64, 128)), Box::new(Exp::Var(end)))),
                Box::new(Exp::Extract(i, i, Box::new(Exp::Var(source)))),
                Box::new(smt_zeros(1)),
            );
            assert_eq!(
                solver.check_sat_with(&Exp::Neq(Box::new(actual), Box::new(expected)), loc),
                SmtResult::Unsat,
                "mask N={n},i={i}"
            );
        }
    }
    Ok(())
}
