//! 原语步骤0–2：独立参考算法、实际注册调用及分步等价证明。
use super::*;
use crate::bitvector::b129::B129;

fn context() -> Context {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let mut config = Config::new();
    config.set_param_value("timeout", "10000");
    Context::new(config)
}

fn gf(args: Vec<Val<B129>>, solver: &mut Solver<B129>) -> Result<Val<B129>, ExecError> {
    let mut frame = LocalFrame::new(crate::ir::Name::from_u32(0), &[], &crate::ir::Ty::Unit, None, &[]);
    variadic_primops::<B129>()["gf2_poly_mul_mod"](args, solver, &mut frame, SourceLoc::unknown())
}

fn bits(value: u128, width: u32) -> Val<B129> {
    Val::Bits(B129::from_str(&format!("#b{:0width$b}", value, width = width as usize)).unwrap())
}

// 与逐位移位约减不同，先形成完整多项式积，再从最高项做长除法。
fn long_division(a: u64, b: u64, width: u32, r: u64) -> u64 {
    let mut product = 0;
    for bit in 0..width {
        if a & (1 << bit) != 0 {
            product ^= b << bit;
        }
    }
    for bit in (width..2 * width).rev() {
        if product & (1 << bit) != 0 {
            product ^= ((1 << width) | r) << (bit - width);
        }
    }
    product
}

#[test]
fn primitive_operator_registration_is_pure() {
    assert!(unary_primops::<B129>().contains_key("isla_reverse_bits"));
    assert!(variadic_primops::<B129>().contains_key("gf2_poly_mul_mod"));
    for name in ["isla_reverse_bits", "gf2_poly_mul_mod"] {
        assert_eq!(effect(name), Some(Effect::Pure));
    }
}

#[test]
fn primitive_reverse_permutations_all_supported_widths() -> Result<(), ExecError> {
    let ctx = context();
    let info = SourceLoc::unknown();
    // B64不能容纳128位具体值，仍须支持128位符号结果。
    for width in [1, 8, 16, 32, 64, 128] {
        let mut solver = Solver::<B64>::new(&ctx);
        let input = solver.declare_bitvector(width, info);
        for name in ["isla_reverse_bits", "isla_brev8", "isla_rev8"] {
            if width % 8 != 0 && name != "isla_reverse_bits" {
                continue;
            }
            let result = unary_primops::<B64>()[name](Val::Symbolic(input), &mut solver, info)?;
            let result_exp = smt_value(&result, info)?;
            for output in 0..width {
                let source = match name {
                    "isla_reverse_bits" => width - 1 - output,
                    "isla_brev8" => output / 8 * 8 + 7 - output % 8,
                    _ => width - 8 - output / 8 * 8 + output % 8,
                };
                assert_eq!(
                    solver.check_sat_with(
                        &Exp::Neq(
                            Box::new(Exp::Extract(output, output, Box::new(result_exp.clone()))),
                            Box::new(Exp::Extract(source, source, Box::new(Exp::Var(input)))),
                        ),
                        info
                    ),
                    SmtResult::Unsat,
                    "{name}/{width}/{output}"
                );
            }
        }
    }
    let mut solver = Solver::<B129>::new(&ctx);
    let reverse = unary_primops::<B129>()["isla_reverse_bits"];
    for width in [1, 8, 16, 32, 64, 128] {
        for input in [0, 1, u128::MAX >> (128 - width)] {
            let value = bits(input, width);
            let once = reverse(value.clone(), &mut solver, info)?;
            assert_eq!(reverse(once, &mut solver, info)?, value);
        }
    }
    assert!(reverse(Val::Bits(B129::zeros(0)), &mut solver, info).is_err());
    Ok(())
}

#[test]
fn primitive_gf8_exhaustive_long_division_and_xtime() -> Result<(), ExecError> {
    let ctx = context();
    let mut solver = Solver::<B129>::new(&ctx);
    for a in 0..256 {
        for b in 0..256 {
            let result = gf(vec![bits(a, 8), bits(b, 8), bits(0x1b, 8)], &mut solver)?;
            assert_eq!(result, bits(long_division(a as u64, b as u64, 8, 0x1b) as u128, 8));
        }
        let xtime = ((a << 1) & 255) ^ if a & 128 != 0 { 0x1b } else { 0 };
        assert_eq!(gf(vec![bits(a, 8), bits(2, 8), bits(0x1b, 8)], &mut solver)?, bits(xtime, 8));
    }
    // 商环不要求r不可约，也必须支持最低位为0的模数。
    for r in [0, 1, 2, 7, 15] {
        for a in 0..16 {
            for b in 0..16 {
                assert_eq!(
                    gf(vec![bits(a, 4), bits(b, 4), bits(r, 4)], &mut solver)?,
                    bits(long_division(a as u64, b as u64, 4, r as u64) as u128, 4)
                );
            }
        }
    }
    Ok(())
}

#[test]
fn primitive_gf_symbolic_and_mixed_match_original_loop() -> Result<(), ExecError> {
    let ctx = context();
    let info = SourceLoc::unknown();
    for width in [1, 4, 8] {
        for mode in 0..4 {
            let mut solver = Solver::<B129>::new(&ctx);
            let a = solver.declare_bitvector(width, info);
            let b = solver.declare_bitvector(width, info);
            let r = if width == 8 { 0x1b } else { 1 };
            let (left, right) = match mode {
                0 => (Val::Symbolic(a), Val::Symbolic(b)),
                1 => (bits(1, width), Val::Symbolic(b)),
                2 => (Val::Symbolic(a), bits(1, width)),
                _ if width > 1 => {
                    let half = solver.declare_bitvector(width / 2, info);
                    (
                        Val::MixedBits(vec![
                            BitsSegment::Concrete(B129::new(1, width - width / 2)),
                            BitsSegment::Symbolic(half),
                        ]),
                        Val::Symbolic(b),
                    )
                }
                _ => (Val::MixedBits(vec![BitsSegment::Symbolic(a)]), Val::Symbolic(b)),
            };
            let ae = smt_value(&left, info)?;
            let be = smt_value(&right, info)?;
            let result = gf(vec![left, right, bits(r, width)], &mut solver)?;
            let mut z = solver.define_bitvector(smt_zeros(width.into()), info);
            let mut h = solver.define_bitvector(be, info);
            for bit in 0..width {
                z = solver.define_bitvector(
                    Exp::Ite(
                        Box::new(Exp::Eq(
                            Box::new(Exp::Extract(bit, bit, Box::new(ae.clone()))),
                            Box::new(bits64(1, 1)),
                        )),
                        Box::new(Exp::Bvxor(Box::new(Exp::Var(z)), Box::new(Exp::Var(h)))),
                        Box::new(Exp::Var(z)),
                    ),
                    info,
                );
                let shifted =
                    solver.define_bitvector(Exp::Bvshl(Box::new(Exp::Var(h)), Box::new(smt_u64_width(1, width))), info);
                h = solver.define_bitvector(
                    Exp::Ite(
                        Box::new(Exp::Eq(
                            Box::new(Exp::Extract(width - 1, width - 1, Box::new(Exp::Var(h)))),
                            Box::new(bits64(1, 1)),
                        )),
                        Box::new(Exp::Bvxor(Box::new(Exp::Var(shifted)), Box::new(smt_u64_width(r as u64, width)))),
                        Box::new(Exp::Var(shifted)),
                    ),
                    info,
                );
            }
            let actual = smt_value(&result, info)?;
            for output in 0..width {
                let lane = |value| Box::new(Exp::Extract(output, output, Box::new(value)));
                assert_eq!(
                    solver.check_sat_with(&Exp::Neq(lane(actual.clone()), lane(Exp::Var(z))), info),
                    SmtResult::Unsat,
                    "GF W={width}, mode={mode}, bit={output}"
                );
            }
        }
    }
    Ok(())
}

#[test]
fn primitive_gf_rejects_invalid_contracts() {
    let ctx = context();
    let mut solver = Solver::<B129>::new(&ctx);
    let symbolic_r = solver.declare_bitvector(8, SourceLoc::unknown());
    for args in [
        vec![],
        vec![bits(1, 8)],
        vec![bits(1, 8), bits(1, 4), bits(1, 8)],
        vec![bits(1, 8), bits(1, 8), Val::Symbolic(symbolic_r)],
        vec![Val::Bits(B129::zeros(0)); 3],
        vec![Val::Bits(B129::zeros(129)); 3],
        vec![Val::I128(1), bits(1, 8), bits(1, 8)],
    ] {
        assert!(gf(args, &mut solver).is_err());
    }
}

#[test]
fn primitive_gf128_step_and_actual_output_composition() -> Result<(), ExecError> {
    let ctx = context();
    let info = SourceLoc::unknown();
    for width in [1, 8, 128] {
        let mut solver = Solver::<B129>::new(&ctx);
        let z = solver.declare_bitvector(width, info);
        let h = solver.declare_bitvector(width, info);
        let c = solver.declare_bitvector(1, info);
        let r = solver.declare_bitvector(width, info);
        // 任意初值、任意低项r：旧条件更新与符号扩展mask更新等价。
        let mask = Exp::SignExtend(width - 1, Box::new(Exp::Var(c)));
        let original_z = Exp::Ite(
            Box::new(Exp::Eq(Box::new(Exp::Var(c)), Box::new(bits64(1, 1)))),
            Box::new(Exp::Bvxor(Box::new(Exp::Var(z)), Box::new(Exp::Var(h)))),
            Box::new(Exp::Var(z)),
        );
        let masked_z = Exp::Bvxor(Box::new(Exp::Var(z)), Box::new(Exp::Bvand(Box::new(mask), Box::new(Exp::Var(h)))));
        assert_eq!(solver.check_sat_with(&Exp::Neq(Box::new(original_z), Box::new(masked_z)), info), SmtResult::Unsat);
        let top = Exp::Extract(width - 1, width - 1, Box::new(Exp::Var(h)));
        let shifted = Exp::Bvshl(Box::new(Exp::Var(h)), Box::new(smt_u64_width(1, width)));
        let original_h = Exp::Ite(
            Box::new(Exp::Eq(Box::new(top.clone()), Box::new(bits64(1, 1)))),
            Box::new(Exp::Bvxor(Box::new(shifted.clone()), Box::new(Exp::Var(r)))),
            Box::new(shifted.clone()),
        );
        let masked_h = Exp::Bvxor(
            Box::new(shifted),
            Box::new(Exp::Bvand(Box::new(Exp::SignExtend(width - 1, Box::new(top))), Box::new(Exp::Var(r)))),
        );
        assert_eq!(solver.check_sat_with(&Exp::Neq(Box::new(original_h), Box::new(masked_h)), info), SmtResult::Unsat);
    }
    // 以已证明的单步恒等式规范化旧循环，再与实际注册的128位输出比较。
    // 此处不是尝试让求解器一次重证两套不同电路；组合条件见实施报告。
    for mode in 0..4 {
        let mut solver = Solver::<B129>::new(&ctx);
        let a = solver.declare_bitvector(128, info);
        let b = solver.declare_bitvector(128, info);
        let (left, right) = match mode {
            0 => (Val::Symbolic(a), Val::Symbolic(b)),
            1 => (bits(0x87, 128), Val::Symbolic(b)),
            2 => (Val::Symbolic(a), bits(0x87, 128)),
            _ => {
                let half = solver.declare_bitvector(64, info);
                (
                    Val::MixedBits(vec![BitsSegment::Concrete(B129::new(0x1234, 64)), BitsSegment::Symbolic(half)]),
                    Val::Symbolic(b),
                )
            }
        };
        let ae = smt_value(&left, info)?;
        let mut h = solver.define_bitvector(smt_value(&right, info)?, info);
        let mut reference = solver.define_bitvector(smt_zeros(128), info);
        for bit in 0..128 {
            let mask = Exp::SignExtend(127, Box::new(Exp::Extract(bit, bit, Box::new(ae.clone()))));
            reference = solver.define_bitvector(
                Exp::Bvxor(Box::new(Exp::Var(reference)), Box::new(Exp::Bvand(Box::new(mask), Box::new(Exp::Var(h))))),
                info,
            );
            let high_mask = Exp::SignExtend(127, Box::new(Exp::Extract(127, 127, Box::new(Exp::Var(h)))));
            h = solver.define_bitvector(
                Exp::Bvxor(
                    Box::new(Exp::Bvshl(Box::new(Exp::Var(h)), Box::new(smt_u64_width(1, 128)))),
                    Box::new(Exp::Bvand(Box::new(high_mask), Box::new(smt_u64_width(0x87, 128)))),
                ),
                info,
            );
        }
        let result = gf(vec![left, right, bits(0x87, 128)], &mut solver)?;
        assert_eq!(
            solver.check_sat_with(&Exp::Neq(Box::new(smt_value(&result, info)?), Box::new(Exp::Var(reference))), info),
            SmtResult::Unsat,
            "128位组合证明，模式{mode}"
        );
    }
    // GHASH最高位约减与零/单位元；避免仅测试低64位。
    let mut solver = Solver::<B129>::new(&ctx);
    assert_eq!(gf(vec![bits(1 << 127, 128), bits(2, 128), bits(0x87, 128)], &mut solver)?, bits(0x87, 128));
    assert_eq!(gf(vec![bits(u128::MAX, 128), bits(1, 128), bits(0x87, 128)], &mut solver)?, bits(u128::MAX, 128));
    Ok(())
}

#[test]
fn primitive_gf_modulus_step_matches_polynomial_division() {
    let ctx = context();
    let info = SourceLoc::unknown();
    for width in [1, 8, 128] {
        let mut solver = Solver::<B129>::new(&ctx);
        let h = solver.declare_bitvector(width, info);
        let r = solver.declare_bitvector(width, info);
        // X*h的次数至多W；一次最高项消元即得到余式。
        let high = Exp::Extract(width - 1, width - 1, Box::new(Exp::Var(h)));
        let raw =
            Exp::Bvshl(Box::new(Exp::ZeroExtend(1, Box::new(Exp::Var(h)))), Box::new(smt_u64_width(1, width + 1)));
        let modulus = Exp::Concat(Box::new(bits64(1, 1)), Box::new(Exp::Var(r)));
        let divided = Exp::Extract(
            width - 1,
            0,
            Box::new(Exp::Ite(
                Box::new(Exp::Eq(Box::new(high.clone()), Box::new(bits64(1, 1)))),
                Box::new(Exp::Bvxor(Box::new(raw.clone()), Box::new(modulus))),
                Box::new(raw),
            )),
        );
        let recurrence = Exp::Bvxor(
            Box::new(Exp::Bvshl(Box::new(Exp::Var(h)), Box::new(smt_u64_width(1, width)))),
            Box::new(Exp::Bvand(Box::new(Exp::SignExtend(width - 1, Box::new(high))), Box::new(Exp::Var(r)))),
        );
        assert_eq!(solver.check_sat_with(&Exp::Neq(Box::new(divided), Box::new(recurrence)), info), SmtResult::Unsat);
    }
}

#[test]
fn primitive_popcount_prefix_invariant_and_encoding() -> Result<(), ExecError> {
    let ctx = context();
    let info = SourceLoc::unknown();
    for width in [0, 1, 2, 4, 8, 16, 32, 64, 128] {
        let mut solver = Solver::<B129>::new(&ctx);
        assert_eq!(isla_count_ones(Val::Bits(B129::ones(width)), &mut solver, info)?, Val::I128(width.into()));
        if width == 0 {
            continue;
        }
        let k = (u32::BITS - width.leading_zeros()).max(1);
        for prefix in 0..width {
            let mut step = Solver::<B129>::new(&ctx);
            let count = step.declare_bitvector(k, info);
            let bit = step.declare_bitvector(1, info);
            step.assert(Exp::Bvule(Box::new(Exp::Var(count)), Box::new(smt_u64_width(prefix.into(), k))));
            let narrow =
                Exp::Bvadd(Box::new(Exp::Var(count)), Box::new(Exp::ZeroExtend(k - 1, Box::new(Exp::Var(bit)))));
            let old = Exp::Bvadd(
                Box::new(Exp::ZeroExtend(128 - k, Box::new(Exp::Var(count)))),
                Box::new(Exp::ZeroExtend(127, Box::new(Exp::Var(bit)))),
            );
            assert_eq!(
                step.check_sat_with(
                    &Exp::Neq(Box::new(Exp::ZeroExtend(128 - k, Box::new(narrow.clone()))), Box::new(old)),
                    info
                ),
                SmtResult::Unsat
            );
            assert_eq!(
                step.check_sat_with(
                    &Exp::Bvugt(Box::new(narrow), Box::new(smt_u64_width((prefix + 1).into(), k))),
                    info
                ),
                SmtResult::Unsat
            );
        }
        let input = solver.declare_bitvector(width, info);
        let result = isla_count_ones(Val::Symbolic(input), &mut solver, info)?;
        let sum = (0..width)
            .map(|bit| Exp::ZeroExtend(k - 1, Box::new(Exp::Extract(bit, bit, Box::new(Exp::Var(input))))))
            .fold(smt_zeros(k.into()), |a, b| Exp::Bvadd(Box::new(a), Box::new(b)));
        assert_eq!(
            solver.check_sat_with(
                &Exp::Neq(Box::new(smt_value(&result, info)?), Box::new(Exp::ZeroExtend(128 - k, Box::new(sum)))),
                info
            ),
            SmtResult::Unsat
        );
    }
    Ok(())
}

#[test]
fn primitive_clmul_original_steps_and_actual_slices() -> Result<(), ExecError> {
    let ctx = context();
    let info = SourceLoc::unknown();
    for width in [4, 32, 64, 128] {
        let mut solver = Solver::<B129>::new(&ctx);
        let a = solver.declare_bitvector(width, info);
        let b = solver.declare_bitvector(width, info);
        let mut reference = solver.define_bitvector(smt_zeros((width * 2).into()), info);
        for bit in 0..width {
            let shifted = Exp::Bvshl(
                Box::new(Exp::ZeroExtend(width, Box::new(Exp::Var(b)))),
                Box::new(smt_u64_width(bit.into(), width * 2)),
            );
            let mask = Exp::Ite(
                Box::new(Exp::Eq(Box::new(Exp::Extract(bit, bit, Box::new(Exp::Var(a)))), Box::new(bits64(1, 1)))),
                Box::new(smt_ones((width * 2).into())),
                Box::new(smt_zeros((width * 2).into())),
            );
            reference = solver.define_bitvector(
                Exp::Bvxor(Box::new(Exp::Var(reference)), Box::new(Exp::Bvand(Box::new(mask), Box::new(shifted)))),
                info,
            );
        }
        let actual = isla_carryless_mul(Val::Symbolic(a), Val::Symbolic(b), &mut solver, info)?;
        for output in 0..width * 2 {
            assert_eq!(
                solver.check_sat_with(
                    &Exp::Neq(
                        Box::new(Exp::Extract(output, output, Box::new(smt_value(&actual, info)?))),
                        Box::new(Exp::Extract(output, output, Box::new(Exp::Var(reference))))
                    ),
                    info
                ),
                SmtResult::Unsat,
                "逐输出位clmul证明 W={width}, bit={output}"
            );
        }
        for (operation, high, low) in [
            (isla_clmul::<B129> as Binary<B129>, width - 1, 0),
            (isla_clmulh::<B129>, width * 2 - 1, width),
            (isla_carryless_mulr::<B129>, width * 2 - 2, width - 1),
        ] {
            let result = operation(Val::Symbolic(a), Val::Symbolic(b), &mut solver, info)?;
            assert_eq!(
                solver.check_sat_with(
                    &Exp::Neq(
                        Box::new(smt_value(&result, info)?),
                        Box::new(Exp::Extract(high, low, Box::new(smt_value(&actual, info)?)))
                    ),
                    info
                ),
                SmtResult::Unsat
            );
        }
        // 任意累加初值/移位项的原条件更新恒等式，支撑逐轮归纳。
        let mut step = Solver::<B129>::new(&ctx);
        let z = step.declare_bitvector(width * 2, info);
        let t = step.declare_bitvector(width * 2, info);
        let c = step.declare_bitvector(1, info);
        let old = Exp::Ite(
            Box::new(Exp::Eq(Box::new(Exp::Var(c)), Box::new(bits64(1, 1)))),
            Box::new(Exp::Bvxor(Box::new(Exp::Var(z)), Box::new(Exp::Var(t)))),
            Box::new(Exp::Var(z)),
        );
        let new = Exp::Bvxor(
            Box::new(Exp::Var(z)),
            Box::new(Exp::Bvand(
                Box::new(Exp::SignExtend(width * 2 - 1, Box::new(Exp::Var(c)))),
                Box::new(Exp::Var(t)),
            )),
        );
        assert_eq!(step.check_sat_with(&Exp::Neq(Box::new(old), Box::new(new)), info), SmtResult::Unsat);
    }
    let mut solver = Solver::<B129>::new(&ctx);
    for a in 0..16 {
        for b in 0..16 {
            let mut product = 0u128;
            for bit in 0..4 {
                if a & (1 << bit) != 0 {
                    product ^= b << bit;
                }
            }
            assert_eq!(isla_carryless_mul(bits(a, 4), bits(b, 4), &mut solver, info)?, bits(product, 8));
            assert_eq!(isla_carryless_mulr(bits(a, 4), bits(b, 4), &mut solver, info)?, bits((product >> 3) & 15, 4));
        }
    }
    // 256位结果超过B129容量，必须精确保留最高有效项。
    let result = isla_carryless_mul(bits(1 << 127, 128), bits(1 << 127, 128), &mut solver, info)?;
    let mut expected = vec![false; 256];
    expected[254] = true;
    assert_eq!(
        solver.check_sat_with(&Exp::Neq(Box::new(smt_value(&result, info)?), Box::new(Exp::Bits(expected))), info),
        SmtResult::Unsat
    );
    Ok(())
}

#[test]
fn dedup_actual_bool_comparison_reuses_both_sat_and_keeps_dead_arm_pruned() {
    let ctx = context();
    let info = SourceLoc::unknown();
    let mut solver = Solver::<B64>::new(&ctx);
    let x = solver.declare_const(smtlib::Ty::BitVec(8), info);
    let result =
        try_concretize_bool_exp(Exp::Eq(Box::new(Exp::Var(x)), Box::new(bits64(7, 8))), &mut solver, info).unwrap();
    let Val::Symbolic(condition) = result else {
        panic!("自由比较必须保留两种取值");
    };
    crate::smt::reset_path_smt_stats();
    assert_eq!(solver.check_sat_with_for_branch(&Exp::Var(condition), info, true), Some(SmtResult::Sat));
    assert_eq!(
        solver.check_sat_with_for_branch(&Exp::Not(Box::new(Exp::Var(condition))), info, true),
        Some(SmtResult::Sat)
    );
    assert_eq!(crate::smt::path_smt_stats().calls, 0);
    solver.assert(Exp::Var(condition));
    if solver.check_sat_with_for_branch(&Exp::Not(Box::new(Exp::Var(condition))), info, true).unwrap().is_sat().unwrap()
    {
        panic!("新增约束之后的死臂不能执行原语不变量检查");
    }
}
