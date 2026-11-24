use super::*;
use crate::bitvector::b64::B64;
use crate::smt::{checkpoint, Config, Context};

#[test]
fn sym_bits_primitive_equivalence() -> Result<(), ExecError> {
    let info = SourceLoc::unknown();
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let mut config = Config::new();
    config.solver_options.sym_bits = true;
    let context = Context::new(config);
    let oracle_context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let choice = solver.declare_bitvector(2, info);
    let len = solver.define_const(Exp::ZeroExtend(126, Box::new(Exp::Var(choice))), info);
    let make_input = |solver: &mut Solver<B64>| {
        let raw = solver.declare_bitvector(3, info);
        let data = (1..=3).fold(smt_zeros(3), |rest, width| {
            let fixed = if width == 3 {
                Exp::Var(raw)
            } else {
                Exp::ZeroExtend(3 - width, Box::new(Exp::Extract(width - 1, 0, Box::new(Exp::Var(raw)))))
            };
            Exp::Ite(
                Box::new(Exp::Eq(Box::new(Exp::Var(len)), Box::new(smt_i128(i128::from(width))))),
                Box::new(fixed),
                Box::new(rest),
            )
        });
        let data = solver.define_bitvector(data, info);
        (Val::SymBits { data, len, cap: 3 }, raw)
    };
    let (a, raw_a) = make_input(&mut solver);
    let (b, raw_b) = make_input(&mut solver);
    let shift = solver.define_const(Exp::Bvsub(Box::new(Exp::Var(len)), Box::new(smt_i128(2))), info);
    let results = |s: &mut Solver<B64>,
                   a: Val<B64>,
                   b: Val<B64>,
                   n: Val<B64>,
                   shift: Val<B64>,
                   subrange_source,
                   subrange_high: Val<B64>| {
        let fixed = Val::Bits(B64::new(0b101, 3));
        Ok::<_, ExecError>(vec![
            ("zeros", zeros(n.clone(), s, info)?),
            ("ones", ones(n.clone(), s, info)?),
            ("not_bits", not_bits(a.clone(), s, info)?),
            ("zero_extend", zero_extend(a.clone(), Val::I128(4), s, info)?),
            ("sign_extend", sign_extend(a.clone(), Val::I128(4), s, info)?),
            ("zero_extend_dynamic", zero_extend(Val::Bits(B64::zeros(0)), n.clone(), s, info)?),
            ("sign_extend_dynamic", sign_extend(Val::Bits(B64::new(1, 1)), subrange_high.clone(), s, info)?),
            ("sail_truncate", sail_truncate(fixed.clone(), n.clone(), s, info)?),
            ("sail_truncateLSB", sail_truncate_lsb(fixed.clone(), n.clone(), s, info)?),
            ("slice", slice_internal(a.clone(), Val::I128(1), subrange_high.clone(), s, info)?),
            ("subrange", subrange_internal(subrange_source, n.clone(), Val::I128(0), s, info)?),
            ("append", append(a.clone(), b.clone(), s, info)?),
            ("and_bits", and_bits(a.clone(), b.clone(), s, info)?),
            ("or_bits", or_bits(a.clone(), b.clone(), s, info)?),
            ("xor_bits", xor_bits(a.clone(), b.clone(), s, info)?),
            ("add_bits", add_bits(a.clone(), b.clone(), s, info)?),
            ("sub_bits", sub_bits(a.clone(), b.clone(), s, info)?),
            ("add_bits_int", add_bits_int(a.clone(), Val::I128(-1), s, info)?),
            ("sub_bits_int", sub_bits_int(a.clone(), Val::I128(1), s, info)?),
            ("eq_bits", eq_bits(a.clone(), b.clone(), s, info)?),
            ("neq_bits", neq_bits(a.clone(), b.clone(), s, info)?),
            ("shiftl", shiftl(a.clone(), shift.clone(), s, info)?),
            ("shiftr", shiftr(a.clone(), shift.clone(), s, info)?),
            ("arith_shiftr", arith_shiftr(a.clone(), shift, s, info)?),
            ("shift_bits_left", shift_bits_left(a.clone(), b.clone(), s, info)?),
            ("shift_bits_right", shift_bits_right(a.clone(), b, s, info)?),
            ("length", length(a.clone(), s, info)?),
            ("unsigned", sail_unsigned(a.clone(), s, info)?),
            ("signed", sail_signed(a, s, info)?),
        ])
    };
    let n_plus_one = solver.define_const(Exp::Bvadd(Box::new(Exp::Var(len)), Box::new(smt_i128(1))), info);
    let actual = results(
        &mut solver,
        a,
        b,
        Val::Symbolic(len),
        Val::Symbolic(shift),
        Val::Bits(B64::new(0b1101, 4)),
        Val::Symbolic(n_plus_one),
    )?;
    assert!(matches!(actual[0].1, Val::SymBits { cap: 3, .. }));
    assert!(matches!(actual[3].1, Val::Symbolic(_)));
    let point = checkpoint(&mut solver);
    for width in 0..=3 {
        // 在独立的 Z3 上下文只重放公开的 SMT 定义，再用旧原语构造该位宽的参照。
        let mut oracle = Solver::from_checkpoint(&oracle_context, point.clone());
        oracle.assert(Exp::Eq(Box::new(Exp::Var(len)), Box::new(smt_i128(i128::from(width)))));
        let fixed = |raw, s: &mut Solver<B64>| {
            if width == 0 {
                Val::Bits(B64::zeros(0))
            } else {
                Val::Symbolic(s.define_bitvector(Exp::Extract(width - 1, 0, Box::new(Exp::Var(raw))), info))
            }
        };
        let a = fixed(raw_a, &mut oracle);
        let b = fixed(raw_b, &mut oracle);
        let expected = results(
            &mut oracle,
            a,
            b,
            Val::I128(i128::from(width)),
            Val::I128(i128::from(width) - 2),
            Val::Bits(B64::new(0b1101, 4)),
            Val::I128(i128::from(width) + 1),
        )?;
        for ((name, actual), (_, expected)) in actual.iter().zip(expected) {
            let comparison = match *name {
                "length" | "signed" | "unsigned" | "eq_bits" | "neq_bits" => {
                    Exp::Eq(Box::new(smt_value(actual, info)?), Box::new(smt_value(&expected, info)?))
                }
                _ => match actual {
                    Val::SymBits { data, len, cap } => {
                        let width = length_bits(&expected, &mut oracle, info)?;
                        let expected = if width == 0 {
                            smt_zeros(i128::from(*cap))
                        } else if width < *cap {
                            Exp::ZeroExtend(*cap - width, Box::new(smt_value(&expected, info)?))
                        } else {
                            assert_eq!(width, *cap);
                            smt_value(&expected, info)?
                        };
                        Exp::And(
                            Box::new(Exp::Eq(Box::new(Exp::Var(*len)), Box::new(smt_i128(i128::from(width))))),
                            Box::new(Exp::Eq(Box::new(Exp::Var(*data)), Box::new(expected))),
                        )
                    }
                    actual => {
                        let width = length_bits(actual, &mut oracle, info)?;
                        assert_eq!(width, length_bits(&expected, &mut oracle, info)?);
                        if width == 0 {
                            Exp::Bool(true)
                        } else {
                            Exp::Eq(Box::new(smt_value(actual, info)?), Box::new(smt_value(&expected, info)?))
                        }
                    }
                },
            };
            let result = oracle.check_sat_with(&Exp::Not(Box::new(comparison)), info);
            assert_eq!(result, SmtResult::Unsat, "{name}, 输入宽度 {width}");
        }
    }
    Ok(())
}

#[test]
fn sym_bits_merge_and_constant_collapse() -> Result<(), ExecError> {
    let info = SourceLoc::unknown();
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let mut config = Config::new();
    config.solver_options.sym_bits = true;
    let context = Context::new(config);
    let mut solver = Solver::<B64>::new(&context);
    let condition = solver.declare_const(Ty::Bool, info);
    let a = Val::Bits(B64::new(1, 2));
    let b = Val::Bits(B64::new(7, 3));
    let merged = merge_val_mode::<_, true>(condition, &a, &b, &mut solver, info)?;
    assert!(matches!(merged, Val::SymBits { cap: 3, .. }), "{merged:?}");
    let third = solver.declare_const(Ty::Bool, info);
    let empty = Val::Bits(B64::zeros(0));
    let merged = merge_val_mode::<_, true>(third, &merged, &empty, &mut solver, info)?;
    let Val::SymBits { len, data, cap: 3 } = merged else {
        panic!("三个候选应保存为一个值");
    };
    for (select_third, select_left, expected_len, expected_data) in
        [(true, true, 2, 1), (true, false, 3, 7), (false, false, 0, 0)]
    {
        let mut check = Solver::from_checkpoint(&context, checkpoint(&mut solver));
        check.assert(binary(Exp::Eq, Exp::Var(third), Exp::Bool(select_third)));
        check.assert(binary(Exp::Eq, Exp::Var(condition), Exp::Bool(select_left)));
        assert_eq!(check.check_sat(info), SmtResult::Sat);
        assert_eq!(check.check_sat_with(&binary(Exp::Neq, Exp::Var(len), int(expected_len)), info), SmtResult::Unsat);
        assert_eq!(
            check.check_sat_with(&binary(Exp::Neq, Exp::Var(data), bits64(expected_data, 3)), info),
            SmtResult::Unsat
        );
    }
    let complement = solver.define_const(binary(Exp::Bvsub, int(3), Exp::Var(len)), info);
    let rest = zeros(Val::Symbolic(complement), &mut solver, info)?;
    let joined = append(Val::SymBits { len, data, cap: 3 }, rest, &mut solver, info)?;
    assert!(matches!(joined, Val::Symbolic(sym) if solver.length(sym) == Some(3)), "{joined:?}");
    Ok(())
}
