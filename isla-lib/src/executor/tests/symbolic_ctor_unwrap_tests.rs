use super::*;

#[test]
fn 符号构造子的直接与字段解包必须检查标签可满足性() {
    let tag_a = test_name(740);
    let tag_b = test_name(741);
    let value = test_name(742);
    let field = test_name(743);
    let shared = empty_shared_state();
    for through_field in [false, true] {
        for selected_tag in [Some(tag_a), Some(tag_b), None] {
            crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let tag = solver.declare_const(Name::smt_ty(), info());
            if let Some(selected_tag) = selected_tag {
                solver.assert(smtlib::Exp::Eq(Box::new(smtlib::Exp::Var(tag)), Box::new(selected_tag.to_smt())));
            }
            let mut frame = make_frame(vec![Instr::End]);
            frame.vars_mut().insert(
                value,
                UVal::Init(Val::SymbolicCtor(
                    tag,
                    HashMap::from_iter([(tag_a, Val::Bits(B64::new(11, 8))), (tag_b, Val::Bits(B64::new(22, 8)))]),
                )),
            );
            let exp = if through_field {
                Exp::Field(Box::new(Exp::Struct(test_name(744), vec![(field, Exp::Id(value))])), field)
            } else {
                Exp::Id(value)
            };
            let result = eval_exp(
                &Exp::Unwrap(tag_a, Box::new(exp)),
                Arc::make_mut(&mut frame.local_state),
                &shared,
                &mut solver,
                info(),
            )
            .map(Cow::into_owned);
            if selected_tag == Some(tag_b) {
                assert!(matches!(result, Err(ExecError::Type(..))), "标签不可匹配时必须保留类型错误");
            } else if selected_tag.is_none() {
                let Err(ExecError::RetryCondition(condition, _)) = result else {
                    panic!("标签不确定时必须请求条件分叉")
                };
                assert!(solver.check_sat_with(&condition, info()).is_sat().unwrap());
                assert!(solver.check_sat_with(&smtlib::Exp::Not(Box::new(condition)), info()).is_sat().unwrap());
            } else {
                assert_eq!(result.unwrap(), Val::Bits(B64::new(11, 8)));
            }
        }
    }
}
