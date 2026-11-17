use super::*;
use crate::bitvector::b64::B64;
use crate::primop_util::smt_value;
use crate::smt::{self, Config, Context};

type Formula = smtlib::Exp<Sym>;
fn site() -> SourceLoc {
    SourceLoc::unknown()
}
fn fixture(rounds: usize) -> (SharedState<'static, B64>, Name, [Name; 3]) {
    let mut shared = SharedState::<B64>::empty(Symtab::new());
    let f = shared.symtab.intern("zrange_lookup");
    let addr = shared.symtab.intern("zaddress");
    let table = shared.symtab.intern("zboundaries");
    let rights = shared.symtab.intern("zrights");
    let invalid = shared.symtab.intern("zinvalid");
    for (reg, ty) in [
        (table, Ty::Vector(Box::new(Ty::Bits(4)))),
        (rights, Ty::Vector(Box::new(Ty::Bool))),
        (invalid, Ty::Vector(Box::new(Ty::Bool))),
    ] {
        shared.registers.insert(reg, ty);
    }
    let idx = shared.symtab.intern("zindex");
    let offset = shared.symtab.intern("zoffset");
    let previous = shared.symtab.intern("zprevious");
    let current = shared.symtab.intern("zcurrent");
    let flag = shared.symtab.intern("zflag");
    let unit = shared.symtab.intern("zunit");
    let unary = primop::unary_primops::<B64>();
    let binary = primop::binary_primops::<B64>();
    let mut body = vec![
        Instr::Init(idx, Ty::I64, Exp::I64(0), site()),
        Instr::Decl(offset, Ty::I128, site()),
        Instr::Decl(previous, Ty::Bits(4), site()),
        Instr::Decl(current, Ty::Bits(4), site()),
        Instr::Decl(flag, Ty::Bool, site()),
        Instr::Decl(unit, Ty::Unit, site()),
        Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(idx), Exp::I64(rounds as i64)]), 0, site()),
        Instr::PrimopUnary(Loc::Id(offset), unary["%i64->%i"], Exp::Id(idx), site()),
        Instr::Copy(Loc::Id(previous), Exp::Bits(B64::new(0, 4)), site()),
        Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(idx), Exp::I64(0)]), 13, site()),
        Instr::PrimopUnary(
            Loc::Id(offset),
            unary["%i64->%i"],
            Exp::Call(Op::Sub, vec![Exp::Id(idx), Exp::I64(1)]),
            site(),
        ),
        Instr::PrimopBinary(Loc::Id(previous), binary["vector_access"], Exp::Id(table), Exp::Id(offset), site()),
        Instr::PrimopUnary(Loc::Id(offset), unary["%i64->%i"], Exp::Id(idx), site()),
        Instr::PrimopBinary(Loc::Id(current), binary["vector_access"], Exp::Id(table), Exp::Id(offset), site()),
        Instr::PrimopBinary(Loc::Id(flag), binary["lteq_bits_u"], Exp::Id(previous), Exp::Id(addr), site()),
        Instr::Jump(Exp::Id(flag).bool_not(), 22, site()),
        Instr::PrimopBinary(Loc::Id(flag), binary["lt_bits_u"], Exp::Id(addr), Exp::Id(current), site()),
        Instr::Jump(Exp::Id(flag).bool_not(), 22, site()),
        Instr::PrimopBinary(Loc::Id(flag), binary["vector_access"], Exp::Id(invalid), Exp::Id(offset), site()),
        Instr::Jump(Exp::Id(flag), 24, site()),
        Instr::PrimopBinary(Loc::Id(RETURN), binary["vector_access"], Exp::Id(rights), Exp::Id(offset), site()),
        Instr::Goto(28),
        Instr::Copy(Loc::Id(idx), Exp::Call(Op::Add, vec![Exp::Id(idx), Exp::I64(1)]), site()),
        Instr::Goto(6),
        Instr::PrimopBinary(
            Loc::Id(unit),
            binary["optimistic_assert"],
            Exp::Bool(false),
            Exp::String("死臂".into()),
            site(),
        ),
        Instr::Goto(28),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), site()),
        Instr::Goto(28),
        Instr::End,
    ];
    body[6] = Instr::Jump(Exp::Call(Op::Eq, vec![Exp::Id(idx), Exp::I64(rounds as i64)]), 26, site());
    shared.functions.insert(f, (vec![(addr, &Ty::Bits(4))], &Ty::Bool, Box::leak(body.into_boxed_slice())));
    (shared, f, [table, rights, invalid])
}
fn registers(names: [Name; 3], rounds: usize, solver: &mut Solver<B64>) -> RegisterBindings<'static, B64> {
    let mut regs = RegisterBindings::new();
    for (reg, ty) in [(names[0], smtlib::Ty::BitVec(4)), (names[1], smtlib::Ty::Bool), (names[2], smtlib::Ty::Bool)] {
        let values = (0..rounds).map(|_| Val::Symbolic(solver.declare_const(ty.clone(), site()))).collect();
        regs.insert(reg, false, UVal::Init(Val::Vector(values)));
    }
    regs
}
fn relation(instance: &SummaryInstance<B64>, output: Sym) -> Formula {
    use smtlib::Exp::*;
    instance.returns.iter().fold(Bool(false), |r, (g, v)| {
        Or(
            Box::new(r),
            Box::new(And(
                Box::new(g.clone()),
                Box::new(Eq(Box::new(Var(output)), Box::new(smt_value(v, site()).unwrap()))),
            )),
        )
    })
}
#[test]
fn prototype_is_disabled_by_default() {
    smt::configure_tastic(smt::Tactic::Qfaufbv);
    let (shared, f, names) = fixture(2);
    let lets = Bindings::default();
    let ctx = Context::new(Config::new());
    let mut solver = Solver::new(&ctx);
    let regs = registers(names, 2, &mut solver);
    let mut cache = Prototype::new(&shared, &lets);
    assert!(cache.call(f, &[Val::Bits(B64::new(0, 4))], &regs, &mut solver, &BTreeSet::new()).unwrap().is_none());
    assert_eq!(cache.builds, 0);
}
#[test]
fn fresh_formals_reuse_across_addresses_and_invalidate_on_writes() {
    smt::configure_tastic(smt::Tactic::Qfaufbv);
    for rounds in [2, 3, 4] {
        let (shared, f, names) = fixture(rounds);
        let lets = Bindings::default();
        let ctx = Context::new(Config::new());
        let mut solver = Solver::new(&ctx);
        let regs = registers(names, rounds, &mut solver);
        let mut cache = Prototype::new(&shared, &lets);
        cache.set_enabled(true);
        let first = cache.call(f, &[Val::Bits(B64::new(0, 4))], &regs, &mut solver, &BTreeSet::new()).unwrap().unwrap();
        assert!(!first.returns.is_empty());
        let address = solver.declare_bitvector(4, site());
        let second = cache.call(f, &[Val::Symbolic(address)], &regs, &mut solver, &BTreeSet::new()).unwrap().unwrap();
        assert_eq!((cache.builds, cache.hits), (1, 1));
        assert!(!second.dead_arms.is_empty());
        assert!(matches!(second.input_domain, smtlib::Exp::Bool(true)));
        // 按同一公开执行器直接内联，不使用缓存构造函数作为等价对照。
        let direct = direct_paths(&shared, f, &[Val::Symbolic(address)], &regs, &mut solver);
        let output = solver.declare_const(smtlib::Ty::Bool, site());
        for (a, b) in
            [(relation(&second, output), relation(&direct, output)), (second.domain.clone(), direct.domain.clone())]
        {
            assert!(solver.check_sat_with(&smtlib::Exp::Neq(Box::new(a), Box::new(b)), site()).is_unsat().unwrap());
        }
        for name in names {
            let guards = |instance: &SummaryInstance<B64>| {
                instance
                    .reads
                    .iter()
                    .filter(|r| r.register == name)
                    .fold(smtlib::Exp::Bool(false), |a, r| smtlib::Exp::Or(Box::new(a), Box::new(r.guard.clone())))
            };
            assert!(
                solver
                    .check_sat_with(&smtlib::Exp::Neq(Box::new(guards(&second)), Box::new(guards(&direct))), site())
                    .is_unsat()
                    .unwrap(),
                "读取守卫必须一致"
            );
        }
        for read in &second.reads {
            assert_eq!(&read.value, regs.get_last_if_initialized(read.register).unwrap(), "每次读取必须绑定同一入口值");
        }
        let dead = second
            .dead_arms
            .iter()
            .cloned()
            .fold(smtlib::Exp::Bool(false), |a, b| smtlib::Exp::Or(Box::new(a), Box::new(b)));
        assert!(solver
            .check_sat_with(&smtlib::Exp::And(Box::new(dead.clone()), Box::new(second.domain.clone())), site())
            .is_unsat()
            .unwrap());
        assert!(
            solver
                .check_sat_with(
                    &smtlib::Exp::Not(Box::new(smtlib::Exp::Or(Box::new(dead), Box::new(second.domain.clone())))),
                    site()
                )
                .is_unsat()
                .unwrap(),
            "正常域与死臂必须穷尽输入"
        );
        let inputs: HashSet<_> = names
            .iter()
            .flat_map(|n| regs.get_last_if_initialized(*n).unwrap().symbolic_variables())
            .chain([address])
            .collect();
        let internal = |instance: &SummaryInstance<B64>| {
            instance.domain.variables().into_iter().filter(|n| !inputs.contains(n)).collect::<HashSet<_>>()
        };
        assert!(!internal(&first).is_empty());
        assert!(internal(&first).is_disjoint(&internal(&second)), "两次调用的辅助符号必须独立");
        cache.call(f, &[Val::Symbolic(address)], &regs, &mut solver, &BTreeSet::from([names[0]])).unwrap().unwrap();
        assert_eq!((cache.builds, cache.hits), (2, 1), "读集有写时必须重新构造");
    }
}

fn direct_paths(
    shared: &SharedState<'static, B64>,
    f: Name,
    args: &[Val<B64>],
    regs: &RegisterBindings<'static, B64>,
    solver: &mut Solver<B64>,
) -> SummaryInstance<B64> {
    let (params, ret, body) = &shared.functions[&f];
    let mut frame = LocalFrame::new(f, params, ret, Some(args), body);
    frame.add_regs(regs);
    let state = TaskState::new();
    let output = Mutex::new(Vec::new());
    start_single(
        frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(solver)),
        shared,
        &output,
        &|_, _, result, _, path_solver, output| {
            let value = match result {
                Ok((Run::Finished(v), _)) => Some(v),
                Err((ExecError::AssertionFailure(..), _)) => None,
                Err((error, _)) => panic!("直接内联失败: {:?}", error),
                _ => panic!("直接内联未正常返回"),
            };
            output
                .lock()
                .unwrap()
                .push((value, path_solver.trace().to_vec().into_iter().rev().cloned().collect::<Vec<_>>()));
        },
    );
    // 独立对照消去直接执行的全部辅助定义；只剩入口符号。
    let mut returns = Vec::new();
    let mut reads = Vec::new();
    let mut dead_arms = Vec::new();
    let mut domain = smtlib::Exp::Bool(false);
    for (value, events) in output.into_inner().unwrap() {
        let mut defs = HashMap::new();
        for e in &events {
            if let Event::Smt(smtlib::Def::DefineConst(n, e), _, _) = e {
                defs.insert(*n, e);
            }
        }
        let mut guard = smtlib::Exp::Bool(true);
        for e in &events {
            match e {
                Event::Smt(smtlib::Def::Assert(e), _, _) => {
                    guard = smtlib::Exp::And(Box::new(guard), Box::new(e.clone_expand(&defs)))
                }
                Event::ReadReg(register, accessor, value) => reads.push(GuardedRegisterRead {
                    register: *register,
                    accessor: accessor.clone(),
                    value: value.clone(),
                    guard: guard.clone(),
                }),
                _ => (),
            }
        }
        if let Some(value) = value {
            let value = solver.define_const(smt_value(&value, site()).unwrap().clone_expand(&defs), site());
            domain = smtlib::Exp::Or(Box::new(domain), Box::new(guard.clone()));
            returns.push((guard, Val::Symbolic(value)));
        } else {
            dead_arms.push(guard)
        }
    }
    SummaryInstance { input_domain: smtlib::Exp::Bool(true), domain, returns, dead_arms, reads }
}

#[test]
fn shape_key_preserves_constructors_vector_lengths_and_enum_payloads() {
    smt::configure_tastic(smt::Tactic::Qfaufbv);
    let mut shared = SharedState::<B64>::empty(Symtab::new());
    let definitions: Vec<crate::ir::Def<_, B64>> = crate::ir_parser::IrParser::new()
        .parse(
            &mut shared.symtab,
            crate::ir_lexer::new_ir_lexer(
                "enum zKind { zA, zB } union zBox { zValues: %vec(%enum zKind), zEmpty: %unit }",
            ),
        )
        .unwrap();
    shared.type_info = IRTypeInfo::new(&definitions);
    let kind = shared.symtab.lookup("zKind");
    let boxed = shared.symtab.lookup("zBox");
    let values = shared.symtab.lookup("zValues");
    let empty = shared.symtab.lookup("zEmpty");
    let f = shared.symtab.intern("zidentity");
    let arg = shared.symtab.intern("zargument");
    let ty = Box::leak(Box::new(Ty::Union(boxed)));
    shared.functions.insert(
        f,
        (
            vec![(arg, ty)],
            ty,
            Box::leak(vec![Instr::Copy(Loc::Id(RETURN), Exp::Id(arg), site()), Instr::End].into_boxed_slice()),
        ),
    );
    let lets = Bindings::default();
    let regs = RegisterBindings::new();
    let ctx = Context::new(Config::new());
    let mut solver = Solver::new(&ctx);
    let mut cache = Prototype::new(&shared, &lets);
    cache.set_enabled(true);
    let make = |n: usize, member| {
        Val::Ctor(
            values,
            Box::new(Val::Vector(
                (0..n).map(|_| Val::Enum(EnumMember { enum_id: EnumId::from_name(kind), member })).collect(),
            )),
        )
    };
    for (n, member, builds, hits) in [(2, 0, 1, 0), (2, 1, 1, 1), (3, 1, 2, 1)] {
        let actual = make(n, member);
        let result = cache.call(f, &[actual], &regs, &mut solver, &BTreeSet::new()).unwrap().unwrap();
        let Val::Ctor(ctor, payload) = &result.returns[0].1 else { panic!("返回必须保留构造子") };
        assert_eq!(*ctor, values);
        let Val::Vector(payload) = payload.as_ref() else { panic!("返回必须保留向量") };
        assert_eq!(payload.len(), n);
        for v in payload {
            let expected = Val::<B64>::Enum(EnumMember { enum_id: EnumId::from_name(kind), member });
            assert!(solver
                .check_sat_with(
                    &smtlib::Exp::Neq(
                        Box::new(smt_value(v, site()).unwrap()),
                        Box::new(smt_value(&expected, site()).unwrap())
                    ),
                    site()
                )
                .is_unsat()
                .unwrap());
        }
        assert_eq!((cache.builds, cache.hits), (builds, hits));
    }
    let result =
        cache.call(f, &[Val::Ctor(empty, Box::new(Val::Unit))], &regs, &mut solver, &BTreeSet::new()).unwrap().unwrap();
    assert!(matches!(&result.returns[0].1,Val::Ctor(n,_) if *n==empty));
    assert_eq!(cache.builds, 3);
}
