//! 区域合并集成的差分判据。旧菱形实现必须不能通过带调用和真实嵌套的用例。
use super::*;
use std::collections::BTreeMap;

type Formula = smtlib::Exp<Sym>;

struct Path {
    records: Vec<RegionMergeRecord<B64>>,
    value: Val<B64>,
    events: Vec<Event<B64>>,
}

fn paths(instrs: Vec<Instr<Name, B64>>, shared: &SharedState<'static, B64>, inputs: usize, merge: bool) -> Vec<Path> {
    paths_with_memory(instrs, shared, inputs, merge, crate::memory::Memory::new())
}

fn paths_with_memory(
    instrs: Vec<Instr<Name, B64>>,
    shared: &SharedState<'static, B64>,
    inputs: usize,
    merge: bool,
    memory: crate::memory::Memory<B64>,
) -> Vec<Path> {
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let mut frame = make_frame(instrs);
    frame.set_memory(memory);
    frame.function_name = TOP_LEVEL_LET;
    for (name, ty) in &shared.registers {
        frame.regs_mut().insert(*name, false, UVal::Uninit(Box::leak(Box::new(ty.clone()))));
    }
    for index in 0..inputs {
        let symbol = solver.declare_const(smtlib::Ty::Bool, info());
        frame.vars_mut().insert(test_name(900 + index as u32), UVal::Init(Val::Symbolic(symbol)));
    }
    let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(merge));
    let output = Mutex::new(Vec::new());
    start_single(
        frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
        shared,
        &output,
        &|_, _, result, _, mut solver, output| match result {
            Ok((Run::Finished(value), frame)) => match solver.check_sat(info()) {
                SmtResult::Sat => output.lock().unwrap().push(Path {
                    records: frame.region_merge_records().to_vec(),
                    value,
                    events: solver.trace().to_vec().into_iter().rev().cloned().collect(),
                }),
                SmtResult::Unsat => (),
                result => panic!("完成路径的可满足性查询失败：{result:?}"),
            },
            Ok((Run::Dead, _)) | Err((ExecError::AssertionFailure(..), _)) => (),
            Err((ExecError::Type(..), _)) if solver.check_sat(info()).is_unsat().unwrap() => (),
            Err((error, _)) => panic!("差分执行失败：{error:?}"),
            _ => panic!("差分执行未正常返回"),
        },
    );
    output.into_inner().unwrap()
}

fn import(path: &Path, inputs: &[Sym], solver: &mut Solver<B64>) -> (Formula, Formula) {
    use smtlib::Exp::*;
    // 确定性的辅助等式可无条件定义：辅助变量只在对应 guard 内使用。
    // 先消去这些变量再检查覆盖，避免把路径局部的新鲜量误当成外部输入。
    let mut definitions = HashMap::new();
    fn auxiliary(exp: &Formula, input_count: usize) -> Option<(Sym, Formula)> {
        match exp {
            Eq(a, b) => match a.as_ref() {
                Var(symbol) if symbol.id as usize >= input_count && !b.variables().contains(symbol) => {
                    Some((*symbol, b.as_ref().clone()))
                }
                _ => match b.as_ref() {
                    Var(symbol) if symbol.id as usize >= input_count && !a.variables().contains(symbol) => {
                        Some((*symbol, a.as_ref().clone()))
                    }
                    _ => None,
                },
            },
            Or(a, b) if matches!(a.as_ref(), Not(_)) => auxiliary(b, input_count),
            _ => None,
        }
    }
    for event in &path.events {
        match event {
            Event::Smt(Def::DefineConst(symbol, exp), _, _) => {
                definitions.insert(*symbol, exp.clone());
            }
            Event::Smt(Def::Assert(exp), _, _) => {
                if let Some((symbol, value)) = auxiliary(exp, inputs.len()) {
                    definitions.insert(symbol, value);
                }
            }
            _ => (),
        }
    }
    fn expand(
        exp: &Formula,
        definitions: &HashMap<Sym, Formula>,
        names: &HashMap<Sym, Sym>,
        active: &mut HashSet<Sym>,
    ) -> Formula {
        exp.map_var(&mut |symbol| {
            Ok::<_, ()>(if let Some(value) = definitions.get(symbol) {
                assert!(active.insert(*symbol), "定义依赖不得成环");
                let value = expand(value, definitions, names, active);
                active.remove(symbol);
                value
            } else {
                Var(*names.get(symbol).expect("未定义的外部符号"))
            })
        })
        .unwrap()
    }
    let mut names = HashMap::new();
    for event in &path.events {
        if let Event::Smt(Def::DeclareConst(original, ty), _, location) = event {
            if definitions.contains_key(original) {
                continue;
            }
            let index = original.id as usize;
            let target = if index < inputs.len() { inputs[index] } else { solver.declare_const(ty.clone(), *location) };
            assert!(names.insert(*original, target).is_none());
        }
    }
    let translate = |exp: &Formula| expand(exp, &definitions, &names, &mut HashSet::new());
    let mut conditions = Bool(true);
    for event in &path.events {
        if let Event::Smt(Def::Assert(exp), _, _) = event {
            conditions = And(Box::new(conditions), Box::new(translate(exp)));
        }
    }
    (conditions, translate(&smt_value(&path.value, info()).unwrap()))
}

/// 同一组输入符号分别导入全部分叉迹和合并迹；Z3 同时检查返回关系与路径覆盖。
fn differential(
    instrs: Vec<Instr<Name, B64>>,
    shared: &SharedState<'static, B64>,
    inputs: usize,
    complete: bool,
) -> (usize, usize) {
    use smtlib::Exp::*;
    let forked = paths(instrs.clone(), shared, inputs, false);
    let merged = paths(instrs, shared, inputs, true);
    if merged.len() == 1 {
        assert!(!merged[0].records.is_empty(), "单路径用例必须实际完成区域合并，不能仅普通剪枝");
    }
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let input_symbols: Vec<_> = (0..inputs).map(|_| solver.declare_const(smtlib::Ty::Bool, info())).collect();
    let relation = |paths: &[Path], solver: &mut Solver<B64>| {
        let mut coverage = Bool(false);
        let mut returned = Bool(false);
        for path in paths {
            let (condition, value) = import(path, &input_symbols, solver);
            coverage = Or(Box::new(coverage), Box::new(condition.clone()));
            returned = Or(Box::new(returned), Box::new(And(Box::new(condition), Box::new(value))));
        }
        (coverage, returned)
    };
    let (fork_coverage, fork_result) = relation(&forked, &mut solver);
    let (merge_coverage, merge_result) = relation(&merged, &mut solver);
    assert!(
        solver.check_sat_with(&Neq(Box::new(fork_result), Box::new(merge_result)), info()).is_unsat().unwrap(),
        "合并返回值必须等价于各路径条件与返回值的合取之析取"
    );
    assert!(
        solver
            .check_sat_with(&Neq(Box::new(fork_coverage.clone()), Box::new(merge_coverage)), info())
            .is_unsat()
            .unwrap(),
        "合并不得改变覆盖"
    );
    if complete {
        assert!(
            solver.check_sat_with(&Not(Box::new(fork_coverage)), info()).is_unsat().unwrap(),
            "无 assume 的用例必须覆盖全部输入"
        );
    }
    (forked.len(), merged.len())
}

fn input(index: u32) -> Exp<Name> {
    Exp::Id(test_name(900 + index))
}

fn helper(shared: &mut SharedState<'static, B64>) -> Name {
    let function = shared.symtab.intern("zregion_pure_helper");
    let argument = shared.symtab.intern("zregion_helper_argument");
    let ty = Box::leak(Box::new(Ty::Bool));
    let params = vec![(argument, &*ty)];
    let body = Box::leak(
        vec![Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Not, vec![Exp::Id(argument)]), info()), Instr::End]
            .into_boxed_slice(),
    );
    shared.functions.insert(function, (params, ty, body));
    function
}

#[test]
fn region_merge_pure_call_and_short_circuit() {
    let mut shared = empty_shared_state();
    let function = helper(&mut shared);
    let program = vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(4),
        Instr::Call(Loc::Id(RETURN), false, function, vec![input(1)], info()),
        Instr::End,
    ];
    assert_eq!(differential(program, &shared, 2, true), (2, 1));
}

#[test]
fn region_merge_declared_union_constructors_are_pure() {
    let mut shared = empty_shared_state();
    let definitions = crate::ir_parser::IrParser::new()
        .parse(&mut shared.symtab, crate::ir_lexer::new_ir_lexer("union zResult { zPayload: %bool, zEmpty: %unit }"))
        .unwrap();
    shared.type_info = IRTypeInfo::new::<B64>(&definitions);
    let result = shared.symtab.lookup("zResult");
    let temporary = shared.symtab.intern("zconstructor_value");
    for (name, argument) in [("zPayload", input(1)), ("zEmpty", Exp::Unit)] {
        let constructor = shared.symtab.lookup(name);
        for through_helper in [false, true] {
            let arm = vec![
                Instr::Decl(temporary, Ty::Union(result), info()),
                Instr::Call(Loc::Id(temporary), false, constructor, vec![argument.clone()], info()),
                Instr::Copy(
                    Loc::Id(RETURN),
                    if name == "zPayload" {
                        Exp::Unwrap(constructor, Box::new(Exp::Id(temporary)))
                    } else {
                        Exp::Kind(constructor, Box::new(Exp::Id(temporary)))
                    },
                    info(),
                ),
            ];
            let mut program = vec![
                Instr::Jump(input(0), 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
                Instr::Goto(if through_helper { 4 } else { 6 }),
            ];
            if through_helper {
                let function = helper(&mut shared);
                let parameter = shared.functions[&function].0[0].0;
                let mut body = arm.clone();
                if name == "zPayload" {
                    body[1] = Instr::Call(Loc::Id(temporary), false, constructor, vec![Exp::Id(parameter)], info());
                }
                body.push(Instr::End);
                shared.functions.get_mut(&function).unwrap().2 = Box::leak(body.into_boxed_slice());
                let summaries = region_summary::function_effect_summaries(&shared);
                assert_eq!(summaries[&function].effect, primop::Effect::Pure);
                assert!(summaries[&function].rejection.is_none());
                program.push(Instr::Call(Loc::Id(RETURN), false, function, vec![input(1)], info()));
            } else {
                program.extend(arm);
            }
            program.push(Instr::End);
            // 每轮替换同名函数体，不能沿用上一轮的 CFG。
            shared.function_regions.lock().unwrap().clear();
            assert_eq!(differential(program, &shared, 2, true), (2, 1), "{name}, helper={through_helper}");
        }
    }
}

#[test]
fn region_merge_undeclared_call_rejected_only_when_reached() {
    let mut shared = empty_shared_state();
    let unknown = shared.symtab.intern("zUndeclaredConstructor");
    let function = helper(&mut shared);
    let call = Instr::Call(Loc::Id(RETURN), false, unknown, vec![Exp::Unit], info());
    shared.functions.get_mut(&function).unwrap().2 = Box::leak(vec![call.clone(), Instr::End].into_boxed_slice());
    let summaries = region_summary::function_effect_summaries(&shared);
    assert_eq!(summaries[&function].effect, primop::Effect::Unknown);
    for instr in [call, Instr::Call(Loc::Id(RETURN), false, function, vec![Exp::Bool(true)], info())] {
        assert!(region_summary::instruction_effect(TOP_LEVEL_LET, 0, &instr, &shared, &summaries).is_none());
        let mut frame = make_frame(vec![
            Instr::Jump(input(0), 3, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            Instr::Goto(4),
            instr,
            Instr::End,
        ]);
        let context = Context::new(Config::new());
        let mut solver = Solver::new(&context);
        let condition = solver.declare_const(smtlib::Ty::Bool, info());
        assert!(merge_region_for_test(condition, 3, &mut frame, &shared, &mut solver, info(), None, None)
            .unwrap()
            .is_none());
    }
}

#[test]
fn region_merge_list_construction_and_pattern_matching() {
    let mut shared = empty_shared_state();
    let definitions = crate::ir_parser::IrParser::new()
        .parse(&mut shared.symtab, crate::ir_lexer::new_ir_lexer("union zOption { zSome: %bool, zNone: %unit }"))
        .unwrap();
    shared.type_info = IRTypeInfo::new::<B64>(&definitions);
    let function = helper(&mut shared);
    let parameter = shared.functions[&function].0[0].0;
    let list = shared.symtab.intern("zlist_value");
    let value = shared.symtab.intern("zoption_value");
    let some = shared.symtab.lookup("zSome");
    let none = shared.symtab.lookup("zNone");
    let cons = primop::binary_primops()["cons"];
    assert_eq!(primop::binary_effect(cons), Some(primop::Effect::Pure));
    // 同时执行 cons、取头、取尾与空列表臂；None 的 unit 载荷来自真实 IR 写法。
    for remaining_element in [false, true] {
        let mut body = vec![
            Instr::Decl(list, Ty::List(Box::new(Ty::Bool)), info()),
            Instr::Decl(value, Ty::Union(shared.symtab.lookup("zOption")), info()),
        ];
        if remaining_element {
            body.push(Instr::PrimopBinary(Loc::Id(list), cons, Exp::Id(parameter), Exp::Id(list), info()));
        }
        let empty_pc = body.len() + 6;
        body.extend(vec![
            Instr::PrimopBinary(Loc::Id(list), cons, Exp::Id(parameter), Exp::Id(list), info()),
            Instr::Call(Loc::Id(value), false, some, vec![Exp::Call(Op::Head, vec![Exp::Id(list)])], info()),
            Instr::Copy(Loc::Id(list), Exp::Call(Op::Tail, vec![Exp::Id(list)]), info()),
            Instr::Jump(Exp::Call(Op::IsEmpty, vec![Exp::Id(list)]), empty_pc, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Unwrap(some, Box::new(Exp::Id(value))), info()),
            Instr::End,
            Instr::Call(Loc::Id(value), false, none, vec![Exp::Unit], info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Kind(some, Box::new(Exp::Id(value))), info()),
            Instr::End,
        ]);
        shared.functions.get_mut(&function).unwrap().2 = Box::leak(body.into_boxed_slice());
        let summaries = region_summary::function_effect_summaries(&shared);
        assert_eq!(summaries[&function].effect, primop::Effect::Pure);
        assert!(summaries[&function].rejection.is_none());
        shared.function_regions.lock().unwrap().clear();
        assert_eq!(
            differential(
                vec![
                    Instr::Jump(input(0), 3, info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                    Instr::Goto(4),
                    Instr::Call(Loc::Id(RETURN), false, function, vec![input(1)], info()),
                    Instr::End,
                ],
                &shared,
                2,
                true
            ),
            (2, 1)
        );
    }
}

/// 多个 End 共享虚拟出口，覆盖函数返回边界。
#[test]
fn region_merge_multiple_returns_common_virtual_exit() {
    let shared = empty_shared_state();
    let mut program = Vec::new();
    for index in 0..4 {
        let pc = program.len();
        program.push(Instr::Jump(input(index), pc + 3, info()));
        program.push(Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()));
        program.push(Instr::End);
    }
    program.push(Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()));
    program.push(Instr::End);
    assert_eq!(differential(program, &shared, 4, true), (5, 1));
}

#[test]
fn region_merge_nested_same_join_and_single_feasible_jump() {
    let shared = empty_shared_state();
    let program = vec![
        Instr::Jump(input(0), 4, info()),
        Instr::Jump(input(0), 4, info()),
        Instr::Copy(Loc::Id(RETURN), input(1), info()),
        Instr::Goto(8),
        Instr::Jump(input(1), 7, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
        Instr::Goto(8),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::End,
    ];
    assert_eq!(differential(program, &shared, 2, true), (3, 1));
}

#[test]
pub(super) fn region_merge_dead_arm_and_guarded_assume() {
    let shared = empty_shared_state();
    let assume = primop::unary_primops()["assume"];
    let program = vec![
        Instr::Jump(input(0), 4, info()),
        Instr::PrimopUnary(Loc::Id(RETURN), assume, Exp::Bool(false), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(5),
        Instr::Copy(Loc::Id(RETURN), input(1), info()),
        Instr::End,
    ];
    assert_eq!(differential(program, &shared, 2, false), (1, 1));
}

#[test]
fn region_merge_four_item_or_chain_differential() {
    fn emit(index: u32, program: &mut Vec<Instr<Name, B64>>) {
        let branch = program.len();
        program.push(Instr::Jump(input(index), 0, info()));
        if index < 3 {
            emit(index + 1, program);
        } else {
            program.push(Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()));
        }
        let goto = program.len();
        program.push(Instr::Goto(0));
        let taken = program.len();
        program.push(Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()));
        let join = program.len();
        program[branch] = Instr::Jump(input(index), taken, info());
        program[goto] = Instr::Goto(join);
    }
    let mut program = Vec::new();
    emit(0, &mut program);
    program.push(Instr::End);
    let mut analysis = crate::ir::regions::FunctionRegions::new(&program, HAVE_EXCEPTION);
    let branches: Vec<_> =
        program.iter().enumerate().filter_map(|(pc, instr)| matches!(instr, Instr::Jump(..)).then_some(pc)).collect();
    let joins: HashSet<_> = branches.iter().map(|pc| analysis.region(*pc).unwrap().join).collect();
    assert_eq!(joins.len(), 4, "四层 OR 必须有四个不同汇合点");
    let shared = empty_shared_state();
    assert_eq!(differential(program, &shared, 4, true), (5, 1));
}

#[test]
fn region_merge_seeded_random_pure_ir() {
    fn emit(depth: u32, seed: &mut u64, function: Name, program: &mut Vec<Instr<Name, B64>>) {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let index = (*seed >> 32) as u32 % 4;
        if depth == 0 {
            program.push(Instr::Call(Loc::Id(RETURN), false, function, vec![input(index)], info()));
            if *seed & 1 != 0 {
                program.push(Instr::PrimopUnary(
                    Loc::Id(RETURN),
                    primop::unary_primops()["not"],
                    Exp::Id(RETURN),
                    info(),
                ));
            }
            if *seed & 7 == 0 {
                let temporary = test_name(1000 + program.len() as u32);
                program.push(Instr::Decl(temporary, Ty::Unit, info()));
                program.push(Instr::PrimopUnary(
                    Loc::Id(temporary),
                    primop::unary_primops()["assume"],
                    input((*seed >> 16) as u32 % 4),
                    info(),
                ));
            }
            return;
        }
        let branch = program.len();
        program.push(Instr::Jump(input(index), 0, info()));
        emit(depth - 1, seed, function, program);
        let goto = program.len();
        program.push(Instr::Goto(0));
        let taken = program.len();
        emit(depth - 1, seed, function, program);
        let join = program.len();
        program[branch] = Instr::Jump(input(index), taken, info());
        program[goto] = Instr::Goto(join);
    }
    for initial in [1, 7, 42, 123, 0x5eed, 0xcafe, 0xdeadbeef, u64::MAX] {
        let mut shared = empty_shared_state();
        let function = helper(&mut shared);
        let mut seed = initial;
        let mut program = Vec::new();
        emit(3, &mut seed, function, &mut program);
        program.push(Instr::End);
        let counts = differential(program, &shared, 4, false);
        assert_eq!(counts.1, 1, "种子 {initial} 必须合并成单路径");
    }
}

#[test]
fn region_merge_single_arm_register_read_union_and_guard() {
    let mut shared = empty_shared_state();
    let register = shared.symtab.intern(Box::leak(zencode::encode("region_lazy_register").into_boxed_str()));
    let mut frame = make_frame(vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(4),
        Instr::Copy(Loc::Id(RETURN), Exp::Id(register), info()),
        Instr::End,
    ]);
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let condition = solver.declare_const(smtlib::Ty::Bool, info());
    frame.vars_mut().insert(test_name(900), UVal::Init(Val::Symbolic(condition)));
    frame.regs_mut().insert(register, false, UVal::Uninit(Box::leak(Box::new(Ty::Bool))));
    let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(true));
    let output = Mutex::new(0);
    start_single(
        frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
        &shared,
        &output,
        &move |_, _, result, _, solver, output| {
            let Ok((Run::Finished(_), frame)) = result else {
                panic!("单臂读取必须成功");
            };
            *output.lock().unwrap() += 1;
            assert!(frame.regs().get_last_if_initialized(register).is_some());
            let records = frame.region_merge_records();
            assert_eq!(records.len(), 1);
            assert_eq!(records[0].single_arm_reads.len(), 1);
            assert_eq!(records[0].single_arm_reads[0].guard, smtlib::Exp::Var(condition));
            assert_eq!(
                solver
                    .trace()
                    .to_vec()
                    .iter()
                    .filter(|event| matches!(event, Event::ReadReg(reg, _, _) if *reg == register))
                    .count(),
                1
            );
        },
    );
    assert_eq!(*output.lock().unwrap(), 1);
}

#[test]
fn region_merge_pow_int_fresh_equations_and_local_variable() {
    let shared = empty_shared_state();
    let base = test_name(960);
    let temporary = test_name(961);
    let program = vec![
        Instr::Decl(base, Ty::I128, info()),
        Instr::PrimopUnary(Loc::Id(base), primop::unary_primops()["isla_bool_to_bit"], input(1), info()),
        Instr::PrimopBinary(
            Loc::Id(base),
            primop::binary_primops()["zero_extend"],
            Exp::Id(base),
            Exp::I128(128),
            info(),
        ),
        Instr::Jump(input(0), 7, info()),
        Instr::Init(temporary, Ty::I128, Exp::I128(2), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(10),
        Instr::PrimopBinary(Loc::Id(base), primop::binary_primops()["pow_int"], Exp::Id(base), Exp::I128(3), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(base), Exp::I128(1)]), info()),
        Instr::Goto(10),
        Instr::End,
    ];
    let merged_paths = paths(program.clone(), &shared, 2, true);
    assert_eq!(merged_paths.len(), 1);
    assert!(
        merged_paths[0].records.iter().all(|record| record.input_symbols.iter().all(|symbol| symbol.id < 2)),
        "纯原语的新鲜中间定义不是自由输入"
    );
    assert_eq!(differential(program, &shared, 2, true), (2, 1));
}

pub(super) fn check_region_effect_rejection_and_negative_cache() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let mut frame = make_frame(vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(4),
        Instr::PrimopVariadic(
            Loc::Id(RETURN),
            primop::variadic_primops()["platform_write_mem"],
            Vec::new(),
            SourceLoc::new(0, 17, 1, 17, 8),
        ),
        Instr::End,
    ]);
    shared.symtab.set_files(vec!["region.sail"]);
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let condition = solver.declare_const(smtlib::Ty::Bool, info());
    let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(true));
    let queue = Worker::new_lifo();
    let sink = SingleForkSink { queue: &queue };
    let before = solver.trace().to_vec().len();
    for _ in 0..2 {
        let outcome = region_merge::try_region(
            condition,
            3,
            0,
            TaskId::fresh(),
            &mut Fraction::one(),
            PathTimeout::unlimited(),
            None,
            &sink,
            &mut frame,
            &state,
            &shared,
            &mut solver,
            info(),
        )
        .unwrap();
        assert!(matches!(outcome, region_merge::RegionResult::Rejected));
        assert_eq!(solver.transaction_depth(), 0);
        assert_eq!(solver.trace().to_vec().len(), before);
    }
    assert!(queue.is_empty());
    let report = shared.execution_stats.merge_json();
    assert_eq!(report["negative_cache_hits"], 1);
    let detail = shared.execution_stats.arm_unsupported_json(&shared.symtab);
    assert_eq!(detail["top"][0]["reason"], "state_effect");
    assert_eq!(detail["top"][0]["target_pc"], 3);
    assert_eq!(detail["top"][0]["location"], "region.sail 17:1 - 17:8");
}

pub(super) fn check_region_rejection_locations_and_budget() {
    let shared = empty_shared_state();
    let mut frame = make_frame(vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(4),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
        Instr::End,
    ]);
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let condition = solver.declare_const(smtlib::Ty::Bool, info());
    let state = TaskState::new()
        .with_execution_limits(ExecutionLimits::default().with_path_merging(true))
        .with_region_step_budget(0);
    let queue = Worker::new_lifo();
    assert!(matches!(
        region_merge::try_region(
            condition,
            3,
            0,
            TaskId::fresh(),
            &mut Fraction::one(),
            PathTimeout::unlimited(),
            None,
            &SingleForkSink { queue: &queue },
            &mut frame,
            &state,
            &shared,
            &mut solver,
            info()
        )
        .unwrap(),
        region_merge::RegionResult::Rejected
    ));
    assert_eq!(solver.transaction_depth(), 0);
    assert_eq!(frame.pc, 0);
    assert!(state.region_negative_cache.lock().unwrap().is_empty(), "动态预算拒绝不能缓存");
    let loop_body: Vec<Instr<Name, B64>> =
        vec![Instr::Jump(input(0), 3, info()), Instr::Goto(0), Instr::End, Instr::End];
    let mut regions = crate::ir::regions::FunctionRegions::new(&loop_body, HAVE_EXCEPTION);
    assert_eq!(regions.region(0), Err(crate::ir::regions::RegionRejection::HasBackEdge));
}

pub(super) fn check_region_read_after_write_location() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    shared.symtab.set_files(vec!["region.sail"]);
    let reg = shared.symtab.intern("zregister");
    let source = SourceLoc::new(0, 23, 1, 23, 10);
    let mut frame = make_frame(vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(5),
        Instr::Copy(Loc::Id(reg), Exp::Bool(true), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), source),
        Instr::End,
    ]);
    frame.regs_mut().insert(reg, false, UVal::Init(Val::Bool(false)));
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let condition = solver.declare_const(smtlib::Ty::Bool, info());
    assert!(merge_region_for_test(condition, 3, &mut frame, &shared, &mut solver, info(), None, None)
        .unwrap()
        .is_none());
    let report = shared.execution_stats.arm_unsupported_json(&shared.symtab);
    assert_eq!(report["top"][0]["reason"], "register_read_after_write");
    assert_eq!(report["top"][0]["source_loc"], serde_json::json!(source));
}

#[test]
fn region_merge_inner_commit_then_outer_rollback_with_assertion() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let asserted = shared.symtab.intern("zasserted");
    let parameter = test_name(971);
    let body = Box::leak(
        vec![
            Instr::PrimopBinary(
                Loc::Id(RETURN),
                primop::binary_primops()["optimistic_assert"],
                Exp::Id(parameter),
                Exp::String("条件".into()),
                info(),
            ),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::End,
        ]
        .into_boxed_slice(),
    );
    shared.functions.insert(asserted, (vec![(parameter, &Ty::Bool)], &Ty::Bool, body));
    let reg = shared.symtab.intern("zregister");
    shared.registers.insert(reg, Ty::Bool);
    let unit = test_name(970);
    let program = vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(11),
        Instr::Jump(input(1), 7, info()),
        Instr::Decl(unit, Ty::Unit, info()),
        Instr::Call(Loc::Id(RETURN), false, asserted, vec![input(2)], info()),
        Instr::Goto(8),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
        Instr::Copy(Loc::Id(reg), Exp::Bool(true), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
        Instr::Goto(11),
        Instr::End,
    ];
    // 寄存器由入口初始化；外层的写后读只能在内层已提交之后触发拒绝。
    // 此处先用真实执行直接检查拒绝不会泄漏到调度边界。
    assert_eq!(differential(program.clone(), &shared, 3, false), (3, 2));
    let mut frame = make_frame(program);
    frame.regs_mut().insert(reg, false, UVal::Init(Val::Bool(false)));
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    for index in 0..3 {
        let symbol = solver.declare_const(smtlib::Ty::Bool, info());
        frame.vars_mut().insert(test_name(900 + index), UVal::Init(Val::Symbolic(symbol)));
    }
    assert!(merge_region_for_test(Sym { id: 0 }, 3, &mut frame, &shared, &mut solver, info(), None, None)
        .unwrap()
        .is_none());
    assert!(frame.region_merge_records().is_empty(), "内层提交后外层回滚必须丢弃全部新记录");
    let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(true));
    let output = Mutex::new(0);
    start_single(
        frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
        &shared,
        &output,
        &|_, _, result, _, solver, output| {
            assert_eq!(solver.transaction_depth(), 0);
            match result {
                Ok((Run::Finished(_), _)) => *output.lock().unwrap() += 1,
                Err((ExecError::AssertionFailure(..), _)) => (),
                _ => panic!("拒绝必须在区域边界回滚"),
            }
        },
    );
    assert_eq!(*output.lock().unwrap(), 2);
    assert!(shared.execution_stats.merge_json()["failure_reasons"]["register_read_after_write"].as_u64().unwrap() > 0);
}

fn policy_limits(shared: &SharedState<B64>, rules: Vec<(Name, crate::config::MergeMode)>) -> ExecutionLimits {
    use crate::config::{ExecutionLimitsConfig, MergePolicyConfig, MergePolicySelectorConfig};
    let config = ExecutionLimitsConfig {
        merge_policy: Some(
            rules
                .into_iter()
                .map(|(name, mode)| MergePolicyConfig {
                    mode,
                    selector: MergePolicySelectorConfig::Function(shared.symtab.to_str(name).to_owned()),
                })
                .collect(),
        ),
        ..ExecutionLimitsConfig::default()
    };
    ExecutionLimits::default().with_config(&config, &shared.symtab)
}

#[test]
fn region_merge_force_process_failure_and_off_conflict() {
    use crate::config::MergeMode;
    if let Ok(case) = std::env::var("ISLA_I2_FORCE_CHILD") {
        let mut shared = empty_shared_state();
        let root = shared.symtab.intern("zroot");
        let callee = helper(&mut shared);
        let argument = test_name(980);
        shared.functions.insert(
            callee,
            (
                vec![(argument, &Ty::Bool)],
                &Ty::Bool,
                Box::leak(
                    vec![
                        Instr::Jump(Exp::Id(argument), 3, info()),
                        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                        Instr::Goto(4),
                        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
                        Instr::End,
                    ]
                    .into_boxed_slice(),
                ),
            ),
        );
        let program = if case == "off" {
            vec![
                Instr::Jump(input(0), 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                Instr::Goto(4),
                Instr::Call(Loc::Id(RETURN), false, callee, vec![input(1)], info()),
                Instr::End,
            ]
        } else if case == "static" {
            vec![
                Instr::Jump(input(0), 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                Instr::Goto(4),
                Instr::PrimopVariadic(
                    Loc::Id(RETURN),
                    primop::variadic_primops()["platform_write_mem"],
                    Vec::new(),
                    info(),
                ),
                Instr::End,
            ]
        } else {
            vec![
                Instr::Jump(input(0), 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                Instr::Goto(4),
                Instr::Exit(ExitCause::Explicit, info()),
                Instr::End,
            ]
        };
        let rules = if case == "off" {
            vec![(root, MergeMode::Force), (callee, MergeMode::Off)]
        } else {
            vec![(root, MergeMode::Force)]
        };
        let state = TaskState::new().with_execution_limits(policy_limits(&shared, rules));
        let mut frame = make_frame(program);
        frame.function_name = root;
        let context = Context::new(Config::new());
        let mut solver = Solver::new(&context);
        for index in 0..2 {
            let symbol = solver.declare_const(smtlib::Ty::Bool, info());
            frame.vars_mut().insert(test_name(900 + index), UVal::Init(Val::Symbolic(symbol)));
        }
        let queue = Worker::new_lifo();
        let result = run_loop(
            0,
            TaskId::fresh(),
            &mut Fraction::one(),
            PathTimeout::unlimited(),
            None,
            &SingleForkSink { queue: &queue },
            &mut frame,
            &state,
            &shared,
            &mut solver,
        );
        panic!("强制失败必须退出进程：{}", result.is_ok());
    }
    for case in ["static", "dynamic", "off"] {
        let started = Instant::now();
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .arg("--exact")
            .arg("executor::tests::region_merge_tests::region_merge_force_process_failure_and_off_conflict")
            .arg("--nocapture")
            .env("ISLA_I2_FORCE_CHILD", case)
            .env("ISLA_STATS", "1")
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(speculation::FORCE_MERGE_EXIT_CODE),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(started.elapsed() < Duration::from_secs(10));
        let stderr = String::from_utf8(output.stderr).unwrap();
        let diagnostic: serde_json::Value =
            stderr.lines().find_map(|line| serde_json::from_str(line).ok()).expect("必须输出结构化诊断");
        let stats: serde_json::Value = stderr
            .lines()
            .find_map(|line| line.strip_prefix("[MERGE_STATS] "))
            .map(|line| serde_json::from_str(line).unwrap())
            .expect("强退前必须报告规则统计");
        if case == "off" {
            assert_eq!(stats["rules"]["0"]["failure_reasons"]["policy_off"], 1);
        }
        assert_eq!(diagnostic["kind"], "force_region_merge_failure");
        assert!(diagnostic["rule"].is_u64());
        if case == "off" {
            assert_eq!(diagnostic["reason"], "policy_off");
            assert!(!diagnostic["force_origin"].is_null());
        }
    }
}

#[test]
fn region_merge_policy_inheritance_and_global_off() {
    use crate::config::MergeMode;
    for (outer, inner, expected) in
        [(MergeMode::Adaptive, Some(MergeMode::Off), 3), (MergeMode::Adaptive, None, 1), (MergeMode::Force, None, 1)]
    {
        let mut shared = empty_shared_state();
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let root = shared.symtab.intern("zroot");
        let callee = helper(&mut shared);
        let argument = test_name(981);
        shared.functions.insert(
            callee,
            (
                vec![(argument, &Ty::Bool)],
                &Ty::Bool,
                Box::leak(
                    vec![
                        Instr::Jump(Exp::Id(argument), 3, info()),
                        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                        Instr::Goto(4),
                        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
                        Instr::End,
                    ]
                    .into_boxed_slice(),
                ),
            ),
        );
        let mut rules = vec![(root, outer)];
        if let Some(inner) = inner {
            rules.push((callee, inner));
        }
        let state = TaskState::new().with_execution_limits(policy_limits(&shared, rules));
        let mut frame = make_frame(vec![
            Instr::Jump(input(0), 3, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            Instr::Goto(4),
            Instr::Call(Loc::Id(RETURN), false, callee, vec![input(1)], info()),
            Instr::End,
        ]);
        frame.function_name = root;
        let context = Context::new(Config::new());
        let mut solver = Solver::new(&context);
        for index in 0..2 {
            let symbol = solver.declare_const(smtlib::Ty::Bool, info());
            frame.vars_mut().insert(test_name(900 + index), UVal::Init(Val::Symbolic(symbol)));
        }
        let output = Mutex::new(0);
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            &shared,
            &output,
            &|_, _, result, _, _, output| {
                assert!(matches!(result, Ok((Run::Finished(_), _))));
                *output.lock().unwrap() += 1;
            },
        );
        assert_eq!(*output.lock().unwrap(), expected);
        assert!(shared.execution_stats.merge_json()["rules"]["0"]["attempts"].as_u64().unwrap() > 0);
    }
}

#[test]
fn region_merge_callee_have_exception_write_rejects() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let function = helper(&mut shared);
    shared.functions.get_mut(&function).unwrap().2 = Box::leak(
        vec![
            Instr::Copy(Loc::Id(HAVE_EXCEPTION), Exp::Bool(false), info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::End,
        ]
        .into_boxed_slice(),
    );
    let mut frame = make_frame(vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(4),
        Instr::Call(Loc::Id(RETURN), false, function, vec![input(1)], info()),
        Instr::End,
    ]);
    frame.lets_mut().insert(HAVE_EXCEPTION, UVal::Init(Val::Bool(false)));
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let condition = solver.declare_const(smtlib::Ty::Bool, info());
    frame.vars_mut().insert(test_name(901), UVal::Init(Val::Bool(true)));
    assert!(merge_region_for_test(condition, 3, &mut frame, &shared, &mut solver, info(), None, None)
        .unwrap()
        .is_none());
    assert_eq!(shared.execution_stats.merge_json()["failure_reasons"]["callee_state_write"], 1);
}

#[test]
fn region_merge_non_returning_helper_exempts_effects_but_rejects_executed_exit() {
    let mut shared = empty_shared_state();
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let throwing = shared.symtab.intern("zthrowing");
    let wrapper = helper(&mut shared);
    let argument = shared.functions[&wrapper].0[0].0;
    shared.functions.insert(
        throwing,
        (
            Vec::new(),
            &Ty::Bool,
            Box::leak(
                vec![
                    Instr::Copy(Loc::Id(CURRENT_EXCEPTION), Exp::Unit, info()),
                    Instr::Copy(Loc::Id(HAVE_EXCEPTION), Exp::Bool(true), info()),
                    Instr::Arbitrary,
                ]
                .into_boxed_slice(),
            ),
        ),
    );
    shared.functions.get_mut(&wrapper).unwrap().2 = Box::leak(
        vec![
            Instr::Jump(Exp::Id(argument), 3, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::End,
            Instr::Call(Loc::Id(RETURN), false, throwing, Vec::new(), info()),
            Instr::Copy(Loc::Id(CURRENT_EXCEPTION), Exp::Unit, info()),
            Instr::End,
        ]
        .into_boxed_slice(),
    );
    let summaries = region_summary::function_effect_summaries(&shared);
    assert!(summaries[&throwing].non_returning);
    assert!(!summaries[&wrapper].non_returning);
    assert_eq!(summaries[&wrapper].effect, primop::Effect::Pure);
    assert_eq!(
        differential(
            vec![
                Instr::Jump(input(0), 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                Instr::Goto(4),
                Instr::Call(Loc::Id(RETURN), false, wrapper, vec![Exp::Bool(false)], info()),
                Instr::End,
            ],
            &shared,
            1,
            true
        ),
        (2, 1)
    );
    for execute_exception in [false, true] {
        let mut frame = make_frame(vec![
            Instr::Jump(input(0), 3, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            Instr::Goto(4),
            Instr::Call(Loc::Id(RETURN), false, wrapper, vec![Exp::Bool(execute_exception)], info()),
            Instr::End,
        ]);
        let context = Context::new(Config::new());
        let mut solver = Solver::new(&context);
        let condition = solver.declare_const(smtlib::Ty::Bool, info());
        let result = merge_region_for_test(condition, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap();
        assert_eq!(result.is_some(), !execute_exception);
        if execute_exception {
            let stats = shared.execution_stats.arm_unsupported_json(&shared.symtab);
            assert_eq!(stats["top"][0]["reason"], "region_escaped");
            assert_eq!(stats["top"][0]["rejected_function"], "region_pure_helper");
            assert_eq!(stats["top"][0]["target_pc"], 3);
            assert!(frame.region_merge_records().is_empty(), "拒绝后必须回滚合并记录");
            assert!(
                matches!(frame.lets().get(&HAVE_EXCEPTION), Some(UVal::Init(Val::Bool(false)))),
                "异常出口拒绝不得执行异常状态写入"
            );
        }
    }
}

#[test]
fn region_merge_non_returning_requires_all_paths_and_preserves_normal_writes() {
    let mut shared = empty_shared_state();
    let function = helper(&mut shared);
    let argument = shared.functions[&function].0[0].0;
    let register = shared.symtab.intern("znormal_write");
    shared.registers.insert(register, Ty::Bool);
    shared.functions.get_mut(&function).unwrap().2 = Box::leak(
        vec![
            Instr::Jump(Exp::Id(argument), 4, info()),
            Instr::Copy(Loc::Id(HAVE_EXCEPTION), Exp::Bool(true), info()),
            Instr::Arbitrary,
            Instr::End,
            Instr::Copy(Loc::Id(register), Exp::Bool(true), info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::End,
        ]
        .into_boxed_slice(),
    );
    let summaries = region_summary::function_effect_summaries(&shared);
    assert!(!summaries[&function].non_returning);
    assert_eq!(summaries[&function].effect, primop::Effect::WritesState);
    let mut frame = make_frame(vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(4),
        Instr::Call(Loc::Id(RETURN), false, function, vec![Exp::Bool(true)], info()),
        Instr::End,
    ]);
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let condition = solver.declare_const(smtlib::Ty::Bool, info());
    assert!(merge_region_for_test(condition, 3, &mut frame, &shared, &mut solver, info(), None, None)
        .unwrap()
        .is_none());
}

#[test]
fn region_merge_non_returning_fixed_point_is_conservative_for_recursion_and_exception_state() {
    let mut shared = empty_shared_state();
    let a = shared.symtab.intern("za");
    let b = shared.symtab.intern("zb");
    let call = |function| Instr::Call(Loc::Id(RETURN), false, function, Vec::new(), info());
    let throwing = || vec![Instr::Copy(Loc::Id(HAVE_EXCEPTION), Exp::Bool(true), info()), Instr::Arbitrary];
    for (body_a, body_b, expected_a, expected_b) in [
        (vec![call(b), Instr::End], throwing(), true, true),
        (vec![call(a), Instr::End], throwing(), false, true),
        (vec![call(b), Instr::End], vec![call(a), Instr::End], false, false),
        (
            vec![Instr::Jump(input(0), 2, info()), call(a), Instr::Exit(ExitCause::Explicit, info())],
            throwing(),
            false,
            true,
        ),
        (vec![Instr::Exit(ExitCause::MatchFailure, info())], throwing(), true, true),
        (vec![Instr::Arbitrary], throwing(), false, true),
        (
            vec![Instr::Copy(Loc::Id(HAVE_EXCEPTION), Exp::Bool(true), info()), Instr::Goto(2), Instr::End],
            throwing(),
            true,
            true,
        ),
        (
            vec![
                Instr::Copy(Loc::Id(HAVE_EXCEPTION), Exp::Bool(true), info()),
                Instr::Copy(Loc::Id(HAVE_EXCEPTION), Exp::Bool(false), info()),
                Instr::End,
            ],
            throwing(),
            false,
            true,
        ),
        (vec![Instr::Goto(0)], throwing(), false, true),
        (vec![call(b), Instr::Exit(ExitCause::Explicit, info())], vec![Instr::Goto(0)], false, false),
        (
            vec![call(b), Instr::Copy(Loc::Id(HAVE_EXCEPTION), Exp::Bool(true), info()), Instr::End],
            vec![Instr::End],
            true,
            false,
        ),
        (
            vec![
                Instr::Copy(Loc::Id(HAVE_EXCEPTION), input(0), info()),
                Instr::Jump(Exp::Id(HAVE_EXCEPTION), 3, info()),
                Instr::Exit(ExitCause::Explicit, info()),
                Instr::Copy(Loc::Id(HAVE_EXCEPTION), Exp::Bool(false), info()),
                Instr::End,
            ],
            throwing(),
            false,
            true,
        ),
        (vec![Instr::Jump(Exp::Id(HAVE_EXCEPTION), 2, info()), Instr::End, Instr::Arbitrary], throwing(), false, true),
    ] {
        shared.functions.insert(a, (Vec::new(), &Ty::Bool, Box::leak(body_a.into_boxed_slice())));
        shared.functions.insert(b, (Vec::new(), &Ty::Bool, Box::leak(body_b.into_boxed_slice())));
        let summaries = region_summary::function_effect_summaries(&shared);
        assert_eq!(summaries[&a].non_returning, expected_a);
        assert_eq!(summaries[&b].non_returning, expected_b);
    }
}

#[test]
fn region_merge_unique_monomorphize_and_retry_in_real_arms() {
    let shared = empty_shared_state();
    let result = test_name(990);
    let temporary = test_name(991);
    let program = vec![
        Instr::Decl(result, Ty::Bits(128), info()),
        Instr::PrimopUnary(Loc::Id(result), primop::unary_primops()["isla_bool_to_bit"], input(0), info()),
        Instr::PrimopBinary(
            Loc::Id(result),
            primop::binary_primops()["zero_extend"],
            Exp::Id(result),
            Exp::I128(128),
            info(),
        ),
        Instr::Jump(input(0), 9, info()),
        Instr::Monomorphize(test_name(900), Ty::Bool, info()),
        Instr::Decl(temporary, Ty::I128, info()),
        Instr::PrimopBinary(
            Loc::Id(temporary),
            primop::binary_primops()["pow_int"],
            Exp::I128(3),
            Exp::Id(result),
            info(),
        ),
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(temporary), Exp::I128(3)]), info()),
        Instr::Goto(13),
        Instr::Monomorphize(test_name(900), Ty::Bool, info()),
        Instr::Decl(temporary, Ty::I128, info()),
        Instr::PrimopBinary(
            Loc::Id(temporary),
            primop::binary_primops()["pow_int"],
            Exp::I128(3),
            Exp::Id(result),
            info(),
        ),
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(temporary), Exp::I128(3)]), info()),
        Instr::End,
    ];
    assert_eq!(differential(program, &shared, 1, true), (2, 1));
}

#[test]
fn region_merge_unique_retry_gate_preserves_guard_checkpoint_and_fraction() {
    let shared = empty_shared_state();
    let mut frame = make_frame(vec![Instr::Jump(input(0), 1, info()), Instr::End]);
    frame.speculation_mode = SpeculationMode::On;
    frame.region_execution = Some(region_merge::RegionExecution {
        region: Arc::new(crate::ir::regions::Region {
            branch_pc: 0,
            join: crate::ir::regions::RegionPoint::Instruction(1),
            nodes: Default::default(),
            kind: crate::ir::regions::RegionKind::Reconvergent,
            local_variables: Default::default(),
        }),
        entry_depth: 0,
        write_depth: 0,
        depth: 1,
        remaining: Arc::new(AtomicUsize::new(10)),
        mode: crate::config::MergeMode::Adaptive,
        origin: (frame.function_name, 0, info()),
    });
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let symbol = solver.declare_const(smtlib::Ty::Bool, info());
    let tx = solver.start_transaction_with_guard(Some(smtlib::Exp::Var(symbol)));
    let state = TaskState::new();
    let queue = Worker::new_lifo();
    let mut fraction = Fraction::one();
    symbolic_length::fork_retry_operand(
        symbol,
        smtlib::Exp::Var(symbol),
        smtlib::Exp::Not(Box::new(smtlib::Exp::Var(symbol))),
        &[Val::Symbolic(symbol)],
        info(),
        TaskId::fresh(),
        &mut fraction,
        None,
        &SingleForkSink { queue: &queue },
        &mut frame,
        &state,
        &mut solver,
    )
    .unwrap();
    assert!(queue.is_empty());
    assert!(fraction.is_one());
    assert_eq!(solver.transaction_depth(), 1);
    solver.rollback_transaction(tx);
    assert!(solver.check_sat_with(&smtlib::Exp::Not(Box::new(smtlib::Exp::Var(symbol))), info()).is_sat().unwrap());
    assert!(shared.function_regions.lock().unwrap().is_empty());
}

#[test]
fn region_merge_nested_single_read_keeps_complete_guard() {
    let mut shared = empty_shared_state();
    let register = shared.symtab.intern("zregister");
    let mut frame = make_frame(vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(7),
        Instr::Jump(input(1), 6, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(7),
        Instr::Copy(Loc::Id(RETURN), Exp::Id(register), info()),
        Instr::End,
    ]);
    frame.regs_mut().insert(register, false, UVal::Uninit(&Ty::Bool));
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let g = solver.declare_const(smtlib::Ty::Bool, info());
    let h = solver.declare_const(smtlib::Ty::Bool, info());
    frame.vars_mut().insert(test_name(900), UVal::Init(Val::Symbolic(g)));
    frame.vars_mut().insert(test_name(901), UVal::Init(Val::Symbolic(h)));
    let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(true));
    start_single(
        frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
        &shared,
        &(),
        &move |_, _, result, _, mut solver, _| {
            let Ok((Run::Finished(_), frame)) = result else {
                panic!("嵌套读取必须成功合并");
            };
            let exact = smtlib::Exp::And(Box::new(smtlib::Exp::Var(g)), Box::new(smtlib::Exp::Var(h)));
            for record in frame.region_merge_records() {
                for read in &record.single_arm_reads {
                    assert!(
                        solver
                            .check_sat_with(
                                &smtlib::Exp::Neq(Box::new(read.guard.clone()), Box::new(exact.clone())),
                                info()
                            )
                            .is_unsat()
                            .unwrap(),
                        "外层不得把嵌套读取的 guard 弱化"
                    );
                }
            }
        },
    );
}

#[test]
fn region_merge_partial_register_write_reuses_original_unwritten_fields() {
    let mut shared = empty_shared_state();
    let register = shared.symtab.intern("zregister");
    let structure = shared.symtab.intern("zstructure");
    let x = shared.symtab.intern("zx");
    let y = shared.symtab.intern("zy");
    shared.type_info.structs.insert(structure, std::collections::BTreeMap::from([(x, Ty::Bool), (y, Ty::Bool)]));
    let mut frame = make_frame(vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Field(Box::new(Exp::Id(register)), y), info()),
        Instr::Goto(5),
        Instr::Copy(Loc::Field(Box::new(Loc::Id(register)), x), Exp::Bool(true), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::End,
    ]);
    frame.regs_mut().insert(register, false, UVal::Uninit(Box::leak(Box::new(Ty::Struct(structure)))));
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let condition = solver.declare_const(smtlib::Ty::Bool, info());
    frame.vars_mut().insert(test_name(900), UVal::Init(Val::Symbolic(condition)));
    let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(true));
    let count = Mutex::new(0);
    start_single(
        frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
        &shared,
        &count,
        &move |_, _, result, _, mut solver, count| {
            let Ok((Run::Finished(_), frame)) = result else {
                panic!("部分字段写与另一臂读取必须合并成功");
            };
            *count.lock().unwrap() += 1;
            let Val::Struct(merged) = frame.regs().get_last_if_initialized(register).unwrap() else {
                panic!("必须保留结构寄存器");
            };
            let events = solver.trace().to_vec();
            let original = events
                .iter()
                .find_map(|event| match event {
                    Event::ReadReg(reg, _, Val::Struct(fields)) if *reg == register => Some(&fields[&y]),
                    _ => None,
                })
                .expect("另一臂读取必须保存前置值");
            let unequal = smtlib::Exp::Neq(
                Box::new(smt_value(&merged[&y], info()).unwrap()),
                Box::new(smt_value(original, info()).unwrap()),
            );
            assert!(
                solver.check_sat_with(&unequal, info()).is_unsat().unwrap(),
                "未写字段在全部分支中必须等于同一前置值"
            );
        },
    );
    assert_eq!(*count.lock().unwrap(), 1);
}

#[test]
fn region_merge_repeated_pure_calls_keep_distinct_local_initial_values() {
    let mut shared = empty_shared_state();
    let function = helper(&mut shared);
    let argument = test_name(1010);
    let local = test_name(1011);
    let first = test_name(1012);
    let second = test_name(1013);
    shared.functions.insert(
        function,
        (
            vec![(argument, &Ty::Bool)],
            &Ty::Bool,
            Box::leak(
                vec![
                    Instr::Decl(local, Ty::Bool, info()),
                    Instr::Jump(Exp::Id(argument), 4, info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(local), info()),
                    Instr::Goto(5),
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(local), info()),
                    Instr::End,
                ]
                .into_boxed_slice(),
            ),
        ),
    );
    let mut frame = make_frame(vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(8),
        Instr::Decl(first, Ty::Bool, info()),
        Instr::Decl(second, Ty::Bool, info()),
        Instr::Call(Loc::Id(first), false, function, vec![input(1)], info()),
        Instr::Call(Loc::Id(second), false, function, vec![input(1)], info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Neq, vec![Exp::Id(first), Exp::Id(second)]), info()),
        Instr::End,
    ]);
    frame.function_name = TOP_LEVEL_LET;
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let outer = solver.declare_const(smtlib::Ty::Bool, info());
    let inner = solver.declare_const(smtlib::Ty::Bool, info());
    frame.vars_mut().insert(test_name(900), UVal::Init(Val::Symbolic(outer)));
    frame.vars_mut().insert(test_name(901), UVal::Init(Val::Symbolic(inner)));
    let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(true));
    start_single(
        frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
        &shared,
        &(),
        &move |_, _, result, _, mut solver, _| {
            let Ok((Run::Finished(value), frame)) = result else {
                panic!("两次纯调用必须完成");
            };
            assert!(!frame.region_merge_records().is_empty());
            for selected in [true, false] {
                let guard = smtlib::Exp::And(
                    Box::new(smtlib::Exp::Var(outer)),
                    Box::new(if selected {
                        smtlib::Exp::Var(inner)
                    } else {
                        smtlib::Exp::Not(Box::new(smtlib::Exp::Var(inner)))
                    }),
                );
                assert!(
                    solver
                        .check_sat_with(
                            &smtlib::Exp::And(Box::new(guard), Box::new(smt_value(&value, info()).unwrap())),
                            info()
                        )
                        .is_sat()
                        .unwrap(),
                    "每次调用的未初始化局部值必须保持相互独立"
                );
            }
        },
    );
}

#[test]
fn region_merge_prior_fresh_definitions_remain_dependencies_after_next_merge() {
    let shared = empty_shared_state();
    let base = test_name(1020);
    let program = vec![
        Instr::Decl(base, Ty::I128, info()),
        Instr::PrimopUnary(Loc::Id(base), primop::unary_primops()["isla_bool_to_bit"], input(1), info()),
        Instr::PrimopBinary(
            Loc::Id(base),
            primop::binary_primops()["zero_extend"],
            Exp::Id(base),
            Exp::I128(128),
            info(),
        ),
        Instr::Jump(input(0), 6, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(8),
        Instr::PrimopBinary(Loc::Id(base), primop::binary_primops()["pow_int"], Exp::Id(base), Exp::I128(3), info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(base), Exp::I128(1)]), info()),
        Instr::Jump(input(1), 11, info()),
        Instr::Copy(Loc::Id(RETURN), input(0), info()),
        Instr::Goto(12),
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Not, vec![input(0)]), info()),
        Instr::End,
    ];
    let merged = paths(program, &shared, 2, true);
    assert_eq!(merged.len(), 1);
    assert!(merged[0].records.len() >= 2);
    for record in &merged[0].records {
        assert!(
            record.input_symbols.iter().all(|symbol| symbol.id < 2),
            "历史纯原语的新鲜定义不能在后续区域提交后重新变成自由输入"
        );
    }
}

#[test]
fn region_merge_force_static_validation_before_execution() {
    let mut shared = empty_shared_state();
    let function = shared.symtab.intern("zloop");
    shared.functions.insert(
        function,
        (
            Vec::new(),
            &Ty::Bool,
            Box::leak(
                vec![Instr::Jump(Exp::Bool(true), 3, info()), Instr::Goto(0), Instr::End, Instr::End]
                    .into_boxed_slice(),
            ),
        ),
    );
    let limits = policy_limits(&shared, vec![(function, crate::config::MergeMode::Force)]);
    let diagnostic = validate_force_regions(&shared, &limits).unwrap_err();
    let diagnostic: serde_json::Value =
        serde_json::from_str(&diagnostic).expect("加载期 Force 拒绝也必须给出结构化诊断");
    assert_eq!(diagnostic["rule"], 0);
    assert_eq!(diagnostic["function"], "loop");
    assert_eq!(diagnostic["branch_pc"], 0);
    assert_eq!(diagnostic["reason"], "has_back_edge");
}

#[test]
fn region_merge_recursive_effect_least_fixed_point() {
    use primop::Effect;
    let mut shared = empty_shared_state();
    let a = shared.symtab.intern("zrecursive_a");
    let b = shared.symtab.intern("zrecursive_b");
    let reg = shared.symtab.intern("zrecursive_register");
    shared.registers.insert(reg, Ty::Bool);
    for (body_a, body_b, expected) in [
        (vec![Instr::Call(Loc::Id(RETURN), false, a, Vec::new(), info()), Instr::End], vec![Instr::End], Effect::Pure),
        (
            vec![Instr::Call(Loc::Id(RETURN), false, b, Vec::new(), info()), Instr::End],
            vec![
                Instr::Copy(Loc::Id(reg), Exp::Bool(true), info()),
                Instr::Call(Loc::Id(RETURN), false, a, Vec::new(), info()),
                Instr::End,
            ],
            Effect::WritesState,
        ),
        (
            vec![Instr::Call(Loc::Id(RETURN), false, b, Vec::new(), info()), Instr::End],
            vec![
                Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
                Instr::Call(Loc::Id(RETURN), false, a, Vec::new(), info()),
                Instr::End,
            ],
            Effect::ReadsState,
        ),
    ] {
        shared.functions.insert(a, (Vec::new(), &Ty::Bool, Box::leak(body_a.into_boxed_slice())));
        shared.functions.insert(b, (Vec::new(), &Ty::Bool, Box::leak(body_b.into_boxed_slice())));
        let summaries = region_summary::function_effect_summaries(&shared);
        assert_eq!(summaries[&a].effect, expected);
        if expected != Effect::Pure {
            assert_eq!(summaries[&b].effect, expected);
        }
    }
}

/// ISLA_REGIONS_IR=/绝对路径/rv64d.ir cargo test -p isla-lib region_merge_real_ir_effects --offline --features smt-thread-interrupt -- --ignored --nocapture
#[test]
#[ignore = "需要外部 rv64d.ir；用 ISLA_REGIONS_IR 指定路径"]
fn region_merge_real_ir_effects() {
    let text = Box::leak(std::fs::read_to_string(std::env::var("ISLA_REGIONS_IR").unwrap()).unwrap().into_boxed_str());
    for configured in [false, true] {
        let mut symtab = Symtab::new();
        let mut definitions =
            crate::ir_parser::IrParser::new().parse(&mut symtab, crate::ir_lexer::new_ir_lexer(text)).unwrap();
        let types = IRTypeInfo::new(&definitions);
        let config_text = std::fs::read_to_string(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../agents/path_merge_call_support/",
            "baseline_config.toml"
        ))
        .unwrap();
        let constants = std::fs::read_to_string(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../agents/path_merge_call_support/baseline_config_const.toml"
        ))
        .unwrap();
        let config =
            ISAConfig::<B64>::parse(if configured { &constants } else { &config_text }, None, &symtab, &types).unwrap();
        if configured {
            assert_eq!(config.const_primops.len(), 45);
            assert_eq!(config.const_primops.values().filter(|(_, effect)| *effect == primop::Effect::Pure).count(), 43);
            assert_eq!(config.const_primops["sys_enable_experimental_extensions"].1, primop::Effect::Pure);
            for name in ["plat_get_16_random_bits", "speculate_conditional"] {
                assert_eq!(config.const_primops[name].1, primop::Effect::WritesState);
            }
        }
        crate::ir::insert_primops(&mut definitions, &symtab, AssertionMode::Optimistic, &config);
        let definitions = Box::leak(definitions.into_boxed_slice());
        let shared = SharedState::new(
            symtab,
            definitions,
            types,
            HashSet::new(),
            HashSet::new(),
            HashSet::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        let summaries = region_summary::function_effect_summaries(&shared);
        for function in [
            "zinternal_errorzIozK",
            "zget_xLPE",
            "zhartSupports",
            "zcurrentlyEnabled",
            "zpte_is_invalid",
            "zpte_is_non_leaf",
            "zpt_walk",
            "zupdate_PTE_Bits",
            "zcheck_PTE_permission",
            "zmatching_pma_bits_range",
        ] {
            eprintln!("诊断 const_primops={configured} {function}: {:?}", summaries[&shared.symtab.lookup(function)]);
        }
        for name in ["zpt_walk", "zupdate_PTE_Bits", "zcheck_PTE_permission", "zmatching_pma_bits_range"] {
            let function = shared.symtab.lookup(name);
            let mut constructors = 0;
            for (pc, instr) in shared.functions[&function].2.iter().enumerate() {
                if let Instr::Call(_, _, callee, _, _) = instr {
                    if shared.type_info.union_ctors.contains(callee) {
                        constructors += 1;
                        let rejection = region_summary::instruction_effect(function, pc, instr, &shared, &summaries);
                        eprintln!(
                            "构造子 const_primops={configured} {name} pc={pc} {}: {rejection:?}",
                            shared.symtab.to_str(*callee)
                        );
                        assert!(rejection.is_none(), "声明的联合构造子必须允许推演");
                    }
                }
            }
            assert!(constructors > 0, "真实 IR 必须覆盖构造子调用：{name}");
            if name != "zpt_walk" {
                assert!(summaries[&function].rejection.is_none(), "{name} 不应再有静态拒绝证据");
            } else {
                let rejection = summaries[&function].rejection.expect("pt_walk 仍含不可推演的调用");
                eprintln!(
                    "pt_walk 剩余传递拒绝 const_primops={configured}: {} pc={} {:?}",
                    shared.symtab.to_str(rejection.function),
                    rejection.pc,
                    rejection.location
                );
            }
        }
        for (function, expected) in [
            ("zinternal_errorzIozK", primop::Effect::WritesState),
            ("zget_xLPE", primop::Effect::ReadsState),
            // hartSupports 还读取全局 let vector_support_level，因此不是 Pure。
            ("zhartSupports", primop::Effect::ReadsState),
            // 必然抛异常的调用不再污染其调用者，正常路径的读状态仍保留。
            ("zcurrentlyEnabled", primop::Effect::ReadsState),
            ("zpte_is_invalid", primop::Effect::ReadsState),
            ("zpte_is_non_leaf", primop::Effect::Pure),
            ("zpt_walk", primop::Effect::WritesState),
            ("zupdate_PTE_Bits", primop::Effect::Pure),
            // 断言的约束通过带条件协议重放：WritesState 等级不代表必须拒绝。
            ("zcheck_PTE_permission", primop::Effect::WritesState),
            ("zmatching_pma_bits_range", primop::Effect::Pure),
        ] {
            let summary = &summaries[&shared.symtab.lookup(function)];
            eprintln!("const_primops={configured} {function}: {:?}", summary.effect);
            assert_eq!(summary.effect, expected, "const_primops={configured} {function}");
            assert_eq!(summary.non_returning, function == "zinternal_errorzIozK");
        }
        for name in ["zinternal_errorzIozK", "zreserved_behaviorzIozK"] {
            assert!(summaries[&shared.symtab.lookup(name)].non_returning);
        }
    }
}

#[test]
fn region_merge_records_json_lines_and_parallel_writes() {
    const CHILD: &str = "ISLA_I3_RECORD_CHILD";
    if std::env::var_os(CHILD).is_some() {
        let mut shared = empty_shared_state();
        let register = shared.symtab.intern("zrecord_register");
        shared.registers.insert(register, Ty::Bool);
        let program = vec![
            Instr::Jump(input(0), 3, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(register), info()),
            Instr::End,
        ];
        std::thread::scope(|scope| {
            for _ in 0..8 {
                let shared = &shared;
                let program = program.clone();
                scope.spawn(move || {
                    for _ in 0..4 {
                        assert_eq!(paths(program.clone(), shared, 1, true).len(), 1);
                    }
                });
            }
        });
        let assume = primop::unary_primops()["assume"];
        assert!(paths(
            vec![
                Instr::Jump(input(0), 3, info()),
                Instr::PrimopUnary(Loc::Id(RETURN), assume, Exp::Bool(false), info()),
                Instr::Goto(4),
                Instr::PrimopUnary(Loc::Id(RETURN), assume, Exp::Bool(false), info()),
                Instr::End,
            ],
            &shared,
            1,
            true
        )
        .is_empty());
        assert_eq!(
            paths(
                vec![
                    Instr::Jump(input(0), 3, info()),
                    Instr::PrimopUnary(Loc::Id(RETURN), assume, Exp::Bool(false), info()),
                    Instr::Goto(4),
                    Instr::Copy(Loc::Id(RETURN), Exp::Id(register), info()),
                    Instr::End,
                ],
                &shared,
                1,
                true
            )
            .len(),
            1
        );
        return;
    }
    let path = std::env::temp_dir().join(format!("isla-i3-records-{}.jsonl", std::process::id()));
    let file = std::fs::File::create(&path).unwrap();
    drop(file);
    let result = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "executor::tests::region_merge_tests::region_merge_records_json_lines_and_parallel_writes",
            "--nocapture",
        ])
        .env(CHILD, "1")
        .env("ISLA_MERGE_RECORDS", &path)
        .output()
        .unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let text = std::fs::read_to_string(&path).unwrap();
    std::fs::remove_file(path).unwrap();
    assert!(text.ends_with('\n'));
    let mut records: Vec<serde_json::Value> = text.lines().map(|line| serde_json::from_str(line).unwrap()).collect();
    assert_eq!(records.len(), 34, "每次成功提交只写一行，含死亡臂剪枝");
    let surviving = records.pop().unwrap();
    assert_eq!(surviving["single_arm_reads"].as_array().unwrap().len(), 1);
    assert_eq!(surviving["single_arm_reads"][0]["guard"]["expression"], "v0");
    let dead = records.pop().unwrap();
    assert_eq!(dead["outcome"], "dead");
    assert_eq!(dead["input_symbols"].as_array().unwrap().len(), 1);
    assert_eq!(dead["single_arm_reads"], serde_json::json!([]));
    let mut ids = HashSet::new();
    for record in records {
        assert!(ids.insert(record["record_id"].as_u64().unwrap()));
        assert_eq!(record["schema_version"], 2);
        assert!(record["function"].is_string());
        assert_eq!(record["branch_pc"], 0);
        assert_eq!(record["join"], serde_json::json!({"instruction":4}));
        assert!(record["source_loc"].is_object());
        assert_eq!(record["condition"]["name"], "v0");
        assert_eq!(record["condition"]["smt_id"], 0);
        assert_eq!(record["depth"], 1);
        let inputs = record["input_symbols"].as_array().unwrap();
        assert_eq!(inputs.len(), 2);
        for (index, input) in inputs.iter().enumerate() {
            assert_eq!(input["smt_id"], index);
            assert_eq!(input["type"], serde_json::json!({"kind":"bool"}));
        }
        let reads = record["single_arm_reads"].as_array().unwrap();
        assert_eq!(reads.len(), 1);
        assert_eq!(reads[0]["register"], "record_register");
        assert_eq!(reads[0]["guard"]["expression"], "v0");
        assert_eq!(reads[0]["guard"]["symbols"][0]["smt_id"], 0);
    }
}

#[test]
fn region_merge_force_toml_exits_with_rule_stats() {
    const CHILD: &str = "ISLA_I3_FORCE_TOML";
    if let Some(path) = std::env::var_os(CHILD) {
        let mut shared = empty_shared_state();
        let root = shared.symtab.intern("zforce_rejected");
        let reg = shared.symtab.intern("zforce_register");
        shared.registers.insert(reg, Ty::Bool);
        let program = vec![
            Instr::Jump(input(0), 3, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            Instr::Goto(5),
            Instr::Copy(Loc::Id(reg), Exp::Bool(true), info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Id(reg), info()),
            Instr::End,
        ];
        shared.functions.insert(root, (Vec::new(), &Ty::Bool, Box::leak(program.clone().into_boxed_slice())));
        let config = crate::config::ExecutionLimitsConfig::from_file(path).unwrap();
        shared.validate_merge_policy(&config).unwrap();
        let state =
            TaskState::new().with_execution_limits(ExecutionLimits::default().with_config(&config, &shared.symtab));
        let mut frame = make_frame(program);
        frame.function_name = root;
        frame.regs_mut().insert(reg, false, UVal::Init(Val::Bool(false)));
        let context = Context::new(Config::new());
        let mut solver = Solver::new(&context);
        let symbol = solver.declare_const(smtlib::Ty::Bool, info());
        frame.vars_mut().insert(test_name(900), UVal::Init(Val::Symbolic(symbol)));
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            &shared,
            &(),
            &|_, _, _, _, _, _| panic!("Force 拒绝必须终止整个进程"),
        );
        panic!("Force 拒绝不能正常返回");
    }
    let path = std::env::temp_dir().join(format!("isla-i3-force-{}.toml", std::process::id()));
    std::fs::write(
        &path,
        "[execution_limits]\n[[execution_limits.merge_policy]]\nmode = \"force\"\nfunction = \"force_rejected\"\n",
    )
    .unwrap();
    let started = Instant::now();
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "executor::tests::region_merge_tests::region_merge_force_toml_exits_with_rule_stats",
            "--nocapture",
        ])
        .env(CHILD, &path)
        .env("ISLA_STATS", "1")
        .output()
        .unwrap();
    std::fs::remove_file(path).unwrap();
    assert!(started.elapsed() < Duration::from_secs(10));
    assert_eq!(output.status.code(), Some(FORCE_MERGE_EXIT_CODE));
    let stderr = String::from_utf8(output.stderr).unwrap();
    let diagnostic: serde_json::Value = stderr.lines().find_map(|line| serde_json::from_str(line).ok()).unwrap();
    assert_eq!(diagnostic["rule"], 0);
    assert_eq!(diagnostic["reason"], "register_read_after_write");
    let report: serde_json::Value = stderr
        .lines()
        .find_map(|line| line.strip_prefix("[MERGE_STATS] "))
        .map(|line| serde_json::from_str(line).unwrap())
        .expect("Force 强退前必须输出统计");
    assert_eq!(report["rules"]["0"]["attempts"], 1);
    assert_eq!(report["rules"]["0"]["successes"], 0);
    assert_eq!(report["rules"]["0"]["failure_reasons"]["register_read_after_write"], 1);
}

#[test]
fn region_merge_effects_use_external_binding_and_reject_callee_vector_writes() {
    let mut shared = empty_shared_state();
    let caller = helper(&mut shared);
    // IR 名称碰巧叫 not，但外部绑定未知时不能借用同名原语的 Pure 分类。
    let alias = shared.symtab.intern("znot");
    shared.externs.insert(alias, (&[], &Ty::Bool, "unregistered_effect"));
    shared.functions.get_mut(&caller).unwrap().2 =
        Box::leak(vec![Instr::Call(Loc::Id(RETURN), false, alias, Vec::new(), info()), Instr::End].into_boxed_slice());
    assert_eq!(region_summary::function_effect_summaries(&shared)[&caller].effect, primop::Effect::Unknown);
    shared.functions.get_mut(&caller).unwrap().2 = Box::leak(
        vec![Instr::Call(Loc::Id(RETURN), false, WRITE_REGISTER_FROM_VECTOR, Vec::new(), info()), Instr::End]
            .into_boxed_slice(),
    );
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let mut frame = make_frame(vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(4),
        Instr::Call(Loc::Id(RETURN), false, caller, vec![Exp::Bool(true)], info()),
        Instr::End,
    ]);
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let symbol = solver.declare_const(smtlib::Ty::Bool, info());
    assert!(merge_region_for_test(symbol, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap().is_none());
    assert_eq!(shared.execution_stats.merge_json()["candidate_attempts"], 0, "被调函数写状态应在推演前拒绝");
}

#[test]
fn region_merge_configured_const_primop_effects() {
    const IR: &str = r#"
register zPC : %bv64
val zconfigured = "configured" : (%unit) -> %bool
val zcaller : (%unit) -> %bool
fn zcaller(zunit) {
  return = zconfigured(());
  end;
}
"#;
    for (entry, expected) in [
        ("configured = false", primop::Effect::Pure),
        ("configured = true", primop::Effect::Pure),
        ("configured = \"undefined : %bool\"", primop::Effect::WritesState),
        ("", primop::Effect::Unknown),
    ] {
        let (symtab, mut definitions) = parse_ir_string(IR);
        let types = IRTypeInfo::new(&definitions);
        let baseline = std::fs::read_to_string(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../agents/path_merge_call_support/baseline_config.toml"
        ))
        .unwrap();
        let baseline = baseline.replace("in_program_order = [\"sail_barrier\"]", "in_program_order = []");
        let config =
            ISAConfig::<B64>::parse(&format!("{baseline}\n[const_primops]\n{entry}\n"), None, &symtab, &types).unwrap();
        crate::ir::insert_primops(&mut definitions, &symtab, AssertionMode::Optimistic, &config);
        let definitions = Box::leak(definitions.into_boxed_slice());
        let shared = SharedState::new(
            symtab,
            definitions,
            types,
            HashSet::new(),
            HashSet::new(),
            HashSet::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        let summaries = region_summary::function_effect_summaries(&shared);
        assert_eq!(summaries[&shared.symtab.lookup("zcaller")].effect, expected, "配置条目：{entry}");
        if expected != primop::Effect::Unknown {
            let program = vec![
                Instr::Jump(input(0), 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
                Instr::Goto(4),
                Instr::Call(Loc::Id(RETURN), false, shared.symtab.lookup("zcaller"), vec![Exp::Unit], info()),
                Instr::End,
            ];
            if expected == primop::Effect::Pure {
                assert_eq!(differential(program, &shared, 1, true), (2, 1));
            } else {
                let merged = paths(program, &shared, 1, true);
                assert_eq!(merged.len(), 2, "每次生成新符号的配置闭包必须拒绝合并");
                assert!(merged.iter().all(|path| path.records.is_empty()));
            }
        }
    }
}

#[test]
fn region_merge_f2_union_initial_value_constraints() {
    for nested in [false, true] {
        for composite in [false, true] {
            for binding in ["register", "variable", "let"] {
                for merge in [false, true] {
                    let mut shared = empty_shared_state();
                    let union = shared.symtab.intern("zf2union");
                    let a = shared.symtab.intern("zf2A");
                    let b = shared.symtab.intern("zf2B");
                    let name = shared.symtab.intern("zf2initial");
                    shared.type_info.unions.insert(union, vec![(a, Ty::Unit), (b, Ty::Unit)]);
                    let pair = shared.symtab.intern("zf2pair");
                    let field = shared.symtab.intern("zf2field");
                    shared
                        .type_info
                        .structs
                        .insert(pair, std::collections::BTreeMap::from([(field, Ty::Union(union))]));
                    let ty = Box::leak(Box::new(if composite { Ty::Struct(pair) } else { Ty::Union(union) }));
                    let read = if composite { Exp::Field(Box::new(Exp::Id(name)), field) } else { Exp::Id(name) };
                    let mut program = vec![
                        Instr::Jump(input(0), 3, info()),
                        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                        Instr::Goto(4),
                        Instr::Copy(Loc::Id(RETURN), Exp::Kind(a, Box::new(read.clone())), info()),
                        Instr::Copy(
                            Loc::Id(RETURN),
                            Exp::Call(
                                Op::And,
                                vec![Exp::Kind(a, Box::new(read.clone())), Exp::Kind(b, Box::new(read.clone()))],
                            ),
                            info(),
                        ),
                        Instr::End,
                    ];
                    if nested {
                        // 在外层真臂内再次分支；仅内层真臂首次读取 union。
                        program = vec![
                            Instr::Jump(input(0), 3, info()),
                            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                            Instr::Goto(8),
                            Instr::Jump(input(1), 6, info()),
                            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                            Instr::Goto(7),
                            Instr::Copy(Loc::Id(RETURN), Exp::Kind(a, Box::new(read.clone())), info()),
                            Instr::Goto(8),
                            program[4].clone(),
                            Instr::End,
                        ];
                    }
                    let mut frame = make_frame(program);
                    match binding {
                        "register" => frame.regs_mut().insert(name, false, UVal::Uninit(ty)),
                        "variable" => {
                            frame.vars_mut().insert(name, UVal::Uninit(ty));
                        }
                        "let" => {
                            frame.lets_mut().insert(name, UVal::Uninit(ty));
                        }
                        _ => unreachable!(),
                    }
                    let context = Context::new(Config::new());
                    let mut solver = Solver::new(&context);
                    let g = solver.declare_const(smtlib::Ty::Bool, info());
                    let h = solver.declare_const(smtlib::Ty::Bool, info());
                    frame.vars_mut().insert(test_name(901), UVal::Init(Val::Symbolic(h)));
                    frame.vars_mut().insert(test_name(900), UVal::Init(Val::Symbolic(g)));
                    let state =
                        TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(merge));
                    let count = Mutex::new(0);
                    start_single(
                        frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
                        &shared,
                        &count,
                        &|_, _, result, _, mut solver, count| {
                            let Ok((Run::Finished(value), frame)) = result else {
                                panic!("union 用例必须完成");
                            };
                            assert!(
                                solver.check_sat_with(&smt_value(&value, info()).unwrap(), info()).is_unsat().unwrap(),
                                "{binding}, merge={merge}: union 初值不得既非 A 又非 B"
                            );
                            if merge {
                                assert!(!frame.region_merge_records().is_empty());
                            }
                            *count.lock().unwrap() += 1;
                        },
                    );
                    assert_eq!(
                        *count.lock().unwrap(),
                        if merge {
                            1
                        } else if nested {
                            3
                        } else {
                            2
                        }
                    );
                }
            }
        }
    }
}

#[test]
fn region_merge_f2_nested_pessimistic_assert_success_domain() {
    let mut shared = empty_shared_state();
    let function = helper(&mut shared);
    let arg = test_name(980);
    shared.functions.insert(
        function,
        (
            vec![(arg, &Ty::Bool)],
            &Ty::Bool,
            Box::leak(
                vec![
                    Instr::Jump(Exp::Id(arg), 3, info()),
                    Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                    Instr::Goto(4),
                    Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
                    Instr::End,
                ]
                .into_boxed_slice(),
            ),
        ),
    );
    let x = test_name(981);
    let unit = test_name(982);
    let program = vec![
        Instr::Decl(x, Ty::Bool, info()),
        Instr::Decl(unit, Ty::Unit, info()),
        Instr::Jump(input(0), 5, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
        Instr::Goto(8),
        Instr::Call(Loc::Id(x), false, function, vec![input(1)], info()),
        Instr::PrimopBinary(
            Loc::Id(unit),
            primop::binary_primops()["pessimistic_assert"],
            Exp::Id(x),
            Exp::String("f2".into()),
            info(),
        ),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
        Instr::End,
    ];
    assert_eq!(differential(program.clone(), &shared, 2, false), (2, 2));
    shared.function_regions.lock().unwrap().clear();
    let wrapper = shared.symtab.intern("zf2wrapper");
    shared.functions.insert(
        wrapper,
        (
            vec![(test_name(900), &Ty::Bool), (test_name(901), &Ty::Bool)],
            &Ty::Bool,
            Box::leak(program.into_boxed_slice()),
        ),
    );
    let resumed = vec![
        Instr::Call(Loc::Id(RETURN), false, wrapper, vec![input(0), input(1)], info()),
        Instr::Jump(input(2), 4, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(5),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
        Instr::End,
    ];
    assert_eq!(differential(resumed, &shared, 3, false), (4, 2), "回放离开函数出口区域后恢复合并");
}

#[test]
fn region_merge_f2_concrete_pessimistic_assert() {
    for value in [false, true] {
        let shared = empty_shared_state();
        let unit = test_name(982);
        let program = vec![
            Instr::Decl(unit, Ty::Unit, info()),
            Instr::Jump(input(0), 4, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::Goto(6),
            Instr::PrimopBinary(
                Loc::Id(unit),
                primop::binary_primops()["pessimistic_assert"],
                Exp::Bool(value),
                Exp::String("f2".into()),
                info(),
            ),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::End,
        ];
        let result = differential(program, &shared, 1, value);
        assert_eq!(result, (if value { 2 } else { 1 }, 1));
    }
}

#[test]
fn region_merge_f2_pow_before_region_inputs() {
    if std::env::var_os("ISLA_F2_INPUT_CHILD").is_none() {
        let path = std::env::temp_dir().join(format!("isla-f2-inputs-{}.jsonl", std::process::id()));
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "executor::tests::region_merge_tests::region_merge_f2_pow_before_region_inputs",
                "--nocapture",
            ])
            .env("ISLA_F2_INPUT_CHILD", "1")
            .env("ISLA_MERGE_RECORDS", &path)
            .output()
            .unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        std::fs::remove_file(path).unwrap();
        return;
    }
    let shared = empty_shared_state();
    let n = test_name(990);
    let x = test_name(991);
    let program = vec![
        Instr::Decl(n, Ty::I128, info()),
        Instr::Decl(x, Ty::I128, info()),
        Instr::PrimopUnary(Loc::Id(n), primop::unary_primops()["isla_bool_to_bit"], input(1), info()),
        Instr::PrimopBinary(Loc::Id(n), primop::binary_primops()["zero_extend"], Exp::Id(n), Exp::I128(128), info()),
        Instr::PrimopBinary(Loc::Id(x), primop::binary_primops()["pow_int"], Exp::Id(n), Exp::I128(2), info()),
        Instr::Jump(input(0), 8, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(x), Exp::I128(0)]), info()),
        Instr::Goto(9),
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(x), Exp::I128(1)]), info()),
        Instr::End,
    ];
    let merged = paths(program.clone(), &shared, 2, true);
    assert_eq!(merged.len(), 1);
    assert_eq!(
        merged[0].records[0].input_symbols,
        HashSet::from([Sym { id: 0 }, Sym { id: 1 }]),
        "区域前纯计算也必须展开到原始输入"
    );
    assert_eq!(differential(program, &shared, 2, true), (2, 1));
    let shared = empty_shared_state();
    let program = vec![
        Instr::Decl(n, Ty::I128, info()),
        Instr::Decl(x, Ty::I128, info()),
        Instr::PrimopBinary(Loc::Id(x), primop::binary_primops()["pow_int"], Exp::Id(n), Exp::I128(2), info()),
        Instr::Jump(input(0), 6, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(x), Exp::I128(0)]), info()),
        Instr::Goto(7),
        Instr::Copy(Loc::Id(RETURN), Exp::Call(Op::Eq, vec![Exp::Id(x), Exp::I128(1)]), info()),
        Instr::End,
    ];
    let merged = paths(program, &shared, 1, true);
    assert_eq!(merged.len(), 1);
    assert_eq!(merged[0].records[0].input_symbols, HashSet::from([Sym { id: 0 }, Sym { id: 1 }]));
}

fn f2_error(case: &str) -> ExecError {
    if case == "timeout" {
        return ExecError::Timeout;
    }
    if case == "assertion" {
        return ExecError::AssertionFailure(None, info());
    }
    struct Dump;
    impl crate::timeout::SmtDumpSource for Dump {
        fn materialize(&self) -> Result<String, String> {
            Ok("(check-sat)".into())
        }
    }
    ExecError::Smt(crate::error::SmtError::Timeout(Arc::new(crate::timeout::SmtTimeout {
        source_loc: info(),
        operation: crate::timeout::SmtOperation::CheckSat,
        limit: Duration::from_millis(1),
        operation_wall: Duration::from_millis(1),
        dump: Arc::new(crate::timeout::TimeoutSmtDump::new(Arc::new(Dump))),
    })))
}

#[test]
fn region_merge_f2_force_and_adaptive_errors() {
    if let Ok(case) = std::env::var("ISLA_F2_ERROR_CHILD") {
        let mut shared = empty_shared_state();
        let root = shared.symtab.intern("zf2errors");
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let error_case = case.clone();
        let program = vec![
            Instr::Jump(input(0), 3, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            Instr::Goto(4),
            Instr::PrimopReset(
                Loc::Id(RETURN),
                Arc::new(move |_, _, solver| {
                    if solver.transaction_depth() != 0 {
                        Err(f2_error(&error_case))
                    } else {
                        Ok(Val::Bool(true))
                    }
                }),
                primop::Effect::Pure,
                info(),
            ),
            Instr::End,
        ];
        let force = std::env::var_os("ISLA_F2_FORCE").is_some();
        let mut state = TaskState::new().with_execution_limits(policy_limits(
            &shared,
            vec![(root, if force { crate::config::MergeMode::Force } else { crate::config::MergeMode::Adaptive })],
        ));
        if case == "budget" {
            state = state.with_region_step_budget(0);
        }
        let context = Context::new(Config::new());
        let mut solver = Solver::new(&context);
        let condition = solver.declare_const(smtlib::Ty::Bool, info());
        let mut frame = make_frame(program);
        frame.function_name = root;
        frame.vars_mut().insert(test_name(900), UVal::Init(Val::Symbolic(condition)));
        let count = Mutex::new(0);
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            &shared,
            &count,
            &|_, _, result, _, solver, count| {
                assert!(!force, "Force 错误必须进程退出");
                let Ok((Run::Finished(_), frame)) = result else {
                    panic!("adaptive 错误必须普通分叉重跑");
                };
                assert_eq!(solver.transaction_depth(), 0);
                assert!(frame.region_merge_records().is_empty());
                *count.lock().unwrap() += 1;
            },
        );
        assert_eq!(*count.lock().unwrap(), 2);
        return;
    }
    for force in [true, false] {
        for case in ["timeout", "smt", "budget", "assertion"] {
            let mut command = std::process::Command::new(std::env::current_exe().unwrap());
            command
                .args([
                    "--exact",
                    "executor::tests::region_merge_tests::region_merge_f2_force_and_adaptive_errors",
                    "--nocapture",
                ])
                .env("ISLA_F2_ERROR_CHILD", case)
                .env("ISLA_STATS", "1")
                .env_remove("ISLA_F2_FORCE");
            if force {
                command.env("ISLA_F2_FORCE", "1");
            }
            let started = Instant::now();
            let output = command.output().unwrap();
            let stderr = String::from_utf8(output.stderr).unwrap();
            assert_eq!(output.status.code(), Some(if force { 86 } else { 0 }), "force={force}, case={case}: {stderr}");
            assert!(started.elapsed() < Duration::from_secs(10));
            if force {
                let diagnostic: serde_json::Value =
                    stderr.lines().find_map(|line| serde_json::from_str(line).ok()).unwrap();
                let reason = match case {
                    "timeout" => "timeout",
                    "smt" => "smt_error",
                    "assertion" => "symbolic_assertion",
                    _ => "step_budget",
                };
                assert_eq!(diagnostic["reason"], reason);
                assert!(stderr.contains("[MERGE_STATS]"));
                assert!(stderr.contains("[FORK_STATS]"));
                assert!(stderr.contains("[SPECULATION_REJECT_STATS]"));
            }
        }
    }
}

#[test]
fn region_merge_f2_records_disabled_skips_scan() {
    if std::env::var_os("ISLA_F2_NO_RECORDS_CHILD").is_some() {
        assert!(std::env::var_os("ISLA_MERGE_RECORDS").is_none());
        let shared = empty_shared_state();
        let program = vec![
            Instr::Jump(input(0), 3, info()),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::End,
        ];
        let state = TaskState::<B64>::new();
        assert!(state.execution_limits.is_none());
        let ignored = std::env::temp_dir().join(format!("isla-f2-ignored-{}.jsonl", std::process::id()));
        std::env::set_var("ISLA_MERGE_RECORDS", &ignored);
        let before = merge_record::DEPENDENCY_SCANS.load(Ordering::Relaxed);
        assert_eq!(paths(program, &shared, 1, true).len(), 1);
        assert_eq!(merge_record::DEPENDENCY_SCANS.load(Ordering::Relaxed), before, "关闭记录不得扫描迹");
        return;
    }
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "executor::tests::region_merge_tests::region_merge_f2_records_disabled_skips_scan",
            "--nocapture",
        ])
        .env("ISLA_F2_NO_RECORDS_CHILD", "1")
        .env_remove("ISLA_MERGE_RECORDS")
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
}

/// 人工注入内部不变量违反：不是某个现有原语的可达反例。
#[test]
#[should_panic(expected = "臂提交前保存点必须有效")]
fn region_merge_f2_invalid_savepoint_panics_before_arm_commit() {
    let shared = empty_shared_state();
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let g = solver.declare_const(smtlib::Ty::Bool, info());
    let old = solver.declare_const(smtlib::Ty::BitVec(64), info());
    let mut frame = make_frame(vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(4),
        Instr::PrimopReset(
            Loc::Id(RETURN),
            Arc::new(move |_, _, solver| {
                solver.mark_bitvector(old);
                Ok(Val::Bool(true))
            }),
            primop::Effect::Pure,
            info(),
        ),
        Instr::End,
    ]);
    frame.vars_mut().insert(test_name(900), UVal::Init(Val::Symbolic(g)));
    let result = merge_region_for_test(g, 3, &mut frame, &shared, &mut solver, info(), None, None);
    assert!(result.is_ok(), "不变量违反必须直接 panic");
}

// 完整旧集合为上限语义的独立参照；有上限时允许 DFS 改变发现顺序与代表值。
fn assert_merge_enumeration_reference(
    frame: &LocalFrame<B64>,
    solver: &mut Solver<B64>,
    state: &TaskState<B64>,
    shared: &SharedState<B64>,
    result: &Val<B64>,
    output: &serde_json::Value,
) {
    let mut limits = state.execution_limits.as_ref().unwrap().clone();
    limits.merge_enumeration.class_cap = usize::MAX;
    limits.merge_enumeration.path_cap = usize::MAX;
    let reference_state = TaskState::new().with_execution_limits(limits);
    let reference = frame.enumerate_merges_blocking(solver, &reference_state, shared, result).unwrap().unwrap();
    let classes = |value: &serde_json::Value| -> BTreeMap<String, HashSet<String>> {
        value["guard_classes"]
            .as_array()
            .unwrap()
            .iter()
            .map(|class| {
                (
                    class["guard_assignment"].to_string(),
                    class["solutions"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|solution| solution["slice_values"].to_string())
                        .collect(),
                )
            })
            .collect()
    };
    let expected = classes(&reference);
    let actual = classes(output);
    let mut total = 0;
    for class in output["guard_classes"].as_array().unwrap() {
        let key = class["guard_assignment"].to_string();
        let solutions = &actual[&key];
        assert_eq!(solutions.len(), class["solution_count"].as_u64().unwrap() as usize);
        assert!(solutions.is_subset(&expected[&key]));
        assert_eq!(class["truncated"], solutions.len() < expected[&key].len());
        total += solutions.len();
        // 每个叶子回投完整类条件及位片段，验证原路径而非只有计数。
        for solution in class["solutions"].as_array().unwrap() {
            use smtlib::Exp::*;
            let mut condition = Bool(true);
            let by_id: HashMap<_, _> = frame.region_merge_records.iter().map(|r| (r.record_id, r)).collect();
            for record in &frame.region_merge_records {
                let mut context = Bool(true);
                let mut current = record;
                while let Some(parent) = current.parent_record {
                    let parent = by_id[&parent];
                    let guard = Var(parent.condition);
                    context = And(
                        Box::new(context),
                        Box::new(if current.arm == "then" { guard } else { Not(Box::new(guard)) }),
                    );
                    current = parent;
                }
                let projection = And(Box::new(context), Box::new(Var(record.condition)));
                let value = class["guard_assignment"][record.record_id.to_string()].as_bool().unwrap();
                condition =
                    And(Box::new(condition), Box::new(if value { projection } else { Not(Box::new(projection)) }));
            }
            for (slice, value) in
                class["tested_slices"].as_array().unwrap().iter().zip(solution["slice_values"].as_array().unwrap())
            {
                let expression = Extract(
                    slice["hi"].as_u64().unwrap() as u32,
                    slice["lo"].as_u64().unwrap() as u32,
                    Box::new(Var(Sym::from_u32(slice["smt_id"].as_u64().unwrap() as u32))),
                );
                condition = And(
                    Box::new(condition),
                    Box::new(Eq(
                        Box::new(expression),
                        Box::new(smtlib::smt_bits_from_str(value.as_str().unwrap()).unwrap()),
                    )),
                );
            }
            assert!(solver.check_sat_with(&condition, info()).is_sat().unwrap());
        }
    }
    assert_eq!(output["enumerated_total"], total);
    let config = &state.execution_limits.as_ref().unwrap().merge_enumeration;
    let remaining = actual.len() < expected.len()
        || output["guard_classes"].as_array().unwrap().iter().any(|c| c["truncated"] == true);
    assert_eq!(output["path_truncated"], total == config.path_cap && remaining);
    if !remaining {
        assert_eq!(actual, expected);
    }
}

// E1：上下文投影必须折叠外层不成立时的无关内层条件。
#[test]
fn merge_enumeration_nested_context_and_fork_inheritance() {
    let shared = empty_shared_state();
    let body = vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(7),
        Instr::Jump(input(1), 6, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(7),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
        Instr::End,
    ];
    let baseline = paths(body.clone(), &shared, 2, false);
    assert_eq!(baseline.len(), 3);
    let merged = paths(body, &shared, 2, true);
    assert_eq!(merged.len(), 1);
    let path = &merged[0];
    assert_eq!(path.records.len(), 2);
    let child = path.records.iter().find(|r| r.parent_record.is_some()).unwrap();
    let parent = path.records.iter().find(|r| r.parent_record.is_none()).unwrap();
    assert_eq!(child.parent_record, Some(parent.record_id));
    assert_eq!(child.arm, "then");
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    for event in &path.events {
        solver.add_event(event.clone());
    }
    let mut frame = make_frame(vec![Instr::End]);
    frame.region_merge_records = path.records.clone();
    let mut restored = make_frame(vec![Instr::End]);
    restored.restore_merge_history(frame.merge_history());
    assert_eq!(restored.region_merge_records().len(), 2);
    let frozen = freeze_frame(&frame);
    let first = unfreeze_frame(&frozen);
    let mut second = unfreeze_frame(&frozen);
    second.region_merge_records.clear();
    assert_eq!(first.region_merge_records().len(), 2);
    let mut limits = ExecutionLimits::default();
    limits.merge_enumeration.enabled = true;
    let state = TaskState::new().with_execution_limits(limits);
    let before = solver.trace().to_vec().len();
    let output = first.enumerate_merges(&mut solver, &state, &shared, &path.value).unwrap().unwrap();
    assert_merge_enumeration_reference(&first, &mut solver, &state, &shared, &path.value, &output);
    assert_eq!(output["guard_classes"].as_array().unwrap().len(), baseline.len());
    assert_eq!(output["enumerated_total"], 3);
    assert_eq!(output["path_truncated"], false);
    assert_eq!(before, solver.trace().to_vec().len(), "枚举不得污染路径求解器");
    // 在已完成的合并历史之后真正 fork：两条任务都继承历史，但各自使用自己的约束。
    let mut fork = make_frame(vec![
        Instr::Jump(input(0), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(4),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
        Instr::End,
    ]);
    fork.restore_merge_history(first.merge_history());
    fork.vars_mut().insert(test_name(900), UVal::Init(Val::Symbolic(Sym { id: 0 })));
    let output = Mutex::new(Vec::new());
    start_single(
        fork.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
        &shared,
        &output,
        &|_, _, result, shared, mut solver, output| {
            let Ok((Run::Finished(value), frame)) = result else {
                panic!("普通分叉必须完成");
            };
            assert_eq!(frame.region_merge_records().len(), 2);
            let enumeration = frame.enumerate_merges(&mut solver, &state, shared, &value).unwrap().unwrap();
            output.lock().unwrap().push(enumeration["enumerated_total"].as_u64().unwrap());
        },
    );
    let mut counts = output.into_inner().unwrap();
    counts.sort();
    assert_eq!(counts, [1, 2]);
}

#[test]
fn merge_enumeration_coupled_slices_caps_and_failure_result() {
    use smtlib::Exp::*;
    let mut shared = empty_shared_state();
    let fault = shared.symtab.intern("zPageFault");
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let bits = solver.declare_bitvector(4, info());
    let r = solver.define_const(Extract(0, 0, Box::new(Var(bits))), info());
    let w = solver.define_const(Extract(1, 1, Box::new(Var(bits))), info());
    let condition = solver.define_const(
        And(
            Box::new(Eq(Box::new(Var(w)), Box::new(smtlib::bits64(1, 1)))),
            Box::new(Eq(Box::new(Var(r)), Box::new(smtlib::bits64(0, 1)))),
        ),
        info(),
    );
    // W && !R 不成立，字段独立乘积会错误包含 (R=0,W=1)。
    solver.add(Def::Assert(Not(Box::new(Var(condition)))));
    let mut frame = make_frame(vec![Instr::End]);
    frame.region_merge_records.push(RegionMergeRecord {
        record_id: 0,
        parent_record: None,
        arm: "root",
        function: TOP_LEVEL_LET,
        branch_pc: 0,
        join: crate::ir::regions::RegionPoint::FunctionExit,
        condition,
        source_loc: info(),
        depth: 1,
        dead: false,
        value_symbols: HashSet::new(),
        input_symbols: HashSet::new(),
        single_arm_reads: vec![],
        memory_reads: Vec::new(),
    });
    let mut rollback_limits = ExecutionLimits::default();
    rollback_limits.merge_enumeration.enabled = true;
    let rollback_state = TaskState::new().with_execution_limits(rollback_limits);
    let before = solver.trace().to_vec().len();
    let error = frame.enumerate_merges_with(&mut solver, &rollback_state, &shared, &Val::Unit, &mut |_, _, _| {
        Err(ExecError::Z3Unknown)
    });
    assert!(matches!(error, Err(ExecError::Z3Unknown)));
    assert_eq!(solver.transaction_depth(), 0);
    assert_eq!(solver.trace().to_vec().len(), before);
    for (class_cap, path_cap, count, truncated) in
        [(10, 10, 3, false), (2, 10, 2, true), (10, 1, 1, true), (3, 3, 3, false)]
    {
        let mut limits = ExecutionLimits::default();
        limits.merge_enumeration = crate::config::MergeEnumerationConfig { enabled: true, class_cap, path_cap };
        let state = TaskState::new().with_execution_limits(limits);
        // 正常处理器失败结果仍必须枚举，不按返回构造子筛掉。
        let failure = Val::Ctor(fault, Box::new(Val::Symbolic(bits)));
        let output = frame.enumerate_merges(&mut solver, &state, &shared, &failure).unwrap().unwrap();
        assert_merge_enumeration_reference(&frame, &mut solver, &state, &shared, &failure, &output);
        assert_eq!(output["enumerated_total"], count);
        assert_eq!(output["guard_classes"][0]["truncated"], truncated);
        assert_eq!(output["path_truncated"], path_cap == 1);
        let class = &output["guard_classes"][0];
        assert_eq!(class["tested_slices"].as_array().unwrap().len(), 2, "未被测试的高两位不参与展开");
        let mut found = HashSet::new();
        for solution in class["solutions"].as_array().unwrap() {
            let values = solution["slice_values"].as_array().unwrap();
            let mut conjunction = Bool(true);
            let mut pair = 0;
            for (slice, value) in class["tested_slices"].as_array().unwrap().iter().zip(values) {
                let lo = slice["lo"].as_u64().unwrap() as u32;
                let bit = match value.as_str().unwrap() {
                    "#b0" => 0,
                    "#b1" => 1,
                    value => panic!("非法位值 {value}"),
                };
                pair |= bit << lo;
                conjunction = And(
                    Box::new(conjunction),
                    Box::new(Eq(Box::new(Extract(lo, lo, Box::new(Var(bits)))), Box::new(smtlib::bits64(bit, 1)))),
                );
            }
            assert!(solver.check_sat_with(&conjunction, info()).is_sat().unwrap(), "每个解必须满足真实路径条件");
            assert!(found.insert(pair), "不得重复枚举同一组合");
        }
        if !truncated {
            let brute_force: HashSet<u64> = (0..4).filter(|value| !(value & 2 != 0 && value & 1 == 0)).collect();
            let r_values: HashSet<_> = brute_force.iter().map(|value| value & 1).collect();
            let w_values: HashSet<_> = brute_force.iter().map(|value| (value >> 1) & 1).collect();
            let independent: HashSet<_> =
                r_values.iter().flat_map(|r| w_values.iter().map(move |w| r | (w << 1))).collect();
            assert_eq!(independent.len(), 4);
            assert_ne!(brute_force, independent, "字段独立乘积会引入非法组合");
            assert_eq!(found, brute_force);
        }
    }
    let child =
        solver.define_const(Eq(Box::new(Extract(2, 2, Box::new(Var(bits)))), Box::new(smtlib::bits64(0, 1))), info());
    let mut record = frame.region_merge_records[0].clone();
    record.record_id = 1;
    record.parent_record = Some(0);
    record.arm = "then";
    record.condition = child;
    frame.region_merge_records.push(record);
    let mut limits = ExecutionLimits::default();
    limits.merge_enumeration.enabled = true;
    let state = TaskState::new().with_execution_limits(limits);
    let output = frame.enumerate_merges(&mut solver, &state, &shared, &Val::Unit).unwrap().unwrap();
    assert_eq!(output["guard_classes"].as_array().unwrap().len(), 1, "内层上下文不成立不得多算叶子");
    assert_eq!(output["enumerated_total"], 6, "二级仍应展开所有守卫测试过的三位可行组合");
    assert!(frame.enumerate_merges(&mut solver, &TaskState::new(), &shared, &Val::Unit).unwrap().is_none());
}

#[test]
fn merge_enumeration_extract_of_derived_symbol() {
    use smtlib::Exp::*;
    let shared = empty_shared_state();
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let input = solver.declare_bitvector(8, info());
    let derived = solver.define_const(Bvxor(Box::new(Var(input)), Box::new(smtlib::bits64(64, 8))), info());
    let slice = solver.define_const(Extract(1, 0, Box::new(Var(derived))), info());
    let guard = solver.define_const(Eq(Box::new(Var(slice)), Box::new(smtlib::bits64(0, 2))), info());
    let mut frame = make_frame(vec![Instr::End]);
    frame.region_merge_records.push(RegionMergeRecord {
        record_id: 0,
        parent_record: None,
        arm: "root",
        function: TOP_LEVEL_LET,
        branch_pc: 0,
        join: crate::ir::regions::RegionPoint::FunctionExit,
        condition: guard,
        source_loc: info(),
        depth: 1,
        dead: false,
        value_symbols: HashSet::new(),
        input_symbols: HashSet::new(),
        single_arm_reads: vec![],
        memory_reads: Vec::new(),
    });
    let mut limits = ExecutionLimits::default();
    limits.merge_enumeration.enabled = true;
    let state = TaskState::new().with_execution_limits(limits);
    let output = frame.enumerate_merges(&mut solver, &state, &shared, &Val::Symbolic(derived)).unwrap().unwrap();
    assert_merge_enumeration_reference(&frame, &mut solver, &state, &shared, &Val::Symbolic(derived), &output);
    assert_eq!(output["guard_classes"][0]["guard_assignment"]["0"], false, "DFS 固定先访问假分支");
    assert_eq!(output["enumerated_total"], 4, "必须阻断派生表达式的真实两位取值");
    let mut limits = ExecutionLimits::default();
    limits.merge_enumeration.enabled = true;
    limits.merge_enumeration.class_cap = 2;
    let limited = TaskState::new().with_execution_limits(limits);
    let output = frame.enumerate_merges(&mut solver, &limited, &shared, &Val::Unit).unwrap().unwrap();
    assert_eq!(output["enumerated_total"], 3);
    assert_eq!(output["guard_classes"].as_array().unwrap().len(), 2, "类上限不应阻止其他类枚举");
    assert!(output["guard_classes"].as_array().unwrap().iter().any(|class| class["truncated"] == true));
    assert_eq!(output["path_truncated"], false);
    let nested = solver.define_const(Extract(0, 0, Box::new(Extract(5, 2, Box::new(Var(input))))), info());
    let guard = solver.define_const(Eq(Box::new(Var(nested)), Box::new(smtlib::bits64(0, 1))), info());
    frame.region_merge_records[0].condition = guard;
    let output = frame.enumerate_merges(&mut solver, &state, &shared, &Val::Unit).unwrap().unwrap();
    assert_eq!(output["enumerated_total"], 2, "连续 Extract 只能枚举真正被测试的一位");
}

#[test]
fn merge_enumeration_f5_深守卫与记录倒序不依赖保存点栈深度() {
    use smtlib::Exp::*;
    let shared = empty_shared_state();
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let guard = solver.declare_const(smtlib::Ty::Bool, info());
    let mut frame = make_frame(vec![Instr::End]);
    for id in (0..70).rev() {
        frame.region_merge_records.push(RegionMergeRecord {
            record_id: id,
            parent_record: if id == 0 { None } else { Some(id - 1) },
            arm: if id == 0 { "root" } else { "then" },
            function: TOP_LEVEL_LET,
            branch_pc: 0,
            join: crate::ir::regions::RegionPoint::FunctionExit,
            condition: guard,
            source_loc: info(),
            depth: id + 1,
            dead: false,
            value_symbols: HashSet::new(),
            input_symbols: HashSet::new(),
            single_arm_reads: vec![],
            memory_reads: vec![],
        });
    }
    let mut limits = ExecutionLimits::default();
    limits.merge_enumeration = crate::config::MergeEnumerationConfig { enabled: true, class_cap: 1, path_cap: 2 };
    let state = TaskState::new().with_execution_limits(limits);
    let before = solver.trace().to_vec().len();
    let output = frame.enumerate_merges(&mut solver, &state, &shared, &Val::Unit).unwrap().unwrap();
    assert_merge_enumeration_reference(&frame, &mut solver, &state, &shared, &Val::Unit, &output);
    assert_eq!(output["enumerated_total"], 2);
    assert_eq!(output["path_truncated"], false);
    assert_eq!(solver.trace().to_vec().len(), before);
    frame.region_merge_records.clear();
    let empty = frame.enumerate_merges(&mut solver, &state, &shared, &Val::Unit).unwrap().unwrap();
    assert_eq!(empty["enumerated_total"], 1);
    solver.assert(Bool(false));
    let unsat = frame.enumerate_merges(&mut solver, &state, &shared, &Val::Unit).unwrap().unwrap();
    assert_eq!(unsat["enumerated_total"], 0);
}

#[test]
#[ignore = "F5 万类压力验证，显式运行"]
fn merge_enumeration_f5_单路径16384类且每类只消费一次模型() {
    let shared = empty_shared_state();
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let mut frame = make_frame(vec![Instr::End]);
    for id in 0..14 {
        let condition = solver.declare_const(smtlib::Ty::Bool, info());
        frame.region_merge_records.push(RegionMergeRecord {
            record_id: id,
            parent_record: None,
            arm: "root",
            function: TOP_LEVEL_LET,
            branch_pc: 0,
            join: crate::ir::regions::RegionPoint::FunctionExit,
            condition,
            source_loc: info(),
            depth: 1,
            dead: false,
            value_symbols: HashSet::new(),
            input_symbols: HashSet::new(),
            single_arm_reads: vec![],
            memory_reads: vec![],
        });
    }
    let mut limits = ExecutionLimits::default();
    limits.merge_enumeration = crate::config::MergeEnumerationConfig { enabled: true, class_cap: 1, path_cap: 16384 };
    let state = TaskState::new().with_execution_limits(limits);
    let before = solver.trace().to_vec().len();
    let mut calls = 0;
    let output = frame
        .enumerate_merges_with(&mut solver, &state, &shared, &Val::Unit, &mut |_, index, _| {
            assert_eq!(index, 0);
            calls += 1;
            Ok(())
        })
        .unwrap()
        .unwrap();
    assert_eq!(calls, 16384);
    assert_eq!(output["enumerated_total"], 16384);
    assert_eq!(output["path_truncated"], false);
    let classes = output["guard_classes"].as_array().unwrap();
    let assignments: HashSet<_> = classes.iter().map(|class| class["guard_assignment"].to_string()).collect();
    assert_eq!(assignments.len(), 16384);
    assert!(classes.iter().all(|class| class["truncated"] == false));
    assert_eq!(solver.transaction_depth(), 0);
    assert_eq!(solver.trace().to_vec().len(), before);
}

/// 与 I2–I5 共用真实 IR、架构初始化及固定原语配置；显式运行以避免依赖外部文件。
#[test]
#[ignore = "需要 ISLA_REGIONS_IR 指向真实 rv64d.ir"]
fn merge_enumeration_real_ir_pte_is_invalid() {
    let text = std::fs::read_to_string(std::env::var("ISLA_REGIONS_IR").unwrap()).unwrap();
    let mut symtab = Symtab::new();
    let mut definitions =
        crate::ir_parser::IrParser::new().parse(&mut symtab, crate::ir_lexer::new_ir_lexer(&text)).unwrap();
    let types = IRTypeInfo::new(&definitions);
    let config_text = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../agents/path_merge_call_support/baseline_config_const.toml"
    ))
    .unwrap();
    let config = ISAConfig::<B64>::parse(&config_text, None, &symtab, &types).unwrap();
    let initialized = crate::init::initialize_architecture(
        &mut definitions,
        symtab,
        types,
        &config,
        AssertionMode::Pessimistic,
        true,
    );
    let shared = &initialized.shared_state;
    let function = shared.symtab.lookup("zpte_is_invalid");
    let (args, ret_ty, body) = &shared.functions[&function];
    let mut counts = Vec::new();
    for (merge, class_cap, path_cap) in
        [(false, 1024, 65536), (true, 1024, 65536), (true, usize::MAX, usize::MAX), (true, 2, 5)]
    {
        let mut limits = ExecutionLimits::default().with_path_merging(merge);
        limits.merge_enumeration = crate::config::MergeEnumerationConfig { enabled: merge, class_cap, path_cap };
        let state = TaskState::new().with_execution_limits(limits);
        let mut frame = LocalFrame::new(function, args, ret_ty, None, body);
        frame.add_regs(&initialized.regs).add_lets(&initialized.lets);
        let context = Context::new(Config::new());
        let mut solver = Solver::new(&context);
        reset_registers(0, &mut frame, &state, shared, &mut solver, info()).unwrap();
        let collected = Mutex::new(Vec::new());
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            shared,
            &collected,
            &|_, _, result, shared, mut solver, collected| {
                let Ok((Run::Finished(value), frame)) = result else {
                    panic!("真实函数必须正常完成");
                };
                let enumeration = frame.enumerate_merges(&mut solver, &state, shared, &value).unwrap();
                if let Some(output) = &enumeration {
                    assert_merge_enumeration_reference(&frame, &mut solver, &state, shared, &value, output);
                    // 在原路径求解器上逐个回投该解的所有片段，不能只验证计数。
                    for class in output["guard_classes"].as_array().unwrap() {
                        for solution in class["solutions"].as_array().unwrap() {
                            use smtlib::Exp::*;
                            let mut condition = Bool(true);
                            for (slice, value) in class["tested_slices"]
                                .as_array()
                                .unwrap()
                                .iter()
                                .zip(solution["slice_values"].as_array().unwrap())
                            {
                                let exp = Extract(
                                    slice["hi"].as_u64().unwrap() as u32,
                                    slice["lo"].as_u64().unwrap() as u32,
                                    Box::new(Var(Sym { id: slice["smt_id"].as_u64().unwrap() as u32 })),
                                );
                                condition = And(
                                    Box::new(condition),
                                    Box::new(Eq(
                                        Box::new(exp),
                                        Box::new(smtlib::smt_bits_from_str(value.as_str().unwrap()).unwrap()),
                                    )),
                                );
                            }
                            assert!(solver.check_sat_with(&condition, info()).is_sat().unwrap());
                        }
                    }
                    eprintln!(
                        "pte_is_invalid class_cap={class_cap} path_cap={path_cap} 叶子={} 解={} 截断={}",
                        output["guard_classes"].as_array().unwrap().len(),
                        output["enumerated_total"],
                        output["path_truncated"]
                    );
                    if let Some(directory) = std::env::var_os("ISLA_ENUMERATION_TEST_OUTPUT") {
                        let directory = std::path::PathBuf::from(directory);
                        std::fs::create_dir_all(&directory).unwrap();
                        std::fs::write(
                            directory.join(format!("pte-{class_cap}-{path_cap}.json")),
                            serde_json::to_vec_pretty(output).unwrap(),
                        )
                        .unwrap();
                    }
                    if class_cap > 2 {
                        assert_eq!(output["guard_classes"].as_array().unwrap().len(), 10);
                        assert_eq!(output["enumerated_total"], 256);
                        assert_eq!(output["path_truncated"], false);
                        assert!(output["guard_classes"]
                            .as_array()
                            .unwrap()
                            .iter()
                            .all(|class| class["truncated"] == false));
                    } else {
                        assert_eq!(output["path_truncated"], true);
                        assert_eq!(output["enumerated_total"], 5);
                    }
                }
                collected.lock().unwrap().push(enumeration);
            },
        );
        counts.push(collected.into_inner().unwrap().len());
    }
    assert_eq!(counts, [10, 1, 1, 1]);
}

/// 直接在真实执行器的收尾求解器上导出与检查，合成 IR 和真实 PTE 共用。
fn sample_run<'ir>(
    frame: LocalFrame<'ir, B64>,
    shared: &SharedState<'ir, B64>,
    pre: BTreeMap<String, Val<B64>>,
    mut solver: Solver<B64>,
    merge: bool,
    samples: &[crate::executor::samples::Sample],
) -> (Vec<crate::executor::samples::Sample>, serde_json::Value) {
    use crate::executor::samples::{SampleChecker, SamplePath};
    let mut limits = ExecutionLimits::default().with_path_merging(merge);
    limits.merge_enumeration.enabled = merge;
    limits.merge_enumeration.path_cap = 10;
    let state = std::sync::Arc::new(TaskState::new().with_execution_limits(limits));
    let collector_state = state.clone();
    let checker = std::sync::Arc::new(SampleChecker::new(samples.to_vec()));
    let collector_checker = checker.clone();
    let output = Mutex::new(Vec::new());
    let cp = checkpoint(&mut solver);
    start_single(
        frame.task_with_checkpoint(TaskId::fresh(), &state, cp),
        shared,
        &output,
        &move |_, _, result, shared, mut solver, output| {
            let Ok((Run::Finished(value), frame)) = result else {
                panic!("样本测试必须完成");
            };
            let path = SamplePath {
                pre: pre.clone(),
                post: BTreeMap::new(),
                result: value.clone(),
                memory: Vec::new(),
                memory_guards: BTreeMap::new(),
            };
            collector_checker.check_path(&path, &mut solver, shared, frame.path_signature()).unwrap();
            let mut generated = Vec::new();
            let enumeration = frame
                .enumerate_merges_with(&mut solver, &collector_state, shared, &value, &mut |class, _, model| {
                    generated.push(path.materialize(model, shared, "merge", frame.path_signature(), Some(class))?);
                    Ok(())
                })
                .unwrap();
            if enumeration.is_none() {
                assert_eq!(solver.check_sat(info()), SmtResult::Sat);
                generated.push(
                    path.materialize(&mut Model::new(&mut solver), shared, "fork", frame.path_signature(), None)
                        .unwrap(),
                );
            }
            let mut output = output.lock().unwrap();
            for mut sample in generated {
                sample.sample_id = output.len() as u64;
                output.push(sample);
            }
        },
    );
    (output.into_inner().unwrap(), checker.report())
}

#[test]
fn samples_two_arm_nested_cross_mode_and_roundtrip() {
    for nested in [false, true] {
        let shared = empty_shared_state();
        let program = if nested {
            vec![
                Instr::Jump(input(0), 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                Instr::Goto(7),
                Instr::Jump(input(1), 6, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                Instr::Goto(7),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
                Instr::End,
            ]
        } else {
            vec![
                Instr::Jump(input(0), 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                Instr::Goto(4),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
                Instr::End,
            ]
        };
        let run = |merge, samples: &[_]| {
            let context = Context::new(Config::new());
            let mut solver = Solver::new(&context);
            let mut frame = make_frame(program.clone());
            frame.function_name = TOP_LEVEL_LET;
            let mut pre = BTreeMap::new();
            for index in 0..3 {
                let value = Val::Symbolic(solver.declare_const(smtlib::Ty::Bool, info()));
                frame.vars_mut().insert(test_name(900 + index), UVal::Init(value.clone()));
                if index == 2 {
                    solver.assert(smt_value(&value, info()).unwrap());
                }
                pre.insert(format!("x{index}"), value);
            }
            sample_run(frame, &shared, pre, solver, merge, samples)
        };
        for source in [false, true] {
            let (samples, _) = run(source, &[]);
            assert_eq!(samples.len(), if nested { 3 } else { 2 });
            // 真实 JSON 往返也必须保留复合类型及样本身份。
            let samples = serde_json::from_str::<Vec<crate::executor::samples::Sample>>(
                &serde_json::to_string(&samples).unwrap(),
            )
            .unwrap();
            let mut outside = samples[0].clone();
            outside.sample_id = 100;
            outside.pre_registers.insert("x2".into(), serde_json::json!({"bool":false}));
            let mut wrong = samples[0].clone();
            wrong.sample_id = 101;
            wrong.result = serde_json::json!({"bool":!wrong.result["bool"].as_bool().unwrap()});
            for target in [false, true] {
                let (_, negative) = run(target, &[outside.clone(), wrong.clone()]);
                assert_eq!(negative["unaccepted_sample_ids"], serde_json::json!([100]));
                assert_eq!(negative["samples"][1]["consistent_paths"], 0);
                assert!(negative["samples"][1]["inconsistent_paths"].as_u64().unwrap() > 0);
                let (_, report) = run(target, &samples);
                assert!(report["unaccepted_sample_ids"].as_array().unwrap().is_empty());
                assert!(report["inconsistent"].as_array().unwrap().is_empty());
                assert!(report["samples"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|s| s["consistent_paths"].as_u64().unwrap() > 0));
            }
        }
    }
}

#[test]
#[ignore = "需要 ISLA_REGIONS_IR 指向真实 Sail IR"]
fn samples_real_ir_pte_cross_mode() {
    let text = std::fs::read_to_string(std::env::var("ISLA_REGIONS_IR").unwrap()).unwrap();
    let mut symtab = Symtab::new();
    let mut definitions =
        crate::ir_parser::IrParser::new().parse(&mut symtab, crate::ir_lexer::new_ir_lexer(&text)).unwrap();
    let types = IRTypeInfo::new(&definitions);
    let config = ISAConfig::<B64>::parse(
        &std::fs::read_to_string(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../agents/path_merge_call_support/baseline_config_const.toml"
        ))
        .unwrap(),
        None,
        &symtab,
        &types,
    )
    .unwrap();
    let initialized = crate::init::initialize_architecture(
        &mut definitions,
        symtab,
        types,
        &config,
        AssertionMode::Pessimistic,
        true,
    );
    let shared = &initialized.shared_state;
    let function = shared.symtab.lookup("zpte_is_invalid");
    let (args, ret_ty, body) = &shared.functions[&function];
    let run = |merge, samples: &[_]| {
        let context = Context::new(Config::new());
        let mut solver = Solver::new(&context);
        let mut frame = LocalFrame::new(function, args, ret_ty, None, body);
        frame.add_regs(&initialized.regs).add_lets(&initialized.lets);
        reset_registers(0, &mut frame, &TaskState::new(), shared, &mut solver, info()).unwrap();
        let mut pre = BTreeMap::new();
        for (name, ty) in args {
            let value = symbolic(ty, shared, &mut solver, info()).unwrap();
            frame.vars_mut().insert(*name, UVal::Init(value.clone()));
            pre.insert(zencode::decode(shared.symtab.to_str(*name)), value);
        }
        sample_run(frame, shared, pre, solver, merge, samples)
    };
    for source in [false, true] {
        let (samples, _) = run(source, &[]);
        assert_eq!(samples.len(), 10);
        let (_, report) = run(!source, &samples);
        assert!(report["unaccepted_sample_ids"].as_array().unwrap().is_empty(), "{report}");
        assert!(report["inconsistent"].as_array().unwrap().is_empty(), "{report}");
        eprintln!("pte 样本方向 merge={source} → merge={}：{report}", !source);
        if let Ok(directory) = std::env::var("ISLA_SAMPLES_TEST_OUTPUT") {
            std::fs::create_dir_all(&directory).unwrap();
            std::fs::write(
                format!("{directory}/pte-source-{source}.json"),
                serde_json::to_string_pretty(&samples).unwrap(),
            )
            .unwrap();
            std::fs::write(
                format!("{directory}/pte-report-{source}.json"),
                serde_json::to_string_pretty(&report).unwrap(),
            )
            .unwrap();
        }
    }
}

#[test]
fn region_merge_f4_union_match_and_nested_tags() {
    let mut shared = empty_shared_state();
    let definitions = crate::ir_parser::IrParser::new()
        .parse(
            &mut shared.symtab,
            crate::ir_lexer::new_ir_lexer("union zF4Result { zNone: %unit, zSome: %bool, zFailure: %bv8 }"),
        )
        .unwrap();
    shared.type_info = IRTypeInfo::new::<B64>(&definitions);
    let union = shared.symtab.lookup("zF4Result");
    let none = shared.symtab.lookup("zNone");
    let some = shared.symtab.lookup("zSome");
    let failure = shared.symtab.lookup("zFailure");
    let value = shared.symtab.intern("zf4value");
    // 内层 None/Some 先合并，外层再与不同载荷类型的 Failure 合并。
    let program = vec![
        Instr::Decl(value, Ty::Union(union), info()),
        Instr::Jump(input(0), 8, info()),
        Instr::Jump(input(1), 5, info()),
        Instr::Call(Loc::Id(value), false, none, vec![Exp::Unit], info()),
        Instr::Goto(6),
        Instr::Call(Loc::Id(value), false, some, vec![input(2)], info()),
        Instr::Goto(9),
        Instr::Goto(9),
        Instr::Call(Loc::Id(value), false, failure, vec![Exp::Bits(B64::new(7, 8))], info()),
        Instr::Jump(Exp::Kind(some, Box::new(Exp::Id(value))), 12, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Unwrap(some, Box::new(Exp::Id(value))), info()),
        Instr::Goto(16),
        Instr::Jump(Exp::Kind(failure, Box::new(Exp::Id(value))), 15, info()),
        Instr::Copy(
            Loc::Id(RETURN),
            Exp::Call(Op::Eq, vec![Exp::Unwrap(failure, Box::new(Exp::Id(value))), Exp::Bits(B64::new(7, 8))]),
            info(),
        ),
        Instr::Goto(16),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::End,
    ];
    assert_eq!(differential(program, &shared, 3, true), (3, 1));
}

#[test]
fn region_merge_f4_union_success_domain_unwrap() {
    let mut shared = empty_shared_state();
    let definitions = crate::ir_parser::IrParser::new()
        .parse(&mut shared.symtab, crate::ir_lexer::new_ir_lexer("union zF4Check { zSuccess: %bool, zFailure: %unit }"))
        .unwrap();
    shared.type_info = IRTypeInfo::new::<B64>(&definitions);
    let value = shared.symtab.intern("zf4check");
    let success = shared.symtab.lookup("zSuccess");
    let failure = shared.symtab.lookup("zFailure");
    // assume 将失败域剪去，再直接解包；差分判据检查成功域以及返回关系。
    let program = vec![
        Instr::Decl(value, Ty::Union(shared.symtab.lookup("zF4Check")), info()),
        Instr::Jump(input(0), 4, info()),
        Instr::Call(Loc::Id(value), false, failure, vec![Exp::Unit], info()),
        Instr::Goto(5),
        Instr::Call(Loc::Id(value), false, success, vec![input(1)], info()),
        Instr::PrimopUnary(
            Loc::Id(RETURN),
            primop::unary_primops()["assume"],
            Exp::Call(Op::Not, vec![Exp::Kind(success, Box::new(Exp::Id(value)))]),
            info(),
        ),
        Instr::Copy(Loc::Id(RETURN), Exp::Unwrap(success, Box::new(Exp::Id(value))), info()),
        Instr::End,
    ];
    assert_eq!(differential(program, &shared, 2, false), (1, 1));
}

#[test]
fn region_merge_f4_unreachable_unknown_extern() {
    let mut shared = empty_shared_state();
    let unknown = shared.symtab.intern("zf4unknown");
    let helper = helper(&mut shared);
    let argument = shared.functions[&helper].0[0].0;
    shared.functions.get_mut(&helper).unwrap().2 = Box::leak(
        vec![
            Instr::Jump(Exp::Id(argument), 3, info()),
            Instr::Call(Loc::Id(RETURN), false, unknown, vec![], info()),
            Instr::Goto(4),
            Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
            Instr::End,
        ]
        .into_boxed_slice(),
    );
    assert_eq!(
        differential(
            vec![
                Instr::Jump(input(0), 3, info()),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                Instr::Goto(4),
                Instr::Call(Loc::Id(RETURN), false, helper, vec![input(0)], info()),
                Instr::End,
            ],
            &shared,
            1,
            true
        ),
        (2, 1)
    );
    // 普通执行的未知入口确实报 NoFunction；推演执行改为可回滚拒绝。
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let mut frame = make_frame(vec![Instr::End]);
    let state = TaskState::new();
    assert!(matches!(
        run_special_primop(
            &Loc::Id(RETURN),
            unknown,
            &[],
            info(),
            0,
            TaskId::fresh(),
            &mut frame,
            &state,
            &shared,
            &mut solver
        ),
        Err(ExecError::NoFunction(..))
    ));
    frame.speculation_mode = SpeculationMode::On;
    assert!(matches!(
        run_special_primop(
            &Loc::Id(RETURN),
            unknown,
            &[],
            info(),
            0,
            TaskId::fresh(),
            &mut frame,
            &state,
            &shared,
            &mut solver
        ),
        Err(ExecError::SpeculativeReject { reason: SpeculativeRejectReason::UnknownExtern, .. })
    ));
}

#[test]
fn region_merge_f4_memory_read_union() {
    use crate::memory::Memory;
    for concrete in [false, true] {
        for same_address in [false, true] {
            let shared = empty_shared_state();
            let mut memory = Memory::new();
            if concrete {
                memory.add_concrete_region(0x1000..0x1010, HashMap::from([(0x1000, 7), (0x1008, 9)]));
            } else {
                memory.add_symbolic_region(0x1000..0x1010);
            }
            let temp = test_name(950);
            let read = |address| {
                Instr::PrimopVariadic(
                    Loc::Id(temp),
                    primop::variadic_primops()["platform_read_mem"],
                    vec![Exp::Unit, Exp::I128(64), Exp::Bits(B64::new(address, 64)), Exp::I128(1)],
                    info(),
                )
            };
            let program = vec![
                Instr::Decl(temp, Ty::Bits(8), info()),
                Instr::Jump(input(0), 5, info()),
                read(0x1000),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
                Instr::Goto(7),
                read(if same_address { 0x1000 } else { 0x1008 }),
                Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
                Instr::End,
            ];
            let forked = paths_with_memory(program.clone(), &shared, 1, false, memory.clone());
            let merged = paths_with_memory(program, &shared, 1, true, memory);
            assert_eq!((forked.len(), merged.len()), (2, 1), "concrete={concrete}, same={same_address}");
            assert_eq!(merged[0].events.iter().filter(|e| e.is_memory_read()).count(), 2);
            let context = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&context);
            let g = solver.declare_const(smtlib::Ty::Bool, info());
            let mut expected = smtlib::Exp::Bool(false);
            let mut domain = smtlib::Exp::Bool(false);
            for path in &forked {
                let (condition, value) = import(path, &[g], &mut solver);
                expected = smtlib::Exp::Or(
                    Box::new(expected),
                    Box::new(smtlib::Exp::And(Box::new(condition.clone()), Box::new(value))),
                );
                domain = smtlib::Exp::Or(Box::new(domain), Box::new(condition));
            }
            let (condition, value) = import(&merged[0], &[g], &mut solver);
            for (lhs, rhs) in
                [(domain, condition.clone()), (expected, smtlib::Exp::And(Box::new(condition), Box::new(value)))]
            {
                assert!(solver
                    .check_sat_with(&smtlib::Exp::Neq(Box::new(lhs), Box::new(rhs)), info())
                    .is_unsat()
                    .unwrap());
            }
        }
    }
}

// 模拟 SeqMemory 的只读回调：每次新鲜读值都以 solver.assert 绑定内存内容。
// 内容依赖既有输入，能检测错误的无条件重放是否缩小另一臂的成功域。
#[derive(Clone, Debug)]
struct F4ReadConstraint {
    input: Sym,
}
impl crate::memory::MemoryCallbacks<B64> for F4ReadConstraint {
    fn symbolic_read(
        &self,
        regions: &[crate::memory::Region<B64>],
        solver: &mut Solver<B64>,
        value: &Val<B64>,
        kind: &Val<B64>,
        address: &Val<B64>,
        bytes: u32,
        tag: &Option<Val<B64>>,
        opts: &crate::smt::ReadOpts,
    ) -> bool {
        let _ = (regions, kind, address, tag, opts);
        assert_eq!(bytes, 1);
        solver.assert(smtlib::Exp::Eq(
            Box::new(smt_value(value, info()).unwrap()),
            Box::new(smtlib::Exp::Ite(
                Box::new(smtlib::Exp::Var(self.input)),
                Box::new(smtlib::bits64(7, 8)),
                Box::new(smtlib::bits64(9, 8)),
            )),
        ));
        false
    }
    fn symbolic_write(
        &mut self,
        regions: &[crate::memory::Region<B64>],
        solver: &mut Solver<B64>,
        value: Sym,
        kind: &Val<B64>,
        address: &Val<B64>,
        data: &Val<B64>,
        bytes: u32,
        tag: &Option<Val<B64>>,
        opts: &crate::smt::WriteOpts,
    ) -> bool {
        let _ = (regions, solver, value, kind, address, data, bytes, tag, opts);
        panic!("测试只允许读取")
    }
    fn symbolic_write_tag(
        &mut self,
        regions: &[crate::memory::Region<B64>],
        solver: &mut Solver<B64>,
        value: Sym,
        kind: &Val<B64>,
        address: &Val<B64>,
        tag: &Val<B64>,
    ) {
        let _ = (regions, solver, value, kind, address, tag);
        panic!("测试只允许读取")
    }
}

#[test]
fn region_merge_f4_memory_constraints_are_guarded_and_reads_survive_checkpoint() {
    use smtlib::Exp::{And, Eq, Not, Var};
    let shared = empty_shared_state();
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let g = solver.declare_const(smtlib::Ty::Bool, info());
    let value = test_name(960);
    let mut frame = make_frame(vec![
        Instr::Jump(Exp::Bool(true), 3, info()),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(false), info()),
        Instr::Goto(6),
        Instr::PrimopVariadic(
            Loc::Id(value),
            primop::variadic_primops()["platform_read_mem"],
            vec![Exp::Unit, Exp::I128(64), Exp::Bits(B64::new(0x1000, 64)), Exp::I128(1)],
            info(),
        ),
        Instr::PrimopUnary(
            Loc::Id(RETURN),
            primop::unary_primops()["assume"],
            Exp::Call(Op::Eq, vec![Exp::Id(value), Exp::Bits(B64::new(7, 8))]),
            info(),
        ),
        Instr::Copy(Loc::Id(RETURN), Exp::Bool(true), info()),
        Instr::End,
    ]);
    frame.vars_mut().insert(value, UVal::Uninit(&Ty::Bits(8)));
    frame.memory_mut().add_symbolic_region(0x1000..0x1010);
    frame.memory_mut().set_client_info(Box::new(F4ReadConstraint { input: g }));
    assert_eq!(merge_region_for_test(g, 3, &mut frame, &shared, &mut solver, info(), None, None).unwrap(), Some(6));
    assert_eq!(frame.region_merge_records().last().unwrap().memory_reads.len(), 1);
    let read = frame.region_merge_records().last().unwrap().memory_reads[0].clone();
    let Event::ReadMem { value: Val::Symbolic(data), .. } = read.2 else { panic!("读取必须产生新鲜值") };
    assert!(solver.check_sat_with(&Not(Box::new(Var(g))), info()).is_sat().unwrap(), "另一臂不应被读值约束删去");
    let wrong = Eq(Box::new(Var(data)), Box::new(smtlib::bits64(255, 8)));
    assert!(solver.check_sat_with(&And(Box::new(Var(g)), Box::new(wrong.clone())), info()).is_unsat().unwrap());
    assert!(
        solver.check_sat_with(&And(Box::new(Not(Box::new(Var(g)))), Box::new(wrong)), info()).is_sat().unwrap(),
        "未读臂的新鲜读值不得被无条件约束"
    );
    // 从真实合并记录构造样本，检查点清空最近提交快照后仍能使用完整 guard。
    let memory =
        solver.trace().to_vec().into_iter().rev().filter(|event| event.is_memory_read_or_write()).cloned().collect();
    let sample_path = crate::executor::samples::SamplePath {
        pre: BTreeMap::from([("g".into(), Val::Symbolic(g))]),
        post: BTreeMap::new(),
        result: Val::Symbolic(g),
        memory,
        memory_guards: frame
            .region_merge_records()
            .iter()
            .flat_map(|record| record.memory_reads.iter().map(|(index, guard, _)| (*index, guard.clone())))
            .collect(),
    };
    let cp = checkpoint(&mut solver);
    let mut replay = Solver::<B64>::from_checkpoint(&context, cp);
    assert_eq!(replay.trace().to_vec().iter().filter(|event| event.is_memory_read()).count(), 1);
    assert_eq!(unfreeze_frame(&freeze_frame(&frame)).region_merge_records().last().unwrap().memory_reads.len(), 1);
    for direction in [false, true] {
        let tx = replay.start_transaction_with_guard(Some(smtlib::Exp::Bool(true)));
        replay.assert(Eq(Box::new(Var(g)), Box::new(smtlib::Exp::Bool(direction))));
        assert!(replay.check_sat(info()).is_sat().unwrap());
        let mut model = Model::new(&mut replay);
        model.set_complete_model(true);
        let sample = sample_path.materialize(&mut model, &shared, "merge", 1, None).unwrap();
        drop(model);
        assert_eq!(sample.pre_memory.len(), usize::from(direction));
        replay.rollback_transaction(tx);
        assert_eq!(sample_path.check(&mut replay, &shared, &sample).unwrap(), Some(true));
    }
}

/// F4 诊断回归：真实 match 链可分析，固定权限不分叉；辅助入口默认关闭合并。
#[test]
#[ignore = "需要 ISLA_REGIONS_IR 指向真实 Sail IR"]
fn region_merge_f4_real_get_xlpe_diagnosis() {
    let text = std::fs::read_to_string(std::env::var("ISLA_REGIONS_IR").unwrap()).unwrap();
    let mut symtab = Symtab::new();
    let mut definitions =
        crate::ir_parser::IrParser::new().parse(&mut symtab, crate::ir_lexer::new_ir_lexer(&text)).unwrap();
    let types = IRTypeInfo::new(&definitions);
    let config_text = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../agents/path_merge_call_support/baseline_config_const.toml"
    ))
    .unwrap();
    let config = ISAConfig::<B64>::parse(&config_text, None, &symtab, &types).unwrap();
    let mut initialized = crate::init::initialize_architecture(
        &mut definitions,
        symtab,
        types,
        &config,
        AssertionMode::Pessimistic,
        true,
    );
    initialized.shared_state.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let shared = &initialized.shared_state;
    let function = shared.symtab.lookup("zget_xLPE");
    let (params, ret, body) = &shared.functions[&function];
    let summaries = region_summary::function_effect_summaries(shared);
    let terminals =
        summaries.iter().filter_map(|(name, summary)| summary.non_returning.then_some(*name)).collect::<Vec<_>>();
    let mut regions = crate::ir::regions::FunctionRegions::with_options(
        body,
        crate::ir::regions::RegionOptions { have_exception: Some(HAVE_EXCEPTION), terminal_calls: &terminals },
    );
    for pc in [1, 6, 11, 26] {
        assert!(regions.region(pc).is_ok(), "match 跳转链必须能识别 pc={pc}");
    }
    for (fixed, merge) in [(true, false), (true, true), (false, false), (false, true)] {
        shared.execution_stats.reset();
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_path_merging(merge));
        let mut frame = LocalFrame::new(function, params, ret, None, body);
        frame.add_regs(&initialized.regs).add_lets(&initialized.lets);
        reset_registers(0, &mut frame, &state, shared, &mut solver, info()).unwrap();
        let member = |name| {
            let (index, _, id) = shared.type_info.enum_members[&shared.symtab.lookup(name)];
            Val::Enum(crate::smt::EnumMember { enum_id: crate::smt::EnumId::from_name(id), member: index })
        };
        if fixed {
            frame.vars_mut().insert(params[0].0, UVal::Init(member("zSupervisor")));
        } else {
            let value = symbolic(params[0].1, shared, &mut solver, info()).unwrap();
            let exp = smt_value(&value, info()).unwrap();
            for invalid in ["zVirtualSupervisor", "zVirtualUser"] {
                solver.assert(smtlib::Exp::Neq(
                    Box::new(exp.clone()),
                    Box::new(smt_value(&member(invalid), info()).unwrap()),
                ));
            }
            frame.vars_mut().insert(params[0].0, UVal::Init(value));
        }
        let bits = shared.symtab.lookup("zbits");
        for name in ["zmenvcfg", "zsenvcfg", "zmseccfg"] {
            frame.regs_mut().assign(
                shared.symtab.lookup(name),
                Val::Struct(HashMap::from_iter([(bits, Val::Bits(B64::new(0, 64)))])),
                shared,
            );
        }
        let results = Mutex::new(Vec::new());
        start_single(
            frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
            shared,
            &results,
            &|_, _, result, _, mut solver, output| match result {
                Ok((Run::Finished(value), _)) if solver.check_sat(info()).is_sat().unwrap() => {
                    let mut model = Model::new(&mut solver);
                    model.set_complete_model(true);
                    assert_eq!(model.get_val(&value).unwrap(), Val::Bool(false));
                    output.lock().unwrap().push(());
                }
                _ => panic!("get_xLPE 诊断路径不应失败"),
            },
        );
        let count = results.into_inner().unwrap().len();
        eprintln!(
            "F4 get_xLPE fixed={fixed} merge={merge} paths={count} forks={:?} merges={:?}",
            shared.execution_stats.fork_json(&shared.symtab),
            shared.execution_stats.merge_json()
        );
        assert_eq!(count, if fixed || merge { 1 } else { 3 });
    }
}

#[test]
fn region_merge_f4_special_calls_still_rejected_statically() {
    let shared = empty_shared_state();
    for name in [RESET_REGISTERS, INTERRUPT_PENDING, INSTR_ANNOUNCE, ABSTRACT_CALL, ABSTRACT_PRIMOP] {
        let instr = Instr::Call(Loc::Id(RETURN), false, name, Vec::new(), info());
        let reject = region_summary::instruction_effect(TOP_LEVEL_LET, 0, &instr, &shared, &HashMap::new());
        assert!(reject.is_some(), "可执行特殊调用不能当成无实现 Unknown：{name:?}");
    }
}
