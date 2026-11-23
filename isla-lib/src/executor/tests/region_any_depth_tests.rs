//! 区域在任意嵌套层失败时须保留已合并前缀，外层继续汇合等价出口。

use super::nested_merge_failure_tests::{
    copy_return, observe, read_string, strategies, string_region, Program, Strategy,
};
use super::region_merge_tests::{
    equivalent_paths, equivalent_register_paths, input, paths_with_state, paths_with_state_in_order, Path,
};
use super::*;
use crate::config::RegionOptions;

fn location(level: usize) -> SourceLoc {
    // 根入口在建立区域事务前查询，仍遵循普通路径的 panic/dead 策略。
    if level == 0 {
        info()
    } else {
        SourceLoc::unknown_unique(level as u32)
    }
}

fn nested_diamonds(depth: usize, mut after_child: impl FnMut(usize) -> Program) -> Program {
    fn level(depth: usize, current: usize, base: usize, after_child: &mut impl FnMut(usize) -> Program) -> Program {
        if current == depth {
            return vec![copy_return(input(depth as u32))];
        }
        let mut inner = level(depth, current + 1, base + 1, after_child);
        inner.extend(after_child(current));
        let sibling = base + inner.len() + 2;
        let mut code = vec![Instr::Jump(input(current as u32), sibling, location(current))];
        code.extend(inner);
        code.push(Instr::Goto(sibling + 1));
        code.push(copy_return(input((depth + current + 1) as u32)));
        code
    }

    let mut program = level(depth, 0, 0, &mut after_child);
    program.push(Instr::End);
    program
}

fn paths(program: &Program, shared: &SharedState<'static, B64>, inputs: usize, limits: ExecutionLimits) -> Vec<Path> {
    paths_with_state(program.clone(), shared, inputs, limits, crate::memory::Memory::new(), |_| ())
}

fn plain_paths(program: &Program, inputs: usize) -> Vec<Path> {
    paths(program, &empty_shared_state(), inputs, ExecutionLimits::default().with_path_merging(false))
}

fn run_in_partial_commit_process(test: &str, options: RegionOptions, run: impl FnOnce()) {
    let (_, test_name) = test.split_once("::").unwrap();
    let args = ["--exact", test_name, "--nocapture", "--test-threads=1"];
    const CHILD: &str = "ISLA_TEST_REGION_ANY_DEPTH";
    if std::env::var_os(CHILD).as_deref() != Some(std::ffi::OsStr::new(test_name)) {
        let result = std::process::Command::new(std::env::current_exe().unwrap())
            .args(args)
            .env(CHILD, test_name)
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&result.stdout);
        assert!(
            result.status.success() && stdout.lines().any(|line| line.starts_with("test result: ok. 1 passed;")),
            "{stdout}{}",
            String::from_utf8_lossy(&result.stderr)
        );
        return;
    }
    options.configure();
    run();
}

fn assert_record(paths: &[Path], function: Name, pc: usize, root: bool) {
    assert!(
        paths.iter().flat_map(|path| &path.records).any(|record| {
            !record.dead
                && record.function == function
                && record.branch_pc == pc
                && record.parent_record.is_none() == root
        }),
        "函数 {function:?} 的 PC {pc} 汇合记录丢失，根记录={root}"
    );
}

#[test]
fn native_query_failures_keep_complementary_branches_and_original_reasons() {
    let options = RegionOptions {
        partial_commit_prefix: true,
        partial_commit_z3_resource_exhausted: true,
        partial_commit_z3_timeout: true,
        ..Default::default()
    };
    run_in_partial_commit_process(
        concat!(module_path!(), "::native_query_failures_keep_complementary_branches_and_original_reasons"),
        options,
        || {
            let depth = 3;
            let inputs = 2 * depth + 1;
            let program = nested_diamonds(depth, |_| Vec::new());
            let plain = plain_paths(&program, inputs);
            for (detail, reason) in [
                ("max. resource limit exceeded", SpeculativeRejectReason::Z3ResourceExhausted),
                ("timeout", SpeculativeRejectReason::Z3Timeout),
            ] {
                for query in [0, 1] {
                    let mut shared = empty_shared_state();
                    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
                    let (merged, observed) =
                        crate::smt::test_queries::with_observed_branch_failure(Some((query, detail)), || {
                            super::path_failure_policy_tests::with_solver_dead(|| {
                                paths(&program, &shared, inputs, Strategy::Recursive.limits())
                            })
                        });
                    assert_eq!(observed.rejected, Some(location(1)), "{reason:?}，查询 {query}");
                    assert_eq!(shared.execution_stats.solver_path_drop_count(), 0);
                    assert_eq!(shared.execution_stats.merge_json()["failure_reasons"][reason.to_string()], 1);
                    assert_eq!(equivalent_paths(&plain, &merged, inputs, true), (depth + 1, 1));
                    assert_record(&merged, TOP_LEVEL_LET, 0, true);
                }
            }
        },
    );
}

#[test]
fn any_depth_single_failure_stays_local() {
    let options = RegionOptions { partial_commit_prefix: true, partial_commit_unknown_z3: true, ..Default::default() };
    run_in_partial_commit_process(concat!(module_path!(), "::any_depth_single_failure_stays_local"), options, || {
        use crate::smt::test_queries::with_observed_branches;
        for depth in 2..=5 {
            let inputs = 2 * depth + 1;
            let program = nested_diamonds(depth, |_| Vec::new());
            let plain = plain_paths(&program, inputs);
            assert_eq!(plain.len(), depth + 1);
            for strategy in strategies() {
                let run = |inject| {
                    let mut shared = empty_shared_state();
                    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
                    let (merged, observed) = with_observed_branches(inject, || {
                        super::path_failure_policy_tests::with_solver_dead(|| {
                            paths(&program, &shared, inputs, strategy.limits())
                        })
                    });
                    (merged, observed, shared.execution_stats.clone())
                };
                let (_, baseline, _) = run(None);
                for level in 1..depth {
                    assert_eq!(baseline.queried.iter().filter(|site| **site == location(level)).count(), 2);
                }
                assert_eq!(baseline.queried.len(), 2 * (depth - 1));
                for (index, site) in baseline.queried.into_iter().enumerate() {
                    let (merged, observed, stats) = run(Some(index));
                    eprintln!("深度 {depth}，{strategy:?}，查询 {index}，位置 {site:?}，终态 {}", merged.len());
                    assert_eq!(observed.rejected, Some(site), "必须命中指定的真实查询");
                    assert_eq!(stats.solver_path_drop_count(), 0, "局部推演失败不得丢掉普通路径");
                    let reason = SpeculativeRejectReason::UnknownZ3.to_string();
                    assert_eq!(stats.merge_json()["failure_reasons"][reason], 1);
                    assert_eq!(equivalent_paths(&plain, &merged, inputs, true), (depth + 1, 1));
                    assert_record(&merged, TOP_LEVEL_LET, 0, true);
                }
            }
        }
    });
}

#[test]
fn any_depth_no_failure_merges_to_one_path() {
    for depth in 2..=5 {
        let inputs = 2 * depth + 1;
        let program = nested_diamonds(depth, |_| Vec::new());
        let plain = plain_paths(&program, inputs);
        for strategy in strategies() {
            let merged = paths(&program, &empty_shared_state(), inputs, strategy.limits());
            assert_eq!(equivalent_paths(&plain, &merged, inputs, true), (depth + 1, 1), "深度 {depth}，{strategy:?}");
            for pc in 0..depth {
                assert_record(&merged, TOP_LEVEL_LET, pc, pc == 0);
            }
        }
    }
}

#[derive(Default)]
struct CutVisits {
    prefix: AtomicUsize,
    rejected: AtomicUsize,
    resumed: AtomicUsize,
    scope_restored: AtomicUsize,
}

fn outside_cut(cut: usize) -> smtlib::Exp<Sym> {
    use smtlib::Exp::{Or, Var};
    (0..cut).fold(Var(Sym::from_u32(cut as u32)), |guard, parent| {
        Or(Box::new(guard), Box::new(Var(Sym::from_u32(parent as u32))))
    })
}

fn middle_cut(depth: usize, cut: usize, visits: Arc<CutVisits>) -> Program {
    let prefix_slot = test_name(880);
    let result_slot = test_name(881);
    nested_diamonds(depth, |level| {
        if level != cut {
            return Vec::new();
        }
        let prefix_visits = visits.clone();
        let query_visits = visits.clone();
        let after_visits = visits.clone();
        let source = SourceLoc::unknown_unique(200 + cut as u32);
        vec![
            Instr::Decl(prefix_slot, Ty::Unit, info()),
            Instr::PrimopReset(
                Loc::Id(prefix_slot),
                Arc::new(move |_, _, solver| {
                    prefix_visits.prefix.fetch_add(1, Ordering::Relaxed);
                    if solver.region_queries_deferred() {
                        let safe = smtlib::Exp::Not(Box::new(outside_cut(cut)));
                        assert!(solver.defer_symbolic_assertion(safe, source));
                    }
                    Ok(Val::Unit)
                }),
                primop::Effect::Pure,
                info(),
            ),
            Instr::Decl(result_slot, Ty::Unit, info()),
            Instr::PrimopReset(
                Loc::Id(result_slot),
                Arc::new(move |_, _, solver| match solver.check_sat_with(&outside_cut(cut), source) {
                    SmtResult::Unsat => {
                        query_visits.resumed.fetch_add(1, Ordering::Relaxed);
                        Ok(Val::Unit)
                    }
                    SmtResult::Unproven(cause @ crate::error::SmtError::DeferredQuery { .. }) => {
                        query_visits.rejected.fetch_add(1, Ordering::Relaxed);
                        Err(ExecError::Unproven(cause))
                    }
                    result => panic!("恢复查询必须引用完整的臂守卫：{result:?}"),
                }),
                primop::Effect::Pure,
                source,
            ),
            Instr::PrimopReset(
                Loc::Id(result_slot),
                Arc::new(move |_, _, solver| {
                    if solver.region_queries_deferred() {
                        assert!(
                            matches!(
                                solver.check_sat(source),
                                SmtResult::Unproven(crate::error::SmtError::DeferredQuery { .. })
                            ),
                            "普通必需查询许可不能泄漏到下一条指令"
                        );
                        after_visits.scope_restored.fetch_add(1, Ordering::Relaxed);
                    }
                    Ok(Val::Unit)
                }),
                primop::Effect::Pure,
                info(),
            ),
        ]
    })
}

fn check_nested_monomorphize_cut() {
    let choice = test_name(882);
    let program = nested_diamonds(3, |level| {
        if level != 1 {
            return Vec::new();
        }
        vec![
            Instr::Decl(choice, Ty::Bool, info()),
            Instr::Copy(Loc::Id(choice), input(7), info()),
            Instr::Monomorphize(choice, Ty::Bool, location(level)),
            copy_return(Exp::Call(Op::Eq, vec![Exp::Id(RETURN), Exp::Id(choice)])),
        ]
    });
    let ordinary = plain_paths(&program, 8);
    for strategy in strategies() {
        let mut shared = empty_shared_state();
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let merged = paths(&program, &shared, 8, strategy.limits());
        assert_eq!(equivalent_paths(&ordinary, &merged, 8, true), (6, 1), "{strategy:?}");
        let reason = SpeculativeRejectReason::UnknownDeferredMode.to_string();
        assert_eq!(shared.execution_stats.merge_json()["failure_reasons"][reason], 1);
        assert_record(&merged, TOP_LEVEL_LET, 0, true);
        assert_record(&merged, TOP_LEVEL_LET, 2, false);
    }
}

#[test]
fn middle_level_failure_keeps_inner_prefix_and_outer_merge() {
    let options = RegionOptions {
        defer_exit_check: true,
        lazy_z3_scope: true,
        partial_commit_prefix: true,
        partial_commit_deferred_mode: true,
        ..Default::default()
    };
    run_in_partial_commit_process(
        concat!(module_path!(), "::middle_level_failure_keeps_inner_prefix_and_outer_merge"),
        options,
        || {
            for (depth, cut) in [(3, 1), (4, 1), (4, 2), (5, 3), (2, 0)] {
                let inputs = 2 * depth + 1;
                let plain = plain_paths(&middle_cut(depth, cut, Arc::new(CutVisits::default())), inputs);
                for strategy in strategies() {
                    for reverse in [false, true] {
                        let visits = Arc::new(CutVisits::default());
                        let merged = paths_with_state_in_order(
                            middle_cut(depth, cut, visits.clone()),
                            &empty_shared_state(),
                            inputs,
                            strategy.limits(),
                            crate::memory::Memory::new(),
                            |_| (),
                            reverse,
                        );
                        let label = format!("深度 {depth}，切点 {cut}，{strategy:?}，逆序 {reverse}");
                        let expected = if cut == 0 { 2 } else { 1 };
                        eprintln!(
                            "{label}，终态 {}，前缀 {}，拒绝 {}，恢复 {}",
                            merged.len(),
                            visits.prefix.load(Ordering::Relaxed),
                            visits.rejected.load(Ordering::Relaxed),
                            visits.resumed.load(Ordering::Relaxed)
                        );
                        assert_eq!(equivalent_paths(&plain, &merged, inputs, true), (depth + 1, expected), "{label}");
                        assert_eq!(visits.prefix.load(Ordering::Relaxed), 1, "完成的前缀不得重做，{label}");
                        assert_eq!(visits.rejected.load(Ordering::Relaxed), 1, "拒绝须发生且只发生一次，{label}");
                        assert_eq!(visits.resumed.load(Ordering::Relaxed), 1, "仅失败臂恢复一次，{label}");
                        assert_eq!(visits.scope_restored.load(Ordering::Relaxed), usize::from(cut != 0), "{label}");
                        for pc in 0..depth {
                            if pc != cut {
                                assert_record(&merged, TOP_LEVEL_LET, pc, pc == if cut == 0 { 1 } else { 0 });
                            }
                        }
                    }
                }
            }
            check_nested_monomorphize_cut();
        },
    );
}

fn call(function: Name, args: Vec<Exp<Name>>) -> Instr<Name, B64> {
    Instr::Call(Loc::Id(RETURN), false, function, args, info())
}

fn call_chain(shared: &mut SharedState<'static, B64>, different: bool) -> (Program, [Name; 3]) {
    let functions = ["zany_depth_f1", "zany_depth_f2", "zany_depth_f3"].map(|name| shared.symtab.intern(name));
    let args = [
        "zany_depth_arg_0",
        "zany_depth_arg_1",
        "zany_depth_arg_2",
        "zany_depth_arg_3",
        "zany_depth_arg_4",
        "zany_depth_arg_5",
        "zany_depth_arg_6",
        "zany_depth_arg_7",
    ]
    .map(|name| shared.symtab.intern(name));
    let params: Vec<_> = args.iter().map(|name| (*name, &Ty::Bool)).collect();
    let slot = shared.symtab.intern("zany_depth_string");
    let mut leaf = string_region(0, Exp::Id(args[2]), slot, different);
    leaf.push(Instr::End);
    shared.functions.insert(functions[2], (params.clone(), &Ty::Bool, Box::leak(leaf.into_boxed_slice())));
    for level in (0..2).rev() {
        let body = vec![
            Instr::Jump(Exp::Id(args[level]), 3, info()),
            copy_return(Exp::Id(args[5])),
            Instr::Goto(12),
            Instr::Jump(Exp::Id(args[level + 6]), 6, info()),
            copy_return(Exp::Bool(false)),
            Instr::Goto(7),
            copy_return(Exp::Bool(true)),
            call(functions[level + 1], args.iter().copied().map(Exp::Id).collect()),
            Instr::Jump(Exp::Id(args[level + 3]), 11, info()),
            copy_return(Exp::Call(Op::Not, vec![Exp::Id(RETURN)])),
            Instr::Goto(12),
            copy_return(Exp::Id(RETURN)),
            Instr::End,
        ];
        shared.functions.insert(functions[level], (params.clone(), &Ty::Bool, Box::leak(body.into_boxed_slice())));
    }
    let program = vec![
        Instr::Jump(input(8), 3, info()),
        copy_return(input(5)),
        Instr::Goto(4),
        call(functions[0], (0..8).map(input).collect()),
        Instr::End,
    ];
    (program, functions)
}

#[test]
fn deep_call_chain_failure_stays_local() {
    for strategy in strategies() {
        for different in [true, false] {
            let mut shared = empty_shared_state();
            let (program, [first, second, third]) = call_chain(&mut shared, different);
            let observed = observe(shared, program, 9, strategy);
            observed.assert_root(38);
            for caller in [first, second] {
                assert!(observed.committed(caller, 0), "调用者的外层区域必须汇合");
                assert!(observed.committed(caller, 3), "调用前的区域必须汇合");
                assert!(observed.committed(caller, 8), "返回后的区域也必须汇合");
            }
            assert_eq!(observed.committed(third, 1), !different);
            if different {
                observed.assert_local_rejection(
                    "any_depth_f3",
                    1,
                    &SpeculativeRejectReason::IncompatibleState.to_string(),
                );
            }
        }
    }
}

#[test]
fn outer_join_merges_equivalent_fragments_to_fewest_paths() {
    let mut shared = empty_shared_state();
    let slot = shared.symtab.intern("zany_depth_group_string");
    let reg = shared.symtab.intern("zany_depth_group_register");
    shared.registers.insert(reg, Ty::Bool);
    for different in [false, true] {
        let save = |text: &str| Instr::Copy(Loc::Id(slot), Exp::String(text.into()), info());
        let write = |value| Instr::Copy(Loc::Id(reg), Exp::Bool(value), info());
        let program = vec![
            Instr::Decl(slot, Ty::String, info()),
            Instr::Jump(input(0), 9, info()),
            Instr::Jump(input(1), 6, info()),
            save("a"),
            write(false),
            Instr::Goto(8),
            save("b"),
            write(true),
            Instr::Goto(16),
            Instr::Jump(input(1), 13, info()),
            save(if different { "c" } else { "a" }),
            write(false),
            Instr::Goto(15),
            save(if different { "d" } else { "b" }),
            write(true),
            Instr::Goto(16),
            read_string(RETURN, slot),
            Instr::End,
        ];
        let run = |limits, reverse| {
            paths_with_state_in_order(
                program.clone(),
                &shared,
                2,
                limits,
                crate::memory::Memory::new(),
                |frame| frame.regs_mut().insert(reg, false, UVal::Init(Val::Bool(false))),
                reverse,
            )
        };
        let plain = run(ExecutionLimits::default().with_path_merging(false), false);
        for strategy in strategies() {
            for reverse in [false, true] {
                let mut limits = strategy.limits();
                limits.merge_concrete_values = false;
                let merged = run(limits, reverse);
                let expect = if different { 4 } else { 2 };
                assert_eq!(equivalent_paths(&plain, &merged, 2, true), (4, expect), "{strategy:?}，逆序 {reverse}");
                equivalent_register_paths(&plain, &merged, 2);
                for path in &merged {
                    assert_eq!(
                        path.events
                            .iter()
                            .filter(|event| matches!(event, Event::WriteReg(name, _, _) if *name == reg))
                            .count(),
                        1,
                        "每个组只发布一次寄存器写，{strategy:?}，逆序 {reverse}"
                    );
                }
            }
        }
    }
}
