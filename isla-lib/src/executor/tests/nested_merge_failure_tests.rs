//! 两个组织者必须保留失败汇合点的片段，并允许祖先继续合并。

use super::region_merge_tests::{equivalent_paths, input, paths_with_state};
use super::*;
use crate::config::RegionOptions;
use serde_json::Value;

pub(super) type Program = Vec<Instr<Name, B64>>;

#[derive(Clone, Copy, Debug)]
pub(super) enum Strategy {
    Recursive,
    Flat { ordered_events: bool },
}

pub(super) fn strategies() -> impl IntoIterator<Item = Strategy> {
    [Strategy::Recursive, Strategy::Flat { ordered_events: false }, Strategy::Flat { ordered_events: true }]
}

impl Strategy {
    pub(super) fn limits(self) -> ExecutionLimits {
        self.apply(ExecutionLimits::default())
    }

    pub(super) fn apply(self, mut limits: ExecutionLimits) -> ExecutionLimits {
        limits.path_merging = true;
        if let Self::Flat { ordered_events } = self {
            limits.merge_strategy = crate::config::MergeStrategy::Flat;
            limits.ordered_events = ordered_events;
        }
        limits
    }
}

#[derive(Debug)]
pub(super) struct Observation {
    paths: (usize, usize),
    records: Vec<(Name, usize, bool)>,
    root_function: String,
    stats: Value,
    rejections: Value,
}

impl Observation {
    pub(super) fn committed(&self, function: Name, branch_pc: usize) -> bool {
        self.records.iter().any(|&(name, pc, _)| name == function && pc == branch_pc)
    }

    pub(super) fn assert_root(&self, forked_paths: usize) {
        let committed = self.records.contains(&(TOP_LEVEL_LET, 0, true));
        let rejected = self.rejections["top"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["function"] == self.root_function && row["branch_pc"] == 0);
        let outcome = match (committed, rejected) {
            (true, false) => "success",
            (false, true) => "rejected",
            (false, false) => "missing",
            (true, true) => "success_and_rejected",
        };
        assert_eq!(
            (outcome, self.paths),
            ("success", (forked_paths, 1)),
            "根 outcome={outcome}，完成路径数={}，合并统计={}，拒绝诊断={}",
            self.paths.1,
            self.stats,
            self.rejections["top"]
        );
        assert!(!self.records.is_empty(), "单条完成路径必须保留合并记录");
    }

    pub(super) fn assert_local_rejection(&self, function: &str, branch_pc: usize, reason: &str) {
        assert!(
            self.stats["failure_reasons"][reason].as_u64().unwrap_or(0) > 0
                && self.rejections["top"].as_array().unwrap().iter().any(|row| {
                    row["function"] == function && row["branch_pc"] == branch_pc && row["reason"] == reason
                }),
            "{function} 的分叉 PC {branch_pc} 应记录本地拒绝 {reason}，实际诊断={}",
            self.rejections["top"]
        );
    }
}

pub(super) fn observe(
    mut shared: SharedState<'static, B64>,
    program: Program,
    inputs: usize,
    strategy: Strategy,
) -> Observation {
    shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
    let run = |code, limits| paths_with_state(code, &shared, inputs, limits, crate::memory::Memory::new(), |_| ());
    let forked = run(program.clone(), ExecutionLimits::default().with_path_merging(false));
    // 保留字符串不兼容作为局部失败夹具，检查祖先合并和守卫不受影响。
    let mut limits = strategy.limits();
    limits.merge_concrete_values = false;
    let merged = run(program, limits);
    let paths = equivalent_paths(&forked, &merged, inputs, true);
    Observation {
        paths,
        records: merged
            .iter()
            .flat_map(|path| &path.records)
            .filter(|record| record.outcome == RegionRecordOutcome::Merged)
            .map(|record| (record.function, record.branch_pc, record.parent_record.is_none()))
            .collect(),
        root_function: crate::zencode::decode(shared.symtab.to_str(TOP_LEVEL_LET)),
        stats: shared.execution_stats.merge_json(),
        rejections: shared.execution_stats.arm_unsupported_json(&shared.symtab),
    }
}

pub(super) fn copy_return(value: Exp<Name>) -> Instr<Name, B64> {
    Instr::Copy(Loc::Id(RETURN), value, info())
}

fn eq(lhs: Exp<Name>, rhs: Exp<Name>) -> Exp<Name> {
    Exp::Call(Op::Eq, vec![lhs, rhs])
}

pub(super) fn read_string(dest: Name, slot: Name) -> Instr<Name, B64> {
    Instr::PrimopBinary(
        Loc::Id(dest),
        primop::binary_primops()["eq_string"],
        Exp::Id(slot),
        Exp::String("a".into()),
        info(),
    )
}

fn string_arm(slot: Name, value: &str) -> Instr<Name, B64> {
    Instr::Copy(Loc::Id(slot), Exp::String(value.into()), info())
}

pub(super) fn string_region(pc: usize, condition: Exp<Name>, slot: Name, different: bool) -> Program {
    vec![
        Instr::Decl(slot, Ty::String, info()),
        Instr::Jump(condition, pc + 4, info()),
        string_arm(slot, "a"),
        Instr::Goto(pc + 5),
        string_arm(slot, if different { "b" } else { "a" }),
        read_string(RETURN, slot),
    ]
}

const ACCESS_NAME: &str = "nested_access";

fn access(shared: &mut SharedState<'static, B64>, different: bool) -> Name {
    let function = shared.symtab.intern("znested_access");
    let width = shared.symtab.intern("znested_width");
    let first_guard = shared.symtab.intern("znested_first_guard");
    let second_guard = shared.symtab.intern("znested_second_guard");
    let string = shared.symtab.intern("znested_string");
    let mut body = string_region(0, Exp::Id(first_guard), string, different);
    // 首次使用字符串后，后续可正常合并的分支只读取布尔结果。
    body.extend([
        Instr::Jump(Exp::Id(second_guard), 9, info()),
        copy_return(eq(Exp::Id(RETURN), eq(Exp::Id(width), Exp::I64(2)))),
        Instr::Goto(10),
        copy_return(eq(Exp::Id(RETURN), eq(Exp::Id(width), Exp::I64(8)))),
        Instr::End,
    ]);
    let params = vec![(width, &Ty::I64), (first_guard, &Ty::Bool), (second_guard, &Ty::Bool)];
    shared.functions.insert(function, (params, &Ty::Bool, Box::leak(body.into_boxed_slice())));
    function
}

fn call_access(function: Name, width: i64, first_guard: u32, second_guard: u32) -> Instr<Name, B64> {
    Instr::Call(
        Loc::Id(RETURN),
        false,
        function,
        vec![Exp::I64(width), input(first_guard), input(second_guard)],
        info(),
    )
}

fn load_shape(strategy: Strategy, different: bool) -> Observation {
    let mut shared = empty_shared_state();
    let callee = access(&mut shared, different);
    // 两个宽度选择位产生四臂。每臂调用同一个 access，只有宽度参数不同。
    let program = vec![
        Instr::Jump(input(0), 6, info()),
        Instr::Jump(input(1), 4, info()),
        call_access(callee, 1, 2, 3),
        Instr::Goto(5),
        call_access(callee, 2, 2, 3),
        Instr::Goto(11),
        Instr::Jump(input(1), 9, info()),
        call_access(callee, 4, 2, 3),
        Instr::Goto(10),
        call_access(callee, 8, 2, 3),
        Instr::Goto(11),
        Instr::End,
    ];
    let observed = observe(shared, program, 4, strategy);
    if different {
        observed.assert_local_rejection(ACCESS_NAME, 1, "SpeculativeRejectReason::IncompatibleState");
    }
    observed
}

fn check_load_shape(different: bool) {
    for strategy in strategies() {
        let observed = load_shape(strategy, different);
        observed.assert_root(16);
    }
}

#[test]
fn nested_inner_merge_failure_outer_merges_load_shape() {
    check_load_shape(true);
}

#[test]
fn nested_inner_merge_failure_outer_merges_load_shape_control() {
    check_load_shape(false);
}

fn check_three_levels(different: bool) {
    for strategy in strategies() {
        let mut shared = empty_shared_state();
        let slot = shared.symtab.intern("znested_three_levels_slot");
        // 根区域内嵌套三层，PC 3、6、10 各有独立的汇合点。
        let mut program = vec![
            Instr::Jump(input(0), 3, info()),
            copy_return(input(3)),
            Instr::Goto(18),
            Instr::Jump(input(1), 6, info()),
            copy_return(Exp::Bool(true)),
            Instr::Goto(17),
            Instr::Jump(input(2), 9, info()),
            copy_return(input(3)),
            Instr::Goto(16),
        ];
        program.extend(string_region(9, input(3), slot, different));
        program.extend([Instr::Goto(16), Instr::Goto(17), Instr::Goto(18), Instr::End]);
        let observed = observe(shared, program, 4, strategy);
        if different {
            observed.assert_local_rejection(&observed.root_function, 10, "SpeculativeRejectReason::IncompatibleState");
        }
        observed.assert_root(5);
        for pc in [3, 6] {
            assert!(observed.committed(TOP_LEVEL_LET, pc), "第 {pc} 条指令的汇合点必须提交：{observed:?}");
        }
        assert_eq!(observed.committed(TOP_LEVEL_LET, 10), !different, "最内层汇合点的合并结果不符");
    }
}

#[test]
fn nested_three_levels_innermost_fails() {
    check_three_levels(true);
}

#[test]
fn nested_three_levels_innermost_fails_control() {
    check_three_levels(false);
}

fn check_callee(different: bool) {
    for strategy in strategies() {
        let mut shared = empty_shared_state();
        let callee = access(&mut shared, different);
        let program = vec![
            Instr::Jump(input(0), 3, info()),
            copy_return(input(2)),
            Instr::Goto(4),
            call_access(callee, 2, 1, 2),
            Instr::End,
        ];
        let observed = observe(shared, program, 3, strategy);
        if different {
            observed.assert_local_rejection(ACCESS_NAME, 1, "SpeculativeRejectReason::IncompatibleState");
        }
        observed.assert_root(5);
        assert!(observed.committed(callee, 6), "被调函数中后续的正常分支必须合并");
    }
}

#[test]
fn nested_callee_region_fails_caller_merges() {
    check_callee(true);
}

#[test]
fn nested_callee_region_fails_caller_merges_control() {
    check_callee(false);
}

fn union_region(shared: &mut SharedState<'static, B64>, slot: Name, different: bool) -> Program {
    let definitions = crate::ir_parser::IrParser::new()
        .parse(&mut shared.symtab, crate::ir_lexer::new_ir_lexer("union zNestedValue { zNestedBits: %bv }"))
        .unwrap();
    shared.type_info = IRTypeInfo::new::<B64>(&definitions);
    let union = shared.symtab.lookup("zNestedValue");
    let ctor = shared.symtab.lookup("zNestedBits");
    let length = shared.symtab.intern("znested_payload_length");
    let arm = |bits| Instr::Call(Loc::Id(slot), false, ctor, vec![Exp::Bits(B64::new(1, bits))], info());
    // 两个载荷均符合动态位向量类型。宽度不同只会在合并同标签载荷时被拒绝。
    vec![
        Instr::Decl(slot, Ty::Union(union), info()),
        Instr::Jump(input(1), 7, info()),
        arm(8),
        Instr::Goto(8),
        arm(if different { 16 } else { 8 }),
        Instr::Decl(length, Ty::I128, info()),
        Instr::PrimopUnary(
            Loc::Id(length),
            primop::unary_primops()["length"],
            Exp::Unwrap(ctor, Box::new(Exp::Id(slot))),
            info(),
        ),
        copy_return(eq(Exp::Id(length), Exp::I128(8))),
    ]
}

fn check_failure_reasons(different: bool) {
    for strategy in strategies() {
        let observations =
            [("SpeculativeRejectReason::IncompatibleState", false), ("SpeculativeRejectReason::UnionPayload", true)]
                .map(|(reason, union)| {
                    let mut shared = empty_shared_state();
                    let slot = shared.symtab.intern("znested_reason_slot");
                    let body = if union {
                        union_region(&mut shared, slot, different)
                    } else {
                        string_region(3, input(1), slot, different)
                    };
                    let mut program =
                        vec![Instr::Jump(input(0), 3, info()), copy_return(input(1)), Instr::Goto(3 + body.len())];
                    program.extend(body);
                    program.push(Instr::End);
                    let observed = observe(shared, program, 2, strategy);
                    if different {
                        observed.assert_local_rejection(&observed.root_function, 4, reason);
                    } else {
                        assert_eq!(observed.rejections["total"], 0, "同形对照不得被拒绝");
                    }
                    assert_eq!(observed.committed(TOP_LEVEL_LET, 4), !different, "内层汇合点的合并结果不符");
                    (reason, observed)
                });
        // 两种失配全部执行完再检查外层，第一种红灯也必须留下第二种的结果。
        for (reason, observed) in &observations {
            eprintln!("{reason}：完成路径数={}，拒绝诊断={}", observed.paths.1, observed.rejections["top"]);
        }
        for (_, observed) in observations {
            observed.assert_root(3);
        }
    }
}

#[test]
fn nested_inner_failure_reasons() {
    check_failure_reasons(true);
}

#[test]
fn nested_inner_failure_reasons_control() {
    check_failure_reasons(false);
}

fn boundary_program(shared: &mut SharedState<'static, B64>, wrapped: bool, different: bool) -> Program {
    let slot = shared.symtab.intern("znested_boundary_slot");
    let compared = shared.symtab.intern("znested_boundary_compared");
    let (pc, mut program) = if wrapped {
        (3, vec![Instr::Jump(input(0), 3, info()), copy_return(input(2)), Instr::Goto(16)])
    } else {
        (0, Vec::new())
    };
    // pc+2 的内层先合并，pc+1 的区域在自己的汇合点才遇到两个不同字符串。
    program.extend([
        Instr::Decl(slot, Ty::String, info()),
        Instr::Jump(input(1), pc + 8, info()),
        Instr::Jump(input(2), pc + 5, info()),
        copy_return(Exp::Bool(false)),
        Instr::Goto(pc + 6),
        copy_return(Exp::Bool(true)),
        string_arm(slot, "a"),
        Instr::Goto(pc + 10),
        copy_return(Exp::Bool(true)),
        string_arm(slot, if different { "b" } else { "a" }),
        Instr::Decl(compared, Ty::Bool, info()),
        read_string(compared, slot),
        copy_return(Exp::Call(Op::And, vec![Exp::Id(RETURN), Exp::Id(compared)])),
        Instr::End,
    ]);
    program
}

fn observe_boundary(strategy: Strategy, wrapped: bool, different: bool) -> Observation {
    let mut shared = empty_shared_state();
    let program = boundary_program(&mut shared, wrapped, different);
    observe(shared, program, 3, strategy)
}

#[test]
fn nested_failure_is_local_to_its_join_without_ancestor() {
    for strategy in strategies() {
        let observed = observe_boundary(strategy, false, true);
        observed.assert_local_rejection(&observed.root_function, 1, "SpeculativeRejectReason::IncompatibleState");
        assert_eq!(observed.paths, (3, 2));
        assert!(!observed.committed(TOP_LEVEL_LET, 1), "失败的汇合点不得提交");
        assert!(observed.committed(TOP_LEVEL_LET, 2), "正常的子区域必须仍能合并");
    }
}

#[test]
fn nested_failure_is_local_to_its_join() {
    for strategy in strategies() {
        let observed = observe_boundary(strategy, true, true);
        observed.assert_local_rejection(&observed.root_function, 4, "SpeculativeRejectReason::IncompatibleState");
        assert!(!observed.committed(TOP_LEVEL_LET, 4), "失败的汇合点不得提交");
        observed.assert_root(4);
    }
}

#[test]
fn nested_failure_is_local_to_its_join_control() {
    for strategy in strategies() {
        let observed = observe_boundary(strategy, true, false);
        observed.assert_root(4);
        assert!(observed.committed(TOP_LEVEL_LET, 4), "等值对照必须提交中层汇合点");
        assert!(observed.committed(TOP_LEVEL_LET, 5), "等值对照必须提交最内层汇合点");
    }
}

fn check_both_exit_modes(test_name: &str, different: bool) {
    const CHILD: &str = "ISLA_NESTED_FAILURE_EXIT_MODE";
    if let Ok(mode) = std::env::var(CHILD) {
        let defer_exit_check = match mode.as_str() {
            "immediate" => false,
            "deferred" => true,
            _ => panic!("未知的出口检查模式 {mode}"),
        };
        RegionOptions { defer_exit_check, ..Default::default() }.configure();
        check_load_shape(different);
        return;
    }

    // 区域配置在进程内冻结，两种模式分别运行。
    let (_, test_name) = test_name.split_once("::").unwrap();
    let outputs = ["immediate", "deferred"].map(|mode| {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", test_name, "--test-threads=1"])
            .env(CHILD, mode)
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let passed =
            output.status.success() && stdout.lines().any(|line| line.starts_with("test result: ok. 1 passed;"));
        (passed, format!("{mode}（{}）\n{stdout}{stderr}", output.status))
    });
    assert!(outputs.iter().all(|(passed, _)| *passed), "{}\n{}", outputs[0].1, outputs[1].1);
}

#[test]
fn nested_failure_defer_and_immediate() {
    check_both_exit_modes(concat!(module_path!(), "::nested_failure_defer_and_immediate"), true);
}

#[test]
fn nested_failure_defer_and_immediate_control() {
    check_both_exit_modes(concat!(module_path!(), "::nested_failure_defer_and_immediate_control"), false);
}

#[test]
fn unknown_z3_nested_arm_keeps_root_and_survivor() {
    for strategy in strategies() {
        let mut shared = empty_shared_state();
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let program = vec![
            Instr::Jump(input(0), 3, info()),
            copy_return(Exp::Bool(false)),
            Instr::Goto(7),
            Instr::Jump(input(1), 6, info()),
            copy_return(Exp::Bool(false)),
            Instr::Goto(7),
            copy_return(Exp::Bool(true)),
            Instr::End,
        ];
        let paths = super::path_failure_policy_tests::with_solver_dead(|| {
            crate::smt::test_queries::with_results([None, None, Some(z3_sys::Z3_L_UNDEF)], || {
                paths_with_state(program, &shared, 2, strategy.limits(), crate::memory::Memory::new(), |_| ())
            })
        });
        assert_eq!(paths.len(), 1);
        assert!(matches!(paths[0].value, Val::Bool(false)));
        assert!(paths[0]
            .records
            .iter()
            .any(|record| record.branch_pc == 0 && record.outcome == RegionRecordOutcome::Merged));
        let diagnostics = shared.execution_stats.merge_json();
        assert_eq!(diagnostics["solver_timeout_dropped_paths"], 1);
        assert_eq!(diagnostics["failures"], 0);
    }
}

#[test]
fn unknown_z3_nested_arm_panics_in_both_organizers() {
    for strategy in strategies() {
        let mut shared = empty_shared_state();
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let program = vec![
            Instr::Jump(input(0), 3, info()),
            copy_return(Exp::Bool(false)),
            Instr::Goto(7),
            Instr::Jump(input(1), 6, info()),
            copy_return(Exp::Bool(false)),
            Instr::Goto(7),
            copy_return(Exp::Bool(true)),
            Instr::End,
        ];
        let message = super::path_failure_policy_tests::panic_message(|| {
            crate::smt::test_queries::with_results([None, None, Some(z3_sys::Z3_L_UNDEF)], || {
                paths_with_state(program, &shared, 2, strategy.limits(), crate::memory::Memory::new(), |_| ())
            });
        });
        assert!(message.contains("branch_feasibility"), "{message}");
        assert_eq!(shared.execution_stats.solver_path_drop_count(), 0);
    }
}

#[test]
fn partial_commit_unknown_z3_keeps_outer_merge() {
    const TEST: &str = "executor::tests::nested_merge_failure_tests::partial_commit_unknown_z3_keeps_outer_merge";
    let args = ["--exact", TEST, "--nocapture", "--test-threads=1"];
    if !std::env::args().skip(1).eq(args) {
        let result = std::process::Command::new(std::env::current_exe().unwrap()).args(args).output().unwrap();
        assert!(
            result.status.success(),
            "{}{}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
        return;
    }
    RegionOptions { partial_commit_unknown_z3: true, ..Default::default() }.configure();
    for strategy in strategies() {
        let program = vec![
            Instr::Jump(input(0), 3, info()),
            copy_return(Exp::Bool(false)),
            Instr::Goto(7),
            Instr::Jump(input(1), 6, info()),
            copy_return(Exp::Bool(false)),
            Instr::Goto(7),
            copy_return(Exp::Bool(true)),
            Instr::End,
        ];
        let plain = paths_with_state(
            program.clone(),
            &empty_shared_state(),
            2,
            ExecutionLimits::default().with_path_merging(false),
            crate::memory::Memory::new(),
            |_| (),
        );
        let mut shared = empty_shared_state();
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let merged = super::path_failure_policy_tests::with_solver_dead(|| {
            crate::smt::test_queries::with_results([None, None, Some(z3_sys::Z3_L_UNDEF)], || {
                paths_with_state(program, &shared, 2, strategy.limits(), crate::memory::Memory::new(), |_| ())
            })
        });
        assert_eq!(equivalent_paths(&plain, &merged, 2, true), (3, 1));
        assert!(merged[0].records.iter().any(|record| record.branch_pc == 0 && record.parent_record.is_none()));
        assert_eq!(shared.execution_stats.merge_json()["failure_reasons"]["SpeculativeRejectReason::UnknownZ3"], 1);
    }
}

#[test]
fn unknown_z3_exit_obligation_replays_and_drops_per_path() {
    const TEST: &str =
        "executor::tests::nested_merge_failure_tests::unknown_z3_exit_obligation_replays_and_drops_per_path";
    let args = ["--exact", TEST, "--nocapture", "--test-threads=1"];
    if !std::env::args().skip(1).eq(args) {
        let result = std::process::Command::new(std::env::current_exe().unwrap()).args(args).output().unwrap();
        assert!(
            result.status.success(),
            "{}{}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
        return;
    }
    RegionOptions { defer_exit_check: true, ..Default::default() }.configure();
    for strategy in strategies() {
        let mut shared = empty_shared_state();
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let check = || {
            Instr::PrimopBinary(
                Loc::Id(RETURN),
                primop::optimistic_assert::<B64>,
                input(1),
                Exp::String("assertion".into()),
                info(),
            )
        };
        let program = vec![Instr::Jump(input(0), 3, info()), check(), Instr::Goto(4), check(), Instr::End];
        let mut replay = empty_shared_state();
        replay.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let paths = crate::smt::test_queries::with_unknown_purposes(&["exit_obligations"], || {
            paths_with_state(program.clone(), &replay, 2, strategy.limits(), crate::memory::Memory::new(), |_| ())
        });
        assert_eq!(paths.len(), 2, "区域出口 Unknown 须回放两条路径");
        assert_eq!(replay.execution_stats.solver_path_drop_count(), 0);
        assert_eq!(replay.execution_stats.merge_json()["failure_reasons"]["SpeculativeRejectReason::UnknownZ3"], 1);
        let paths = super::path_failure_policy_tests::with_solver_dead(|| {
            crate::smt::test_queries::with_unknown_purposes(&["exit_obligations", "assertion", "assertion"], || {
                paths_with_state(program, &shared, 2, strategy.limits(), crate::memory::Memory::new(), |_| ())
            })
        });
        assert!(paths.is_empty());
        let diagnostics = shared.execution_stats.merge_json();
        assert_eq!(diagnostics["solver_timeout_dropped_paths"], 2);
        assert_eq!(diagnostics["failure_reasons"]["SpeculativeRejectReason::UnknownZ3"], 1);
        let drops = shared.execution_stats.solver_path_drops_since(0);
        assert!(drops.first_locations.iter().all(|drop| drop.purpose == "assertion"));
    }
}

#[test]
fn partial_commit_nested_retry_operand_keeps_root() {
    const CHILD: &str = "ISLA_TEST_PARTIAL_COMMIT_RETRY_OPERAND";
    let enabled = match std::env::var(CHILD).as_deref() {
        Ok("true") => true,
        Ok("false") => false,
        Ok(value) => panic!("无效的测试开关 {value}"),
        Err(_) => {
            let name = concat!(module_path!(), "::partial_commit_nested_retry_operand_keeps_root");
            let (_, name) = name.split_once("::").unwrap();
            for setting in ["false", "true"] {
                let output = std::process::Command::new(std::env::current_exe().unwrap())
                    .args(["--exact", name, "--nocapture", "--test-threads=1"])
                    .env(CHILD, setting)
                    .output()
                    .unwrap();
                let stdout = String::from_utf8_lossy(&output.stdout);
                assert!(
                    output.status.success()
                        && stdout.lines().any(|line| line.starts_with("test result: ok. 1 passed;")),
                    "{setting}\n{stdout}{}",
                    String::from_utf8_lossy(&output.stderr)
                );
            }
            return;
        }
    };
    RegionOptions { partial_commit_retry_operand: enabled, ..Default::default() }.configure();
    use smtlib::Exp::{Ite, Var};
    for strategy in strategies() {
        let mut shared = empty_shared_state();
        let exponent = shared.symtab.intern("znested_exponent");
        let power = shared.symtab.intern("znested_power");
        let program = vec![
            Instr::Jump(input(0), 3, info()),
            copy_return(Exp::Bool(false)),
            Instr::Goto(11),
            Instr::Jump(input(1), 6, info()),
            copy_return(Exp::Bool(false)),
            Instr::Goto(11),
            Instr::Decl(exponent, Ty::I128, info()),
            Instr::Decl(power, Ty::I128, info()),
            Instr::PrimopReset(
                Loc::Id(exponent),
                Arc::new(|_, _, solver| {
                    Ok(Val::Symbolic(solver.define_bitvector(
                        Ite(
                            Box::new(Var(Sym::from_u32(2))),
                            Box::new(crate::primop_util::smt_i128(1)),
                            Box::new(crate::primop_util::smt_i128(0)),
                        ),
                        info(),
                    )))
                }),
                primop::Effect::Pure,
                info(),
            ),
            Instr::PrimopBinary(
                Loc::Id(power),
                primop::binary_primops()["pow_int"],
                Exp::I128(-1),
                Exp::Id(exponent),
                info(),
            ),
            copy_return(eq(Exp::Id(power), Exp::I128(-1))),
            Instr::End,
        ];
        let observation = observe(shared, program, 3, strategy);
        let reason = SpeculativeRejectReason::RetryOperand.to_string();
        if enabled {
            observation.assert_root(4);
            observation.assert_local_rejection(&observation.root_function, 9, &reason);
        } else {
            assert_eq!(observation.paths, (4, 4));
            assert!(!observation.committed(TOP_LEVEL_LET, 0));
            observation.assert_local_rejection(&observation.root_function, 0, &reason);
        }
    }
}
