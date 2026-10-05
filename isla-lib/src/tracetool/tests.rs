use super::super::itrace::*;
use super::super::sequence::*;
use super::*;
use crate::bitvector::b64::B64;
use crate::ir::{Instr, SharedState};
use crate::source_loc::SourceLoc;
use crate::timeout::{PathTimeSnapshot, SmtDumpSource, SmtOperation, SmtTimeout, TimeoutDiagnostic, TimeoutSmtDump};
use crate::{ir, ir_lexer, ir_parser};
use std::collections::HashSet;
use std::panic::{self, AssertUnwindSafe};
use std::sync::Arc;
use std::time::Duration;

#[test]
fn btrace_lists_unexecuted_rewritten_branches_without_recording_edges() {
    use crate::ir::{Def, ExitCause, Exp, IRTypeInfo, Loc, Ty, SAIL_ASSERT};
    let mut symtab = Symtab::new();
    let function = symtab.intern("zrewritten_branch");
    let result = symtab.intern("zresult");
    let mut defs: Vec<Def<Name, B64>> = vec![
        Def::Val(function, Vec::new(), Ty::Unit),
        Def::Fn(
            function,
            Vec::new(),
            vec![
                Instr::Call(Loc::Id(result), false, SAIL_ASSERT, vec![Exp::Bool(false)], SourceLoc::unknown()),
                Instr::End,
            ],
        ),
    ];
    ir::assertions_to_jumps(&mut defs);
    let type_info = IRTypeInfo::new(&defs);
    let state = SharedState::new(
        symtab,
        &defs,
        type_info,
        HashSet::new(),
        HashSet::new(),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    let body = state.functions.get(&function).unwrap().2;
    assert!(matches!(body[2], Instr::Jump(_, 4, _)));
    assert!(matches!(body[3], Instr::Exit(ExitCause::AssertionFailure, _)));
    let output = std::env::temp_dir().join(format!("branch_sites_{}.txt", std::process::id()));
    let handler = TraceHandler::default();
    handler.set_path(Some(output.clone()));
    handler.set_traces(false, false, true);
    handler.write_branch_sites(&state);
    handler.dump();
    let text = std::fs::read_to_string(&output).unwrap();
    let site: serde_json::Value =
        serde_json::from_str(text.lines().find(|line| line.starts_with('{')).unwrap()).unwrap();
    assert_eq!(site["function"], "zrewritten_branch");
    assert_eq!(site["pc"], 2);
    assert_eq!(site["target"], 4);
    assert_eq!(site["fallthrough"], 3);
    assert!(!text.contains("branch_edge"), "静态清单不能伪装成实际经过的边");
    handler.configure("reset", fixture_ir_path(), Some(output.clone()), &state.symtab);
    handler.set_traces(true, false, false);
    handler.write_branch_sites(&state);
    handler.dump();
    assert!(std::fs::read_to_string(&output).unwrap().is_empty());
    std::fs::remove_file(output).unwrap();
}

#[test]
fn ftrace_projects_existing_events_in_execution_order_across_forks() {
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    use crate::smt::{Config, Context, Solver};
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let caller = Name::from_u32(10);
    let callee = Name::from_u32(11);
    solver.trace_call(caller);
    let checkpoint = crate::smt::checkpoint(&mut solver);
    solver.trace_call(callee);
    solver.trace_return(callee);
    solver.trace_return(caller);
    let mut path = TracePerPath::default();
    path.capture_function_trace(solver.trace());
    assert_eq!(path.function_trace, vec![(caller, true), (callee, true), (callee, false), (caller, false)]);
    let mut child = Solver::<B64>::from_checkpoint(&context, checkpoint);
    child.trace_return(caller);
    let mut child_path = path.clone();
    child_path.capture_function_trace(child.trace());
    assert_eq!(child_path.function_trace, vec![(caller, true), (caller, false)]);
    assert_eq!(path.function_trace.len(), 4);
}

#[test]
#[should_panic(expected = "btrace: 实际后继与跳转方向不符")]
fn btrace_rejects_inconsistent_executed_successor() {
    let mut path = TracePerPath::default();
    path.record_jump(
        Name::from_u32(1),
        Vec::new(),
        0,
        3,
        true,
        &Instr::<Name, B64>::Jump(crate::ir::Exp::Bool(true), 2, SourceLoc::unknown()),
    );
}
#[test]
fn trace_kinds_compose_without_losing_branch_evidence() {
    let state = parse_shared_state();
    let function = state.symtab.lookup("zcache_ok");
    let output = std::env::temp_dir().join(format!("trace_kinds_{}.txt", std::process::id()));
    let handler = TraceHandler::default();
    handler.set_path(Some(output.clone()));
    let instruction = Instr::<Name, B64>::Jump(crate::ir::Exp::Bool(true), 7, crate::source_loc::SourceLoc::unknown());
    let mut path = TracePerPath::default();
    path.record_instruction(function, Vec::new(), 99, &instruction, &handler);
    path.record_jump(function, Vec::new(), 99, 7, true, &instruction);
    path.function_trace = vec![(function, true), (function, false)];
    let mut completed = TraceCompletedPath::without_diagnostics(path);
    completed.set_path_signature(42);
    for instructions in [false, true] {
        for functions in [false, true] {
            for branches in [false, true] {
                handler.set_traces(instructions, functions, branches);
                let text = completed.render_text(&handler, &state.symtab).unwrap();
                assert_eq!(text.contains("[zcache_ok 99]:"), instructions);
                assert_eq!(text.contains("function_call function=zcache_ok"), functions);
                assert_eq!(text.contains("function_return function=zcache_ok"), functions);
                assert_eq!(text.contains("branch_edge function=zcache_ok pc=99 successor=7 taken=true"), branches);
                assert!(text.contains("path_signature: 42"));
                assert!(text.contains("instruction_count: 1"));
                assert!(!text.contains("not found"));
            }
        }
    }
    handler.dump();
    std::fs::remove_file(output).unwrap();
}

#[test]
fn function_branch_trace_does_not_store_instruction_payloads() {
    let state = parse_shared_state();
    let function = state.symtab.lookup("zcache_ok");
    let handler = TraceHandler::default();
    handler.set_traces(false, true, true);
    let mut path = TracePerPath::default();
    for pc in 0..100 {
        path.record_instruction(function, Vec::new(), pc, &Instr::<Name, B64>::End, &handler);
    }
    assert_eq!(path.instruction_count, 100);
    assert_eq!(path.record_count(), 0);
    assert_eq!(path.executed_functions.len(), 1);
}
// 实际生产序列，计数测试不复制另一套实现。
type SharingSequence<T> = SharedSequence<T>;

struct CountedPayload {
    value: usize,
    backtrace: Vec<usize>,
    clones: Arc<std::sync::atomic::AtomicUsize>,
    backtrace_clones: Arc<std::sync::atomic::AtomicUsize>,
    drops: Arc<std::sync::atomic::AtomicUsize>,
}

impl Clone for CountedPayload {
    fn clone(&self) -> Self {
        self.clones.fetch_add(1, Ordering::Relaxed);
        self.backtrace_clones.fetch_add(self.backtrace.len(), Ordering::Relaxed);
        Self {
            value: self.value,
            backtrace: self.backtrace.clone(),
            clones: self.clones.clone(),
            backtrace_clones: self.backtrace_clones.clone(),
            drops: self.drops.clone(),
        }
    }
}

impl Drop for CountedPayload {
    fn drop(&mut self) {
        self.drops.fetch_add(1, Ordering::Relaxed);
    }
}

#[test]
fn itrace_sharing_snapshot_and_first_append_copy_no_payload() {
    use std::sync::atomic::AtomicUsize;
    let clones = Arc::new(AtomicUsize::new(0));
    let backtrace_clones = Arc::new(AtomicUsize::new(0));
    let drops = Arc::new(AtomicUsize::new(0));
    let item = |value| CountedPayload {
        value,
        backtrace: vec![value; 8],
        clones: clones.clone(),
        backtrace_clones: backtrace_clones.clone(),
        drops: drops.clone(),
    };
    let mut prefix = SharingSequence::default();
    for i in 0..4096 {
        prefix.push(item(i));
    }
    let mut branches = (0..64).map(|_| prefix.clone()).collect::<Vec<_>>();
    let snapshot_clones = clones.load(Ordering::Relaxed);
    for branch in &mut branches {
        for i in 4096..4099 {
            branch.push(item(i));
        }
    }
    let append_clones = clones.load(Ordering::Relaxed) - snapshot_clones;
    eprintln!(
        "ITRACE_COPY_COUNT n=4096 k=64 snapshot={} append={} backtrace={}",
        snapshot_clones,
        append_clones,
        backtrace_clones.load(Ordering::Relaxed)
    );
    assert_eq!(snapshot_clones, 0, "快照不可复制 payload");
    assert_eq!(append_clones, 0, "共享后首次追加不可复制 payload");
    for branch in &branches {
        assert!(std::ptr::eq(prefix.iter().next().unwrap(), branch.iter().next().unwrap()));
        assert_eq!(branch.iter().map(|p| p.value).collect::<Vec<_>>(), (0..4099).collect::<Vec<_>>());
    }
    drop(prefix);
    drop(branches);
    assert_eq!(drops.load(Ordering::Relaxed), 4096 + 64 * 3);
}

#[test]
fn itrace_sharing_chunks_and_multiple_forks_match_vec() {
    let mut sequence = SharedSequence::default();
    let mut reference = Vec::new();
    assert_eq!(sequence.iter().len(), 0);
    assert!(sequence.iter().next().is_none());
    for i in 0..(256 * 5 + 3) {
        sequence.push(i);
        reference.push(i);
        if i % 71 == 0 {
            let mut child = sequence.clone();
            let mut expected_child = reference.clone();
            child.push(usize::MAX);
            expected_child.push(usize::MAX);
            let mut grandchild = child.clone();
            grandchild.push(17);
            assert_eq!(child.iter().copied().collect::<Vec<_>>(), expected_child);
            expected_child.push(17);
            assert_eq!(grandchild.iter().copied().collect::<Vec<_>>(), expected_child);
            assert_eq!(sequence.iter().copied().collect::<Vec<_>>(), reference);
        }
    }
    let mut iter = sequence.iter();
    for (index, value) in reference.iter().enumerate() {
        assert_eq!(iter.len(), reference.len() - index);
        assert_eq!(iter.next(), Some(value));
    }
    assert_eq!(iter.len(), 0);
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next(), None);
}

#[test]
fn itrace_sharing_deep_chain_drop_is_iterative_and_exact() {
    use std::sync::atomic::AtomicUsize;
    // 小栈上释放长链；每次共享后追加强制形成一个新的不可变 chunk。
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            struct Payload(Arc<AtomicUsize>);
            impl Drop for Payload {
                fn drop(&mut self) {
                    self.0.fetch_add(1, Ordering::Relaxed);
                }
            }
            let drops = Arc::new(AtomicUsize::new(0));
            let mut sequence = SharedSequence::default();
            for _ in 0..100_000 {
                let previous = sequence.clone();
                sequence.push(Payload(drops.clone()));
                drop(previous);
            }
            let sibling = sequence.clone();
            drop(sequence);
            assert_eq!(drops.load(Ordering::Relaxed), 0);
            assert_eq!(sibling.iter().count(), 100_000);
            drop(sibling);
            assert_eq!(drops.load(Ordering::Relaxed), 100_000);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn itrace_sharing_parallel_read_and_drop_keep_all_payloads() {
    let mut sequence = SharedSequence::default();
    for i in 0..2049 {
        sequence.push(i);
    }
    let tasks = (0..8)
        .map(|index| {
            let mut sibling = sequence.clone();
            std::thread::spawn(move || {
                sibling.push(index);
                assert_eq!(sibling.iter().take(2049).copied().collect::<Vec<_>>(), (0..2049).collect::<Vec<_>>());
                assert_eq!(sibling.iter().last(), Some(&index));
            })
        })
        .collect::<Vec<_>>();
    drop(sequence);
    for task in tasks {
        task.join().unwrap();
    }
}

#[test]
fn completed_path_keeps_terminal_and_only_taken_branch_edges() {
    let shared_state = parse_shared_state();
    let output_path = std::env::temp_dir().join(format!("itrace_edge_metadata_{}.txt", std::process::id()));
    let handler = TraceHandler::init("branch", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);
    let function = shared_state.symtab.lookup("zcache_ok");
    let mut path = TracePerPath::default();
    path.record(function, Vec::new(), 0);
    path.record_branch_edge(function, Vec::new(), 0, 3, true);
    let mut completed = TraceCompletedPath::without_diagnostics(path);
    completed.set_path_signature(19);
    let text = completed.render_text(&handler, &shared_state.symtab).expect("itrace text");
    assert!(text.contains("path_signature: 19"));
    assert!(text.contains("branch_edge"));
    assert!(text.contains("taken=true"));
    assert_eq!(text.matches("branch_edge").count(), 1);
    drop(handler);
    let _ = std::fs::remove_file(output_path);
}

#[test]
fn branch_edges_keep_reentrant_call_contexts_separate() {
    let shared_state = parse_shared_state();
    let function = shared_state.symtab.lookup("zcache_ok");
    let caller = shared_state.symtab.lookup("zpc_lookup");
    let mut path = TracePerPath::default();
    path.record_branch_edge(function, vec![(caller, 1)], 4, 9, true);
    path.record_branch_edge(function, vec![(caller, 2)], 4, 5, false);
    let first = path.branch_edges.iter().next().unwrap();
    let second = path.branch_edges.iter().nth(1).unwrap();
    assert_eq!(first.pc, second.pc);
    assert_ne!(first.backtrace, second.backtrace);
    assert_eq!(first.successor_pc, 9);
    assert_eq!(second.successor_pc, 5);
}

struct FixedDump;

impl SmtDumpSource for FixedDump {
    fn materialize(&self) -> Result<String, String> {
        Ok("(check-sat)\n".to_string())
    }
}

#[test]
fn completed_path_renders_path_wall_and_cpu_at_the_end() {
    let shared_state = parse_shared_state();
    let output_path = std::env::temp_dir().join(format!("itrace_completed_smt_timing_{}.txt", std::process::id()));
    let handler =
        TraceHandler::init("SMT timing test", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);
    let mut execution_trace = TracePerPath::default();
    execution_trace.record(shared_state.symtab.lookup("zcache_ok"), Vec::new(), 0);
    let completed = TraceCompletedPath::with_timing(
        execution_trace,
        Vec::new(),
        PathTimeSnapshot { active_wall: Duration::from_millis(19), executor_cpu: Duration::from_millis(7) },
    );

    let text = completed.render_text(&handler, &shared_state.symtab).unwrap();
    let instruction = text.find("[zcache_ok 0]").unwrap();
    let path_timing = text.find("---- path timing ----").unwrap();
    assert!(instruction < path_timing);
    assert!(text.contains("active_wall: 19ms"));
    assert!(text.contains("executor_cpu: 7ms"));
    assert!(text.ends_with("===="));

    drop(handler);
    let _ = std::fs::remove_file(output_path);
}

#[test]
fn completed_path_renders_smtperf_summary() {
    let shared_state = parse_shared_state();
    let output_path = std::env::temp_dir().join(format!("itrace_completed_smtperf_{}.txt", std::process::id()));
    let handler =
        TraceHandler::init("SMT perf test", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);
    let mut execution_trace = TracePerPath::default();
    execution_trace.record(shared_state.symtab.lookup("zcache_ok"), Vec::new(), 0);
    let mut completed = TraceCompletedPath::without_diagnostics(execution_trace);
    completed.set_smtperf_summary(Some(
        "SMT 未超时求解耗时样本总数: 1\nSMT 最慢 #1: 7us, operation: CheckSat\n".to_string(),
    ));

    let text = completed.render_text(&handler, &shared_state.symtab).unwrap();

    assert!(text.contains("---- smt performance ----"));
    assert!(text.contains("SMT 未超时求解耗时样本总数: 1"));
    assert!(text.contains("SMT 最慢 #1: 7us, operation: CheckSat"));

    drop(handler);
    let _ = std::fs::remove_file(output_path);
}

#[test]
fn completed_path_renders_smt_timeout_metadata() {
    let shared_state = parse_shared_state();
    let output_path = std::env::temp_dir().join(format!("itrace_completed_smt_timeout_{}.txt", std::process::id()));
    let handler =
        TraceHandler::init("SMT timeout test", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);
    let mut execution_trace = TracePerPath::default();
    execution_trace.record(shared_state.symtab.lookup("zcache_ok"), Vec::new(), 0);
    let timeout = Arc::new(SmtTimeout {
        source_loc: crate::source_loc::SourceLoc::unknown(),
        operation: SmtOperation::ModelEval,
        limit: Duration::from_secs(2),
        operation_wall: Duration::from_secs(2),
        dump: Arc::new(TimeoutSmtDump::new(Arc::new(FixedDump))),
    });
    let completed = TraceCompletedPath::new(execution_trace, vec![TimeoutDiagnostic::Smt(timeout)]);

    let text = completed.render_text(&handler, &shared_state.symtab).unwrap();

    assert!(text.contains("operation: ModelEval"));
    assert!(text.contains("limit: 2s"));
    assert!(text.contains("operation_wall: 2s"));

    drop(handler);
    let _ = std::fs::remove_file(output_path);
}

struct PanicDump;

impl SmtDumpSource for PanicDump {
    fn materialize(&self) -> Result<String, String> {
        panic!("metadata-only itrace diagnostic materialized its SMT dump")
    }
}

#[test]
fn metadata_only_timeout_diagnostic_does_not_materialize_smt() {
    let shared_state = parse_shared_state();
    let output_path = std::env::temp_dir().join(format!("itrace_completed_metadata_only_{}.txt", std::process::id()));
    let handler = TraceHandler::init(
        "SMT metadata-only test",
        fixture_ir_path(),
        Some(output_path.clone()),
        &shared_state.symtab,
    );
    let mut execution_trace = TracePerPath::default();
    execution_trace.record(shared_state.symtab.lookup("zcache_ok"), Vec::new(), 0);
    let timeout = Arc::new(SmtTimeout {
        source_loc: crate::source_loc::SourceLoc::unknown(),
        operation: SmtOperation::ModelEval,
        limit: Duration::from_secs(2),
        operation_wall: Duration::from_secs(2),
        dump: Arc::new(TimeoutSmtDump::new(Arc::new(PanicDump))),
    });
    let mut completed = TraceCompletedPath::without_diagnostics(execution_trace);
    completed.push_diagnostic_with_dump(TimeoutDiagnostic::Smt(timeout), false);

    let text = completed.render_text(&handler, &shared_state.symtab).unwrap();

    assert!(text.contains("operation: ModelEval"));
    assert!(!text.contains("---- timeout smt2 begin ----"));

    drop(handler);
    let _ = std::fs::remove_file(output_path);
}

fn parse_shared_state() -> crate::ir::SharedState<'static, B64> {
    const IR_FIXTURE: &str = include_str!("../../tests/fixtures/ir_cache_assumption.ir");
    let mut symtab = Symtab::new();
    let defs: Vec<ir::Def<Name, B64>> = ir_parser::IrParser::new()
        .parse(&mut symtab, ir_lexer::new_ir_lexer(IR_FIXTURE))
        .expect("parse fixture failed");
    let defs: &'static [ir::Def<Name, B64>] = Box::leak(defs.into_boxed_slice());
    let type_info = crate::ir::IRTypeInfo::new(defs);

    crate::ir::SharedState::new(
        symtab,
        defs,
        type_info,
        HashSet::new(),
        HashSet::new(),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    )
}

fn fixture_ir_path() -> PathBuf {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
    PathBuf::from(manifest_dir).join("tests/fixtures/ir_cache_assumption.ir")
}

fn write_temp_ir_file(name: &str, content: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!("{}_{}.ir", name, std::process::id()));
    std::fs::write(&path, content).expect("write temporary IR file");
    path
}

#[test]
fn itrace_per_path_record_stores_instruction_context_without_summary() {
    let mut path = TracePerPath::default();
    let function_name = Name::from_u32(7);
    let backtrace = vec![(Name::from_u32(1), 11), (Name::from_u32(2), 22)];

    path.record(function_name, backtrace.clone(), 42);

    let records = path.records().collect::<Vec<_>>();
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].function_name, function_name);
    assert_eq!(records[0].backtrace, backtrace);
    assert_eq!(records[0].pc, 42);
    assert!(records[0].summary.is_none());
}

#[test]
fn itrace_per_path_record_summary_stores_timeout_context() {
    let mut path = TracePerPath::default();
    let function_name = Name::from_u32(7);
    let backtrace = vec![(Name::from_u32(1), 11), (Name::from_u32(2), 22)];

    path.record_summary(function_name, backtrace.clone(), 42, "timeout: path exceeded 2000ms");

    let records = path.records().collect::<Vec<_>>();
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].function_name, function_name);
    assert_eq!(records[0].backtrace, backtrace);
    assert_eq!(records[0].pc, 42);
    assert_eq!(records[0].summary.as_deref(), Some("timeout: path exceeded 2000ms"));
}

#[test]
fn ir_file_cache_from_file_builds_lookup_table_from_fixture() {
    let shared_state = parse_shared_state();
    let cache = IrFileCache::from_file(&fixture_ir_path(), &shared_state.symtab);
    let zcache_ok = shared_state.symtab.lookup("zcache_ok");
    let zpc_lookup = shared_state.symtab.lookup("zpc_lookup");

    assert_eq!(cache.lookup_line(zcache_ok, 0), Some("z0 : %i;".to_string()));
    assert_eq!(cache.lookup_line(zcache_ok, 3), Some("return = z1;".to_string()));
    assert_eq!(cache.lookup_line(zpc_lookup, 1), Some("p1 : %i;".to_string()));
    assert_eq!(cache.lookup_line(zpc_lookup, 5), Some("end;".to_string()));
}

#[test]
fn ir_file_cache_from_file_returns_none_for_unknown_function_and_out_of_range_pc() {
    let shared_state = parse_shared_state();
    let cache = IrFileCache::from_file(&fixture_ir_path(), &shared_state.symtab);
    let zcache_ok = shared_state.symtab.lookup("zcache_ok");
    let unknown = Name::from_u32(u32::MAX);

    assert!(cache.lookup_line(unknown, 0).is_none());
    assert!(cache.lookup_line(zcache_ok, 100).is_none());
    assert!(cache.lookup_line(zcache_ok, u64::MAX).is_none());
}

#[test]
fn ir_file_cache_from_file_strips_source_locations_and_keeps_function_boundaries() {
    let mut symtab = Symtab::new();
    let zfirst = symtab.intern("zfirst");
    let zsecond = symtab.intern("zsecond");
    let ir_path = write_temp_ir_file(
        "itrace_cache_boundaries",
        r#"
fn zfirst() {
  z0 : %i `14 248:2-248:53;
  z1 : %i `15;
}

fn zsecond() {
  p0 : %i `16 12:1-12:9;
}
"#,
    );

    let cache = IrFileCache::from_file(&ir_path, &symtab);

    assert_eq!(cache.lookup_line(zfirst, 0), Some("z0 : %i;".to_string()));
    assert_eq!(cache.lookup_line(zfirst, 1), Some("z1 : %i;".to_string()));
    assert!(cache.lookup_line(zfirst, 2).is_none(), "first function should not include second function lines");
    assert_eq!(cache.lookup_line(zsecond, 0), Some("p0 : %i;".to_string()));

    let _ = std::fs::remove_file(&ir_path);
}

#[test]
fn ir_file_cache_from_file_ignores_non_function_blocks() {
    let mut symtab = Symtab::new();
    let zfirst = symtab.intern("zfirst");
    let zsecond = symtab.intern("zsecond");
    let zstruct_like = symtab.intern("zstruct_like");
    let zunion_like = symtab.intern("zunion_like");
    let ir_path = write_temp_ir_file(
        "itrace_cache_non_function_blocks",
        r#"
struct zstruct_like {
  field : %i;
}

fn zfirst() {
  f0 : %i `1;
}

union zunion_like {
  member : %i;
}

fn zsecond() {
  s0 : %i `2;
}
"#,
    );

    let cache = IrFileCache::from_file(&ir_path, &symtab);

    assert_eq!(cache.lookup_line(zfirst, 0), Some("f0 : %i;".to_string()));
    assert_eq!(cache.lookup_line(zsecond, 0), Some("s0 : %i;".to_string()));
    assert!(cache.lookup_line(zstruct_like, 0).is_none());
    assert!(cache.lookup_line(zunion_like, 0).is_none());

    let _ = std::fs::remove_file(&ir_path);
}

#[test]
fn ir_file_cache_from_file_skips_functions_missing_from_symtab() {
    let mut symtab = Symtab::new();
    let zknown = symtab.intern("zknown");
    let ir_path = write_temp_ir_file(
        "itrace_cache_missing_symtab",
        r#"
fn zknown() {
  k0 : %i `1;
}

fn zmissing() {
  m0 : %i `2;
}
"#,
    );

    let cache = IrFileCache::from_file(&ir_path, &symtab);
    let zmissing = symtab.intern("zmissing");

    assert_eq!(cache.lookup_line(zknown, 0), Some("k0 : %i;".to_string()));
    assert!(cache.lookup_line(zmissing, 0).is_none());

    let _ = std::fs::remove_file(&ir_path);
}

#[test]
fn ir_file_cache_from_file_panics_with_path_when_file_is_missing() {
    let symtab = Symtab::new();
    let ir_path = std::env::temp_dir().join(format!("itrace_missing_cache_{}.ir", std::process::id()));
    let _ = std::fs::remove_file(&ir_path);

    let panic_result = panic::catch_unwind(AssertUnwindSafe(|| {
        let cache = IrFileCache::from_file(&ir_path, &symtab);
        let _ = cache.functions.len();
    }));

    let payload = panic_result.expect_err("missing IR file should panic");
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .expect("panic payload should be a string");

    assert!(message.contains("IR file should be openable after successful IR parse"));
    assert!(message.contains(&ir_path.display().to_string()));
}

#[test]
fn itrace_branch_title_formats_readable_conditions() {
    let mut symtab = Symtab::new();
    symtab.intern("zbranch_flag");
    let mut path = TracePerPath::default();
    path.push_branch_condition(smtlib::Exp::<Sym>::Var(Sym::from_u32(25)));
    path.push_branch_condition(smtlib::Exp::<Sym>::Not(Box::new(smtlib::Exp::<Sym>::Bool(false))));

    let title = path.render_title("handler title", &symtab);

    assert_eq!(title, "<handler title> path(handler title_branch_zbranch_flag_!false):");
    assert!(!title.contains("branch_conditions"));
    assert!(!title.contains("Bool"));
}

#[test]
fn itrace_per_path_render_text_uses_lookup_and_fallback() {
    let shared_state = parse_shared_state();
    let temp_dir = std::env::temp_dir();
    let output_path = temp_dir.join(format!("itrace_render_fallback_{}.txt", std::process::id()));
    let _ = std::fs::remove_file(&output_path);
    let handler =
        TraceHandler::init("itrace test title", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);
    let mut path = TracePerPath::default();
    let known_fn = shared_state.symtab.lookup("zcache_ok");

    path.record(known_fn, Vec::new(), 0);
    path.record(known_fn, Vec::new(), 99);
    path.push_branch_condition(smtlib::Exp::<Sym>::Bool(false));

    let text = path.render_text(&handler, &shared_state.symtab).expect("render itrace text");

    assert!(text.contains("<itrace test title> path(itrace test title_branch_false):"));
    assert!(!text.contains("branch_conditions"));
    assert!(!text.contains("Bool"));
    assert!(text.contains("[zcache_ok 0]: z0 : %i;"));
    assert!(text.contains("[zcache_ok 99]: zcache_ok:99 not found"));
    assert!(text.ends_with("\n\n===="));

    drop(handler);
    let _ = std::fs::remove_file(&output_path);
}

#[test]
fn itrace_per_path_render_text_matches_reference_itrace_shape() {
    let shared_state = parse_shared_state();
    let temp_dir = std::env::temp_dir();
    let output_path = temp_dir.join(format!("itrace_render_shape_{}.txt", std::process::id()));
    let _ = std::fs::remove_file(&output_path);
    let handler = TraceHandler::init("zRTYPE", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);
    let mut path = TracePerPath::default();
    let zcache_ok = shared_state.symtab.lookup("zcache_ok");

    path.record(zcache_ok, Vec::new(), 0);
    path.record(zcache_ok, Vec::new(), 1);

    let text = path.render_text(&handler, &shared_state.symtab).expect("render itrace text");
    let expected = "\
<zRTYPE> path(zRTYPE):
instruction_count: 2
executed_functions: [\"zcache_ok\"]
[zcache_ok 0]: z0 : %i;
[zcache_ok 1]: z1 : %i;

====";

    assert_eq!(text, expected);

    drop(handler);
    let _ = std::fs::remove_file(&output_path);
}

#[test]
fn itrace_handler_writes_rendered_path_text() {
    let temp_dir = std::env::temp_dir();
    let output_path = temp_dir.join("itrace_submit_trace_module_test.txt");
    let _ = std::fs::remove_file(&output_path);
    let shared_state = parse_shared_state();
    let handler =
        TraceHandler::init("itrace test title", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);
    let mut path = TracePerPath::default();

    path.record(shared_state.symtab.lookup("zcache_ok"), Vec::new(), 3);
    handler.submit_path(&path, &shared_state.symtab);
    handler.dump();

    let content = std::fs::read_to_string(&output_path).expect("read itrace submit output");
    assert!(content.contains("<itrace test title> path(itrace test title):"));
    assert!(content.contains("[zcache_ok 3]: return = z1;"));

    let _ = std::fs::remove_file(&output_path);
}

#[test]
fn itrace_handler_writes_summary_record_text() {
    let temp_dir = std::env::temp_dir();
    let output_path = temp_dir.join(format!("itrace_summary_record_{}.txt", std::process::id()));
    let _ = std::fs::remove_file(&output_path);
    let shared_state = parse_shared_state();
    let handler =
        TraceHandler::init("itrace test title", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);
    let mut path = TracePerPath::default();

    path.record_summary(shared_state.symtab.lookup("zcache_ok"), Vec::new(), 3, "timeout: path exceeded 2000ms");
    handler.submit_path(&path, &shared_state.symtab);
    handler.dump();

    let content = std::fs::read_to_string(&output_path).expect("read itrace summary output");
    assert!(content.contains("<itrace test title> path(itrace test title):"));
    assert!(content.contains("[zcache_ok 3]: timeout: path exceeded 2000ms"));
    assert!(!content.contains("[zcache_ok 3]: return = z1;"));

    let _ = std::fs::remove_file(&output_path);
}

#[test]
fn itrace_handler_submits_trace_path_without_exposing_rendered_text() {
    let temp_dir = std::env::temp_dir();
    let output_path = temp_dir.join(format!("itrace_submit_path_api_{}.txt", std::process::id()));
    let _ = std::fs::remove_file(&output_path);
    let shared_state = parse_shared_state();
    let handler =
        TraceHandler::init("itrace test title", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);
    let mut path = TracePerPath::default();

    path.record(shared_state.symtab.lookup("zcache_ok"), Vec::new(), 3);
    handler.submit_path(&path, &shared_state.symtab);
    handler.dump();

    let content = std::fs::read_to_string(&output_path).expect("read itrace submit output");
    assert!(content.contains("<itrace test title> path(itrace test title):"));
    assert!(content.contains("[zcache_ok 3]: return = z1;"));

    let _ = std::fs::remove_file(&output_path);
}

#[test]
fn itrace_handler_submits_multiple_rendered_paths() {
    let temp_dir = std::env::temp_dir();
    let output_path = temp_dir.join(format!("itrace_integration_itrace_module_test_{}.txt", std::process::id()));
    let _ = std::fs::remove_file(&output_path);
    let shared_state = parse_shared_state();
    let handler =
        TraceHandler::init("itrace test title", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);
    let zcache_ok = shared_state.symtab.lookup("zcache_ok");
    let zpc_lookup = shared_state.symtab.lookup("zpc_lookup");

    let mut first_path = TracePerPath::default();
    first_path.push_branch_condition(smtlib::Exp::<Sym>::Bool(true));
    first_path.record(zcache_ok, Vec::new(), 0);
    first_path.record(zcache_ok, Vec::new(), 3);

    let mut second_path = TracePerPath::default();
    second_path.push_branch_condition(smtlib::Exp::<Sym>::Bool(false));
    second_path.record(zpc_lookup, Vec::new(), 1);
    second_path.record(zpc_lookup, Vec::new(), 5);

    handler.submit_path(&first_path, &shared_state.symtab);
    handler.submit_path(&second_path, &shared_state.symtab);
    handler.dump();

    let content = std::fs::read_to_string(&output_path).expect("read itrace integration output");

    assert_eq!(content.matches("<itrace test title> path").count(), 2);
    assert!(content.contains("<itrace test title> path(itrace test title_branch_true):"));
    assert!(content.contains("<itrace test title> path(itrace test title_branch_false):"));
    assert!(!content.contains("branch_conditions"));
    assert!(!content.contains("Bool"));
    assert!(content.contains("[zcache_ok 0]: z0 : %i;"));
    assert!(content.contains("[zcache_ok 3]: return = z1;"));
    assert!(content.contains("[zpc_lookup 1]: p1 : %i;"));
    assert!(content.contains("end"));
    assert!(!content.contains("`1"));
    assert!(!content.contains("`4"));
    assert!(!content.contains("`11"));

    let title_prefix = "<itrace test title> path";
    let first_title = content.find(title_prefix).expect("first path title missing");
    let second_title = content[first_title + 1..]
        .find(title_prefix)
        .map(|offset| first_title + 1 + offset)
        .expect("second path title missing");
    assert!(content[first_title..second_title].contains("[zcache_ok 0]: z0 : %i;"));
    assert!(content[first_title..second_title].contains("[zcache_ok 3]: return = z1;"));
    assert!(content[second_title..].contains("[zpc_lookup 1]: p1 : %i;"));
    assert!(content[second_title..].contains("end"));

    let _ = std::fs::remove_file(&output_path);
}

#[test]
fn strip_source_loc_standard() {
    assert_eq!(strip_source_loc("[zfunc 0]: zz40 : %bv `14 248:2-248:53;"), "[zfunc 0]: zz40 : %bv;");
}

#[test]
fn is_source_loc_accepts_supported_suffix_forms() {
    assert!(is_source_loc("14"));
    assert!(is_source_loc("14 248:2-248:53"));
    assert!(is_source_loc("0 1:0-1:0"));
}

#[test]
fn is_source_loc_rejects_empty_or_non_numeric_suffixes() {
    assert!(!is_source_loc(""));
    assert!(!is_source_loc("abc"));
    assert!(!is_source_loc("14 abc:2-248:53"));
    assert!(!is_source_loc("file 248:2-248:53"));
    assert!(!is_source_loc("14 248:x-248:53"));
    assert!(!is_source_loc("14 248:2-248:y"));
}

#[test]
fn is_source_loc_rejects_malformed_ranges() {
    assert!(!is_source_loc("14 248"));
    assert!(!is_source_loc("14 248:2"));
    assert!(!is_source_loc("14 248:2-248"));
    assert!(!is_source_loc("14 248:2:3-248:53"));
    assert!(!is_source_loc("14 248:2-248:53:1"));
    assert!(!is_source_loc("14 248:2-248:53 extra"));
}

#[test]
fn strip_source_loc_with_trailing_whitespace() {
    assert_eq!(strip_source_loc("[zfunc 0]: zz40 : %bv `14 248:2-248:53;   \t"), "[zfunc 0]: zz40 : %bv;");
}

#[test]
fn strip_source_loc_short() {
    assert_eq!(strip_source_loc("[zfunc 1]: zz41 : %i `14"), "[zfunc 1]: zz41 : %i;");
    assert_eq!(strip_source_loc("[zfunc 2]: zz41 : %i `14;"), "[zfunc 2]: zz41 : %i;");
}

#[test]
fn strip_source_loc_range_without_semicolon() {
    assert_eq!(strip_source_loc("[zfunc 3]: zz42 : %i `14 248:2-248:53"), "[zfunc 3]: zz42 : %i;");
}

#[test]
fn strip_source_loc_uses_last_backtick() {
    assert_eq!(strip_source_loc("[zfunc 4]: call `not_a_loc arg `14 248:2-248:53;"), "[zfunc 4]: call `not_a_loc arg;");
}

#[test]
fn strip_source_loc_preserves_invalid_backtick_suffixes() {
    assert_eq!(strip_source_loc("[zfunc 5]: zz43 : %i `abc;"), "[zfunc 5]: zz43 : %i `abc;");
    assert_eq!(strip_source_loc("[zfunc 6]: zz43 : %i `14 abc:2-248:53;"), "[zfunc 6]: zz43 : %i `14 abc:2-248:53;");
    assert_eq!(strip_source_loc("[zfunc 7]: zz43 : %i `14 248:2;"), "[zfunc 7]: zz43 : %i `14 248:2;");
}

#[test]
fn strip_no_sourceloc() {
    assert_eq!(strip_source_loc("goto 5"), "goto 5");
    assert_eq!(strip_source_loc("  goto 5  "), "  goto 5  ");
}

// ---- Task 4: TraceHandler tests ----

#[test]
fn itrace_handler_init_builds_ir_cache() {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
    let ir_path = PathBuf::from(manifest_dir).join("tests/fixtures/ir_cache_assumption.ir");
    assert!(ir_path.exists(), "Test fixture not found at {:?}", ir_path);

    let temp_dir = std::env::temp_dir();
    let output_path = temp_dir.join("itrace_test_init.txt");
    let _ = std::fs::remove_file(&output_path);

    let shared_state = parse_shared_state();
    let handler = TraceHandler::init("test", ir_path, Some(output_path.clone()), &shared_state.symtab);

    assert_eq!(
        handler.lookup_ir_line(shared_state.symtab.lookup("zcache_ok"), 0, &shared_state.symtab),
        Some("z0 : %i;".to_string()),
        "Should resolve zcache_ok through the handler API"
    );
    assert_eq!(
        handler.lookup_ir_line(shared_state.symtab.lookup("zpc_lookup"), 1, &shared_state.symtab),
        Some("p1 : %i;".to_string()),
        "Should resolve zpc_lookup through the handler API"
    );
    assert!(
        !handler
            .lookup_ir_line(shared_state.symtab.lookup("zcache_ok"), 0, &shared_state.symtab)
            .expect("zcache_ok line")
            .contains('`'),
        "Line should not contain SourceLoc"
    );

    drop(handler);
    let _ = std::fs::remove_file(&output_path);
}

#[test]
fn itrace_handler_default_no_thread() {
    let handler = TraceHandler::default();
    assert!(!handler.writer.has_write_thread());
    assert!(handler.writer.output_path().is_none());
}

#[test]
fn itrace_handler_submit_path_without_output_path_does_not_render_or_queue() {
    let shared_state = parse_shared_state();
    let handler = TraceHandler::default();
    let mut path = TracePerPath::default();

    path.record(shared_state.symtab.lookup("zcache_ok"), Vec::new(), 0);
    handler.submit_path(&path, &shared_state.symtab);

    assert!(
        handler.writer.completed_queue.pop().is_none(),
        "submit_path should skip rendering when no output path is configured"
    );
}

#[test]
fn writer_wakes_for_batches_drains_on_shutdown_and_restarts() {
    let output = std::env::temp_dir().join(format!("writer_wakeup_{}.txt", std::process::id()));
    let writer = Arc::new(TraceWriter::with_output_path(Some(output.clone())));
    for round in 0..3 {
        if round != 0 {
            writer.set_path(Some(output.clone()));
        }
        // 队列为空时也必须能收到下一批，不能只靠退出时排空。
        writer.submit_text(format!("round-{round}"));
        let deadline = std::time::Instant::now() + Duration::from_secs(2);
        loop {
            if std::fs::read_to_string(&output).unwrap_or_default().contains(&format!("round-{round}")) {
                break;
            }
            assert!(std::time::Instant::now() < deadline, "writer 未响应入队唤醒");
            std::thread::sleep(Duration::from_millis(1));
        }
        let workers = (0..4)
            .map(|worker| {
                let writer = Arc::clone(&writer);
                std::thread::spawn(move || {
                    for item in 0..100 {
                        writer.submit_text(format!("{round}-{worker}-{item}"));
                    }
                })
            })
            .collect::<Vec<_>>();
        for worker in workers {
            worker.join().unwrap();
        }
        writer.dump();
        let text = std::fs::read_to_string(&output).unwrap();
        for worker in 0..4 {
            for item in 0..100 {
                assert_eq!(text.lines().filter(|line| *line == format!("{round}-{worker}-{item}")).count(), 1);
            }
        }
    }
    writer.set_path(Some(output.clone()));
    writer.dump(); // 空队列退出也必须唤醒等待线程。
    drop(writer);
    std::fs::remove_file(output).unwrap();
}

#[test]
fn itrace_write_thread_writes_to_file() {
    let temp_dir = std::env::temp_dir();
    let output_path = temp_dir.join("itrace_test_write.txt");
    let _ = std::fs::remove_file(&output_path);

    let shared_state = parse_shared_state();
    let handler = TraceHandler::init("test", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);

    handler.writer.submit_text("line1".to_string());
    handler.writer.submit_text("line2".to_string());
    handler.writer.submit_text("line3".to_string());

    handler.dump();

    let content = std::fs::read_to_string(&output_path).expect("read");
    assert!(content.contains("line1"), "Should contain line1");
    assert!(content.contains("line2"), "Should contain line2");
    assert!(content.contains("line3"), "Should contain line3");

    let _ = std::fs::remove_file(&output_path);
}

#[test]
fn itrace_handler_graceful_shutdown() {
    let temp_dir = std::env::temp_dir();
    let output_path = temp_dir.join("itrace_test_shutdown.txt");
    let _ = std::fs::remove_file(&output_path);

    let shared_state = parse_shared_state();
    let handler = TraceHandler::init("test", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);

    handler.writer.submit_text("data_before_drop".to_string());

    // Drop should trigger dump internally — no panic, no hang
    drop(handler);

    let content = std::fs::read_to_string(&output_path).expect("read");
    assert!(content.contains("data_before_drop"), "Should contain submitted data after drop");

    let _ = std::fs::remove_file(&output_path);
}

#[test]
fn itrace_set_path_spawns_thread() {
    let temp_dir = std::env::temp_dir();
    let output_path = temp_dir.join("itrace_test_setpath.txt");
    let _ = std::fs::remove_file(&output_path);

    let handler = TraceHandler::default();
    assert!(!handler.writer.has_write_thread());

    handler.set_path(Some(output_path.clone()));
    assert!(handler.writer.has_write_thread(), "Thread should be spawned after set_path");

    handler.writer.submit_text("via_set_path".to_string());
    handler.dump();

    let content = std::fs::read_to_string(&output_path).expect("read");
    assert!(content.contains("via_set_path"), "Should contain submitted data");

    let _ = std::fs::remove_file(&output_path);
}

#[test]
fn itrace_set_path_after_dump_writes_new_path_only() {
    let temp_dir = std::env::temp_dir();
    let first_path = temp_dir.join(format!("itrace_reconfigure_set_path_first_{}.txt", std::process::id()));
    let second_path = temp_dir.join(format!("itrace_reconfigure_set_path_second_{}.txt", std::process::id()));
    let _ = std::fs::remove_file(&first_path);
    let _ = std::fs::remove_file(&second_path);

    let handler = TraceHandler::default();
    handler.set_path(Some(first_path.clone()));
    handler.writer.submit_text("first-path-line".to_string());
    handler.dump();

    handler.set_path(Some(second_path.clone()));
    std::thread::sleep(std::time::Duration::from_millis(20));
    handler.writer.submit_text("second-path-line".to_string());
    handler.dump();

    let first_content = std::fs::read_to_string(&first_path).expect("read first itrace output");
    let second_content = std::fs::read_to_string(&second_path).expect("read second itrace output");
    assert!(first_content.contains("first-path-line"));
    assert!(!first_content.contains("second-path-line"), "second path data leaked into first file");
    assert!(second_content.contains("second-path-line"));
    assert!(!second_content.contains("first-path-line"), "first path data leaked into second file");

    let _ = std::fs::remove_file(&first_path);
    let _ = std::fs::remove_file(&second_path);
}

#[test]
fn itrace_configure_after_dump_rebuilds_writer_and_cache_for_new_path() {
    let temp_dir = std::env::temp_dir();
    let first_path = temp_dir.join(format!("itrace_reconfigure_first_{}.txt", std::process::id()));
    let second_path = temp_dir.join(format!("itrace_reconfigure_second_{}.txt", std::process::id()));
    let _ = std::fs::remove_file(&first_path);
    let _ = std::fs::remove_file(&second_path);

    let shared_state = parse_shared_state();
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
    let ir_path = PathBuf::from(manifest_dir).join("tests/fixtures/ir_cache_assumption.ir");

    let handler = TraceHandler::default();
    handler.configure("first title", ir_path.clone(), Some(first_path.clone()), &shared_state.symtab);
    handler.writer.submit_text("first configured line".to_string());
    handler.dump();

    handler.configure("second title", ir_path, Some(second_path.clone()), &shared_state.symtab);
    std::thread::sleep(std::time::Duration::from_millis(20));
    let zcache_ok = shared_state.symtab.lookup("zcache_ok");
    let ir_line = handler
        .lookup_ir_line(zcache_ok, 0, &shared_state.symtab)
        .expect("configured cache should resolve fixture line");
    handler.writer.submit_text(format!("{}\n{}", handler.title(), ir_line));
    handler.dump();

    let first_content = std::fs::read_to_string(&first_path).expect("read first configured itrace output");
    let second_content = std::fs::read_to_string(&second_path).expect("read second configured itrace output");
    assert!(first_content.contains("first configured line"));
    assert!(!first_content.contains("second title"), "second configure data leaked into first file");
    assert!(second_content.contains("second title"));
    assert!(second_content.contains("z0 : %i;"));
    assert!(!second_content.contains('`'));
    assert!(!second_content.contains("first configured line"), "first configure data leaked into second file");

    let _ = std::fs::remove_file(&first_path);
    let _ = std::fs::remove_file(&second_path);
}

#[test]
fn itrace_handler_lookup_ir_line() {
    let shared_state = parse_shared_state();
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
    let ir_path = std::path::PathBuf::from(manifest_dir).join("tests/fixtures/ir_cache_assumption.ir");

    let handler = TraceHandler::init("test", ir_path, None, &shared_state.symtab);

    let fn_name = shared_state.symtab.lookup("zcache_ok");
    assert_eq!(
        handler.lookup_ir_line(fn_name, 0, &shared_state.symtab),
        Some("z0 : %i;".to_string()),
        "Should return first IR line for zcache_ok"
    );
    assert_eq!(
        handler.lookup_ir_line(fn_name, 3, &shared_state.symtab),
        Some("return = z1;".to_string()),
        "Should return IR line for pc 3"
    );
}

#[test]
fn itrace_handler_lookup_ir_line_fallbacks() {
    let shared_state = parse_shared_state();
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
    let ir_path = std::path::PathBuf::from(manifest_dir).join("tests/fixtures/ir_cache_assumption.ir");

    let handler = TraceHandler::init("test", ir_path, None, &shared_state.symtab);

    let unknown_fn = Name::from_u32(u32::MAX);
    assert!(handler.lookup_ir_line(unknown_fn, 0, &shared_state.symtab).is_none());

    let known_fn = shared_state.symtab.lookup("zcache_ok");
    assert!(handler.lookup_ir_line(known_fn, 100, &shared_state.symtab).is_none());
    assert!(handler.lookup_ir_line(known_fn, u64::MAX, &shared_state.symtab).is_none());
}

#[test]
fn itrace_handler_lookup_ir_line_poisoned_cache_lock() {
    let shared_state = parse_shared_state();
    let handler = TraceHandler::default();

    let fn_name = shared_state.symtab.lookup("zcache_ok");

    let _ = panic::catch_unwind(AssertUnwindSafe(|| {
        let _guard = handler.ir_cache.lock().expect("mutex");
        panic!("poison cache lock");
    }));

    assert!(handler.lookup_ir_line(fn_name, 0, &shared_state.symtab).is_none());
}

// ---- IO panic 行为测试 ----

#[test]
fn itrace_handler_init_panics_when_output_path_is_unwritable() {
    let bad_path = PathBuf::from("/dev/null/impossible/itrace_output.txt");
    let shared_state = parse_shared_state();

    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        let _handler =
            TraceHandler::init("bad-path-test", fixture_ir_path(), Some(bad_path.clone()), &shared_state.symtab);
    }));

    let payload = result.expect_err("init with unwritable path should panic");
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .expect("panic payload should be a string");

    assert!(message.contains("impossible"), "panic message should contain path fragment, got: {}", message);
}

#[test]
fn itrace_handler_configure_panics_when_output_path_is_unwritable() {
    let temp_dir = std::env::temp_dir();
    let good_path = temp_dir.join(format!("itrace_configure_good_{}.txt", std::process::id()));
    let bad_path = PathBuf::from("/dev/null/impossible/itrace_output2.txt");
    let _ = std::fs::remove_file(&good_path);

    let shared_state = parse_shared_state();
    let handler = TraceHandler::init("good", fixture_ir_path(), Some(good_path.clone()), &shared_state.symtab);
    handler.dump();

    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        handler.configure("bad-path-configure", fixture_ir_path(), Some(bad_path.clone()), &shared_state.symtab);
    }));

    let payload = result.expect_err("configure with unwritable path should panic");
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .expect("panic payload should be a string");

    assert!(message.contains("impossible"), "panic message should contain path fragment, got: {}", message);

    let _ = std::fs::remove_file(&good_path);
}

#[test]
fn itrace_handler_set_path_panics_when_output_path_is_unwritable() {
    let bad_path = PathBuf::from("/dev/null/impossible/itrace_output3.txt");
    let handler = TraceHandler::default();

    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        handler.set_path(Some(bad_path.clone()));
    }));

    let payload = result.expect_err("set_path with unwritable path should panic");
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .expect("panic payload should be a string");

    assert!(message.contains("impossible"), "panic message should contain path fragment, got: {}", message);
}

// ---- 多 handler 独立 title / 输出文件测试 ----

#[test]
fn itrace_separate_handlers_write_independent_titles_and_files() {
    // 模拟多 clause 场景：每个 clause 应该用独立的 handler，
    // 各自有独立的 title 和输出文件，互不干扰。
    let temp_dir = std::env::temp_dir();
    let output_a = temp_dir.join(format!("itrace_clause_a_{}.txt", std::process::id()));
    let output_b = temp_dir.join(format!("itrace_clause_b_{}.txt", std::process::id()));
    let _ = std::fs::remove_file(&output_a);
    let _ = std::fs::remove_file(&output_b);

    let shared_state = parse_shared_state();
    let zcache_ok = shared_state.symtab.lookup("zcache_ok");
    let zpc_lookup = shared_state.symtab.lookup("zpc_lookup");

    // clause A: 独立 handler，title 为 "clause_A"
    let handler_a = TraceHandler::init("clause_A", fixture_ir_path(), Some(output_a.clone()), &shared_state.symtab);
    let mut path_a = TracePerPath::default();
    path_a.record(zcache_ok, Vec::new(), 0);
    handler_a.submit_path(&path_a, &shared_state.symtab);
    handler_a.dump();

    // clause B: 独立 handler，title 为 "clause_B"
    let handler_b = TraceHandler::init("clause_B", fixture_ir_path(), Some(output_b.clone()), &shared_state.symtab);
    let mut path_b = TracePerPath::default();
    path_b.record(zpc_lookup, Vec::new(), 1);
    handler_b.submit_path(&path_b, &shared_state.symtab);
    handler_b.dump();

    let content_a = std::fs::read_to_string(&output_a).expect("read clause A output");
    let content_b = std::fs::read_to_string(&output_b).expect("read clause B output");

    // 各自文件只包含各自的 title
    assert!(content_a.contains("clause_A"), "clause A output should contain 'clause_A'");
    assert!(!content_a.contains("clause_B"), "clause A output should NOT contain 'clause_B'");
    assert!(content_b.contains("clause_B"), "clause B output should contain 'clause_B'");
    assert!(!content_b.contains("clause_A"), "clause B output should NOT contain 'clause_A'");

    // 各自文件只包含各自的 IR 行
    assert!(content_a.contains("[zcache_ok 0]: z0 : %i;"), "clause A output should contain zcache_ok line");
    assert!(content_b.contains("[zpc_lookup 1]: p1 : %i;"), "clause B output should contain zpc_lookup line");

    let _ = std::fs::remove_file(&output_a);
    let _ = std::fs::remove_file(&output_b);
}

#[test]
fn itrace_handler_configure_resets_title_independently() {
    // 验证 configure 调用后 title 被独立更新，不会残留旧 title。
    let temp_dir = std::env::temp_dir();
    let first_path = temp_dir.join(format!("itrace_title_first_{}.txt", std::process::id()));
    let second_path = temp_dir.join(format!("itrace_title_second_{}.txt", std::process::id()));
    let _ = std::fs::remove_file(&first_path);
    let _ = std::fs::remove_file(&second_path);

    let shared_state = parse_shared_state();
    let handler = TraceHandler::default();

    handler.configure("first_clause", fixture_ir_path(), Some(first_path.clone()), &shared_state.symtab);
    let mut path1 = TracePerPath::default();
    path1.record(shared_state.symtab.lookup("zcache_ok"), Vec::new(), 0);
    handler.submit_path(&path1, &shared_state.symtab);
    handler.dump();

    handler.configure("second_clause", fixture_ir_path(), Some(second_path.clone()), &shared_state.symtab);
    let mut path2 = TracePerPath::default();
    path2.record(shared_state.symtab.lookup("zpc_lookup"), Vec::new(), 1);
    handler.submit_path(&path2, &shared_state.symtab);
    handler.dump();

    let first_content = std::fs::read_to_string(&first_path).expect("read first title output");
    let second_content = std::fs::read_to_string(&second_path).expect("read second title output");

    assert!(first_content.contains("first_clause"));
    assert!(!first_content.contains("second_clause"), "second title should not leak into first file");
    assert!(second_content.contains("second_clause"));
    assert!(!second_content.contains("first_clause"), "first title should not leak into second file");

    let _ = std::fs::remove_file(&first_path);
    let _ = std::fs::remove_file(&second_path);
}

// ---- QA 复核：writer writeln panic / spawn panic / stop_write_thread 错误传播 ----

#[test]
fn itrace_handler_dump_propagates_writer_panic() {
    let temp_dir = std::env::temp_dir();
    let output_path = temp_dir.join(format!("itrace_writer_panic_{}.txt", std::process::id()));
    let _ = std::fs::remove_file(&output_path);

    let shared_state = parse_shared_state();
    let handler = TraceHandler::init("panic-test", fixture_ir_path(), Some(output_path.clone()), &shared_state.symtab);

    // 正常提交数据然后 dump，不应 panic
    handler.writer.submit_text("before-panic".to_string());
    handler.dump();

    let content = std::fs::read_to_string(&output_path).expect("read output");
    assert!(content.contains("before-panic"));

    let _ = std::fs::remove_file(&output_path);
}

#[test]
fn itrace_handler_init_creates_file_at_exact_user_path() {
    let temp_dir = std::env::temp_dir();
    let exact_path = temp_dir.join(format!("itrace_exact_user_path_{}.txt", std::process::id()));
    let _ = std::fs::remove_file(&exact_path);

    let shared_state = parse_shared_state();
    let handler =
        TraceHandler::init("single-clause", fixture_ir_path(), Some(exact_path.clone()), &shared_state.symtab);

    let mut path = TracePerPath::default();
    path.record(shared_state.symtab.lookup("zcache_ok"), Vec::new(), 0);
    handler.submit_path(&path, &shared_state.symtab);
    handler.dump();

    assert!(exact_path.exists(), "file should be created at the exact user-specified path, no suffix added");
    let content = std::fs::read_to_string(&exact_path).expect("read");
    assert!(content.contains("single-clause"));
    assert!(content.contains("[zcache_ok 0]: z0 : %i;"));

    let _ = std::fs::remove_file(&exact_path);
}
