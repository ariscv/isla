//! 显式开启的 Rust 容器内存估算；不查询 Z3，也不代表 RSS。
use crate::executor::{
    frame::{Frame, LocalFrame, LocalState},
    samples::SamplePath,
    RegionMergeRecord,
};
use crate::{
    bitvector::BV,
    ir::{UVal, Val},
    smt::{
        smtlib::{Def, Exp},
        Checkpoint, Event, Solver, Sym,
    },
};
use serde::Serialize;
use serde_json::{json, Value};
use std::{
    cell::Cell,
    collections::{HashMap, HashSet},
    mem::{size_of, size_of_val},
    sync::{
        atomic::{AtomicBool, AtomicUsize, Ordering},
        Mutex, OnceLock,
    },
    time::Instant,
};

static ENABLED: AtomicBool = AtomicBool::new(false);
static EPOCH: AtomicUsize = AtomicUsize::new(1);
static NEXT_ACTIVE: AtomicUsize = AtomicUsize::new(0);
static STATE: OnceLock<Mutex<State>> = OnceLock::new();
thread_local! { static TASK: Cell<Option<(usize, usize)>> = const { Cell::new(None) }; }
#[derive(Default)]
struct State {
    active: HashMap<usize, (usize, Option<(Instant, usize, usize, SolverMemory)>)>,
    queue: Option<(Instant, usize, usize, usize, usize)>,
    resident_seen: HashSet<usize>,
    resident_bytes: usize,
    resident_count: usize,
}
#[derive(Default, Serialize)]
pub struct SolverMemory {
    pub bytes: usize,
    pub layers: Vec<Value>,
    pub model_caches: usize,
}
pub fn configure(enabled: bool) {
    if enabled {
        STATE.get_or_init(|| Mutex::new(State::default()));
    }
    ENABLED.store(enabled, Ordering::Relaxed);
}
#[inline]
pub fn enabled() -> bool {
    ENABLED.load(Ordering::Relaxed)
}
pub struct ActiveTask {
    execution: usize,
    previous: Option<(usize, usize)>,
}
pub fn begin_task(task_id: usize) -> ActiveTask {
    // 普通 fork 沿用逻辑 TaskId；统计必须按执行实例区分，不能改变调度器身份。
    let execution = NEXT_ACTIVE.fetch_add(1, Ordering::Relaxed);
    let previous = TASK.with(|task| task.replace(Some((execution, 0))));
    assert!(STATE.get().unwrap().lock().unwrap().active.insert(execution, (task_id, None)).is_none());
    ActiveTask { execution, previous }
}
impl Drop for ActiveTask {
    fn drop(&mut self) {
        // collector 可以同线程调用 start_single；内层完成后恢复外层采样身份。
        let current = TASK.with(|task| task.replace(self.previous));
        assert_eq!(current.unwrap().0, self.execution);
        STATE.get().unwrap().lock().unwrap().active.remove(&self.execution).unwrap();
    }
}
/// 每个请求周期只遍历一次；长 SMT 期间保留旧样本，输出年龄而不冒充同步全量。
#[inline]
pub fn poll<B: BV>(frame: &LocalFrame<B>, solver: &Solver<B>) {
    if !enabled() {
        return;
    }
    let epoch = EPOCH.load(Ordering::Relaxed);
    let id = TASK.with(|task| match task.get() {
        Some((id, previous)) if previous != epoch => {
            task.set(Some((id, epoch)));
            Some(id)
        }
        _ => None,
    });
    if let Some(id) = id {
        let mut seen = HashSet::new();
        let frame_bytes = local_frame_bytes(frame, &mut seen);
        let checkpoint_bytes = solver.estimated_trace_bytes(&mut seen);
        let tables = solver.memory_stats();
        STATE.get().unwrap().lock().unwrap().active.get_mut(&id).unwrap().1 =
            Some((Instant::now(), frame_bytes, checkpoint_bytes, tables));
    }
}
pub(crate) fn queue_sample<'a, 'ir, 'task, B: BV + 'a>(
    tasks: impl Iterator<Item = &'a crate::executor::Task<'ir, 'task, B>>,
    active: usize,
) where
    'ir: 'a,
    'task: 'a,
{
    let mut seen = HashSet::new();
    let (mut count, mut frames, mut checkpoints) = (0, 0, 0);
    for task in tasks {
        count += 1;
        frames += frame_bytes(&task.frame, &mut seen);
        checkpoints += task.checkpoint.estimated_bytes(&mut seen);
    }
    STATE.get().unwrap().lock().unwrap().queue = Some((Instant::now(), active, count, frames, checkpoints));
}
/// 由保留路径的拥有者在创建/释放该集合时配对清空；地址去重只在集合存活期间有效。
pub fn reset_resident() {
    if !enabled() {
        return;
    }
    let mut state = STATE.get().unwrap().lock().unwrap();
    state.resident_seen.clear();
    state.resident_count = 0;
    state.resident_bytes = 0;
}
pub fn retain<B: BV>(checkpoint: &Checkpoint<B>, path: &SamplePath<B>, records: &[RegionMergeRecord<B>], extra: usize) {
    if !enabled() {
        return;
    }
    let mut state = STATE.get().unwrap().lock().unwrap();
    let bytes =
        checkpoint.estimated_bytes(&mut state.resident_seen) + sample_path_bytes(path) + records_bytes(records) + extra;
    state.resident_bytes += bytes;
    state.resident_count += 1;
}
pub fn snapshot() -> Value {
    let state = STATE.get().unwrap().lock().unwrap();
    let now = Instant::now();
    let mut frame_bytes = 0;
    let mut checkpoint_bytes = 0;
    let mut solver_bytes = 0;
    let mut models = 0;
    let mut samples = Vec::new();
    for (execution, (id, sample)) in &state.active {
        if let Some((at, frames, checkpoints, solver)) = sample {
            frame_bytes += frames;
            checkpoint_bytes += checkpoints;
            solver_bytes += solver.bytes;
            models += solver.model_caches;
            samples.push(json!({"execution":execution,"task":id,"age_seconds":now.duration_since(*at).as_secs_f64(),"savepoint_depth":solver.layers.len()-1,"layers":solver.layers}));
        }
    }
    let queue = state.queue.map(|(at,active,count,frames,checkpoints)| json!({"age_seconds":now.duration_since(at).as_secs_f64(),"active_at_census":active,"tasks":count,"frame_bytes":frames,"checkpoint_bytes":checkpoints}));
    let process = std::fs::read_to_string("/proc/self/status").ok().map(|status| {
        status
            .lines()
            .filter(|line| line.starts_with("VmRSS:") || line.starts_with("VmHWM:"))
            .map(str::to_owned)
            .collect::<Vec<_>>()
    });
    json!({"schema":1,"kind":"memory_stats","queue_coverage":"MultiRuntime only; most recent census with age","active_task_definition":"registered execution scopes including suspended collector parents","active_tasks":state.active.len(),"sampled_active_tasks":samples.len(),"active_frame_bytes_logical":frame_bytes,"active_checkpoint_bytes_logical":checkpoint_bytes,"active_solver_container_bytes":solver_bytes,"model_cache_references":models,"active_samples":samples,"queue":queue,"resident_paths":state.resident_count,"resident_bytes":state.resident_bytes,"process":process,"estimate":"capacity_payload; shared Arc nodes deduplicated within queue/resident census; active tasks and categories may overlap; do not sum as RSS","excluded":["Z3 opaque solver/AST/model storage","allocator/hash-table control and slack beyond reported capacity","Arc headers","call-stack closures and captured frames","custom memory callbacks/regions","IR/shared global state","trace-tool records","region work-stack frames","uninitialized type storage","nested SMT array type boxes","frame function assumptions/pc counts/interrupts/expression retry/speculation logs","solver enum/name/performance caches","non-SMT Assume event expression payload","queued fork-condition payload"]})
}
pub fn print() {
    if !enabled() {
        return;
    }
    EPOCH.fetch_add(1, Ordering::Relaxed);
    eprintln!("[MEMORY_STATS] {}", snapshot());
}

/// HashMap 的 capacity 只估算可装载 payload，不冒充实际 bucket/control 分配。
pub fn map_bytes<K, V>(capacity: usize) -> usize {
    capacity * size_of::<(K, V)>()
}
pub fn value_heap_bytes<B: BV>(value: &Val<B>) -> usize {
    match value {
        Val::String(s) => s.capacity(),
        Val::MixedBits(v) => v.capacity() * size_of::<crate::ir::BitsSegment<B>>(),
        Val::Vector(v) | Val::List(v) => {
            v.capacity() * size_of::<Val<B>>() + v.iter().map(value_heap_bytes).sum::<usize>()
        }
        Val::Struct(v) | Val::SymbolicCtor(_, v) => {
            map_bytes::<crate::ir::Name, Val<B>>(v.capacity()) + v.values().map(value_heap_bytes).sum::<usize>()
        }
        Val::Ctor(_, v) => size_of::<Val<B>>() + value_heap_bytes(v),
        _ => 0,
    }
}
pub fn exp_heap_bytes<V>(exp: &Exp<V>) -> usize {
    exp_stats(exp).1
}

/// 只读统计原始表达式树节点数与堆载荷；不克隆表达式、不翻译SMT。
pub fn exp_stats<V>(exp: &Exp<V>) -> (usize, usize) {
    use Exp::*;
    // SMT 表达式可呈长链；诊断遍历不用宿主调用栈。
    let mut pending = vec![exp];
    let mut bytes = 0;
    let mut nodes = 0;
    while let Some(exp) = pending.pop() {
        nodes += 1;
        bytes += size_of::<Exp<V>>();
        match exp {
            Bits(v) => bytes += v.capacity(),
            Not(a) | Bvnot(a) | Bvneg(a) | Extract(_, _, a) | ZeroExtend(_, a) | SignExtend(_, a) | FPUnary(_, a) => {
                pending.push(a)
            }
            Eq(a, b)
            | Neq(a, b)
            | And(a, b)
            | Or(a, b)
            | Bvand(a, b)
            | Bvor(a, b)
            | Bvxor(a, b)
            | Bvnand(a, b)
            | Bvnor(a, b)
            | Bvxnor(a, b)
            | Bvadd(a, b)
            | Bvsub(a, b)
            | Bvmul(a, b)
            | Bvudiv(a, b)
            | Bvsdiv(a, b)
            | Bvurem(a, b)
            | Bvsrem(a, b)
            | Bvsmod(a, b)
            | Bvult(a, b)
            | Bvslt(a, b)
            | Bvule(a, b)
            | Bvsle(a, b)
            | Bvuge(a, b)
            | Bvsge(a, b)
            | Bvugt(a, b)
            | Bvsgt(a, b)
            | Bvshl(a, b)
            | Bvlshr(a, b)
            | Bvashr(a, b)
            | Concat(a, b)
            | Select(a, b)
            | FPBinary(_, a, b)
            | FPRoundingUnary(_, a, b) => {
                pending.push(a);
                pending.push(b);
            }
            Ite(a, b, c) | Store(a, b, c) | FPRoundingBinary(_, a, b, c) => {
                pending.push(a);
                pending.push(b);
                pending.push(c);
            }
            FPfma(a, b, c, d) => {
                pending.push(a);
                pending.push(b);
                pending.push(c);
                pending.push(d);
            }
            App(_, args) | Distinct(args) => {
                bytes += (args.capacity() - args.len()) * size_of::<Exp<V>>();
                pending.extend(args);
            }
            Var(_) | Bits64(_) | Enum(_) | Bool(_) | FPConstant(..) | FPRoundingMode(_) => (),
        }
    }
    (nodes, bytes - size_of::<Exp<V>>())
}
pub fn event_heap_bytes<B: BV>(event: &Event<B>) -> usize {
    use Event::*;
    match event {
        Smt(Def::DefineConst(_, exp) | Def::Assert(exp), _, _) => exp_heap_bytes(exp),
        Smt(Def::DeclareFun(_, args, _), _, _) => args.capacity() * size_of::<crate::smt::smtlib::Ty>(),
        ReadReg(_, a, v) | WriteReg(_, a, v) | AssumeReg(_, a, v) => {
            a.capacity() * size_of::<crate::smt::Accessor>() + value_heap_bytes(v)
        }
        Abstract { args, return_value, .. }
        | AssumeFun { args, return_value, .. }
        | UseFunAssumption { args, return_value, .. } => {
            args.capacity() * size_of::<Val<B>>()
                + args.iter().map(value_heap_bytes).sum::<usize>()
                + value_heap_bytes(return_value)
        }
        ReadMem { value, read_kind, address, tag_value, .. } => {
            value_heap_bytes(value)
                + value_heap_bytes(read_kind)
                + value_heap_bytes(address)
                + tag_value.as_ref().map_or(0, value_heap_bytes)
        }
        WriteMem { write_kind, address, data, tag_value, .. } => {
            value_heap_bytes(write_kind)
                + value_heap_bytes(address)
                + value_heap_bytes(data)
                + tag_value.as_ref().map_or(0, value_heap_bytes)
        }
        MarkReg { regs, mark } => regs.capacity() * size_of::<crate::ir::Name>() + mark.capacity(),
        AddressAnnounce { address } | Branch { address } | Instr(address) => value_heap_bytes(address),
        _ => 0,
    }
}
/// 逻辑载荷字节：共享载荷仍按每个逻辑出现计算，不能当作物理堆或 RSS。
pub fn records_bytes<'a, B: BV + 'a>(records: impl IntoIterator<Item = &'a RegionMergeRecord<B>>) -> usize {
    records
        .into_iter()
        .map(|r| {
            size_of::<RegionMergeRecord<B>>()
                + r.value_symbols.capacity() * size_of::<Sym>()
                + r.input_symbols.capacity() * size_of::<Sym>()
                + r.single_arm_reads.len() * size_of::<crate::executor::GuardedRegisterRead<B>>()
                + r.single_arm_reads
                    .iter()
                    .map(|read| {
                        read.accessor.capacity() * size_of::<crate::smt::Accessor>()
                            + value_heap_bytes(&read.value)
                            + exp_heap_bytes(&read.guard)
                    })
                    .sum::<usize>()
                + r.memory_reads.len() * size_of::<(usize, Exp<Sym>, Event<B>)>()
                + r.memory_reads
                    .iter()
                    .map(|(_, guard, event)| exp_heap_bytes(guard) + event_heap_bytes(event))
                    .sum::<usize>()
        })
        .sum::<usize>()
}
fn sample_path_bytes<B: BV>(path: &SamplePath<B>) -> usize {
    size_of_val(path)
        + path
            .pre
            .iter()
            .chain(path.post.iter())
            .map(|(name, value)| size_of_val(name) + name.capacity() + size_of_val(value) + value_heap_bytes(value))
            .sum::<usize>()
        + value_heap_bytes(&path.result)
        + path.memory.capacity() * size_of::<Event<B>>()
        + path.memory.iter().map(event_heap_bytes).sum::<usize>()
        + path.memory_guards.values().map(|g| size_of::<(usize, Exp<Sym>)>() + exp_heap_bytes(g)).sum::<usize>()
}
fn bindings_bytes<B: BV>(bindings: &crate::ir::Bindings<B>) -> usize {
    map_bytes::<crate::ir::Name, UVal<B>>(bindings.capacity())
        + bindings
            .values()
            .map(|v| match v {
                UVal::Init(value) => value_heap_bytes(value),
                _ => 0,
            })
            .sum::<usize>()
}
fn state_bytes<B: BV>(state: &LocalState<B>) -> usize {
    size_of_val(state)
        + bindings_bytes(&state.vars)
        + bindings_bytes(&state.lets)
        + state.regs.estimated_bytes()
        + state.pure_definitions.capacity() * size_of::<(u32, u32)>()
        + map_bytes::<usize, Val<B>>(state.expression_values.capacity())
        + state.expression_values.values().map(value_heap_bytes).sum::<usize>()
}
// 同一份 census 内共享状态去重；活动线程的独立样本不能跨时间去重。
fn shared_bytes<B: BV>(
    state: &std::sync::Arc<LocalState<B>>,
    stack: &std::sync::Arc<Vec<crate::ir::Bindings<B>>>,
    seen: &mut HashSet<usize>,
) -> usize {
    let mut bytes = 0;
    if seen.insert(std::sync::Arc::as_ptr(state) as usize) {
        bytes += state_bytes(state);
    }
    if seen.insert(std::sync::Arc::as_ptr(stack) as usize) {
        bytes += size_of_val(stack.as_ref())
            + stack.capacity() * size_of::<crate::ir::Bindings<B>>()
            + stack.iter().map(bindings_bytes).sum::<usize>();
    }
    bytes
}
fn frame_bytes<B: BV>(frame: &Frame<B>, seen: &mut HashSet<usize>) -> usize {
    size_of_val(frame)
        + shared_bytes(&frame.local_state, &frame.stack_vars, seen)
        + records_bytes(&frame.region_merge_records)
        + if seen.insert(std::sync::Arc::as_ptr(&frame.memory) as usize) {
            frame.memory.estimated_bytes(seen)
        } else {
            0
        }
        + if seen.insert(std::sync::Arc::as_ptr(&frame.backtrace) as usize) {
            frame.backtrace.capacity() * size_of::<(crate::ir::Name, usize)>()
        } else {
            0
        }
}
fn local_frame_bytes<B: BV>(frame: &LocalFrame<B>, seen: &mut HashSet<usize>) -> usize {
    size_of_val(frame)
        + shared_bytes(&frame.local_state, &frame.stack_vars, seen)
        + records_bytes(&frame.region_merge_records)
        + if seen.insert(std::sync::Arc::as_ptr(&frame.memory) as usize) {
            frame.memory.estimated_bytes(seen)
        } else {
            0
        }
        + if seen.insert(std::sync::Arc::as_ptr(&frame.backtrace) as usize) {
            frame.backtrace.capacity() * size_of::<(crate::ir::Name, usize)>()
        } else {
            0
        }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        bitvector::b64::B64,
        smt::{self, Config, Context, Event, Solver},
    };
    #[test]
    fn memory_stats_checkpoint_sharing_is_counted_once() {
        smt::configure_tastic(smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        solver.add_event(Event::Cycle);
        let first = smt::checkpoint(&mut solver);
        let mut seen = std::collections::HashSet::new();
        let bytes = first.estimated_bytes(&mut seen);
        assert!(bytes > std::mem::size_of_val(&first));
        assert_eq!(first.clone().estimated_bytes(&mut seen), std::mem::size_of_val(&first));
        solver.add_event(Event::Cycle);
        let second = smt::checkpoint(&mut solver);
        let delta = second.estimated_bytes(&mut seen);
        assert!(delta > std::mem::size_of_val(&second));
        assert!(delta <= bytes);
    }
    #[test]
    fn memory_stats_nested_values_include_capacity() {
        let value = crate::ir::Val::<B64>::Vector(vec![crate::ir::Val::String(String::with_capacity(100))]);
        assert!(value_heap_bytes(&value) >= 100 + std::mem::size_of::<crate::ir::Val<B64>>());
    }
    #[test]
    fn memory_stats_savepoints_report_each_layer_without_queries() {
        smt::configure_tastic(smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        solver.fresh();
        let a = solver.start_transaction();
        solver.fresh();
        let b = solver.start_transaction();
        let queries = smt::test_query_count();
        let sample = solver.memory_stats();
        assert_eq!(sample.layers.len(), 3);
        assert_eq!(queries, smt::test_query_count());
        assert!(sample.bytes > 0);
        solver.rollback_transaction(b);
        solver.rollback_transaction(a);
    }
    #[test]
    fn memory_stats_snapshot_child() {
        let Ok(mode) = std::env::var("MEMORY_STATS_CHILD") else {
            return;
        };
        configure(mode == "on");
        let stats = std::sync::Arc::new(super::super::ExecutionStats::new(false));
        let reporter =
            super::super::merge_diagnostics::SnapshotReporter::start(stats, std::time::Duration::from_millis(20));
        if mode == "off" {
            assert!(STATE.get().is_none(), "默认关闭不得分配统计状态");
            drop(reporter);
            return;
        }
        let active = begin_task(42);
        let missing = begin_task_for_test(43);
        let execution = TASK.with(|task| task.get().unwrap().0);
        STATE.get().unwrap().lock().unwrap().active.get_mut(&execution).unwrap().1 = Some((
            Instant::now(),
            10,
            20,
            SolverMemory { bytes: 30, layers: vec![json!({"layer":0})], model_caches: 1 },
        ));
        let frame = LocalFrame::<B64>::new(crate::ir::RETURN, &[], &crate::ir::Ty::Unit, None, &[]);
        let task_state = crate::executor::TaskState::new();
        let task = frame.task_with_checkpoint(crate::executor::TaskId::fresh(), &task_state, Checkpoint::new());
        let tasks = vec![task];
        queue_sample(tasks.iter(), 2);
        let start = snapshot();
        assert_eq!(start["active_tasks"], 2);
        assert_eq!(start["sampled_active_tasks"], 1);
        assert_eq!(start["queue"]["tasks"], 1);
        assert!(start["queue"]["frame_bytes"].as_u64().unwrap() > size_of::<Frame<B64>>() as u64);
        std::thread::sleep(std::time::Duration::from_millis(70));
        let old = snapshot();
        assert!(old["active_samples"][0]["age_seconds"].as_f64().unwrap() >= 0.06);
        STATE.get().unwrap().lock().unwrap().active.remove(&missing).unwrap();
        drop(active);
        assert_eq!(snapshot()["active_tasks"], 0);
        drop(reporter);
    }
    fn begin_task_for_test(id: usize) -> usize {
        let execution = NEXT_ACTIVE.fetch_add(1, Ordering::Relaxed);
        STATE.get().unwrap().lock().unwrap().active.insert(execution, (id, None));
        execution
    }
    #[test]
    fn memory_stats_independent_flag_periodic_and_off() {
        for mode in ["on", "off"] {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["memory_stats_snapshot_child", "--nocapture", "--test-threads=1"])
                .env("MEMORY_STATS_CHILD", mode)
                .env_remove("ISLA_STATS")
                .output()
                .unwrap();
            assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stdout));
            let text = String::from_utf8(output.stderr).unwrap();
            if mode == "off" {
                assert!(text.is_empty(), "关闭时不得输出：{text}");
            } else {
                let rows: Vec<Value> = text
                    .lines()
                    .filter_map(|line| line.strip_prefix("[MEMORY_STATS] "))
                    .map(|line| serde_json::from_str(line).unwrap())
                    .collect();
                assert!(rows.len() >= 2, "独立 flag 周期输出缺失：{text}");
                assert!(rows.iter().any(|row| row["active_tasks"] == 2 && row["sampled_active_tasks"] == 1));
                assert_eq!(rows.last().unwrap()["active_tasks"], 0);
            }
        }
    }
    #[test]
    fn memory_stats_same_task_id_child() {
        if std::env::var_os("MEMORY_STATS_SAME_TASK_CHILD").is_none() {
            return;
        }
        configure(true);
        let parent = begin_task(7);
        let child = std::thread::spawn(|| {
            let active = begin_task(7);
            assert_eq!(snapshot()["active_tasks"], 2);
            drop(active);
        })
        .join();
        // 红阶段第二线程会在旧的统计锁内 panic，避免清理再 panic 掩盖原失败。
        if child.is_err() {
            std::mem::forget(parent);
        } else {
            drop(parent);
        }
        assert!(child.is_ok(), "同一逻辑 TaskId 的执行实例必须能并发登记");
        assert_eq!(snapshot()["active_tasks"], 0);
    }
    #[test]
    fn memory_stats_same_task_id_concurrent_registration() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["memory_stats_same_task_id_child", "--nocapture", "--test-threads=1"])
            .env("MEMORY_STATS_SAME_TASK_CHILD", "1")
            .output()
            .unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    }

    #[test]
    fn memory_stats_nested_task_child() {
        if std::env::var_os("MEMORY_STATS_NESTED_TASK_CHILD").is_none() {
            return;
        }
        configure(true);
        // 红阶段 begin_task 会先覆盖 TLS 再 panic，隔离原故障而不触发二次清理 panic。
        let outer = std::mem::ManuallyDrop::new(begin_task(7));
        let old = TASK.with(Cell::get);
        let nested = begin_task(7);
        assert_eq!(snapshot()["active_tasks"], 2);
        drop(nested);
        assert_eq!(TASK.with(Cell::get), old, "内层退出必须恢复外层采样身份");
        assert_eq!(snapshot()["active_tasks"], 1);
        drop(std::mem::ManuallyDrop::into_inner(outer));
        assert_eq!(snapshot()["active_tasks"], 0);
    }
    #[test]
    fn memory_stats_nested_collector_registration() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["memory_stats_nested_task_child", "--nocapture", "--test-threads=1"])
            .env("MEMORY_STATS_NESTED_TASK_CHILD", "1")
            .output()
            .unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    }
}
