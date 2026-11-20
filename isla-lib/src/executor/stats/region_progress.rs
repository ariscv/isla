//! 可关闭的区域步数与真实查询诊断；不参与执行决策。
use crate::bitvector::BV;
use crate::executor::LocalFrame;
use crate::ir::{Instr, Symtab, UVal, Val};
use crate::timeout::SmtOperation;
use serde_json::{json, Value};
use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

#[cfg(test)]
thread_local! {static TEST_ENABLED:Cell<Option<bool>>=const{Cell::new(None)};}
pub(crate) fn enabled() -> bool {
    #[cfg(test)]
    if let Some(value) = TEST_ENABLED.with(Cell::get) {
        return value;
    }
    cfg!(test) || crate::config::RegionOptions::current().progress
}
// 诊断身份独立于执行侧访问作用域，开关诊断不改变执行编号。
static NEXT_INVOCATION: AtomicUsize = AtomicUsize::new(1);
pub(crate) fn fresh_invocation() -> usize {
    NEXT_INVOCATION
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
        .expect("诊断调用编号溢出")
}
static EMITTED: AtomicUsize = AtomicUsize::new(0);
static LIVE_ROWS: AtomicUsize = AtomicUsize::new(0);
thread_local! {
    static DEPTH: Cell<usize> = const { Cell::new(0) };
    static LABEL: Cell<&'static str> = const { Cell::new("unclassified") };
    static ROOT: RefCell<Option<Progress>> = const { RefCell::new(None) };
}
#[derive(Default, serde::Serialize)]
struct Counts {
    steps: u64,
    queries: u64,
    smt_seconds: f64,
}
#[derive(Default, serde::Serialize)]
struct WorkSeconds {
    target_translate: f64,
    buffer_translate: f64,
    query_setup: f64,
    z3_check: f64,
    model_eval: f64,
    profiling: f64,
}
#[derive(Clone, Copy)]
pub(crate) enum WorkKind {
    TargetTranslate,
    BufferTranslate,
    QuerySetup,
    Z3Check,
    ModelEval,
    Profiling,
}
/// 与真实求解阶段配对的只读计时；关闭诊断不读取时钟。
pub(crate) struct WorkTimer {
    started: Option<Instant>,
    kind: WorkKind,
}
impl WorkTimer {
    pub(crate) fn start(kind: WorkKind) -> Self {
        Self { started: enabled().then(Instant::now), kind }
    }
}
impl Drop for WorkTimer {
    fn drop(&mut self) {
        let Some(started) = self.started else { return };
        let seconds = started.elapsed().as_secs_f64();
        ROOT.with(|root| {
            if let Some(p) = root.borrow_mut().as_mut() {
                match self.kind {
                    WorkKind::TargetTranslate => p.work.target_translate += seconds,
                    WorkKind::BufferTranslate => p.work.buffer_translate += seconds,
                    WorkKind::QuerySetup => p.work.query_setup += seconds,
                    WorkKind::Z3Check => p.work.z3_check += seconds,
                    WorkKind::ModelEval => p.work.model_eval += seconds,
                    WorkKind::Profiling => p.work.profiling += seconds,
                }
            }
        });
    }
}
static FOOTPRINT_SAMPLES: AtomicUsize = AtomicUsize::new(0);
pub(crate) fn needs_footprint() -> bool {
    if !enabled() || FOOTPRINT_SAMPLES.load(Ordering::Relaxed) >= 4096 {
        return false;
    }
    // 普通回归不做昂贵的AST普查；生产仍只由同一个 region-progress 配置开关启用。
    #[cfg(test)]
    if !TEST_ENABLED.with(|flag| flag.get() == Some(true)) {
        return false;
    }
    ROOT.with(|root| root.borrow().as_ref().is_some_and(|p| p.footprint_epoch != Some(p.back_edges.len())))
}
pub(crate) fn footprint(mut value: Value) {
    ROOT.with(|root| {
        if let Some(p) = root.borrow_mut().as_mut() {
            FOOTPRINT_SAMPLES.fetch_add(1, Ordering::Relaxed);
            value["query_site"] = json!(p.current);
            value["query_phase"] = json!(query_label());
            value["query_ordinal"] = json!(p.counts.queries + 1);
            value["boundary_ordinal"] = json!(p.back_edges.len());
            p.footprint = Some(value);
            p.footprint_epoch = Some(p.back_edges.len());
        }
    });
}
struct RoundProbe {
    id: usize,
    last: Instant,
    queries: u64,
    smt_seconds: f64,
    round: usize,
}
struct Progress {
    origin: Value,
    outcome: String,
    work: WorkSeconds,
    footprint: Option<Value>,
    footprint_epoch: Option<usize>,
    counts: Counts,
    sites: BTreeMap<String, Counts>,
    phases: BTreeMap<String, Counts>,
    branches: BTreeMap<String, u64>,
    current: String,
    back_edges: Vec<Value>,
    initial: Option<Value>,
    call_instance: Option<usize>,
    exhausted: Option<Value>,
    probe: Option<RoundProbe>,
}
pub(crate) struct AttemptGuard {
    active: bool,
    root: bool,
}
impl AttemptGuard {
    pub(crate) fn start(origin: Value) -> Self {
        if !enabled() {
            return Self { active: false, root: false };
        }
        let root = DEPTH.with(|d| {
            let n = d.get();
            d.set(n + 1);
            n == 0
        });
        if root {
            super::region_cost::reset_boundary();
        }
        if root && (EMITTED.load(Ordering::Relaxed) < 256 || crate::smt::probe_query_timings_enabled()) {
            ROOT.with(|r| {
                *r.borrow_mut() = Some(Progress {
                    origin,
                    outcome: "unfinished".into(),
                    work: WorkSeconds::default(),
                    footprint: None,
                    footprint_epoch: None,
                    counts: Counts::default(),
                    sites: BTreeMap::new(),
                    phases: BTreeMap::new(),
                    branches: BTreeMap::new(),
                    current: "entry".into(),
                    back_edges: Vec::new(),
                    initial: None,
                    call_instance: None,
                    exhausted: None,
                    probe: crate::smt::probe_query_timings_enabled().then(|| {
                        static NEXT_PROBE: AtomicUsize = AtomicUsize::new(1);
                        RoundProbe {
                            id: NEXT_PROBE.fetch_add(1, Ordering::Relaxed),
                            last: Instant::now(),
                            queries: 0,
                            smt_seconds: 0.0,
                            round: 0,
                        }
                    }),
                })
            });
        }
        Self { active: true, root }
    }
    pub(crate) fn finish(&mut self, outcome: &str) {
        if self.root {
            ROOT.with(|r| {
                if let Some(p) = r.borrow_mut().as_mut() {
                    p.outcome = outcome.into()
                }
            });
        }
    }
}
impl Drop for AttemptGuard {
    fn drop(&mut self) {
        if !self.active {
            return;
        }
        DEPTH.with(|d| d.set(d.get().checked_sub(1).expect("诊断尝试栈失衡")));
        if self.root {
            let p = ROOT.with(|r| r.borrow_mut().take());
            if let Some(p) = &p {
                if let Some(probe) = &p.probe {
                    crate::smt::probe_query_event(|| {
                        json!({"type":"attempt_end","attempt":probe.id,
                        "origin":p.origin,"call_instance":p.call_instance,"outcome":p.outcome,
                        "last_completed_round":probe.round,"tail_wall_seconds":probe.last.elapsed().as_secs_f64(),
                        "tail_queries":p.counts.queries-probe.queries,"tail_smt_seconds":p.counts.smt_seconds-probe.smt_seconds})
                    });
                }
            }
            if let Some(p) = p.filter(|p| p.counts.steps >= 256 && !p.back_edges.is_empty()) {
                if EMITTED.fetch_add(1, Ordering::Relaxed) < 256 {
                    let _log = crate::executor::stats::path_account::Scope::enter(
                        crate::executor::stats::path_account::Category::Log,
                    );
                    eprintln!(
                        "{}",
                        json!({"kind":"region_progress","origin":p.origin,"outcome":p.outcome,"counts":p.counts,"work_seconds":p.work,"query_footprint":p.footprint,"sites":p.sites,"query_phases":p.phases,"branch_results":p.branches,"back_edges":p.back_edges,"initial":p.initial,"call_instance":p.call_instance,"exhausted":p.exhausted,"note":"每个根尝试；真实Z3查询不含模型求值；步数含嵌套区域；回边仅记录实际执行前的无条件后跳"})
                    );
                }
            }
        }
    }
}
fn integers<B: BV>(frame: &LocalFrame<B>, symtab: &Symtab) -> Value {
    let mut values = frame
        .local_state
        .vars
        .iter()
        .filter_map(|(n, v)| match v {
            UVal::Init(Val::I64(i)) => Some((crate::zencode::decode(symtab.to_str(*n)), *i)),
            _ => None,
        })
        .collect::<Vec<_>>();
    values.sort_by(|a, b| a.0.cmp(&b.0));
    values.truncate(64);
    json!(values.into_iter().collect::<BTreeMap<_, _>>())
}
pub(crate) fn step<B: BV>(frame: &LocalFrame<B>, symtab: &Symtab, solver: &crate::smt::Solver<B>) {
    let cost_scope =
        crate::executor::stats::region_cost::Scope::enter(crate::executor::stats::region_cost::Category::Diagnostics);
    let _ = &cost_scope;
    if !enabled() || frame.region_execution.is_none() {
        return;
    }
    super::merge_timing::live_step(frame.function_name, frame.pc, symtab);
    ROOT.with(|r| {
        let mut r=r.borrow_mut();let Some(p)=r.as_mut() else{return};
        let function=crate::zencode::decode(symtab.to_str(frame.function_name));
        let mut key=format!("{}@{}",function,frame.pc);
        if p.sites.len()>=512 && !p.sites.contains_key(&key) {key="other".into();}
        p.current=key.clone();if p.call_instance.is_none(){p.call_instance=Some(frame.local_state.call_instance);}p.counts.steps+=1;p.sites.entry(key).or_default().steps+=1;
        if p.initial.is_none() {p.initial=Some(json!({"function":function,"pc":frame.pc,"integers":integers(frame,symtab)}));}
        if let Some(Instr::Goto(target))=frame.instrs.get(frame.pc) {
            if *target<frame.pc && p.back_edges.len()<512 {
                if p.origin["function"].as_str()==Some(function.as_str()) {
                    if let Some(probe) = &mut p.probe {
                        let end = Instant::now();
                        let wall = end.duration_since(probe.last).as_secs_f64();
                        let costs = super::region_cost::snapshot();
                        let snapshot_start = Instant::now();
                        let snapshot = solver.probe_transaction_snapshot();
                        probe.round += 1;
                        crate::smt::probe_query_event(|| json!({"type":"round", "attempt":probe.id,
                            "origin":p.origin,"call_instance":p.call_instance,"round":probe.round,
                            "back_edge_pc":frame.pc,"target":target,"integers":integers(frame,symtab),
                            "deferred":solver.region_queries_deferred(), "wall_seconds":wall, "costs":costs,
                            "queries":p.counts.queries-probe.queries,"smt_seconds":p.counts.smt_seconds-probe.smt_seconds,
                            "transaction":snapshot,"snapshot_seconds":snapshot_start.elapsed().as_secs_f64()}));
                        probe.queries=p.counts.queries;
                        probe.smt_seconds=p.counts.smt_seconds;
                        super::region_cost::reset_boundary();
                        probe.last=Instant::now();
                    }
                }
                let edge=json!({"function":function,"pc":frame.pc,"target":target,"steps":p.counts.steps,"queries":p.counts.queries,"smt_seconds":p.counts.smt_seconds,"work_seconds":p.work,"query_footprint":p.footprint,"query_phases":p.phases,"definition_footprint":solver.region_definition_footprint(),"integers":integers(frame,symtab)});
                if p.origin["function"].as_str()==Some(function.as_str()) && LIVE_ROWS.fetch_add(1,Ordering::Relaxed)<2048 {
                    let _log = crate::executor::stats::path_account::Scope::enter(
                        crate::executor::stats::path_account::Category::Log,
                    );
                    eprintln!("{}",json!({"kind":"region_iteration","origin":p.origin,"call_instance":p.call_instance,"edge":edge}));
                }
                p.back_edges.push(edge);
            }
        }
    });
}
pub(crate) fn exhausted<B: BV>(frame: &LocalFrame<B>, symtab: &Symtab) {
    if !enabled() {
        return;
    }
    ROOT.with(|r|if let Some(p)=r.borrow_mut().as_mut(){p.exhausted=Some(json!({"function":crate::zencode::decode(symtab.to_str(frame.function_name)),"pc":frame.pc,"integers":integers(frame,symtab)}));});
}
pub(crate) fn smt(operation: SmtOperation, wall: Duration) {
    if !enabled() || matches!(operation, SmtOperation::ModelEval) {
        return;
    }
    ROOT.with(|r| {
        let mut r = r.borrow_mut();
        if let Some(p) = r.as_mut() {
            p.counts.queries += 1;
            p.counts.smt_seconds += wall.as_secs_f64();
            let site = p.sites.entry(p.current.clone()).or_default();
            site.queries += 1;
            site.smt_seconds += wall.as_secs_f64();
            let phase = p.phases.entry(query_label().into()).or_default();
            phase.queries += 1;
            phase.smt_seconds += wall.as_secs_f64();
        }
    });
}
pub(crate) fn branch_result(a: bool, b: bool) {
    if enabled() {
        ROOT.with(|r| {
            if let Some(p) = r.borrow_mut().as_mut() {
                *p.branches.entry(format!("{a}/{b}")).or_default() += 1;
            }
        });
    }
}
pub(crate) fn query_label() -> &'static str {
    LABEL.with(Cell::get)
}
pub(crate) struct QueryScope(Option<&'static str>);
impl QueryScope {
    pub(crate) fn enter(label: &'static str) -> Self {
        Self(Some(LABEL.with(|l| l.replace(label))))
    }
    pub(crate) fn fallback(label: &'static str) -> Self {
        if query_label() == "unclassified" {
            Self::enter(label)
        } else {
            Self(None)
        }
    }
}
impl Drop for QueryScope {
    fn drop(&mut self) {
        if let Some(old) = self.0 {
            LABEL.with(|l| l.set(old));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn region_progress_query_scope_restores_outer_classification() {
        assert_eq!(query_label(), "unclassified");
        {
            let branch = QueryScope::enter("branch_feasibility");
            {
                let proof = QueryScope::fallback("boolean_proof");
                assert_eq!(query_label(), "branch_feasibility");
                drop(proof);
            }
            drop(branch);
        }
        assert_eq!(query_label(), "unclassified");
    }
}

pub(crate) fn loop_return<B: BV>(frame: &LocalFrame<B>, symtab: &Symtab) {
    if enabled() && frame.region_execution.is_none() && frame.local_state.loop_attempt_seen {
        let _log =
            crate::executor::stats::path_account::Scope::enter(crate::executor::stats::path_account::Category::Log);
        eprintln!(
            "{}",
            json!({"kind":"loop_call_return","call_instance":frame.local_state.call_instance,"function":crate::zencode::decode(symtab.to_str(frame.function_name)),"integers":integers(frame,symtab)})
        );
    }
}

#[cfg(test)]
#[test]
fn region_progress_disabled_has_no_collection_or_call_id_allocation() {
    let old = TEST_ENABLED.with(|flag| flag.replace(Some(false)));
    let frame = crate::executor::LocalFrame::<crate::bitvector::b64::B64>::new(
        crate::ir::TOP_LEVEL_LET,
        &[],
        &crate::ir::Ty::Unit,
        None,
        &[],
    );
    let state = frame.local_state.clone();
    let before = EMITTED.load(Ordering::Relaxed);
    let scope = QueryScope::enter("disabled");
    let timer = WorkTimer::start(WorkKind::TargetTranslate);
    assert!(timer.started.is_none());
    assert!(!needs_footprint());
    drop(timer);
    assert_eq!(query_label(), "disabled");
    assert_eq!(frame.local_state.call_instance, 0);
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = crate::smt::Context::new(crate::smt::Config::new());
    let solver = crate::smt::Solver::<crate::bitvector::b64::B64>::new(&context);
    step(&frame, &Symtab::new(), &solver);
    smt(SmtOperation::CheckSat, Duration::from_millis(1));
    assert!(std::sync::Arc::ptr_eq(&state, &frame.local_state));
    assert!(ROOT.with(|root| root.borrow().is_none()));
    assert_eq!(EMITTED.load(Ordering::Relaxed), before);
    drop(scope);
    TEST_ENABLED.with(|flag| flag.set(old));
}

/// 由外部指定位置及轮次的单调用有界导出；不改变执行或查询策略。
pub(crate) fn query_dump_point() -> Option<Value> {
    let sites = &crate::config::RegionOptions::current().query_dump_sites;
    if sites.is_empty() {
        return None;
    }
    ROOT.with(|root| {
        let root = root.borrow();
        let p = root.as_ref()?;
        if !sites.contains(&p.current) { return None; }
        let round = p.back_edges.len() + 1;
        if ![2,4,6,8].contains(&round) { return None; }
        static CALL: AtomicUsize = AtomicUsize::new(0);
        let id = p.call_instance?;
        let selected = CALL.compare_exchange(0, id, Ordering::Relaxed, Ordering::Relaxed).unwrap_or_else(|x| x);
        if selected != 0 && selected != id { return None; }
        Some(json!({"round":round,"call_instance":id,"site":p.current,"phase":query_label(),"query_ordinal":p.counts.queries+1,"origin":p.origin}))
    })
}

/// 当前真实查询的只读位置；影子诊断不推进计数或修改分类。
pub(crate) fn query_metadata() -> Option<Value> {
    if !enabled() {
        return None;
    }
    ROOT.with(|root|root.borrow().as_ref().map(|p|json!({"origin":p.origin,"call_instance":p.call_instance,"round":p.back_edges.len()+1,"site":p.current,"phase":query_label(),"ordinal":p.counts.queries+1})))
}

/// 与本线程根区域起止日志使用相同的纯诊断编号；不改执行调用身份。
pub(crate) fn probe_attempt_id() -> Option<usize> {
    ROOT.with(|root| root.borrow().as_ref().and_then(|p| p.probe.as_ref().map(|p| p.id)))
}
