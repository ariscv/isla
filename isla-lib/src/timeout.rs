use std::collections::BTreeMap;
use std::fmt;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use crate::source_loc::SourceLoc;

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct PathTimeSnapshot {
    pub active_wall: Duration,
    pub executor_cpu: Duration,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SmtOperation {
    CheckSat,
    CheckSatAssuming,
    ModelEval,
}

/// 一条路径上最慢的那次受保护 Z3 调用。
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SlowestSmtCall {
    pub operation: SmtOperation,
    pub source_loc: SourceLoc,
    pub wall: Duration,
}

/// 同一个调用点（Sail 源码位置）上的求解次数与累计耗时。
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SmtCallSite {
    pub source_loc: SourceLoc,
    pub calls: u64,
    pub wall: Duration,
}

/// 一条路径上所有受保护 Z3 调用的耗时汇总。
///
/// 用来回答"路径预算是被谁吃掉的"：是大量正常求解累积的，还是少数调用打满了单次
/// deadline（`--smt-timeout`）。被中断的调用同样计入 `calls` 与 `wall`，另外单独统计。
/// `sites` 按调用点聚合，用来判断求解次数是集中在少数几行（循环体反复求解）还是摊开的。
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SmtCallStats {
    pub calls: u64,
    pub wall: Duration,
    pub slowest: Option<SlowestSmtCall>,
    pub timeouts: u64,
    pub timeout_wall: Duration,
    sites: Vec<SmtCallSite>,
}

impl SmtCallStats {
    /// `Default` 的 const 版本，供线程局部统计初始化使用。
    pub const fn empty() -> Self {
        SmtCallStats {
            calls: 0,
            wall: Duration::ZERO,
            slowest: None,
            timeouts: 0,
            timeout_wall: Duration::ZERO,
            sites: Vec::new(),
        }
    }

    pub fn record(&mut self, operation: SmtOperation, source_loc: SourceLoc, wall: Duration, timed_out: bool) {
        self.calls += 1;
        self.wall = self.wall.saturating_add(wall);
        if self.slowest.map_or(true, |slowest| wall > slowest.wall) {
            self.slowest = Some(SlowestSmtCall { operation, source_loc, wall });
        }
        if timed_out {
            self.timeouts += 1;
            self.timeout_wall = self.timeout_wall.saturating_add(wall);
        }
        // 调用点数量是 IR 里的静态位置数（几十个量级），线性查找比哈希更省。
        match self.sites.iter_mut().find(|site| site.source_loc == source_loc) {
            Some(site) => {
                site.calls += 1;
                site.wall = site.wall.saturating_add(wall);
            }
            None => self.sites.push(SmtCallSite { source_loc, calls: 1, wall }),
        }
    }

    pub fn max_wall(&self) -> Duration {
        self.slowest.map_or(Duration::ZERO, |slowest| slowest.wall)
    }

    /// 不同调用点的个数。
    pub fn distinct_sites(&self) -> usize {
        self.sites.len()
    }

    /// 求解次数最多的前 `count` 个调用点；次数集中在少数几行说明是循环体在反复求解。
    pub fn hottest_sites(&self, count: usize) -> Vec<SmtCallSite> {
        let mut sites = self.sites.clone();
        sites.sort_by(|left, right| right.calls.cmp(&left.calls).then(right.wall.cmp(&left.wall)));
        sites.truncate(count);
        sites
    }
}

/// 单条路径撞上 `--timeout` 预算时的原因判定。
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum PathTimeoutCause {
    /// 少数 SMT 调用打满单次 deadline，这些调用本身就吃掉了路径预算的一半以上。
    /// 这种情况放宽路径预算没用，要么放宽 `--smt-timeout`，要么让约束更好解。
    SmtOperationTimeouts,
    /// 没有（或很少）调用被中断，时间是被正常求解累积掉的：路径确实需要更多预算。
    SlowSmtSolving,
    /// 时间主要不在 SMT 上，瓶颈在 executor 解释执行本身。
    ExecutorWork,
}

/// 路径预算耗尽时的诊断：SMT 用时构成 + 原因判定。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathTimeoutDiagnostic {
    pub limit: Duration,
    pub timing: PathTimeSnapshot,
    pub smt: SmtCallStats,
    /// 单次 SMT operation 的 deadline（`--smt-timeout`）；未配置时为 `None`。
    pub smt_operation_limit: Option<Duration>,
    /// 这条路径累计执行的控制流步数（jump/goto/call）。死循环会让它无上界地增长，
    /// 而 Sail 里 trip count 具体的 `foreach` 只会给出与 num_elem 成比例的数量级。
    pub control_flow_steps: u32,
    /// 撞上预算时停在哪条 IR 指令上，形如 `execute:1234`。
    pub position: String,
}

/// 报告里列出的最热调用点个数。
const HOTTEST_SITE_COUNT: usize = 3;

/// 被中断的调用占到路径预算这个比例时，判定为"少数操作超时吃掉了预算"。
const SMT_TIMEOUT_SHARE_OF_BUDGET: f64 = 0.5;
/// SMT 累计耗时占到 active_wall 这个比例时，判定瓶颈在求解而不是解释执行。
const SMT_SHARE_OF_ACTIVE_WALL: f64 = 0.7;

impl PathTimeoutDiagnostic {
    pub fn cause(&self) -> PathTimeoutCause {
        if self.smt.timeouts > 0 && share(self.smt.timeout_wall, self.limit) >= SMT_TIMEOUT_SHARE_OF_BUDGET {
            PathTimeoutCause::SmtOperationTimeouts
        } else if share(self.smt.wall, self.timing.active_wall) >= SMT_SHARE_OF_ACTIVE_WALL {
            PathTimeoutCause::SlowSmtSolving
        } else {
            PathTimeoutCause::ExecutorWork
        }
    }

    /// 面向日志的多行诊断；每行都带具体数字，便于判断结论是否可信。
    pub fn report_lines(&self, files: &[&str]) -> Vec<String> {
        let mut lines = vec![format!(
            "路径超时: 预算 {}, active_wall {}, executor_cpu {}, 控制流步数 {}, 停在 {}",
            seconds(self.limit),
            seconds(self.timing.active_wall),
            seconds(self.timing.executor_cpu),
            self.control_flow_steps,
            self.position,
        )];

        match self.smt.slowest {
            Some(slowest) => lines.push(format!(
                "  SMT 调用 {} 次, 累计 {} (占 active_wall {}), 最慢单次 {} [{:?} @ {}]",
                self.smt.calls,
                seconds(self.smt.wall),
                percent(self.smt.wall, self.timing.active_wall),
                seconds(slowest.wall),
                slowest.operation,
                slowest.source_loc.location_string(files),
            )),
            None => lines.push("  SMT 调用 0 次".to_string()),
        }

        let hottest = self.smt.hottest_sites(HOTTEST_SITE_COUNT);
        if !hottest.is_empty() {
            lines.push(format!(
                "  最热调用点({} 个不同位置): {}",
                self.smt.distinct_sites(),
                hottest
                    .iter()
                    .map(|site| format!(
                        "{} 次/{} @ {}",
                        site.calls,
                        seconds(site.wall),
                        site.source_loc.location_string(files)
                    ))
                    .collect::<Vec<_>>()
                    .join("; ")
            ));
        }

        if self.smt.timeouts > 0 {
            lines.push(format!(
                "  其中被单次上限{}中断 {} 次, 累计 {} (占预算 {})",
                match self.smt_operation_limit {
                    Some(limit) => format!("({})", seconds(limit)),
                    None => String::new(),
                },
                self.smt.timeouts,
                seconds(self.smt.timeout_wall),
                percent(self.smt.timeout_wall, self.limit),
            ));
        }

        lines.push(format!(
            "  判定: {}",
            match self.cause() {
                PathTimeoutCause::SmtOperationTimeouts =>
                    "少数 SMT 操作打满单次上限吃掉了路径预算；放宽 --timeout 无效，应调整 --smt-timeout 或简化约束",
                PathTimeoutCause::SlowSmtSolving =>
                    "没有操作被单次上限中断，时间由正常求解累积而成：确实需要更多路径预算",
                PathTimeoutCause::ExecutorWork => "时间主要不在 SMT 上，瓶颈在 executor 解释执行",
            }
        ));

        lines
    }
}

fn share(part: Duration, whole: Duration) -> f64 {
    if whole.is_zero() {
        0.0
    } else {
        part.as_secs_f64() / whole.as_secs_f64()
    }
}

fn percent(part: Duration, whole: Duration) -> String {
    format!("{:.1}%", share(part, whole) * 100.0)
}

fn seconds(duration: Duration) -> String {
    format!("{:.1}s", duration.as_secs_f64())
}

/// Dump 时使用的 SMT symbol 名称快照。
#[derive(Clone, Debug, Default)]
pub struct SmtDumpNames {
    symbol_names: BTreeMap<u32, String>,
    ir_names: BTreeMap<u32, String>,
    enum_members: BTreeMap<u32, Vec<String>>,
}

impl SmtDumpNames {
    pub(crate) fn insert_ir_name(&mut self, name_id: u32, name: String) {
        self.ir_names.insert(name_id, name);
    }

    pub(crate) fn insert_enum_members(&mut self, enum_id: u32, members: Vec<String>) {
        self.enum_members.insert(enum_id, members);
    }

    pub(crate) fn bind_symbol_to_ir_name(&mut self, symbol_id: u32, name_id: u32) {
        let name = self.ir_names.get(&name_id).expect("SMT dump symbol references an unknown IR name");
        let candidate = format!("isla_{}__s{}", name, symbol_id);
        match self.symbol_names.get_mut(&symbol_id) {
            Some(existing) if candidate < *existing => *existing = candidate,
            Some(_) => (),
            None => {
                self.symbol_names.insert(symbol_id, candidate);
            }
        }
    }

    pub(crate) fn symbol_name(&self, symbol_id: u32) -> String {
        self.symbol_names.get(&symbol_id).cloned().unwrap_or_else(|| format!("isla_s{}", symbol_id))
    }

    pub(crate) fn enum_sort_name(&self, enum_id: u32) -> String {
        self.ir_names
            .get(&enum_id)
            .map(|name| format!("isla_{}__n{}", name, enum_id))
            .unwrap_or_else(|| format!("isla_s{}", enum_id))
    }

    pub(crate) fn enum_member_name(&self, enum_id: u32, member: usize, generated_symbol_id: u32) -> String {
        self.enum_members
            .get(&enum_id)
            .and_then(|members| members.get(member))
            .map(|name| format!("isla_{}__e{}_m{}", name, enum_id, member))
            .unwrap_or_else(|| format!("isla_s{}", generated_symbol_id))
    }

    fn merge(&mut self, other: Self) {
        for (name_id, name) in other.ir_names {
            self.ir_names.entry(name_id).or_insert(name);
        }
        for (enum_id, members) in other.enum_members {
            self.enum_members.entry(enum_id).or_insert(members);
        }
        for (symbol_id, name) in other.symbol_names {
            match self.symbol_names.get_mut(&symbol_id) {
                Some(existing) if name < *existing => *existing = name,
                Some(_) => (),
                None => {
                    self.symbol_names.insert(symbol_id, name);
                }
            }
        }
    }
}

pub trait SmtDumpSource: Send + Sync {
    fn materialize(&self) -> Result<String, String>;

    fn materialize_with_names(&self, _names: &SmtDumpNames) -> Result<String, String> {
        self.materialize()
    }
}

pub struct TimeoutSmtDump {
    source: Arc<dyn SmtDumpSource>,
    names: Mutex<SmtDumpNames>,
    materialized: Mutex<Option<Result<Arc<str>, Arc<str>>>>,
}

impl TimeoutSmtDump {
    pub fn new(source: Arc<dyn SmtDumpSource>) -> Self {
        TimeoutSmtDump { source, names: Mutex::new(SmtDumpNames::default()), materialized: Mutex::new(None) }
    }

    pub(crate) fn configure_names(&self, names: SmtDumpNames) {
        let materialized = self.materialized.lock().expect("timeout SMT dump cache poisoned");
        assert!(materialized.is_none(), "SMT dump names were configured after materialization");
        self.names.lock().expect("timeout SMT dump names poisoned").merge(names);
    }

    pub fn materialize(&self) -> Result<Arc<str>, Arc<str>> {
        let mut materialized = self.materialized.lock().expect("timeout SMT dump cache poisoned");
        if let Some(result) = materialized.as_ref() {
            return result.clone();
        }

        let names = self.names.lock().expect("timeout SMT dump names poisoned").clone();
        let result = self.source.materialize_with_names(&names).map(Arc::<str>::from).map_err(Arc::<str>::from);
        *materialized = Some(result.clone());
        result
    }

    pub fn is_materialized(&self) -> bool {
        self.materialized.lock().expect("timeout SMT dump cache poisoned").is_some()
    }
}

impl fmt::Debug for TimeoutSmtDump {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TimeoutSmtDump").field("materialized", &self.is_materialized()).finish()
    }
}

#[derive(Debug)]
pub struct SmtTimeout {
    pub source_loc: SourceLoc,
    pub operation: SmtOperation,
    pub limit: Duration,
    pub operation_wall: Duration,
    pub dump: Arc<TimeoutSmtDump>,
}

impl SmtTimeout {
    pub fn source_loc(&self) -> SourceLoc {
        self.source_loc
    }
}

#[derive(Clone, Debug)]
pub enum TimeoutDiagnostic {
    Smt(Arc<SmtTimeout>),
}

impl TimeoutDiagnostic {
    pub fn metadata_lines(&self) -> Vec<String> {
        let TimeoutDiagnostic::Smt(timeout) = self;
        let lines = vec![
            "timeout_kind: smt".to_string(),
            format!("operation: {:?}", timeout.operation),
            format!("limit: {:?}", timeout.limit),
            format!("operation_wall: {:?}", timeout.operation_wall),
        ];
        lines
    }

    pub fn dump(&self) -> Arc<TimeoutSmtDump> {
        match self {
            TimeoutDiagnostic::Smt(timeout) => timeout.dump.clone(),
        }
    }
}

pub fn append_path_timing_lines(lines: &mut Vec<String>, timing: PathTimeSnapshot) {
    lines.push(format!("active_wall: {:?}", timing.active_wall));
    lines.push(format!("executor_cpu: {:?}", timing.executor_cpu));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn secs(value: u64) -> Duration {
        Duration::from_secs(value)
    }

    /// 30m 路径预算，单次 SMT 上限 60s。
    fn diagnostic(smt: SmtCallStats, active_wall: Duration) -> PathTimeoutDiagnostic {
        PathTimeoutDiagnostic {
            limit: secs(1800),
            timing: PathTimeSnapshot { active_wall, executor_cpu: active_wall },
            smt,
            smt_operation_limit: Some(secs(60)),
            control_flow_steps: 987_654,
            position: "execute:1234".to_string(),
        }
    }

    /// 造一份统计：`calls` 次调用摊在一个热点调用点上，其中最慢一次 `slowest` 秒。
    fn smt_stats(calls: u64, wall: u64, timeouts: u64, timeout_wall: u64, slowest: u64) -> SmtCallStats {
        SmtCallStats {
            calls,
            wall: secs(wall),
            slowest: Some(SlowestSmtCall {
                operation: SmtOperation::CheckSatAssuming,
                source_loc: SourceLoc::new(0, 120, 4, 123, 60),
                wall: secs(slowest),
            }),
            timeouts,
            timeout_wall: secs(timeout_wall),
            sites: vec![SmtCallSite { source_loc: SourceLoc::new(0, 120, 4, 123, 60), calls, wall: secs(wall) }],
        }
    }

    #[test]
    fn slowest_call_and_timeout_totals_are_tracked() {
        let interrupted = SourceLoc::new(0, 120, 4, 123, 60);
        let mut stats = SmtCallStats::empty();
        stats.record(SmtOperation::CheckSat, SourceLoc::unknown(), secs(1), false);
        stats.record(SmtOperation::CheckSatAssuming, interrupted, secs(60), true);
        stats.record(SmtOperation::ModelEval, SourceLoc::unknown(), secs(2), false);

        assert_eq!(stats.calls, 3);
        assert_eq!(stats.wall, secs(63));
        assert_eq!(stats.max_wall(), secs(60));
        // 按调用点聚合：unknown 的两次归到一起，被中断那次单独一个位置。
        assert_eq!(stats.distinct_sites(), 2);
        let hottest = stats.hottest_sites(2);
        assert_eq!(hottest[0].source_loc, SourceLoc::unknown());
        assert_eq!(hottest[0].calls, 2);
        assert_eq!(hottest[1].source_loc, interrupted);
        assert_eq!(hottest[1].wall, secs(60));
        let slowest = stats.slowest.expect("最慢调用应当被记录");
        assert_eq!(slowest.operation, SmtOperation::CheckSatAssuming);
        assert_eq!(slowest.source_loc, interrupted);
        // 被中断的调用同时计入总量和超时量。
        assert_eq!(stats.timeouts, 1);
        assert_eq!(stats.timeout_wall, secs(60));
    }

    #[test]
    fn cause_separates_smt_deadline_pressure_from_genuinely_slow_solving() {
        // 24 次打满 60s 上限 = 24m，占 30m 预算的 80%：放宽路径预算没用。
        let deadline_pressure = diagnostic(smt_stats(600, 1750, 24, 1440, 60), secs(1800));
        assert_eq!(deadline_pressure.cause(), PathTimeoutCause::SmtOperationTimeouts);

        // 一次超时只占预算 3.3%，其余是正常求解累积出来的：确实需要更多预算。
        let slow_solving = diagnostic(smt_stats(9000, 1740, 1, 60, 60), secs(1800));
        assert_eq!(slow_solving.cause(), PathTimeoutCause::SlowSmtSolving);

        // SMT 只占 active_wall 的 20%，瓶颈不在求解器。
        let executor_bound = diagnostic(smt_stats(300, 360, 0, 0, 5), secs(1800));
        assert_eq!(executor_bound.cause(), PathTimeoutCause::ExecutorWork);
    }

    #[test]
    fn report_lines_carry_the_numbers_behind_the_verdict() {
        let files = ["extensions/V/vext_arith_insts.sail"];
        let lines = diagnostic(smt_stats(600, 1750, 24, 1440, 60), secs(1800)).report_lines(&files);
        let report = lines.join("\n");

        assert!(report.contains("预算 1800.0s"), "{}", report);
        assert!(report.contains("SMT 调用 600 次"), "{}", report);
        assert!(report.contains("最慢单次 60.0s"), "{}", report);
        assert!(report.contains("CheckSatAssuming @ extensions/V/vext_arith_insts.sail 120:4 - 123:60"), "{}", report);
        assert!(report.contains("被单次上限(60.0s)中断 24 次"), "{}", report);
        assert!(report.contains("占预算 80.0%"), "{}", report);
        assert!(report.contains("少数 SMT 操作打满单次上限"), "{}", report);
        // 死循环判断要用的两项：控制流步数与最热调用点的求解次数。
        assert!(report.contains("控制流步数 987654"), "{}", report);
        assert!(report.contains("停在 execute:1234"), "{}", report);
        assert!(report.contains("最热调用点(1 个不同位置): 600 次/1750.0s @"), "{}", report);
    }

    #[test]
    fn report_lines_handle_paths_that_never_called_the_solver() {
        let lines = diagnostic(SmtCallStats::empty(), secs(1800)).report_lines(&[]);
        let report = lines.join("\n");

        assert!(report.contains("SMT 调用 0 次"), "{}", report);
        assert!(report.contains("瓶颈在 executor 解释执行"), "{}", report);
    }
}
