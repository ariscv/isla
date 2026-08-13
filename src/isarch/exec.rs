use super::clause::{get_extension_clauses, normalize_clause_name};
use super::target::{Target, RISCV};
use super::timeout_report::TimeoutReporter;
pub use super::timeout_report::{TimeoutReportConfig, TimeoutSmtOutput};
use super::{get_all_clause_names, list_instructions, try_get_assembly_encdec, try_get_assembly_name};
use isla_lib::bitvector::BV;
use isla_lib::config::ExecutionLimitsConfig;
use isla_lib::error::IslaError;
use isla_lib::error::{ExecError, SmtError};
use isla_lib::executor::{backtrace_string, LocalFrame, Run};
use isla_lib::executor::{ExecutionLimits, LimitBehavior, TaskState};
use isla_lib::fmtval::FmtVal;
use isla_lib::ir::*;
use isla_lib::log;
use isla_lib::primop_util::symbolic;
use isla_lib::register::RegisterBindings;
use isla_lib::smt::{Config, Context, Model};
use isla_lib::smt::{Solver, Sym};
use isla_lib::source_loc::{SourceLoc, SourceRegionSpec};
use isla_lib::zencode;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

#[allow(non_camel_case_types)]
#[derive(Serialize, Deserialize, Clone)]
struct AssemGenJsonItem {
    arch: BTreeMap<String, String>,
    #[serde(rename = "test-ins")]
    test_ins: String,
    #[serde(rename = "test-ins-encdec")]
    test_ins_encdec: String,
    #[serde(rename = "isa-state")]
    isa_state: BTreeMap<String, String>,
    ret_val: String,
}
impl AssemGenJsonItem {
    pub fn new<B: BV>(
        target: &dyn Target<B>,
        test_ins: String,
        test_ins_encdec: String,
        isa_state: BTreeMap<String, String>,
        ret_val: String,
    ) -> Self {
        let mut arch = BTreeMap::new();
        arch.insert("pretty-name".to_string(), target.arch_pretty_name().to_string());
        arch.insert("name".to_string(), target.arch_name().to_string());
        arch.insert("xlen".to_string(), target.xlen().to_string());
        arch.insert("ext".to_string(), "IMACFD".to_string());
        AssemGenJsonItem { arch, test_ins, test_ins_encdec, isa_state, ret_val }
    }
}
trait ToJSON: Serialize {
    #[allow(dead_code)]
    fn to_json_str(&self) -> String {
        serde_json::to_string_pretty(self).unwrap()
    }
    fn to_json(&self, file_path: Option<String>) {
        let json = serde_json::to_string_pretty(self).unwrap();
        // 若未指定输出路径，则默认写到当前目录下的 assem_gen.json
        let path = file_path.unwrap_or_else(|| "assem_gen.json".to_string());
        // 支持类似 "output/a/b.json" 的路径：先提取父目录并递归创建（等价 mkdir -p）
        if let Some(parent) = Path::new(&path).parent() {
            // parent 可能为空（例如仅文件名 "a.json"），空路径时无需创建目录
            if !parent.as_os_str().is_empty() {
                fs::create_dir_all(parent).unwrap();
            }
        }
        // 目录准备好之后再写文件
        fs::write(path, json).unwrap();
    }
}
#[allow(non_camel_case_types)]
#[derive(Serialize, Deserialize)]
struct AssemGenJson {
    gen: Vec<AssemGenJsonItem>,
}
impl ToJSON for AssemGenJson {}
impl ToJSON for AssemGenJsonItem {}
impl AssemGenJson {
    fn new(gen: Vec<AssemGenJsonItem>) -> Self {
        AssemGenJson { gen }
    }
}

/// 一条完成的用例 + 它的路径签名。签名用于收尾阶段的稳定排序与配额取样，让多线程下
/// 的产出顺序不影响最终落盘的用例集合（按 codex 评审意见的"路径局部指纹 + 全量 canonical sort"）。
#[derive(Clone)]
struct CollectedCase {
    path_signature: u64,
    item: AssemGenJsonItem,
}

struct SolveCollectorState {
    cases: Vec<CollectedCase>,
    case_quota: Option<CaseQuota>,
    first_error: Option<ExecError>,
}

impl SolveCollectorState {
    fn new() -> Self {
        Self::with_case_quota(None)
    }

    fn with_case_quota(case_quota: Option<CaseQuota>) -> Self {
        SolveCollectorState { first_error: None, cases: Vec::new(), case_quota }
    }

    fn record_error(&mut self, error: &ExecError) -> bool {
        let error = match error {
            ExecError::Timeout => ExecError::Timeout,
            ExecError::Smt(error) => ExecError::Smt(error.clone()),
            _ => return false,
        };
        if self.first_error.is_none() {
            self.first_error = Some(error);
        }
        true
    }
}

struct ErrorRecorder<'a> {
    collected: &'a Mutex<SolveCollectorState>,
    reporter: &'a TimeoutReporter,
    clause: &'a str,
}

impl ErrorRecorder<'_> {
    fn record_error_diagnostic<'ir, B: BV>(
        &self,
        error: &ExecError,
        frame: &LocalFrame<'ir, B>,
        shared_state: &SharedState<'ir, B>,
    ) -> Vec<(isla_lib::timeout::TimeoutDiagnostic, bool)> {
        frame.configure_timeout_smt_dump(error, shared_state);
        self.record_configured_error_diagnostic(error)
    }

    fn record_configured_error_diagnostic(
        &self,
        error: &ExecError,
    ) -> Vec<(isla_lib::timeout::TimeoutDiagnostic, bool)> {
        if !self.collected.lock().expect("solve collector mutex poisoned").record_error(error) {
            return Vec::new();
        }
        let diagnostics = match error {
            ExecError::Smt(SmtError::Timeout(timeout)) => {
                let diagnostic = isla_lib::timeout::TimeoutDiagnostic::Smt(timeout.clone());
                drop(diagnostic.dump().materialize());
                vec![(diagnostic, self.reporter.itrace_enabled())]
            }
            _ => Vec::new(),
        };
        self.reporter.report_error(self.clause, error);
        diagnostics
    }
}

fn should_collect_unfinished_path<B: BV>(run: &Run<B>) -> bool {
    !matches!(run, Run::Dead)
}

/// 收集一个值里出现的全部符号变量，按出现顺序去重。
fn collect_symbolic_vars<B: BV>(value: &Val<B>, symbols: &mut Vec<Sym>) {
    match value {
        Val::Symbolic(sym) => {
            if !symbols.contains(sym) {
                symbols.push(*sym)
            }
        }
        Val::Vector(values) | Val::List(values) => {
            for value in values {
                collect_symbolic_vars(value, symbols)
            }
        }
        Val::Struct(fields) => {
            for value in fields.values() {
                collect_symbolic_vars(value, symbols)
            }
        }
        Val::Ctor(_, value) => collect_symbolic_vars(value, symbols),
        Val::SymbolicCtor(sym, fields) => {
            if !symbols.contains(sym) {
                symbols.push(*sym)
            }
            for value in fields.values() {
                collect_symbolic_vars(value, symbols)
            }
        }
        _ => (),
    }
}

/// 让路径没有约束到的枚举字段在不同路径上取到不同成员。
///
/// 在 funct6 dispatch 之前就 `return Illegal_Instruction()` 的路径根本没有约束过 funct6，
/// Z3 于是在每条这样的路径上都给出同一个成员（枚举里的第一个），结果所有这类非法用例
/// 都被标注成同一条子指令——VVTYPE 里就是 vadd.vv，实测被顶到 196 条，而其它子指令一条
/// 非法用例都分不到。这里按路径签名给每个符号枚举字段挑一个候选成员，能满足就钉住，
/// 让非法用例散布到各条子指令上，覆盖面也更广。
///
/// 路径本身已经约束住的字段（例如走进某个 funct6 arm 的路径）候选值会 Unsat，直接跳过，
/// 因此不会改变任何一条路径的语义，只影响"任意值"的取法。
fn diversify_unconstrained_enums<'ir, B: BV>(
    args: &[Val<B>],
    signature: u64,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) {
    let mut symbols = Vec::new();
    for arg in args {
        collect_symbolic_vars(arg, &mut symbols)
    }
    if symbols.is_empty() {
        return;
    }

    // 先用一个模型认出哪些符号是枚举，同时拿到它们的 enum_id。
    let mut enum_symbols = Vec::new();
    if solver.check_sat(SourceLoc::unknown()) != isla_lib::smt::SmtResult::Sat {
        return;
    }
    {
        let mut model = Model::new(solver);
        for sym in symbols {
            if let Ok(isla_lib::smt::ModelVal::Exp(isla_lib::smt::smtlib::Exp::Enum(member))) = model.get_var(sym) {
                enum_symbols.push((sym, member))
            }
        }
    }

    for (index, (sym, member)) in enum_symbols.into_iter().enumerate() {
        let members = match shared_state.type_info.enums.get(&member.enum_id.to_name()) {
            Some(members) if members.len() > 1 => members.len(),
            _ => continue,
        };
        let candidate = (signature.wrapping_add(index as u64) % members as u64) as usize;
        if candidate == member.member {
            continue;
        }
        let preferred = isla_lib::smt::smtlib::Exp::Eq(
            Box::new(isla_lib::smt::smtlib::Exp::Var(sym)),
            Box::new(isla_lib::smt::smtlib::Exp::Enum(isla_lib::smt::EnumMember {
                enum_id: member.enum_id,
                member: candidate,
            })),
        );
        // Unsat 说明这条路径已经把该字段约束成别的成员了，保持原样。
        if solver.check_sat_with(&preferred, SourceLoc::unknown()) == isla_lib::smt::SmtResult::Sat {
            solver.add(isla_lib::smt::smtlib::Def::Assert(preferred))
        }
    }
}

/// 输出层配额：按 `(助记符, 完整 test-ins, ret_val 类别)` 分组，每组最多保留 N 条。
///
/// 这是 KLEE `emittedErrors` 的可复现改写——把"限流只作用在输出层、执行路径一条不少"
/// 的设计原样保留，把全局 static 集合换成"所有 worker join 后做一次确定性归并"。
/// 成功用例（`Retire_Success`）默认不限量，配额只压非法用例。
///
/// 分组键带了完整 `test-ins`：同一个非法编码配不同 vtype 各算一条是主要冗余形态，
/// 按 `(助记符, test-ins)` 分组能让这些落在同一个桶里被均匀取样。
#[derive(Clone, Debug, Default)]
pub struct CaseQuota {
    /// 按 `ret_val` 类别名做前缀过滤的配额。key 是 ret_val 字符串里的构造子名
    /// （例如 `Illegal_Instruction`、`Retire_Success`），value 是每组上限。
    /// 未列出的类别不限量。
    pub per_class: BTreeMap<String, u32>,
}

impl CaseQuota {
    fn from_config(map: &BTreeMap<String, u32>) -> Self {
        CaseQuota { per_class: map.clone() }
    }

    fn limit_for(&self, ret_val: &str) -> Option<u32> {
        // ret_val 形如 "Illegal_Instruction(())" / "Retire_Success(())"，取构造子名做匹配。
        let name = ret_val.split('(').next().unwrap_or(ret_val);
        self.per_class.get(name).copied()
    }
}

/// 收尾阶段的确定性归并：分组配额 + 全量 canonical sort。
///
/// 顺序由 `path_signature` + 序列化文本（tie-breaker）决定，与 worker 调度无关，
/// 因此 THREADS=1/4/64 跑出来的 JSON 逐字节一致。
fn finalize_cases(mut cases: Vec<CollectedCase>, quota: &Option<CaseQuota>) -> Vec<AssemGenJsonItem> {
    // 1. 组内配额：按 (助记符, 完整 test-ins, ret_val 类别) 分桶，每组按签名均匀取样。
    if let Some(quota) = quota {
        cases = apply_case_quota(cases, quota);
    }
    // 2. 全量稳定排序：签名 + 序列化文本做 tie-breaker，杜绝签名碰撞时的调度依赖。
    cases.sort_by(|a, b| {
        let a_text = serde_json::to_string(&a.item).expect("AssemGenJsonItem 序列化失败");
        let b_text = serde_json::to_string(&b.item).expect("AssemGenJsonItem 序列化失败");
        a.path_signature.cmp(&b.path_signature).then_with(|| a_text.cmp(&b_text))
    });
    cases.into_iter().map(|case| case.item).collect()
}

fn apply_case_quota(cases: Vec<CollectedCase>, quota: &CaseQuota) -> Vec<CollectedCase> {
    use std::collections::HashMap;
    // 先按分组键装桶。
    let mut buckets: HashMap<(String, String, String), Vec<CollectedCase>> = HashMap::new();
    for case in cases {
        let mnemonic = case.item.test_ins.split_whitespace().next().unwrap_or("").to_string();
        let ret_class = case.item.ret_val.split('(').next().unwrap_or("").to_string();
        let key = (mnemonic, case.item.test_ins.clone(), ret_class);
        buckets.entry(key).or_default().push(case);
    }
    // 每个桶按 ret_val 类别查配额；超过配额的按签名均匀取样。
    let mut kept = Vec::with_capacity(buckets.values().map(|v| v.len()).sum());
    for (_, mut bucket) in buckets {
        let limit = bucket.first().and_then(|c| quota.limit_for(&c.item.ret_val));
        match limit {
            Some(0) => {}
            Some(n) if (n as usize) < bucket.len() => {
                bucket.sort_by(|a, b| {
                    let a_text = serde_json::to_string(&a.item).expect("AssemGenJsonItem 序列化失败");
                    let b_text = serde_json::to_string(&b.item).expect("AssemGenJsonItem 序列化失败");
                    a.path_signature.cmp(&b.path_signature).then_with(|| a_text.cmp(&b_text))
                });
                let k = bucket.len();
                for i in 0..n as usize {
                    // 均匀取样：在排序后的桶里等间距取 n 个，比取前 n 更能让 vtype/操作数分散。
                    let idx = if n == 1 { 0 } else { i * (k - 1) / (n as usize - 1) };
                    kept.push(bucket[idx].clone());
                }
            }
            _ => kept.extend(bucket),
        }
    }
    kept
}

fn solve_execution_limits(symtab: &Symtab, config: Option<&ExecutionLimitsConfig>) -> ExecutionLimits {
    const GATHER_SOURCE_FILE: &str = "extensions/V/vext_arith_insts.sail";

    // 执行限制配置：局部 branch/loop 预算负责压制路径规模；达到预算后按固定 seed
    // 可复现抽样一侧继续执行，而不是固定选择 true 或直接丢弃整条路径。
    //
    // - max_forks_per_branch=2：每个 (函数, IR PC, 最近两层调用点, SourceLoc) 最多实际 fork 2 次；
    //   后续访问成对均衡地抽样 true/false，避免循环热点吃光深层分支预算。
    // - max_forks_per_path=None：不设置全局 path fork 上限，避免在 SourceLoc region 之外裁剪路径。
    // - max_backjumps_per_loop=None：当前只限制下面四个 gather 条件分支，不提前退出有界 vector 循环。
    // - max_path_depth=None：不使用全局路径深度限制，区域外控制流保持完整遍历。
    // - regions：只选择两个 gather 指令的 mask 和 idx < VLMAX 逐元素热点；constructor、编码 guard、
    //   合法性检查与主 match 保持完整展开，避免影响 VVTYPE 指令种类覆盖。
    let default_region_specs = [
        // VV_VRGATHER：逐元素 mask 分支。
        SourceRegionSpec::new(GATHER_SOURCE_FILE, (186, 6), (192, 7)),
        // VV_VRGATHER：逐元素 idx < VLMAX 分支。
        SourceRegionSpec::new(GATHER_SOURCE_FILE, (191, 20), (191, 65)),
        // VV_VRGATHEREI16：逐元素 mask 分支。
        SourceRegionSpec::new(GATHER_SOURCE_FILE, (195, 6), (201, 7)),
        // VV_VRGATHEREI16：逐元素 idx < VLMAX 分支。
        SourceRegionSpec::new(GATHER_SOURCE_FILE, (200, 20), (200, 65)),
    ];
    let limits = ExecutionLimits::default()
        .with_max_forks_per_branch(2)
        .with_limit_behavior(LimitBehavior::Concretize)
        .with_region_specs(&default_region_specs, symtab);

    // TOML 中出现的字段逐项覆盖代码默认策略；regions 出现时整体替换默认 SourceRegion 集合。
    match config {
        Some(config) => limits.with_config(config, symtab),
        None => limits,
    }
}

/// 基于用户指定的 itrace 基路径和 clause 名，生成每个 clause 独立的输出文件路径。
/// 规则：`output/itrace.txt` + clause `zadd` → `output/itrace_zadd.txt`
#[cfg(feature = "itrace")]
fn clause_itrace_output_path(base_path: &Path, clause: &str) -> PathBuf {
    let stem = base_path.file_stem().and_then(|s| s.to_str()).unwrap_or("itrace");
    let extension = base_path.extension().and_then(|s| s.to_str()).unwrap_or("txt");
    let new_name = format!("{}_{}.{}", stem, clause, extension);
    base_path.with_file_name(new_name)
}

/// solve-state 子命令的主入口函数
/// 支持通过 clause 名、扩展名、汇编指令名或 --all 来筛选需要符号执行的 clause
pub fn solve_state_main<'ir, B: BV>(
    shared_state: &SharedState<'ir, B>,
    regs: &'ir RegisterBindings<'ir, B>,
    lets: &'ir Bindings<'ir, B>,
    initial_memory: Option<isla_lib::memory::Memory<B>>,
    target: &mut dyn RISCV<B>,
    clauses: &[String],
    extensions: &[String],
    instruction_names: &[String],
    run_all: bool,
    itrace_path: Option<PathBuf>,
    ir_file_path: Option<PathBuf>,
    num_threads: usize,
    timeout: Option<u64>,
    execution_limits_config: Option<&ExecutionLimitsConfig>,
    timeout_report_config: TimeoutReportConfig,
) -> bool {
    let case_quota = execution_limits_config.and_then(|cfg| cfg.case_quota.as_ref().map(CaseQuota::from_config));
    let mut clause_set: HashSet<String> = HashSet::new();
    let mut success = true;

    // 添加显式指定的 clause
    clause_set.extend(clauses.iter().map(|clause| normalize_clause_name(clause)));

    // 添加扩展对应的 clause
    for ext in extensions {
        let ext_clauses = get_extension_clauses(ext);
        if ext_clauses.is_empty() {
            log!(log::SYM_EXEC, &format!("警告: 未知扩展 '{}'", ext));
            success = false;
        }
        clause_set.extend(ext_clauses);
    }

    // 根据汇编指令名查找对应的 clause
    if !instruction_names.is_empty() {
        let instruction_map = list_instructions(shared_state, regs, lets);
        for inst_name in instruction_names {
            let mut found = false;
            for (clause_display_name, names) in &instruction_map {
                if names.iter().any(|n| n == inst_name) {
                    clause_set.insert(zencode::encode(clause_display_name));
                    found = true;
                }
            }
            if !found {
                log!(log::SYM_EXEC, &format!("警告: 未找到指令 '{}' 对应的 clause", inst_name));
                success = false;
            }
        }
    }

    // --all 模式：执行所有 clause
    if run_all {
        clause_set.extend(get_all_clause_names(shared_state));
    }

    #[cfg(not(feature = "itrace"))]
    let _ = (&itrace_path, &ir_file_path);

    #[cfg(feature = "itrace")]
    if itrace_path.is_some() && ir_file_path.is_none() {
        panic!("itrace: 使用 --itrace 时必须同时指定 --arch/-A 提供 IR 文件路径");
    }

    if clause_set.is_empty() {
        eprintln!("错误: 未指定任何要符号执行的 clause");
        eprintln!("请使用 --clause, --extension, --instruction-name 或 --all 指定");
        return false;
    }

    let num_clauses = clause_set.len();
    log!(log::SYM_EXEC, &format!("solve_state: 共 {} 个 clause 待执行", num_clauses));
    let execution_limits = solve_execution_limits(&shared_state.symtab, execution_limits_config);
    let timeout_reporter = TimeoutReporter::new(timeout_report_config);

    for clause in clause_set {
        #[cfg(feature = "itrace")]
        if let Some(base_path) = &itrace_path {
            // 多个 clause 同时执行时，为每个 clause 生成独立 itrace 输出文件，避免互相覆盖。
            let output_path =
                if num_clauses > 1 { clause_itrace_output_path(base_path, &clause) } else { base_path.clone() };
            if let Some(ir) = ir_file_path.as_ref() {
                // 每次执行前用当前 clause、IR 文件和输出路径配置 itrace 追踪器。
                shared_state.itrace.configure(clause.as_str(), ir.clone(), Some(output_path), &shared_state.symtab);
            }
        }

        match run_symbolic_execute_with_target(
            target,
            &clause,
            shared_state,
            regs,
            lets,
            initial_memory.clone(),
            num_threads,
            timeout,
            &execution_limits,
            &timeout_reporter,
            case_quota.clone(),
        ) {
            Ok(_) => {}
            Err(e) => {
                eprintln!("错误: clause '{}' 符号执行失败: {}", clause, e);
                log!(log::SYM_EXEC, &format!("solve_state: {}运行错误 {}", clause, e));
                success = false;
            }
        }

        #[cfg(feature = "itrace")]
        if itrace_path.is_some() {
            shared_state.itrace.dump();
        }
    }

    success
}

#[allow(non_snake_case)]
fn symbolic_args_from_types<B: BV>(
    instruction_name: &str,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    // 查找指令的构造函数名称
    let ctor_name = shared_state.symtab.lookup(instruction_name);

    // 从 union 类型信息中获取构造函数的参数类型
    let instruction_union = shared_state.type_info.unions.get(&shared_state.symtab.lookup("zinstruction"));

    let Some(union_members) = instruction_union else {
        // zinstruction union 不存在
        panic!("run_symbolic_execute: 在symtab中没找到符号'zinstruction'");
    };

    // 查找当前构造函数的类型
    let Some((_, ctor_ty)) = union_members.iter().find(|(n, _ty)| *n == ctor_name) else {
        // 指令不在 zinstruction union 中（可能是其他架构的指令）
        return Err(ExecError::Type(
            format!("指令 '{}' 不在 zinstruction union 中", instruction_name),
            SourceLoc::unknown(),
        ));
    };

    symbolic(ctor_ty, shared_state, solver, SourceLoc::unknown())
}
fn run_symbolic_execute_with_target<'ir, B: BV>(
    target: &mut dyn RISCV<B>,
    instruction_name: &str,
    shared_state: &SharedState<'ir, B>,
    regs: &'ir RegisterBindings<'ir, B>,
    lets: &'ir Bindings<'ir, B>,
    initial_memory: Option<isla_lib::memory::Memory<B>>,
    num_threads: usize,
    timeout: Option<u64>,
    execution_limits: &ExecutionLimits,
    timeout_reporter: &TimeoutReporter,
    case_quota: Option<CaseQuota>,
) -> Result<Option<String>, ExecError> {
    use isla_lib::smt::checkpoint;

    let state_regs = target.reg_list();

    let mut cfg = Config::new();
    cfg.set_param_value("model", "true");
    let ctx = Context::new(cfg);
    let mut solver = Solver::new(&ctx);
    let mut symbolic_regs = regs.clone();

    // pre-state 主动符号化：遍历 target 提供的寄存器、按类型符号化并覆盖，返回 PreStateCtx 供求解后取 pre-state。
    target.setup_pre_state(&mut symbolic_regs, lets, shared_state, &mut solver)?;

    //不要删掉这个注释！！！留着以后改pmp的时候用
    /* if target.pmp_symbolic() {
        target.apply_symbolic_pmp_to_registers(&shared_state.symtab, &mut symbolic_regs, shared_state, &mut solver)?;
    } */

    // 使用 symbolic_args_from_types 生成符号化参数
    let ctor_name = shared_state.symtab.lookup(instruction_name);

    let fun_args = vec![Val::<B>::Ctor(
        ctor_name,
        Box::new(symbolic_args_from_types(instruction_name, shared_state, &symbolic_regs, lets, &mut solver)?),
    )];
    log!(log::SYM_EXEC, &format!("fun_args:{:?}", fun_args));
    log!(log::ARCH_INFO, &format!("{:?}", state_regs));

    // 生成参数（暂时使用默认值，测试checkpoint机制）

    // 构造指令值

    // 创建checkpoint，包含符号化变量
    let cp = checkpoint(&mut solver);

    // 使用checkpoint执行函数，支持错误传播
    let result: Arc<Mutex<SolveCollectorState>> =
        Arc::new(Mutex::new(SolveCollectorState::with_case_quota(case_quota)));

    let task_state = TaskState::new().with_execution_limits(execution_limits.clone());

    //isla_lib::executor::execute_ir_function_with_checkpoint_and_limits(
    isla_lib::executor::execute_ir_function_with_checkpoint_multi_thread(
        "zexecute",
        &fun_args,
        shared_state,
        &symbolic_regs,
        lets,
        &result,
        &|thread, _task_id, exec_result, shared_state, mut solver, collected| {
            let mut itrace_diagnostics = Vec::new();
            let submit_itrace = |frame, diagnostics: &mut Vec<(isla_lib::timeout::TimeoutDiagnostic, bool)>| {
                isla_lib::executor::submit_itrace_for_local_frame_with_diagnostics(
                    frame,
                    shared_state,
                    std::mem::take(diagnostics),
                );
            };
            let error_recorder = ErrorRecorder { collected, reporter: timeout_reporter, clause: instruction_name };
            let should_submit_itrace = match &exec_result {
                Ok((Run::Finished(_), _)) => true,
                Ok((run, _)) => should_collect_unfinished_path(run),
                Err((ExecError::AssertionFailure(_, _), _)) => false,
                Err((error, frame)) => {
                    itrace_diagnostics = error_recorder.record_error_diagnostic(error, frame, shared_state);
                    true
                }
            };

            match &exec_result {
                Ok((run, frame)) => match run {
                    Run::Finished(Val::Poison) => {
                        log!(log::SYM_EXEC, &format!("警告: {}这个Ctor返回值是Poison，可能是相关扩展（如H扩展）造成的，因此产生了sail的_inner_error_", instruction_name))
                    }
                    Run::Finished(ret_val) => {
                        let ret_val_str = ret_val.to_str(shared_state).to_string();
                        log!(
                            log::PATH_RESULT,
                            &format!(
                                "1. tid:{} 执行好一条路径，fork={}，ret_val={}",
                                thread,
                                frame.forks(),
                                ret_val_str
                            )
                        );
                        // Illegal_Instruction is a valid Sail ExecutionResult; JSON keeps every finished ret_val.
                        /* let assembly = {
                            // 获取 zexecute 函数的参数信息
                            let execute_fn_id = shared_state.symtab.lookup("zexecute");
                            let (fn_args, _, _) = shared_state.functions.get(&execute_fn_id).unwrap();

                            // 提取第一个参数（指令）的值
                            match fn_args.first() {
                                Some((arg_name, _)) => {
                                    match frame.vars().get(arg_name) {
                                        // arg_val 就是指令的参数值
                                        Some(UVal::Init(arg_val)) => {
                                            println!("{:#?}", arg_val);
                                            get_assembly_name(arg_val.clone(), &shared_state, regs, lets)
                                        }
                                        _ => panic!(""),
                                    }
                                }
                                _ => panic!(""),
                            }
                        };
                        println!("assembly:{:#?}", assembly); */
                        // isarch::get_assembly_name(Val::Unit /* ??? */, &shared_state, regs, lets);

                        let mut test_ins = String::new();
                        let mut test_ins_encdec = String::new();
                        let mut isa_state: BTreeMap<String, String> = BTreeMap::new();
                        // 未被这条路径约束的枚举字段（典型是提前返回 Illegal 的路径上的
                        // funct6）先按路径签名挑一个成员钉住，否则所有这类用例都会被标注
                        // 成同一条子指令。
                        diversify_unconstrained_enums(&fun_args, frame.path_signature(), shared_state, &mut solver);
                        // 获取ISA状态（寄存器、lets变量等）
                        // 首先检查solver是否可满足
                        let smt_result = solver.check_sat(SourceLoc::unknown());
                        if let isla_lib::smt::SmtResult::Error(error) = &smt_result {
                            let error = ExecError::Smt(error.clone());
                            itrace_diagnostics = error_recorder.record_error_diagnostic(&error, frame, shared_state);
                            log!(log::SYM_EXEC, &format!("collector final SMT query failed: {}", error));
                            submit_itrace(frame, &mut itrace_diagnostics);
                            return;
                        }
                        if smt_result == isla_lib::smt::SmtResult::Sat {
                            if let Ok(mut model) =
                                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| Model::new(&solver)))
                            {
                                // 开启 model completion：未被约束的 pre-state 符号变量也会得到一个具体值，
                                // 这样所有主动符号化的 pre-state 寄存器都能输出（与 testgen 一致）。
                                // model.set_complete_model(true);
                                log!(log::PATH_RESULT, &format!("2. === ISA State (Thread {}) ===", thread));
                                let test = Sym::from_u32(6);
                                // dlog!("model.get_var({:?})={:?}", test, model.get_var(test));
                                // dlog!("fun_args={:#?}", model.get_val(&fun_args[0]));
                                match model.get_val(&fun_args[0]) {
                                    Ok(arg_val) => {
                                        let asm_opt =
                                            match try_get_assembly_name(arg_val.clone(), shared_state, regs, lets) {
                                                Ok(assembly) => assembly,
                                                Err(error) => {
                                                    itrace_diagnostics =
                                                        error_recorder.record_configured_error_diagnostic(&error);
                                                    log!(
                                                        log::PATH_RESULT,
                                                        &format!(
                                                            "警告: clause{} 汇编名称求解失败 {:?}",
                                                            instruction_name, error
                                                        )
                                                    );
                                                    submit_itrace(frame, &mut itrace_diagnostics);
                                                    return;
                                                }
                                            };
                                        log!(log::PATH_RESULT, &format!("当前汇编：{:?}", asm_opt));
                                        match asm_opt {
                                            Some(asm) => test_ins = asm,
                                            None => {
                                                submit_itrace(frame, &mut itrace_diagnostics);
                                                return;
                                            }
                                        }
                                        let asm_encdec_opt =
                                            match try_get_assembly_encdec(arg_val.clone(), shared_state, regs, lets) {
                                                Ok(encoded) => match encoded {
                                                    Some(val) => match FmtVal::from_val(&val, &mut model) {
                                                        Ok(fmt_val) => Some(fmt_val.to_str(shared_state)),
                                                        Err(err) => {
                                                            itrace_diagnostics = error_recorder
                                                                .record_error_diagnostic(&err, frame, shared_state);
                                                            log!(
                                                                log::PATH_RESULT,
                                                                &format!(
                                                                    "警告: {}汇编编码不可格式化 {:?}",
                                                                    instruction_name, err
                                                                )
                                                            );
                                                            None
                                                        }
                                                    },
                                                    None => None,
                                                },
                                                Err(error) => {
                                                    itrace_diagnostics =
                                                        error_recorder.record_configured_error_diagnostic(&error);
                                                    log!(
                                                        log::PATH_RESULT,
                                                        &format!(
                                                            "警告: clause{} 汇编编码求解失败 {:?}",
                                                            instruction_name, error
                                                        )
                                                    );
                                                    submit_itrace(frame, &mut itrace_diagnostics);
                                                    return;
                                                }
                                            };
                                        log!(log::PATH_RESULT, &format!("当前汇编encdec：{:?}", asm_encdec_opt));
                                        match asm_encdec_opt {
                                            Some(encdec) => test_ins_encdec = encdec,
                                            None => {
                                                submit_itrace(frame, &mut itrace_diagnostics);
                                                return;
                                            }
                                        }
                                    }
                                    Err(e) => {
                                        itrace_diagnostics =
                                            error_recorder.record_error_diagnostic(&e, frame, shared_state);
                                        log!(
                                            log::PATH_RESULT,
                                            &format!("警告: clause{} model.get_val失败 {:?}", instruction_name, e)
                                        );
                                        submit_itrace(frame, &mut itrace_diagnostics);
                                        return;
                                    }
                                }

                                // pre-state 取值：通过 target 和 setup 阶段生成的 PreStateCtx 查询具体解。
                                match target.solve_pre_state(&mut model, shared_state) {
                                    Ok(state) => isa_state.extend(state),
                                    Err(error) => {
                                        itrace_diagnostics =
                                            error_recorder.record_error_diagnostic(&error, frame, shared_state);
                                        log!(
                                            log::PATH_RESULT,
                                            &format!("警告: clause{} pre-state求解失败 {:?}", instruction_name, error)
                                        );
                                        submit_itrace(frame, &mut itrace_diagnostics);
                                        return;
                                    }
                                }

                                log!(
                                    log::PATH_RESULT,
                                    &format!("isa_state={}", serde_json::to_string_pretty(&isa_state).unwrap())
                                );
                                // 遍历lets中的特殊变量（如current_privilege等）
                                /* for (let_name, let_val) in frame.lets().iter() {
                                    let let_name_str = shared_state.symtab.to_str(*let_name);
                                    // 过滤掉一些内部变量
                                    if !let_name_str.starts_with("__") && let_name_str != "NULL" {
                                        match let_val {
                                            UVal::Init(Val::Symbolic(sym)) => match model.get_var(*sym) {
                                                Ok(isla_lib::smt::ModelVal::Exp(isla_lib::smt::smtlib::Exp::Bits64(bv))) => {
                                                    println!("  let {} = 0x{:x}", let_name_str, bv.lower_u64());
                                                }
                                                Ok(isla_lib::smt::ModelVal::Exp(isla_lib::smt::smtlib::Exp::Bits(bv))) => {
                                                    let hex_str: String = bv
                                                        .chunks(4)
                                                        .rev()
                                                        .map(|chunk: &[bool]| {
                                                            let mut n = 0u8;
                                                            for (i, bit) in chunk.iter().enumerate() {
                                                                if *bit {
                                                                    n |= 1 << i;
                                                                }
                                                            }
                                                            format!("{:x}", n)
                                                        })
                                                        .collect();
                                                    println!("  let {} = 0b{}", let_name_str, hex_str);
                                                }
                                                Ok(isla_lib::smt::ModelVal::Exp(isla_lib::smt::smtlib::Exp::Bool(b))) => {
                                                    println!("  let {} = {}", let_name_str, b);
                                                }
                                                Ok(isla_lib::smt::ModelVal::Exp(isla_lib::smt::smtlib::Exp::Enum(
                                                    member,
                                                ))) => {
                                                    let name = member.to_name(shared_state);
                                                    println!(
                                                        "  let {} = {}",
                                                        let_name_str,
                                                        shared_state.symtab.to_str(name)
                                                    );
                                                }
                                                _ => {}
                                            },
                                            UVal::Init(Val::Bits(bv)) => {
                                                println!("  let {} = 0x{:x}", let_name_str, bv.lower_u64());
                                            }
                                            UVal::Init(Val::Bool(b)) => {
                                                println!("  let {} = {}", let_name_str, b);
                                            }
                                            _ => {}
                                        }
                                    }
                                } */

                                // events
                                /* let mut events_vec = solver.trace().to_vec();
                                let events: Vec<Event<B>> = events_vec.drain(..).cloned().collect();
                                for event in events {
                                    match event {
                                        Event::Fork(fork_id, sym, branch_number, _) => {
                                            println!(
                                                " [event] Fork({}, {:?}, {}, _ )",
                                                fork_id,
                                                model.get_var(sym).unwrap(),
                                                branch_number
                                            )
                                        }
                                        _ => println!(" [event] {:?}", event),
                                    }
                                } */
                                log!(log::PATH_RESULT, "3. ==============================");
                            }
                        }
                        let single_instruction_json =
                            AssemGenJsonItem::new(target, test_ins, test_ins_encdec, isa_state, ret_val_str);
                        collected.lock().expect("solve collector mutex poisoned").cases.push(CollectedCase {
                            path_signature: frame.path_signature(),
                            item: single_instruction_json,
                        });
                    }
                    Run::Exit => {
                        log!(log::PATH_RESULT, &format!("tid:{} 执行好一条路径(Exit)，fork={}", thread, frame.forks()))
                    }
                    Run::Dead => {}

                    Run::Suspended => log!(
                        log::PATH_RESULT,
                        &format!("tid:{} 执行好一条路径(Suspended)，fork={}", thread, frame.forks())
                    ),
                },
                Err((error, frame)) => {
                    match error {
                        ExecError::MatchFailure(_) => {
                            // 静默处理
                        }
                        ExecError::AssertionFailure(_, _) => {
                            // assert 失败表示当前路径不满足模型前置条件，丢弃该路径。
                        }
                        _ => {
                            log!(
                                log::SYM_EXEC,
                                &format!(
                                    "执行错误: {}({:?})[{}]",
                                    error,
                                    error,
                                    error.source_loc().location_string(shared_state.symtab.files())
                                )
                            );
                            log!(
                                log::SYM_EXEC,
                                &format!("调用栈: {}", backtrace_string(frame.backtrace(), &shared_state.symtab))
                            );
                        }
                    }
                }
            }
            if should_submit_itrace {
                let frame = match &exec_result {
                    Ok((_, frame)) | Err((_, frame)) => frame,
                };
                submit_itrace(frame, &mut itrace_diagnostics);
            }
        },
        cp,
        num_threads,
        timeout,
        &task_state,
    );

    // 提取字符串结果
    let result_mutex = match Arc::try_unwrap(result) {
        Ok(result_mutex) => result_mutex,
        Err(_) => panic!("{} 执行结束后 result 收集器仍有共享引用", instruction_name),
    };
    let xlen_name_str = target.arch_pretty_name().to_string();
    let state = result_mutex.into_inner().expect("solve collector mutex poisoned");
    let quota = state.case_quota;
    let items = finalize_cases(state.cases, &quota);
    let json = AssemGenJson::new(items);
    json.to_json(Some(format!("output/{}_{}.json", xlen_name_str, instruction_name)));
    match state.first_error {
        Some(error) => Err(error),
        None => Ok(None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::bitvector::b64::B64;
    use isla_lib::config::LimitBehaviorConfig;
    use isla_lib::source_loc::SourceRegion;
    use isla_lib::timeout::{SmtDumpNames, SmtDumpSource, SmtOperation, SmtTimeout, TimeoutSmtDump};
    use std::time::Duration;

    struct NamesDump;

    impl SmtDumpSource for NamesDump {
        fn materialize(&self) -> Result<String, String> {
            panic!("timeout dump test must materialize with configured names")
        }

        fn materialize_with_names(&self, names: &SmtDumpNames) -> Result<String, String> {
            Ok(format!("{:?}", names))
        }
    }

    #[test]
    fn error_diagnostic_records_timeout_with_frame_names() {
        let argument_text = zencode::encode("test_argument");
        let function_text = zencode::encode("test_function");
        let mut symtab = Symtab::new();
        let argument = symtab.intern(&argument_text);
        let function_name = symtab.intern(&function_text);
        let shared_state: SharedState<B64> = SharedState::empty(symtab);
        let instrs: Vec<Instr<Name, B64>> = Vec::new();
        let mut frame = LocalFrame::new(function_name, &[], &Ty::Unit, None, &instrs);
        frame.vars_mut().insert(argument, UVal::Init(Val::Symbolic(Sym::from_u32(17))));
        let timeout = Arc::new(SmtTimeout {
            source_loc: SourceLoc::unknown(),
            operation: SmtOperation::CheckSat,
            limit: Duration::from_secs(1),
            operation_wall: Duration::from_secs(1),
            dump: Arc::new(TimeoutSmtDump::new(Arc::new(NamesDump))),
        });
        let error = ExecError::Smt(SmtError::Timeout(timeout.clone()));
        let collected = Mutex::new(SolveCollectorState::new());
        let reporter = TimeoutReporter::new(TimeoutReportConfig {
            output: TimeoutSmtOutput::new(false, false, true),
            directory: PathBuf::new(),
        });

        let recorder = ErrorRecorder { collected: &collected, reporter: &reporter, clause: "zTEST" };
        let diagnostics = recorder.record_error_diagnostic(&error, &frame, &shared_state);

        let state = collected.into_inner().unwrap();
        let Some(ExecError::Smt(SmtError::Timeout(recorded))) = state.first_error else {
            panic!("SMT timeout was not recorded")
        };
        assert!(Arc::ptr_eq(&recorded, &timeout));
        assert_eq!(diagnostics.len(), 1);
        assert!(timeout.dump.materialize().unwrap().contains("isla_test_argument__s17"));
    }

    #[test]
    fn solve_execution_limits_use_local_sampling_as_primary_path_bound() {
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["extensions/V/vext_arith_insts.sail"]);
        let limits = solve_execution_limits(&symtab, None);

        assert_eq!(limits.max_forks_per_branch, Some(2));
        assert_eq!(limits.max_forks_per_path, None);
        assert_eq!(limits.max_backjumps_per_loop, None);
        assert_eq!(limits.max_path_depth, None);
        assert_eq!(limits.call_context_depth, None);
        assert_eq!(limits.on_limit_reached, LimitBehavior::Concretize);
        assert_eq!(limits.regions.as_ref().unwrap().len(), 4);

        assert_eq!(
            limits.regions,
            Some(vec![
                SourceRegion::from_source_loc(SourceLoc::new(0, 186, 6, 192, 7)),
                SourceRegion::from_source_loc(SourceLoc::new(0, 191, 20, 191, 65)),
                SourceRegion::from_source_loc(SourceLoc::new(0, 195, 6, 201, 7)),
                SourceRegion::from_source_loc(SourceLoc::new(0, 200, 20, 200, 65)),
            ])
        );
    }

    #[test]
    fn solve_execution_limits_applies_toml_override_after_defaults() {
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["extensions/V/vext_arith_insts.sail"]);
        let config = ExecutionLimitsConfig {
            max_forks_per_branch: Some(7),
            max_forks_per_path: Some(11),
            call_context_depth: Some(3),
            on_limit_reached: Some(LimitBehaviorConfig::Truncate),
            ..ExecutionLimitsConfig::default()
        };

        let limits = solve_execution_limits(&symtab, Some(&config));

        assert_eq!(limits.max_forks_per_branch, Some(7));
        assert_eq!(limits.max_forks_per_path, Some(11));
        assert_eq!(limits.call_context_depth, Some(3));
        assert_eq!(limits.on_limit_reached, LimitBehavior::Truncate);
        assert_eq!(limits.regions.as_ref().unwrap().len(), 4);
    }

    #[test]
    fn solve_execution_limits_can_be_disabled_by_toml() {
        let symtab = Symtab::new();
        let config = ExecutionLimitsConfig { enabled: Some(false), ..ExecutionLimitsConfig::default() };

        let limits = solve_execution_limits(&symtab, Some(&config));

        assert_eq!(limits.max_forks_per_branch, None);
        assert_eq!(limits.max_forks_per_path, None);
        assert!(limits.regions.is_none());
    }

    #[test]
    fn solve_execution_limits_missing_default_region_file_matches_nothing_without_panicking() {
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["core/types.sail"]);

        let limits = solve_execution_limits(&symtab, None);

        assert_eq!(limits.max_forks_per_branch, Some(2));
        assert_eq!(limits.max_fork_pct_per_branch, None);
        assert_eq!(limits.max_backjumps_per_loop, None);
        assert_eq!(limits.regions, Some(Vec::new()));
    }

    #[test]
    fn solve_execution_limits_missing_configured_region_keeps_path_limits_only() {
        let mut symtab = Symtab::new();
        symtab.set_files(vec!["core/types.sail"]);
        let config = ExecutionLimitsConfig {
            max_forks_per_branch: Some(7),
            max_forks_per_path: Some(11),
            regions: Some(vec![SourceRegionSpec::new("extensions/V/vext_arith_insts.sail", (186, 6), (192, 7))]),
            ..ExecutionLimitsConfig::default()
        };

        let limits = solve_execution_limits(&symtab, Some(&config));

        assert_eq!(limits.max_forks_per_branch, Some(7));
        assert_eq!(limits.max_forks_per_path, Some(11));
        assert_eq!(limits.regions, Some(Vec::new()));
    }

    #[test]
    fn unfinished_path_collection_skips_dead_paths() {
        assert!(!should_collect_unfinished_path::<B64>(&Run::Dead));
        assert!(should_collect_unfinished_path::<B64>(&Run::Exit));
        assert!(should_collect_unfinished_path::<B64>(&Run::Suspended));
    }

    fn collected_case(signature: u64, test_ins: &str, ret_val: &str) -> CollectedCase {
        CollectedCase {
            path_signature: signature,
            item: AssemGenJsonItem {
                arch: BTreeMap::new(),
                test_ins: test_ins.to_string(),
                test_ins_encdec: "32'h0000_0000".to_string(),
                isa_state: BTreeMap::new(),
                ret_val: ret_val.to_string(),
            },
        }
    }

    #[test]
    fn case_quota_zero_discards_every_case_in_the_bucket() {
        let quota = CaseQuota { per_class: BTreeMap::from([(String::from("Illegal_Instruction"), 0)]) };
        let cases = vec![
            collected_case(1, "vadd.vv v0, v1, v2", "Illegal_Instruction(())"),
            collected_case(2, "vadd.vv v0, v1, v2", "Illegal_Instruction(())"),
            collected_case(3, "vadd.vv v0, v1, v2", "Retire_Success(())"),
        ];

        let finalized = finalize_cases(cases, &Some(quota));

        assert_eq!(finalized.len(), 1);
        assert_eq!(finalized[0].ret_val, "Retire_Success(())");
    }

    #[test]
    fn case_quota_same_signature_uses_canonical_json_tie_breaker() {
        let quota = CaseQuota { per_class: BTreeMap::from([(String::from("Illegal_Instruction"), 1)]) };
        let first = vec![
            collected_case(9, "vadd.vv v0, v1, v2", "Illegal_Instruction(())"),
            collected_case(9, "vadd.vv v0, v1, v3", "Illegal_Instruction(())"),
        ];
        let second = first.iter().cloned().rev().collect();

        let first = serde_json::to_string(&finalize_cases(first, &Some(quota.clone()))).unwrap();
        let second = serde_json::to_string(&finalize_cases(second, &Some(quota))).unwrap();

        assert_eq!(first, second);
    }

    #[cfg(feature = "itrace")]
    #[test]
    fn clause_itrace_output_path_appends_clause_suffix() {
        let base = PathBuf::from("output/itrace.txt");
        let result = clause_itrace_output_path(&base, "zadd");
        assert_eq!(result, PathBuf::from("output/itrace_zadd.txt"));
    }

    #[cfg(feature = "itrace")]
    #[test]
    fn clause_itrace_output_path_preserves_directory() {
        let base = PathBuf::from("/tmp/deep/dir/trace.log");
        let result = clause_itrace_output_path(&base, "zlw");
        assert_eq!(result, PathBuf::from("/tmp/deep/dir/trace_zlw.log"));
    }

    #[cfg(feature = "itrace")]
    #[test]
    fn clause_itrace_output_path_handles_no_extension() {
        let base = PathBuf::from("output/itrace");
        let result = clause_itrace_output_path(&base, "zsub");
        assert_eq!(result, PathBuf::from("output/itrace_zsub.txt"));
    }
}
