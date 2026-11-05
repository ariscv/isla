//! 合并记录与 JSON Lines 输出。未开启输出时不进行依赖分析。
use super::*;
use crate::ir::regions::RegionPoint;
use crate::primop::Effect;

static PATH: std::sync::OnceLock<Option<std::path::PathBuf>> = std::sync::OnceLock::new();

/// 由 TaskState::new 在执行开始前调用，之后不再读取环境变量。
pub(super) fn initialize() {
    PATH.get_or_init(|| std::env::var_os("ISLA_MERGE_RECORDS").map(std::path::PathBuf::from));
}
pub(super) fn enabled() -> bool {
    initialize();
    PATH.get().unwrap().is_some()
}

#[cfg(test)]
pub(super) static DEPENDENCY_SCANS: AtomicUsize = AtomicUsize::new(0);

/// 主迹的寄存器读取只保证前置状态/访问足迹可信；需要逐条精确读写顺序时不可信。
/// 单臂读取保留其条件，后续记录输出可据此恢复精确路径。
#[derive(Clone, Debug)]
pub struct GuardedRegisterRead<B> {
    pub register: Name,
    pub accessor: Vec<Accessor>,
    pub value: Val<B>,
    pub guard: smtlib::Exp<Sym>,
}

#[derive(Clone, Debug)]
pub struct RegionMergeRecord<B> {
    pub function: Name,
    pub branch_pc: usize,
    pub join: RegionPoint,
    pub condition: Sym,
    pub source_loc: SourceLoc,
    pub depth: usize,
    /// 两臂都死亡时没有存活合并值，但剪枝本身仍是一次成功提交。
    pub dead: bool,
    /// 合并值中的符号；最外层提交后展开 DefineConst 依赖，得到自由输入。
    pub value_symbols: HashSet<Sym>,
    /// 仅输出开启时计算；关闭时保留空集，避免扫描完整执行迹。
    pub input_symbols: HashSet<Sym>,
    pub single_arm_reads: Vec<GuardedRegisterRead<B>>,
}

pub(super) fn publish<B: BV>(
    records: &mut [RegionMergeRecord<B>],
    pure_definitions: &[(u32, u32)],
    task_id: TaskId,
    shared: &SharedState<B>,
    solver: &Solver<B>,
) {
    if !enabled() {
        return;
    }
    #[cfg(test)]
    DEPENDENCY_SCANS.fetch_add(1, Ordering::Relaxed);
    let mut events = solver.trace().to_vec();
    let fresh: HashSet<_> = events
        .iter()
        .filter_map(|event| match event {
            Event::Smt(Def::DeclareConst(symbol, _), _, _) => Some(*symbol),
            _ => None,
        })
        .collect();
    // pow_int 等纯计算用 DeclareConst + 等式共享中间结果；按 I1 协议
    // 解开 guard 后把定义依赖交给已有 EventReferences 展开。
    let pure_ranges = pure_definitions;
    let mut equations = Vec::new();
    let mut derived = HashSet::new();
    for event in &events {
        if let Event::Smt(Def::Assert(exp), attributes, location) = event {
            let mut exp = exp;
            while let smtlib::Exp::Or(left, right) = exp {
                if matches!(left.as_ref(), smtlib::Exp::Not(_)) {
                    exp = right;
                } else {
                    break;
                }
            }
            if let smtlib::Exp::Eq(left, right) = exp {
                if let smtlib::Exp::Var(symbol) = left.as_ref() {
                    if fresh.contains(symbol)
                        && pure_ranges.iter().any(|(start, end)| *start < symbol.id && symbol.id < *end)
                        && !right.variables().contains(symbol)
                    {
                        derived.insert(*symbol);
                        equations.push(Event::Smt(
                            Def::DefineConst(*symbol, right.as_ref().clone()),
                            *attributes,
                            *location,
                        ));
                    }
                }
            }
        }
    }
    events.extend(equations.iter());
    let references = crate::simplify::EventReferences::from_events(&events);
    let declared: HashSet<_> = events
        .iter()
        .filter_map(|event| match event {
            Event::Smt(Def::DeclareConst(symbol, _), _, _) => Some(*symbol),
            _ => None,
        })
        .collect();
    for record in records.iter_mut() {
        record.input_symbols = record
            .value_symbols
            .iter()
            .flat_map(|symbol| references.dependencies(*symbol))
            .filter(|symbol| declared.contains(symbol) && !derived.contains(symbol))
            .collect();
    }
    emit_records(records, task_id, shared, solver);
}

/// 进程内唯一写端：先完整序列化，再持锁追加整行；不依赖进程退出时析构刷新。
/// 两个入口共用真实执行器，因此环境变量在两处均生效。
fn emit_records<B: BV>(records: &[RegionMergeRecord<B>], task_id: TaskId, shared: &SharedState<B>, solver: &Solver<B>) {
    use serde_json::json;
    use std::io::Write;
    static OUTPUT: std::sync::OnceLock<Mutex<std::fs::File>> = std::sync::OnceLock::new();
    static NEXT_RECORD: AtomicUsize = AtomicUsize::new(0);
    let path = PATH.get().expect("任务启动时必须缓存记录配置").as_ref().expect("发布记录必须已开启输出");
    let output = OUTPUT.get_or_init(|| {
        Mutex::new(
            std::fs::OpenOptions::new().create(true).append(true).open(path).expect("打开 ISLA_MERGE_RECORDS 失败"),
        )
    });
    let types: HashMap<_, _> = solver
        .trace()
        .to_vec()
        .iter()
        .filter_map(|event| match event {
            Event::Smt(Def::DeclareConst(symbol, ty), _, _) => Some((*symbol, ty.clone())),
            _ => None,
        })
        .collect();
    fn type_json(ty: &smtlib::Ty, symtab: &Symtab) -> serde_json::Value {
        match ty {
            smtlib::Ty::Bool => json!({"kind":"bool"}),
            smtlib::Ty::BitVec(width) => json!({"kind":"bitvector", "width":width}),
            smtlib::Ty::Enum(id) => json!({"kind":"enum", "name":zencode::decode(symtab.to_str(id.to_name()))}),
            smtlib::Ty::Array(domain, range) => {
                json!({"kind":"array", "domain":type_json(domain, symtab), "range":type_json(range, symtab)})
            }
            smtlib::Ty::Float(exponent, significand) => {
                json!({"kind":"float", "exponent":exponent, "significand":significand})
            }
            smtlib::Ty::RoundingMode => json!({"kind":"rounding_mode"}),
        }
    }
    let symbol_json = |symbol: Sym, ty: &smtlib::Ty| {
        json!({
            "name":format!("v{}", symbol.id), "smt_id":symbol.id, "type":type_json(ty, &shared.symtab)
        })
    };
    for record in records {
        let mut inputs: Vec<_> = record.input_symbols.iter().copied().collect();
        inputs.sort_by_key(|symbol| symbol.id);
        let inputs: Vec<_> = inputs
            .into_iter()
            .map(|symbol| symbol_json(symbol, types.get(&symbol).expect("自由输入必须有声明类型")))
            .collect();
        let reads: Vec<_> = record
            .single_arm_reads
            .iter()
            .map(|read| {
                let mut symbols: Vec<_> = read.guard.variables().into_iter().collect();
                symbols.sort_by_key(|symbol| symbol.id);
                let symbols: Vec<_> =
                    symbols.into_iter().map(|symbol| symbol_json(symbol, &smtlib::Ty::Bool)).collect();
                let accessor: Vec<_> =
                    read.accessor.iter().map(|accessor| accessor.to_string(&shared.symtab)).collect();
                // 复用现有 SMT-LIB 输出器，变量名与记录中的 vN 一致，不能使用 Z3 的 k!N 内部名。
                let event = Event::<B>::Smt(Def::Assert(read.guard.clone()), DefAttrs::default(), record.source_loc);
                let mut expression = Vec::new();
                crate::simplify::write_events_with_opts(
                    &mut expression,
                    &[event],
                    shared,
                    &crate::simplify::WriteOpts::smtlib(),
                )
                .expect("保护条件必须可写为 SMT-LIB");
                let expression = String::from_utf8(expression).expect("SMT-LIB 必须是 UTF-8");
                let expression = expression.trim().strip_prefix("(assert ").unwrap().strip_suffix(')').unwrap();
                json!({"register":zencode::decode(shared.symtab.to_str(read.register)), "accessor":accessor,
                "value":read.value.to_string(shared), "guard":{"expression":expression, "symbols":symbols}})
            })
            .collect();
        let join = match record.join {
            RegionPoint::Instruction(pc) => json!({"instruction":pc}),
            RegionPoint::FunctionExit => json!({"function_exit":true}),
        };
        let record_id = NEXT_RECORD
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .expect("合并记录编号溢出");
        let value = json!({"schema_version":1, "record_id":record_id, "task_id":task_id.as_usize(),
            "function":zencode::decode(shared.symtab.to_str(record.function)), "branch_pc":record.branch_pc, "join":join,
            "source_loc":record.source_loc, "location":record.source_loc.location_string(shared.symtab.files()),
            "condition":symbol_json(record.condition, &smtlib::Ty::Bool), "input_symbols":inputs,
            "single_arm_reads":reads, "depth":record.depth, "outcome":if record.dead { "dead" } else { "merged" }});
        let mut line = serde_json::to_vec(&value).expect("合并记录必须可序列化");
        line.push(b'\n');
        output.lock().unwrap().write_all(&line).expect("写入 ISLA_MERGE_RECORDS 失败");
    }
}

/// 给纯原语生成的声明划定符号区间，区分定义等式和 assume 对已有输入的约束。
/// fresh 只预留编号，不声明变量；因此不会改变 SMT 状态，也无需新的求解器接口。
/// 普通执行可使用未注册的自定义函数指针，此时不记录纯定义；推演预检仍要求分类。
pub(super) fn evaluate_primop<'ir, B: BV>(
    frame: &mut LocalFrame<'ir, B>,
    solver: &mut Solver<B>,
    effect: Option<Effect>,
    evaluate: impl FnOnce(&mut Solver<B>, &mut LocalFrame<'ir, B>) -> Result<Val<B>, ExecError>,
) -> Result<Val<B>, ExecError> {
    let start = if enabled() && effect == Some(Effect::Pure) { Some(solver.fresh()) } else { None };
    let result = evaluate(solver, frame);
    if let Some(start) = start {
        let end = solver.fresh();
        frame.local_state.pure_definitions.push((start.id, end.id));
    }
    result
}
