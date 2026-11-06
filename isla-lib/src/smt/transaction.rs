//! 求解器保存点及旧单层事务接口。日志共用一个缓冲，各层只保存起始偏移。
use super::*;
use std::sync::atomic::{AtomicU64, Ordering};

/// 完整快照的显式资源上限；达到上限仍可提交/回滚，新增一层则 panic。
pub const MAX_TRANSACTION_DEPTH: usize = 64;

static NEXT_TRANSACTION_ID: AtomicU64 = AtomicU64::new(0);

/// 事务句柄只用于定位保存点，必须按后进先出顺序回滚。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SolverTransaction {
    id: u64,
    depth: usize,
    pub(super) head_len: usize,
}

// 独立持有保存点的模型引用，提交、回滚以及带活动保存点销毁 Solver 都会正确释放。
struct SavedModel<'ctx> {
    model: Option<Z3_model>,
    ctx: &'ctx Context,
}

impl Drop for SavedModel<'_> {
    fn drop(&mut self) {
        if let Some(model) = self.model.take() {
            unsafe { Z3_model_dec_ref(self.ctx.z3_ctx, model) };
        }
    }
}

pub(super) struct SolverSavepoint<'ctx> {
    token: SolverTransaction,
    pub(super) events_len: usize,
    // 只表示不支持的操作；新层继承父层状态，普通断言不会置位。
    pub(super) invalid: bool,
    decls: HashMap<Sym, Ast<'ctx>>,
    sail_bitvectors: HashSet<Sym>,
    func_decls: HashMap<Sym, FuncDecl<'ctx>>,
    def_attrs: DefAttrs,
    cycles: i128,
    asserts_since_check: usize,
    last_check_sat: bool,
    model: SavedModel<'ctx>,
    performance_info: PerformanceInfo,
    smt_stats: crate::timeout::SmtCallStats,
    condition_depth: usize,
    guard: Option<Exp<Sym>>,
    order_register_reads: bool,
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    pub fn transaction_depth(&self) -> usize {
        self.savepoints.len()
    }

    /// 在保存点内用同一 Context、同一断言集做只读增量查询。
    /// tactic solver 每次查询可能重新执行预处理；计数 DFS 需要复用查询间的学习结果。
    /// 现有构造接口不能临时切换后端，因此在此资源边界配对替换、恢复 solver。
    pub(crate) fn with_incremental_checks<T>(&mut self, query: impl FnOnce(&mut Self) -> T) -> T {
        assert!(self.transaction_depth() > 0, "增量查询必须位于保存点内");
        let original = self.z3_solver;
        let model = self.stashed_model.take();
        let last_check_sat = self.last_check_sat;
        let asserts_since_check = self.asserts_since_check;
        let depth = self.transaction_depth();
        let events_len = self.transaction_events.len();
        unsafe {
            let incremental = Z3_mk_solver(self.ctx.z3_ctx);
            Z3_solver_inc_ref(self.ctx.z3_ctx, incremental);
            let assertions = Z3_solver_get_assertions(self.ctx.z3_ctx, original);
            Z3_ast_vector_inc_ref(self.ctx.z3_ctx, assertions);
            for index in 0..Z3_ast_vector_size(self.ctx.z3_ctx, assertions) {
                Z3_solver_assert(self.ctx.z3_ctx, incremental, Z3_ast_vector_get(self.ctx.z3_ctx, assertions, index));
            }
            Z3_ast_vector_dec_ref(self.ctx.z3_ctx, assertions);
            self.z3_solver = incremental;
        }
        self.last_check_sat = false;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| query(self)));
        self.clear_stashed_model();
        unsafe { Z3_solver_dec_ref(self.ctx.z3_ctx, self.z3_solver) };
        self.z3_solver = original;
        self.stashed_model = model;
        self.last_check_sat = last_check_sat;
        self.asserts_since_check = asserts_since_check;
        assert_eq!(self.transaction_depth(), depth, "增量查询不得遗留保存点");
        assert_eq!(self.transaction_events.len(), events_len, "增量查询不得修改执行迹");
        match result {
            Ok(value) => value,
            Err(panic) => std::panic::resume_unwind(panic),
        }
    }

    pub fn start_transaction(&mut self) -> SolverTransaction {
        self.start_transaction_with_guard(None)
    }

    /// 创建可嵌套的分支臂保存点。None 表示无条件层；Some(g) 在结束本层时配对 pop。
    pub fn start_transaction_with_guard(&mut self, guard: Option<Exp<Sym>>) -> SolverTransaction {
        assert!(
            self.transaction_depth() < MAX_TRANSACTION_DEPTH,
            "保存点嵌套深度超过上限 {}（当前 {}）",
            MAX_TRANSACTION_DEPTH,
            self.transaction_depth()
        );
        // 先翻译，非法符号不能留下半初始化的保存点或 Z3 scope。
        let condition = guard.as_ref().map(|exp| self.translate_exp(exp));
        let token = SolverTransaction {
            // 全局唯一编号也能拒绝已销毁求解器的旧句柄，且不引入裸指针的 Send/Sync 限制。
            id: NEXT_TRANSACTION_ID
                .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
                .expect("保存点编号溢出"),
            depth: self.transaction_depth() + 1,
            head_len: self.trace.head.len(),
        };
        if self.savepoints.is_empty() {
            assert!(self.transaction_events.is_empty(), "保存点栈与缓冲必须同时清空");
            assert!(self.transaction_event_guards.is_empty(), "事件及其条件必须同时清空");
            self.last_committed_transaction = None;
            self.committed_transaction_events.clear();
        }
        if let Some(model) = self.stashed_model {
            unsafe { Z3_model_inc_ref(self.ctx.z3_ctx, model) };
        }
        // next_var 不回退：符号已经交给调用方，复用编号会让旧值错误引用新定义。
        // 枚举 sort 是 Context 的全局注册状态，不能撤销；其定义在回滚时仍须可重放。
        // z3_solver/ctx/symbol_namer 不变，迹在活动保存点期间不发布也不能建检查点。
        // 完整复制符号表也覆盖对已有 Sym 的重定义，不能只删除新鲜编号区间。
        // 每层复制符号表、函数表、位向量集合和性能图：时间/空间为当前状态规模，
        // 总成本随路径规模和嵌套深度增长。后续可改为逐项记录旧值的增量撤销日志，
        // 提交合并父层日志、回滚按逆序恢复；届时仍须处理已有 Sym 重定义和模型引用。
        self.savepoints.push(SolverSavepoint {
            token,
            events_len: self.transaction_events.len(),
            invalid: self.transaction_invalid(),
            decls: self.decls.clone(),
            sail_bitvectors: self.sail_bitvectors.clone(),
            func_decls: self.func_decls.clone(),
            def_attrs: self.def_attrs,
            cycles: self.cycles,
            asserts_since_check: self.asserts_since_check,
            last_check_sat: self.last_check_sat,
            model: SavedModel { model: self.stashed_model, ctx: self.ctx },
            performance_info: self.performance_info.clone(),
            smt_stats: path_smt_stats(),
            condition_depth: self.transaction_conditions.len(),
            guard,
            order_register_reads: false,
        });
        if let Some(condition) = condition {
            self.clear_stashed_model();
            self.last_check_sat = false;
            unsafe {
                Z3_solver_push(self.ctx.z3_ctx, self.z3_solver);
                Z3_solver_assert(self.ctx.z3_ctx, self.z3_solver, condition.z3_ast);
            }
            self.transaction_conditions.push(self.savepoints.last().unwrap().guard.clone().unwrap());
        }
        token
    }

    pub fn rollback_transaction(&mut self, tx: SolverTransaction) {
        let savepoint = self.savepoints.last().expect("没有可回滚的保存点");
        assert_eq!(savepoint.token, tx, "必须回滚当前求解器最内层的保存点");
        assert_eq!(
            self.transaction_conditions.len(),
            savepoint.condition_depth + usize::from(savepoint.guard.is_some()),
            "不能在尚未退出的臂条件内结束保存点"
        );
        assert_eq!(self.trace.head.len(), tx.head_len, "保存点期间不能改写已发布的迹");
        let mut savepoint = self.savepoints.pop().unwrap();
        if savepoint.guard.is_some() {
            unsafe { Z3_solver_pop(self.ctx.z3_ctx, self.z3_solver, 1) };
            self.transaction_conditions.pop().unwrap();
        }
        self.clear_stashed_model();
        self.decls = savepoint.decls;
        self.sail_bitvectors = savepoint.sail_bitvectors;
        self.func_decls = savepoint.func_decls;
        self.def_attrs = savepoint.def_attrs;
        self.cycles = savepoint.cycles;
        self.asserts_since_check = savepoint.asserts_since_check;
        self.last_check_sat = savepoint.last_check_sat;
        self.stashed_model = savepoint.model.model.take();
        self.performance_info = savepoint.performance_info;
        restore_path_smt_stats(savepoint.smt_stats);
        // 只保留本层的全局枚举定义；内层回滚也不能提前发布到迹。
        let enums: Vec<_> = self
            .transaction_events
            .drain(savepoint.events_len..)
            .zip(self.transaction_event_guards.drain(savepoint.events_len..))
            .filter(|(event, _)| matches!(event, Event::Smt(Def::DefineEnum(..), ..)))
            .collect();
        for (event, _) in enums {
            self.transaction_events.push(event);
            // 枚举 sort 是 Context 全局状态，不属于已回滚的分支臂。
            self.transaction_event_guards.push(None);
        }
        if self.savepoints.is_empty() {
            self.trace.head.append(&mut self.transaction_events);
            self.transaction_event_guards.clear();
        }
    }

    pub fn transaction_invalid(&self) -> bool {
        self.savepoints.iter().any(|savepoint| savepoint.invalid)
    }

    /// 臂条件只在推演期间生效；正常返回、Err 返回及 panic 展开均配对 pop。
    pub(crate) fn with_transaction_condition<T>(&mut self, condition: &Exp<Sym>, f: impl FnOnce(&mut Self) -> T) -> T {
        assert!(!self.savepoints.is_empty(), "推测臂条件必须位于事务中");
        self.clear_stashed_model();
        self.last_check_sat = false;
        unsafe { Z3_solver_push(self.ctx.z3_ctx, self.z3_solver) };
        self.transaction_conditions.push(condition.clone());
        let depth = self.transaction_depth();
        let events_len = self.transaction_events.len();
        // 翻译条件也可能 panic，必须一并纳入清理范围。
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.z3_assert(condition);
            f(self)
        }));
        let balanced = self.transaction_depth() == depth;
        // panic 或遗漏结束内层保存点时，先在所属臂条件内撤销它们，避免恢复带已退出条件的模型。
        while self.transaction_depth() > depth {
            let token = self.savepoints.last().unwrap().token;
            self.rollback_transaction(token);
        }
        // 兼容旧执行器在同一个事务中依次推演两个臂：仅包装本次臂新增的事件，
        // 另一臂的查询因而只看到带条件的约束，定义则像以前一样跨 pop 保留。
        self.guard_transaction_events(events_len, condition);
        unsafe { Z3_solver_pop(self.ctx.z3_ctx, self.z3_solver, 1) };
        self.transaction_conditions.pop().unwrap();
        self.clear_stashed_model();
        self.last_check_sat = false;
        match result {
            Ok(value) => {
                assert!(balanced, "退出臂条件前必须结束其内层保存点");
                value
            }
            Err(panic) => std::panic::resume_unwind(panic),
        }
    }

    pub fn commit_transaction(&mut self) {
        let savepoint = self.savepoints.last().expect("没有可提交的保存点");
        assert!(!self.transaction_invalid(), "不能提交失效的保存点");
        assert_eq!(
            self.transaction_conditions.len(),
            savepoint.condition_depth + usize::from(savepoint.guard.is_some()),
            "不能在尚未退出的臂条件内结束保存点"
        );
        assert_eq!(self.trace.head.len(), savepoint.token.head_len, "保存点期间不能改写已发布的迹");
        let savepoint = self.savepoints.pop().unwrap();
        if let Some(guard) = &savepoint.guard {
            unsafe { Z3_solver_pop(self.ctx.z3_ctx, self.z3_solver, 1) };
            self.transaction_conditions.pop().unwrap();
            self.guard_transaction_events(savepoint.events_len, guard);
            // pop 或把 c 换成 g→c 都会改变查询上下文，臂内模型不能继续使用。
            self.clear_stashed_model();
            self.last_check_sat = false;
        }
        if self.savepoints.is_empty() {
            if savepoint.order_register_reads {
                order_register_reads(&mut self.transaction_events, &mut self.transaction_event_guards, 0);
            }
            // 定义已在符号表中跨 pop 保留；只把缓冲的断言重放到 Z3。
            // 内层不写 Z3，由父层再次包装，所以得到 g1→(g2→c)。
            // 断言计数和性能记录在入缓冲时已更新，重放不再次记账。
            let assertions: Vec<_> = self
                .transaction_events
                .iter()
                .filter_map(|event| match event {
                    Event::Smt(Def::Assert(exp), ..) => Some(exp.clone()),
                    _ => None,
                })
                .collect();
            if !assertions.is_empty() {
                self.clear_stashed_model();
                self.last_check_sat = false;
            }
            for exp in assertions {
                self.z3_assert(&exp);
            }
            self.committed_transaction_events =
                self.transaction_event_guards.drain(..).zip(self.transaction_events.iter().cloned()).collect();
            self.trace.head.append(&mut self.transaction_events);
            self.last_committed_transaction = Some((savepoint.token, self.trace.head.len()));
        }
        // 内层提交保留定义、带条件事件与统计；父层回滚仍可完整撤销。
    }

    /// 提交已判死的臂：撤销本层全部状态，仅向父层加入 g→false。
    /// None 的死臂意味着当前父路径不可满足；调用方负责证明死亡，Unknown 不能当作 Unsat。
    pub fn commit_dead_transaction(&mut self) {
        assert!(!self.transaction_invalid(), "不能提交失效的保存点");
        let savepoint = self.savepoints.last().expect("没有可提交的保存点");
        let token = savepoint.token;
        let guard = savepoint.guard.clone();
        self.rollback_transaction(token);
        let constraint = match &guard {
            Some(g) => Exp::Not(Box::new(g.clone())),
            None => Exp::Bool(false),
        };
        self.assert(constraint);
        if self.savepoints.is_empty() {
            self.committed_transaction_events =
                self.trace.head[token.head_len..].iter().cloned().map(|event| (None, event)).collect();
            self.committed_transaction_events.last_mut().unwrap().0 = guard;
            self.last_committed_transaction = Some((token, self.trace.head.len()));
        } else {
            *self.transaction_event_guards.last_mut().unwrap() = guard;
        }
    }

    /// 最近一次最外层提交在发布时的带条件事件快照，供合并记录读取。
    /// 主迹仍按访问足迹并集发布；快照不受旧执行器提交后替换寄存器事件的影响。
    /// 开始下一个最外层事务或发布检查点时清空；嵌套条件以合取表示。
    /// SMT 声明与定义仍无条件生效，其事件 guard 只记录分支来源。
    pub fn committed_transaction_events(&self) -> &[(Option<Exp<Sym>>, Event<B>)] {
        &self.committed_transaction_events
    }

    fn guard_transaction_events(&mut self, start: usize, guard: &Exp<Sym>) {
        assert_eq!(self.transaction_events.len(), self.transaction_event_guards.len(), "事件条件必须对齐");
        for (event, condition) in
            self.transaction_events[start..].iter_mut().zip(&mut self.transaction_event_guards[start..])
        {
            if let Event::Smt(Def::Assert(exp), ..) = event {
                // 现有 Exp 没有 Implies；¬g∨c 与 g→c 等价，不新增全局表达式变体。
                *exp = Exp::Or(Box::new(Exp::Not(Box::new(guard.clone()))), Box::new(exp.clone()));
            }
            *condition = Some(match condition.take() {
                Some(inner) => Exp::And(Box::new(guard.clone()), Box::new(inner)),
                None => guard.clone(),
            });
        }
    }

    /// 查询所有尚未发布的断言。AST 必须存活到 Z3 check 返回，不能只收集裸指针。
    pub(super) fn transaction_assertions(&self) -> Vec<Ast<'ctx>> {
        self.transaction_events
            .iter()
            .filter_map(|event| match event {
                Event::Smt(Def::Assert(exp), ..) => Some(self.translate_exp(exp)),
                _ => None,
            })
            .collect()
    }

    /// 内层整理请求无副作用：只追加事件，不修改父层偏移，也不提前跨臂移动读取。
    /// 最外层提交前的请求延迟到发布时执行；内层调用方在最外层另行请求整理。
    /// 同时保留旧执行器在提交后补发合并寄存器事件、再调用此方法的契约。
    pub(crate) fn order_transaction_register_reads(&mut self, tx: SolverTransaction) {
        if tx.depth != 1 {
            return;
        }
        if let Some(savepoint) = self.savepoints.first_mut() {
            assert_eq!(savepoint.token, tx, "只能重排当前最外层保存点");
            savepoint.order_register_reads = true;
            return;
        }
        let (committed, published_end) = self.last_committed_transaction.expect("只能重排本求解器最近提交的事务");
        assert_eq!(committed, tx, "只能重排本求解器最近提交的最外层事务");
        // 旧执行器显式调用此整理口，用补发的合并读取替换两臂的原始读写，
        // 随后再补发合并写入。commit 出口本身始终发布全部缓冲事件。
        // 只清理本次提交区间的寄存器事件，保留其他事件和真正重复的合并读取。
        let published: Vec<_> = self
            .trace
            .head
            .drain(tx.head_len..published_end)
            .filter(|event| !matches!(event, Event::ReadReg(..) | Event::WriteReg(..)))
            .collect();
        self.trace.head.splice(tx.head_len..tx.head_len, published);
        self.last_committed_transaction = None;
        // 发布后的兼容整理不修改发布时快照；主迹的新增合并事件没有臂条件。
        let mut guards = vec![None; self.trace.head.len()];
        order_register_reads(&mut self.trace.head, &mut guards, tx.head_len);
    }
}

// 既有读取整理算法；事件条件随事件一起移动，不能只重排主缓冲。
fn order_register_reads<B: BV>(events: &mut Vec<Event<B>>, guards: &mut Vec<Option<Exp<Sym>>>, start: usize) {
    // 非 SMT 事件是顺序屏障。读取只能越过 SMT 定义，并且必须位于所用符号定义之后。
    let mut position = start;
    for index in start..events.len() {
        if let Event::ReadReg(_, _, value) = &events[index] {
            let mut symbols = value.symbolic_variables();
            if let Some(guard) = &guards[index] {
                // 带条件读取也使用 guard 的符号，不能越过其声明或定义。
                symbols.extend(guard.variables());
            }
            let base = position;
            for (offset, definition) in events[base..index].iter().enumerate() {
                if let Event::Smt(Def::DeclareConst(sym, _) | Def::DefineConst(sym, _), _, _) = definition {
                    if symbols.contains(sym) {
                        position = base + offset + 1;
                    }
                }
            }
            let event = events.remove(index);
            let guard = guards.remove(index);
            events.insert(position, event);
            guards.insert(position, guard);
            position += 1;
        } else if !matches!(&events[index], Event::Smt(..)) {
            position = index + 1;
        }
    }
}
