//! 求解器保存点及旧单层事务接口。日志共用一个缓冲，各层只保存起始偏移。
use super::*;
use std::sync::atomic::{AtomicU64, Ordering};

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
    floating_point_seen: bool,
    last_check_sat: bool,
    pub(super) knowledge: dedup::Knowledge,
    model: SavedModel<'ctx>,
    performance_info: PerformanceInfo,
    smt_stats: crate::timeout::SmtCallStats,
    condition_depth: usize,
    guard: Option<Exp<Sym>>,
    order_register_reads: bool,
    deferred_obligations_len: usize,
    deferred_input_facts_len: usize,
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    /// 仅显式探针读取：断言树节点与保存点表项，不建快照、不翻译表达式、不查询。
    pub(crate) fn probe_transaction_snapshot(&self) -> serde_json::Value {
        let mut count = 0;
        let mut prefix = Vec::new();
        for (index, event) in self.transaction_events.iter().enumerate() {
            if let Event::Smt(Def::Assert(exp), _, location) = event {
                count += 1;
                if prefix.len() < 4096 {
                    prefix.push(serde_json::json!({"event_index":index,
                        "nodes":crate::executor::stats::memory_stats::exp_stats(exp).0,
                        "source":location}));
                }
            }
        }
        serde_json::json!({"savepoint_count":self.savepoints.len(),
            "native_condition_scopes":unsafe { Z3_solver_get_num_scopes(self.ctx.z3_ctx, self.z3_solver) },
            "saved_decl_entries":self.savepoints.iter().map(|s|s.decls.len()).sum::<usize>(),
            "saved_function_entries":self.savepoints.iter().map(|s|s.func_decls.len()).sum::<usize>(),
            "saved_assert_counters":self.savepoints.iter().map(|s|s.asserts_since_check).sum::<usize>(),
            "buffered_event_count":self.transaction_events.len(),"buffered_assertion_count":count,
            "omitted_assertions":count-prefix.len(),"prefix_assertions":prefix})
    }

    fn lazy_condition_scopes(&self) -> bool {
        self.deferred_region_queries && crate::config::RegionOptions::current().lazy_z3_scope
    }

    pub fn transaction_depth(&self) -> usize {
        self.savepoints.len()
    }

    /// 在保存点内用同一 Context、同一断言集做只读增量查询。
    /// tactic solver 每次查询可能重新执行预处理；计数 DFS 需要复用查询间的学习结果。
    /// 现有构造接口不能临时切换后端，因此在此资源边界配对替换、恢复 solver。
    pub(crate) fn with_incremental_checks<T>(&mut self, query: impl FnOnce(&mut Self) -> T) -> T {
        assert!(self.transaction_depth() > 0, "增量查询必须位于保存点内");
        let original = self.z3_solver;
        let was_incremental = self.incremental_checks;
        self.incremental_checks = true;
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
        self.incremental_checks = was_incremental;
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
        let cost_scope = crate::executor::stats::region_cost::Scope::enter(
            crate::executor::stats::region_cost::Category::EventBuffer,
        );
        let _ = &cost_scope;

        // 先翻译，非法符号不能留下半初始化的保存点或 Z3 scope。
        let condition = guard.as_ref().map(|exp| self.translate_exp(exp));
        let lazy = self.lazy_condition_scopes();
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
        {
            let snapshot_scope = crate::executor::stats::region_cost::Scope::enter(
                crate::executor::stats::region_cost::Category::Savepoint,
            );
            let _ = &snapshot_scope;
            if crate::executor::stats::region_cost::enabled() {
                let entries = self.decls.len() + self.sail_bitvectors.len() + self.func_decls.len();
                let bytes = self.decls.capacity() * std::mem::size_of::<(Sym, Ast<'ctx>)>()
                    + self.sail_bitvectors.capacity() * std::mem::size_of::<Sym>()
                    + self.func_decls.capacity() * std::mem::size_of::<(Sym, FuncDecl<'ctx>)>();
                crate::executor::stats::region_cost::count(
                    crate::executor::stats::region_cost::Category::Savepoint,
                    entries,
                    bytes,
                );
            }
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
                floating_point_seen: self.floating_point_seen.get(),
                last_check_sat: self.last_check_sat,
                knowledge: self.knowledge,
                model: SavedModel { model: self.stashed_model, ctx: self.ctx },
                performance_info: self.performance_info.clone(),
                smt_stats: path_smt_stats(),
                condition_depth: self.transaction_conditions.len(),
                guard,
                order_register_reads: false,
                deferred_input_facts_len: self.deferred_assertions.as_ref().map_or(0, |state| state.input_facts.len()),
                deferred_obligations_len: self.deferred_assertions.as_ref().map_or(0, |state| state.obligations.len()),
            });
        }
        if let Some(condition) = condition {
            let sat = self.guard_known_sat(self.savepoints.last().unwrap().guard.as_ref().unwrap());
            self.knowledge.change();
            self.knowledge.sat = sat;
            self.clear_stashed_model();
            self.last_check_sat = false;
            if !lazy {
                unsafe {
                    let native_scope = crate::executor::stats::region_cost::Scope::enter(
                        crate::executor::stats::region_cost::Category::NativeScope,
                    );
                    let _ = &native_scope;

                    Z3_solver_push(self.ctx.z3_ctx, self.z3_solver);
                    crate::executor::stats::region_cost::count(
                        crate::executor::stats::region_cost::Category::ReplayAssert,
                        1,
                        0,
                    );
                    Z3_solver_assert(self.ctx.z3_ctx, self.z3_solver, condition.z3_ast);
                }
            }
            self.transaction_condition_scopes.push(if lazy { Some(condition) } else { None });
            self.transaction_conditions.push(self.savepoints.last().unwrap().guard.clone().unwrap());
        }
        token
    }

    pub fn rollback_transaction(&mut self, tx: SolverTransaction) {
        let cost_scope =
            crate::executor::stats::region_cost::Scope::enter(crate::executor::stats::region_cost::Category::Release);
        let _ = &cost_scope;
        if crate::executor::stats::region_cost::enabled() {
            crate::executor::stats::region_cost::count(
                crate::executor::stats::region_cost::Category::Release,
                self.decls.len() + self.func_decls.len() + self.sail_bitvectors.len(),
                self.decls.capacity() * std::mem::size_of::<(Sym, Ast<'ctx>)>(),
            );
        }

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
            if self.transaction_condition_scopes.pop().expect("条件作用域必须对齐").is_none() {
                unsafe {
                    let native_scope = crate::executor::stats::region_cost::Scope::enter(
                        crate::executor::stats::region_cost::Category::NativeScope,
                    );
                    let _ = &native_scope;
                    Z3_solver_pop(self.ctx.z3_ctx, self.z3_solver, 1)
                }
            }
            self.transaction_conditions.pop().unwrap();
        }
        self.clear_stashed_model();
        self.decls = savepoint.decls;
        self.sail_bitvectors = savepoint.sail_bitvectors;
        self.func_decls = savepoint.func_decls;
        self.def_attrs = savepoint.def_attrs;
        self.cycles = savepoint.cycles;
        self.asserts_since_check = savepoint.asserts_since_check;
        self.floating_point_seen.set(savepoint.floating_point_seen);
        self.last_check_sat = savepoint.last_check_sat;
        self.knowledge = savepoint.knowledge;
        self.stashed_model = savepoint.model.model.take();
        self.performance_info = savepoint.performance_info;
        if let Some(state) = &mut self.deferred_assertions {
            state.obligations.truncate(savepoint.deferred_obligations_len);
            state.input_facts.truncate(savepoint.deferred_input_facts_len);
        }
        restore_path_smt_stats(savepoint.smt_stats);
        // 只保留本层的全局枚举定义；内层回滚也不能提前发布到迹。
        let enums: Vec<_> = self
            .transaction_events
            .drain(savepoint.events_len..)
            .zip(self.transaction_event_guards.drain(savepoint.events_len..))
            .filter(|(event, _)| matches!(event, Event::Smt(Def::DefineEnum(..), ..)))
            .collect();
        self.logical_arms.truncate(savepoint.events_len);
        for (event, _) in enums {
            self.transaction_events.push(event);
            // 枚举 sort 是 Context 全局状态，不属于已回滚的分支臂。
            self.transaction_event_guards.push(None);
            self.logical_arms.record_global_event();
        }
        if self.savepoints.is_empty() {
            // 查询前缀只供活动区域复用；回滚后不能让辅助solver继续持有废弃AST。
            self.region_query = None;
            self.trace.head.append(&mut self.transaction_events);
            self.transaction_event_guards.clear();
            self.logical_arms.clear();
        }
    }

    pub fn transaction_invalid(&self) -> bool {
        self.savepoints.iter().any(|savepoint| savepoint.invalid)
    }

    /// 臂条件只在推演期间生效；正常返回、Err 返回及 panic 展开均配对 pop。
    pub(crate) fn with_transaction_condition<T>(&mut self, condition: &Exp<Sym>, f: impl FnOnce(&mut Self) -> T) -> T {
        let cost_scope =
            crate::executor::stats::region_cost::Scope::enter(crate::executor::stats::region_cost::Category::Guard);
        let _ = &cost_scope;
        assert!(!self.savepoints.is_empty(), "推测臂条件必须位于事务中");
        let deferred_ast = self.lazy_condition_scopes().then(|| self.translate_exp(condition));
        let native = deferred_ast.is_none();
        let saved = self.knowledge;
        // 暂时加入的臂条件不能使用调用者见证；纯定义范围退出后可归还它。
        // SavedModel接管同一引用，不复制模型；断言或改绑均会改变constraints版本。
        let mut caller_model = SavedModel { model: self.stashed_model.take(), ctx: self.ctx };
        let caller_last_check_sat = self.last_check_sat;
        let sat = self.guard_known_sat(condition);
        self.knowledge.change();
        self.knowledge.sat = sat;
        self.clear_stashed_model();
        self.last_check_sat = false;
        if native {
            unsafe {
                let native_scope = crate::executor::stats::region_cost::Scope::enter(
                    crate::executor::stats::region_cost::Category::NativeScope,
                );
                let _ = &native_scope;
                Z3_solver_push(self.ctx.z3_ctx, self.z3_solver)
            }
        }
        self.transaction_condition_scopes.push(deferred_ast);
        self.transaction_conditions.push(condition.clone());
        let depth = self.transaction_depth();
        let events_len = self.transaction_events.len();
        // 翻译条件也可能 panic，必须一并纳入清理范围。
        drop(cost_scope);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            if native {
                self.z3_assert(condition);
            }
            f(self)
        }));
        let cost_scope =
            crate::executor::stats::region_cost::Scope::enter(crate::executor::stats::region_cost::Category::Guard);
        let _ = &cost_scope;
        let balanced = self.transaction_depth() == depth;
        // panic 或遗漏结束内层保存点时，先在所属臂条件内撤销它们，避免恢复带已退出条件的模型。
        while self.transaction_depth() > depth {
            let token = self.savepoints.last().unwrap().token;
            self.rollback_transaction(token);
        }
        // 兼容旧执行器在同一个事务中依次推演两个臂：仅包装本次臂新增的事件，
        // 另一臂的查询因而只看到带条件的约束，定义则像以前一样跨 pop 保留。
        let unchanged = self.knowledge.constraints == saved.constraints;
        self.knowledge.sat = unchanged && (self.knowledge.sat || saved.sat);
        self.knowledge.change();
        self.guard_transaction_events(events_len, condition);
        if self.transaction_condition_scopes.pop().expect("条件作用域必须对齐").is_none() {
            unsafe {
                let native_scope = crate::executor::stats::region_cost::Scope::enter(
                    crate::executor::stats::region_cost::Category::NativeScope,
                );
                let _ = &native_scope;
                Z3_solver_pop(self.ctx.z3_ctx, self.z3_solver, 1)
            }
        }
        self.transaction_conditions.pop().unwrap();
        self.clear_stashed_model();
        self.last_check_sat = false;
        if unchanged && balanced && result.is_ok() {
            self.stashed_model = caller_model.model.take();
            self.last_check_sat = caller_last_check_sat && self.has_stashed_model();
        }
        match result {
            Ok(value) => {
                assert!(balanced, "退出臂条件前必须结束其内层保存点");
                value
            }
            Err(panic) => std::panic::resume_unwind(panic),
        }
    }

    pub fn commit_transaction(&mut self) {
        let cost_scope = crate::executor::stats::region_cost::Scope::enter(
            crate::executor::stats::region_cost::Category::EventBuffer,
        );
        let _ = &cost_scope;
        let savepoint = self.savepoints.last().expect("没有可提交的保存点");
        assert!(!self.transaction_invalid(), "不能提交失效的保存点");
        assert_eq!(
            self.transaction_conditions.len(),
            savepoint.condition_depth + usize::from(savepoint.guard.is_some()),
            "不能在尚未退出的臂条件内结束保存点"
        );
        assert_eq!(self.trace.head.len(), savepoint.token.head_len, "保存点期间不能改写已发布的迹");
        let savepoint = self.savepoints.pop().unwrap();
        let unchanged = self.knowledge.constraints == savepoint.knowledge.constraints;
        self.knowledge.sat = unchanged && (self.knowledge.sat || savepoint.knowledge.sat);
        self.knowledge.change();
        if let Some(guard) = &savepoint.guard {
            if self.transaction_condition_scopes.pop().expect("条件作用域必须对齐").is_none() {
                unsafe {
                    let native_scope = crate::executor::stats::region_cost::Scope::enter(
                        crate::executor::stats::region_cost::Category::NativeScope,
                    );
                    let _ = &native_scope;
                    Z3_solver_pop(self.ctx.z3_ctx, self.z3_solver, 1)
                }
            }
            self.transaction_conditions.pop().unwrap();
            self.guard_transaction_events(savepoint.events_len, guard);
            // 已缓存的模型满足全部前提、活动臂条件与缓冲断言。
            // 撤去 g 并把 c 改为 g→c 只会弱化约束，同一见证仍然有效。
        }
        if self.savepoints.is_empty() {
            // 最外层已提交，辅助solver的旧scope与学习状态不再属于活动区域。
            // 主solver和其模型各自持有引用；释放辅助资源不改变已提交约束。
            self.region_query = None;
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
            // 这些断言已经参与模型查询；新增 assert 本身会清除旧模型。
            // 提交只发布缓冲内容，不凭空恢复没有验证过的见证。
            for exp in assertions {
                self.z3_assert(&exp);
            }
            self.committed_transaction_events =
                self.transaction_event_guards.drain(..).zip(self.transaction_events.iter().cloned()).collect();
            self.trace.head.append(&mut self.transaction_events);
            self.last_committed_transaction = Some((savepoint.token, self.trace.head.len()));
            self.logical_arms.clear();
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
    /// 只读检查待提交前缀，不改变查询、见证或事务状态。
    pub(crate) fn transaction_has_memory_writes(&self) -> bool {
        self.transaction_events.iter().any(Event::is_memory_write)
    }

    pub fn committed_transaction_events(&self) -> &[(Option<Exp<Sym>>, Event<B>)] {
        &self.committed_transaction_events
    }

    fn guard_transaction_events(&mut self, start: usize, guard: &Exp<Sym>) {
        let cost_scope =
            crate::executor::stats::region_cost::Scope::enter(crate::executor::stats::region_cost::Category::Guard);
        let _ = &cost_scope;
        if crate::executor::stats::region_cost::enabled() {
            let diagnostic = crate::executor::stats::region_cost::Scope::enter(
                crate::executor::stats::region_cost::Category::Diagnostics,
            );
            let g = crate::executor::stats::memory_stats::exp_stats(guard).0;
            let mut nodes = g * (self.transaction_events.len() - start);
            for event in &self.transaction_events[start..] {
                if let Event::Smt(Def::Assert(exp), ..) = event {
                    nodes += g + crate::executor::stats::memory_stats::exp_stats(exp).0;
                }
            }
            crate::executor::stats::region_cost::count(
                crate::executor::stats::region_cost::Category::Guard,
                nodes,
                nodes * std::mem::size_of::<Exp<Sym>>(),
            );
            drop(diagnostic);
        }

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
        let cost_scope = crate::executor::stats::region_cost::Scope::enter(
            crate::executor::stats::region_cost::Category::ReplayAssert,
        );
        let _ = &cost_scope;
        let timer = WorkTimer::start(WorkKind::BufferTranslate);
        assert_eq!(self.transaction_conditions.len(), self.transaction_condition_scopes.len(), "条件作用域必须对齐");
        let assertions = self
            .transaction_events
            .iter()
            .filter_map(|event| match event {
                Event::Smt(Def::Assert(exp), ..) => Some(self.translate_exp(exp)),
                _ => None,
            })
            .chain(self.transaction_condition_scopes.iter().flatten().cloned())
            .collect();
        drop(timer);
        assertions
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

impl<B: BV> Solver<'_, B> {
    /// 各层真实 capacity 的 payload 估算；模型只数引用，不访问 Z3 opaque 对象。
    pub fn memory_stats(&self) -> crate::executor::stats::memory_stats::SolverMemory {
        use crate::executor::stats::memory_stats::{event_heap_bytes, exp_heap_bytes, map_bytes, SolverMemory};
        use std::mem::{size_of, size_of_val};
        let mut layers = vec![
            serde_json::json!({"layer":0,"decls_capacity":self.decls.capacity(),"sail_bitvectors_capacity":self.sail_bitvectors.capacity(),"func_decls_capacity":self.func_decls.capacity()}),
        ];
        let mut bytes = size_of_val(self)
            + map_bytes::<Sym, Ast>(self.decls.capacity())
            + self.sail_bitvectors.capacity() * size_of::<Sym>()
            + map_bytes::<Sym, FuncDecl>(self.func_decls.capacity());
        let mut models = usize::from(self.stashed_model.is_some());
        bytes += self.savepoints.capacity() * size_of::<SolverSavepoint>();
        for (index, point) in self.savepoints.iter().enumerate() {
            layers.push(serde_json::json!({"layer":index+1,"decls_capacity":point.decls.capacity(),"sail_bitvectors_capacity":point.sail_bitvectors.capacity(),"func_decls_capacity":point.func_decls.capacity()}));
            bytes += map_bytes::<Sym, Ast>(point.decls.capacity())
                + point.sail_bitvectors.capacity() * size_of::<Sym>()
                + map_bytes::<Sym, FuncDecl>(point.func_decls.capacity())
                + point.guard.as_ref().map_or(0, exp_heap_bytes);
            models += usize::from(point.model.model.is_some());
        }
        bytes += self.transaction_events.capacity() * size_of::<Event<B>>()
            + self.transaction_events.iter().map(event_heap_bytes).sum::<usize>()
            + self.logical_arms.heap_bytes()
            + self.transaction_event_guards.capacity() * size_of::<Option<Exp<Sym>>>()
            + self.transaction_event_guards.iter().flatten().map(exp_heap_bytes).sum::<usize>()
            + self.committed_transaction_events.capacity() * size_of::<(Option<Exp<Sym>>, Event<B>)>()
            + self
                .committed_transaction_events
                .iter()
                .map(|(g, e)| g.as_ref().map_or(0, exp_heap_bytes) + event_heap_bytes(e))
                .sum::<usize>()
            + self.transaction_condition_scopes.capacity() * size_of::<Option<Ast>>()
            + self.transaction_conditions.capacity() * size_of::<Exp<Sym>>()
            + self.transaction_conditions.iter().map(exp_heap_bytes).sum::<usize>();
        SolverMemory { bytes, layers, model_caches: models }
    }
}
