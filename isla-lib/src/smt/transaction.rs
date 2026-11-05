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
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    pub fn transaction_depth(&self) -> usize {
        self.savepoints.len()
    }

    pub fn start_transaction(&mut self) -> SolverTransaction {
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
            self.last_committed_transaction = None;
        }
        if let Some(model) = self.stashed_model {
            unsafe { Z3_model_inc_ref(self.ctx.z3_ctx, model) };
        }
        // next_var 不回退：符号已经交给调用方，复用编号会让旧值错误引用新定义。
        // 枚举 sort 是 Context 的全局注册状态，不能撤销；其定义在回滚时仍须可重放。
        // z3_solver/ctx/symbol_namer 不变，迹在活动保存点期间不发布也不能建检查点。
        // 完整复制符号表也覆盖对已有 Sym 的重定义，不能只删除新鲜编号区间。
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
            condition_depth: self.condition_depth,
        });
        token
    }

    pub fn rollback_transaction(&mut self, tx: SolverTransaction) {
        let savepoint = self.savepoints.last().expect("没有可回滚的保存点");
        assert_eq!(savepoint.token, tx, "必须回滚当前求解器最内层的保存点");
        assert_eq!(self.condition_depth, savepoint.condition_depth, "不能在尚未退出的臂条件内结束保存点");
        assert_eq!(self.trace.head.len(), tx.head_len, "保存点期间不能改写已发布的迹");
        let mut savepoint = self.savepoints.pop().unwrap();
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
            .filter(|event| matches!(event, Event::Smt(Def::DefineEnum(..), ..)))
            .collect();
        self.transaction_events.extend(enums);
        if self.savepoints.is_empty() {
            self.trace.head.append(&mut self.transaction_events);
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
        self.condition_depth += 1;
        let depth = self.transaction_depth();
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
        unsafe { Z3_solver_pop(self.ctx.z3_ctx, self.z3_solver, 1) };
        self.condition_depth -= 1;
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
        assert_eq!(self.condition_depth, savepoint.condition_depth, "不能在尚未退出的臂条件内结束保存点");
        assert_eq!(self.trace.head.len(), savepoint.token.head_len, "保存点期间不能改写已发布的迹");
        let savepoint = self.savepoints.pop().unwrap();
        if self.savepoints.is_empty() {
            self.trace.head.append(&mut self.transaction_events);
            self.last_committed_transaction = Some((savepoint.token, self.trace.head.len()));
        }
        // 内层提交只移除保存点，定义、全部事件与统计留在父层；父层回滚仍可完整撤销。
    }

    /// 仅最外层可重排读取；内层调用直接拒绝，避免改变父层缓冲偏移。
    /// 同时保留旧执行器在提交后补发合并寄存器事件、再调用此方法的契约。
    pub(crate) fn order_transaction_register_reads(&mut self, tx: SolverTransaction) {
        assert_eq!(tx.depth, 1, "内层保存点不能重排读取事件");
        let (events, start) = if let Some(savepoint) = self.savepoints.last() {
            assert_eq!(self.transaction_depth(), 1, "嵌套期间不能重排读取事件");
            assert_eq!(savepoint.token, tx, "只能重排当前最外层保存点");
            (&mut self.transaction_events, savepoint.events_len)
        } else {
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
            (&mut self.trace.head, tx.head_len)
        };
        // 非 SMT 事件是顺序屏障。读取只能越过 SMT 定义，并且必须位于所用符号定义之后。
        let mut position = start;
        for index in start..events.len() {
            if let Event::ReadReg(_, _, value) = &events[index] {
                let symbols = value.symbolic_variables();
                let base = position;
                for (offset, definition) in events[base..index].iter().enumerate() {
                    if let Event::Smt(Def::DeclareConst(sym, _) | Def::DefineConst(sym, _), _, _) = definition {
                        if symbols.contains(sym) {
                            position = base + offset + 1;
                        }
                    }
                }
                let event = events.remove(index);
                events.insert(position, event);
                position += 1;
            } else if !matches!(&events[index], Event::Smt(..)) {
                position = index + 1;
            }
        }
    }
}
