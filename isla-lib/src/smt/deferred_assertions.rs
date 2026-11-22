//! 区域断言按执行顺序先验证后假设；不使用自身、后续断言或正常退出域。
use super::*;
use std::collections::BTreeMap;

#[cfg(test)]
thread_local! {
    static TEST_MANDATORY_QUERY_COUNT: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_test_mandatory_query_count() {
    TEST_MANDATORY_QUERY_COUNT.with(|count| count.set(0));
}

#[cfg(test)]
pub(crate) fn test_mandatory_query_count() -> u64 {
    TEST_MANDATORY_QUERY_COUNT.with(std::cell::Cell::get)
}

pub(super) struct DeferredAssertions<B> {
    entry: Checkpoint<B>,
    event_start: usize,
    pub(super) obligations: Vec<Exp<Sym>>,
    pub(super) input_facts: Vec<Exp<Sym>>,
    exit_constraints: HashSet<Sym>,
    blocked: BTreeMap<&'static str, usize>,
    first_blocked: Option<SourceLoc>,
    verification_seconds: f64,
    verification_result: Option<String>,
}

impl<B: BV> Solver<'_, B> {
    /// 嵌套区域复用同一义务集合；作用域退出或panic时清理，不能泄漏到普通执行。
    pub(crate) fn with_deferred_region_queries<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let previous = self.deferred_region_queries;
        if !previous {
            assert!(self.deferred_assertions.is_none(), "上次区域的断言义务必须已清理");
            self.deferred_assertions = Some(DeferredAssertions {
                entry: self.checkpoint_snapshot(),
                event_start: self.transaction_events.len(),
                obligations: Vec::new(),
                input_facts: Vec::new(),
                exit_constraints: HashSet::new(),
                blocked: BTreeMap::new(),
                first_blocked: None,
                verification_seconds: 0.0,
                verification_result: None,
            });
        }
        self.deferred_region_queries = true;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(self)));
        self.deferred_region_queries = previous;
        if !previous {
            let state = self.deferred_assertions.take().expect("区域必须有义务上下文");
            static LOGGED: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
            if crate::executor::stats::region_progress::enabled()
                && (!state.obligations.is_empty() || !state.blocked.is_empty())
                && LOGGED.fetch_add(1, std::sync::atomic::Ordering::Relaxed) < 128
            {
                eprintln!(
                    "{}",
                    serde_json::json!({"kind":"region_deferred_exit",
                    "obligations":state.obligations.len(),"blocked_queries":state.blocked,
                    "first_blocked_source":state.first_blocked,"verification_seconds":state.verification_seconds,
                    "verification_result":state.verification_result,
                    "attempt":crate::executor::stats::merge_diagnostics::root_attempt()})
                );
            }
        }
        match result {
            Ok(value) => value,
            Err(error) => std::panic::resume_unwind(error),
        }
    }

    /// 根出口分治认证需要在延后义务仍可读取时查询候选。只临时恢复真实查询；
    /// 义务上下文、事务和后续登记均保持不变。
    pub(crate) fn suspend_deferred_region_queries<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        assert!(self.deferred_region_queries, "只能在延后区域认证期间暂停延后查询");
        self.deferred_region_queries = false;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(self)));
        self.deferred_region_queries = true;
        match result {
            Ok(value) => value,
            Err(error) => std::panic::resume_unwind(error),
        }
    }

    pub(crate) fn note_deferred_mandatory_query(
        &mut self,
        purpose: &'static str,
        info: SourceLoc,
        returns_unknown: bool,
    ) {
        #[cfg(test)]
        TEST_MANDATORY_QUERY_COUNT.with(|count| count.set(count.get() + u64::from(returns_unknown)));
        crate::executor::stats::merge_diagnostics::record_deferred_query(purpose, info, returns_unknown);
        let state = self.deferred_assertions.as_mut().expect("延迟查询必须属于活动区域");
        *state.blocked.entry(purpose).or_default() += 1;
        state.first_blocked.get_or_insert(info);
    }

    /// 范围与标签共用原到达域下的出口义务，未验证时不登记求解知识。
    pub(crate) fn defer_safety_check(
        &mut self,
        condition: &Exp<Sym>,
        enabled: bool,
        purpose: &'static str,
        info: SourceLoc,
    ) -> bool {
        if !self.deferred_region_queries || !enabled {
            return false;
        }
        self.note_deferred_mandatory_query(purpose, info, false);
        self.defer_assertion(condition.clone(), info);
        true
    }

    pub(crate) fn defer_assertion(&mut self, condition: Exp<Sym>, info: SourceLoc) {
        assert!(self.deferred_region_queries && !self.savepoints.is_empty(), "义务必须在延迟区域事务中记录");
        let guard = self
            .transaction_conditions
            .iter()
            .cloned()
            .fold(Exp::Bool(true), |a, b| Exp::And(Box::new(a), Box::new(b)));
        // 只取在本义务之前出现的断言；已提交的兄弟臂断言已带守卫。
        // 当前活动臂中的断言由本义务的完整guard限制，不能拿自己的c证明自己。
        let state = self.deferred_assertions.as_ref().unwrap();
        let mut preceding = Exp::Bool(true);
        for event in &self.transaction_events[state.event_start..] {
            if let Event::Smt(Def::Assert(exp), ..) = event {
                let mut exit = false;
                let _ = exp.map_var(&mut |v| {
                    exit |= state.exit_constraints.contains(v);
                    Ok::<_, ()>(Exp::Var(*v))
                });
                if !exit {
                    preceding = Exp::And(Box::new(preceding), Box::new(exp.clone()));
                }
            }
        }
        let prefix = self.define_const(preceding, info);
        let bad = self.define_const(
            Exp::And(
                Box::new(Exp::Var(prefix)),
                Box::new(Exp::And(Box::new(guard), Box::new(Exp::Not(Box::new(condition.clone()))))),
            ),
            info,
        );
        self.deferred_assertions.as_mut().unwrap().obligations.push(Exp::Var(bad));
        // 只供正常结果和后续义务使用；当前义务已在此之前冻结。
        self.assert(condition);
    }

    /// 首次符号化/提升初始值的类型域事实，与假设断言成功分开。
    pub(crate) fn assert_region_input_fact(&mut self, exp: Exp<Sym>) {
        if self.deferred_region_queries {
            let guard = self
                .transaction_conditions
                .iter()
                .cloned()
                .fold(Exp::Bool(true), |a, b| Exp::And(Box::new(a), Box::new(b)));
            self.deferred_assertions
                .as_mut()
                .unwrap()
                .input_facts
                .push(Exp::Or(Box::new(Exp::Not(Box::new(guard))), Box::new(exp.clone())));
        }
        self.assert(exp);
    }

    /// 正常出口域不能进入任何安全义务的前序前提。
    pub(crate) fn assert_region_exit(&mut self, exp: Exp<Sym>) {
        if self.deferred_region_queries {
            let marker = self.define_const(exp, SourceLoc::unknown());
            self.deferred_assertions.as_mut().unwrap().exit_constraints.insert(marker);
            self.assert(Exp::Var(marker));
        } else {
            self.assert(exp);
        }
    }

    pub(crate) fn region_definition_footprint(&self) -> serde_json::Value {
        let mut definitions = 0;
        let mut nodes = 0;
        let mut assertions = 0;
        for event in &self.transaction_events {
            match event {
                Event::Smt(Def::DefineConst(_, exp), ..) => {
                    definitions += 1;
                    nodes += crate::executor::stats::memory_stats::exp_stats(exp).0;
                }
                Event::Smt(Def::Assert(exp), ..) => {
                    assertions += crate::executor::stats::memory_stats::exp_stats(exp).0;
                }
                _ => (),
            }
        }
        serde_json::json!({"definition_events":definitions,"definition_expression_nodes":nodes,"assertion_expression_nodes":assertions,"obligations":self.deferred_assertions.as_ref().map_or(0,|s|s.obligations.len())})
    }

    /// 使用失败点的前缀认证错误，后续正常域的约束不参与检查。
    pub(crate) fn check_arm_error(
        &self,
        guard: Sym,
        point: &Checkpoint<B>,
        info: SourceLoc,
        queries: Option<&mut ArmErrorQueries<'_>>,
    ) -> Option<SmtResult> {
        if !self.validates_candidates() {
            return None;
        }
        let mut verifier = Solver::from_checkpoint(self.ctx, point.clone());
        let target = Exp::Var(guard);
        match queries {
            Some(queries) => Some(queries.check(&verifier, &target, info)),
            None => verifier.check_candidate_sat_with(&target, info),
        }
    }

    pub(crate) fn check_deferred_assertions(&mut self, info: SourceLoc) -> Option<SmtResult> {
        self.check_deferred_assertions_with(None, info)
    }

    /// `condition` 选择一组根出口臂。每项义务本身已经包含产生它的臂守卫，
    /// 因而该查询只认证此组，不能由兄弟臂的正常出口掩盖失败。
    pub(crate) fn check_deferred_assertions_with(
        &mut self,
        condition: Option<&Exp<Sym>>,
        info: SourceLoc,
    ) -> Option<SmtResult> {
        if !self.validates_candidates() {
            return None;
        }
        let state = self.deferred_assertions.as_ref().expect("验证必须在活动义务作用域中");
        if state.obligations.is_empty() {
            return Some(Unsat);
        }
        let started = Instant::now();
        let bad = state.obligations.iter().cloned().fold(Exp::Bool(false), |a, b| Exp::Or(Box::new(a), Box::new(b)));
        // 前序断言已经冻结到各自的bad定义中；此处仅重放定义和初始类型域。
        // 不再无条件加入所有正常结果断言，避免后续约束掩盖前面的错误。
        let mut definitions: Vec<_> = self.transaction_events[state.event_start..]
            .iter()
            .filter(|event| matches!(event,Event::Smt(def,..) if !matches!(def,Def::Assert(_))))
            .cloned()
            .collect();
        definitions.extend(
            state.input_facts.iter().cloned().map(|fact| Event::Smt(Def::Assert(fact), DefAttrs::default(), info)),
        );
        let diagnostic = crate::executor::stats::region_progress::enabled();
        let definition_nodes: usize = if diagnostic {
            definitions
                .iter()
                .filter_map(|e| match e {
                    Event::Smt(Def::DefineConst(_, exp), ..) => {
                        Some(crate::executor::stats::memory_stats::exp_stats(exp).0)
                    }
                    _ => None,
                })
                .sum()
        } else {
            0
        };
        let count = definitions.len();
        let trace = Arc::new(Some(Trace {
            checkpoints: state.entry.num,
            head: definitions,
            event_guards: Vec::new(),
            head_prefix: None,
            tail: state.entry.trace.clone(),
        }));
        let point = Checkpoint { num: state.entry.num + 1, next_var: self.next_var, trace, cycles: 0 };
        if diagnostic {
            eprintln!(
                "{}",
                serde_json::json!({"kind":"region_assert_obligation_start", "obligations":state.obligations.len(), "definition_events":count, "definition_expression_nodes":definition_nodes, "obligation_expression_nodes":crate::executor::stats::memory_stats::exp_stats(&bad).0})
            );
        }
        let replay_started = Instant::now();
        let mut verifier = Solver::<B>::from_checkpoint(self.ctx, point.clone());
        let replay_seconds = replay_started.elapsed().as_secs_f64();
        let check_started = Instant::now();
        let target = match condition {
            Some(condition) => Exp::And(Box::new(condition.clone()), Box::new(bad.clone())),
            None => bad.clone(),
        };
        let result = verifier.check_sat_with(&target, info);
        let check_seconds = check_started.elapsed().as_secs_f64();
        // 仅显式诊断开关导出少量小检查；旧日志没有这些dump，不能冒充旧查询重放。
        if matches!(result, Sat) && state.obligations.len() <= 8 {
            if let Some(directory) = &crate::config::RegionOptions::current().obligation_dump_dir {
                static DUMPS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
                let ordinal = DUMPS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if ordinal < 4 {
                    let extra: Vec<_> = self.transaction_events[state.event_start..]
                        .iter()
                        .filter_map(|event| match event {
                            Event::Smt(Def::Assert(exp), _, loc) => Some((exp.clone(), *loc)),
                            _ => None,
                        })
                        .collect();
                    let values: Vec<_> = self.transaction_events[state.event_start..]
                        .iter()
                        .filter_map(|event| match event {
                            Event::Smt(Def::DefineConst(sym, _) | Def::DeclareConst(sym, _), _, loc)
                                if verifier.length(*sym) == Some(2) =>
                            {
                                Some((*sym, *loc))
                            }
                            _ => None,
                        })
                        .collect();
                    dump::write_obligation_diagnostic(
                        point,
                        &bad,
                        &extra,
                        &values,
                        &std::path::PathBuf::from(directory),
                        ordinal,
                        replay_seconds,
                        check_seconds,
                    );
                }
            }
        }
        let seconds = started.elapsed().as_secs_f64();
        let state = self.deferred_assertions.as_mut().unwrap();
        state.verification_seconds += seconds;
        state.verification_result = Some(format!("{result:?}"));
        if diagnostic {
            eprintln!(
                "{}",
                serde_json::json!({"kind":"region_assert_obligation_check","obligations":state.obligations.len(),"definition_events":count,"definition_expression_nodes":definition_nodes,"obligation_expression_nodes":crate::executor::stats::memory_stats::exp_stats(&bad).0,"seconds":seconds,"replay_seconds":replay_seconds,"check_seconds":check_seconds,"result":format!("{result:?}")})
            );
        }
        Some(result)
    }
}
