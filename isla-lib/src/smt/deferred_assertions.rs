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
    pub(super) arm: DeferredArmAssertions,
    verification_seconds: f64,
    verification_result: Option<String>,
}

/// 只携带当前臂在执行顺序中已冻结的数据。认证入口和 Z3 状态属于最外层 A。
#[derive(Default)]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub(crate) struct DeferredArmAssertions {
    pub(super) obligations: Vec<DeferredObligation>,
    pub(super) input_facts: Vec<Exp<Sym>>,
    exit_constraints: HashSet<Sym>,
    blocked: BTreeMap<&'static str, usize>,
    first_blocked: Option<SourceLoc>,
}

#[derive(Clone)]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub(super) struct DeferredObligation {
    prefix: Sym,
    bad: Sym,
}

impl DeferredArmAssertions {
    pub(crate) fn remap_symbols(&mut self, remap: &SymRemap) {
        for item in &mut self.obligations {
            item.prefix = remap.get(item.prefix);
            item.bad = remap.get(item.bad);
        }
        for fact in &mut self.input_facts {
            *fact = remap.exp(fact);
        }
        self.exit_constraints = self.exit_constraints.drain().map(|sym| remap.get(sym)).collect();
    }
}

// 前序断言与臂守卫都从 true 左折叠，替换起点即可恢复串行顺序。
fn prepend_conjunction(exp: &mut Exp<Sym>, prefix: &Exp<Sym>) {
    let mut first = exp;
    while let Exp::And(left, _) = first {
        first = left;
    }
    assert_eq!(*first, Exp::Bool(true), "远端合取必须从 true 开始");
    *first = prefix.clone();
}

impl<B: BV> Solver<'_, B> {
    pub(crate) fn take_arm_assertions(&mut self) -> Option<DeferredArmAssertions> {
        self.deferred_assertions.as_mut().map(|state| std::mem::take(&mut state.arm))
    }

    /// B 从私有检查点执行。补齐 A 中排在 B 前面的断言和活动的祖先守卫，
    /// 保留每项义务和类型域事实在臂内的执行边界。
    pub(crate) fn import_arm_assertions(
        &mut self,
        remote: Option<DeferredArmAssertions>,
        suffix: &mut [ArmSuffixEvent<B>],
    ) {
        assert_eq!(self.deferred_assertions.is_some(), remote.is_some(), "两臂的延后查询模式必须一致");
        let Some(mut remote) = remote else { return };
        let ancestors = (!self.transaction_conditions.is_empty()).then(|| {
            self.transaction_conditions.iter().cloned().fold(Exp::Bool(true), |a, b| Exp::And(Box::new(a), Box::new(b)))
        });
        if !remote.obligations.is_empty() {
            let mut prefixes: HashSet<_> = remote.obligations.iter().map(|item| item.prefix).collect();
            let mut bad: HashSet<_> =
                ancestors.iter().flat_map(|_| remote.obligations.iter().map(|item| item.bad)).collect();
            let prior = self.preceding_assertions();
            for item in suffix {
                if let Event::Smt(Def::DefineConst(sym, exp), ..) = &mut item.event {
                    if prefixes.remove(sym) {
                        prepend_conjunction(exp, &prior);
                    } else if bad.remove(sym) {
                        let Exp::And(_, rest) = exp else { unreachable!("义务反例必须包含前序断言") };
                        let Exp::And(guard, _) = rest.as_mut() else { unreachable!("义务反例必须包含守卫") };
                        prepend_conjunction(guard, ancestors.as_ref().unwrap());
                    }
                }
            }
            assert!(prefixes.is_empty() && bad.is_empty(), "每项义务的前序和反例定义必须随臂交付");
        }
        if let Some(ancestors) = &ancestors {
            for fact in &mut remote.input_facts {
                let Exp::Or(negated_guard, _) = fact else { unreachable!("类型域事实必须包含守卫") };
                let Exp::Not(guard) = negated_guard.as_mut() else {
                    unreachable!("类型域事实必须由守卫推出")
                };
                prepend_conjunction(guard, ancestors);
            }
        }
        let local = &mut self.deferred_assertions.as_mut().unwrap().arm;
        local.obligations.extend(remote.obligations);
        local.input_facts.extend(remote.input_facts);
        local.exit_constraints.extend(remote.exit_constraints);
        local.first_blocked = local.first_blocked.or(remote.first_blocked);
        for (purpose, count) in remote.blocked {
            *local.blocked.entry(purpose).or_default() += count;
        }
    }

    /// 嵌套区域复用同一义务集合；作用域退出或panic时清理，不能泄漏到普通执行。
    pub(crate) fn with_deferred_region_queries<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let previous = self.deferred_region_queries;
        if !previous {
            assert!(self.deferred_assertions.is_none(), "上次区域的断言义务必须已清理");
            self.deferred_assertions = Some(DeferredAssertions {
                entry: self.checkpoint_snapshot(),
                event_start: self.transaction_events.len(),
                arm: DeferredArmAssertions::default(),
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
                && (!state.arm.obligations.is_empty() || !state.arm.blocked.is_empty())
                && LOGGED.fetch_add(1, std::sync::atomic::Ordering::Relaxed) < 128
            {
                eprintln!(
                    "{}",
                    serde_json::json!({"kind":"region_deferred_exit",
                    "obligations":state.arm.obligations.len(),"blocked_queries":state.arm.blocked,
                    "first_blocked_source":state.arm.first_blocked,"verification_seconds":state.verification_seconds,
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

    /// 仅选中的区域指令可做必需查询，求解器条件和义务集合沿用活动前缀。
    pub(crate) fn with_region_resume_queries<R>(&mut self, run: impl FnOnce(&mut Self) -> R) -> R {
        let previous = self.ordinary_region_resume_queries;
        self.ordinary_region_resume_queries = !self.no_smt();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(self)));
        self.ordinary_region_resume_queries = previous;
        match result {
            Ok(value) => value,
            Err(panic) => std::panic::resume_unwind(panic),
        }
    }

    pub(crate) fn end_region_resume_queries(&mut self) {
        self.ordinary_region_resume_queries = false;
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
        *state.arm.blocked.entry(purpose).or_default() += 1;
        state.arm.first_blocked.get_or_insert(info);
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
        let preceding = self.preceding_assertions();
        let prefix = self.define_const(preceding, info);
        let bad = self.define_const(
            Exp::And(
                Box::new(Exp::Var(prefix)),
                Box::new(Exp::And(Box::new(guard), Box::new(Exp::Not(Box::new(condition.clone()))))),
            ),
            info,
        );
        self.deferred_assertions.as_mut().unwrap().arm.obligations.push(DeferredObligation { prefix, bad });
        // 只供正常结果和后续义务使用；当前义务已在此之前冻结。
        self.assert(condition);
    }

    fn preceding_assertions(&self) -> Exp<Sym> {
        // 只取在本义务之前出现的断言；已提交的兄弟臂断言已带守卫。
        // 当前活动臂中的断言由本义务的完整guard限制，不能拿自己的c证明自己。
        let state = self.deferred_assertions.as_ref().unwrap();
        let mut preceding = Exp::Bool(true);
        for event in &self.transaction_events[state.event_start..] {
            if let Event::Smt(Def::Assert(exp), ..) = event {
                let mut exit = false;
                let _ = exp.map_var(&mut |v| {
                    exit |= state.arm.exit_constraints.contains(v);
                    Ok::<_, ()>(Exp::Var(*v))
                });
                if !exit {
                    preceding = Exp::And(Box::new(preceding), Box::new(exp.clone()));
                }
            }
        }
        preceding
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
                .arm
                .input_facts
                .push(Exp::Or(Box::new(Exp::Not(Box::new(guard))), Box::new(exp.clone())));
        }
        self.assert(exp);
    }

    /// 正常出口域不能进入任何安全义务的前序前提。
    pub(crate) fn assert_region_exit(&mut self, exp: Exp<Sym>) {
        if self.deferred_region_queries {
            let marker = self.define_const(exp, SourceLoc::unknown());
            self.deferred_assertions.as_mut().unwrap().arm.exit_constraints.insert(marker);
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
        serde_json::json!({"definition_events":definitions,"definition_expression_nodes":nodes,"assertion_expression_nodes":assertions,"obligations":self.deferred_assertions.as_ref().map_or(0,|s|s.arm.obligations.len())})
    }

    /// 使用失败点的前缀认证错误，后续正常域的约束不参与检查。
    pub(crate) fn check_arm_error(
        &self,
        guard: Sym,
        point: &Checkpoint<B>,
        info: SourceLoc,
        queries: Option<&mut ArmErrorQueries<'_, B>>,
    ) -> Option<SmtResult> {
        if !self.validates_candidates() {
            return None;
        }
        let target = Exp::Var(guard);
        match queries {
            Some(queries) => Some(queries.check(point, &target, info)),
            None => Solver::from_checkpoint(self.ctx, point.clone()).check_candidate_sat_with(&target, info),
        }
    }

    pub(crate) fn check_deferred_assertions(&mut self, info: SourceLoc) -> Option<SmtResult> {
        self.check_deferred_assertions_from(0, info)
    }

    pub(crate) fn check_deferred_assertions_since_savepoint(&mut self, info: SourceLoc) -> Option<SmtResult> {
        let start = self.savepoints.last().expect("前缀认证必须在活动保存点内").deferred_obligations_len;
        self.check_deferred_assertions_from(start, info)
    }

    fn check_deferred_assertions_from(&mut self, start: usize, info: SourceLoc) -> Option<SmtResult> {
        if !self.validates_candidates() {
            return None;
        }
        let state = self.deferred_assertions.as_ref().expect("验证必须在活动义务作用域中");
        let obligations = &state.arm.obligations[start..];
        let obligation_count = obligations.len();
        if obligations.is_empty() {
            return Some(Unsat);
        }
        let started = Instant::now();
        let bad = obligations
            .iter()
            .map(|item| Exp::Var(item.bad))
            .fold(Exp::Bool(false), |a, b| Exp::Or(Box::new(a), Box::new(b)));
        // 前序断言已经冻结到各自的bad定义中；此处仅重放定义和初始类型域。
        // 不再无条件加入所有正常结果断言，避免后续约束掩盖前面的错误。
        let mut definitions: Vec<_> = self.transaction_events[state.event_start..]
            .iter()
            .filter(|event| matches!(event,Event::Smt(def,..) if !matches!(def,Def::Assert(_))))
            .cloned()
            .collect();
        definitions.extend(
            state.arm.input_facts.iter().cloned().map(|fact| Event::Smt(Def::Assert(fact), DefAttrs::default(), info)),
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
            projected: None,
            tail: state.entry.trace.clone(),
        }));
        let point = Checkpoint { num: state.entry.num + 1, next_var: self.next_var, trace, cycles: 0 };
        if diagnostic {
            eprintln!(
                "{}",
                serde_json::json!({"kind":"region_assert_obligation_start", "obligations":obligation_count, "definition_events":count, "definition_expression_nodes":definition_nodes, "obligation_expression_nodes":crate::executor::stats::memory_stats::exp_stats(&bad).0})
            );
        }
        let replay_started = Instant::now();
        let mut verifier = Solver::<B>::from_checkpoint(self.ctx, point.clone());
        let replay_seconds = replay_started.elapsed().as_secs_f64();
        let check_started = Instant::now();
        let result = verifier.check_sat_with(&bad, info);
        let check_seconds = check_started.elapsed().as_secs_f64();
        // 仅显式诊断开关导出少量小检查；旧日志没有这些dump，不能冒充旧查询重放。
        if matches!(result, Sat) && obligation_count <= 8 {
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
                serde_json::json!({"kind":"region_assert_obligation_check","obligations":obligation_count,"definition_events":count,"definition_expression_nodes":definition_nodes,"obligation_expression_nodes":crate::executor::stats::memory_stats::exp_stats(&bad).0,"seconds":seconds,"replay_seconds":replay_seconds,"check_seconds":check_seconds,"result":format!("{result:?}")})
            );
        }
        Some(result)
    }
}
