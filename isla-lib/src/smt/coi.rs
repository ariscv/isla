//! 查询级切片只读取已翻译的约束。主求解器和迹继续持有全部断言。
use super::*;

type Support = Option<Vec<Z3_func_decl>>;

#[derive(Default)]
pub(super) struct Coi<'ctx> {
    premises: Vec<(Ast<'ctx>, Support)>,
    certified: HashMap<Z3_ast, Ast<'ctx>>,
    uninterpreted: Option<u32>,
    #[cfg(test)]
    removed: usize,
}

impl<'ctx> Coi<'ctx> {
    fn support(&mut self, root: &Ast<'ctx>) -> Support {
        let ctx = root.ctx.z3_ctx;
        let uninterpreted = *self.uninterpreted.get_or_insert_with(|| unsafe {
            let raw = Z3_mk_fresh_const(ctx, c"isla_coi".as_ptr(), Z3_mk_bool_sort(ctx));
            Z3_inc_ref(ctx, raw);
            let fresh = Ast { ctx: root.ctx, z3_ast: raw };
            rewrite::decl_kind_raw(ctx, Z3_get_app_decl(ctx, Z3_to_app(ctx, fresh.z3_ast)))
        });
        let mut pending = vec![root.z3_ast];
        let mut seen = HashSet::new();
        let mut declarations = HashSet::new();
        while let Some(node) = pending.pop() {
            if !seen.insert(node) {
                continue;
            }
            unsafe {
                match Z3_get_sort_kind(ctx, Z3_get_sort(ctx, node)) {
                    SortKind::Bool | SortKind::BV | SortKind::Datatype => (),
                    _ => return None,
                }
                match Z3_get_ast_kind(ctx, node) {
                    AstKind::Numeral => (),
                    AstKind::App => {
                        let app = Z3_to_app(ctx, node);
                        let declaration = Z3_get_app_decl(ctx, app);
                        let kind = rewrite::decl_kind_raw(ctx, declaration);
                        match kind {
                            // Z3 的布尔、位向量和数据类型运算编号。其它理论可能携带隐藏依赖。
                            0x100..=0x10b | 0x400..=0x43f | 0x800..=0x802 => (),
                            _ if kind == uninterpreted => {
                                declarations.insert(declaration);
                            }
                            _ => return None,
                        }
                        pending.extend((0..Z3_get_app_num_args(ctx, app)).map(|i| Z3_get_app_arg(ctx, app, i)));
                    }
                    _ => return None,
                }
            }
        }
        Some(declarations.into_iter().collect())
    }

    fn replace_suffix(&mut self, current: &[Ast<'ctx>]) {
        let keep = self.premises.iter().zip(current).take_while(|((a, _), b)| a.z3_ast == b.z3_ast).count();
        self.premises.truncate(keep);
        for ast in &current[keep..] {
            let support = self.support(ast);
            self.premises.push((ast.clone(), support));
        }
    }

    fn partition(&mut self, seeds: &[Ast<'ctx>]) -> Option<Vec<bool>> {
        let mut symbols = HashSet::new();
        for seed in seeds {
            symbols.extend(self.support(seed)?);
        }
        let mut users = HashMap::<_, Vec<_>>::new();
        let mut keep = vec![false; self.premises.len()];
        for (index, (_, support)) in self.premises.iter().enumerate() {
            let support = support.as_ref()?;
            // 无自由符号的断言可能恒假。直接保留在目标查询内。
            keep[index] = support.is_empty();
            for &symbol in support {
                users.entry(symbol).or_default().push(index);
            }
        }
        let mut pending: Vec<_> = symbols.iter().copied().collect();
        while let Some(symbol) = pending.pop() {
            for &index in users.remove(&symbol).as_deref().unwrap_or_default() {
                if !std::mem::replace(&mut keep[index], true) {
                    pending.extend(
                        self.premises[index].1.as_ref().unwrap().iter().copied().filter(|s| symbols.insert(*s)),
                    );
                }
            }
        }
        (keep.contains(&true) && keep.contains(&false)).then_some(keep)
    }
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    /// 只交付可行性。切片模型不能交给使用完整路径模型的调用方。
    pub(super) fn coi_feasibility(
        &mut self,
        seeds: &[Exp<Sym>],
        condition: Option<&Exp<Sym>>,
        info: SourceLoc,
        purpose: &'static str,
    ) -> Option<SmtResult> {
        if self.coi.is_none() || self.no_smt() || (self.deferred_region_queries && !self.ordinary_region_resume_queries)
        {
            return None;
        }
        #[cfg(test)]
        if let Some(reason) = test_queries::take_unknown_reason(info) {
            return Some(Error(z3_query_error(info, Duration::ZERO, None, reason.into(), false)));
        }
        let target = condition.map(|exp| self.translate_exp(exp));
        let mut anchors: Vec<_> = seeds.iter().map(|exp| self.translate_exp(exp)).collect();
        anchors.extend(target.iter().cloned());
        let pending = self.transaction_assertions();
        let raw_pending: Vec<_> = pending.iter().map(|ast| ast.z3_ast).collect();
        let (premises, _) = self.region_query_complete(&raw_pending, false);
        let premises: Vec<_> = premises
            .into_iter()
            .map(|z3_ast| {
                unsafe { Z3_inc_ref(self.ctx.z3_ctx, z3_ast) };
                Ast { ctx: self.ctx, z3_ast }
            })
            .collect();
        let cache = self.coi.as_mut().unwrap();
        cache.replace_suffix(&premises);
        let keep = cache.partition(&anchors)?;
        let (relevant, omitted): (Vec<_>, Vec<_>) = premises.into_iter().zip(keep).partition(|(_, keep)| *keep);
        let relevant: Vec<_> =
            relevant.iter().map(|(ast, _)| ast.z3_ast).chain(target.iter().map(|ast| ast.z3_ast)).collect();
        let omitted: Vec<_> = omitted.into_iter().map(|(ast, _)| ast).collect();
        let omitted_proven = self.knowledge.sat
            || self.has_stashed_model()
            || omitted.iter().all(|ast| self.coi.as_ref().unwrap().certified.contains_key(&ast.z3_ast));
        #[cfg(test)]
        {
            self.coi.as_mut().unwrap().removed += omitted.len();
        }
        probe_query_event(|| {
            serde_json::json!({
                "type":"coi_slice", "purpose":purpose, "kept":relevant.len() - usize::from(target.is_some()),
                "removed":omitted.len(), "removed_already_sat":omitted_proven,
            })
        });
        let _scope = crate::executor::stats::region_progress::QueryScope::fallback(purpose);
        let result = self.coi_check(&relevant, condition, info);
        if result != Sat || omitted_proven {
            return Some(result);
        }

        // 变量不相交足以拼合两个模型，仍需要分别认证省略部分。
        let _scope = crate::executor::stats::region_progress::QueryScope::enter("coi_independent");
        let assertions: Vec<_> = omitted.iter().map(|ast| ast.z3_ast).collect();
        let result = self.coi_check(&assertions, condition, info);
        if result == Sat {
            self.coi.as_mut().unwrap().certified = omitted.into_iter().map(|ast| (ast.z3_ast, ast)).collect();
        }
        Some(result)
    }

    /// 根出口和终态保存点只需可行性。完整模型仍按常规入口单独取得。
    pub fn check_exit_feasibility(&mut self, symbols: impl IntoIterator<Item = Sym>, info: SourceLoc) -> SmtResult {
        if self.coi.is_some() && !self.has_stashed_model() {
            let seeds: Vec<_> = symbols.into_iter().map(Exp::Var).collect();
            if let Some(result) = self.coi_feasibility(&seeds, None, info, "exit_feasibility") {
                return result;
            }
        }
        self.check_sat(info)
    }

    pub fn coi_query_slicing_enabled(&self) -> bool {
        self.coi.is_some()
    }

    #[cfg(test)]
    pub(super) fn coi_removed_assertions(&self) -> usize {
        self.coi.as_ref().unwrap().removed
    }

    fn coi_check(&self, assertions: &[Z3_ast], condition: Option<&Exp<Sym>>, info: SourceLoc) -> SmtResult {
        let query = self.query_from_assertions(assertions);
        let budget = query.resource_budget(None);
        let slow = self.slow_query_begin(query.z3_solver);
        let start = Instant::now();
        match timeout_Z3_solver_check_assumptions(self.ctx.z3_ctx, query.z3_solver, &[], info) {
            Ok(result) => {
                self.slow_query_finish(slow, query.z3_solver, condition, info, result);
                match result {
                    Z3_L_TRUE => Sat,
                    Z3_L_FALSE => Unsat,
                    _ => Error(query.failure(info, start.elapsed(), budget)),
                }
            }
            Err(Z3TimeoutError::Interrupted(limit)) => {
                let request =
                    condition.map_or(SmtDumpRequest::CheckSat, |exp| SmtDumpRequest::CheckSatWith(exp.clone()));
                let dump = timeout_dump_from_checkpoint(self.checkpoint_snapshot(), request);
                Error(z3_timeout_error(SmtOperation::CheckSatAssuming, info, start.elapsed(), limit, dump))
            }
        }
    }
}
