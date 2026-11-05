//! F5 差分测试专用：冻结的阻断子句参照算法。
use super::*;

fn blocking_satisfiable<B: BV>(solver: &mut Solver<B>) -> Result<bool, ExecError> {
    match solver.check_sat(SourceLoc::unknown()) {
        SmtResult::Sat => Ok(true),
        SmtResult::Unsat => Ok(false),
        SmtResult::Unknown => Err(ExecError::Z3Unknown),
        SmtResult::Error(error) => Err(ExecError::Smt(error)),
    }
}

impl<B: BV> LocalFrame<'_, B> {
    /// 在本路径求解器存活时枚举。所有阻断约束均随保存点回滚；错误也必须回滚。
    /// 未开启时不读取执行迹、不查询模型、不改变输出。
    pub fn enumerate_merges_blocking(
        &self,
        solver: &mut Solver<B>,
        state: &TaskState<B>,
        shared: &SharedState<B>,
        result: &Val<B>,
    ) -> Result<Option<Value>, ExecError> {
        self.enumerate_merges_blocking_with(solver, state, shared, result, &mut |_, _, _| Ok(()))
    }

    /// 每个解在完整模型仍存活时调用消费方；关闭枚举时不调用。
    pub fn enumerate_merges_blocking_with(
        &self,
        solver: &mut Solver<B>,
        state: &TaskState<B>,
        shared: &SharedState<B>,
        result: &Val<B>,
        consume: &mut impl FnMut(usize, usize, &mut Model<B>) -> Result<(), ExecError>,
    ) -> Result<Option<Value>, ExecError> {
        use Formula::*;
        let Some(config) = state.execution_limits.as_ref().map(|limits| &limits.merge_enumeration) else {
            return Ok(None);
        };
        if !config.enabled {
            return Ok(None);
        }
        assert!(config.class_cap > 0 && config.path_cap > 0, "枚举上限必须大于零");
        assert_eq!(solver.transaction_depth(), 0, "仅在路径结束后枚举");
        let records = &self.region_merge_records;
        let by_id: HashMap<_, _> = records.iter().map(|record| (record.record_id, record)).collect();
        assert_eq!(by_id.len(), records.len(), "帧内记录编号必须唯一");
        let mut contexts = HashMap::new();
        let contexts: Vec<_> =
            records.iter().map(|record| context(record, &by_id, &mut HashSet::new(), &mut contexts)).collect();
        let projections: Vec<_> = records
            .iter()
            .zip(&contexts)
            .map(|(record, ctx)| And(Box::new(ctx.clone()), Box::new(Var(record.condition))))
            .collect();
        let events = super::definition_events(solver, &self.local_state.pure_definitions).0;
        let definitions: HashMap<_, _> = events
            .iter()
            .filter_map(|event| match event {
                Event::Smt(Def::DefineConst(symbol, exp), _, location) => Some((*symbol, (exp.clone(), *location))),
                _ => None,
            })
            .collect();
        let slices: Vec<Vec<_>> = records
            .iter()
            .map(|record| {
                let mut slices = std::collections::BTreeMap::new();
                tested_slices(record.condition, &definitions, &mut HashSet::new(), &mut HashSet::new(), &mut slices);
                slices.into_iter().collect()
            })
            .collect();
        let tx = solver.start_transaction();
        let output = (|| {
            let mut classes = Vec::new();
            let mut total = 0;
            let mut path_truncated = false;
            while blocking_satisfiable(solver)? {
                if total == config.path_cap {
                    path_truncated = true;
                    break;
                }
                let mut model = Model::new(solver);
                model.set_complete_model(true);
                let assignment: Vec<_> = projections
                    .iter()
                    .map(|exp| match model.get_exp(exp)?.unwrap_exp() {
                        Bool(value) => Ok(value),
                        value => panic!("守卫投影必须为布尔值：{value:?}"),
                    })
                    .collect::<Result<_, ExecError>>()?;
                drop(model);
                let class_constraint =
                    projections.iter().zip(&assignment).fold(Bool(true), |condition, (exp, value)| {
                        And(
                            Box::new(condition),
                            Box::new(if *value { exp.clone() } else { Not(Box::new(exp.clone())) }),
                        )
                    });
                let mut tested = Vec::new();
                let mut expressions = Vec::new();
                // 二级使用本路径全部守卫测试过的片段；只有一级对上下文做规范化。
                for (index, record) in records.iter().enumerate() {
                    for ((symbol, hi, lo), source_loc) in &slices[index] {
                        tested.push(json!({"symbol":format!("v{symbol}"), "smt_id":symbol, "hi":hi, "lo":lo,
                            "source_loc":source_loc, "record_id":record.record_id}));
                        expressions.push(Extract(*hi, *lo, Box::new(Var(Sym { id: *symbol }))));
                    }
                }
                let class_tx = solver.start_transaction();
                solver.add(Def::Assert(class_constraint.clone()));
                let solutions = (|| {
                    let mut solutions = Vec::new();
                    let mut truncated = false;
                    while blocking_satisfiable(solver)? {
                        // 多查一次区分“刚好完整”与确有未输出的可行解。
                        if solutions.len() == config.class_cap || total == config.path_cap {
                            truncated = true;
                            path_truncated |= total == config.path_cap;
                            break;
                        }
                        let mut model = Model::new(solver);
                        model.set_complete_model(true);
                        let values: Vec<_> = expressions
                            .iter()
                            .map(|exp| model.get_exp(exp).map(ModelVal::unwrap_exp))
                            .collect::<Result<_, _>>()?;
                        let representative_result = model.get_val(result)?.to_string(shared);
                        let symbols: std::collections::BTreeSet<_> =
                            tested.iter().map(|slice| slice["smt_id"].as_u64().unwrap() as u32).collect();
                        let mut inputs = Vec::new();
                        for symbol in symbols {
                            let value = model.get_exp(&Var(Sym { id: symbol }))?.unwrap_exp();
                            inputs.push(
                                json!({"symbol":format!("v{symbol}"), "smt_id":symbol, "value":bits_text(&value)}),
                            );
                        }
                        consume(classes.len(), solutions.len(), &mut model)?;
                        drop(model);
                        let slice_values: Vec<_> = values.iter().map(bits_text).collect();
                        solutions.push(json!({"slice_values":slice_values, "representative":{"result":representative_result, "inputs":inputs}}));
                        total += 1;
                        let block = expressions.iter().zip(values).fold(Bool(false), |block, (exp, value)| {
                            Or(Box::new(block), Box::new(Neq(Box::new(exp.clone()), Box::new(value))))
                        });
                        solver.add(Def::Assert(block));
                    }
                    Ok::<_, ExecError>((solutions, truncated))
                })();
                solver.rollback_transaction(class_tx);
                let (solutions, truncated) = solutions?;
                let guard_assignment: serde_json::Map<_, _> = records
                    .iter()
                    .zip(&assignment)
                    .map(|(record, value)| (record.record_id.to_string(), json!(value)))
                    .collect();
                classes.push(
                    json!({"class_id":classes.len(), "guard_assignment":guard_assignment, "tested_slices":tested,
                    "solution_count":solutions.len(), "solutions":solutions, "truncated":truncated}),
                );
                solver.add(Def::Assert(Not(Box::new(class_constraint))));
                if path_truncated {
                    break;
                }
            }
            let guard_records: Vec<_> = records.iter().map(|record| json!({"record_id":record.record_id, "parent_record":record.parent_record,
                "arm":record.arm, "condition":{"symbol":format!("v{}", record.condition.id), "smt_id":record.condition.id},
                "source_loc":record.source_loc, "function":zencode::decode(shared.symtab.to_str(record.function)),
                "branch_pc":record.branch_pc})).collect();
            Ok(Some(json!({"schema_version":1, "guard_records":guard_records, "guard_classes":classes,
                "path_truncated":path_truncated, "enumerated_total":total, "class_cap":config.class_cap, "path_cap":config.path_cap})))
        })();
        solver.rollback_transaction(tx);
        output
    }
}
