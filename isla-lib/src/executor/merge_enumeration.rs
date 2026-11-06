//! 合并路径终态的两级枚举，与具体 ISA 无关。
//! 主迹仍采用寄存器读取并集语义，枚举不恢复精确事件顺序。
use super::*;
use serde_json::{json, Value};
use smtlib::Exp as Formula;

#[path = "merge_components.rs"]
mod components;

#[path = "merge_parallel.rs"]
mod parallel;

type SampleConsumer<'a, B> = dyn Fn(usize, usize, &[String], bool, &mut Model<B>) -> Result<(), ExecError> + Sync + 'a;
type ClassConsumer<'a> = dyn Fn(usize, &Value) -> Result<(), ExecError> + Sync + 'a;

fn guard_order<B>(records: &[RegionMergeRecord<B>]) -> Vec<usize> {
    let positions: HashMap<_, _> =
        records.iter().enumerate().map(|(index, record)| (record.record_id, index)).collect();
    let mut order: Vec<_> = (0..records.len()).collect();
    order.sort_by_cached_key(|index| {
        let mut chain = vec![*index];
        let mut record = &records[*index];
        while let Some(parent) = record.parent_record {
            let parent = positions[&parent];
            assert!(!chain.contains(&parent), "记录上下文不得成环");
            chain.push(parent);
            record = &records[parent];
        }
        chain.reverse();
        chain
    });
    order
}

fn context<B>(
    record: &RegionMergeRecord<B>,
    records: &HashMap<usize, &RegionMergeRecord<B>>,
    visiting: &mut HashSet<usize>,
    contexts: &mut HashMap<usize, Formula<Sym>>,
) -> Formula<Sym> {
    use Formula::*;
    if let Some(context) = contexts.get(&record.record_id) {
        return context.clone();
    }
    assert!(visiting.insert(record.record_id), "记录上下文不得成环");
    let result = match record.parent_record {
        None => {
            assert_eq!(record.arm, "root", "根记录不得属于某个分支臂");
            Bool(true)
        }
        Some(parent) => {
            let parent = records.get(&parent).expect("父记录必须保存在同一路径帧中");
            let guard = match record.arm {
                "then" => Var(parent.condition),
                "else" => Not(Box::new(Var(parent.condition))),
                arm => panic!("无效的记录臂 {arm}"),
            };
            And(Box::new(context(parent, records, visiting, contexts)), Box::new(guard))
        }
    };
    visiting.remove(&record.record_id);
    contexts.insert(record.record_id, result.clone());
    result
}

/// 沿定义依赖扫描实际 Extract 项，保留一般派生符号的 AST 语义。
/// 一旦消费一个片段，就不再把它的整段输入当作另一个待枚举字段。
fn tested_slices(
    symbol: Sym,
    definitions: &HashMap<Sym, (Formula<Sym>, SourceLoc)>,
    visiting: &mut HashSet<Sym>,
    visited: &mut HashSet<Sym>,
    slices: &mut std::collections::BTreeMap<(u32, u32, u32), SourceLoc>,
) {
    use Formula::*;
    if visited.contains(&symbol) {
        return;
    }
    assert!(visiting.insert(symbol), "守卫定义依赖不得成环");
    if let Some((definition, location)) = definitions.get(&symbol) {
        let mut expression = definition.clone();
        // 必须先折叠同一 AST 内连续的 Extract，再消费片段；否则会先收集内层宽字段。
        expression.modify(&mut |exp| {
            if let Extract(hi, lo, inner) = exp {
                if let Extract(inner_hi, inner_lo, value) = inner.as_ref() {
                    assert!(*hi <= inner_hi - inner_lo, "片段不得超出输入位宽");
                    *exp =
                        Extract(hi.checked_add(*inner_lo).unwrap(), lo.checked_add(*inner_lo).unwrap(), value.clone());
                }
            }
        });
        expression.modify(&mut |exp| {
            if let Extract(hi, lo, inner) = exp {
                if let Var(input) = inner.as_ref() {
                    let (mut input, mut hi, mut lo) = (*input, *hi, *lo);
                    let mut aliases = HashSet::new();
                    while let Some((definition, _)) = definitions.get(&input) {
                        assert!(aliases.insert(input), "片段定义不得成环");
                        match definition {
                            Var(alias) => input = *alias,
                            Extract(inner_hi, inner_lo, value) => {
                                assert!(hi <= inner_hi - inner_lo, "片段不得超出输入位宽");
                                if let Var(alias) = value.as_ref() {
                                    hi = hi.checked_add(*inner_lo).unwrap();
                                    lo = lo.checked_add(*inner_lo).unwrap();
                                    input = *alias;
                                } else {
                                    break;
                                }
                            }
                            _ => break,
                        }
                    }
                    slices.insert((input.id, hi, lo), *location);
                    // 只用于依赖扫描，不交给求解器；阻止继续枚举未被测试的输入位。
                    *exp = Bool(true);
                }
            }
        });
        for input in expression.variables() {
            tested_slices(input, definitions, visiting, visited, slices);
        }
    }
    visiting.remove(&symbol);
    visited.insert(symbol);
}

fn bits_text(value: &Formula<Sym>) -> String {
    match value {
        Formula::Bits64(bits) => format!("#b{:0width$b}", bits.lower_u64(), width = bits.len() as usize),
        Formula::Bits(bits) => {
            format!("#b{}", bits.iter().rev().map(|bit| if *bit { '1' } else { '0' }).collect::<String>())
        }
        value => panic!("片段取值必须是具体位向量：{value:?}"),
    }
}

/// 假设只在本次查询生效；不增加路径断言或逐解阻断子句。
fn satisfiable<B: BV>(solver: &mut Solver<B>, condition: &Formula<Sym>) -> Result<bool, ExecError> {
    match solver.check_sat_with(condition, SourceLoc::unknown()) {
        SmtResult::Sat => Ok(true),
        SmtResult::Unsat => Ok(false),
        SmtResult::Unknown => Err(ExecError::Z3Unknown),
        SmtResult::Error(error) => Err(ExecError::Smt(error)),
    }
}

impl<B: BV> LocalFrame<'_, B> {
    /// 未开启时不读取执行迹、不查询模型、不改变输出。
    pub fn enumerate_merges(
        &self,
        solver: &mut Solver<B>,
        state: &TaskState<B>,
        shared: &SharedState<B>,
        result: &Val<B>,
    ) -> Result<Option<Value>, ExecError> {
        self.enumerate_merges_parallel_with(solver, state, shared, result, &|_, _, _| Ok(()))
    }

    /// 保留可变消费者接口；消费者由互斥锁保护，按需使用并行只读接口提高物化吞吐。
    pub fn enumerate_merges_with(
        &self,
        solver: &mut Solver<B>,
        state: &TaskState<B>,
        shared: &SharedState<B>,
        result: &Val<B>,
        consume: &mut (impl FnMut(usize, usize, &mut Model<B>) -> Result<(), ExecError> + Send),
    ) -> Result<Option<Value>, ExecError> {
        let consume = Mutex::new(consume);
        self.enumerate_merges_parallel_with(solver, state, shared, result, &|class, solution, model| {
            consume.lock().unwrap()(class, solution, model)
        })
    }

    /// 并行消费者在各工作线程本地使用模型；模型及其 Z3 Context 不跨线程传递。
    pub fn enumerate_merges_parallel_with(
        &self,
        solver: &mut Solver<B>,
        state: &TaskState<B>,
        shared: &SharedState<B>,
        result: &Val<B>,
        consume: &(impl Fn(usize, usize, &mut Model<B>) -> Result<(), ExecError> + Sync),
    ) -> Result<Option<Value>, ExecError> {
        self.enumerate_merges_output_with(
            solver,
            state,
            shared,
            result,
            &|class, solution, _, _, model| consume(class, solution, model),
            None,
            true,
        )
    }

    /// 输出端收到同一个模型、被测片段与最终截断标志；显式外置解可避免在 gen JSON 中积攒全部组合。
    pub fn enumerate_merges_output_with(
        &self,
        solver: &mut Solver<B>,
        state: &TaskState<B>,
        shared: &SharedState<B>,
        result: &Val<B>,
        consume: &SampleConsumer<'_, B>,
        complete: Option<&ClassConsumer<'_>>,
        retain_solutions: bool,
    ) -> Result<Option<Value>, ExecError> {
        let Some(config) = state.execution_limits.as_ref().map(|limits| &limits.merge_enumeration) else {
            return Ok(None);
        };
        if !config.enabled {
            return Ok(None);
        }
        // 分量诊断需要完整的原顺序联合见证，继续使用其专用串行参照遍历。
        if config.mode == crate::config::MergeEnumerationMode::Count
            && std::env::var("ISLA_ENUM_COMPONENTS").as_deref() == Ok("1")
        {
            return self.enumerate_merges_partition(
                solver,
                state,
                shared,
                result,
                consume,
                complete,
                retain_solutions,
                None,
                None,
            );
        }
        parallel::enumerate(self, solver, state, shared, result, consume, complete, retain_solutions).map(Some)
    }

    fn enumerate_merges_partition(
        &self,
        solver: &mut Solver<B>,
        state: &TaskState<B>,
        shared: &SharedState<B>,
        result: &Val<B>,
        consume: &SampleConsumer<'_, B>,
        complete: Option<&ClassConsumer<'_>>,
        retain_solutions: bool,
        partition: Option<&parallel::Partition>,
        plans: Option<&HashMap<Vec<bool>, parallel::ClassPlan>>,
    ) -> Result<Option<Value>, ExecError> {
        use Formula::*;
        let Some(config) = state.execution_limits.as_ref().map(|limits| &limits.merge_enumeration) else {
            return Ok(None);
        };
        if !config.enabled {
            return Ok(None);
        }
        assert!(
            config.class_cap > 0 && config.path_cap > 0 && config.sample_stride > 0,
            "枚举上限和采样步长必须大于零"
        );
        assert_eq!(solver.transaction_depth(), 0, "仅在路径结束后枚举");
        let records = &self.region_merge_records;
        let by_id: HashMap<_, _> = records.iter().map(|record| (record.record_id, record)).collect();
        assert_eq!(by_id.len(), records.len(), "帧内记录编号必须唯一");
        let mut contexts = HashMap::new();
        for record in records {
            context(record, &by_id, &mut HashSet::new(), &mut contexts);
        }
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
        // 提交历史通常子记录在前；按父链的原始位置做字典序排序，
        // 得到每棵守卫树的前序，整棵子树先于下一根，而非按深度广度遍历。
        let order = guard_order(records);
        let positions: HashMap<_, _> =
            order.iter().enumerate().map(|(position, index)| (records[*index].record_id, position)).collect();
        let mut tested = Vec::new();
        let mut expressions = Vec::new();
        let mut bits = std::collections::BTreeSet::new();
        let mut symbols = std::collections::BTreeSet::new();
        // 二级仍使用整条路径全部被测片段，并在类间复用扫描结果。
        for (index, record) in records.iter().enumerate() {
            for ((symbol, hi, lo), source_loc) in &slices[index] {
                tested.push(json!({"symbol":format!("v{symbol}"), "smt_id":symbol, "hi":hi, "lo":lo,
                    "source_loc":source_loc, "record_id":record.record_id}));
                expressions.push((*symbol, *hi, *lo));
                symbols.insert(*symbol);
                for bit in *lo..=*hi {
                    bits.insert((*symbol, bit));
                }
            }
        }
        // 一次取回所有裸守卫，再按父链规范化；不为每个守卫单独抽取模型。
        let packed_guards = records
            .iter()
            .map(|record| {
                Ite(Box::new(Var(record.condition)), Box::new(smtlib::bits64(1, 1)), Box::new(smtlib::bits64(0, 1)))
            })
            .reduce(|high, low| Concat(Box::new(high), Box::new(low)));
        let bit_predicates: Vec<_> = bits
            .iter()
            .map(|(symbol, bit)| {
                Eq(Box::new(Extract(*bit, *bit, Box::new(Var(Sym { id: *symbol })))), Box::new(smtlib::bits64(1, 1)))
            })
            .collect();
        let probing = partition.is_some() && plans.is_none();
        let partition_cap = plans.map_or(config.path_cap, |plans| {
            plans.values().filter(|plan| plan.partition == partition.unwrap().id).map(|plan| plan.count).sum()
        });
        let counting = probing || config.mode == crate::config::MergeEnumerationMode::Count;
        let measuring = probing
            && config.mode == crate::config::MergeEnumerationMode::Count
            && std::env::var("ISLA_ENUM_MEASURE").as_deref() == Ok("1");
        let measure = |phase, classes, paths| {
            if measuring {
                eprintln!(
                    "[MERGE_ENUMERATION_MEASURE] {}",
                    json!({"phase":phase,
                    "path_signature":self.path_signature(), "partition_id":partition.unwrap().id,
                    "counted_classes":classes, "counted_paths":paths})
                );
            }
        };
        // DFS 只抽取被投影的一位谓词见证；完整输入、返回值和状态仅在选中位置求值。
        let packed_bits = bit_predicates
            .iter()
            .map(|bit| Ite(Box::new(bit.clone()), Box::new(smtlib::bits64(1, 1)), Box::new(smtlib::bits64(0, 1))))
            .reduce(|high, low| Concat(Box::new(high), Box::new(low)));
        // 物化会在 Z3 Context 中创建 AST、补全模型，影响后续代表值。
        // 复用现有事件重放接口隔离 DFS 与逐解物化，避免 stride 改变样本内容。
        let replay_events: Vec<_> = solver.trace().to_vec().into_iter().rev().cloned().collect();
        let tx = solver.start_transaction();
        let mut diagnostic = if counting && std::env::var("ISLA_ENUM_COMPONENTS").as_deref() == Ok("1") {
            Some(components::Diagnostic::new(records, &contexts, &expressions, &bits, &replay_events))
        } else {
            None
        };
        let enumerate = |solver: &mut Solver<B>| {
            let started = std::time::Instant::now();
            let mut sat_time = std::time::Duration::ZERO;
            let mut projection_time = std::time::Duration::ZERO;
            let mut sat_checks = 0;
            let mut class_count = 0;
            let mut truncated_classes = 0;
            let mut classes = Vec::new();
            let mut total = 0;
            let mut exported_samples = 0;
            let mut path_truncated = false;
            // 在原路径约束与活动上下文中固定的守卫，不必在每个类重复探测相反分支。
            // 只剪去已由 SAT 证明确不可能的极性；不限制任何真实可行类。
            let mut split_guards = vec![true; records.len()];
            {
                let queried = std::time::Instant::now();
                for (index, record) in records.iter().enumerate() {
                    let ctx = &contexts[&record.record_id];
                    let guard = Var(record.condition);
                    sat_checks += 1;
                    let positive = satisfiable(solver, &And(Box::new(ctx.clone()), Box::new(guard.clone())))?;
                    split_guards[index] = positive && {
                        sat_checks += 1;
                        satisfiable(solver, &And(Box::new(ctx.clone()), Box::new(Not(Box::new(guard)))))?
                    };
                }
                sat_time += queried.elapsed();
            }
            let mut pending = if let Some(partition) = partition {
                vec![(partition.condition.clone(), partition.depth)]
            } else if counting {
                vec![(Bool(true), 0)]
            } else if let Some(index) = order.first() {
                let guard = Var(records[*index].condition);
                vec![(guard.clone(), 1), (Not(Box::new(guard)), 1)]
            } else {
                vec![(Bool(true), 0)]
            };
            while let Some((class_prefix, guard_depth)) = pending.pop() {
                if plans.is_some() && total == partition_cap {
                    break;
                }
                let queried = std::time::Instant::now();
                let feasible = satisfiable(solver, &class_prefix)?;
                sat_time += queried.elapsed();
                sat_checks += 1;
                if !feasible {
                    continue;
                }
                if (partition.is_none() || probing) && total == config.path_cap {
                    path_truncated = true;
                    break;
                }
                // 分区内先按 false/true 顺序展开守卫，确保 path_cap 截取规范前缀。
                // 这样类内上限很大时，预计数也不会遍历超过本分区的路径预算。
                if partition.is_some() {
                    let mut model = Model::new(solver);
                    model.set_complete_model(true);
                    let raw = packed_guards
                        .as_ref()
                        .map(|packed| model.get_exp(packed).map(|value| bits_text(&value.unwrap_exp())))
                        .transpose()?;
                    drop(model);
                    let mut values = Vec::<bool>::new();
                    let mut split = None;
                    for (position, index) in order.iter().enumerate() {
                        let record = &records[*index];
                        let mut current = record;
                        let mut active = true;
                        while let Some(parent) = current.parent_record {
                            let value = values[positions[&parent]];
                            active &= if current.arm == "then" { value } else { !value };
                            current = by_id[&parent];
                        }
                        values.push(active && raw.as_ref().unwrap().as_bytes()[2 + *index] == b'1');
                        if position >= guard_depth && active && split_guards[*index] {
                            split = Some((position, Var(record.condition)));
                            break;
                        }
                    }
                    if let Some((position, guard)) = split {
                        pending.push((And(Box::new(class_prefix.clone()), Box::new(guard.clone())), position + 1));
                        pending.push((And(Box::new(class_prefix), Box::new(Not(Box::new(guard)))), position + 1));
                        continue;
                    }
                }
                let mut assignment = Vec::<bool>::new();
                let mut solutions = Vec::new();
                let mut solution_count = 0;
                let mut class_exported = 0;
                let mut truncated = false;
                // 一级叶子的 Sat 缓存直接用于第一个解，class_cap=1 只创建一次模型。
                let mut candidate = Some((class_prefix, 0));
                let mut remaining = Vec::<(Formula<Sym>, usize)>::new();
                while let Some((mut prefix, depth)) = candidate.take() {
                    let projected = std::time::Instant::now();
                    let mut model = Model::new(solver);
                    model.set_complete_model(true);
                    if solution_count == 0 {
                        let raw = if let Some(packed) = &packed_guards {
                            bits_text(&model.get_exp(packed)?.unwrap_exp())
                        } else {
                            String::new()
                        };
                        // 当前模型已证明沿其取值的全部后续分支可行，直接走到叶子。
                        // 相反分支压栈，后续从最深未访问前缀开始 Sat 剪枝。
                        for (position, index) in order.iter().enumerate() {
                            let record = &records[*index];
                            let mut current = record;
                            let mut active = true;
                            while let Some(parent) = current.parent_record {
                                let value = assignment[positions[&parent]];
                                active &= if current.arm == "then" { value } else { !value };
                                current = by_id[&parent];
                            }
                            let value = active && raw.as_bytes()[2 + *index] == b'1';
                            assignment.push(value);
                            if partition.is_none() && position >= guard_depth && active && split_guards[*index] {
                                let selected =
                                    if value { Var(record.condition) } else { Not(Box::new(Var(record.condition))) };
                                pending.push((
                                    And(Box::new(prefix.clone()), Box::new(Not(Box::new(selected.clone())))),
                                    position + 1,
                                ));
                                prefix = And(Box::new(prefix), Box::new(selected));
                            }
                        }
                    }
                    let plan = plans.map(|plans| plans.get(&assignment));
                    if matches!(plan, Some(None)) {
                        break;
                    }
                    let plan = plan.flatten();
                    let class_id = plan.map_or(class_count, |plan| plan.class_id);
                    let ordinal = plan.map_or(total, |plan| plan.ordinal.checked_add(solution_count).unwrap());
                    let class_cap = plan.map_or(config.class_cap.min(config.path_cap), |plan| plan.count);
                    let export = !counting && ordinal % config.sample_stride == 0;
                    let selected: Vec<_> = {
                        let raw = if let Some(packed) = &packed_bits {
                            bits_text(&model.get_exp(packed)?.unwrap_exp())
                        } else {
                            String::new()
                        };
                        if let Some(diagnostic) = &mut diagnostic {
                            let mut record_assignment = vec![false; records.len()];
                            for (index, value) in order.iter().zip(&assignment) {
                                record_assignment[*index] = *value;
                            }
                            diagnostic.observe(&record_assignment, &raw);
                        }
                        bit_predicates
                            .iter()
                            .enumerate()
                            .skip(depth)
                            .map(|(index, bit)| {
                                if raw.as_bytes()[2 + index] == b'1' {
                                    bit.clone()
                                } else {
                                    Not(Box::new(bit.clone()))
                                }
                            })
                            .collect()
                    };
                    drop(model);
                    if export {
                        let context = crate::smt::Context::new(crate::smt::Config::new());
                        let mut representative_solver = Solver::new_seeded(&context, 0);
                        for event in &replay_events {
                            representative_solver.add_event(event.clone());
                        }
                        let condition = selected
                            .iter()
                            .fold(prefix.clone(), |condition, bit| And(Box::new(condition), Box::new(bit.clone())));
                        assert!(satisfiable(&mut representative_solver, &condition)?, "DFS 见证必须可重放");
                        let mut model = Model::new(&representative_solver);
                        model.set_complete_model(true);
                        // 每个完整符号只取一次；本地截取所有重复或重叠片段。
                        let inputs: std::collections::BTreeMap<_, _> = symbols
                            .iter()
                            .map(|symbol| {
                                let value = model.get_exp(&Var(Sym { id: *symbol }))?.unwrap_exp();
                                Ok((*symbol, bits_text(&value)))
                            })
                            .collect::<Result<_, ExecError>>()?;
                        let values: Vec<_> = expressions
                            .iter()
                            .map(|(symbol, hi, lo)| {
                                let value = &inputs[symbol];
                                format!("#b{}", &value[value.len() - 1 - *hi as usize..value.len() - *lo as usize])
                            })
                            .collect();
                        let representative_result = model.get_val(result)?.to_string(shared);
                        let truncated = plan.map_or(false, |plan| plan.truncated || plan.path_truncated);
                        consume(class_id, solution_count, &values, truncated, &mut model)?;
                        class_exported += 1;
                        exported_samples += 1;
                        if retain_solutions {
                            solutions.push(
                                json!({"slice_values":values, "representative":{"result":representative_result}}),
                            );
                        }
                    }
                    projection_time += projected.elapsed();
                    solution_count += 1;
                    total += 1;
                    if measuring && total % 4096 == 0 {
                        measure("progress", class_count, total);
                    }
                    // 模型见证直接选择后续位分支；前沿仍通过 SAT 检查剪枝。
                    if solution_count == class_cap || ((partition.is_none() || probing) && total == config.path_cap) {
                        let leaf =
                            selected.iter().fold(Bool(true), |leaf, bit| And(Box::new(leaf), Box::new(bit.clone())));
                        let rest = And(Box::new(prefix), Box::new(Not(Box::new(leaf))));
                        let rest = remaining
                            .iter()
                            .fold(rest, |rest, (condition, _)| Or(Box::new(rest), Box::new(condition.clone())));
                        let queried = std::time::Instant::now();
                        truncated = satisfiable(solver, &rest)?;
                        sat_time += queried.elapsed();
                        sat_checks += 1;
                        path_truncated |= (partition.is_none() || probing) && truncated && total == config.path_cap;
                        break;
                    }
                    // 下一次从最深未访问分支开始；所选分支由当前模型直接剪枝。
                    let mut prefix = prefix;
                    for (index, selected) in selected.into_iter().enumerate() {
                        remaining.push((
                            And(Box::new(prefix.clone()), Box::new(Not(Box::new(selected.clone())))),
                            depth + index + 1,
                        ));
                        prefix = And(Box::new(prefix), Box::new(selected));
                    }
                    while let Some((prefix, depth)) = remaining.pop() {
                        let queried = std::time::Instant::now();
                        let feasible = satisfiable(solver, &prefix)?;
                        sat_time += queried.elapsed();
                        sat_checks += 1;
                        if feasible {
                            candidate = Some((prefix, depth));
                            break;
                        }
                    }
                }
                if probing || (!counting && class_exported > 0) {
                    let class_id = plans.map_or(class_count, |plans| plans[&assignment].class_id);
                    let mut record_assignment = vec![false; records.len()];
                    for (index, value) in order.iter().zip(assignment) {
                        record_assignment[*index] = value;
                    }
                    let guard_assignment: serde_json::Map<_, _> = records
                        .iter()
                        .zip(record_assignment)
                        .map(|(record, value)| (record.record_id.to_string(), json!(value)))
                        .collect();
                    if !probing {
                        if let Some(complete) = complete {
                            complete(
                                class_id,
                                &json!({"guard_assignment":guard_assignment, "tested_slices":tested, "solution_count":class_exported}),
                            )?;
                        }
                    }
                    classes.push(json!({"class_id":class_id, "guard_assignment":guard_assignment,
                    "counted_paths":solution_count,
                    "solution_count":class_exported, "solutions":solutions, "truncated":truncated}));
                }
                class_count += 1;
                truncated_classes += usize::from(truncated);
                if shared.execution_stats.enabled() && class_count % 4096 == 0 {
                    eprintln!("[MERGE_ENUMERATION_PROGRESS] stride={} 类={class_count} 解={total} 已导出={exported_samples} 耗时={:?} SAT次数={sat_checks} SAT耗时={sat_time:?} 投影耗时={projection_time:?}", config.sample_stride, started.elapsed());
                }
                if path_truncated {
                    break;
                }
            }
            if measuring {
                measure("partition_complete", class_count, total);
            }
            if partition.is_none() {
                shared.execution_stats.enumeration_counted(
                    class_count,
                    total,
                    truncated_classes,
                    path_truncated,
                    config.sample_stride,
                    exported_samples,
                );
            }
            if counting && !probing {
                if let Some(diagnostic) = &diagnostic {
                    diagnostic.finish(&replay_events, class_count, total, path_truncated, truncated_classes)?;
                }
                if shared.execution_stats.enabled() {
                    eprintln!("[MERGE_ENUMERATION_COUNT] 类={class_count} 解={total} 耗时={:?} SAT次数={sat_checks} SAT耗时={sat_time:?} 投影耗时={projection_time:?}", started.elapsed());
                }
                return Ok(Some(json!({"schema_version":2, "mode":"count", "counted_classes":class_count,
                    "counted_paths":total, "truncated_classes":truncated_classes,
                    "sample_stride":config.sample_stride, "exported_samples":exported_samples,
                    "path_truncated":path_truncated, "class_cap":config.class_cap, "path_cap":config.path_cap})));
            }
            let guard_records: Vec<_> = records.iter().map(|record| json!({"record_id":record.record_id, "parent_record":record.parent_record,
                "arm":record.arm, "condition":{"symbol":format!("v{}", record.condition.id), "smt_id":record.condition.id},
                "source_loc":record.source_loc, "function":zencode::decode(shared.symtab.to_str(record.function)),
                "branch_pc":record.branch_pc})).collect();
            Ok(Some(
                json!({"schema_version":2, "guard_records":guard_records, "tested_slices":tested, "guard_classes":classes,
                "path_truncated":path_truncated, "enumerated_total":exported_samples,
                "sample_stride":config.sample_stride, "counted_classes":class_count, "counted_paths":total,
                "exported_samples":exported_samples, "truncated_classes":truncated_classes, "class_cap":config.class_cap, "path_cap":config.path_cap}),
            ))
        };
        let output = if counting || partition.is_some() {
            solver.with_incremental_checks(enumerate)
        } else {
            let context = crate::smt::Context::new(crate::smt::Config::new());
            let mut projection_solver = Solver::new_seeded(&context, 0);
            for event in &replay_events {
                projection_solver.add_event(event.clone());
            }
            let projection_tx = projection_solver.start_transaction();
            let output = projection_solver.with_incremental_checks(enumerate);
            projection_solver.rollback_transaction(projection_tx);
            output
        };
        solver.rollback_transaction(tx);
        output
    }
}

#[cfg(test)]
#[path = "tests/merge_enumeration_reference.rs"]
mod reference;
