//! 在守卫前缀上拆分两级 DFS；线程各自重放原迹，合并后按守卫位串分配类号和预算。
use super::*;
use crate::config::MergeEnumerationMode;
use std::sync::{Arc, Condvar, Mutex};

static THREAD_BUDGET: (Mutex<usize>, Condvar) = (Mutex::new(0), Condvar::new());

pub(super) struct ThreadBudget(usize);

pub(super) fn reserve_threads(workers: usize, configured: usize) -> ThreadBudget {
    assert!(workers > 0 && workers <= configured);
    let process_budget = std::thread::available_parallelism().unwrap().get().min(16).max(configured);
    let mut active = THREAD_BUDGET.0.lock().unwrap();
    while active.checked_add(workers).unwrap() > process_budget {
        active = THREAD_BUDGET.1.wait(active).unwrap();
    }
    *active += workers;
    ThreadBudget(workers)
}

impl Drop for ThreadBudget {
    fn drop(&mut self) {
        let mut active = THREAD_BUDGET.0.lock().unwrap();
        *active = active.checked_sub(self.0).unwrap();
        THREAD_BUDGET.1.notify_all();
    }
}

pub(super) struct Partition {
    pub(super) id: usize,
    pub(super) condition: Formula<Sym>,
    pub(super) depth: usize,
}

pub(super) struct ClassPlan {
    pub(super) class_id: usize,
    pub(super) ordinal: usize,
    pub(super) count: usize,
    pub(super) truncated: bool,
    pub(super) path_truncated: bool,
    pub(super) partition: usize,
}

pub(super) fn enumerate<B: BV>(
    frame: &LocalFrame<B>,
    solver: &mut Solver<B>,
    state: &TaskState<B>,
    shared: &SharedState<B>,
    result: &Val<B>,
    consume: &SampleConsumer<'_, B>,
    complete: Option<&ClassConsumer<'_>>,
    retain_solutions: bool,
    guard_catalog: bool,
) -> Result<Value, ExecError> {
    use Formula::*;
    let config = &state.execution_limits.as_ref().unwrap().merge_enumeration;
    assert!(config.enumeration_threads > 0, "枚举线程数必须大于零");
    assert_eq!(solver.transaction_depth(), 0, "仅在路径结束后枚举");
    if guard_catalog {
        assert_eq!(config.mode, MergeEnumerationMode::Count);
        assert_eq!(config.class_cap, 1);
        assert_eq!(config.path_cap, usize::MAX);
    }
    let streaming = config.max_output_bytes.is_some() && config.mode == MergeEnumerationMode::Samples;
    let guard_state = if streaming {
        let mut limits = state.execution_limits.as_ref().unwrap().clone();
        limits.merge_enumeration.class_cap = 1;
        limits.merge_enumeration.path_cap = usize::MAX;
        limits.merge_enumeration.max_output_bytes = None;
        Some(TaskState::<B>::new().with_execution_limits(limits))
    } else {
        None
    };
    let accepted = std::sync::atomic::AtomicUsize::new(0);
    let cancelled = Mutex::new(None);
    let stream_consume = |class, solution, slices: &[String], truncated, model: &mut Model<B>| {
        use std::sync::atomic::Ordering;
        if let Some(reason) = *cancelled.lock().unwrap() {
            return Err(ExecError::SampleOutputStopped(reason));
        }
        if accepted
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |value| (value < config.path_cap).then(|| value + 1))
            .is_err()
        {
            *cancelled.lock().unwrap() = Some("path_cap");
            return Err(ExecError::SampleOutputStopped("path_cap"));
        }
        match consume(class, solution, slices, truncated, model) {
            Ok(()) => Ok(()),
            Err(ExecError::SampleOutputStopped(reason)) => {
                *cancelled.lock().unwrap() = Some(reason);
                Err(ExecError::SampleOutputStopped(reason))
            }
            Err(error) => Err(error),
        }
    };
    let started = std::time::Instant::now();
    let records = &frame.region_merge_records;
    let by_id: HashMap<_, _> = records.iter().map(|record| (record.record_id, record)).collect();
    assert_eq!(records.len(), by_id.len(), "帧内记录编号必须唯一");
    let mut contexts = HashMap::new();
    for record in records {
        context(record, &by_id, &mut HashSet::new(), &mut contexts);
    }
    let order = guard_order(records);
    let replay_events: Vec<_> = solver.trace().to_vec().into_iter().rev().cloned().collect();
    // 只选择原路径和活动上下文中两种极性均可行的分裂守卫。
    let context = crate::smt::Context::new(crate::smt::Config::new());
    let mut partition_solver = Solver::new_seeded(&context, 0);
    for event in &replay_events {
        partition_solver.add_event(event.clone());
    }
    let mut partitions = vec![Partition { id: 0, condition: Bool(true), depth: 0 }];
    let transaction = partition_solver.start_transaction();
    let split = partition_solver.with_incremental_checks(|solver| {
        // 调用方可传入空域；仅对已经证明可满足的根前缀要求子分支非空。
        if !satisfiable(solver, &Bool(true))? {
            return Ok(());
        }
        // 先证明每个前缀可满足，再把任务数增加到线程数的四倍；空前缀不占工作线程。
        // 单线程沿用单任务，路径/类预算仍由下面的规范类目录统一分配。
        // 当全路径预算最多容纳一个满额类时，更多预计数分区只会放大被丢弃的工作。
        let task_target = if config.enumeration_threads == 1 || config.path_cap <= config.class_cap {
            config.enumeration_threads
        } else {
            config.enumeration_threads.checked_mul(4).unwrap()
        };
        for (position, index) in order.iter().enumerate() {
            if partitions.len() >= task_target {
                break;
            }
            let record = &records[*index];
            let predicate = And(Box::new(contexts[&record.record_id].clone()), Box::new(Var(record.condition)));
            let current = std::mem::take(&mut partitions);
            let remaining = current.len();
            let mut next = Vec::new();
            for (offset, partition) in current.into_iter().enumerate() {
                if next.len() + remaining - offset >= task_target {
                    next.push(partition);
                    continue;
                }
                let previous = next.len();
                for value in [false, true] {
                    let condition = And(
                        Box::new(partition.condition.clone()),
                        Box::new(if value { predicate.clone() } else { Not(Box::new(predicate.clone())) }),
                    );
                    if satisfiable(solver, &condition)? {
                        next.push(Partition { id: 0, condition, depth: position + 1 });
                    }
                }
                assert!(next.len() > previous, "已证明可满足的前缀必须至少有一个可行子分支");
            }
            partitions = next;
        }
        Ok::<_, ExecError>(())
    });
    partition_solver.rollback_transaction(transaction);
    split?;
    for (index, partition) in partitions.iter_mut().enumerate() {
        partition.id = index;
    }
    drop(partition_solver);
    drop(context);
    let workers = config.enumeration_threads.min(partitions.len());
    let measuring =
        config.mode == MergeEnumerationMode::Count && std::env::var("ISLA_ENUM_MEASURE").as_deref() == Ok("1");
    if measuring {
        eprintln!(
            "[MERGE_ENUMERATION_MEASURE] {}",
            json!({"phase":"started",
            "path_signature":frame.path_signature(), "partitions":partitions.len()})
        );
    }
    // 路径内线程数为 1 时仍允许既有的跨路径并发，避免串行化 -T 的完成路径。
    let budget = reserve_threads(workers, config.enumeration_threads);
    let next_probe = std::sync::atomic::AtomicUsize::new(0);
    let next_export = std::sync::atomic::AtomicUsize::new(0);
    let output = std::thread::scope(|scope| {
        let (sender, receiver) = std::sync::mpsc::channel();
        let mut handles = Vec::new();
        let mut plan_senders = Vec::new();
        for _ in 0..workers {
            let sender = sender.clone();
            let partitions = &partitions;
            let replay_events = &replay_events;
            let guard_state = guard_state.as_ref();
            let stream_consume = &stream_consume;
            let next_probe = &next_probe;
            let next_export = &next_export;
            let (plan_sender, plan_receiver) = std::sync::mpsc::channel::<Arc<HashMap<Vec<bool>, ClassPlan>>>();
            plan_senders.push(plan_sender);
            handles.push(scope.spawn(move || {
                // Event<B> 在编译期满足 Send + Sync；没有跨线程传递 Z3 AST/Context。
                let context = crate::smt::Context::new(crate::smt::Config::new());
                let mut solver = Solver::new_seeded(&context, 0);
                for event in replay_events {
                    solver.add_event(event.clone());
                }
                let mut probes = Vec::new();
                loop {
                    let index = next_probe.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if index >= partitions.len() {
                        break;
                    }
                    let output = frame.enumerate_merges_partition(
                        &mut solver,
                        guard_state.unwrap_or(state),
                        shared,
                        result,
                        &|_, _, _, _, _| unreachable!(),
                        None,
                        true,
                        Some(&partitions[index]),
                        None,
                    );
                    if shared.execution_stats.enabled() {
                        if let Ok(Some(output)) = &output {
                            eprintln!(
                                "[MERGE_ENUMERATION_PROGRESS] 阶段=分区计数 分区={index} 类={} 解={} 耗时={:?}",
                                output["counted_classes"],
                                output["counted_paths"],
                                started.elapsed()
                            );
                        }
                    }
                    probes.push((index, output));
                }
                sender.send(probes).unwrap();
                drop(sender);
                let selected = plan_receiver.recv().expect("协调线程必须提交计划或显式取消");
                if config.mode == MergeEnumerationMode::Count || selected.is_empty() {
                    return Ok(Vec::new());
                }
                let mut outputs = Vec::new();
                loop {
                    let index = next_export.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if index >= partitions.len() {
                        break;
                    }
                    if !selected.values().any(|plan| plan.partition == index) {
                        continue;
                    }
                    let output = frame
                        .enumerate_merges_partition(
                            &mut solver,
                            state,
                            shared,
                            result,
                            if streaming { stream_consume } else { consume },
                            complete,
                            retain_solutions,
                            Some(&partitions[index]),
                            Some(&selected),
                        )?
                        .unwrap();
                    outputs.push(output);
                }
                Ok::<_, ExecError>(outputs)
            }));
        }
        drop(sender);
        let mut probes = Vec::new();
        let mut error = None;
        let mut batches = 0;
        for batch in receiver {
            batches += 1;
            for (partition, output) in batch {
                match output {
                    Ok(Some(output)) => probes.push((partition, output)),
                    Ok(None) => unreachable!("启用枚举必须返回结果"),
                    Err(failure) => error = Some(failure),
                }
            }
        }
        if batches != workers {
            for sender in &plan_senders {
                sender.send(Arc::new(HashMap::new())).unwrap();
            }
            for handle in handles {
                handle.join().unwrap()?;
            }
            unreachable!("工作线程缺少结果时必须存在 panic");
        }
        // 错误也必须唤醒等待的工作线程，再回传原错误。
        if let Some(error) = error {
            for sender in &plan_senders {
                sender.send(Arc::new(HashMap::new())).unwrap();
            }
            for handle in handles {
                handle.join().unwrap()?;
            }
            return Err(error);
        }
        probes.sort_by_key(|(partition, _)| *partition);
        let first = &probes.first().unwrap().1;
        let guard_records = first["guard_records"].clone();
        let tested_slices = first["tested_slices"].clone();
        let mut classes = std::collections::BTreeMap::new();
        let mut path_truncated =
            !streaming && probes.iter().any(|(_, output)| output["path_truncated"].as_bool().unwrap());
        for (partition, output) in probes {
            for class in output["guard_classes"].as_array().unwrap() {
                let key: Vec<_> = order
                    .iter()
                    .map(|index| class["guard_assignment"][records[*index].record_id.to_string()].as_bool().unwrap())
                    .collect();
                let count = class["counted_paths"].as_u64().unwrap() as usize;
                let truncated = !streaming && class["truncated"].as_bool().unwrap();
                assert!(classes.insert(key, (partition, count, truncated)).is_none(), "前缀分区不得重复守卫赋值");
            }
        }
        let mut selected = HashMap::new();
        let mut total = 0usize;
        let mut truncated_classes = 0;
        let mut partition_counts = vec![(0usize, 0usize); partitions.len()];
        for (key, (partition, count, truncated)) in classes {
            if total == config.path_cap {
                path_truncated = true;
                break;
            }
            assert!(count > 0);
            let kept = count.min(config.path_cap - total);
            let truncated = truncated || kept < count;
            let class_id = selected.len();
            selected.insert(
                key,
                ClassPlan {
                    class_id,
                    ordinal: if streaming { 0 } else { total },
                    count: if streaming { config.class_cap } else { kept },
                    truncated,
                    path_truncated: false,
                    partition,
                },
            );
            total += kept;
            truncated_classes += usize::from(truncated);
            partition_counts[partition].0 += 1;
            partition_counts[partition].1 += kept;
            path_truncated |= kept < count || (truncated && total == config.path_cap);
        }
        for plan in selected.values_mut() {
            plan.path_truncated = path_truncated;
        }
        let selected = Arc::new(selected);
        for sender in plan_senders {
            sender.send(selected.clone()).unwrap();
        }
        let mut outputs = Vec::new();
        for handle in handles {
            outputs.extend(handle.join().unwrap()?);
        }
        let by_class: HashMap<_, _> = selected.values().map(|plan| (plan.class_id, plan)).collect();
        if streaming {
            total = outputs.iter().map(|output| output["counted_paths"].as_u64().unwrap() as usize).sum();
            path_truncated |= outputs.iter().any(|output| output["path_truncated"].as_bool().unwrap());
            truncated_classes = outputs
                .iter()
                .flat_map(|output| output["guard_classes"].as_array().unwrap())
                .filter(|class| class["truncated"].as_bool().unwrap())
                .count();
            partition_counts.fill((0, 0));
            for output in &outputs {
                for class in output["guard_classes"].as_array().unwrap() {
                    let plan = by_class[&(class["class_id"].as_u64().unwrap() as usize)];
                    partition_counts[plan.partition].0 += 1;
                    partition_counts[plan.partition].1 += class["counted_paths"].as_u64().unwrap() as usize;
                }
            }
        }
        let counted_classes = if streaming {
            outputs.iter().map(|output| output["guard_classes"].as_array().unwrap().len()).sum()
        } else {
            selected.len()
        };
        let partition_json: Vec<_> = partition_counts
            .iter()
            .enumerate()
            .map(|(index, (classes, paths))| {
                if shared.execution_stats.enabled() {
                    eprintln!(
                        "[MERGE_ENUMERATION_PARTITION] 分区={index} 类={classes} 解={paths} 线程={workers} 耗时={:?}",
                        started.elapsed()
                    );
                }
                json!({"partition_id":index,"counted_classes":classes,"counted_paths":paths})
            })
            .collect();
        let mut classes = Vec::new();
        let mut exported_samples = 0;
        for output in outputs {
            for mut class in output["guard_classes"].as_array().unwrap().iter().cloned() {
                let key: Vec<_> = order
                    .iter()
                    .map(|index| class["guard_assignment"][records[*index].record_id.to_string()].as_bool().unwrap())
                    .collect();
                let plan = &selected[&key];
                assert_eq!(class["class_id"], plan.class_id);
                if !streaming {
                    class["truncated"] = json!(plan.truncated);
                }
                class.as_object_mut().unwrap().remove("counted_paths");
                exported_samples += class["solution_count"].as_u64().unwrap() as usize;
                classes.push(class);
            }
        }
        classes.sort_by_key(|class| class["class_id"].as_u64().unwrap());
        assert!(classes.windows(2).all(|pair| pair[0]["class_id"] != pair[1]["class_id"]));
        shared.execution_stats.enumeration_counted(
            counted_classes,
            total,
            truncated_classes,
            path_truncated,
            config.sample_stride,
            exported_samples,
        );
        if config.mode == MergeEnumerationMode::Count {
            if measuring {
                eprintln!(
                    "[MERGE_ENUMERATION_MEASURE] {}",
                    json!({"phase":"complete",
                    "path_signature":frame.path_signature(), "counted_classes":counted_classes,
                    "counted_paths":total, "path_truncated":path_truncated, "truncated_classes":truncated_classes})
                );
            }
            let mut output = json!({"schema_version":2,"mode":"count","counted_classes":counted_classes,
                "counted_paths":total,"truncated_classes":truncated_classes,"path_truncated":path_truncated,
                "class_cap":config.class_cap,"path_cap":config.path_cap,"sample_stride":config.sample_stride,
                "exported_samples":0,"enumeration_threads":workers,"partitions":partition_json});
            if guard_catalog {
                let mut assignments: Vec<_> = selected.iter().map(|(values, plan)| (plan.class_id, values)).collect();
                assignments.sort_by_key(|(class, _)| *class);
                output["guard_assignments"] =
                    json!(assignments.into_iter().map(|(_, values)| values).collect::<Vec<_>>());
            }
            return Ok(output);
        }
        let expected = total / config.sample_stride + usize::from(total % config.sample_stride != 0);
        if !streaming {
            assert_eq!(exported_samples, expected, "分区的规范序 ordinal 必须保持 stride 和总预算");
        }
        Ok(
            json!({"schema_version":if retain_solutions { 2 } else { 3 }, "solutions_external":!retain_solutions,"stop_reason":*cancelled.lock().unwrap(),"guard_records":guard_records,"tested_slices":tested_slices,"guard_classes":classes,
            "path_truncated":path_truncated,"enumerated_total":exported_samples,"exported_samples":exported_samples,
            "counted_classes":counted_classes,"counted_paths":total,"truncated_classes":truncated_classes,
            "class_cap":config.class_cap,"path_cap":config.path_cap,"sample_stride":config.sample_stride,
            "enumeration_threads":workers,"partitions":partition_json}),
        )
    });
    drop(budget);
    output
}
