//! 分量域精确计数与 Knuth 随机探测；不物化或导出完整样本。
use super::*;

use num_bigint::BigUint;
use num_traits::ToPrimitive;

struct Probe {
    weight: f64,
    classes: f64,
    assignment: Vec<bool>,
}

fn probe<B: BV>(
    solver: &mut Solver<B>,
    guards: &[Formula<Sym>],
    bits: &[Formula<Sym>],
    excluded: &HashSet<Vec<bool>>,
    coin: &mut impl FnMut() -> bool,
) -> Result<Probe, ExecError> {
    use Formula::*;
    let tx = solver.start_transaction();
    let output = (|| {
        let mut result = Probe { weight: 1.0, classes: 1.0, assignment: Vec::new() };
        if !satisfiable(solver, &Bool(true))? {
            result.weight = 0.0;
            result.classes = 0.0;
            return Ok(result);
        }
        for (level, predicates) in [guards, bits].into_iter().enumerate() {
            for predicate in predicates {
                let negative = Not(Box::new(predicate.clone()));
                let positive = predicate.clone();
                let no = satisfiable(solver, &negative)?;
                let yes = satisfiable(solver, &positive)?;
                assert!(no || yes, "可满足前缀必须存在可满足分支");
                let value = if no && yes {
                    result.weight *= 2.0;
                    coin()
                } else {
                    yes
                };
                if level == 0 {
                    result.assignment.push(value);
                }
                solver.add(Def::Assert(if value { positive } else { negative }));
                assert!(result.weight.is_finite(), "Knuth权重超出数值范围");
            }
            if level == 0 {
                result.classes = result.weight;
                if excluded.contains(&result.assignment) {
                    result.weight = 0.0;
                    return Ok(result);
                }
            }
        }
        Ok(result)
    })();
    solver.rollback_transaction(tx);
    output
}

#[cfg(test)]
fn probe_reference<B: BV>(
    solver: &mut Solver<B>,
    guards: &[Formula<Sym>],
    bits: &[Formula<Sym>],
    excluded: &HashSet<Vec<bool>>,
    coin: &mut impl FnMut() -> bool,
) -> Result<Probe, ExecError> {
    use Formula::*;
    let mut result = Probe { weight: 1.0, classes: 1.0, assignment: Vec::new() };
    if !satisfiable(solver, &Bool(true))? {
        result.weight = 0.0;
        result.classes = 0.0;
        return Ok(result);
    }
    let mut prefix = Bool(true);
    for (level, predicates) in [guards, bits].into_iter().enumerate() {
        for predicate in predicates {
            let negative = And(Box::new(prefix.clone()), Box::new(Not(Box::new(predicate.clone()))));
            let positive = And(Box::new(prefix.clone()), Box::new(predicate.clone()));
            let no = satisfiable(solver, &negative)?;
            let yes = satisfiable(solver, &positive)?;
            assert!(no || yes, "可满足前缀必须存在可满足分支");
            let value = if no && yes {
                result.weight *= 2.0;
                coin()
            } else {
                yes
            };
            if level == 0 {
                result.assignment.push(value);
            }
            prefix = if value { positive } else { negative };
            assert!(result.weight.is_finite(), "Knuth权重超出数值范围");
        }
        if level == 0 {
            result.classes = result.weight;
            if excluded.contains(&result.assignment) {
                result.weight = 0.0;
                return Ok(result);
            }
        }
    }
    Ok(result)
}

fn summarize(values: &[f64]) -> Value {
    assert!(values.len() >= 2 && values.iter().all(|value| value.is_finite() && *value >= 0.0));
    let n = values.len() as f64;
    let mean = values.iter().sum::<f64>() / n;
    let variance = values.iter().map(|value| (value - mean).powi(2)).sum::<f64>() / (n - 1.0);
    let error = (variance / n).sqrt();
    assert!(mean.is_finite() && error.is_finite());
    json!({"n":values.len(),"mean":mean,"standard_error":error,
        "confidence_95":[(mean-1.96*error).max(0.0),mean+1.96*error],
        "interval_method":"normal_approximation_fixed_n"})
}

/// 域查询只遍历一个经依赖证明的分量；达到验证额度时返回未完成证明，转估计层。
fn domain_count<B: BV>(solver: &mut Solver<B>, bits: &[Formula<Sym>], cap: usize) -> Result<Option<usize>, ExecError> {
    use Formula::*;
    let mut free = Vec::new();
    for bit in bits {
        let yes = satisfiable(solver, bit)?;
        let no = satisfiable(solver, &Not(Box::new(bit.clone())))?;
        assert!(yes || no, "已知可行类中的位必须有取值");
        if yes && no {
            free.push(bit.clone());
        }
    }
    let mut pending = vec![(Bool(true), 0)];
    let mut count = 0;
    while let Some((prefix, depth)) = pending.pop() {
        if !satisfiable(solver, &prefix)? {
            continue;
        }
        if depth == free.len() {
            count += 1;
            if count > cap {
                return Ok(None);
            }
        } else {
            pending.push((And(Box::new(prefix.clone()), Box::new(free[depth].clone())), depth + 1));
            pending.push((And(Box::new(prefix), Box::new(Not(Box::new(free[depth].clone())))), depth + 1));
        }
    }
    Ok(Some(count))
}

/// 一级只枚举守卫类，模型引导前缀与现有DFS一致，不展开位组合。
#[cfg(test)]
fn guard_classes<B: BV>(solver: &mut Solver<B>, guards: &[Formula<Sym>]) -> Result<Vec<Vec<bool>>, ExecError> {
    use Formula::*;
    let mut split = Vec::new();
    for guard in guards {
        split.push(satisfiable(solver, guard)? && satisfiable(solver, &Not(Box::new(guard.clone())))?);
    }
    let packed = guards
        .iter()
        .map(|guard| Ite(Box::new(guard.clone()), Box::new(smtlib::bits64(1, 1)), Box::new(smtlib::bits64(0, 1))))
        .reduce(|high, low| Concat(Box::new(high), Box::new(low)));
    let mut pending = vec![(Bool(true), 0)];
    let mut classes = Vec::new();
    while let Some((mut prefix, depth)) = pending.pop() {
        if !satisfiable(solver, &prefix)? {
            continue;
        }
        let mut model = Model::new(solver);
        model.set_complete_model(true);
        let raw = packed
            .as_ref()
            .map(|packed| model.get_exp(packed).map(|value| bits_text(&value.unwrap_exp())))
            .transpose()?;
        drop(model);
        let assignment: Vec<_> =
            guards.iter().enumerate().map(|(index, _)| raw.as_ref().unwrap().as_bytes()[2 + index] == b'1').collect();
        for index in depth..guards.len() {
            if !split[index] {
                continue;
            }
            let selected = if assignment[index] { guards[index].clone() } else { Not(Box::new(guards[index].clone())) };
            pending.push((And(Box::new(prefix.clone()), Box::new(Not(Box::new(selected.clone())))), index + 1));
            prefix = And(Box::new(prefix), Box::new(selected));
        }
        classes.push(assignment);
    }
    classes.sort();
    assert!(classes.windows(2).all(|pair| pair[0] != pair[1]), "守卫类不得重复");
    Ok(classes)
}

pub(super) fn run<B: BV>(
    path_signature: u64,
    events: &[Event<B>],
    guards: &[Formula<Sym>],
    record_ids: &[usize],
    bits: &[Formula<Sym>],
    assignments: Vec<Vec<bool>>,
    config: &crate::config::MergeEnumerationConfig,
) -> Result<Value, ExecError> {
    use Formula::*;
    assert_eq!(guards.len(), record_ids.len());
    assert!(config.predict_probes >= 200 && config.predict_domain_cap > 0);
    let started = std::time::Instant::now();
    let workers = config.enumeration_threads.min(config.predict_probes);
    let budget = parallel::reserve_threads(workers, config.enumeration_threads);
    eprintln!(
        "[MERGE_PREDICT_SAMPLER_START] {}",
        json!({"path_signature":path_signature,"probes":config.predict_probes,
        "guard_depth":guards.len(),"bit_depth":bits.len(),"threads":workers})
    );
    let context = crate::smt::Context::new(crate::smt::Config::new());
    let mut solver = Solver::new_seeded(&context, 0);
    for event in events {
        solver.add_event(event.clone());
    }
    let mut graph = components::PredictionGraph::new(events);
    let tx = solver.start_transaction();
    let exact=solver.with_incremental_checks(|solver| {
        eprintln!("[MERGE_PREDICT_CLASSES] {}",json!({"path_signature":path_signature,"classes":assignments.len(),"seconds":started.elapsed().as_secs_f64()}));
        let mut classes=Vec::new();
        let mut sum=BigUint::from(0u8);
        let mut bounded=BigUint::from(0u8);
        let mut excluded=HashSet::new();
        let mut incomplete=None;
        for assignment in assignments {
            let guard_assignment:serde_json::Map<_,_>=record_ids.iter().zip(&assignment).map(|(id,value)|(id.to_string(),json!(value))).collect();
            if incomplete.is_some() {
                bounded+=BigUint::from(1u8);
                classes.push(json!({"class_id":classes.len(),"guard_values":assignment,"guard_assignment":guard_assignment,
                    "method":"path_knuth_unobserved","distribution":null,"lower_bound":"1"}));
                continue;
            }
            let literals:Vec<_>=guards.iter().zip(&assignment).map(|(guard,value)|if *value {guard.clone()} else {Not(Box::new(guard.clone()))}).collect();
            let (candidate,groups)=graph.groups(bits,&literals);
            let class_tx=solver.start_transaction();
            solver.add(Def::Assert(literals.iter().cloned().fold(Bool(true),|prefix,literal|And(Box::new(prefix),Box::new(literal)))));
            let counted=(|| {
                let mut product=BigUint::from(1u8);
                let mut components=Vec::new();
                for group in &groups {
                    let projected:Vec<_>=group.iter().map(|index|bits[*index].clone()).collect();
                    let Some(count)=domain_count(solver,&projected,config.predict_domain_cap)? else {return Ok(None);};
                    assert!(count>0);product*=count;
                    components.push(json!({"bit_indices":group,"domain_size":count}));
                }
                Ok::<_,ExecError>(Some((product,components)))
            })();
            solver.rollback_transaction(class_tx);
            let Some((product,components))=counted? else {
                incomplete=Some(json!({"reason":"component_domain_exceeds_verification_cap", "guard_values":assignment,
                    "candidate_components":candidate.len(),"verified_components":groups.len(),"domain_cap":config.predict_domain_cap}));
                let lower=config.predict_domain_cap.checked_add(1).unwrap();
                bounded+=BigUint::from(config.class_cap.min(lower));
                classes.push(json!({"class_id":classes.len(),"guard_values":assignment,"guard_assignment":guard_assignment,
                    "method":"path_knuth_unobserved","distribution":null,"lower_bound":lower.to_string()}));
                continue;
            };
            classes.push(json!({"class_id":classes.len(),"guard_values":assignment,"guard_assignment":guard_assignment,
                "method":"exact_component_domains","exact":product.to_string(),"components":components,
                "independence_proof":"disjoint_free_atom_support_including_all_path_assertions_and_class_literals",
                "candidate_components":candidate.len()}));
            assert!(excluded.insert(assignment));
            bounded+=product.clone().min(BigUint::from(config.class_cap));
            sum+=product;
        }
        Ok::<_,ExecError>((classes,sum,bounded,excluded,incomplete))
    });
    solver.rollback_transaction(tx);
    let (mut class_reports, exact_total, bounded_prefix, excluded, incomplete) = exact?;
    drop(solver);
    drop(context);
    let exact_value = exact_total.to_f64().unwrap();
    assert!(exact_value.is_finite());
    let (total, method, class_distribution_complete) = if incomplete.is_none() {
        (
            json!({"exact":exact_total.to_string(),"mean":exact_value,"standard_error":0.0,"confidence_95":[exact_value,exact_value]}),
            "exact",
            true,
        )
    } else {
        let completed = Mutex::new(Vec::new());
        std::thread::scope(|scope| {
            let mut handles = Vec::new();
            for worker in 0..workers {
                let completed = &completed;
                let excluded = &excluded;
                handles.push(scope.spawn(move || {
                    let context=crate::smt::Context::new(crate::smt::Config::new());
                    let mut solver=Solver::new_seeded(&context,0);
                    for event in events {solver.add_event(event.clone());}
                    let tx=solver.start_transaction();
                    let status=solver.with_incremental_checks(|solver| {
                        for index in (worker..config.predict_probes).step_by(workers) {
                            let mix=crate::executor::execution_limits::splitmix64;
                            let mut state=mix(config.predict_seed).wrapping_add(mix(path_signature)).wrapping_add(mix(index as u64));
                            let sample=probe(solver,guards,bits,excluded,&mut || {
                                state=state.wrapping_add(0x9e37_79b9_7f4a_7c15);mix(state)>>63 != 0
                            })?;
                            let mut completed=completed.lock().unwrap();
                            completed.push((index,sample));
                            if completed.len()%32==0 || completed.len()==config.predict_probes {
                                eprintln!("[MERGE_PREDICT_PROGRESS] {}",json!({"path_signature":path_signature,
                                    "completed_probes":completed.len(),"target_probes":config.predict_probes,"seconds":started.elapsed().as_secs_f64()}));
                            }
                        }
                        Ok::<_,ExecError>(())
                    });
                    solver.rollback_transaction(tx);
                    status
                }));
            }
            for handle in handles {
                handle.join().unwrap()?;
            }
            Ok::<_, ExecError>(())
        })?;
        let mut samples = completed.into_inner().unwrap();
        samples.sort_by_key(|(index, _)| *index);
        assert_eq!(samples.len(), config.predict_probes);
        assert!(samples.iter().enumerate().all(|(expected, (index, _))| expected == *index));
        let weights: Vec<_> = samples.iter().map(|(_, sample)| sample.weight).collect();
        let mut total = summarize(&weights);
        total["mean"] = json!(total["mean"].as_f64().unwrap() + exact_value);
        for index in 0..2 {
            total["confidence_95"][index] = json!(total["confidence_95"][index].as_f64().unwrap() + exact_value);
        }
        total["exact_prefix"] = json!(exact_total.to_string());
        for report in class_reports.iter_mut().filter(|report| report["method"] == "path_knuth_unobserved") {
            let assignment: Vec<_> =
                report["guard_values"].as_array().unwrap().iter().map(|value| value.as_bool().unwrap()).collect();
            let observations = samples.iter().filter(|(_, sample)| sample.assignment == assignment).count();
            if observations == 0 {
                continue;
            }
            let values: Vec<_> = samples
                .iter()
                .map(|(_, sample)| if sample.assignment == assignment { sample.weight } else { 0.0 })
                .collect();
            report["method"] = json!("path_knuth_contribution");
            report["observations"] = json!(observations);
            report["distribution"] = summarize(&values);
        }
        let class_weights: Vec<_> = samples.iter().map(|(_, sample)| sample.classes).collect();
        total["estimated_guard_classes"] = summarize(&class_weights);
        (total, "knuth_after_incomplete_component_proof", false)
    };
    drop(budget);
    let bounded_exact = if incomplete.is_none() || bounded_prefix >= BigUint::from(config.path_cap) {
        Some(bounded_prefix.clone().min(BigUint::from(config.path_cap)).to_string())
    } else {
        None
    };
    let output = json!({"schema_version":1,"mode":"predict","path_signature":path_signature,"method":method,
        "total":total,"guard_classes":class_reports,"guard_class_catalog_complete":true,
        "bounded_output":{"class_cap":config.class_cap,"path_cap":config.path_cap,"exact":bounded_exact,
            "lower_bound":bounded_prefix.min(BigUint::from(config.path_cap)).to_string(),"sample_stride":config.sample_stride},"class_distribution_complete":class_distribution_complete,
        "unobserved_classes":"unknown_not_zero","exact_layer_incomplete":incomplete,"probes":if class_distribution_complete {0} else {config.predict_probes},
        "probe_seed":config.predict_seed,"domain_cap":config.predict_domain_cap,"enumeration_threads":workers,
        "guard_depth":guards.len(),"bit_depth":bits.len(),"seconds":started.elapsed().as_secs_f64()});
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::smt::{Config, Context};

    #[test]
    fn predict_256组合精确域乘积与估计区间覆盖真值() {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let input = solver.declare_bitvector(8, SourceLoc::unknown());
        let bits: Vec<_> = (0..8)
            .map(|bit| {
                Formula::Eq(
                    Box::new(Formula::Extract(bit, bit, Box::new(Formula::Var(input)))),
                    Box::new(smtlib::bits64(1, 1)),
                )
            })
            .collect();
        let guards = bits[..2].to_vec();
        let events: Vec<_> = solver.trace().to_vec().into_iter().rev().cloned().collect();
        let config = crate::config::MergeEnumerationConfig {
            predict_probes: 256,
            predict_domain_cap: 256,
            enumeration_threads: 2,
            ..Default::default()
        };
        let catalog = guard_classes(&mut solver, &guards).unwrap();
        let report = run(7, &events, &guards, &[1, 2], &bits, catalog.clone(), &config).unwrap();
        assert_eq!(report["total"]["exact"], "256");
        assert_eq!(report["guard_classes"].as_array().unwrap().len(), 4);
        let estimated = run(
            7,
            &events,
            &guards,
            &[1, 2],
            &bits,
            catalog,
            &crate::config::MergeEnumerationConfig { predict_domain_cap: 1, ..config },
        )
        .unwrap();
        assert!(estimated["total"]["confidence_95"][0].as_f64().unwrap() <= 256.0);
        assert!(estimated["total"]["confidence_95"][1].as_f64().unwrap() >= 256.0);
        assert_eq!(solver.transaction_depth(), 0);
    }

    #[test]
    fn predict_隐藏xor耦合不能把边际域乘积当真值() {
        use Formula::*;
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let vars: Vec<_> = (0..3).map(|_| Var(solver.declare_const(smtlib::Ty::Bool, SourceLoc::unknown()))).collect();
        solver
            .assert(Eq(Box::new(vars[2].clone()), Box::new(Neq(Box::new(vars[0].clone()), Box::new(vars[1].clone())))));
        let events: Vec<_> = solver.trace().to_vec().into_iter().rev().cloned().collect();
        let config = crate::config::MergeEnumerationConfig {
            predict_probes: 256,
            predict_domain_cap: 256,
            enumeration_threads: 1,
            ..Default::default()
        };
        let report = run(9, &events, &[], &[], &vars, vec![vec![]], &config).unwrap();
        assert_eq!(report["total"]["exact"], "4");
        assert_eq!(report["guard_classes"][0]["components"].as_array().unwrap().len(), 1);
    }

    #[test]
    fn predict_保存点探测与固定事件迹前缀参照逐次等价() {
        use Formula::*;
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let vars: Vec<_> = (0..5).map(|_| Var(solver.declare_const(smtlib::Ty::Bool, SourceLoc::unknown()))).collect();
        solver
            .assert(Eq(Box::new(vars[4].clone()), Box::new(Neq(Box::new(vars[0].clone()), Box::new(vars[3].clone())))));
        let tx = solver.start_transaction();
        solver.with_incremental_checks(|solver| {
            let before = solver.trace().to_vec().len();
            let depth = solver.transaction_depth();
            for seed in 0..64u64 {
                let mut a = seed;
                let mut b = seed;
                let first = probe_reference(solver, &vars[..2], &vars, &HashSet::new(), &mut || {
                    a = crate::executor::execution_limits::splitmix64(a);
                    a >> 63 != 0
                })
                .unwrap();
                let second = probe(solver, &vars[..2], &vars, &HashSet::new(), &mut || {
                    b = crate::executor::execution_limits::splitmix64(b);
                    b >> 63 != 0
                })
                .unwrap();
                assert_eq!(first.weight, second.weight);
                assert_eq!(first.classes, second.classes);
                assert_eq!(first.assignment, second.assignment);
                assert_eq!(solver.trace().to_vec().len(), before);
                assert_eq!(solver.transaction_depth(), depth);
            }
        });
        solver.rollback_transaction(tx);
    }

    #[test]
    fn predict_不平衡三叶树探测按分支概率加权() {
        use Formula::*;
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let x = Var(solver.declare_const(smtlib::Ty::Bool, SourceLoc::unknown()));
        let y = Var(solver.declare_const(smtlib::Ty::Bool, SourceLoc::unknown()));
        solver.assert(Or(Box::new(x.clone()), Box::new(Not(Box::new(y.clone())))));
        let tx = solver.start_transaction();
        let values = solver.with_incremental_checks(|solver| {
            [false, true].map(|value| {
                probe(solver, &[], &[x.clone(), y.clone()], &HashSet::new(), &mut || value).unwrap().weight
            })
        });
        solver.rollback_transaction(tx);
        assert_eq!(values, [2.0, 4.0]);
        let summary = summarize(&values);
        assert_eq!(summary["mean"], 3.0);
        assert_eq!(summary["standard_error"], 1.0);
    }
}
