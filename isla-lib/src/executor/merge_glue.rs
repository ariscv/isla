//! ISLA_ENUM_GLUE 的只读依赖消融；不修改 Support 的传播规则或预测算法。
use super::*;

const CATEGORIES: [&str; 4] = ["class_literal", "memory_alias_consistency", "full_operand_fallback", "other"];

impl PredictionGraph {
    fn features(&self, expression: &Formula<Sym>) -> (bool, Vec<Value>, Vec<u32>) {
        use Formula::*;
        let mut pending = vec![expression.clone()];
        let mut visited = HashSet::new();
        let mut memory = false;
        let mut wide = std::collections::BTreeMap::new();
        while let Some(mut expression) = pending.pop() {
            expression.modify(&mut |node| {
                match node {
                    Var(symbol) => {
                        memory |= matches!(self.support.types.get(symbol), Some(smtlib::Ty::Array(..)));
                        if visited.insert(symbol.id) {
                            if let Some(definition) = self.support.definitions.get(symbol) {
                                pending.push(definition.clone());
                            }
                        }
                    }
                    Select(..) | Store(..) => memory = true,
                    _ => (),
                }
                let operand = match &*node {
                    Eq(a, _) | Neq(a, _) | Bvadd(a, _) | Bvsub(a, _) | Bvmul(a, _)
                    | Bvult(a, _) | Bvslt(a, _) | Bvule(a, _) | Bvsle(a, _)
                    | Bvuge(a, _) | Bvsge(a, _) | Bvugt(a, _) | Bvsgt(a, _)
                    | Bvshl(a, _) | Bvlshr(a, _) | Bvashr(a, _)
                    | Bvudiv(a, _) | Bvsdiv(a, _) | Bvurem(a, _) | Bvsrem(a, _) | Bvsmod(a, _) => Some(a.as_ref()),
                    _ => None,
                };
                if let Some(width) = operand.and_then(|operand| self.support.width(operand)).filter(|width| *width > 1) {
                    let formula = format!("{node:?}");
                    let operator = formula.split('(').next().unwrap();
                    wide.insert(formula.clone(), json!({"operator":operator,"width":width,"summary":formula.chars().take(220).collect::<String>()}));
                }
            });
        }
        let mut visited: Vec<_> = visited.into_iter().collect();
        visited.sort();
        (memory, wide.into_values().collect(), visited)
    }

    /// 仅重算原语法图。正负极性不改变 Support，故这里不需要按类解 SMT。
    pub(super) fn explain(&mut self, bits: &[Formula<Sym>], literals: &[Formula<Sym>]) -> Value {
        let (candidate, verified) = self.groups(bits, literals);
        let constraints: Vec<_> = self.constraints.iter().chain(literals).cloned().collect();
        let dependencies: Vec<_> = constraints.iter().map(|e| self.support.collect(e, None)).collect();
        let mut owners = std::collections::BTreeMap::<Atom, std::collections::BTreeSet<usize>>::new();
        for (group, indices) in candidate.iter().enumerate() {
            for index in indices {
                for atom in self.support.collect(&bits[*index], None) {
                    owners.entry(atom).or_default().insert(group);
                }
            }
        }
        let mut uses = std::collections::BTreeMap::<Atom, Vec<usize>>::new();
        for (index, atoms) in dependencies.iter().enumerate() {
            for atom in atoms {
                uses.entry(*atom).or_default().push(index);
            }
        }
        // 将约束也作为节点，复用同一 partition 查找通过隐藏原子传递的连接。
        let mut nodes = bits.to_vec();
        nodes.extend(constraints.iter().cloned());
        let connected = partition(&nodes, &[], &mut self.support);
        let mut bit_group = vec![0; bits.len()];
        for (group, indices) in candidate.iter().enumerate() {
            for index in indices {
                bit_group[*index] = group;
            }
        }
        let mut reachable = vec![std::collections::BTreeSet::new(); constraints.len()];
        for group in connected {
            let touched: std::collections::BTreeSet<_> =
                group.iter().filter(|index| **index < bits.len()).map(|index| bit_group[*index]).collect();
            for index in group.into_iter().filter(|index| *index >= bits.len()) {
                reachable[index - bits.len()] = touched.clone();
            }
        }
        let mut categories = Vec::new();
        let mut bridges = Vec::new();
        let mut counts = std::collections::BTreeMap::<&str, usize>::new();
        for (index, expression) in constraints.iter().enumerate() {
            let (memory, wide, symbols) = self.features(expression);
            let category = if index >= self.constraints.len() {
                CATEGORIES[0]
            } else if memory {
                CATEGORIES[1]
            } else if !wide.is_empty() {
                CATEGORIES[2]
            } else {
                CATEGORIES[3]
            };
            categories.push(category);
            *counts.entry(category).or_default() += 1;
            let direct: std::collections::BTreeSet<_> =
                dependencies[index].iter().filter_map(|atom| owners.get(atom)).flatten().copied().collect();
            let hidden = dependencies[index].iter().any(|atom| !owners.contains_key(atom) && uses[atom].len() > 1);
            if reachable[index].len() < 2 || (direct.len() < 2 && !hidden) {
                continue;
            }
            let atoms: Vec<_> = dependencies[index].iter().filter(|atom| owners.contains_key(atom) || uses[atom].len()>1).map(|atom| {
                let groups = owners.get(atom).cloned().unwrap_or_default();
                let ty = self.support.types.get(&Sym {id:atom.0});
                json!({"symbol":format!("v{}",atom.0),"smt_id":atom.0,"bit":atom.1,
                    "kind":if atom.1.is_some() {"bit"} else if matches!(ty,Some(smtlib::Ty::Array(..))) {"array"} else {"boolean_enum_or_function"},
                    "direct_components":groups,"constraint_uses":uses[atom]})
            }).collect();
            bridges.push(json!({"constraint_id":index,"origin":if index<self.constraints.len() {"path_assertion"} else {"class_literal"},
                "class_literal_index":if index<self.constraints.len() {None} else {Some(index-self.constraints.len())},
                "category":category,"summary":format!("{expression:?}").chars().take(280).collect::<String>(),"formula":format!("{expression:?}"),
                "direct_components":direct,"transitive_components":reachable[index],"bridge_atoms":atoms,
                "has_memory":memory,"has_full_operand_fallback":!wide.is_empty(),"full_operand_sites":wide,"definition_symbols":symbols}));
        }
        let mut ablation = serde_json::Map::new();
        for category in CATEGORIES {
            let kept: Vec<_> = constraints
                .iter()
                .zip(&categories)
                .filter(|(_, kind)| **kind != category)
                .map(|(e, _)| e.clone())
                .collect();
            ablation.insert(category.into(), json!(partition(bits, &kept, &mut self.support).len()));
        }
        let without_wide: Vec<_> =
            constraints.iter().filter(|expression| self.features(expression).1.is_empty()).cloned().collect();
        let without_memory: Vec<_> =
            constraints.iter().filter(|expression| !self.features(expression).0).cloned().collect();
        let path_only = partition(bits, &self.constraints, &mut self.support).len();
        let class_only = partition(bits, literals, &mut self.support).len();
        let neither: Vec<_> = constraints
            .iter()
            .zip(&categories)
            .filter(|(_, kind)| **kind != CATEGORIES[0] && **kind != CATEGORIES[1])
            .map(|(e, _)| e.clone())
            .collect();
        let polarity = literals.iter().all(|literal| {
            self.support.collect(literal, None) == self.support.collect(&Formula::Not(Box::new(literal.clone())), None)
        });
        json!({"candidate_components":candidate.len(),"verified_components":verified.len(),"candidate_partition":candidate,"verified_partition":verified,
            "constraint_counts":counts,"ablation":ablation,"path_assertions_only":path_only,"class_literals_only":class_only,
            "feature_ablation":{"without_any_full_operand_fallback":partition(bits,&without_wide,&mut self.support).len(),"without_any_memory":partition(bits,&without_memory,&mut self.support).len()},
            "without_class_and_memory":partition(bits,&neither,&mut self.support).len(),"without_all":partition(bits,&[],&mut self.support).len(),
            "polarity_invariant":polarity,"bridges":bridges})
    }

    pub(in super::super) fn diagnose<B: BV>(
        directory: &std::path::Path,
        signature: u64,
        events: &[Event<B>],
        guards: &[Formula<Sym>],
        record_ids: &[usize],
        bits: &[Formula<Sym>],
        slices: &[(u32, u32, u32)],
        assignments: &[Vec<bool>],
        records: &[RegionMergeRecord<B>],
        shared: &SharedState<B>,
    ) -> Result<(), ExecError> {
        use Formula::*;
        let started = std::time::Instant::now();
        assert!(!assignments.is_empty(), "完成可行路径必须有守卫类");
        let mut graph = Self::new(events);
        let literals = |assignment: &[bool]| {
            guards
                .iter()
                .zip(assignment)
                .map(|(g, v)| if *v { g.clone() } else { Not(Box::new(g.clone())) })
                .collect::<Vec<_>>()
        };
        // 复现 F5/c57 的守卫候选图：守卫加完整 Extract 切片，不含路径断言。
        let mut guard_nodes = guards.to_vec();
        let mut unique_slices = slices.to_vec();
        unique_slices.sort();
        unique_slices.dedup();
        guard_nodes
            .extend(unique_slices.iter().map(|(symbol, hi, lo)| Extract(*hi, *lo, Box::new(Var(Sym { id: *symbol })))));
        let guard_groups: Vec<Vec<_>> = partition(&guard_nodes, &[], &mut graph.support)
            .into_iter()
            .map(|group| group.into_iter().filter(|index| *index < guards.len()).collect::<Vec<_>>())
            .filter(|group| !group.is_empty())
            .collect();
        let domains: Vec<std::collections::BTreeSet<Vec<bool>>> = guard_groups
            .iter()
            .map(|group| {
                assignments.iter().map(|assignment| group.iter().map(|index| assignment[*index]).collect()).collect()
            })
            .collect();
        let product = domains.iter().fold(num_bigint::BigUint::from(1u8), |product, domain| product * domain.len());
        let first = literals(&assignments[0]);
        let mut report = graph.explain(bits, &first);
        assert!(report["polarity_invariant"].as_bool().unwrap());
        let last = graph.groups(bits, &literals(assignments.last().unwrap())).1;
        assert_eq!(serde_json::to_value(last).unwrap(), report["verified_partition"], "依赖图不应受字面量极性影响");
        let context = crate::smt::Context::new(crate::smt::Config::new());
        let mut solver = Solver::new_seeded(&context, 0);
        for event in events {
            solver.add_event(event.clone());
        }
        let guarded: std::collections::BTreeMap<_, _> = records
            .iter()
            .flat_map(|record| record.memory_reads.iter().map(|(index, guard, _)| (*index, guard.clone())))
            .collect();
        let reads: Vec<_> = events
            .iter()
            .filter(|event| event.is_memory_read_or_write())
            .enumerate()
            .filter_map(|(index, event)| {
                if let Event::ReadMem { address, bytes, .. } = event {
                    Some((index, address, *bytes, guarded.get(&index).cloned().unwrap_or(Bool(true))))
                } else {
                    None
                }
            })
            .collect();
        let tx = solver.start_transaction();
        let queries = solver.with_incremental_checks(|solver| {
            let mut pairs = Vec::new();
            for (i,(left,a,an,ag)) in reads.iter().enumerate() {
                if *an==0 { continue; }
                for (right,b,bn,bg) in reads.iter().skip(i+1) {
                    if *bn==0 { continue; }
                    let a=crate::primop_util::smt_value(a,SourceLoc::unknown())?;
                    let b=crate::primop_util::smt_value(b,SourceLoc::unknown())?;
                    let active=And(Box::new(ag.clone()),Box::new(bg.clone()));
                    let equal=And(Box::new(active.clone()),Box::new(Eq(Box::new(a.clone()),Box::new(b.clone()))));
                    let overlap=Or(Box::new(Bvult(Box::new(Bvsub(Box::new(a.clone()),Box::new(b.clone()))),Box::new(smtlib::bits64(*bn as u64,64)))),
                        Box::new(Bvult(Box::new(Bvsub(Box::new(b),Box::new(a))),Box::new(smtlib::bits64(*an as u64,64)))));
                    let overlap=And(Box::new(active.clone()),Box::new(overlap));
                    pairs.push(json!({"left_read":left,"right_read":right,"active_sat":satisfiable(solver,&active)?,
                        "base_alias_sat":satisfiable(solver,&equal)?,"byte_overlap_sat":satisfiable(solver,&overlap)?,"query":format!("{equal:?}")}));
                }
            }
            Ok::<_,ExecError>(pairs)
        });
        solver.rollback_transaction(tx);
        let queries = queries?;
        // 只对显式选择的路径检查首次类退出精确层的原因；不展开全路径。
        let detailed = std::env::var_os("ISLA_ENUM_GLUE_DETAIL").map_or(false, |values| {
            values
                .to_str()
                .expect("详细路径列表必须为UTF-8")
                .split(',')
                .any(|value| value.parse::<u64>().expect("详细路径列表必须是逗号分隔的u64签名") == signature)
        });
        if detailed {
            let tx = solver.start_transaction();
            let counted = solver.with_incremental_checks(|solver| {
                let class_tx = solver.start_transaction();
                let result = (|| {
                    for literal in &first {
                        solver.add(Def::Assert(literal.clone()));
                    }
                    assert!(satisfiable(solver, &Bool(true))?);
                    super::super::predict::domain_count(solver, bits, 256)
                })();
                solver.rollback_transaction(class_tx);
                result
            });
            solver.rollback_transaction(tx);
            let count = counted?;
            report["first_class_domain_at_cap_256"] =
                json!({"complete":count.is_some(),"exact":count,"lower_bound":count.unwrap_or(257)});
            let definitions: std::collections::BTreeMap<_, _> =
                graph.support.definitions.iter().map(|(sym, e)| (format!("v{}", sym.id), format!("{e:?}"))).collect();
            report["definitions"] = json!(definitions);
            report["projected_bits"] = json!(bits.iter().map(|e| format!("{e:?}")).collect::<Vec<_>>());
        } else {
            report.as_object_mut().unwrap().remove("bridges");
        }
        report["guard_candidate_groups"] = json!(guard_groups);
        report["guard_domain_sizes"] = json!(domains.iter().map(|domain| domain.len()).collect::<Vec<_>>());
        report["guard_domain_product"] = json!(product.to_string());
        report["guard_product_equal"] = json!(product == num_bigint::BigUint::from(assignments.len()));
        report["schema_version"] = json!(1);
        report["path_signature"] = json!(signature);
        report["class_count"] = json!(assignments.len());
        report["first_class_id"] = json!(0);
        report["first_class_guard_values"] = json!(assignments[0]);
        report["record_ids"] = json!(record_ids);
        report["distinct_verified_partitions"] = json!(1);
        report["same_for_all_classes"] = json!(true);
        report["partition_proof"] =
            json!("Support(literal)=Support(Not(literal)); no per-class simplification; first/last checked");
        report["read_alias_queries"] = json!(queries);
        report["read_count"] = json!(reads.len());
        report["guard_records"]=json!(records.iter().map(|r| json!({"record_id":r.record_id,"parent_record":r.parent_record,"arm":r.arm,
            "function":zencode::decode(shared.symtab.to_str(r.function)),"branch_pc":r.branch_pc,"condition":r.condition.id})).collect::<Vec<_>>());
        report["seconds"] = json!(started.elapsed().as_secs_f64());
        std::fs::create_dir_all(directory).expect("创建粘合诊断目录失败");
        std::fs::write(directory.join(format!("glue-{signature}.json")), serde_json::to_vec_pretty(&report).unwrap())
            .expect("写粘合诊断失败");
        eprintln!(
            "[ENUM_GLUE] {}",
            json!({"path_signature":signature,"classes":assignments.len(),"candidate_components":report["candidate_components"],
            "verified_components":report["verified_components"],"seconds":started.elapsed().as_secs_f64()})
        );
        Ok(())
    }
}
