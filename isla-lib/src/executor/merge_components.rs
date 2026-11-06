//! 仅供 ISLA_ENUM_COMPONENTS=1 的只读诊断；不改变枚举输出或预算。
use super::*;

// 自由 BV 按位区分；数组、布尔及函数符号作为不可拆原子。
type Atom = (u32, Option<u32>);
type Atoms = std::collections::BTreeSet<Atom>;

struct Support {
    definitions: HashMap<Sym, Formula<Sym>>,
    types: HashMap<Sym, smtlib::Ty>,
    cache: HashMap<(Sym, Option<(u32, u32)>), Atoms>,
}

impl Support {
    fn new(definitions: HashMap<Sym, Formula<Sym>>, types: HashMap<Sym, smtlib::Ty>) -> Self {
        Self { definitions, types, cache: HashMap::new() }
    }

    fn width(&self, exp: &Formula<Sym>) -> Option<u32> {
        use Formula::*;
        match exp {
            Var(v) => match self.types.get(v) {
                Some(smtlib::Ty::BitVec(n)) => Some(*n),
                _ => self.definitions.get(v).and_then(|e| self.width(e)),
            },
            Bits64(b) => Some(b.len()),
            Bits(b) => Some(b.len() as u32),
            Extract(hi, lo, _) => Some(hi - lo + 1),
            ZeroExtend(n, e) | SignExtend(n, e) => self.width(e).map(|w| w + n),
            Concat(a, b) => Some(self.width(a)? + self.width(b)?),
            Ite(_, a, _) => self.width(a),
            Bvnot(a) | Bvneg(a) => self.width(a),
            Bvand(a, _)
            | Bvor(a, _)
            | Bvxor(a, _)
            | Bvadd(a, _)
            | Bvsub(a, _)
            | Bvmul(a, _)
            | Bvshl(a, _)
            | Bvlshr(a, _)
            | Bvashr(a, _) => self.width(a),
            _ => None,
        }
    }

    fn collect(&mut self, exp: &Formula<Sym>, range: Option<(u32, u32)>) -> Atoms {
        use Formula::*;
        match exp {
            Var(v) => {
                let key = (*v, range);
                if let Some(found) = self.cache.get(&key) {
                    return found.clone();
                }
                let found: Atoms = if let Some(e) = self.definitions.get(v).cloned() {
                    self.collect(&e, range)
                } else if let Some(smtlib::Ty::BitVec(n)) = self.types.get(v) {
                    let (hi, lo) = range.unwrap_or((n - 1, 0));
                    assert!(hi < *n && lo <= hi);
                    (lo..=hi).map(|bit| (v.id, Some(bit))).collect()
                } else {
                    Atoms::from([(v.id, None)])
                };
                self.cache.insert(key, found.clone());
                found
            }
            Extract(hi, lo, e) => {
                let (hi, lo) = range.map(|(h, l)| (h + lo, l + lo)).unwrap_or((*hi, *lo));
                self.collect(e, Some((hi, lo)))
            }
            Bvnot(e) => self.collect(e, range),
            Bvand(a, b) | Bvor(a, b) | Bvxor(a, b) | Bvnand(a, b) | Bvnor(a, b) | Bvxnor(a, b) => {
                let mut found = self.collect(a, range);
                found.extend(self.collect(b, range));
                found
            }
            Concat(a, b) if range.is_some() && self.width(b).is_some() => {
                let (hi, lo) = range.unwrap();
                let width = self.width(b).unwrap();
                let mut found = Atoms::new();
                if hi >= width {
                    found.extend(self.collect(a, Some((hi - width, lo.saturating_sub(width)))));
                }
                if lo < width {
                    found.extend(self.collect(b, Some((hi.min(width - 1), lo))));
                }
                found
            }
            ZeroExtend(_, e) | SignExtend(_, e) if range.is_some() && self.width(e).is_some() => {
                let (hi, lo) = range.unwrap();
                let width = self.width(e).unwrap();
                let mut found = Atoms::new();
                if lo < width {
                    found.extend(self.collect(e, Some((hi.min(width - 1), lo))));
                }
                if hi >= width && matches!(exp, SignExtend(..)) {
                    found.extend(self.collect(e, Some((width - 1, width - 1))));
                }
                found
            }
            Ite(c, a, b) => {
                let mut found = self.collect(c, None);
                found.extend(self.collect(a, range));
                found.extend(self.collect(b, range));
                found
            }
            Bits(_) | Bits64(_) | Enum(_) | Bool(_) | FPConstant(..) | FPRoundingMode(_) => Atoms::new(),
            _ => {
                // 未证明可逐位传播的运算使用完整操作数依赖，仍保留操作数内部的 Extract。
                let children: Vec<&Formula<Sym>> = match exp {
                    Not(a) | Bvneg(a) | ZeroExtend(_, a) | SignExtend(_, a) | FPUnary(_, a) => vec![a],
                    Eq(a, b)
                    | Neq(a, b)
                    | And(a, b)
                    | Or(a, b)
                    | Bvadd(a, b)
                    | Bvsub(a, b)
                    | Bvmul(a, b)
                    | Bvudiv(a, b)
                    | Bvsdiv(a, b)
                    | Bvurem(a, b)
                    | Bvsrem(a, b)
                    | Bvsmod(a, b)
                    | Bvult(a, b)
                    | Bvslt(a, b)
                    | Bvule(a, b)
                    | Bvsle(a, b)
                    | Bvuge(a, b)
                    | Bvsge(a, b)
                    | Bvugt(a, b)
                    | Bvsgt(a, b)
                    | Bvshl(a, b)
                    | Bvlshr(a, b)
                    | Bvashr(a, b)
                    | Concat(a, b)
                    | Select(a, b)
                    | FPBinary(_, a, b)
                    | FPRoundingUnary(_, a, b) => vec![a, b],
                    Store(a, b, c) | FPRoundingBinary(_, a, b, c) => vec![a, b, c],
                    FPfma(a, b, c, d) => vec![a, b, c, d],
                    App(_, args) | Distinct(args) => args.iter().collect(),
                    _ => unreachable!("已在外层匹配的依赖节点"),
                };
                let mut found = Atoms::new();
                if let App(f, _) = exp {
                    found.insert((f.id, None));
                }
                for child in children {
                    found.extend(self.collect(child, None));
                }
                found
            }
        }
    }
}

fn root(parents: &mut [usize], mut n: usize) -> usize {
    while parents[n] != n {
        parents[n] = parents[parents[n]];
        n = parents[n];
    }
    n
}

fn partition(nodes: &[Formula<Sym>], constraints: &[Formula<Sym>], support: &mut Support) -> Vec<Vec<usize>> {
    let mut parents: Vec<_> = (0..nodes.len()).collect();
    let mut atoms = std::collections::BTreeMap::<Atom, usize>::new();
    for (index, exp) in nodes.iter().chain(constraints.iter()).enumerate() {
        let dependencies = support.collect(exp, None);
        let anchor = if index < nodes.len() {
            index
        } else {
            let n = parents.len();
            parents.push(n);
            n
        };
        for atom in dependencies {
            let other = *atoms.entry(atom).or_insert_with(|| {
                let n = parents.len();
                parents.push(n);
                n
            });
            let a = root(&mut parents, anchor);
            let b = root(&mut parents, other);
            parents[b] = a;
        }
    }
    let mut groups = std::collections::BTreeMap::<usize, Vec<usize>>::new();
    for index in 0..nodes.len() {
        groups.entry(root(&mut parents, index)).or_default().push(index);
    }
    let mut groups: Vec<_> = groups.into_values().collect();
    groups.sort_by_key(|group| group[0]);
    groups
}

pub(super) struct Diagnostic {
    guards: usize,
    slices: Vec<(u32, u32, u32)>,
    predicates: Vec<Formula<Sym>>,
    groups: Vec<Vec<usize>>,
    constraint_groups: Vec<Vec<usize>>,
    slice_counts: Vec<usize>,
    guard_domains: Vec<std::collections::BTreeSet<Vec<bool>>>,
    guard_assignments: HashSet<Vec<bool>>,
    witness_domains: Vec<std::collections::BTreeSet<Vec<bool>>>,
    record_ids: Vec<usize>,
    setup_time: std::time::Duration,
}

impl Diagnostic {
    pub(super) fn new<B: BV>(
        records: &[RegionMergeRecord<B>],
        contexts: &HashMap<usize, Formula<Sym>>,
        slices: &[(u32, u32, u32)],
        bits: &std::collections::BTreeSet<(u32, u32)>,
        events: &[Event<B>],
    ) -> Self {
        use Formula::*;
        let started = std::time::Instant::now();
        let mut definitions = HashMap::new();
        let mut types = HashMap::new();
        let mut constraints = Vec::new();
        fn conjuncts(exp: &Formula<Sym>, out: &mut Vec<Formula<Sym>>) {
            if let And(a, b) = exp {
                conjuncts(a, out);
                conjuncts(b, out);
            } else {
                out.push(exp.clone());
            }
        }
        for event in events {
            match event {
                Event::Smt(Def::DeclareConst(v, ty), ..) => {
                    types.insert(*v, ty.clone());
                }
                Event::Smt(Def::DefineConst(v, e), ..) => {
                    definitions.insert(*v, e.clone());
                }
                Event::Smt(Def::Assert(e), ..) => conjuncts(e, &mut constraints),
                _ => (),
            }
        }
        let mut nodes: Vec<_> =
            records.iter().map(|r| And(Box::new(contexts[&r.record_id].clone()), Box::new(Var(r.condition)))).collect();
        let mut predicates = nodes.clone();
        let mut unique = slices.to_vec();
        unique.sort();
        unique.dedup();
        nodes.extend(unique.iter().map(|(v, hi, lo)| Extract(*hi, *lo, Box::new(Var(Sym { id: *v })))));
        predicates.extend(bits.iter().map(|(v, bit)| {
            Eq(Box::new(Extract(*bit, *bit, Box::new(Var(Sym { id: *v })))), Box::new(smtlib::bits64(1, 1)))
        }));
        let mut support = Support::new(definitions, types);
        let constraint_groups = partition(&nodes, &constraints, &mut support);
        // 原断言可能因数组一致性等原因将整路径相连。候选图只用于提出切分，
        // 是否可乘由完整守卫边际域的基数及原约束 SAT 验证决定。
        let node_groups = partition(&nodes, &[], &mut support);
        let slice_counts = node_groups.iter().map(|g| g.iter().filter(|n| **n >= records.len()).count()).collect();
        let groups: Vec<Vec<usize>> = node_groups
            .iter()
            .map(|group| {
                let mut positions: Vec<_> = group.iter().copied().filter(|n| *n < records.len()).collect();
                for (bit_index, (v, bit)) in bits.iter().enumerate() {
                    if group.iter().filter(|n| **n >= records.len()).any(|n| {
                        let (sv, hi, lo) = unique[*n - records.len()];
                        sv == *v && lo <= *bit && *bit <= hi
                    }) {
                        positions.push(records.len() + bit_index);
                    }
                }
                positions
            })
            .collect();
        eprintln!(
            "[ENUM_COMPONENT_GRAPH] {}",
            json!({"record_ids":records.iter().map(|r|r.record_id).collect::<Vec<_>>(),"nodes":node_groups,"constraint_nodes":constraint_groups,"slices":unique})
        );
        Self {
            guards: records.len(),
            slices: unique,
            predicates,
            guard_domains: vec![Default::default(); groups.len()],
            guard_assignments: HashSet::new(),
            witness_domains: vec![Default::default(); groups.len()],
            groups,
            constraint_groups,
            slice_counts,
            record_ids: records.iter().map(|r| r.record_id).collect(),
            setup_time: started.elapsed(),
        }
    }

    pub(super) fn observe(&mut self, guards: &[bool], bits: &str) {
        self.guard_assignments.insert(guards.to_vec());
        let mut values = guards.to_vec();
        values.extend(bits.bytes().skip(2).map(|b| b == b'1'));
        assert_eq!(values.len(), self.predicates.len());
        for (index, group) in self.groups.iter().enumerate() {
            self.guard_domains[index].insert(group.iter().filter(|n| **n < self.guards).map(|n| values[*n]).collect());
            // class_cap=1 只给片段域的见证下界；不把它冒充完整枚举。
            self.witness_domains[index].insert(group.iter().map(|n| values[*n]).collect());
        }
    }

    pub(super) fn finish<B: BV>(
        &self,
        events: &[Event<B>],
        actual: usize,
        paths: usize,
        truncated: bool,
        truncated_classes: usize,
    ) -> Result<(), ExecError> {
        use Formula::*;
        assert_eq!(self.guard_assignments.len(), actual, "类计数必须与去重守卫赋值一致");
        let started = std::time::Instant::now();
        let ctx = crate::smt::Context::new(crate::smt::Config::new());
        let mut solver = Solver::new_seeded(&ctx, 0);
        for event in events {
            solver.add_event(event.clone());
        }
        let sampled: Vec<Vec<_>> = self
            .witness_domains
            .iter()
            .map(|domain| {
                let values: Vec<_> = domain.iter().collect();
                (0..values.len().min(8)).map(|n| values[n * values.len() / values.len().min(8)]).collect()
            })
            .collect();
        let condition = |index: usize, value: &Vec<bool>| {
            self.groups[index].iter().zip(value).fold(Bool(true), |p, (n, v)| {
                let e = self.predicates[*n].clone();
                And(Box::new(p), Box::new(if *v { e } else { Not(Box::new(e)) }))
            })
        };
        let mut checks = 0usize;
        let mut unsat = 0usize;
        let mut joint_checks = 0usize;
        let mut joint_unsat = 0usize;
        let product = self.guard_domains.iter().try_fold(1u128, |p, d| p.checked_mul(d.len() as u128));
        let mut missing_guard_tuple = None;
        let mut missing_tuple_unsat = None;
        if !truncated && product.map_or(false, |n| n > actual as u128) {
            // 完整类集合已有所有守卫取值；从边际笛卡尔积中找一个真实缺失的组合，
            // 再交回原约束求解器，不能把两两抽样未发现反例当成全局独立。
            let domains: Vec<Vec<_>> = self.guard_domains.iter().map(|d| d.iter().collect()).collect();
            let mut positions = vec![0; domains.len()];
            loop {
                let mut assignment = vec![false; self.guards];
                for (i, group) in self.groups.iter().enumerate() {
                    for (node, value) in group.iter().filter(|n| **n < self.guards).zip(domains[i][positions[i]]) {
                        assignment[*node] = *value;
                    }
                }
                if !self.guard_assignments.contains(&assignment) {
                    missing_guard_tuple = Some(assignment);
                    break;
                }
                let mut index = positions.len();
                loop {
                    assert!(index > 0, "基数不等必有缺失守卫组合");
                    index -= 1;
                    positions[index] += 1;
                    if positions[index] < domains[index].len() {
                        break;
                    }
                    positions[index] = 0;
                }
            }
        }
        let tx = solver.start_transaction();
        let verified = solver.with_incremental_checks(|solver| {
            for a in 0..sampled.len() {
                for b in a + 1..sampled.len() {
                    for av in &sampled[a] {
                        for bv in &sampled[b] {
                            checks += 1;
                            unsat += usize::from(!satisfiable(
                                solver,
                                &And(Box::new(condition(a, av)), Box::new(condition(b, bv))),
                            )?);
                        }
                    }
                }
            }
            if sampled.len() > 2 && sampled.iter().all(|d| !d.is_empty()) {
                // 确定性混合 64 个全分量见证，补充检查两两可行遗漏的高阶耦合。
                let mut seed = 0x1234_5678u64;
                for _ in 0..64 {
                    let mut p = Bool(true);
                    for (index, domain) in sampled.iter().enumerate() {
                        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
                        p = And(Box::new(p), Box::new(condition(index, domain[(seed >> 32) as usize % domain.len()])));
                    }
                    joint_checks += 1;
                    joint_unsat += usize::from(!satisfiable(solver, &p)?);
                }
            }
            if let Some(values) = &missing_guard_tuple {
                let condition = self.predicates.iter().take(self.guards).zip(values).fold(Bool(true), |p, (e, v)| {
                    And(Box::new(p), Box::new(if *v { e.clone() } else { Not(Box::new(e.clone())) }))
                });
                missing_tuple_unsat = Some(!satisfiable(solver, &condition)?);
                assert_eq!(missing_tuple_unsat, Some(true), "完整类集合缺失的组合必须 UNSAT");
            }
            Ok::<_, ExecError>(())
        });
        solver.rollback_transaction(tx);
        verified?;
        let witness_product = self.witness_domains.iter().try_fold(1u128, |p, d| p.checked_mul(d.len() as u128));
        let components:Vec<_>=self.groups.iter().enumerate().map(|(i,g)|json!({"guards":g.iter().filter(|n|**n<self.guards).count(),
            "slices":self.slice_counts[i],"tested_bits":g.iter().filter(|n|**n>=self.guards).count(),"guard_domain":self.guard_domains[i].len(),"observed_joint_domain":self.witness_domains[i].len(),"sampled_values":sampled[i].len()})).collect();
        eprintln!(
            "[ENUM_COMPONENTS] {}",
            json!({"record_ids":self.record_ids,"guard_records":self.guards,
            "constraint_components":self.constraint_groups.iter().map(|g|json!({"guards":g.iter().filter(|n|**n<self.guards).count(),"slices":g.iter().filter(|n|**n>=self.guards).count()})).collect::<Vec<_>>(),
            "candidate_rule":"guard_slice_dependencies_without_path_assertions","unique_slices":self.slices.len(),"components":components,
            "actual_classes":actual,"actual_paths":paths,"path_truncated":truncated,"truncated_classes":truncated_classes,
            "guard_product":product.map(|p|p.to_string()),"guard_product_equal":!truncated && product==Some(actual as u128),
            "observed_joint_product":witness_product.map(|p|p.to_string()),"slice_domains_complete":truncated_classes==0 && !truncated,
            "missing_guard_tuple":missing_guard_tuple,"missing_tuple_unsat":missing_tuple_unsat,
            "pair_checks":checks,"pair_unsat":unsat,"joint_checks":joint_checks,"joint_unsat":joint_unsat,
            "graph_ms":self.setup_time.as_millis(),"verification_ms":started.elapsed().as_millis()})
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::smt::{Config, Context};

    #[test]
    fn components_两两可行不能证明三分量独立() {
        use Formula::*;
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let x = solver.declare_const(smtlib::Ty::Bool, SourceLoc::unknown());
        let y = solver.declare_const(smtlib::Ty::Bool, SourceLoc::unknown());
        let z = solver.declare_const(smtlib::Ty::Bool, SourceLoc::unknown());
        solver.add(Def::Assert(Eq(Box::new(Var(z)), Box::new(Neq(Box::new(Var(x)), Box::new(Var(y)))))));
        let events: Vec<_> = solver.trace().to_vec().into_iter().rev().cloned().collect();
        let mut diagnostic = Diagnostic {
            guards: 3,
            slices: Vec::new(),
            predicates: vec![Var(x), Var(y), Var(z)],
            groups: vec![vec![0], vec![1], vec![2]],
            constraint_groups: vec![vec![0, 1, 2]],
            slice_counts: vec![0; 3],
            guard_domains: vec![Default::default(); 3],
            guard_assignments: HashSet::new(),
            witness_domains: vec![Default::default(); 3],
            record_ids: vec![0, 1, 2],
            setup_time: Default::default(),
        };
        for (x, y) in [(false, false), (false, true), (true, false), (true, true)] {
            diagnostic.observe(&[x, y, x != y], "");
        }
        // 候选乘积 8 > 实际 4；finish 必须找到原约束拒绝的具体组合。
        diagnostic.finish(&events, 4, 4, false, 0).unwrap();
    }

    #[test]
    fn components_共享整字的不同位可分离且隐藏约束传递耦合() {
        use Formula::*;
        let x = Sym { id: 0 };
        let h = Sym { id: 1 };
        let a = Extract(0, 0, Box::new(Var(x)));
        let b = Extract(1, 1, Box::new(Var(x)));
        let types = HashMap::from([(x, smtlib::Ty::BitVec(2)), (h, smtlib::Ty::BitVec(1))]);
        let mut support = Support::new(HashMap::new(), types);
        assert_eq!(partition(&[a.clone(), b.clone()], &[], &mut support), vec![vec![0], vec![1]]);
        let constraints = vec![Eq(Box::new(a.clone()), Box::new(Var(h))), Eq(Box::new(Var(h)), Box::new(b.clone()))];
        assert_eq!(partition(&[a, b], &constraints, &mut support), vec![vec![0, 1]]);
    }

    #[test]
    fn components_派生ite保留条件依赖且求解器拒绝伪独立组合() {
        use Formula::*;
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let x = solver.declare_const(smtlib::Ty::Bool, SourceLoc::unknown());
        let y = solver.declare_const(smtlib::Ty::Bool, SourceLoc::unknown());
        solver.add(Def::Assert(Eq(Box::new(Var(x)), Box::new(Var(y)))));
        assert!(satisfiable(&mut solver, &Var(x)).unwrap());
        assert!(satisfiable(&mut solver, &Not(Box::new(Var(y)))).unwrap());
        assert!(!satisfiable(&mut solver, &And(Box::new(Var(x)), Box::new(Not(Box::new(Var(y)))))).unwrap());
        let d = Sym { id: 100 };
        let mut support = Support::new(
            HashMap::from([(d, Ite(Box::new(Var(x)), Box::new(Var(y)), Box::new(Bool(false))))]),
            HashMap::new(),
        );
        assert_eq!(partition(&[Var(d), Var(x)], &[], &mut support), vec![vec![0, 1]]);
    }
}
