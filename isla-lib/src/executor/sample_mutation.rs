//! 在规范守卫约束下生成输入；复用样本绑定、具体化及枚举器的按位依赖。
use super::*;
use crate::executor::merge_record::{context, guard_order, model_guards, Atoms, Support};
use crate::smt::smtlib::{bits64, Def, Ty};
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::time::Instant;

#[derive(Clone, Default, serde::Serialize)]
pub struct MutationProfile {
    pub total_seconds: f64,
    pub parent_seconds: f64,
    pub query_seconds: f64,
    pub materialize_seconds: f64,
    pub queries: usize,
    pub bucket_rejections: usize,
    pub fixed_buckets: usize,
}
thread_local! {
    static QUERY_PROFILE: RefCell<MutationProfile> = RefCell::new(MutationProfile::default());
}

#[path = "sample_mutation_ppn.rs"]
mod ppn;

struct Field {
    name: String,
    expression: Exp<Sym>,
    active: Exp<Sym>,
    width: Option<u32>,
    atoms: Vec<Atoms>,
    mutable: bool,
}

pub struct Mutation {
    pub sample: Sample,
    pub changes: Vec<Value>,
}

pub struct PathMutator<B: BV> {
    pub profile: MutationProfile,
    pub avoid_known_ppn_overflow: bool,
    pub ppn_overflow_retained_for_class: bool,
    fields: Vec<Field>,
    guards: Vec<Exp<Sym>>,
    guard_atoms: Vec<Atoms>,
    constraints: Vec<Atoms>,
    // 每类保留所有输入字段的具体取值，用于整解阻断及字段排重。
    history: BTreeMap<String, Vec<Vec<Exp<Sym>>>>,
    records: Vec<super::super::RegionMergeRecord<B>>,
    order: Vec<usize>,
}

fn conjunction(parts: impl IntoIterator<Item = Exp<Sym>>) -> Exp<Sym> {
    parts.into_iter().fold(Exp::Bool(true), |a, b| Exp::And(Box::new(a), Box::new(b)).eval())
}

fn different(a: Exp<Sym>, b: Exp<Sym>) -> Exp<Sym> {
    Exp::Neq(Box::new(a), Box::new(b))
}

fn query<B: BV>(solver: &mut Solver<B>, condition: &Exp<Sym>) -> Result<bool, ExecError> {
    let started = Instant::now();
    let result = solver.check_sat_with(condition, SourceLoc::unknown());
    QUERY_PROFILE.with(|p| {
        let mut p = p.borrow_mut();
        p.queries += 1;
        p.query_seconds += started.elapsed().as_secs_f64();
    });
    match result {
        SmtResult::Sat => Ok(true),
        SmtResult::Unsat => Ok(false),
        SmtResult::Unknown => Err(ExecError::Z3Unknown),
        SmtResult::Error(error) => Err(ExecError::Smt(error)),
    }
}

fn bits(exp: &Exp<Sym>) -> Vec<bool> {
    match exp {
        Exp::Bits64(value) => value.to_vec(),
        Exp::Bits(value) => value.clone(),
        _ => panic!("变异字段必须为位向量"),
    }
}

impl<B: BV> PathMutator<B> {
    pub fn new(path: &SamplePath<B>, solver: &Solver<B>, records: &[super::super::RegionMergeRecord<B>]) -> Self {
        let mut definitions = HashMap::new();
        let mut types = HashMap::new();
        let mut assertions = Vec::new();
        for event in solver.trace().to_vec().into_iter().rev() {
            if let Event::Smt(def, ..) = event {
                match def {
                    Def::DeclareConst(s, ty) => {
                        types.insert(*s, ty.clone());
                    }
                    Def::DefineConst(s, exp) => {
                        definitions.insert(*s, exp.clone());
                    }
                    Def::Assert(exp) => assertions.push(exp.clone()),
                    _ => (),
                }
            }
        }
        let mut support = Support::new(definitions, types);
        let by_id = records.iter().map(|r| (r.record_id, r)).collect();
        let mut contexts = HashMap::new();
        let mut visiting = HashSet::new();
        let order = guard_order(records);
        let guards = order
            .iter()
            .copied()
            .map(|i| {
                let record = &records[i];
                conjunction([context(record, &by_id, &mut visiting, &mut contexts), Exp::Var(record.condition)])
            })
            .collect::<Vec<_>>();
        let guard_atoms = guards.iter().map(|g| support.collect(g, None)).collect::<Vec<_>>();
        let mut relevant = guard_atoms.iter().flatten().copied().collect::<Atoms>();
        // 同值传递的寄存器不构成被测行为；不靠改写未使用的寄存器制造多样性。
        let outputs = std::iter::once(&path.result)
            .chain(path.post.iter().filter_map(|(name, value)| (path.pre.get(name) != Some(value)).then_some(value)));
        for value in outputs {
            for symbol in value.symbolic_variables() {
                relevant.extend(support.collect(&Exp::Var(symbol), None));
            }
        }
        for event in &path.memory {
            let values = match event {
                Event::ReadMem { address, .. } => vec![address],
                Event::WriteMem { address, data, .. } => vec![address, data],
                _ => panic!("变异路径只允许访存事件"),
            };
            for value in values {
                for symbol in value.symbolic_variables() {
                    relevant.extend(support.collect(&Exp::Var(symbol), None));
                }
            }
        }
        let constraints = assertions.iter().map(|e| support.collect(e, None)).filter(|s| !s.is_empty()).collect();
        let mut values = Vec::new();
        fn leaves<B: BV>(
            name: String,
            value: &Val<B>,
            out: &mut Vec<(String, Exp<Sym>, Exp<Sym>)>,
            shared_name: impl Fn(crate::ir::Name) -> String + Copy,
        ) {
            match value {
                Val::Struct(fields) => {
                    let mut fields = fields.iter().collect::<Vec<_>>();
                    fields.sort_by_key(|(n, _)| **n);
                    for (field, value) in fields {
                        leaves(format!("{name}.{}", shared_name(*field)), value, out, shared_name);
                    }
                }
                Val::Ctor(n, value) => leaves(format!("{name}.{}", shared_name(*n)), value, out, shared_name),
                Val::Vector(values) | Val::List(values) => {
                    for (i, value) in values.iter().enumerate() {
                        leaves(format!("{name}[{i}]"), value, out, shared_name);
                    }
                }
                _ if !value.symbolic_variables().is_empty() => out.push((
                    name,
                    smt_value(value, SourceLoc::unknown()).expect("变异前态必须支持 SMT 等式"),
                    Exp::Bool(true),
                )),
                _ => (),
            }
        }
        // 结构字段使用 IR 名字编号；路径内稳定，JSON 同时保留完整寄存器字段。
        for (name, value) in &path.pre {
            leaves(format!("pre.{name}"), value, &mut values, |n| n.to_string());
        }
        for (i, event) in path.memory.iter().enumerate() {
            if let Event::ReadMem { value, .. } = event {
                if !value.symbolic_variables().is_empty() {
                    values.push((
                        format!("read.{i}"),
                        smt_value(value, SourceLoc::unknown()).unwrap(),
                        path.memory_guards.get(&i).cloned().unwrap_or(Exp::Bool(true)),
                    ));
                }
            }
        }
        let type_context = solver_type_context(solver);
        let fields = values
            .into_iter()
            .map(|(name, expression, active)| {
                let width = match expression.infer(&type_context, &HashMap::new()) {
                    Some(Ty::BitVec(w)) => Some(w),
                    _ => None,
                };
                let atoms: Vec<_> = match width {
                    Some(w) => (0..w).map(|bit| support.collect(&expression, Some((bit, bit)))).collect(),
                    None => vec![support.collect(&expression, None)],
                };
                let mutable = name.starts_with("read.") || atoms.iter().any(|a| !a.is_disjoint(&relevant));
                Field { name, expression, active, width, atoms, mutable }
            })
            .collect();
        Self {
            profile: MutationProfile::default(),
            avoid_known_ppn_overflow: false,
            ppn_overflow_retained_for_class: false,
            fields,
            guards,
            guard_atoms,
            constraints,
            history: BTreeMap::new(),
            records: records.to_vec(),
            order,
        }
    }

    pub fn generate(
        &mut self,
        path: &SamplePath<B>,
        solver: &mut Solver<B>,
        shared: &SharedState<B>,
        parent: &Sample,
        target: &str,
        neighbor: bool,
        random: &mut impl FnMut() -> u64,
    ) -> Result<Option<Mutation>, ExecError> {
        self.ppn_overflow_retained_for_class = false;
        QUERY_PROFILE.with(|p| *p.borrow_mut() = MutationProfile::default());
        let started = Instant::now();
        let result = self.generate_inner(path, solver, shared, parent, target, neighbor, random);
        self.profile = QUERY_PROFILE.with(|p| p.borrow().clone());
        self.profile.total_seconds = started.elapsed().as_secs_f64();
        result
    }

    fn generate_inner(
        &mut self,
        path: &SamplePath<B>,
        solver: &mut Solver<B>,
        shared: &SharedState<B>,
        parent: &Sample,
        target: &str,
        neighbor: bool,
        random: &mut impl FnMut() -> u64,
    ) -> Result<Option<Mutation>, ExecError> {
        assert_eq!(solver.transaction_depth(), 0);
        assert_eq!(target.len(), self.guards.len(), "目标守卫长度与路径不同");
        let parent_started = Instant::now();
        let tx = solver.start_transaction_with_guard(Some(Exp::Bool(true)));
        let baseline = (|| {
            assert!(path.bind(solver, shared, parent)?, "父 corpus entry 必须被原路径接纳");
            let mut model = Model::new(solver);
            model.set_complete_model(true);
            let values = self
                .fields
                .iter()
                .map(|f| model.get_exp(&f.expression).map(|v| v.unwrap_exp()))
                .collect::<Result<Vec<_>, _>>()?;
            let active = self
                .fields
                .iter()
                .map(|f| model.get_exp(&f.active).map(|v| matches!(v.unwrap_exp(), Exp::Bool(true))))
                .collect::<Result<Vec<_>, _>>()?;
            let parent_vector = model_guards(&mut model, &self.records, &self.order)?.values;
            Ok::<_, ExecError>((values, active, parent_vector))
        })();
        solver.rollback_transaction(tx);
        let (baseline, active, parent_vector) = baseline?;
        QUERY_PROFILE.with(|p| p.borrow_mut().parent_seconds = parent_started.elapsed().as_secs_f64());
        let class = conjunction(self.guards.iter().zip(target.bytes()).map(|(g, bit)| {
            assert!(bit == b'0' || bit == b'1');
            if bit == b'1' {
                g.clone()
            } else {
                Exp::Not(Box::new(g.clone()))
            }
        }));
        let previous = self.history.get(target).cloned().unwrap_or_default();
        let mut common = vec![class.clone()];
        let mut ppn_preferences = Vec::new();
        if self.avoid_known_ppn_overflow {
            ppn_preferences = self.leaf_ppn_preferences();
            let preferred =
                conjunction(std::iter::once(class.clone()).chain(ppn_preferences.iter().map(|(_, _, p)| p.clone())));
            if query(solver, &preferred)? {
                common.push(preferred);
            } else {
                // 只用目标类判定，不把父值绑定或排重导致的失败记成类要求。
                assert!(query(solver, &class)?, "目标类必须可满足");
                self.ppn_overflow_retained_for_class = true;
                ppn_preferences.clear();
            }
        }
        // 整解排重只计活动字段；未活动读取不是输入。
        for solution in &previous {
            let same = conjunction(self.fields.iter().zip(solution).filter(|(f, _)| f.mutable).map(|(f, value)| {
                Exp::Or(
                    Box::new(Exp::Not(Box::new(f.active.clone()))),
                    Box::new(Exp::Eq(Box::new(f.expression.clone()), Box::new(value.clone()))),
                )
            }));
            common.push(Exp::Not(Box::new(same)));
        }
        let mut candidates = Vec::new();
        if neighbor {
            assert!(parent_vector.iter().zip(target.bytes()).any(|(a, b)| *a != (b == b'1')), "形态 B 必须改变目标类");
            let mut affected = Atoms::new();
            for (i, bit) in target.bytes().enumerate() {
                if parent_vector[i] != (bit == b'1') {
                    affected.extend(self.guard_atoms[i].iter().copied());
                }
            }
            loop {
                let before = affected.len();
                for constraint in &self.constraints {
                    if !constraint.is_disjoint(&affected) {
                        affected.extend(constraint.iter().copied());
                    }
                }
                if affected.len() == before {
                    break;
                }
            }
            let masks = self
                .fields
                .iter()
                .enumerate()
                .map(|(i, f)| {
                    f.atoms.iter().map(|atoms| !active[i] || !atoms.is_disjoint(&affected)).collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            candidates.push((None, masks));
            // 优先保住父值；若其他守卫把输入关联起来，再放开这些关联位。
            // 例如目标只翻转 x 的守卫，但保持 x == y 也要求允许 y 改变。
            let mut expanded = affected.clone();
            loop {
                let before = expanded.len();
                for constraint in self.constraints.iter().chain(&self.guard_atoms) {
                    if !constraint.is_disjoint(&expanded) {
                        expanded.extend(constraint.iter().copied());
                    }
                }
                if expanded.len() == before {
                    break;
                }
            }
            let masks = self
                .fields
                .iter()
                .enumerate()
                .map(|(i, field)| {
                    field.atoms.iter().map(|atoms| !active[i] || !atoms.is_disjoint(&expanded)).collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            if masks != candidates[0].1 {
                candidates.push((None, masks));
            }
        } else {
            assert!(parent_vector.iter().zip(target.bytes()).all(|(a, b)| *a == (b == b'1')), "形态 A 必须固定父类");
            for (i, field) in self.fields.iter().enumerate() {
                if !active[i] || !field.mutable {
                    continue;
                }
                if let Some(width) = field.width {
                    for lo in (0..width).step_by(8) {
                        let hi = (lo + 8).min(width);
                        if field.atoms[lo as usize..hi as usize].iter().all(BTreeSet::is_empty) {
                            continue;
                        }
                        let mut masks = self.fields.iter().map(|f| vec![false; f.atoms.len()]).collect::<Vec<_>>();
                        masks[i][lo as usize..hi as usize].fill(true);
                        candidates.push((Some(i), masks));
                    }
                } else if matches!(baseline[i], Exp::Enum(_)) {
                    let mut masks = self.fields.iter().map(|f| vec![false; f.atoms.len()]).collect::<Vec<_>>();
                    masks[i][0] = true;
                    candidates.push((Some(i), masks));
                }
            }
            for i in (1..candidates.len()).rev() {
                let j = (random() % (i as u64 + 1)) as usize;
                candidates.swap(i, j);
            }
        }
        for (selected, mut masks) in candidates {
            let mut conditions = common.clone();
            for (i, leaf, _) in &ppn_preferences {
                // 允许清除父输入的超宽高位；非叶仍遵守原来的父值绑定。
                for bit in 46..54 {
                    if active[*i] && !masks[*i][bit] {
                        conditions.push(Exp::Or(
                            Box::new(leaf.clone()),
                            Box::new(Exp::Eq(
                                Box::new(Exp::Extract(
                                    bit as u32,
                                    bit as u32,
                                    Box::new(self.fields[*i].expression.clone()),
                                )),
                                Box::new(bits64(bits(&baseline[*i])[bit] as u64, 1)),
                            )),
                        ));
                    }
                    masks[*i][bit] = true;
                }
            }
            if let Some(i) = selected {
                conditions.push(different(self.fields[i].expression.clone(), baseline[i].clone()));
                for solution in &previous {
                    conditions.push(different(self.fields[i].expression.clone(), solution[i].clone()));
                }
            }
            for (i, field) in self.fields.iter().enumerate() {
                if !active[i] {
                    continue;
                }
                if let Some(width) = field.width {
                    let mask = &masks[i];
                    if mask.iter().all(|v| !*v) {
                        conditions.push(Exp::Eq(Box::new(field.expression.clone()), Box::new(baseline[i].clone())));
                    } else {
                        let parent_bits = bits(&baseline[i]);
                        let fixed_mask = Exp::Bits((0..width as usize).map(|b| !mask[b]).collect());
                        let fixed_value = Exp::Bits((0..width as usize).map(|b| !mask[b] && parent_bits[b]).collect());
                        conditions.push(Exp::Eq(
                            Box::new(Exp::Bvand(Box::new(field.expression.clone()), Box::new(fixed_mask))),
                            Box::new(fixed_value),
                        ));
                    }
                } else if !masks[i][0] {
                    conditions.push(Exp::Eq(Box::new(field.expression.clone()), Box::new(baseline[i].clone())));
                }
            }
            let mut condition = Exp::Var(solver.define_const(conjunction(conditions), SourceLoc::unknown()));
            if !query(solver, &condition)? {
                continue;
            }
            // 固定全部活动输入的自由位，消除求解器模型偏好的不确定性。
            for (i, field) in self.fields.iter().enumerate() {
                if active[i] && masks[i].iter().all(|bit| !*bit) {
                    continue;
                }
                if !query(solver, &conjunction([condition.clone(), field.active.clone()]))? {
                    continue;
                }
                if let Some(width) = field.width {
                    let mut open = (0..width as usize).filter(|b| masks[i][*b] || !active[i]).collect::<Vec<_>>();
                    // 相邻位组成桶，避免把固定的高位与可变低位打散。
                    // 桶顺序和桶内极性仍由该 mutant 的独立随机流选择。
                    let mut buckets = open.chunks_mut(8).collect::<Vec<_>>();
                    for j in (1..buckets.len()).rev() {
                        let k = (random() % (j as u64 + 1)) as usize;
                        buckets.swap(j, k);
                    }
                    for bucket in buckets {
                        let preferred = random();
                        let choices = bucket
                            .iter()
                            .enumerate()
                            .map(|(offset, bit)| {
                                Exp::Eq(
                                    Box::new(Exp::Extract(
                                        *bit as u32,
                                        *bit as u32,
                                        Box::new(field.expression.clone()),
                                    )),
                                    Box::new(bits64((preferred >> offset) & 1, 1)),
                                )
                            })
                            .collect::<Vec<_>>();
                        let trial = conjunction(std::iter::once(condition.clone()).chain(choices.iter().cloned()));
                        if query(solver, &trial)? {
                            condition = Exp::Var(solver.define_const(trial, SourceLoc::unknown()));
                        } else {
                            QUERY_PROFILE.with(|p| p.borrow_mut().bucket_rejections += 1);
                            // 先证明整个桶只有一个取值；只有证明成功才复用模型值。
                            // 即使缓存模型来自更早的 Sat 查询，此处的反例查询也保证健全。
                            let concrete = {
                                let mut model = Model::new(solver);
                                model.set_complete_model(true);
                                bits(&model.get_exp(&field.expression)?.unwrap_exp())
                            };
                            let fixed = conjunction(bucket.iter().map(|bit| {
                                Exp::Eq(
                                    Box::new(Exp::Extract(
                                        *bit as u32,
                                        *bit as u32,
                                        Box::new(field.expression.clone()),
                                    )),
                                    Box::new(bits64(concrete[*bit] as u64, 1)),
                                )
                            }));
                            if !query(solver, &conjunction([condition.clone(), Exp::Not(Box::new(fixed.clone()))]))? {
                                QUERY_PROFILE.with(|p| p.borrow_mut().fixed_buckets += 1);
                                condition = Exp::Var(
                                    solver.define_const(conjunction([condition, fixed]), SourceLoc::unknown()),
                                );
                                continue;
                            }
                            for choice in choices {
                                let trial = conjunction([condition.clone(), choice.clone()]);
                                let accepted = if query(solver, &trial)? { choice } else { Exp::Not(Box::new(choice)) };
                                condition = Exp::Var(
                                    solver.define_const(conjunction([condition, accepted]), SourceLoc::unknown()),
                                );
                            }
                        }
                    }
                } else if masks[i][0] {
                    match &baseline[i] {
                        Exp::Bool(_) => {
                            let preference =
                                Exp::Eq(Box::new(field.expression.clone()), Box::new(Exp::Bool(random() & 1 != 0)));
                            let trial = conjunction([condition.clone(), preference.clone()]);
                            let accepted =
                                if query(solver, &trial)? { preference } else { Exp::Not(Box::new(preference)) };
                            condition =
                                Exp::Var(solver.define_const(conjunction([condition, accepted]), SourceLoc::unknown()));
                        }
                        Exp::Enum(member) => {
                            // 沿用规范见证的声明成员顺序，再由本 mutant 的随机流打散。
                            // 每个候选仍须满足原允许集合、目标守卫及已固定字段。
                            let mut members =
                                (0..shared.type_info.enums[&member.enum_id.to_name()].len()).collect::<Vec<_>>();
                            for j in (1..members.len()).rev() {
                                let k = (random() % (j as u64 + 1)) as usize;
                                members.swap(j, k);
                            }
                            let mut selected = None;
                            for index in members {
                                let value =
                                    Exp::Enum(crate::smt::EnumMember { enum_id: member.enum_id, member: index });
                                let trial = conjunction([
                                    condition.clone(),
                                    Exp::Eq(Box::new(field.expression.clone()), Box::new(value)),
                                ]);
                                if query(solver, &trial)? {
                                    selected = Some(trial);
                                    break;
                                }
                            }
                            condition =
                                Exp::Var(solver.define_const(
                                    selected.expect("可满足枚举必须存在允许的成员"),
                                    SourceLoc::unknown(),
                                ));
                        }
                        _ => panic!("当前变异器只支持位向量、布尔及枚举自由字段"),
                    }
                }
            }
            assert!(query(solver, &condition)?, "取值偏好不得破坏可满足性");
            let materialize_started = Instant::now();
            let mut model = Model::new(solver);
            model.set_complete_model(true);
            let values = self
                .fields
                .iter()
                .map(|f| model.get_exp(&f.expression).map(|v| v.unwrap_exp()))
                .collect::<Result<Vec<_>, _>>()?;
            let mut changes = Vec::new();
            for (i, field) in self.fields.iter().enumerate() {
                if matches!(model.get_exp(&field.active)?.unwrap_exp(), Exp::Bool(true)) && values[i] != baseline[i] {
                    changes.push(json!({"field":field.name,"before":format!("{:?}",baseline[i]),"after":format!("{:?}",values[i]),"opened_bits":masks[i].iter().enumerate().filter_map(|(b,v)|v.then_some(b)).collect::<Vec<_>>()}));
                }
            }
            let sample = path.materialize(&mut model, shared, "merge", parent.path_signature, None)?;
            self.history.entry(target.into()).or_default().push(values);
            QUERY_PROFILE.with(|p| p.borrow_mut().materialize_seconds = materialize_started.elapsed().as_secs_f64());
            return Ok(Some(Mutation { sample, changes }));
        }
        Ok(None)
    }
}

fn solver_type_context<B: BV>(solver: &Solver<B>) -> HashMap<Sym, Ty> {
    let mut types = HashMap::new();
    let mut functions = HashMap::new();
    for event in solver.trace().to_vec().into_iter().rev() {
        if let Event::Smt(def, ..) = event {
            match def {
                Def::DeclareConst(s, ty) => {
                    types.insert(*s, ty.clone());
                }
                Def::DeclareFun(s, args, ret) => {
                    functions.insert(*s, (args.clone(), ret.clone()));
                }
                Def::DefineConst(s, e) => {
                    types.insert(*s, e.infer(&types, &functions).expect("路径表达式类型必须完整"));
                }
                _ => (),
            }
        }
    }
    types
}
