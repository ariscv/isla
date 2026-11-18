//! 在目标守卫类内直接求解取点，并按完整输入排重。
use super::*;
use crate::executor::merge_record::{context, guard_order, model_guards};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::time::Instant;

#[derive(Clone, Default, serde::Serialize)]
pub struct MutationProfile {
    pub total_seconds: f64,
    pub parent_seconds: f64,
    pub query_seconds: f64,
    pub materialize_seconds: f64,
    pub queries: usize,
    pub fill_seconds: f64,
}
thread_local! {
    static QUERY_PROFILE: RefCell<MutationProfile> = RefCell::new(MutationProfile::default());
}

struct Field {
    name: String,
    expression: Exp<Sym>,
    active: Exp<Sym>,
}

struct Input {
    values: Vec<Exp<Sym>>,
    active: Vec<bool>,
}

pub struct Mutation {
    pub sample: Sample,
    pub changes: Vec<Value>,
}

pub struct PathMutator<B: BV> {
    pub profile: MutationProfile,
    fields: Vec<Field>,
    guards: Vec<Exp<Sym>>,
    input_domain: Exp<Sym>,
    checkpoint: crate::smt::Checkpoint<B>,
    // 每类记录完整输入；未活动读取的模型值不属于该输入。
    history: BTreeMap<String, Vec<Input>>,
    records: Vec<super::super::RegionMergeRecord<B>>,
    order: Vec<usize>,
}

fn conjunction(parts: impl IntoIterator<Item = Exp<Sym>>) -> Exp<Sym> {
    parts.into_iter().fold(Exp::Bool(true), |a, b| Exp::And(Box::new(a), Box::new(b)).eval())
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

impl<B: BV> PathMutator<B> {
    pub fn new(path: &SamplePath<B>, solver: &mut Solver<B>, records: &[super::super::RegionMergeRecord<B>]) -> Self {
        let checkpoint = crate::smt::checkpoint(solver);
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
        let fields = values.into_iter().map(|(name, expression, active)| Field { name, expression, active }).collect();
        Self {
            profile: MutationProfile::default(),
            fields,
            guards,
            input_domain: Exp::Bool(true),
            checkpoint,
            history: BTreeMap::new(),
            records: records.to_vec(),
            order,
        }
    }

    /// 调用方提供同一路径符号上的布尔条件；域固定后才开始记录输入历史。
    pub fn with_input_domain(mut self, condition: Exp<Sym>) -> Self {
        assert!(self.history.is_empty(), "不能在已有取点历史中改变输入域");
        self.input_domain = condition;
        self
    }

    pub fn field_names(&self) -> impl Iterator<Item = &str> {
        self.fields.iter().map(|field| field.name.as_str())
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
        QUERY_PROFILE.with(|p| *p.borrow_mut() = MutationProfile::default());
        let started = Instant::now();
        let result = self.generate_inner(path, solver, shared, parent, target, neighbor, None, random);
        self.profile = QUERY_PROFILE.with(|p| p.borrow().clone());
        self.profile.total_seconds = started.elapsed().as_secs_f64();
        result
    }

    /// 仅允许选中叶字段变化；其余活动状态及活动值保持父输入。
    /// 返回 None 只表示此子集无新输入，不代表整个守卫类耗尽。
    pub fn generate_with_fields(
        &mut self,
        path: &SamplePath<B>,
        solver: &mut Solver<B>,
        shared: &SharedState<B>,
        parent: &Sample,
        target: &str,
        neighbor: bool,
        selected: &std::collections::BTreeSet<String>,
        random: &mut impl FnMut() -> u64,
    ) -> Result<Option<Mutation>, ExecError> {
        assert!(selected.iter().all(|name| self.fields.iter().any(|f| &f.name == name)), "未知变异字段");
        QUERY_PROFILE.with(|p| *p.borrow_mut() = MutationProfile::default());
        let started = Instant::now();
        let result = self.generate_inner(path, solver, shared, parent, target, neighbor, Some(selected), random);
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
        selected: Option<&std::collections::BTreeSet<String>>,
        random: &mut impl FnMut() -> u64,
    ) -> Result<Option<Mutation>, ExecError> {
        assert_eq!(solver.transaction_depth(), 0);
        assert_eq!(target.len(), self.guards.len(), "目标守卫长度与路径不同");
        let parent_started = Instant::now();
        // 父输入只在独立求解器中认证；它的绑定不能进入目标类的求解。
        let mut parent_solver = Solver::from_checkpoint_for_samples(solver.context(), self.checkpoint.clone(), None);
        assert!(path.bind(&mut parent_solver, shared, parent)?, "父 corpus entry 必须被原路径接纳");
        let mut model = Model::new(&parent_solver);
        model.set_complete_model(true);
        let baseline = self
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
        let parent_class: String = parent_vector.iter().map(|v| if *v { '1' } else { '0' }).collect();
        assert_eq!(parent_class != target, neighbor, "A 必须保持父类，B 必须选择邻类");
        let subset_condition = selected.map(|names| {
            if names.is_empty() {
                return Exp::Bool(false);
            }
            conjunction(self.fields.iter().zip(&baseline).zip(&active).map(|((field, value), active)| {
                let equal = Exp::Eq(Box::new(field.expression.clone()), Box::new(value.clone()));
                if names.contains(&field.name) {
                    if !active {
                        return Exp::Bool(false);
                    }
                    conjunction([field.active.clone(), Exp::Not(Box::new(equal))])
                } else if *active {
                    conjunction([field.active.clone(), equal])
                } else {
                    Exp::Not(Box::new(field.active.clone()))
                }
            }))
        });
        let history = self.history.entry(parent_class).or_default();
        if !history.iter().any(|input| {
            input.active == active
                && input.values.iter().zip(&baseline).zip(&active).all(|((a, b), active)| !active || a == b)
        }) {
            history.push(Input { values: baseline.clone(), active });
        }
        drop(model);
        // 父绑定AST必须保留到取点结束；HashMap析构顺序会影响同Context的
        // AST编号复用，提前释放会使相同随机流在同一类中取到不同输入。
        QUERY_PROFILE.with(|p| p.borrow_mut().parent_seconds = parent_started.elapsed().as_secs_f64());
        // 每次重新重放原路径，避免上一点的填值断言或求解器状态影响下一点。
        *solver = Solver::from_checkpoint_for_samples(solver.context(), self.checkpoint.clone(), Some(random() as u32));
        let class = conjunction(self.guards.iter().zip(target.bytes()).map(|(g, bit)| {
            assert!(bit == b'0' || bit == b'1');
            if bit == b'1' {
                g.clone()
            } else {
                Exp::Not(Box::new(g.clone()))
            }
        }));
        let mut conditions = vec![class, self.input_domain.clone()];
        if let Some(subset_condition) = subset_condition {
            conditions.push(subset_condition);
        }
        if let Some(previous) = self.history.get(target) {
            for input in previous {
                let same = conjunction(self.fields.iter().zip(&input.values).zip(&input.active).map(
                    |((field, value), active)| {
                        if *active {
                            conjunction([
                                field.active.clone(),
                                Exp::Eq(Box::new(field.expression.clone()), Box::new(value.clone())),
                            ])
                        } else {
                            Exp::Not(Box::new(field.active.clone()))
                        }
                    },
                ));
                conditions.push(Exp::Not(Box::new(same)));
            }
        }
        let condition = conjunction(conditions);
        if !query(solver, &condition)? {
            return Ok(None);
        }
        let fill_started = Instant::now();
        fill_arbitrary_inputs(solver, &condition, random)?;
        QUERY_PROFILE.with(|p| {
            let mut p = p.borrow_mut();
            p.queries += 1; // 填值后的一次最终可满足性检查。
            p.fill_seconds = fill_started.elapsed().as_secs_f64();
        });
        let materialize_started = Instant::now();
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
        let mut changes = Vec::new();
        for (i, field) in self.fields.iter().enumerate() {
            if active[i] && values[i] != baseline[i] {
                changes.push(
                    json!({"field":field.name,"before":format!("{:?}",baseline[i]),"after":format!("{:?}",values[i])}),
                );
            }
        }
        let sample = path.materialize(&mut model, shared, "merge", parent.path_signature, None)?;
        self.history.entry(target.into()).or_default().push(Input { values, active });
        QUERY_PROFILE.with(|p| p.borrow_mut().materialize_seconds = materialize_started.elapsed().as_secs_f64());
        Ok(Some(Mutation { sample, changes }))
    }
}
