//! 保留每类输入历史；每个请求用独立 Context 求解，保证随机流可复现。
use super::{corpus::ClassIdentity, Mutator};
use crate::isarch::{resident::ResidentPath, target::Target};
use isla_lib::{
    bitvector::BV,
    executor::samples::{mutation::PathMutator, Sample},
    ir::SharedState,
    smt::{smtlib::Exp, Config, Context, Model, Solver, Sym},
};
use rand::RngCore;
use rand_chacha::ChaCha8Rng;
use serde_json::Value;
use std::cell::RefCell;

pub struct SolverMutator<'a, 'ir, B: BV> {
    pub path: &'a ResidentPath<B>,
    shared: &'a SharedState<'ir, B>,
    target: &'a dyn Target<B>,
    mutator: RefCell<PathMutator<B>>,
    pub changes: RefCell<Vec<Value>>,
    config: super::MutationConfig,
    pub selected: RefCell<Option<Vec<String>>>,
}
impl<'a, 'ir, B: BV> SolverMutator<'a, 'ir, B> {
    pub fn new(
        path: &'a ResidentPath<B>,
        context: &Context,
        shared: &'a SharedState<'ir, B>,
        target: &'a dyn Target<B>,
        config: &super::MutationConfig,
    ) -> Self {
        let mut solver = Solver::from_checkpoint(context, path.checkpoint.clone());
        let mutator = PathMutator::new(&path.path, &mut solver, &path.records);
        Self {
            path,
            shared,
            target,
            mutator: RefCell::new(mutator),
            changes: RefCell::new(Vec::new()),
            config: config.clone(),
            selected: RefCell::new(None),
        }
    }
}
impl<B: BV> SolverMutator<'_, '_, B> {
    pub fn with_input_domain(mut self, domain: Exp<Sym>) -> Self {
        self.mutator = RefCell::new(self.mutator.into_inner().with_input_domain(domain));
        self
    }
}
impl<B: BV> Mutator for SolverMutator<'_, '_, B> {
    fn mutate(&self, parent: &Sample, record: &Value, rng: &mut ChaCha8Rng) -> Sample {
        self.try_mutate(parent, record, rng).expect("目标类的完整输入已耗尽")
    }
    fn try_mutate(&self, parent: &Sample, record: &Value, rng: &mut ChaCha8Rng) -> Option<Sample> {
        self.changes.borrow_mut().clear();
        let identity: ClassIdentity = serde_json::from_value(record["target_identity"].clone()).unwrap();
        assert_eq!(identity.path_signature, self.path.signature);
        let context = Context::new(Config::new());
        let mut solver = Solver::new_for_samples(&context, None);
        let mut mutator = self.mutator.borrow_mut();
        let selected = if self.config.is_legacy() || record["operator"] == "B" {
            None
        } else {
            Some(self.config.select(mutator.field_names(), &mut || rng.next_u64()))
        };
        *self.selected.borrow_mut() = selected.as_ref().map(|fields| fields.iter().cloned().collect());
        let changed = if let Some(fields) = &selected {
            mutator.generate_with_fields(
                &self.path.path,
                &mut solver,
                self.shared,
                parent,
                &identity.guard_vector,
                record["operator"] == "B",
                fields,
                &mut || rng.next_u64(),
            )
        } else {
            mutator.generate(
                &self.path.path,
                &mut solver,
                self.shared,
                parent,
                &identity.guard_vector,
                record["operator"] == "B",
                &mut || rng.next_u64(),
            )
        }
        .expect("求解器变异失败");
        drop(mutator);
        if std::env::var_os("ISLA_MUTATION_PROFILE").is_some() {
            eprintln!("[FUZZ_SOLVER_PROFILE] {}", serde_json::to_string(&self.mutator.borrow().profile).unwrap());
        }
        changed.map(|changed| {
            *self.changes.borrow_mut() = changed.changes;
            let mut sample = changed.sample;
            sample.isa_state =
                crate::isarch::samples::isa_state(self.target, &sample, &mut Model::new(&solver), self.shared)
                    .expect("变异前态展示失败");
            sample.sample_id = record["sample_id"].as_u64().unwrap();
            sample.path_signature = 0;
            sample.class_id = None;
            sample.post_registers.clear();
            sample.post_memory.clear();
            sample.result = Value::Null;
            sample.ret_val.clear();
            sample
        })
    }
}
