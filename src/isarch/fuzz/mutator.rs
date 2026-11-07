//! 求解器变异器持有常驻求解器；trait 的不可变接收者通过局部可变状态复用事务。
use super::{corpus::ClassIdentity, Mutator};
use crate::isarch::{resident::ResidentPath, target::Target};
use isla_lib::{
    bitvector::BV,
    executor::samples::{mutation::PathMutator, Sample},
    ir::SharedState,
    smt::{Context, Model, Solver},
};
use rand::RngCore;
use rand_chacha::ChaCha8Rng;
use serde_json::Value;
use std::cell::RefCell;

pub struct SolverMutator<'a, 'ctx, 'ir, B: BV> {
    pub path: &'a ResidentPath<B>,
    shared: &'a SharedState<'ir, B>,
    target: &'a dyn Target<B>,
    solver: RefCell<Solver<'ctx, B>>,
    mutator: RefCell<PathMutator<B>>,
    pub changes: RefCell<Vec<Value>>,
}
impl<'a, 'ctx, 'ir, B: BV> SolverMutator<'a, 'ctx, 'ir, B> {
    pub fn new(
        path: &'a ResidentPath<B>,
        context: &'ctx Context,
        shared: &'a SharedState<'ir, B>,
        target: &'a dyn Target<B>,
    ) -> Self {
        let solver = Solver::from_checkpoint(context, path.checkpoint.clone());
        let mutator = PathMutator::new(&path.path, &solver, &path.records);
        Self {
            path,
            shared,
            target,
            solver: RefCell::new(solver),
            mutator: RefCell::new(mutator),
            changes: RefCell::new(Vec::new()),
        }
    }
}
impl<B: BV> Mutator for SolverMutator<'_, '_, '_, B> {
    fn mutate(&self, parent: &Sample, record: &Value, rng: &mut ChaCha8Rng) -> Sample {
        self.try_mutate(parent, record, rng).expect("目标类当前可变字段的取值已耗尽")
    }
    fn try_mutate(&self, parent: &Sample, record: &Value, rng: &mut ChaCha8Rng) -> Option<Sample> {
        let identity: ClassIdentity = serde_json::from_value(record["target_identity"].clone()).unwrap();
        assert_eq!(identity.path_signature, self.path.signature);
        let mut solver = self.solver.borrow_mut();
        let changed = self
            .mutator
            .borrow_mut()
            .generate(
                &self.path.path,
                &mut solver,
                self.shared,
                parent,
                &identity.guard_vector,
                record["operator"] == "B",
                &mut || rng.next_u64(),
            )
            .expect("求解器变异失败");
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
