//! 目标类固定归属一个队列；同类请求按编号串行，不同类可以并行。
use super::{ablation::input_domain::InputDomain, mutator::SolverMutator, Executor, Mutator};
use crate::isarch::{resident::ResidentPath, target::Target};
use isla_lib::{
    bitvector::BV,
    error::{ExecError, SmtError},
    executor::samples::{mutation::PathMutator, Sample},
    ir::SharedState,
    smt::{smtlib::Exp, Config, Context, Model, SmtResult, Solver, Sym},
    source_loc::SourceLoc,
};
use rand_chacha::ChaCha8Rng;
use serde_json::{json, Value};
use std::collections::BTreeMap;

pub(super) struct Job {
    pub target_index: usize,
    pub parent: Sample,
    pub record: Value,
    pub rng: ChaCha8Rng,
}
pub(super) fn owner(target: usize, threads: usize) -> usize {
    target % threads
}
pub(super) struct GenerationPool {
    inputs: Vec<crossbeam::channel::Sender<Job>>,
    output: crossbeam::channel::Receiver<(u64, Option<Sample>, Value)>,
    pending: usize,
}
impl Executor for GenerationPool {
    type Input = Job;
    type Output = (u64, Option<Sample>, Value);
    fn submit(&mut self, batch: Vec<Job>) {
        assert_eq!(self.pending, 0, "上一批生成尚未完成");
        self.pending = batch.len();
        for job in batch {
            self.inputs[owner(job.target_index, self.inputs.len())].send(job).expect("生成线程退出");
        }
    }
    fn drain(&mut self) -> Vec<Self::Output> {
        let mut result = (0..self.pending).map(|_| self.output.recv().expect("生成线程退出")).collect::<Vec<_>>();
        result.sort_by_key(|(id, _, _)| *id);
        self.pending = 0;
        result
    }
}
impl GenerationPool {
    pub(super) fn with<B: BV, R>(
        paths: &[ResidentPath<B>],
        shared: &SharedState<B>,
        target: &dyn Target<B>,
        threads: usize,
        mutation_config: &super::MutationConfig,
        run: impl FnOnce(&mut Self) -> R,
    ) -> R {
        Self::with_domain(paths, shared, target, threads, mutation_config, None, run)
    }
    pub(super) fn with_domain<B: BV, R>(
        paths: &[ResidentPath<B>],
        shared: &SharedState<B>,
        target: &dyn Target<B>,
        threads: usize,
        mutation_config: &super::MutationConfig,
        domain: Option<&InputDomain>,
        run: impl FnOnce(&mut Self) -> R,
    ) -> R {
        assert!(threads > 0);
        std::thread::scope(|scope| {
            let (output_tx, output) = crossbeam::channel::unbounded();
            let mut inputs = Vec::new();
            for _ in 0..threads {
                let (input_tx, input_rx) = crossbeam::channel::bounded::<Job>(2);
                inputs.push(input_tx);
                let output_tx = output_tx.clone();
                scope.spawn(move || {
                    let mut config = Config::new();
                    config.set_param_value("model", "true");
                    let context = Context::new(config);
                    let mut mutators = BTreeMap::new();
                    for mut job in input_rx {
                        let signature = job.parent.path_signature;
                        let mutator = mutators.entry(signature).or_insert_with(|| {
                            let path = paths.iter().find(|p| p.signature == signature).unwrap();
                            SolverMutator::new(path, &context, shared, target, mutation_config).with_input_domain(
                                InputDomain::compile_optional(domain, &path.path, shared).expect("硬件输入域配置无效"),
                            )
                        });
                        let sample = mutator.try_mutate(&job.parent, &job.record, &mut job.rng);
                        job.record["changes"] = json!(*mutator.changes.borrow());
                        if let Some(selected) = &*mutator.selected.borrow() {
                            job.record["mutation_fields"] = json!(selected);
                            if sample.is_none() {
                                job.record["generation_status"] = json!("mutation_subset_unsatisfiable_or_seen");
                            }
                        }
                        output_tx.send((job.record["sample_id"].as_u64().unwrap(), sample, job.record)).unwrap();
                    }
                });
            }
            drop(output_tx);
            let mut pool = Self { inputs, output, pending: 0 };
            run(&mut pool)
        })
    }
}

pub(super) enum Replacement {
    Found(Sample),
    EmptyInDomain,
    BudgetExhausted,
}

pub(super) fn replace_witness<B: BV>(
    path: &ResidentPath<B>,
    shared: &SharedState<B>,
    target: &dyn Target<B>,
    original: &Sample,
    class: Exp<Sym>,
    domain: Exp<Sym>,
    attempts: usize,
    timeout_ms: u32,
    mut random: impl FnMut() -> u64,
    constructible: impl Fn(&Sample) -> bool,
) -> Result<Replacement, ExecError> {
    let mut config = Config::new();
    config.set_param_value("timeout", &timeout_ms.to_string());
    let context = Context::new(config);
    let solve = || {
        let mut solver = Solver::from_checkpoint(&context, path.checkpoint.clone());
        // 枚举器已给出完整的活动守卫条件。先锁定此类，再复用整输入排重取点。
        solver.assert(class);
        // 证明空交集时不排除原代表或已拒绝的具体输入。
        match solver.check_sat_with(&domain, SourceLoc::unknown()) {
            SmtResult::Unsat => return Ok(Replacement::EmptyInDomain),
            SmtResult::Sat => (),
            SmtResult::Unknown => return Ok(Replacement::BudgetExhausted),
            SmtResult::Error(error) => return Err(ExecError::Smt(error)),
        }
        let mut mutator = PathMutator::new(&path.path, &mut solver, &[]).with_input_domain(domain);
        for _ in 0..attempts {
            let Some(mutation) = mutator.generate(&path.path, &mut solver, shared, original, "", false, &mut random)?
            else {
                break;
            };
            let mut sample = mutation.sample;
            sample.class_id = original.class_id;
            sample.isa_state = crate::isarch::samples::isa_state(target, &sample, &mut Model::new(&solver), shared)?;
            if constructible(&sample) {
                sample.truncated = original.truncated;
                return Ok(Replacement::Found(sample));
            }
        }
        Ok(Replacement::BudgetExhausted)
    };
    match solve() {
        Err(ExecError::Z3Unknown | ExecError::Smt(SmtError::Timeout(_))) => Ok(Replacement::BudgetExhausted),
        result => result,
    }
}

#[cfg(test)]
pub(super) fn test_executor_order() {
    let (input_tx, input_rx) = crossbeam::channel::bounded(2);
    let (output_tx, output) = crossbeam::channel::unbounded();
    let mut pool = GenerationPool { inputs: vec![input_tx], output, pending: 0 };
    let sample = super::tests::example_sample();
    pool.submit(vec![Job {
        target_index: 0,
        parent: sample.clone(),
        record: json!({}),
        rng: super::random_stream(0, "测试", 0),
    }]);
    assert!(input_rx.recv().is_ok());
    output_tx.send((3, Some(sample.clone()), json!({}))).unwrap();
    assert_eq!(pool.drain()[0].0, 3);
    pool.pending = 2;
    output_tx.send((9, Some(sample.clone()), json!({}))).unwrap();
    output_tx.send((1, None, json!({}))).unwrap();
    let drained = pool.drain();
    assert_eq!(drained.iter().map(|r| r.0).collect::<Vec<_>>(), vec![1, 9]);
    assert!(drained[0].1.is_none(), "耗尽结果必须传回 campaign");
    assert_eq!(pool.pending, 0);
}
