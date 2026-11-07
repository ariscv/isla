//! 目标类固定归属一个队列；同类请求按编号串行，不同类可以并行。
use super::{mutator::SolverMutator, Executor, Mutator};
use crate::isarch::{resident::ResidentPath, target::Target};
use isla_lib::{
    bitvector::BV,
    executor::samples::Sample,
    ir::SharedState,
    smt::{Config, Context},
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
    output: crossbeam::channel::Receiver<(u64, Sample, Value)>,
    pending: usize,
}
impl Executor for GenerationPool {
    type Input = Job;
    type Output = (u64, Sample, Value);
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
                            SolverMutator::new(
                                paths.iter().find(|p| p.signature == signature).unwrap(),
                                &context,
                                shared,
                                target,
                            )
                        });
                        let sample = mutator
                            .try_mutate(&job.parent, &job.record, &mut job.rng)
                            .expect("预约目标类的可变空间已耗尽");
                        job.record["changes"] = json!(*mutator.changes.borrow());
                        output_tx.send((sample.sample_id, sample, job.record)).unwrap();
                    }
                });
            }
            drop(output_tx);
            let mut pool = Self { inputs, output, pending: 0 };
            run(&mut pool)
        })
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
    output_tx.send((3, sample.clone(), json!({}))).unwrap();
    assert_eq!(pool.drain()[0].0, 3);
    pool.pending = 2;
    output_tx.send((9, sample.clone(), json!({}))).unwrap();
    output_tx.send((1, sample, json!({}))).unwrap();
    assert_eq!(pool.drain().iter().map(|r| r.0).collect::<Vec<_>>(), vec![1, 9]);
    assert_eq!(pool.pending, 0);
}
