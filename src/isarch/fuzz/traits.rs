//! 闭环接口；候选特征由调用方定义，调度只在整批完成后提交。
use isla_lib::executor::samples::Sample;
use rand_chacha::ChaCha8Rng;
use serde_json::Value;

pub trait Scheduler {
    fn next_batch(&self, limit: usize) -> Vec<usize>;
    fn on_batch_end(&mut self, completed: usize);
}

pub trait Mutator {
    fn mutate(&self, parent: &Sample, record: &Value, rng: &mut ChaCha8Rng) -> Sample;
}

/// submit 接受整批任务，drain 按编号返回全部结果；后续可接异步 worker 队列。
pub trait Executor {
    type Input;
    type Output;
    fn submit(&mut self, batch: Vec<Self::Input>);
    fn drain(&mut self) -> Vec<Self::Output>;
}

pub trait Oracle {
    fn compare(&self, expected: &Value, observed: &Value) -> Option<Value>;
}

pub trait Feedback {
    type Feature;
    fn observe(&mut self, sample_id: u64, feature: &Self::Feature);
    fn is_novel(&self, feature: &Self::Feature) -> bool {
        let _ = feature;
        false
    }
    fn score(&self, feature: &Self::Feature) -> f64 {
        let _ = feature;
        1.0
    }
    fn on_corpus_add(&mut self, sample_id: u64) {
        let _ = sample_id;
    }
    fn on_mismatch(&mut self, sample_id: u64, mismatch: &Value) {
        let _ = (sample_id, mismatch);
    }
}

pub struct ReplayScheduler {
    position: usize,
    total: usize,
}
impl ReplayScheduler {
    pub fn new(total: usize) -> Self {
        Self { position: 0, total }
    }
}
impl Scheduler for ReplayScheduler {
    fn next_batch(&self, limit: usize) -> Vec<usize> {
        assert!(limit > 0, "批量大小必须大于零");
        (self.position..self.total.min(self.position + limit)).collect()
    }
    fn on_batch_end(&mut self, completed: usize) {
        self.position += completed;
        assert!(self.position <= self.total, "调度超出输入范围");
    }
}

pub struct NoHardwareOracle;
impl Oracle for NoHardwareOracle {
    fn compare(&self, expected: &Value, observed: &Value) -> Option<Value> {
        let _ = (expected, observed);
        None
    }
}

#[derive(Default)]
pub struct LogFeedback {
    pub rows: Vec<Value>,
}
impl Feedback for LogFeedback {
    type Feature = Value;
    fn observe(&mut self, sample_id: u64, feature: &Value) {
        self.rows.push(serde_json::json!({"sample_id":sample_id,"features":feature}));
    }
}
