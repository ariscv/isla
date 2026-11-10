//! 按真实 Arc 节点去重，保留空段及检查点计数。
use super::event::Event;
use crate::bitvector::BV;
use crate::smt::{Checkpoint, Trace};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Segment<B> {
    pub id: u64,
    pub parent: Option<u64>,
    pub checkpoints: u64,
    pub events: Vec<Event<B>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckpointData {
    pub num: u64,
    pub next_var: u32,
    pub leaf: Option<u64>,
}

pub struct TraceWriter<B> {
    pub segments: Vec<Segment<B>>,
    nodes: HashMap<usize, u64>,
    // 持有原节点，防止导出器存活期间地址被分配给另一个 Arc。
    keepalive: Vec<Arc<Option<Trace<B>>>>,
}
impl<B> Default for TraceWriter<B> {
    fn default() -> Self {
        Self { segments: Vec::new(), nodes: HashMap::new(), keepalive: Vec::new() }
    }
}
impl<B: BV> TraceWriter<B> {
    pub fn capture(&mut self, checkpoint: &Checkpoint<B>) -> CheckpointData {
        let (num, next_var, trace) = checkpoint.path_cache_parts();
        let mut pending = Vec::new();
        let mut next = trace;
        let mut parent = loop {
            let key = Arc::as_ptr(next) as usize;
            if let Some(id) = self.nodes.get(&key) {
                break Some(*id);
            }
            match next.as_ref() {
                None => break None,
                Some(segment) => {
                    pending.push((key, segment, next.clone()));
                    next = segment.path_cache_parts().2;
                }
            }
        };
        for (key, segment, original) in pending.into_iter().rev() {
            let id = self.segments.len().try_into().unwrap();
            let (checkpoints, head, _) = segment.path_cache_parts();
            self.segments.push(Segment {
                id,
                parent,
                checkpoints: checkpoints.try_into().unwrap(),
                events: head.iter().cloned().map(Into::into).collect(),
            });
            self.keepalive.push(original);
            assert!(self.nodes.insert(key, id).is_none());
            parent = Some(id);
        }
        CheckpointData { num: num.try_into().unwrap(), next_var, leaf: parent }
    }
}

pub struct TraceReader<B> {
    nodes: Vec<Arc<Option<Trace<B>>>>,
    depths: Vec<u64>,
    empty: Arc<Option<Trace<B>>>,
}
impl<B: BV> TraceReader<B> {
    pub fn new(segments: &[Segment<B>]) -> Self {
        let mut reader = Self { nodes: Vec::new(), depths: Vec::new(), empty: Arc::new(None) };
        for (index, segment) in segments.iter().enumerate() {
            assert_eq!(segment.id, index as u64, "缓存段编号不连续");
            let (parent, depth) = match segment.parent {
                Some(id) => {
                    assert!(id < segment.id, "缓存父段不存在或父链成环：{}", segment.id);
                    (reader.nodes[id as usize].clone(), reader.depths[id as usize])
                }
                None => (reader.empty.clone(), 0),
            };
            assert_eq!(segment.checkpoints, depth, "缓存空段或检查点计数不一致");
            let events = segment.events.iter().cloned().map(Into::into).collect();
            reader.nodes.push(Arc::new(Some(Trace::from_path_cache_parts(depth.try_into().unwrap(), events, parent))));
            reader.depths.push(depth + 1);
        }
        reader
    }
    pub fn restore(&self, checkpoint: &CheckpointData) -> Checkpoint<B> {
        let (trace, num) = match checkpoint.leaf {
            Some(id) => {
                let index = usize::try_from(id).expect("缓存叶段编号越界");
                (self.nodes.get(index).expect("缓存叶段不存在").clone(), self.depths[index])
            }
            None => (self.empty.clone(), 0),
        };
        assert_eq!(num, checkpoint.num, "缓存检查点段数不一致");
        Checkpoint::from_path_cache_parts(num.try_into().unwrap(), checkpoint.next_var, trace)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        bitvector::b64::B64,
        smt::{self, Config, Context, Event, Solver},
    };
    #[test]
    fn 按地址去重期间必须持有原节点() {
        smt::configure_tastic(smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        solver.add_event(Event::Cycle);
        let checkpoint = smt::checkpoint(&mut solver);
        let trace = checkpoint.path_cache_parts().2;
        let count = Arc::strong_count(trace);
        let mut writer = TraceWriter::default();
        writer.capture(&checkpoint);
        assert!(Arc::strong_count(trace) > count, "按地址去重必须阻止节点释放后复用地址");
    }
}
