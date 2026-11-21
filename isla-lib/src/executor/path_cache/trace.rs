//! 按真实 Arc 节点去重，保留空段及检查点计数。
use super::event::Event;
use crate::bitvector::BV;
use crate::smt::{Checkpoint, Trace, TraceHead};
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

/// schema 7：第一次使用前缀时携带事件，其余段引用首次使用的段号。
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum HeadPrefix<B> {
    Define(Vec<Event<B>>),
    Reference(u64),
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct LinkedSegment<B> {
    pub id: u64,
    pub parent: Option<u64>,
    pub checkpoints: u64,
    pub event_count: u64,
    pub head_prefix: Option<HeadPrefix<B>>,
    pub events: Vec<Event<B>>,
}

impl<B> From<Segment<B>> for LinkedSegment<B> {
    fn from(segment: Segment<B>) -> Self {
        Self {
            id: segment.id,
            parent: segment.parent,
            checkpoints: segment.checkpoints,
            event_count: segment.events.len() as u64,
            head_prefix: None,
            events: segment.events,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckpointData {
    pub num: u64,
    pub next_var: u32,
    pub leaf: Option<u64>,
}

struct PlannedSegment<B> {
    source: Arc<Option<Trace<B>>>,
    parent: Option<u64>,
    depth: u64,
    event_count: u64,
    prefix_owner: Option<u64>,
}

/// 只登记段的顺序、父链和长度。源 Arc 防止登记期间节点释放并复用地址。
pub struct TracePlan<B> {
    nodes: HashMap<usize, u64>,
    prefix_owners: HashMap<usize, u64>,
    segments: Vec<PlannedSegment<B>>,
}

impl<B> Default for TracePlan<B> {
    fn default() -> Self {
        Self { nodes: HashMap::new(), prefix_owners: HashMap::new(), segments: Vec::new() }
    }
}

impl<B: BV> TracePlan<B> {
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
        for (key, segment, source) in pending.into_iter().rev() {
            let id = self.segments.len() as u64;
            let depth = segment.path_cache_parts().0 as u64;
            let (events, prefix) = segment.path_cache_head();
            let event_count = (events.len() + prefix.map_or(0, |prefix| prefix.events.len())) as u64;
            let prefix_owner =
                prefix.map(|prefix| *self.prefix_owners.entry(Arc::as_ptr(prefix) as usize).or_insert(id));
            self.segments.push(PlannedSegment { source, parent, depth, event_count, prefix_owner });
            assert!(self.nodes.insert(key, id).is_none());
            parent = Some(id);
        }
        CheckpointData { num: num as u64, next_var, leaf: parent }
    }

    pub fn segment(&self, index: usize) -> LinkedSegment<B> {
        let segment = &self.segments[index];
        let id = index as u64;
        let (events, prefix) = segment.source.as_ref().as_ref().unwrap().path_cache_head();
        let head_prefix = segment.prefix_owner.map(|owner| {
            if owner == id {
                HeadPrefix::Define(prefix.unwrap().events.iter().cloned().map(Into::into).collect())
            } else {
                HeadPrefix::Reference(owner)
            }
        });
        LinkedSegment {
            id,
            parent: segment.parent,
            checkpoints: segment.depth,
            event_count: segment.event_count,
            head_prefix,
            events: events.iter().cloned().map(Into::into).collect(),
        }
    }

    pub fn segments(&self) -> impl ExactSizeIterator<Item = LinkedSegment<B>> + '_ {
        (0..self.segments.len()).map(|index| self.segment(index))
    }
}

/// 用于旧格式的精确往返检查和小型测试。
pub struct TraceWriter<B> {
    pub segments: Vec<Segment<B>>,
    plan: TracePlan<B>,
}
impl<B> Default for TraceWriter<B> {
    fn default() -> Self {
        Self { segments: Vec::new(), plan: TracePlan::default() }
    }
}
impl<B: BV> TraceWriter<B> {
    pub fn capture(&mut self, checkpoint: &Checkpoint<B>) -> CheckpointData {
        let result = self.plan.capture(checkpoint);
        for segment in &self.plan.segments[self.segments.len()..] {
            let (_, events, _) = segment.source.as_ref().as_ref().unwrap().path_cache_parts();
            self.segments.push(Segment {
                id: self.segments.len() as u64,
                parent: segment.parent,
                checkpoints: segment.depth,
                events: events.cloned().map(Into::into).collect(),
            });
        }
        result
    }
}

pub struct TraceReader<B> {
    nodes: Vec<Arc<Option<Trace<B>>>>,
    depths: Vec<u64>,
    empty: Arc<Option<Trace<B>>>,
}
impl<B: BV> TraceReader<B> {
    pub fn new(segments: &[Segment<B>]) -> Self {
        let mut reader = Self::empty();
        for segment in segments {
            reader.push(segment.id, segment.parent, segment.checkpoints, &segment.events, None);
        }
        reader
    }

    /// 使用已完成结构校验的段重建检查点，运行态继续共享同一份头部事件。
    pub fn from_linked(segments: &[LinkedSegment<B>]) -> Self {
        let mut reader = Self::empty();
        let mut prefixes = HashMap::<u64, Arc<TraceHead<B>>>::new();
        for segment in segments {
            let prefix = match &segment.head_prefix {
                Some(HeadPrefix::Define(events)) => {
                    let prefix = Trace::path_cache_prefix(events.iter().cloned().map(Into::into).collect());
                    assert!(prefixes.insert(segment.id, prefix.clone()).is_none());
                    Some(prefix)
                }
                Some(HeadPrefix::Reference(id)) => Some(prefixes.get(id).expect("缓存共享前缀不存在").clone()),
                None => None,
            };
            reader.push(segment.id, segment.parent, segment.checkpoints, &segment.events, prefix);
        }
        reader
    }

    fn empty() -> Self {
        Self { nodes: Vec::new(), depths: Vec::new(), empty: Arc::new(None) }
    }

    fn push(
        &mut self,
        id: u64,
        parent: Option<u64>,
        checkpoints: u64,
        events: &[Event<B>],
        prefix: Option<Arc<TraceHead<B>>>,
    ) {
        assert_eq!(id, self.nodes.len() as u64, "缓存段编号不连续");
        let (parent, depth) = match parent {
            Some(parent) => {
                assert!(parent < id, "缓存父段不存在或父链成环：{id}");
                (self.nodes[parent as usize].clone(), self.depths[parent as usize])
            }
            None => (self.empty.clone(), 0),
        };
        assert_eq!(checkpoints, depth, "缓存空段或检查点计数不一致");
        let events = events.iter().cloned().map(Into::into).collect();
        self.nodes.push(Arc::new(Some(Trace::from_path_cache_parts(
            depth.try_into().unwrap(),
            events,
            prefix,
            parent,
        ))));
        self.depths.push(depth + 1);
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
