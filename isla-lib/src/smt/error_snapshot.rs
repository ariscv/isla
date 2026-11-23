//! 一个根事务内，按事件缓冲的位置冻结不可变分段。错误叶只引用本臂可见的位置。
use super::{Event, BV};
use std::sync::{Arc, Weak};

const BLOCK: usize = u64::BITS as usize;

#[derive(Debug)]
pub(super) struct Segment<B> {
    previous: Option<Arc<Self>>,
    events: Arc<Vec<Event<B>>>,
    selected: u64,
    pub(super) len: usize,
}

impl<B> Drop for Segment<B> {
    fn drop(&mut self) {
        let mut previous = self.previous.take();
        while let Some(node) = previous {
            let Some(mut node) = Arc::into_inner(node) else { break };
            previous = node.previous.take();
        }
    }
}

impl<B> Segment<B> {
    fn indices(&self) -> impl DoubleEndedIterator<Item = usize> + '_ {
        (0..self.events.len()).filter(|i| self.selected & (1 << i) != 0)
    }

    pub(super) fn iter(&self) -> impl DoubleEndedIterator<Item = &Event<B>> {
        let chunks: Vec<_> = std::iter::successors(Some(self), |s| s.previous.as_deref()).collect();
        chunks.into_iter().rev().flat_map(|s| s.indices().map(|i| &s.events[i]))
    }

    pub(super) fn event(&self, index: usize) -> &Event<B> {
        let mut s = self;
        while let Some(prev) = s.previous.as_deref() {
            if prev.len <= index {
                break;
            }
            s = prev;
        }
        let offset = index - s.previous.as_ref().map_or(0, |p| p.len);
        &s.events[s.indices().nth(offset).expect("事件偏移必须在投影段内")]
    }
}

impl<B: BV> Segment<B> {
    pub(super) fn estimated_bytes(node: &Arc<Self>, seen: &mut std::collections::HashSet<usize>) -> usize {
        let mut bytes = 0;
        for node in std::iter::successors(Some(node), |s| s.previous.as_ref()) {
            if !seen.insert(Arc::as_ptr(node) as usize) {
                break;
            }
            bytes += std::mem::size_of::<Self>();
            if seen.insert(Arc::as_ptr(&node.events) as usize) {
                bytes += std::mem::size_of::<Vec<Event<B>>>()
                    + node.events.capacity() * std::mem::size_of::<Event<B>>()
                    + node.events.iter().map(crate::executor::stats::memory_stats::event_heap_bytes).sum::<usize>();
            }
        }
        bytes
    }
}

struct Block<B> {
    end: usize,
    events: Weak<Vec<Event<B>>>,
    projection: Weak<Segment<B>>,
}

pub(super) struct SnapshotBlocks<B>(Vec<Block<B>>);

impl<B> Default for SnapshotBlocks<B> {
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl<B: BV> SnapshotBlocks<B> {
    /// 保留改写点前面的槽位。被截短的最后一段仍引用原数组，旧叶不受影响。
    pub(super) fn truncate(&mut self, start: usize) {
        if self.0.last().is_none_or(|block| block.end <= start) {
            return;
        }
        let full = self.0.partition_point(|block| block.end <= start);
        let partial = start > 0 && (full == 0 || self.0[full - 1].end < start);
        self.0.truncate(full + usize::from(partial));
        if partial {
            self.0[full].end = start;
        }
    }

    pub(super) fn project(&mut self, events: &[Event<B>], selected: &[bool]) -> Option<Arc<Segment<B>>> {
        assert_eq!(events.len(), selected.len());
        let mut end = self.0.last().map_or(0, |block| block.end);
        while end < events.len() {
            end = (end + BLOCK).min(events.len());
            self.0.push(Block { end, events: Weak::new(), projection: Weak::new() });
        }

        let mut tip = None;
        let mut start = 0;
        for block in &mut self.0 {
            let range = start..block.end;
            start = block.end;
            let mask =
                selected[range.clone()].iter().enumerate().fold(0, |bits, (i, &keep)| bits | ((keep as u64) << i));
            if mask == 0 {
                continue;
            }
            // 同一输入段、相同位置和相同父段对应同一段投影。不同选择仍共用事件载荷。
            if let Some(old) = block.projection.upgrade() {
                let same_parent = match (&old.previous, &tip) {
                    (Some(a), Some(b)) => Arc::ptr_eq(a, b),
                    (None, None) => true,
                    _ => false,
                };
                if same_parent && old.selected == mask {
                    tip = Some(old);
                    continue;
                }
            }
            let frozen = block.events.upgrade().unwrap_or_else(|| {
                let items = Arc::new(events[range].to_vec());
                block.events = Arc::downgrade(&items);
                items
            });
            let len = tip.as_ref().map_or(0, |p| p.len) + mask.count_ones() as usize;
            let node = Arc::new(Segment { previous: tip, events: frozen, selected: mask, len });
            block.projection = Arc::downgrade(&node);
            tip = Some(node);
        }
        tip
    }
}
