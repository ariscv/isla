//! 三种轨迹共用的不可变前缀序列。
use std::sync::Arc;

// 源码配置：Limited(256) 按容量分块；Unlimited 仅在共享后追加时分块。
pub(super) const TRACE_CHUNK_CAPACITY: ChunkCapacity = ChunkCapacity::Unlimited;

// 两个变体供上方配置选择，单次构建可能只使用其中一个。
#[allow(dead_code)]
pub(super) enum ChunkCapacity {
    Limited(usize),
    Unlimited,
}

impl PartialEq<ChunkCapacity> for usize {
    fn eq(&self, capacity: &ChunkCapacity) -> bool {
        match capacity {
            ChunkCapacity::Limited(limit) => self == limit,
            ChunkCapacity::Unlimited => false,
        }
    }
}

impl PartialOrd<ChunkCapacity> for usize {
    fn partial_cmp(&self, capacity: &ChunkCapacity) -> Option<std::cmp::Ordering> {
        Some(match capacity {
            ChunkCapacity::Limited(limit) => self.cmp(limit),
            // 即使 usize::MAX 也小于无限容量，不能把它当作无限的哨兵值。
            ChunkCapacity::Unlimited => std::cmp::Ordering::Less,
        })
    }
}

// 沿用 SMT Trace 的不可变 Arc 前缀机制；各类轨迹的观察序列共用这一局部表示。
// head 共享或填满时封入前缀，禁止 make_mut 克隆 payload。
pub(super) struct SharedSequence<T> {
    len: usize,
    head: Arc<Vec<T>>,
    prefix: Option<Arc<TraceChunk<T>>>,
}

struct TraceChunk<T> {
    items: Arc<Vec<T>>,
    previous: Option<Arc<TraceChunk<T>>>,
}

impl<T> Drop for TraceChunk<T> {
    fn drop(&mut self) {
        let mut previous = self.previous.take();
        while let Some(chunk) = previous {
            // into_inner 对并发丢弃最后两个 Arc 也保证恰好一方取得所有权。
            match Arc::into_inner(chunk) {
                Some(mut chunk) => previous = chunk.previous.take(),
                None => break,
            }
        }
    }
}

impl<T> Default for SharedSequence<T> {
    fn default() -> Self {
        Self { len: 0, head: Arc::new(Vec::new()), prefix: None }
    }
}

impl<T> Clone for SharedSequence<T> {
    fn clone(&self) -> Self {
        Self { len: self.len, head: self.head.clone(), prefix: self.prefix.clone() }
    }
}

impl<T> SharedSequence<T> {
    pub(super) fn push(&mut self, item: T) {
        if self.head.len() >= TRACE_CHUNK_CAPACITY || Arc::get_mut(&mut self.head).is_none() {
            let old_head = std::mem::replace(&mut self.head, Arc::new(Vec::new()));
            if !old_head.is_empty() {
                self.prefix = Some(Arc::new(TraceChunk { items: old_head, previous: self.prefix.take() }));
            }
        }
        Arc::get_mut(&mut self.head).expect("trace 新后缀必须独占").push(item);
        self.len += 1;
    }

    pub(super) fn len(&self) -> usize {
        self.len
    }
    pub(super) fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub(super) fn iter(&self) -> SharedSequenceIter<'_, T> {
        let mut chunks = vec![self.head.as_slice()];
        let mut prefix = self.prefix.as_deref();
        while let Some(chunk) = prefix {
            chunks.push(chunk.items.as_slice());
            prefix = chunk.previous.as_deref();
        }
        SharedSequenceIter { chunks, current: [].iter(), remaining: self.len }
    }
}

pub(super) struct SharedSequenceIter<'a, T> {
    chunks: Vec<&'a [T]>,
    current: std::slice::Iter<'a, T>,
    remaining: usize,
}

impl<'a, T> Iterator for SharedSequenceIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(item) = self.current.next() {
                self.remaining -= 1;
                return Some(item);
            }
            self.current = self.chunks.pop()?.iter();
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<T> ExactSizeIterator for SharedSequenceIter<'_, T> {}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn trace_capacity_comparison_handles_boundaries_and_unlimited() {
        let finite = ChunkCapacity::Limited(256);
        assert!(255usize < finite);
        assert!(256usize == finite);
        assert!(256usize >= finite);
        assert!(257usize > finite);
        assert!(257usize != finite);
        assert!(usize::MAX == ChunkCapacity::Limited(usize::MAX));
        for len in [0usize, 255, 256, 257, usize::MAX] {
            assert!(len < ChunkCapacity::Unlimited);
            assert!(len <= ChunkCapacity::Unlimited);
            assert!(len != ChunkCapacity::Unlimited);
            assert!(!(len >= ChunkCapacity::Unlimited));
            assert!(!(len > ChunkCapacity::Unlimited));
        }
    }
    #[test]
    fn trace_capacity_preserves_exclusive_records() {
        let mut sequence = SharedSequence::default();
        for i in 0..1025 {
            sequence.push(i);
        }
        match TRACE_CHUNK_CAPACITY {
            ChunkCapacity::Unlimited => {
                assert!(sequence.prefix.is_none(), "无限容量下独占记录不应因长度分块");
                assert_eq!(sequence.head.len(), 1025);
            }
            ChunkCapacity::Limited(capacity) => {
                assert!(capacity > 0, "有限块容量必须大于零");
                assert_eq!(sequence.head.len(), (1025 - 1) % capacity + 1);
                let mut prefix = sequence.prefix.as_deref();
                let mut chunks = 0;
                while let Some(chunk) = prefix {
                    assert_eq!(chunk.items.len(), capacity);
                    chunks += 1;
                    prefix = chunk.previous.as_deref();
                }
                assert_eq!(chunks, (1025 - 1) / capacity);
            }
        }
        assert_eq!(sequence.iter().copied().collect::<Vec<_>>(), (0..1025).collect::<Vec<_>>());
        let mut child = sequence.clone();
        child.push(1025);
        assert!(std::ptr::eq(sequence.iter().next().unwrap(), child.iter().next().unwrap()));
        assert_eq!(sequence.len(), 1025);
        assert_eq!(child.iter().copied().collect::<Vec<_>>(), (0..1026).collect::<Vec<_>>());
    }
}
