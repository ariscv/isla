//! 合并历史的不可变分段；执行帧克隆不复制历史，连续视图只在消费边界建立。
use super::RegionMergeRecord;
use std::ops::Deref;
#[cfg(test)]
use std::ops::DerefMut;
use std::sync::{Arc, OnceLock};

#[derive(Debug)]
pub struct MergeHistory<B>(Arc<Segment<B>>);
#[derive(Debug)]
struct Segment<B> {
    len: usize,
    items: Option<Items<B>>,
    flat: OnceLock<Vec<RegionMergeRecord<B>>>,
}
#[derive(Debug)]
enum Items<B> {
    Leaf(Vec<RegionMergeRecord<B>>),
    Concat(MergeHistory<B>, MergeHistory<B>),
    Range(MergeHistory<B>, usize),
}
// 长时间执行可产生很长的前缀链，最后一个引用释放时用迭代销毁。
impl<B> Drop for Segment<B> {
    fn drop(&mut self) {
        let mut pending = vec![self.items.take()];
        while let Some(items) = pending.pop() {
            let children = match items {
                Some(Items::Concat(a, b)) => vec![a, b],
                Some(Items::Range(a, _)) => vec![a],
                _ => continue,
            };
            for child in children {
                if let Some(mut segment) = Arc::into_inner(child.0) {
                    pending.push(segment.items.take());
                }
            }
        }
    }
}
impl<B> Clone for MergeHistory<B> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
impl<B> From<Vec<RegionMergeRecord<B>>> for MergeHistory<B> {
    fn from(items: Vec<RegionMergeRecord<B>>) -> Self {
        Self(Arc::new(Segment { len: items.len(), items: Some(Items::Leaf(items)), flat: OnceLock::new() }))
    }
}
impl<B> Default for MergeHistory<B> {
    fn default() -> Self {
        Vec::new().into()
    }
}
impl<B> MergeHistory<B> {
    pub fn len(&self) -> usize {
        self.0.len
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    #[cfg(test)]
    pub(super) fn retained_record_slots(&self) -> usize {
        let mut pending = vec![self];
        let mut seen = std::collections::HashSet::new();
        let mut slots = 0;
        while let Some(history) = pending.pop() {
            if !seen.insert(Arc::as_ptr(&history.0)) {
                continue;
            }
            slots += history.0.flat.get().map_or(0, Vec::capacity);
            match history.0.items.as_ref().unwrap() {
                Items::Leaf(items) => slots += items.capacity(),
                Items::Concat(left, right) => pending.extend([left, right]),
                Items::Range(source, _) => pending.push(source),
            }
        }
        slots
    }
    pub fn clear(&mut self) {
        *self = Self::default();
    }
    fn concat(&mut self, right: Self) {
        if right.is_empty() {
            return;
        }
        if self.is_empty() {
            *self = right;
            return;
        }
        *self = Self(Arc::new(Segment {
            len: self.len().checked_add(right.len()).expect("合并历史长度溢出"),
            items: Some(Items::Concat(self.clone(), right)),
            flat: OnceLock::new(),
        }));
    }
    fn range(&self, start: usize, end: usize) -> Self {
        assert!(start <= end && end <= self.len());
        if start == end {
            return Self::default();
        }
        if start == 0 && end == self.len() {
            return self.clone();
        }
        Self(Arc::new(Segment {
            len: end - start,
            items: Some(Items::Range(self.clone(), start)),
            flat: OnceLock::new(),
        }))
    }
    pub(super) fn append_suffix(&mut self, other: &Self, start: usize) {
        self.concat(other.range(start, other.len()));
    }
    pub fn push(&mut self, record: RegionMergeRecord<B>) {
        if let Some(segment) = Arc::get_mut(&mut self.0) {
            if let Some(Items::Leaf(items)) = &mut segment.items {
                items.push(record);
                segment.len += 1;
                segment.flat.take();
                return;
            }
        }
        self.concat(vec![record].into());
    }
    pub fn iter(&self) -> HistoryIter<'_, B> {
        self.suffix(0)
    }
    pub(super) fn suffix(&self, start: usize) -> HistoryIter<'_, B> {
        assert!(start <= self.len());
        HistoryIter { pending: vec![(self, start, self.len())], current: [].iter() }
    }
}
impl<B: Clone> MergeHistory<B> {
    /// 只重建本次产生或重命名的后缀；已有前缀不建立连续视图。
    pub(super) fn edit_suffix(&mut self, start: usize, edit: impl FnOnce(&mut [RegionMergeRecord<B>])) {
        let mut items: Vec<_> = self.suffix(start).cloned().collect();
        edit(&mut items);
        let unchanged = self.suffix(start).zip(&items).take_while(|(a, b)| a.same_occurrence(b)).count();
        if unchanged == items.len() {
            return;
        }
        let mut prefix = self.range(0, start + unchanged);
        // into_iter().skip().collect() 可以复用原 Vec 的整段容量，必须显式收缩。
        items.drain(..unchanged);
        items.shrink_to_fit();
        prefix.concat(items.into());
        *self = prefix;
    }
    pub(super) fn last_mut(&mut self) -> Option<&mut RegionMergeRecord<B>> {
        if self.is_empty() {
            return None;
        }
        let last = self.len() - 1;
        let unique_leaf = Arc::get_mut(&mut self.0).is_some_and(|s| matches!(s.items, Some(Items::Leaf(_))));
        if !unique_leaf {
            let tail = vec![self.suffix(last).next().unwrap().clone()];
            let mut prefix = self.range(0, last);
            prefix.concat(tail.into());
            *self = prefix;
        }
        let segment = Arc::get_mut(&mut self.0).unwrap();
        match segment.items.as_mut().unwrap() {
            Items::Leaf(items) => items.last_mut(),
            Items::Concat(_, tail) => tail.last_mut(),
            Items::Range(..) => unreachable!(),
        }
    }
}
impl<B: Clone> Deref for MergeHistory<B> {
    type Target = [RegionMergeRecord<B>];
    fn deref(&self) -> &Self::Target {
        if let Some(Items::Leaf(items)) = &self.0.items {
            items
        } else {
            self.0.flat.get_or_init(|| self.iter().cloned().collect())
        }
    }
}
// 可变切片仅用于需要原位改动的测试；生产更新必须指定新增后缀边界。
#[cfg(test)]
impl<B: Clone> DerefMut for MergeHistory<B> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        let unique_leaf = Arc::get_mut(&mut self.0).is_some_and(|s| matches!(s.items, Some(Items::Leaf(_))));
        if !unique_leaf {
            *self = self.iter().cloned().collect::<Vec<_>>().into();
        }
        let segment = Arc::get_mut(&mut self.0).unwrap();
        match segment.items.as_mut().unwrap() {
            Items::Leaf(items) => items,
            _ => unreachable!(),
        }
    }
}
pub struct HistoryIter<'a, B> {
    pending: Vec<(&'a MergeHistory<B>, usize, usize)>,
    current: std::slice::Iter<'a, RegionMergeRecord<B>>,
}
impl<'a, B> Iterator for HistoryIter<'a, B> {
    type Item = &'a RegionMergeRecord<B>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(record) = self.current.next() {
                return Some(record);
            }
            let (history, start, end) = self.pending.pop()?;
            if start == end {
                continue;
            }
            match history.0.items.as_ref().unwrap() {
                Items::Leaf(items) => self.current = items[start..end].iter(),
                Items::Range(source, offset) => self.pending.push((source, start + offset, end + offset)),
                Items::Concat(left, right) => {
                    let split = left.len();
                    if end > split {
                        self.pending.push((right, start.saturating_sub(split), end - split));
                    }
                    if start < split {
                        self.pending.push((left, start, end.min(split)));
                    }
                }
            }
        }
    }
}
impl<'a, B> IntoIterator for &'a MergeHistory<B> {
    type Item = &'a RegionMergeRecord<B>;
    type IntoIter = HistoryIter<'a, B>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
