//! 组织者只保存就绪片段。准入、保存点和汇合条件由调用方共同处理。

use super::super::TaskState;
use crate::config::MergeStrategy;
use std::collections::VecDeque;

pub(in crate::executor) enum ReadyFragments<T> {
    Stack(Vec<T>),
    Queue(VecDeque<T>),
}

impl<T> ReadyFragments<T> {
    pub(in crate::executor) fn new<B>(state: &TaskState<B>) -> Self {
        match state.execution_limits.as_ref().map(|limits| limits.merge_strategy).unwrap_or_default() {
            MergeStrategy::Recursive => Self::Stack(Vec::new()),
            MergeStrategy::Flat => Self::Queue(VecDeque::new()),
        }
    }

    /// 同一组片段的原始顺序由分叉决定。栈把新发现的一组放到旧工作之前。
    pub(in crate::executor) fn extend(&mut self, fragments: impl DoubleEndedIterator<Item = T>) {
        match self {
            Self::Stack(stack) => stack.extend(fragments.rev()),
            Self::Queue(queue) => queue.extend(fragments),
        }
    }

    pub(in crate::executor) fn len(&self) -> usize {
        match self {
            Self::Stack(stack) => stack.len(),
            Self::Queue(queue) => queue.len(),
        }
    }

    pub(in crate::executor) fn pop(&mut self) -> Option<T> {
        match self {
            Self::Stack(stack) => stack.pop(),
            Self::Queue(queue) => queue.pop_front(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::executor::ExecutionLimits;

    #[test]
    fn organizers_choose_distinct_next_fragments_when_both_are_ready() {
        for (strategy, expected) in [(MergeStrategy::Recursive, 3), (MergeStrategy::Flat, 2)] {
            let mut limits = ExecutionLimits::default().with_path_merging(true);
            limits.merge_strategy = strategy;
            let state = TaskState::<B64>::new().with_execution_limits(limits);
            let mut ready = ReadyFragments::new(&state);
            ready.extend([1, 2].into_iter());
            assert_eq!(ready.pop(), Some(1));
            ready.extend([3, 4].into_iter());
            assert_eq!(ready.pop(), Some(expected));
        }
    }
}
