//! 循环前沿的逻辑臂依赖与存活量。
use super::*;

impl<B: BV> Solver<'_, B> {
    pub(crate) fn loop_arm_count(&self) -> usize {
        self.logical_arms.arms.len()
    }
    #[cfg(test)]
    pub(crate) fn loop_event_count(&self) -> usize {
        self.transaction_events.len()
    }
}

impl LogicalArm {
    fn index(self) -> usize {
        self.0.get() - 1
    }
    fn at(index: usize) -> Self {
        Self(NonZeroUsize::new(index.checked_add(1).expect("逻辑臂编号溢出")).unwrap())
    }
}

impl LogicalArms {
    pub(super) fn children(&self) -> Vec<Vec<LogicalArm>> {
        let mut children = vec![Vec::new(); self.arms.len()];
        for (index, node) in self.arms.iter().enumerate() {
            if let Some(parent) = node.parent {
                children[parent.index()].push(LogicalArm::at(index));
            }
        }
        children
    }

    /// 两种遍历共用 sources。投影沿父臂向上，撤销沿子臂向下。
    /// 只有从每个活入口看，两种可达性都相同的旧节点才能共用编号。
    fn compact_loop(&mut self, start: usize, live: &mut [LogicalArm]) {
        let end = self.arms.len();
        let mut roots = live.to_vec();
        roots.extend(self.active);
        for (index, node) in self.arms.iter().enumerate() {
            for other in node.parent.iter().chain(&node.sources) {
                if (index < start) != (other.index() < start) {
                    roots.push(LogicalArm::at(index.min(other.index())));
                }
            }
        }
        roots.sort_unstable_by_key(|id| id.index());
        roots.dedup();
        let children = self.children();
        let mut signatures = vec![Vec::with_capacity(roots.len()); end - start];
        for root in &roots {
            let visible = self.reachable(*root, |_, node, pending| pending.extend(node.parent));
            let discard = self.reachable(*root, |id, _, pending| pending.extend(&children[id.index()]));
            for (i, key) in signatures.iter_mut().enumerate() {
                key.push(u8::from(visible[start + i]) | (u8::from(discard[start + i]) << 1));
            }
        }

        // 活入口保留独立节点，供以后接入新来源或新子臂。入口以前的编号始终稳定。
        let mut groups = HashMap::new();
        let mut count = start;
        let mut ids: Vec<_> = (0..start).map(LogicalArm::at).collect();
        for (i, key) in signatures.into_iter().enumerate() {
            let mut allocate = || {
                let id = LogicalArm::at(count);
                count += 1;
                id
            };
            let id = if roots.binary_search_by_key(&(start + i), |id| id.index()).is_ok() {
                allocate()
            } else {
                *groups.entry(key).or_insert_with(allocate)
            };
            ids.push(id);
        }
        if count == end {
            return;
        }
        let mut parents = vec![Vec::new(); count - start];
        let mut sources = vec![Vec::new(); count - start];
        for (i, node) in self.arms[start..].iter().enumerate() {
            let group = ids[start + i];
            let index = group.index() - start;
            parents[index].extend(node.parent.map(|p| ids[p.index()]).filter(|p| *p != group));
            sources[index].extend(node.sources.iter().map(|s| ids[s.index()]).filter(|s| *s != group));
        }
        for list in parents.iter_mut().chain(&mut sources) {
            list.sort_unstable_by_key(|id| id.index());
            list.dedup();
        }
        // 一个等价类可能继承多条父边。为多出的每条边保留一个双向来源节点，
        // 使向上投影和向下撤销都能像原图一样穿过该类。
        let extra = parents.iter().map(|p| p.len().saturating_sub(1)).sum::<usize>();
        if count + extra >= end {
            return;
        }
        for node in &mut self.arms[..start] {
            if let Some(parent) = &mut node.parent {
                *parent = ids[parent.index()];
            }
            for source in &mut node.sources {
                *source = ids[source.index()];
            }
        }
        self.arms.truncate(start);
        let mut aliases = Vec::with_capacity(extra);
        for (i, (mut parents, mut sources)) in parents.into_iter().zip(sources).enumerate() {
            let parent = parents.pop();
            for other in parents {
                sources.push(LogicalArm::at(count + aliases.len()));
                aliases.push(Arm { parent: Some(other), sources: vec![LogicalArm::at(start + i)] });
            }
            self.arms.push(Arm { parent, sources });
        }
        self.arms.extend(aliases);
        if self.arms.len() < self.arms.capacity() / 2 {
            self.arms.shrink_to_fit();
        }
        for owner in &mut self.owners {
            if let Some(arm) = &mut owner.arm {
                *arm = ids[arm.index()];
            }
        }
        for arm in live {
            *arm = ids[arm.index()];
        }
        // 活动调用栈持有入口以前的编号。折叠只发生在本轮的原生臂返回后。
        assert!(self.active.is_none_or(|id| id.index() < start));
    }
}

impl<B: BV> Solver<'_, B> {
    pub(crate) fn compact_loop_arms(&mut self, start: usize, live: &mut [LogicalArm]) {
        self.logical_arms.compact_loop(start, live);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn arm(journal: &mut LogicalArms, parent: Option<LogicalArm>, sources: Vec<LogicalArm>) -> LogicalArm {
        let id = LogicalArm::at(journal.arms.len());
        journal.arms.push(Arm { parent, sources });
        journal.owners.push(EffectOwner { arm: Some(id), ..Default::default() });
        id
    }

    // 同一事件从某个出口可见，并不表示撤销该出口可以删除它。
    fn effects(journal: &LogicalArms, roots: &[LogicalArm]) -> Vec<Vec<(bool, bool)>> {
        let children = journal.children();
        roots
            .iter()
            .map(|root| {
                let removed = journal.reachable(*root, |id, _, pending| pending.extend(&children[id.index()]));
                journal
                    .group_events(Some(*root))
                    .zip(&journal.owners)
                    .map(|((visible, _, _), owner)| (visible, removed[owner.arm.unwrap().index()]))
                    .collect()
            })
            .collect()
    }

    #[test]
    fn loop_arm_compaction_preserves_projection_and_discard_for_future_children() {
        let run = |compact| {
            let mut journal = LogicalArms::default();
            let outer = arm(&mut journal, None, vec![]);
            let sibling = arm(&mut journal, None, vec![]);
            let start = journal.arms.len();
            let mut exit = arm(&mut journal, Some(outer), vec![]);
            let mut next = arm(&mut journal, Some(outer), vec![]);
            for i in 0..16 {
                let hit = arm(&mut journal, Some(next), vec![]);
                if i == 3 {
                    journal.arms[sibling.index()].sources.push(hit);
                }
                let miss = arm(&mut journal, Some(next), vec![]);
                exit = arm(&mut journal, Some(outer), vec![exit, hit]);
                next = arm(&mut journal, Some(outer), vec![miss]);
                if compact {
                    let mut live = [exit, next];
                    journal.compact_loop(start, &mut live);
                    [exit, next] = live;
                }
            }
            let child = arm(&mut journal, Some(next), vec![]);
            let joined = arm(&mut journal, Some(outer), vec![child, exit]);
            (journal.arms.len(), effects(&journal, &[outer, sibling, exit, next, child, joined]))
        };
        let (full, before) = run(false);
        let (kept, after) = run(true);
        assert!(kept < full);
        assert_eq!(before, after);
        assert!(after.iter().flatten().any(|(visible, discard)| visible != discard));
    }
}
