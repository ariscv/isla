//! 循环工作项的等待关系；此处不选择哪个工作项先执行。

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(in crate::executor) struct LoopNode(usize);

struct Node<W> {
    work: W,
    parent: Option<(LoopNode, usize)>,
    children: [Option<LoopNode>; 2],
}

pub(in crate::executor) struct LoopDependencies<W> {
    nodes: Vec<Option<Node<W>>>,
    vacant: Vec<usize>,
}

impl<W> LoopDependencies<W> {
    pub(in crate::executor) fn new(work: W) -> (Self, LoopNode) {
        (
            Self { nodes: vec![Some(Node { work, parent: None, children: [None, None] })], vacant: Vec::new() },
            LoopNode(0),
        )
    }

    fn node(&self, id: LoopNode) -> &Node<W> {
        self.nodes[id.0].as_ref().expect("循环依赖必须指向活动工作项")
    }

    fn node_mut(&mut self, id: LoopNode) -> &mut Node<W> {
        self.nodes[id.0].as_mut().expect("循环依赖必须指向活动工作项")
    }

    pub(in crate::executor) fn work_mut(&mut self, id: LoopNode) -> &mut W {
        &mut self.node_mut(id).work
    }

    pub(in crate::executor) fn work(&self, id: LoopNode) -> &W {
        &self.node(id).work
    }

    pub(in crate::executor) fn ancestors(&self, id: LoopNode) -> impl Iterator<Item = &W> {
        std::iter::successors(Some(id), |id| self.node(*id).parent.map(|(parent, _)| parent)).map(|id| self.work(id))
    }

    pub(in crate::executor) fn attach(&mut self, parent: LoopNode, side: usize, work: W) -> LoopNode {
        assert!(self.node(parent).children[side].is_none(), "每臂最多等待一个子汇合");
        let node = Node { work, parent: Some((parent, side)), children: [None, None] };
        let child = if let Some(slot) = self.vacant.pop() {
            assert!(self.nodes[slot].replace(node).is_none());
            LoopNode(slot)
        } else {
            self.nodes.push(Some(node));
            LoopNode(self.nodes.len() - 1)
        };
        self.node_mut(parent).children[side] = Some(child);
        child
    }

    /// 轮次已经只有一条继续路径。按执行顺序交出沿途完成的工作项，保留根槽供下一轮使用。
    pub(in crate::executor) fn drain_spine(&mut self, frontier: &mut LoopNode) -> Vec<W> {
        let mut retired = Vec::new();
        while self.node(*frontier).parent.is_some() {
            let (work, parent) = self.complete(*frontier);
            retired.push(work);
            *frontier = parent.unwrap().0;
        }
        retired.reverse();
        retired
    }

    pub(in crate::executor) fn can_complete(&self, id: LoopNode) -> bool {
        self.node(id).children.iter().all(Option::is_none)
    }

    pub(in crate::executor) fn complete(&mut self, id: LoopNode) -> (W, Option<(LoopNode, usize)>) {
        assert!(self.can_complete(id), "子汇合完成前不能关闭父项");
        let node = self.nodes[id.0].take().unwrap();
        if let Some((parent, side)) = node.parent {
            assert_eq!(self.node_mut(parent).children[side].take(), Some(id));
        }
        self.vacant.push(id.0);
        (node.work, node.parent)
    }
}
