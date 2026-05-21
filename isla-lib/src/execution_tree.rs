// BSD 2-Clause License
//
// Copyright (c) 2026
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// 1. Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, RwLock};

use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::Direction;

use crate::bitvector::BV;
use crate::smt::{Event, Sym};
use crate::source_loc::SourceLoc;

#[derive(Debug)]
pub struct NodeData<B> {
    pub(crate) events: Mutex<Vec<Event<B>>>,
    source_loc: Option<SourceLoc>,
    pub(crate) cfg_info: Mutex<Option<String>>,
}

impl<B> NodeData<B> {
    fn new() -> Self {
        NodeData { events: Mutex::new(Vec::new()), source_loc: None, cfg_info: Mutex::new(None) }
    }

    pub fn set_cfg_info(&self, info: &str) {
        *self.cfg_info.lock().unwrap() = Some(info.to_string());
    }

    pub fn get_cfg_info(&self) -> Option<String> {
        self.cfg_info.lock().unwrap().clone()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeEdge {
    pub fork_id: u32,
    pub condition: Option<Sym>,
    pub condition_expr: Option<String>,
    pub taken: bool,
    pub source_loc: SourceLoc,
}

#[derive(Debug)]
pub struct ExecutionTree<B> {
    graph: RwLock<DiGraph<(), TreeEdge>>,
    nodes: RwLock<HashMap<NodeIndex, Arc<NodeData<B>>>>,
}

impl<B: BV> ExecutionTree<B> {
    pub fn new() -> Self {
        let tree = ExecutionTree { graph: RwLock::new(DiGraph::new()), nodes: RwLock::new(HashMap::new()) };
        let _ = tree.add_node();
        tree
    }

    pub fn add_node(&self) -> (NodeIndex, Arc<NodeData<B>>) {
        let node = Arc::new(NodeData::new());
        let index = {
            let mut graph = self.graph.write().unwrap();
            graph.add_node(())
        };
        self.nodes.write().unwrap().insert(index, Arc::clone(&node));
        (index, node)
    }

    pub fn root(&self) -> (NodeIndex, Arc<NodeData<B>>) {
        let index = NodeIndex::new(0);
        let data = self.nodes.read().unwrap().get(&index).expect("execution tree root missing").clone();
        (index, data)
    }

    pub fn node_data(&self, index: NodeIndex) -> Arc<NodeData<B>> {
        self.nodes.read().unwrap().get(&index).expect("execution tree node missing").clone()
    }

    pub fn add_edge(&self, from: NodeIndex, to: NodeIndex, edge: TreeEdge) {
        self.graph.write().unwrap().add_edge(from, to, edge);
    }

    pub fn fork(
        &self,
        parent: NodeIndex,
        fork_id: u32,
        condition: Sym,
        source_loc: SourceLoc,
    ) -> ((NodeIndex, Arc<NodeData<B>>), (NodeIndex, Arc<NodeData<B>>)) {
        let (left_index, left_node, right_index, right_node) = {
            let mut graph = self.graph.write().unwrap();
            let left_index = graph.add_node(());
            let right_index = graph.add_node(());
            graph.add_edge(
                parent,
                left_index,
                TreeEdge { fork_id, condition: Some(condition), condition_expr: None, taken: true, source_loc },
            );
            graph.add_edge(
                parent,
                right_index,
                TreeEdge { fork_id, condition: Some(condition), condition_expr: None, taken: false, source_loc },
            );
            (left_index, Arc::new(NodeData::new()), right_index, Arc::new(NodeData::new()))
        };

        let mut nodes = self.nodes.write().unwrap();
        nodes.insert(left_index, Arc::clone(&left_node));
        nodes.insert(right_index, Arc::clone(&right_node));
        ((left_index, left_node), (right_index, right_node))
    }

    pub fn parent(&self, node: NodeIndex) -> Option<NodeIndex> {
        let graph = self.graph.read().unwrap();
        graph.neighbors_directed(node, Direction::Incoming).next()
    }

    /// Returns the path from root to `node` (inclusive, root first).
    pub fn path_to_root(&self, mut node: NodeIndex) -> Vec<NodeIndex> {
        let mut path = Vec::new();
        loop {
            path.push(node);
            match self.parent(node) {
                Some(parent) => node = parent,
                None => break,
            }
        }
        path.reverse();
        path
    }

    /// Returns the lowest common ancestor of two nodes.
    pub fn lca(&self, a: NodeIndex, b: NodeIndex) -> NodeIndex {
        let ap = self.path_to_root(a);
        let bp = self.path_to_root(b);
        ap.into_iter()
            .zip(bp)
            .take_while(|(x, y)| x == y)
            .last()
            .map(|(x, _)| x)
            .expect("execution tree should have root")
    }

    /// Returns the path from `ancestor` (exclusive) to `node` (inclusive).
    /// Panics if `ancestor` is not an ancestor of `node`.
    pub fn path_from_ancestor(&self, ancestor: NodeIndex, node: NodeIndex) -> Vec<NodeIndex> {
        let path = self.path_to_root(node);
        let pos = path.iter().position(|n| *n == ancestor).expect("ancestor not on path");
        path[pos + 1..].to_vec()
    }

    pub fn read_graph(&self) -> std::sync::RwLockReadGuard<'_, DiGraph<(), TreeEdge>> {
        self.graph.read().unwrap()
    }

    pub fn read_nodes(&self) -> std::sync::RwLockReadGuard<'_, HashMap<NodeIndex, Arc<NodeData<B>>>> {
        self.nodes.read().unwrap()
    }

    #[cfg(test)]
    fn node_count(&self) -> usize {
        self.graph.read().unwrap().node_count()
    }

    #[cfg(test)]
    fn node_data_count(&self) -> usize {
        self.nodes.read().unwrap().len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::smt::Event;
    use crate::source_loc::SourceLoc;

    fn assert_path(tree: &ExecutionTree<B64>, node: NodeIndex, expected: &[NodeIndex]) {
        assert_eq!(tree.path_to_root(node), expected);
    }

    #[test]
    fn creates_root_adds_nodes_and_forks() {
        let tree = ExecutionTree::<B64>::new();
        assert_eq!(tree.node_count(), 1);
        assert_eq!(tree.node_data_count(), 1);

        let (node, data) = tree.add_node();
        assert_eq!(tree.parent(node), None);
        assert_eq!(tree.node_count(), 2);
        assert_eq!(tree.node_data_count(), 2);
        assert!(data.events.lock().unwrap().is_empty());
        assert!(data.source_loc.is_none());

        let (left, right) = tree.fork(node, 0, Sym::from_u32(0), SourceLoc::unknown());
        assert_eq!(tree.node_count(), 4);
        assert_eq!(tree.node_data_count(), 4);
        assert_eq!(tree.parent(left.0), Some(node));
        assert_eq!(tree.parent(right.0), Some(node));
        assert!(left.1.events.lock().unwrap().is_empty());
        assert!(right.1.events.lock().unwrap().is_empty());
    }

    #[test]
    fn path_to_root_returns_correct_path() {
        let tree = ExecutionTree::<B64>::new();
        let (root, _) = tree.root();
        let ((left, _), (right, _)) = tree.fork(root, 0, Sym::from_u32(0), SourceLoc::unknown());

        assert_path(&tree, left, &[root, left]);
        assert_path(&tree, right, &[root, right]);

        let ((left_left, _), _) = tree.fork(left, 1, Sym::from_u32(1), SourceLoc::unknown());
        assert_path(&tree, left_left, &[root, left, left_left]);
    }

    #[test]
    fn lca_returns_common_ancestor() {
        let tree = ExecutionTree::<B64>::new();
        let (root, _) = tree.root();
        let ((left, _), (right, _)) = tree.fork(root, 0, Sym::from_u32(0), SourceLoc::unknown());
        let ((left_left, _), (left_right, _)) = tree.fork(left, 1, Sym::from_u32(1), SourceLoc::unknown());

        assert_eq!(tree.lca(left_left, left_right), left);
        assert_eq!(tree.lca(left_left, right), root);
        assert_eq!(tree.lca(left, right), root);
    }

    #[test]
    fn events_stored_per_node() {
        let tree = ExecutionTree::<B64>::new();
        let (root_index, root_data) = tree.root();
        root_data.events.lock().unwrap().push(Event::Cycle);

        let ((left_index, left_data), _) = tree.fork(root_index, 0, Sym::from_u32(0), SourceLoc::unknown());
        left_data.events.lock().unwrap().push(Event::Cycle);
        left_data.events.lock().unwrap().push(Event::Cycle);

        let root_events = root_data.events.lock().unwrap().clone();
        let left_events = left_data.events.lock().unwrap().clone();

        assert_eq!(root_events.len(), 1);
        assert!(matches!(root_events[0], Event::Cycle));
        assert_eq!(left_events.len(), 2);
        assert!(left_events.iter().all(|event| matches!(event, Event::Cycle)));

        assert_eq!(tree.node_data(root_index).events.lock().unwrap().len(), 1);
        assert_eq!(tree.node_data(left_index).events.lock().unwrap().len(), 2);
    }

    #[test]
    fn concurrent_add_node_and_fork() {
        use std::sync::Arc;
        use std::thread;

        let tree = Arc::new(ExecutionTree::<B64>::new());
        let num_threads = 4;
        let forks_per_thread = 100;

        let handles: Vec<_> = (0..num_threads)
            .map(|t| {
                let tree = Arc::clone(&tree);
                thread::spawn(move || {
                    for i in 0..forks_per_thread {
                        let (node, _) = tree.add_node();
                        let fork_id = (t * forks_per_thread + i) as u32;
                        let ((left, _), (right, _)) =
                            tree.fork(node, fork_id, Sym::from_u32(fork_id), SourceLoc::unknown());
                        assert_eq!(tree.parent(left), Some(node));
                        assert_eq!(tree.parent(right), Some(node));
                    }
                })
            })
            .collect();

        for h in handles {
            h.join().expect("thread panicked");
        }

        let expected = 1 + num_threads * forks_per_thread * 3;
        assert_eq!(tree.node_count(), expected);
        assert_eq!(tree.node_data_count(), expected);
    }
}
