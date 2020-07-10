use crate::graph::Graph;
use slotmap::DefaultKey;
use std::{
    cmp::{Ord, Ordering, PartialOrd},
    collections::{BinaryHeap, VecDeque},
    fmt::Debug,
};

#[derive(Debug, PartialEq, Copy, Clone)]
pub(crate) enum StorageKind {
    BFSQueue,
    DFSStack,
    LexicographicalHeap,
    PrimWeightPriority,
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub(crate) struct HeapEntry<T: Copy + Debug + Ord> {
    slotmap_key: DefaultKey,
    node_value: T,
    extra: i32,
}

impl<T: Copy + Debug + Ord> Ord for HeapEntry<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        other
            .extra
            .cmp(&self.extra)
            .then_with(|| other.node_value.cmp(&self.node_value))
    }
}

impl<T: Copy + Debug + Ord> PartialOrd for HeapEntry<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug)]
pub(crate) struct NodeStorage<'a, T: Copy + Debug + Ord, U: Debug> {
    kind: StorageKind,
    graph: &'a Graph<T, U>,
    pub(crate) queue: Option<VecDeque<DefaultKey>>,
    pub(crate) stack: Option<Vec<DefaultKey>>,
    pub(crate) heap: Option<BinaryHeap<HeapEntry<T>>>,
    pub(crate) priority_queue: Option<BinaryHeap<HeapEntry<T>>>,
}

impl<'a, T: Copy + Debug + Ord, U: Debug> NodeStorage<'a, T, U> {
    pub(crate) fn new(g: &'a Graph<T, U>, kind: StorageKind) -> Self {
        let mut ret = NodeStorage {
            kind,
            graph: g,
            queue: None,
            stack: None,
            heap: None,
            priority_queue: None,
        };
        match kind {
            StorageKind::BFSQueue => {
                ret.queue = Some(VecDeque::new());
            }
            StorageKind::DFSStack => {
                ret.stack = Some(Vec::new());
            }
            StorageKind::LexicographicalHeap => {
                ret.heap = Some(BinaryHeap::new());
            }
            StorageKind::PrimWeightPriority => {
                ret.priority_queue = Some(BinaryHeap::new());
            }
        }
        ret
    }

    pub(crate) fn push(&mut self, elem: DefaultKey) {
        match self.kind {
            StorageKind::BFSQueue => {
                if let Some(ref mut storage) = self.queue {
                    (*storage).push_back(elem);
                }
            }
            StorageKind::DFSStack => {
                if let Some(ref mut storage) = self.stack {
                    (*storage).push(elem);
                    storage.dedup();
                }
            }
            StorageKind::LexicographicalHeap => {
                if let Some(ref mut storage) = self.heap {
                    (*storage).push(HeapEntry {
                        slotmap_key: elem,
                        node_value: *self.graph.nodes.get(elem).unwrap(),
                        extra: *self.graph.indegrees.get(elem).unwrap_or(&0usize) as i32,
                    });
                }
            }
            _ => {}
        }
    }

    pub(crate) fn push_weight(&mut self, elem: DefaultKey, weight: i32) {
        match self.kind {
            StorageKind::PrimWeightPriority => {
                if let Some(ref mut storage) = self.priority_queue {
                    (*storage).push(HeapEntry {
                        slotmap_key: elem,
                        node_value: *self.graph.nodes.get(elem).unwrap(),
                        extra: weight,
                    });
                }
            }
            _ => panic!("what are u doing"),
        }
    }

    pub(crate) fn pop(&mut self) -> Option<DefaultKey> {
        match self.kind {
            StorageKind::BFSQueue => {
                if let Some(ref mut storage) = self.queue {
                    (*storage).pop_front()
                } else {
                    None
                }
            }
            StorageKind::DFSStack => {
                if let Some(ref mut storage) = self.stack {
                    (*storage).pop()
                } else {
                    None
                }
            }
            StorageKind::LexicographicalHeap => {
                if let Some(ref mut storage) = self.heap {
                    (*storage).pop().map(|x| x.slotmap_key)
                } else {
                    None
                }
            }
            StorageKind::PrimWeightPriority => {
                if let Some(ref mut storage) = self.priority_queue {
                    (*storage).pop().map(|x| x.slotmap_key)
                } else {
                    None
                }
            }
        }
    }

    pub(crate) fn pop_with_weight(&mut self) -> Option<(DefaultKey, i32)> {
        if let StorageKind::PrimWeightPriority = self.kind {
            if let Some(ref mut storage) = self.priority_queue {
                return (*storage).pop().map(|x| (x.slotmap_key, x.extra));
            } else {
                return None;
            }
        }
        None
    }

    pub(crate) fn is_empty(&self) -> Option<bool> {
        match self.kind {
            StorageKind::BFSQueue => {
                if let Some(ref storage) = self.queue {
                    Some((*storage).is_empty())
                } else {
                    None
                }
            }
            StorageKind::DFSStack => {
                if let Some(ref storage) = self.stack {
                    Some((*storage).is_empty())
                } else {
                    None
                }
            }
            StorageKind::LexicographicalHeap => {
                if let Some(ref storage) = self.heap {
                    Some((*storage).is_empty())
                } else {
                    None
                }
            }
            StorageKind::PrimWeightPriority => {
                if let Some(ref storage) = self.priority_queue {
                    Some((*storage).is_empty())
                } else {
                    None
                }
            }
        }
    }

    pub(crate) fn reduce_indegree(&mut self, dst: DefaultKey) {
        if let StorageKind::LexicographicalHeap = self.kind {
            let mut v = self.heap.take().unwrap().into_vec();

            for mut e in v.iter_mut() {
                if e.slotmap_key == dst {
                    e.extra -= 1;
                }
            }

            self.heap.replace(v.into());
        }
    }

    pub(crate) fn reduce_weight_to(&mut self, node: DefaultKey, cmp_weight: i32) -> Option<()> {
        let mut ret: Option<()> = None;

        if let StorageKind::PrimWeightPriority = self.kind {
            let mut v = self.priority_queue.take().unwrap().into_vec();

            for mut e in v.iter_mut() {
                if e.slotmap_key == node && cmp_weight < e.extra {
                    e.extra = cmp_weight;
                    ret = Some(());
                }
            }

            self.priority_queue.replace(v.into());
        }
        ret
    }
}
