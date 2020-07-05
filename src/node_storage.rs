use std::{cmp::{Ord, Ordering}, collections::{BinaryHeap, VecDeque}, error, fmt, fmt::Debug, result};
use slotmap::{DefaultKey, SecondaryMap};
use crate::graph::Graph;

#[derive(Debug, PartialEq, Copy, Clone)]
pub(crate) enum StorageKind {
    BFSQueue,
    DFSStack,
    LexicographicalTopologicalBinaryHeap,
}

#[derive(Debug)]
pub(crate) struct NodeStorage<'a, T: Copy + Debug + Ord, U: Debug> {
    kind: StorageKind,
    graph: &'a Graph<T, U>,
    queue: Option<VecDeque<DefaultKey>>,
    stack: Option<Vec<DefaultKey>>,
    heap: Option<BinaryHeap<DefaultKey>>,
}

impl<'a, T: Copy + Debug + Ord, U: Debug> NodeStorage<'a, T, U> {
    pub(crate) fn new(g: &'a Graph<T, U>, kind: StorageKind) -> Self {
        let mut ret = NodeStorage{
            kind: kind,
            graph: g,
            queue: None,
            stack: None,
            heap: None,
        };
        match kind {
            StorageKind::BFSQueue => {
                ret.queue = Some(VecDeque::new());
            },
            StorageKind::DFSStack => {
                ret.stack = Some(Vec::new());
            },
            StorageKind::LexicographicalTopologicalBinaryHeap => {
                ret.heap = Some(BinaryHeap::new());
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
            },
            StorageKind::DFSStack => {
                if let Some(ref mut storage) = self.stack {
                    (*storage).push(elem);
                }
            },
            StorageKind::LexicographicalTopologicalBinaryHeap => {
                if let Some(ref mut storage) = self.heap {
                    (*storage).push(elem);
                }
            }
        }
    }

    pub(crate) fn pop(&mut self) -> Option<DefaultKey> {
        return match self.kind {
            StorageKind::BFSQueue => {
                if let Some(ref mut storage) = self.queue {
                    (*storage).pop_front()
                } else {
                    None
                }
            },
            StorageKind::DFSStack => {
                if let Some(ref mut storage) = self.stack {
                    (*storage).pop()
                } else {
                    None
                }
            },
            StorageKind::LexicographicalTopologicalBinaryHeap => {
                if let Some(ref mut storage) = self.stack {
                    (*storage).pop()
                } else {
                    None
                }
            }
        }
    }

    pub(crate) fn is_empty(&self) -> Option<bool> {
        return match self.kind {
            StorageKind::BFSQueue => {
                if let Some(ref storage) = self.queue {
                    Some((*storage).is_empty())
                } else {
                    None
                }
            },
            StorageKind::DFSStack => {
                if let Some(ref storage) = self.stack {
                    Some((*storage).is_empty())
                } else {
                    None
                }
            },
            StorageKind::LexicographicalTopologicalBinaryHeap => {
                if let Some(ref storage) = self.heap {
                    Some((*storage).is_empty())
                } else {
                    None
                }
            }
        }
    }
}
