use std::{cmp::{Ord, Ordering}, collections::{VecDeque}, error, fmt, fmt::Debug, result};
use slotmap::{DefaultKey, SecondaryMap};
use crate::graph::Graph;

#[derive(Debug, PartialEq, Copy, Clone)]
pub(crate) enum StorageKind {
    BFSQueue,
    DFSStack,
    LexicographicalStack,
}

#[derive(Debug)]
pub(crate) struct NodeStorage<'a, T: Copy + Debug + Ord, U: Debug> {
    kind: StorageKind,
    graph: &'a Graph<T, U>,
    queue: Option<VecDeque<DefaultKey>>,
    stack: Option<Vec<DefaultKey>>,
    pub(crate) heap: Option<Vec<DefaultKey>>,
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
            StorageKind::LexicographicalStack => {
                ret.heap = Some(Vec::new());
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
            StorageKind::LexicographicalStack => {
                if let Some(ref mut storage) = self.heap {
                    (*storage).push(elem);
                }

                // simulate a binary heap without having to
                // use std::collections::BinaryHeap
                // by sorting after insertion
                //
                // sorting by the lexicographical value
                // of the node tag, since the DefaultKey
                // is auto-assigned by slotmap
                // and is meaningless

                let mut storage_copy = self.heap.as_ref().unwrap().clone();

                storage_copy.sort_by_key(|elem| {
                    self.graph.nodes.get(*elem).unwrap()
                });
                storage_copy.reverse();

                self.heap = Some(storage_copy);
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
            StorageKind::LexicographicalStack => {
                if let Some(ref mut storage) = self.heap {
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
            StorageKind::LexicographicalStack => {
                if let Some(ref storage) = self.heap {
                    Some((*storage).is_empty())
                } else {
                    None
                }
            }
        }
    }
}
