use crate::graph::Graph;
use slotmap::DefaultKey;
use std::{
    cmp::{Ord, Ordering, PartialOrd},
    collections::{BinaryHeap, VecDeque},
    fmt::Debug,
    thread, time,
};

const TENS: time::Duration = time::Duration::from_secs(10);

#[derive(Debug, PartialEq, Copy, Clone)]
pub(crate) enum StorageKind {
    BFSQueue,
    DFSStack,
    LexicographicalHeap,
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub(crate) struct HeapEntry<T: Copy + Debug + Ord> {
    slotmap_key: DefaultKey,
    node_value: T,
    indegree: i32,
}

impl<T: Copy + Debug + Ord> Ord for HeapEntry<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.indegree
            .cmp(&other.indegree)
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
}

impl<'a, T: Copy + Debug + Ord, U: Debug> NodeStorage<'a, T, U> {
    pub(crate) fn new(g: &'a Graph<T, U>, kind: StorageKind) -> Self {
        let mut ret = NodeStorage {
            kind,
            graph: g,
            queue: None,
            stack: None,
            heap: None,
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
                        indegree: *self.graph.indegrees.get(elem).unwrap_or(&0usize) as i32,
                    });
                    //*storage.dedup();
                }
            }
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
                    (*storage).pop().map(|x| {
                        println!("storage: {:#?}", storage);
                        thread::sleep(tens);
                        x.slotmap_key
                    })
                } else {
                    None
                }
            }
        }
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
        }
    }

    pub(crate) fn reduce_indegree(&mut self, dst: DefaultKey) {
        if let StorageKind::LexicographicalHeap = self.kind {
            let mut v = self.heap.take().unwrap().into_vec();

            for mut e in v.iter_mut() {
                if e.slotmap_key == dst {
                    e.indegree -= 1;
                }
            }

            self.heap.replace(v.into());
        }
    }
}
