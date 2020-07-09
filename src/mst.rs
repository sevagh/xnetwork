use crate::{
    graph::Graph,
    node_storage::{NodeStorage, StorageKind},
};
use partitions::PartitionVec;
use slotmap::{DefaultKey, SecondaryMap};
use std::{
    cmp::{Ord, Ordering, PartialOrd},
    collections::{BinaryHeap, HashMap},
    error, fmt,
    fmt::Debug,
    result,
};
use unordered_pair::UnorderedPair;

pub type MinimumSpanningTreeResult<T> = result::Result<T, MinimumSpanningTreeError>;

#[derive(Debug)]
pub struct MinimumSpanningTreeError;

impl fmt::Display for MinimumSpanningTreeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "not a dag")
    }
}

impl error::Error for MinimumSpanningTreeError {
    fn description(&self) -> &str {
        "not a dag"
    }

    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

#[derive(Debug)]
pub struct Prim<'a, T: Copy + Debug + Ord, U: Debug> {
    graph: &'a Graph<T, U>,
    to_yield: Vec<EdgeMST>,
    distance: NodeStorage<'a, T, U>,
    intree: SecondaryMap<DefaultKey, bool>,
    parent: SecondaryMap<DefaultKey, DefaultKey>,
}

impl<'a, T: Copy + Debug + Ord, U: Debug> Prim<'a, T, U> {
    pub(crate) fn for_graph(g: &'a Graph<T, U>) -> Self {
        let mut prim = Prim {
            graph: g,
            to_yield: vec![],
            intree: SecondaryMap::with_capacity(g.nodes.len()),
            parent: SecondaryMap::with_capacity(g.nodes.len()),
            distance: NodeStorage::new(g, StorageKind::PrimWeightPriority),
        };
        prim.init();
        prim
    }

    fn init(&mut self) {
        for k in self.graph.nodes.keys() {
            self.intree.insert(k, false);
            self.distance.push_weight(k, i32::MAX);
            self.parent.insert(k, DefaultKey::default());
        }
    }

    pub fn do_prim(&mut self, start: DefaultKey) {
        let mut node: DefaultKey = start;

        while !self.intree.get(node).unwrap() {
            self.intree.insert(node, true);

            if let Some(edge_list) = self.graph.edges.get(node) {
                for edge in edge_list.iter() {
                    if !self.intree.get(edge.dst).unwrap()
                        && self
                            .distance
                            .reduce_weight_to(edge.dst, edge.w.unwrap())
                            .is_some()
                    {
                        self.parent.insert(edge.dst, node);
                    }
                }
            }

            // pop the next lowest entry from the priority queue
            // stuff them in to_yield for the iterator
            if let Some((k, dist)) = self.distance.pop_with_weight() {
                if !self.intree.get(k).unwrap() {
                    node = k;
                    self.to_yield.push(EdgeMST {
                        nodes: UnorderedPair(*self.parent.get(k).unwrap(), k),
                        weight: dist,
                    });
                }
            }
        }

        self.to_yield.reverse();
    }
}

impl<'a, T: Copy + Debug + Ord, U: Debug> Iterator for Prim<'a, T, U> {
    type Item = EdgeMST;

    fn next(&mut self) -> Option<Self::Item> {
        self.to_yield.pop()
    }
}

#[derive(Debug, Copy, Clone)]
pub struct EdgeMST {
    nodes: UnorderedPair<DefaultKey>,
    weight: i32,
}

impl Ord for EdgeMST {
    fn cmp(&self, other: &Self) -> Ordering {
        other.weight.cmp(&self.weight)
    }
}

impl PartialEq for EdgeMST {
    fn eq(&self, other: &Self) -> bool {
        other.nodes.eq(&self.nodes)
    }
}

impl PartialOrd for EdgeMST {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Eq for EdgeMST {}

#[derive(Debug)]
pub struct Kruskal<'a, T: Copy + Debug + Ord, U: Debug> {
    graph: &'a Graph<T, U>,
    to_yield: Vec<EdgeMST>,
    set: PartitionVec<DefaultKey>,
    node_idx_map: HashMap<DefaultKey, usize>,
    edge_heap: BinaryHeap<EdgeMST>,
}

impl<'a, T: Copy + Debug + Ord, U: Debug> Kruskal<'a, T, U> {
    pub(crate) fn for_graph(g: &'a Graph<T, U>) -> Self {
        let mut krusk = Kruskal {
            graph: g,
            to_yield: vec![],
            set: PartitionVec::with_capacity(g.nodes.len()),
            edge_heap: BinaryHeap::with_capacity(g.edges.len()),
            node_idx_map: HashMap::with_capacity(g.nodes.len()),
        };
        krusk.init();
        krusk
    }

    fn init(&mut self) {
        for (i, k) in self.graph.nodes.keys().enumerate() {
            self.set.push(k);
            self.node_idx_map.insert(k, i);

            for e in self.graph.edges.get(k).unwrap() {
                self.edge_heap.push(EdgeMST {
                    nodes: UnorderedPair(k, e.dst),
                    weight: e.w.unwrap_or(i32::MAX),
                })
            }
        }
    }

    pub fn do_kruskal(&mut self) {
        let mut idx1: usize;
        let mut idx2: usize;

        while !self.edge_heap.is_empty() {
            if let Some(next_cheapest_edge) = self.edge_heap.pop() {
                idx1 = *self.node_idx_map.get(&next_cheapest_edge.nodes.0).unwrap();
                idx2 = *self.node_idx_map.get(&next_cheapest_edge.nodes.1).unwrap();

                if !self.set.same_set(idx1, idx2) {
                    self.to_yield.push(next_cheapest_edge);
                    self.set.union(idx1, idx2);
                }
            }
        }
        self.to_yield.reverse();
    }
}

impl<'a, T: Copy + Debug + Ord, U: Debug> Iterator for Kruskal<'a, T, U> {
    type Item = EdgeMST;

    fn next(&mut self) -> Option<Self::Item> {
        self.to_yield.pop()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_prim_mst() {
        let mut g = Graph::<i32, &str>::new_undirected();

        let a = g.add_node(0, Some("a"));
        let b = g.add_node(1, Some("b"));
        let c = g.add_node(2, Some("c"));
        let d = g.add_node(3, Some("d"));

        g.add_edge(a, b, Some(5));
        g.add_edge(b, c, Some(2));
        g.add_edge(b, d, Some(13));
        g.add_edge(c, d, Some(4));

        let mut prim = g.mst_prim().unwrap();
        prim.do_prim(a);

        //for visited_node in prim {
        //    println!("prim mst: {:#?}", visited_node);
        //}
        assert_eq!(
            prim.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(a, b),
                weight: 5,
            })
        );

        assert_eq!(
            prim.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(b, c),
                weight: 2,
            })
        );

        assert_eq!(
            prim.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(c, d),
                weight: 4,
            })
        );

        assert_eq!(prim.next(), None);
    }

    #[test]
    fn test_prim_mst() {
        /*
         * testcase from skiena, pp196 figure 6.3
         */

        let mut graph = Graph::<i32, &str>::new_undirected();

        let a = graph.add_node(0, Some("a"));
        let b = graph.add_node(1, Some("b"));
        let c = graph.add_node(2, Some("c"));
        let d = graph.add_node(3, Some("d"));
        let e = graph.add_node(4, Some("e"));
        let f = graph.add_node(5, Some("f"));
        let g = graph.add_node(6, Some("g"));

        graph.add_edge(a, b, Some(5));
        graph.add_edge(a, c, Some(7));
        graph.add_edge(a, d, Some(12));

        graph.add_edge(b, c, Some(9));

        graph.add_edge(b, e, Some(7));
        graph.add_edge(e, g, Some(2));
        graph.add_edge(e, c, Some(4));

        graph.add_edge(e, f, Some(5));
        graph.add_edge(f, g, Some(2));

        graph.add_edge(d, g, Some(7));
        graph.add_edge(d, c, Some(4));
        graph.add_edge(c, g, Some(3));

        let mut prim = graph.mst_prim().unwrap();
        prim.do_prim(a);

        //for visited_node in prim {
        //    println!("prim mst: {:?}", graph.print_info(visited_node));
        //}
        assert_eq!(
            prim.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(a, b),
                weight: 5,
            })
        );
        assert_eq!(
            prim.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(a, c),
                weight: 7,
            })
        );
        assert_eq!(
            prim.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(c, g),
                weight: 3,
            })
        );
        assert_eq!(
            prim.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(g, e),
                weight: 2,
            })
        );
        assert_eq!(
            prim.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(g, f),
                weight: 5,
            })
        );
        assert_eq!(
            prim.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(c, d),
                weight: 4,
            })
        );
        assert_eq!(prim.next(), None);
    }

    #[test]
    fn basic_kruskal_mst() {
        let mut g = Graph::<i32, &str>::new_undirected();

        let a = g.add_node(0, Some("a"));
        let b = g.add_node(1, Some("b"));
        let c = g.add_node(2, Some("c"));
        let d = g.add_node(3, Some("d"));

        g.add_edge(a, b, Some(5));
        g.add_edge(b, c, Some(2));
        g.add_edge(b, d, Some(13));
        g.add_edge(c, d, Some(4));

        let mut kruskal = g.mst_kruskal().unwrap();
        kruskal.do_kruskal();

        //for visited_node in kruskal {
        //    println!("kruskal mst: {:#?}", visited_node);
        //}
        assert_eq!(
            kruskal.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(c, b),
                weight: 2,
            })
        );
        assert_eq!(
            kruskal.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(c, d),
                weight: 4,
            })
        );
        assert_eq!(
            kruskal.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(b, a),
                weight: 5,
            })
        );
        assert_eq!(kruskal.next(), None);
    }

    #[test]
    fn test_kruskal_mst() {
        /*
         * testcase from skiena, pp196 figure 6.3
         */

        let mut graph = Graph::<i32, &str>::new_undirected();

        let a = graph.add_node(0, Some("a"));
        let b = graph.add_node(1, Some("b"));
        let c = graph.add_node(2, Some("c"));
        let d = graph.add_node(3, Some("d"));
        let e = graph.add_node(4, Some("e"));
        let f = graph.add_node(5, Some("f"));
        let g = graph.add_node(6, Some("g"));

        graph.add_edge(a, b, Some(5));
        graph.add_edge(a, c, Some(7));
        graph.add_edge(a, d, Some(12));

        graph.add_edge(b, c, Some(9));

        graph.add_edge(b, e, Some(7));
        graph.add_edge(e, g, Some(2));
        graph.add_edge(e, c, Some(4));

        graph.add_edge(e, f, Some(5));
        graph.add_edge(f, g, Some(2));

        graph.add_edge(d, g, Some(7));
        graph.add_edge(d, c, Some(4));
        graph.add_edge(c, g, Some(3));

        let mut kruskal = graph.mst_kruskal().unwrap();
        kruskal.do_kruskal();

        //for edge in kruskal {
        //    println!("kruskal mst: {:?}", edge);
        //}

        assert_eq!(
            kruskal.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(e, g),
                weight: 2,
            })
        );
        assert_eq!(
            kruskal.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(f, g),
                weight: 2,
            })
        );
        assert_eq!(
            kruskal.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(g, c),
                weight: 3,
            })
        );
        assert_eq!(
            kruskal.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(d, c),
                weight: 4,
            })
        );
        assert_eq!(
            kruskal.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(a, b),
                weight: 5,
            })
        );
        assert_eq!(
            kruskal.next(),
            Some(EdgeMST {
                nodes: UnorderedPair(b, e),
                weight: 7,
            })
        );
        assert_eq!(kruskal.next(), None);
    }
}
