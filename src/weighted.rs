use crate::{
    graph::Graph,
    node_storage::{NodeStorage, StorageKind},
};
use slotmap::{DefaultKey, SecondaryMap};
use std::fmt::Debug;

#[derive(Debug)]
pub struct Prim<'a, T: Copy + Debug + Ord, U: Debug> {
    graph: &'a Graph<T, U>,
    to_yield: Vec<DefaultKey>,
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

        self.to_yield.push(node);

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
            if let Some((k, _dist)) = self.distance.pop_with_weight() {
                if !self.intree.get(k).unwrap() {
                    node = k;
                    self.to_yield.push(k);
                }
            }
        }

        self.to_yield.reverse();
    }
}

impl<'a, T: Copy + Debug + Ord, U: Debug> Iterator for Prim<'a, T, U> {
    type Item = DefaultKey;

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

        let mut prim = g.mst_prim();
        prim.do_prim(a);

        //for visited_node in prim {
        //    println!("prim mst: {:#?}", visited_node);
        //}
        assert_eq!(prim.next(), Some(a));
        assert_eq!(prim.next(), Some(b));
        assert_eq!(prim.next(), Some(c));
        assert_eq!(prim.next(), Some(d));
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

        let mut prim = graph.mst_prim();
        prim.do_prim(a);

        //for visited_node in prim {
        //    println!("prim mst: {:?}", graph.print_info(visited_node));
        //}
        assert_eq!(prim.next(), Some(a));
        assert_eq!(prim.next(), Some(b));
        assert_eq!(prim.next(), Some(c));
        assert_eq!(prim.next(), Some(g));
        assert_eq!(prim.next(), Some(e));
        assert_eq!(prim.next(), Some(f));
        assert_eq!(prim.next(), Some(d));
        assert_eq!(prim.next(), None);
    }
}
