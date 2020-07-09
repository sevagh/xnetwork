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
                        self.to_yield.push(edge.dst);
                    }
                }
            }

            // pop the next lowest entry from the priority queue
            if let Some((k, dist)) = self.distance.pop_with_weight() {
                if !self.intree.get(k).unwrap() {
                    node = k;
                    println!("popped {:?} with distance {} for next iter", k, dist);
                }
            }
        }

        for (k, v) in self.parent.iter() {
            println!("k: {:?}, v: {:?}", k, v);
        }
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

        g.add_edge(a, b, Some(5));
        g.add_edge(b, c, Some(2));

        let mut prim = g.mst_prim();
        prim.do_prim(a);

        for visited_node in prim {
            println!("prim mst: {:#?}", visited_node);
        }

        assert_eq!(2 + 2, 4);
    }
}
