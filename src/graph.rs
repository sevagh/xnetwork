use slotmap::{DefaultKey, SecondaryMap, SlotMap, SparseSecondaryMap};
use crate::bfs::BFS;

#[derive(Debug)]
pub(crate) struct Edge {
    pub(crate) src: DefaultKey,
    pub(crate) dst: DefaultKey,
    pub(crate) w: Option<f64>,
}

#[derive(Debug)]
pub struct Graph<T: Copy, U> {
    pub(crate) nodes: SlotMap<DefaultKey, T>,
    pub(crate) node_infos: SecondaryMap<DefaultKey, U>,
    pub(crate) edges: SparseSecondaryMap<DefaultKey, Edge>,
    pub(crate) directed: bool,
}

impl<T: Copy, U> Graph<T, U> {
    fn new(directed: bool) -> Self {
        Graph {
            nodes: SlotMap::new(),
            node_infos: SecondaryMap::new(),
            edges: SparseSecondaryMap::new(),
            directed,
        }
    }

    pub fn new_directed() -> Self {
        Self::new(true)
    }

    pub fn new_undirected() -> Self {
        Self::new(false)
    }

    pub fn add_node(&mut self, new_node: T, extra_data: Option<U>) -> DefaultKey {
        let k = self.nodes.insert(new_node);
        if let Some(x) = extra_data {
            self.node_infos.insert(k, x);
        }
        k
    }

    pub fn add_edge(&mut self, src: DefaultKey, dst: DefaultKey, weight: Option<f64>) {
        if self.directed {
            self.edges.insert(src, Edge { src: src, dst: dst, w: weight });
        } else {
            self.edges.insert(src, Edge { src: src, dst: dst, w: weight });
            self.edges.insert(dst, Edge { src: src, dst: dst, w: weight });
        }
    }

    pub fn bfs<'a>(&'a self) -> BFS<'a, T, U> {
        BFS::for_graph(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::size_of_val;

    #[test]
    fn basic_add_node_eges() {
        let mut g = Graph::<i32, &str>::new_undirected();

        let tristram = g.add_node(0, Some("Tristram"));
        let alpha_centauri = g.add_node(1, Some("AlphaCentauri"));
        let _saturn = g.add_node(2, Some("Saturn"));

        g.add_edge(tristram, alpha_centauri, None);

        //println!("g is {:#?}", g);
        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn overwrite_node() {
        let mut g = Graph::<i32, &str>::new_undirected();

        let tristram = g.add_node(0, Some("Tristram"));
        let alpha_centauri = g.add_node(1, Some("AlphaCentauri"));
        let saturn = g.add_node(1, Some("Saturn"));

        g.add_edge(tristram, alpha_centauri, None);

        // this can't make sense since saturn took alpha_centauri's place
        g.add_edge(saturn, alpha_centauri, None);

        //println!("g is {:#?}", g);
        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn node_overhead_single_node() {
        let mut g = Graph::<i32, &str>::new_undirected();

        let _tristram = g.add_node(0, Some("Tristram"));

        struct GraphNodeNoGraph<'a> {
            _k: i32,
            _v: &'a str,
        };

        let gnog = GraphNodeNoGraph{
            _k: 0,
            _v: "Tristram",
        };

        println!("mem of node outside graph: {:#?}", size_of_val(&gnog));
        println!("mem of graph with node: {:#?}", size_of_val(&g));

        //println!("g is {:#?}", g);
        assert_eq!(2 + 2, 4);
    }
}
