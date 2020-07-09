use crate::{
    bfs::BFS,
    dfs::{DFS, NULL_KEY},
    weighted::Prim,
};
use slotmap::{DefaultKey, SecondaryMap, SlotMap, SparseSecondaryMap};
use std::{cmp::Ord, fmt::Debug};

#[derive(Debug, Clone)]
pub(crate) struct Edge {
    pub(crate) dst: DefaultKey,
    pub(crate) w: Option<i32>,
}

#[derive(Debug)]
pub struct Graph<T: Copy + Debug + Ord, U: Debug> {
    pub(crate) nodes: SlotMap<DefaultKey, T>,
    pub(crate) node_infos: SecondaryMap<DefaultKey, U>,
    pub(crate) edges: SparseSecondaryMap<DefaultKey, Vec<Edge>>,
    pub(crate) outdegrees: SparseSecondaryMap<DefaultKey, usize>,
    pub(crate) indegrees: SparseSecondaryMap<DefaultKey, usize>,
    pub(crate) directed: bool,
}

pub fn find_path(src: DefaultKey, dst: DefaultKey, parents: &SecondaryMap<DefaultKey, DefaultKey>) {
    if src == dst || dst == *NULL_KEY {
        println!("start: {:?}", src);
    } else {
        find_path(src, *(parents.get(dst).unwrap()), parents);
        println!(" end: {:?}", dst);
    }
}

impl<T: Copy + Debug + Ord, U: Debug> Graph<T, U> {
    fn new(directed: bool) -> Self {
        Graph {
            nodes: SlotMap::new(),
            node_infos: SecondaryMap::new(),
            edges: SparseSecondaryMap::new(),
            outdegrees: SparseSecondaryMap::new(),
            indegrees: SparseSecondaryMap::new(),
            directed,
        }
    }

    pub fn n_edges(&self) -> usize {
        let mut ret: usize = 0;
        for deg in self.outdegrees.values() {
            ret += deg;
        }
        ret
    }

    pub fn n_nodes(&self) -> usize {
        self.nodes.len()
    }

    pub fn n_nodes_mut(&mut self) -> usize {
        self.nodes.len()
    }

    pub fn outdegree(&self, node: DefaultKey) -> usize {
        if let Some(deg) = self.outdegrees.get(node) {
            return *deg;
        }
        0
    }

    pub fn indegree(&self, node: DefaultKey) -> usize {
        if let Some(deg) = self.indegrees.get(node) {
            return *deg;
        }
        0
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

    pub fn add_edge(&mut self, src: DefaultKey, dst: DefaultKey, weight: Option<i32>) {
        let new_edge = Edge { dst, w: weight };

        if let Some(x) = self.outdegrees.get_mut(src) {
            *x += 1;
        } else {
            self.outdegrees.insert(src, 1);
        }

        if let Some(x) = self.indegrees.get_mut(dst) {
            *x += 1;
        } else {
            self.indegrees.insert(dst, 1);
        }

        match self.edges.get_mut(src) {
            Some(edge_list) => {
                edge_list.push(new_edge);
            }
            None => {
                self.edges.insert(src, vec![new_edge]);
            }
        }

        if !self.directed {
            let reverse = Edge {
                dst: src,
                w: weight,
            };

            match self.edges.get_mut(dst) {
                Some(edge_list) => {
                    edge_list.push(reverse);
                }
                None => {
                    self.edges.insert(dst, vec![reverse]);
                }
            }
        }
    }

    pub fn print_info(&self, n: DefaultKey) {
        println!(
            "key: {:?}, value: {:?}",
            self.nodes.get(n),
            self.node_infos.get(n)
        );
    }

    pub fn get_node_info(&self, n: DefaultKey) -> Option<&U> {
        self.node_infos.get(n)
    }

    pub fn bfs(&self) -> BFS<T, U> {
        BFS::for_graph(self)
    }

    pub fn dfs(&self) -> DFS<T, U> {
        DFS::for_graph(self)
    }

    pub fn topological_sort(&self) -> DFS<T, U> {
        DFS::for_graph_topo(self)
    }

    pub fn lexicographical_topological_sort(&self) -> DFS<T, U> {
        DFS::for_graph_lexi_topo(self)
    }

    pub fn mst_prim(&self) -> Prim<T, U> {
        Prim::for_graph(self)
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

        let gnog = GraphNodeNoGraph {
            _k: 0,
            _v: "Tristram",
        };

        println!("mem of node outside graph: {:#?}", size_of_val(&gnog));
        println!("mem of graph with node: {:#?}", size_of_val(&g));

        //println!("g is {:#?}", g);
        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn test_outdegree_nnodes_nedges() {
        let mut g = Graph::<i32, &str>::new_undirected();

        let a = g.add_node(0, Some("a"));
        let b = g.add_node(1, Some("b"));
        let c = g.add_node(2, Some("c"));
        let d = g.add_node(3, Some("d"));

        g.add_edge(a, b, None);
        g.add_edge(a, c, None);
        g.add_edge(a, d, None);
        g.add_edge(d, c, None);

        assert_eq!(g.outdegree(a), 3);
        assert_eq!(g.outdegree(d), 1);
        assert_eq!(g.outdegree(b), 0);
        assert_eq!(g.outdegree(c), 0);

        assert_eq!(g.n_nodes(), 4);
        assert_eq!(g.n_edges(), 4);
    }
}
