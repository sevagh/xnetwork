use crate::{
    graph::Graph,
    node_storage::{NodeStorage, StorageKind},
};
use linked_hash_set::LinkedHashSet;
use slotmap::{DefaultKey, SecondaryMap};
use std::{cmp::Ord, error, fmt, fmt::Debug, result};

lazy_static! {
    pub(crate) static ref NULL_KEY: DefaultKey = DefaultKey::default();
}

type TopologicalSortResult<T> = result::Result<T, TopologicalSortError>;

#[derive(Debug)]
pub struct TopologicalSortError;

impl fmt::Display for TopologicalSortError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "not a dag")
    }
}

impl error::Error for TopologicalSortError {
    fn description(&self) -> &str {
        "not a dag"
    }

    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

#[derive(Debug)]
pub struct DFS<'a, T: Copy + Debug + Ord, U: Debug> {
    graph: &'a Graph<T, U>,

    processed: SecondaryMap<DefaultKey, bool>,
    discovered: SecondaryMap<DefaultKey, bool>,
    parent: SecondaryMap<DefaultKey, DefaultKey>,
    entry_time: SecondaryMap<DefaultKey, usize>,
    exit_time: SecondaryMap<DefaultKey, usize>,

    to_yield: Vec<DefaultKey>,
    storage_kind: StorageKind,
    n_edges: usize,
    time: usize,
    finished: bool,
    topological: bool,
    lexicographical: bool,
}

impl<'a, T: Copy + Debug + Ord, U: Debug> DFS<'a, T, U> {
    pub(crate) fn for_graph(g: &'a Graph<T, U>) -> Self {
        let mut dfs = DFS {
            graph: g,
            processed: SecondaryMap::with_capacity(g.nodes.len()),
            discovered: SecondaryMap::with_capacity(g.nodes.len()),
            parent: SecondaryMap::with_capacity(g.nodes.len()),
            entry_time: SecondaryMap::with_capacity(g.nodes.len()),
            exit_time: SecondaryMap::with_capacity(g.nodes.len()),
            to_yield: Vec::with_capacity(g.nodes.len()),
            storage_kind: StorageKind::DFSStack,
            n_edges: 0,
            time: 0,
            finished: false,
            topological: false,
            lexicographical: false,
        };
        dfs.init();
        dfs
    }

    pub(crate) fn for_graph_topo(g: &'a Graph<T, U>) -> Self {
        let mut dfs = DFS::for_graph(g);
        dfs.topological = true;
        dfs
    }

    pub(crate) fn for_graph_lexi_topo(g: &'a Graph<T, U>) -> Self {
        let mut dfs = DFS::for_graph(g);
        dfs.topological = true;
        dfs.lexicographical = true;
        dfs.storage_kind = StorageKind::LexicographicalHeap;
        dfs
    }

    pub fn get_n_edges(&self) -> usize {
        self.n_edges
    }

    fn init(&mut self) {
        for k in self.graph.nodes.keys() {
            self.processed.insert(k, false);
            self.discovered.insert(k, false);
            self.parent.insert(k, *NULL_KEY);
        }
    }

    pub fn do_topological_sort(&mut self) -> TopologicalSortResult<()> {
        if !self.graph.directed {
            return Err(TopologicalSortError);
        }
        self.topological = true;

        let mut starting_node: Option<DefaultKey> = None;
        for k in self.graph.nodes.keys() {
            if self.graph.indegree(k) == 0 {
                starting_node = Some(k);
                break;
            }
        }

        if starting_node.is_none() {
            return Err(TopologicalSortError);
        }

        if self.do_dfs_priv(&[starting_node.unwrap()]).is_err() {
            return Err(TopologicalSortError);
        }

        for k in self.graph.nodes.keys() {
            if !self.discovered.get(k).unwrap() && self.do_dfs_priv(&[k]).is_err() {
                return Err(TopologicalSortError);
            }
        }

        Ok(())
    }

    pub fn do_lexicographical_topological_sort(&mut self) -> TopologicalSortResult<()> {
        if !self.graph.directed {
            return Err(TopologicalSortError);
        }

        self.topological = true;
        self.lexicographical = true;

        let mut starting_nodes: Vec<DefaultKey> = vec![];
        for k in self.graph.nodes.keys() {
            if self.graph.indegree(k) == 0 {
                starting_nodes.push(k);
            }
        }
        starting_nodes.sort_by_key(|k| self.graph.nodes.get(*k).unwrap());

        if self.do_dfs_priv(&starting_nodes).is_err() {
            return Err(TopologicalSortError);
        }

        Ok(())
    }

    pub fn do_dfs(&mut self, node: DefaultKey) -> TopologicalSortResult<()> {
        let ret = self.do_dfs_priv(&[node]);
        self.to_yield.reverse();
        ret
    }

    fn do_dfs_priv(&mut self, start: &[DefaultKey]) -> TopologicalSortResult<()> {
        let mut stack1 = NodeStorage::new(self.graph, self.storage_kind);
        let mut stack2 = LinkedHashSet::with_capacity(self.graph.nodes.len());

        if self.finished {
            return Ok(());
        }

        let mut node: DefaultKey;

        for st in start {
            stack1.push(*st);
        }

        'outer: while !stack1.is_empty().unwrap() {
            node = stack1.pop().unwrap();

            self.discovered.insert(node, true);
            self.time += 1;
            self.entry_time.insert(node, self.time);

            self.process_node_early(node);

            if let Some(edge_list) = self.graph.edges.get(node) {
                // accumulate all possible nodes in stack1
                // which will do a lexicographical sort on insertion
                if !edge_list.is_empty() {
                    stack2.insert_if_absent(node);

                    for edge in edge_list.iter() {
                        if !self.discovered.get(edge.dst).unwrap() {
                            self.parent.insert(edge.dst, node);

                            self.process_edge();

                            stack1.push(edge.dst);
                            stack1.reduce_indegree(edge.dst);
                        } else if (!self.processed.get(edge.dst).unwrap()
                            && *(self.parent.get(node).unwrap()) != edge.dst)
                            || self.graph.directed
                        {
                            self.process_edge();

                            // reduce the indegree of a node
                            // after processing an edge
                            // it should let nodes bubble to the top
                            // when their prerequisites are unlocked
                            stack1.reduce_indegree(edge.dst);
                        }
                        if self.finished {
                            return Ok(());
                        }
                    }
                    continue 'outer;
                }
            }

            self.process_node_late(node);
            self.time += 1;
            self.exit_time.insert(node, self.time);
            self.processed.insert(node, true);
        }

        while !stack2.is_empty() {
            node = stack2.pop_back().unwrap();

            if *self.processed.get(node).unwrap() {
                continue;
            }

            self.process_node_late(node);
            self.time += 1;
            self.exit_time.insert(node, self.time);
            self.processed.insert(node, true);
        }

        self.to_yield.dedup();
        Ok(())
    }

    fn process_node_early(&mut self, node: DefaultKey) {
        if !self.topological {
            self.to_yield.push(node);
        }
    }

    fn process_node_late(&mut self, node: DefaultKey) {
        if self.topological {
            self.to_yield.push(node);
        }
    }

    fn process_edge(&mut self) {
        self.n_edges += 1;
    }
}

impl<'a, T: Copy + Debug + Ord, U: Debug> Iterator for DFS<'a, T, U> {
    type Item = DefaultKey;

    fn next(&mut self) -> Option<Self::Item> {
        self.to_yield.pop()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_dfs() {
        let mut g = Graph::<i32, &str>::new_undirected();

        let tristram = g.add_node(0, Some("Tristram"));
        let alpha_centauri = g.add_node(1, Some("AlphaCentauri"));
        let _saturn = g.add_node(2, Some("Saturn"));

        g.add_edge(tristram, alpha_centauri, None);

        let mut dfs = g.dfs();
        dfs.do_dfs(tristram).unwrap();

        for visited_node in dfs {
            println!("dfs visited node: {:#?}", visited_node);
        }

        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn real_dfs() {
        let mut g = Graph::<i32, &str>::new_undirected();

        let a = g.add_node(0, Some("a"));
        let b = g.add_node(1, Some("b"));
        let c = g.add_node(2, Some("c"));

        g.add_edge(a, c, None);
        g.add_edge(c, b, None);

        let mut dfs = g.dfs();
        dfs.do_dfs(a).unwrap();

        for visited_node in dfs {
            println!("dfs visited node: {:#?}", visited_node);
            g.print_info(visited_node);
        }
    }

    #[test]
    fn real_dfs_asserts() {
        let mut g = Graph::<i32, &str>::new_undirected();

        let a = g.add_node(0, Some("a"));
        let b = g.add_node(1, Some("b"));
        let c = g.add_node(2, Some("c"));

        g.add_edge(a, c, None);
        g.add_edge(c, b, None);

        let mut dfs = g.dfs();
        dfs.do_dfs(a).unwrap();

        assert_eq!(dfs.next(), Some(a));
        assert_eq!(dfs.next(), Some(c));
        assert_eq!(dfs.next(), Some(b));
        assert_eq!(dfs.next(), None);
    }

    #[test]
    fn real_dfs_2asserts() {
        let mut g = Graph::<i32, &str>::new_undirected();

        let a = g.add_node(0, Some("a"));
        let b = g.add_node(1, Some("b"));
        let c = g.add_node(2, Some("c"));
        let d = g.add_node(3, Some("d"));
        let e = g.add_node(4, Some("e"));
        let f = g.add_node(5, Some("f"));

        g.add_edge(a, b, None);
        g.add_edge(b, c, None);
        g.add_edge(b, d, None);
        g.add_edge(b, e, None);
        g.add_edge(b, f, None);
        g.add_edge(c, a, None);
        g.add_edge(d, c, None);

        println!("dfs from node 'b'");

        let mut dfs_from_b = g.dfs();

        // kick off the dfs with the starting node
        dfs_from_b.do_dfs(b).unwrap();

        for next in dfs_from_b {
            g.print_info(next);
        }

        println!("dfs from node 'f'");

        let mut dfs_from_f = g.dfs();

        // kick off the dfs with the starting node
        dfs_from_f.do_dfs(f).unwrap();

        for next in dfs_from_f {
            g.print_info(next);
        }
        //assert_eq!(dfs.next(), Some(b));
        //assert_eq!(dfs.next(), Some(c));
        //assert_eq!(dfs.next(), Some(d));
        //assert_eq!(dfs.next(), Some(a));
        //assert_eq!(dfs.next(), Some(e));
        //assert_eq!(dfs.next(), Some(f));
        //assert_eq!(dfs.next(), None);
    }

    #[test]
    fn dfs_avoid_cycles() {
        let mut g1 = Graph::<i32, &str>::new_undirected();

        let a1 = g1.add_node(0, Some("a"));
        let b1 = g1.add_node(1, Some("b"));
        let c1 = g1.add_node(2, Some("c"));

        g1.add_edge(a1, b1, None);
        g1.add_edge(b1, c1, None);
        g1.add_edge(c1, a1, None);

        let mut dfs1 = g1.dfs();
        dfs1.do_dfs(a1).unwrap();

        assert_eq!(dfs1.next(), Some(a1));
        assert_eq!(dfs1.next(), Some(c1));
        assert_eq!(dfs1.next(), Some(b1));
        assert_eq!(dfs1.next(), None);
        //assert_eq!(dfs1.n_edges, g1.n_edges());
        println!(
            "graph edges 1: {}, dfs n_edges: {}",
            g1.n_edges(),
            dfs1.n_edges
        );

        println!("\n\n");

        let mut g2 = Graph::<i32, &str>::new_undirected();

        let a2 = g2.add_node(0, Some("a"));
        let b2 = g2.add_node(2, Some("b"));
        let c2 = g2.add_node(3, Some("c"));
        let d2 = g2.add_node(4, Some("d"));

        g2.add_edge(a2, b2, None);
        g2.add_edge(b2, c2, None);
        g2.add_edge(c2, a2, None);
        g2.add_edge(a2, d2, None);

        let mut dfs = g2.dfs();
        dfs.do_dfs(a2).unwrap();

        assert_eq!(dfs.next(), Some(a2));
        assert_eq!(dfs.next(), Some(d2));
        assert_eq!(dfs.next(), Some(c2));
        assert_eq!(dfs.next(), Some(b2));
        assert_eq!(dfs.next(), None);
        //assert_eq!(dfs.n_edges, g2.n_edges());
        println!(
            "graph edges 2: {}, dfs n_edges: {}",
            g2.n_edges(),
            dfs.n_edges
        );
    }

    #[test]
    fn wont_topological_sort_undirected() {
        let g = Graph::<i32, &str>::new_undirected();
        let mut dfs = g.topological_sort();
        assert!(dfs.do_topological_sort().is_err());
    }

    #[test]
    fn basic_topological_sort() {
        let mut g = Graph::<i32, &str>::new_directed();

        let tristram = g.add_node(0, Some("Tristram"));
        let alpha_centauri = g.add_node(1, Some("AlphaCentauri"));
        let _saturn = g.add_node(2, Some("Saturn"));

        g.add_edge(tristram, alpha_centauri, None);

        let mut dfs = g.topological_sort();
        dfs.do_topological_sort().unwrap();

        for visited_node in dfs {
            println!("topological_sort visited node: {:#?}", visited_node);
        }

        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn real_topological_sort() {
        // testcase from pp179 of skiena (figure 5.15)
        let mut gr = Graph::<i32, &str>::new_directed();

        let a = gr.add_node(0, Some("a"));
        let b = gr.add_node(1, Some("b"));
        let c = gr.add_node(2, Some("c"));
        let d = gr.add_node(3, Some("d"));
        let e = gr.add_node(4, Some("e"));
        let f = gr.add_node(5, Some("f"));
        let g = gr.add_node(6, Some("g"));

        gr.add_edge(g, a, None);
        gr.add_edge(a, b, None);
        gr.add_edge(a, c, None);
        gr.add_edge(b, d, None);
        gr.add_edge(b, c, None);
        gr.add_edge(c, e, None);
        gr.add_edge(c, f, None);
        gr.add_edge(e, d, None);
        gr.add_edge(f, e, None);

        let mut dfs = gr.topological_sort();
        dfs.do_topological_sort().unwrap();

        for d in dfs {
            gr.print_info(d);
        }

        //assert_eq!(dfs.next(), Some(g));
        //assert_eq!(dfs.next(), Some(a));
        //assert_eq!(dfs.next(), Some(b));
        //assert_eq!(dfs.next(), Some(c));
        //assert_eq!(dfs.next(), Some(f));
        //assert_eq!(dfs.next(), Some(e));
        //assert_eq!(dfs.next(), Some(d));
        //assert_eq!(dfs.next(), None);
    }

    #[test]
    fn topo_with_cycle() {
        let mut g1 = Graph::<i32, &str>::new_directed();

        let a1 = g1.add_node(0, Some("a"));
        let b1 = g1.add_node(1, Some("b"));
        let c1 = g1.add_node(2, Some("c"));

        g1.add_edge(a1, b1, None);
        g1.add_edge(b1, c1, None);
        g1.add_edge(c1, a1, None);

        let mut dfs1 = g1.topological_sort();
        assert!(dfs1.do_topological_sort().is_err());
    }

    #[test]
    fn test_lexico_1() {
        let mut g = Graph::new_directed();

        let a = g.add_node(0, Some("A"));
        let b = g.add_node(1, Some("B"));
        let c = g.add_node(2, Some("C"));
        let d = g.add_node(3, Some("D"));
        let e = g.add_node(4, Some("E"));
        let f = g.add_node(5, Some("F"));
        let h = g.add_node(7, Some("H"));
        let i = g.add_node(8, Some("I"));

        g.add_edge(c, a, None);
        g.add_edge(c, f, None);

        g.add_edge(a, b, None);
        g.add_edge(a, d, None);

        g.add_edge(d, e, None);
        g.add_edge(b, e, None);
        g.add_edge(f, e, None);

        g.add_edge(a, e, None);
        g.add_edge(i, e, None);
        g.add_edge(h, i, None);

        let mut sorted_order = g.lexicographical_topological_sort();
        sorted_order.do_lexicographical_topological_sort().unwrap();

        let lexicographical_traverse_order = sorted_order
            .map(|x| {
                if let Some(letter) = g.get_node_info(x) {
                    letter
                } else {
                    ""
                }
            })
            .collect::<Vec<&str>>()
            .join("");

        println!(
            "lexicographically topologically sorted order: {}",
            lexicographical_traverse_order
        );

        assert_eq!(lexicographical_traverse_order, "CABDFHIE");
    }

    #[test]
    fn test_lexico_2() {
        let mut g = Graph::new_directed();

        let a = g.add_node(0, Some("A"));
        let b = g.add_node(1, Some("B"));
        let c = g.add_node(2, Some("C"));
        let d = g.add_node(3, Some("D"));
        let e = g.add_node(4, Some("E"));
        let f = g.add_node(5, Some("F"));
        let g_node = g.add_node(6, Some("G"));
        let h = g.add_node(7, Some("H"));
        let i = g.add_node(8, Some("I"));
        let j = g.add_node(9, Some("J"));
        let k = g.add_node(10, Some("K"));
        let l = g.add_node(11, Some("L"));
        let m = g.add_node(12, Some("M"));
        let n = g.add_node(13, Some("N"));
        let o = g.add_node(14, Some("O"));
        let p = g.add_node(15, Some("P"));
        let q = g.add_node(16, Some("Q"));
        let r = g.add_node(17, Some("R"));
        let s = g.add_node(18, Some("S"));
        let t = g.add_node(19, Some("T"));
        let u = g.add_node(20, Some("U"));
        let v = g.add_node(21, Some("V"));
        let w = g.add_node(22, Some("W"));
        let x = g.add_node(23, Some("X"));
        let y = g.add_node(24, Some("Y"));
        let z = g.add_node(25, Some("Z"));

        g.add_edge(q, i, None);
        g.add_edge(b, m, None);
        g.add_edge(r, f, None);
        g.add_edge(g_node, s, None);
        g.add_edge(m, a, None);
        g.add_edge(z, w, None);
        g.add_edge(j, c, None);
        g.add_edge(k, o, None);
        g.add_edge(c, i, None);
        g.add_edge(y, l, None);
        g.add_edge(n, p, None);
        g.add_edge(s, x, None);
        g.add_edge(e, u, None);
        g.add_edge(u, v, None);
        g.add_edge(d, f, None);
        g.add_edge(w, h, None);
        g.add_edge(t, i, None);
        g.add_edge(h, v, None);
        g.add_edge(l, o, None);
        g.add_edge(p, a, None);
        g.add_edge(a, i, None);
        g.add_edge(f, o, None);
        g.add_edge(v, x, None);
        g.add_edge(i, o, None);
        g.add_edge(x, o, None);
        g.add_edge(f, v, None);
        g.add_edge(l, p, None);
        g.add_edge(y, p, None);
        g.add_edge(y, x, None);
        g.add_edge(y, o, None);
        g.add_edge(d, a, None);
        g.add_edge(t, f, None);
        g.add_edge(w, x, None);
        g.add_edge(r, a, None);
        g.add_edge(e, f, None);
        g.add_edge(h, i, None);
        g.add_edge(k, y, None);
        g.add_edge(w, p, None);
        g.add_edge(v, o, None);
        g.add_edge(n, e, None);
        g.add_edge(l, i, None);
        g.add_edge(b, g_node, None);
        g.add_edge(d, t, None);
        g.add_edge(j, l, None);
        g.add_edge(m, y, None);
        g.add_edge(t, a, None);
        g.add_edge(k, d, None);
        g.add_edge(h, p, None);
        g.add_edge(p, i, None);
        g.add_edge(t, l, None);
        g.add_edge(j, n, None);
        g.add_edge(u, f, None);
        g.add_edge(u, i, None);
        g.add_edge(a, f, None);
        g.add_edge(u, p, None);
        g.add_edge(r, h, None);
        g.add_edge(g_node, v, None);
        g.add_edge(p, f, None);
        g.add_edge(b, d, None);
        g.add_edge(u, x, None);
        g.add_edge(k, a, None);
        g.add_edge(g_node, d, None);
        g.add_edge(n, u, None);
        g.add_edge(u, l, None);
        g.add_edge(m, j, None);
        g.add_edge(i, x, None);
        g.add_edge(h, l, None);
        g.add_edge(m, s, None);
        g.add_edge(e, o, None);
        g.add_edge(q, f, None);
        g.add_edge(a, o, None);
        g.add_edge(t, p, None);
        g.add_edge(f, x, None);
        g.add_edge(d, p, None);
        g.add_edge(a, x, None);
        g.add_edge(g_node, z, None);
        g.add_edge(w, f, None);
        g.add_edge(q, x, None);
        g.add_edge(c, v, None);
        g.add_edge(l, v, None);
        g.add_edge(e, l, None);
        g.add_edge(b, x, None);
        g.add_edge(m, v, None);
        g.add_edge(f, i, None);
        g.add_edge(p, x, None);
        g.add_edge(c, a, None);
        g.add_edge(z, h, None);
        g.add_edge(q, s, None);
        g.add_edge(g_node, x, None);
        g.add_edge(t, o, None);
        g.add_edge(p, o, None);
        g.add_edge(t, v, None);
        g.add_edge(n, v, None);
        g.add_edge(z, x, None);
        g.add_edge(l, x, None);
        g.add_edge(z, y, None);
        g.add_edge(n, t, None);
        g.add_edge(s, t, None);
        g.add_edge(g_node, k, None);
        g.add_edge(t, x, None);
        g.add_edge(r, x, None);

        let mut sorted_order = g.lexicographical_topological_sort();

        // possible starting edges are 'Q', 'R', 'B'
        sorted_order.do_lexicographical_topological_sort().unwrap();

        let lexicographical_traverse_order = sorted_order
            .map(|x| {
                if let Some(letter) = g.get_node_info(x) {
                    letter
                } else {
                    ""
                }
            })
            .collect::<Vec<&str>>()
            .join("");

        println!(
            "lexicographically topologically sorted order: {}",
            lexicographical_traverse_order
        );
        assert_eq!(lexicographical_traverse_order, "BGKDMJCNEQRSTUZWHYLPAFIVXO");
    }
}
