use crate::graph::Graph;
use slotmap::{DefaultKey, SecondaryMap};
use std::{collections::VecDeque, fmt::Debug};

lazy_static! {
    static ref NULL_KEY: DefaultKey = DefaultKey::default();
}

#[derive(Debug)]
pub struct DFS<'a, T: Copy + Debug, U: Debug> {
    graph: &'a Graph<T, U>,

    processed: SecondaryMap<DefaultKey, bool>,
    discovered: SecondaryMap<DefaultKey, bool>,
    parent: SecondaryMap<DefaultKey, DefaultKey>,
    entry_time: SecondaryMap<DefaultKey, usize>,
    exit_time: SecondaryMap<DefaultKey, usize>,

    to_yield: VecDeque<DefaultKey>,
    n_edges: usize,
    time: usize,
}

impl<'a, T: Copy + Debug, U: Debug> DFS<'a, T, U> {
    pub(crate) fn for_graph(g: &'a Graph<T, U>) -> Self {
        let mut dfs = DFS {
            graph: g,
            processed: SecondaryMap::with_capacity(g.nodes.len()),
            discovered: SecondaryMap::with_capacity(g.nodes.len()),
            parent: SecondaryMap::with_capacity(g.nodes.len()),
            entry_time: SecondaryMap::with_capacity(g.nodes.len()),
            exit_time: SecondaryMap::with_capacity(g.nodes.len()),
            to_yield: VecDeque::with_capacity(g.nodes.len()),
            n_edges: 0,
            time: 0,
        };
        dfs.init();
        dfs
    }

    fn init(&mut self) {
        for k in self.graph.nodes.keys() {
            self.processed.insert(k, false);
            self.discovered.insert(k, false);
            self.parent.insert(k, *NULL_KEY);
        }
    }

    pub fn do_dfs(&mut self, node: DefaultKey) {
        self.discovered.insert(node, true);
        self.time += 1;

        self.entry_time.insert(node, self.time);

        self.process_node_early(node);

        if let Some(edge_list) = self.graph.edges.get(node) {
            for edge in edge_list.iter() {
                if !self.discovered.get(edge.dst).unwrap() {
                    self.parent.insert(edge.dst, node);
                    self.process_edge(node, edge.dst);

                    // make recursive dfs explicit with a stack
                    self.do_dfs(edge.dst);
                    continue;
                } else if (!self.processed.get(edge.dst).unwrap()
                    && *(self.parent.get(node).unwrap()) != edge.dst)
                    || self.graph.directed
                {
                    self.process_edge(node, edge.dst);
                }
            }
        }

        self.process_node_late(node);
        self.time += 1;
        self.exit_time.insert(node, self.time);
        self.processed.insert(node, true);
    }

    fn process_node_early(&mut self, node: DefaultKey) {
        self.to_yield.push_back(node);
    }

    fn process_node_late(&mut self, _node: DefaultKey) {}

    fn process_edge(&mut self, _src: DefaultKey, _dst: DefaultKey) {
        self.n_edges += 1;
    }
}

impl<'a, T: Copy + Debug, U: Debug> Iterator for DFS<'a, T, U> {
    type Item = DefaultKey;

    fn next(&mut self) -> Option<Self::Item> {
        self.to_yield.pop_front()
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
        dfs.do_dfs(tristram);

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
        dfs.do_dfs(a);

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
        dfs.do_dfs(a);

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
        dfs_from_b.do_dfs(b);

        for next in dfs_from_b {
            g.print_info(next);
        }

        println!("dfs from node 'f'");

        let mut dfs_from_f = g.dfs();

        // kick off the dfs with the starting node
        dfs_from_f.do_dfs(f);

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
    fn real_dfs_tremaux_tree() {
        // from
        // https://en.wikipedia.org/wiki/Depth-first_search#Example

        let mut gr = Graph::<i32, &str>::new_undirected();

        let a = gr.add_node(0, Some("a"));
        let b = gr.add_node(1, Some("b"));
        let c = gr.add_node(2, Some("c"));
        let d = gr.add_node(3, Some("d"));
        let e = gr.add_node(4, Some("e"));
        let f = gr.add_node(5, Some("f"));
        let g = gr.add_node(6, Some("g"));

        gr.add_edge(a, b, None);
        gr.add_edge(b, d, None);
        gr.add_edge(b, f, None);
        gr.add_edge(f, e, None);
        gr.add_edge(a, c, None);
        gr.add_edge(c, g, None);
        gr.add_edge(a, e, None);

        let mut dfs = gr.dfs();
        dfs.do_dfs(a);

        assert_eq!(dfs.next(), Some(a));
        assert_eq!(dfs.next(), Some(b));
        assert_eq!(dfs.next(), Some(d));
        assert_eq!(dfs.next(), Some(f));
        assert_eq!(dfs.next(), Some(e));
        assert_eq!(dfs.next(), Some(c));
        assert_eq!(dfs.next(), Some(g));
    }
}
