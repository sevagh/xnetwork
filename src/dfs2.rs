use crate::graph::{find_path, Graph};
use slotmap::{DefaultKey, SecondaryMap};
use std::{cmp::Ord, collections::VecDeque, error, fmt, fmt::Debug, result};

lazy_static! {
    pub(crate) static ref NULL_KEY: DefaultKey = DefaultKey::default();
}

#[derive(Debug, PartialEq)]
enum EdgeKind {
    Undefined,
    Tree,
    Back,
    Forward,
    Cross,
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
pub struct DFS2<'a, T: Copy + Debug + Ord, U: Debug> {
    graph: &'a Graph<T, U>,

    processed: SecondaryMap<DefaultKey, bool>,
    discovered: SecondaryMap<DefaultKey, bool>,
    parent: SecondaryMap<DefaultKey, DefaultKey>,
    entry_time: SecondaryMap<DefaultKey, usize>,
    exit_time: SecondaryMap<DefaultKey, usize>,

    to_yield: VecDeque<DefaultKey>,
    stack: Vec<DefaultKey>,
    n_edges: usize,
    time: usize,
    finished: bool,
    topological: bool,
    lexicographical: bool,
}

impl<'a, T: Copy + Debug + Ord, U: Debug> DFS2<'a, T, U> {
    pub(crate) fn for_graph(g: &'a Graph<T, U>) -> Self {
        let mut dfs = DFS2 {
            graph: g,
            processed: SecondaryMap::with_capacity(g.nodes.len()),
            discovered: SecondaryMap::with_capacity(g.nodes.len()),
            parent: SecondaryMap::with_capacity(g.nodes.len()),
            entry_time: SecondaryMap::with_capacity(g.nodes.len()),
            exit_time: SecondaryMap::with_capacity(g.nodes.len()),
            to_yield: VecDeque::with_capacity(g.nodes.len()),
            n_edges: 0,
            time: 0,
            finished: false,
            topological: false,
            lexicographical: false,
        };
        dfs.init();
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

        if self.do_dfs(starting_node.unwrap()).is_err() {
            return Err(TopologicalSortError);
        }

        for k in self.graph.nodes.keys() {
            println!("checking node: {:?}", k);
            if !self.discovered.get(k).unwrap() {
                println!("undiscovered! doing...");
                if self.do_dfs(k).is_err() {
                    return Err(TopologicalSortError);
                }
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

        let mut starting_node: Option<DefaultKey> = None;
        for k in self.graph.nodes.keys() {
            if self.graph.indegree(k) == 0 {
                starting_node = Some(k);
                break;
            }
        }

        if self.do_dfs(starting_node.unwrap()).is_err() {
            return Err(TopologicalSortError);
        }

        for k in self.graph.nodes.keys() {
            if !self.discovered.get(k).unwrap() && self.do_dfs(k).is_err() {
                return Err(TopologicalSortError);
            }
        }
        Ok(())
    }

    pub fn do_dfs(&mut self, node: DefaultKey) -> TopologicalSortResult<()> {
        if self.finished {
            return Ok(());
        }

        println!("discovering, incrementing time, entry time for node {:?}", node);
        self.graph.print_info(node);

        self.discovered.insert(node, true);
        self.time += 1;

        self.entry_time.insert(node, self.time);

        self.process_node_early(node);

        if let Some(edge_list) = self.graph.edges.get(node) {
            for edge in edge_list.iter() {
                if !self.discovered.get(edge.dst).unwrap() {
                    self.parent.insert(edge.dst, node);

                    if self.process_edge(node, edge.dst).is_err() && self.lexicographical {
                        return Err(TopologicalSortError);
                    }

                    println!("\tkicking off recursion from {:?} to {:?}", node, edge.dst);
                    println!("\n");
                    if self.do_dfs(edge.dst).is_err() {
                        return Err(TopologicalSortError);
                    }

                    continue;
                } else if (!self.processed.get(edge.dst).unwrap()
                    && *(self.parent.get(node).unwrap()) != edge.dst)
                    || self.graph.directed
                {
                    if self.process_edge(node, edge.dst).is_err() && self.lexicographical {
                        return Err(TopologicalSortError);
                    }
                    if self.finished {
                        return Ok(());
                    }
                }
            }
        }

        self.process_node_late(node);
        self.time += 1;
        self.exit_time.insert(node, self.time);
        self.processed.insert(node, true);

        Ok(())
    }

    fn process_node_early(&mut self, node: DefaultKey) {
        if !self.topological {
            self.to_yield.push_back(node);
        }
    }

    fn process_node_late(&mut self, node: DefaultKey) {
        if self.topological {
            self.to_yield.push_back(node);
        }
    }

    fn process_edge(&mut self, src: DefaultKey, dst: DefaultKey) -> TopologicalSortResult<()> {
        if self.classify_edge(src, dst) == EdgeKind::Back {
            if !self.topological {
                // check for back edges
                eprintln!(
                    "[INFO] found cycle {:?}, {:?}",
                    self.graph.nodes.get(dst).unwrap(),
                    self.graph.nodes.get(src).unwrap()
                );
                find_path(dst, src, &self.parent);

                if self.n_edges == self.graph.n_edges() {
                    self.finished = true;
                }
            } else if self.lexicographical {
                return Err(TopologicalSortError);
            }
        }
        self.n_edges += 1;
        Ok(())
    }

    fn classify_edge(&self, src: DefaultKey, dst: DefaultKey) -> EdgeKind {
        if *(self.parent.get(dst).unwrap()) == src {
            EdgeKind::Tree
        } else if *(self.discovered.get(dst).unwrap()) && !*(self.processed.get(dst).unwrap()) {
            EdgeKind::Back
        } else if *(self.processed.get(dst).unwrap())
            && (self.entry_time.get(dst).unwrap() > self.entry_time.get(src).unwrap())
        {
            EdgeKind::Forward
        } else if *(self.processed.get(dst).unwrap())
            && (self.entry_time.get(dst).unwrap() < self.entry_time.get(src).unwrap())
        {
            EdgeKind::Cross
        } else {
            EdgeKind::Undefined
        }
    }
}

impl<'a, T: Copy + Debug + Ord, U: Debug> Iterator for DFS2<'a, T, U> {
    type Item = DefaultKey;

    fn next(&mut self) -> Option<Self::Item> {
        if self.topological {
            self.to_yield.pop_back()
        } else {
            self.to_yield.pop_front()
        }
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
        assert_eq!(dfs1.next(), Some(b1));
        assert_eq!(dfs1.next(), Some(c1));
        assert_eq!(dfs1.next(), None);
        assert_eq!(dfs1.n_edges, g1.n_edges());
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

        let mut dfs2 = g2.dfs();
        dfs2.do_dfs(a2).unwrap();

        assert_eq!(dfs2.next(), Some(a2));
        assert_eq!(dfs2.next(), Some(b2));
        assert_eq!(dfs2.next(), Some(c2));
        assert_eq!(dfs2.next(), Some(d2));
        assert_eq!(dfs2.next(), None);
        assert_eq!(dfs2.n_edges, g2.n_edges());
        println!(
            "graph edges 2: {}, dfs n_edges: {}",
            g2.n_edges(),
            dfs2.n_edges
        );
    }

    #[test]
    fn wont_topological_sort_undirected() {
        let g = Graph::<i32, &str>::new_undirected();
        let mut dfs = g.dfs();
        assert!(dfs.do_topological_sort().is_err());
    }

    #[test]
    fn basic_topological_sort() {
        let mut g = Graph::<i32, &str>::new_directed();

        let tristram = g.add_node(0, Some("Tristram"));
        let alpha_centauri = g.add_node(1, Some("AlphaCentauri"));
        let _saturn = g.add_node(2, Some("Saturn"));

        g.add_edge(tristram, alpha_centauri, None);

        let mut dfs = g.dfs();
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

        let mut dfs = gr.dfs();
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
}
