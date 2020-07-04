use crate::graph::Graph;
use slotmap::{DefaultKey, SecondaryMap};
use std::{collections::VecDeque, fmt::Debug};

#[derive(Debug)]
pub struct BFS<'a, T: Copy + Debug, U: Debug> {
    graph: &'a Graph<T, U>,

    // could these all be one giant SecondaryMap with a "NodeMeta"/"BFSInfo" struct stored?
    // probably without making my life unhappier w.r.t. ownership
    // and iterating over some members of processed/discovered/colors/parents while modifying
    // others
    processed: SecondaryMap<DefaultKey, bool>,
    discovered: SecondaryMap<DefaultKey, bool>,
    colors: SecondaryMap<DefaultKey, Color>,
    parent: SecondaryMap<DefaultKey, Option<DefaultKey>>,

    queue: VecDeque<DefaultKey>,
    to_yield: VecDeque<DefaultKey>,
    bipartite: bool,
    n_edges: usize,
}

#[derive(Debug, PartialEq)]
enum Color {
    Uncolored,
    White,
    Black,
}

impl Color {
    fn complement(&self) -> Self {
        match self {
            Color::White => Color::Black,
            Color::Black => Color::White,
            _ => Color::Uncolored,
        }
    }
}

impl<'a, T: Copy + Debug, U: Debug> BFS<'a, T, U> {
    pub(crate) fn for_graph(g: &'a Graph<T, U>) -> Self {
        let mut bfs = BFS {
            graph: g,
            processed: SecondaryMap::with_capacity(g.nodes.len()),
            discovered: SecondaryMap::with_capacity(g.nodes.len()),
            parent: SecondaryMap::with_capacity(g.nodes.len()),
            colors: SecondaryMap::with_capacity(g.nodes.len()),
            queue: VecDeque::with_capacity(g.nodes.len()),
            to_yield: VecDeque::with_capacity(g.nodes.len()),
            bipartite: true,
            n_edges: 0,
        };
        bfs.init();
        bfs
    }

    fn init(&mut self) {
        for k in self.graph.nodes.keys() {
            self.processed.insert(k, false);
            self.discovered.insert(k, false);
            self.parent.insert(k, None);
            self.colors.insert(k, Color::Uncolored);
        }
    }

    pub fn do_bfs(&mut self, start: DefaultKey) {
        self.queue.push_back(start);
        self.discovered.insert(self.queue[0], true);

        let mut node: DefaultKey;

        while !self.queue.is_empty() {
            node = self.queue.pop_front().unwrap();

            self.process_node_early(node);
            self.processed.insert(node, true);

            if let Some(edge_list) = self.graph.edges.get(node) {
                for edge in edge_list.iter() {
                    if !self.processed.get(edge.dst).unwrap() || self.graph.directed {
                        self.process_edge(node, edge.dst);
                    }

                    if !self.discovered.get(edge.dst).unwrap() {
                        self.queue.push_back(edge.dst);
                        self.discovered.insert(edge.dst, true);
                        self.parent.insert(edge.dst, Some(node));
                    }
                }
            }
            self.process_node_late(node);
        }
    }

    pub fn connected_components(&mut self) -> i32 {
        let mut c: i32 = 0;

        for k in self.graph.nodes.keys() {
            // if it's unvisited, kick off the bfs
            if !self.discovered.get(k).unwrap() {
                c += 1;

                self.do_bfs(k);
            }
        }

        c
    }

    pub fn two_color(&mut self) -> bool {
        for k in self.graph.nodes.keys() {
            // if it's unvisited, kick off the bfs
            if !self.discovered.get(k).unwrap() {
                self.colors.insert(k, Color::White);
                self.do_bfs(k);
            }
        }

        self.bipartite
    }

    pub fn n_edges(&self) -> usize {
        self.n_edges
    }

    fn process_node_early(&mut self, node: DefaultKey) {
        self.to_yield.push_back(node);
    }

    fn process_node_late(&mut self, _node: DefaultKey) {}

    fn process_edge(&mut self, src: DefaultKey, dst: DefaultKey) {
        self.n_edges += 1;

        if self.colors.get(src).unwrap() == self.colors.get(dst).unwrap() {
            self.bipartite = false;
            eprintln!(
                "[WARN] not bipartite due to edge {:?}, {:?}",
                self.graph.nodes.get(src).unwrap(),
                self.graph.nodes.get(dst).unwrap()
            );
        }

        self.colors
            .insert(dst, self.colors.get(src).unwrap().complement());
    }
}

impl<'a, T: Copy + Debug, U: Debug> Iterator for BFS<'a, T, U> {
    type Item = DefaultKey;

    fn next(&mut self) -> Option<Self::Item> {
        self.to_yield.pop_front()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_bfs() {
        let mut g = Graph::<i32, &str>::new_undirected();

        let tristram = g.add_node(0, Some("Tristram"));
        let alpha_centauri = g.add_node(1, Some("AlphaCentauri"));
        let _saturn = g.add_node(2, Some("Saturn"));

        g.add_edge(tristram, alpha_centauri, None);

        let mut bfs = g.bfs();
        bfs.do_bfs(tristram);

        for visited_node in bfs {
            println!("bfs visited node: {:#?}", visited_node);
        }

        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn real_bfs() {
        let mut g = Graph::<i32, &str>::new_undirected();

        let a = g.add_node(0, Some("a"));
        let b = g.add_node(1, Some("b"));
        let c = g.add_node(2, Some("c"));

        g.add_edge(a, c, None);
        g.add_edge(c, b, None);

        let mut bfs = g.bfs();
        bfs.do_bfs(a);

        for visited_node in bfs {
            println!("bfs visited node: {:#?}", visited_node);
            g.print_info(visited_node);
        }
    }

    #[test]
    fn real_bfs_asserts() {
        let mut g = Graph::<i32, &str>::new_undirected();

        let a = g.add_node(0, Some("a"));
        let b = g.add_node(1, Some("b"));
        let c = g.add_node(2, Some("c"));

        g.add_edge(a, c, None);
        g.add_edge(c, b, None);

        let mut bfs = g.bfs();
        bfs.do_bfs(a);

        assert_eq!(bfs.next(), Some(a));
        assert_eq!(bfs.next(), Some(c));
        assert_eq!(bfs.next(), Some(b));
        assert_eq!(bfs.next(), None);
    }

    #[test]
    fn real_bfs_asserts_2() {
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
        g.add_edge(b, a, None);
        g.add_edge(b, e, None);
        g.add_edge(b, f, None);
        g.add_edge(c, a, None);
        g.add_edge(d, c, None);
        g.add_edge(e, b, None);
        g.add_edge(f, b, None);

        let mut bfs = g.bfs();

        // kick off the bfs with the starting node
        bfs.do_bfs(b);

        for next in bfs {
            g.print_info(next);
        }
        //assert_eq!(bfs.next(), Some(b));
        //assert_eq!(bfs.next(), Some(c));
        //assert_eq!(bfs.next(), Some(d));
        //assert_eq!(bfs.next(), Some(a));
        //assert_eq!(bfs.next(), Some(e));
        //assert_eq!(bfs.next(), Some(f));
        //assert_eq!(bfs.next(), None);
    }

    #[test]
    fn test_connected_components() {
        let mut g = Graph::<i32, &str>::new_undirected();

        let tristram = g.add_node(0, Some("Tristram"));
        let alpha_centauri = g.add_node(1, Some("AlphaCentauri"));
        let saturn = g.add_node(2, Some("Saturn"));
        let pluto = g.add_node(3, Some("Pluto"));

        g.add_edge(tristram, alpha_centauri, None);
        g.add_edge(saturn, pluto, None);

        let mut b = g.bfs();

        assert_eq!(b.connected_components(), 2);

        // check if we processed every edge
        assert_eq!(g.n_edges(), b.n_edges());
    }

    #[test]
    fn test_two_colors_is_bipartite() {
        let mut g = Graph::<i32, &str>::new_undirected();

        // dogs love only cats
        // cats love only dogs

        let cat1 = g.add_node(0, Some("cat1"));
        let cat2 = g.add_node(1, Some("cat2"));

        let dog1 = g.add_node(2, Some("dog1"));
        let dog2 = g.add_node(3, Some("dog2"));

        g.add_edge(dog1, cat1, None);
        g.add_edge(dog2, cat2, None);

        let mut b = g.bfs();

        assert!(b.two_color());

        // check if we processed every edge
        assert_eq!(g.n_edges(), b.n_edges());

        for (k, v) in b.colors.iter() {
            println!("node: {:#?}, color: {:#?}", b.graph.nodes.get(k), v);
        }
    }

    #[test]
    fn test_two_colors_is_not_bipartite() {
        let mut g = Graph::<i32, &str>::new_undirected();

        // dogs love only cats
        // cats love only dogs
        // but we violate that rule

        let cat1 = g.add_node(0, Some("cat1"));
        let cat2 = g.add_node(1, Some("cat2"));

        let dog1 = g.add_node(2, Some("dog1"));

        g.add_edge(dog1, cat1, None);
        g.add_edge(dog1, cat2, None);
        g.add_edge(cat1, cat2, None);

        let mut b = g.bfs();

        assert!(!b.two_color());

        // check if we processed every edge
        assert_eq!(g.n_edges(), b.n_edges());

        for (k, v) in b.colors.iter() {
            println!("node: {:?}, color: {:?}", b.graph.nodes.get(k), v);
            g.print_info(k);
        }
    }
}
