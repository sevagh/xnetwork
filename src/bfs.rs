use crate::graph::{Edge, Graph};
use slotmap::{DefaultKey, SecondaryMap};
use std::{collections::VecDeque, fmt::Debug};

#[derive(Debug)]
pub struct BFS<'a, T: Copy + Debug, U: Debug> {
    graph: &'a Graph<T, U>,
    processed: SecondaryMap<DefaultKey, bool>,
    discovered: SecondaryMap<DefaultKey, bool>,
    parent: SecondaryMap<DefaultKey, Option<DefaultKey>>,
    queue: VecDeque<DefaultKey>,
    to_yield: VecDeque<DefaultKey>,
}

impl<'a, T: Copy + Debug, U: Debug> BFS<'a, T, U> {
    pub(crate) fn for_graph(g: &'a Graph<T, U>) -> Self {
        let mut bfs = BFS {
            graph: g,
            processed: SecondaryMap::new(),
            discovered: SecondaryMap::new(),
            parent: SecondaryMap::new(),
            queue: VecDeque::with_capacity(g.nodes.len()),
            to_yield: VecDeque::with_capacity(g.nodes.len()),
        };
        bfs.init();
        bfs
    }

    fn init(&mut self) {
        let mut first_key = self.graph.nodes.keys().take(1);

        if let Some(x) = first_key.next() {
            self.queue.push_back(x);
        }

        if self.queue.is_empty() {
            return;
        }

        for k in self.graph.nodes.keys() {
            self.processed.insert(k, false);
            self.discovered.insert(k, false);
            self.parent.insert(k, None);
        }

        self.discovered.insert(self.queue[0], true);

        let mut node: DefaultKey;
        let mut dest_node: DefaultKey;

        while !self.queue.is_empty() {
            node = self.queue.pop_front().unwrap();

            self.process_node_early(node);
            self.processed.insert(node, true);

            if let Some(edge_list) = self.graph.edges.get(node) {
                for edge in edge_list.iter() {
                    assert!(edge.src == node);

                    // do stuff with edge here
                    //possible_edge =

                    dest_node = edge.dst;

                    // unwrap because i don't expect this to not be set
                    if !self.processed.get(dest_node).unwrap() || self.graph.directed {
                        self.process_edge(edge);
                    }

                    // unwrap because i don't expect this to not be set
                    if !self.discovered.get(dest_node).unwrap() {
                        self.queue.push_back(dest_node);
                        self.discovered.insert(dest_node, true);
                        self.parent.insert(dest_node, Some(node));
                    }
                }
            }
            self.process_node_late(node);
        }
    }

    fn process_node_early(&mut self, node: DefaultKey) {
        self.to_yield.push_back(node);
    }

    fn process_node_late(&mut self, _node: DefaultKey) {}

    fn process_edge(&mut self, _edge: &Edge) {}
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

        let bfs = g.bfs();

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

        let bfs = g.bfs();

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

        assert_eq!(bfs.next(), Some(a));
        assert_eq!(bfs.next(), Some(c));
        assert_eq!(bfs.next(), Some(b));
        assert_eq!(bfs.next(), None);
    }
}
