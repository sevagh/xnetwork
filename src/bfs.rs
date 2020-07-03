use crate::graph::{Graph, Edge};
use slotmap::{DefaultKey, SecondaryMap};
use std::collections::VecDeque;

#[derive(Debug)]
pub struct IterNode<'a, T: 'a + Copy, U: 'a> {
    key: &'a T,
    extra: &'a U,
}

#[derive(Debug)]
pub struct BFS<'a, T: Copy, U> {
    graph: &'a Graph<T, U>,
    processed: SecondaryMap<DefaultKey, bool>,
    discovered: SecondaryMap<DefaultKey, bool>,
    parent: SecondaryMap<DefaultKey, Option<DefaultKey>>,
    queue: VecDeque<DefaultKey>,
    nodes_to_yield: VecDeque<DefaultKey>,
}

impl <'a, T: Copy, U> BFS<'a, T, U> {
    pub(crate) fn for_graph(g: &'a Graph<T, U>) -> Self {
        let mut bfs = BFS{
            graph: g,
            processed: SecondaryMap::new(),
            discovered: SecondaryMap::new(),
            parent: SecondaryMap::new(),
            queue: VecDeque::with_capacity(g.nodes.len()),
            nodes_to_yield: VecDeque::with_capacity(g.nodes.len()),
        };
        bfs.init();
        bfs
    }

    fn init(&mut self) {
        let mut first_key = self.graph.nodes.keys().take(1);

        if let Some(x) = first_key.next() {
            self.queue.push_back(x);
        }

        for k in self.graph.nodes.keys() {
            self.processed.insert(k, false);
            self.discovered.insert(k, false);
            self.parent.insert(k, None);
        }

        if self.queue.is_empty() {
            return;
        }

        self.discovered.insert(self.queue[0], true);

        let mut node: DefaultKey;
        let mut dest_node: DefaultKey;

        let mut possible_edge: Option<&Edge>;

        while !self.queue.is_empty() {
            node = self.queue.pop_front().unwrap();

            self.process_node_early(node);
            self.processed.insert(node, true);

            possible_edge = self.graph.edges.get(node);

            while let Some(edge) = possible_edge {
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

                possible_edge = self.graph.edges.get(dest_node);
            }
            self.process_node_late(node);
        }
    }

    fn process_node_early(&mut self, node: DefaultKey) {
        println!("processed node {:#?}", node);
        self.nodes_to_yield.push_back(node);
    }

    fn process_node_late(&mut self, _node: DefaultKey) {
    }

    fn process_edge(&mut self, edge: &Edge) {
        println!("processed edge {:#?}", edge);
    }
}

impl <'a, T: Copy, U> Iterator for BFS<'a, T, U> {
    type Item = &'a IterNode<'a, T, U>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(ret_node) = self.nodes_to_yield.pop_back() {
            Some(IterNode{
                key: self.graph.nodes.get(ret_node).unwrap(),
                extra: self.graph.node_infos.get(ret_node).unwrap(),
            });
        }
        None
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

        for visited_node in bfs.next() {
            println!("bfs visited node: {:#?}", visited_node);
        }

        assert_eq!(2 + 2, 4);
    }
}
