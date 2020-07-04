use crate::{dfs::NULL_KEY, graph::Graph};
use slotmap::{DefaultKey, SecondaryMap};
use std::{collections::VecDeque, fmt::Debug};
use std::{error, fmt, result};

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
pub struct TopologicalSort<'a, T: Copy + Debug, U: Debug> {
    graph: &'a Graph<T, U>,

    processed: SecondaryMap<DefaultKey, bool>,
    discovered: SecondaryMap<DefaultKey, bool>,
    parent: SecondaryMap<DefaultKey, DefaultKey>,
    entry_time: SecondaryMap<DefaultKey, usize>,
    exit_time: SecondaryMap<DefaultKey, usize>,

    to_yield: VecDeque<DefaultKey>,
    n_edges: usize,
    time: usize,
    finished: bool,
}

impl<'a, T: Copy + Debug, U: Debug> TopologicalSort<'a, T, U> {
    pub(crate) fn for_graph(g: &'a Graph<T, U>) -> Self {
        let mut topological_sort = TopologicalSort {
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
        };
        topological_sort.init();
        topological_sort
    }

    fn init(&mut self) {
        for k in self.graph.nodes.keys() {
            self.processed.insert(k, false);
            self.discovered.insert(k, false);
            self.parent.insert(k, *NULL_KEY);
        }
    }

    pub fn do_topological_sort(&mut self, node: DefaultKey) -> TopologicalSortResult<()> {
        if self.finished {
            return Ok(());
        }

        self.discovered.insert(node, true);

        //// enqueue the first one in sorted order
        //if self.time == 0 {
        //    self.to_yield.push_back(node);
        //}

        self.time += 1;

        self.entry_time.insert(node, self.time);

        self.process_node_early(node);

        if let Some(edge_list) = self.graph.edges.get(node) {
            for edge in edge_list.iter() {
                if !self.discovered.get(edge.dst).unwrap() {
                    self.parent.insert(edge.dst, node);

                    if self.process_edge(node, edge.dst).is_err() {
                        return Err(TopologicalSortError);
                    }

                    // make recursive topological_sort explicit with a stack
                    if self.do_topological_sort(edge.dst).is_err() {
                        return Err(TopologicalSortError);
                    }

                    continue;
                } else if (!self.processed.get(edge.dst).unwrap()
                    && *(self.parent.get(node).unwrap()) != edge.dst)
                    || self.graph.directed
                {
                    if self.process_edge(node, edge.dst).is_err() {
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

    fn process_node_early(&mut self, _node: DefaultKey) {}

    // notice the switch from enqueueing the node early in dfs
    // vs late in topological sort
    fn process_node_late(&mut self, node: DefaultKey) {
        self.to_yield.push_back(node);
    }

    fn process_edge(&mut self, src: DefaultKey, dst: DefaultKey) -> TopologicalSortResult<()> {
        // check for back edges
        if self.classify_edge(src, dst) == EdgeKind::Back {
            return Err(TopologicalSortError);
        }
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

impl<'a, T: Copy + Debug, U: Debug> Iterator for TopologicalSort<'a, T, U> {
    type Item = DefaultKey;

    fn next(&mut self) -> Option<Self::Item> {
        self.to_yield.pop_back()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wont_topological_sort_undirected() {
        let g = Graph::<i32, &str>::new_undirected();
        assert!(g.topological_sort().is_none());
    }

    #[test]
    fn basic_topological_sort() {
        let mut g = Graph::<i32, &str>::new_directed();

        let tristram = g.add_node(0, Some("Tristram"));
        let alpha_centauri = g.add_node(1, Some("AlphaCentauri"));
        let _saturn = g.add_node(2, Some("Saturn"));

        g.add_edge(tristram, alpha_centauri, None);

        let mut topological_sort = g.topological_sort().unwrap();
        topological_sort.do_topological_sort(tristram).unwrap();

        for visited_node in topological_sort {
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

        let mut topological_sort = gr.topological_sort().unwrap();
        topological_sort.do_topological_sort(g).unwrap();

        assert_eq!(topological_sort.next(), Some(g));
        assert_eq!(topological_sort.next(), Some(a));
        assert_eq!(topological_sort.next(), Some(b));
        assert_eq!(topological_sort.next(), Some(c));
        assert_eq!(topological_sort.next(), Some(f));
        assert_eq!(topological_sort.next(), Some(e));
        assert_eq!(topological_sort.next(), Some(d));
    }
}
