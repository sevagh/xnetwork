use crate::{
    dfs::NULL_KEY,
    graph::{Edge, Graph},
};
use slotmap::{DefaultKey, SecondaryMap, SparseSecondaryMap};
use std::{cmp::Ord, collections::VecDeque, error, fmt, fmt::Debug, result};

#[derive(Debug, PartialEq)]
enum EdgeKind {
    Undefined,
    Tree,
    Back,
    Forward,
    Cross,
}

type LexicographicalTopologicalSortResult<T> =
    result::Result<T, LexicographicalTopologicalSortError>;

#[derive(Debug)]
pub struct LexicographicalTopologicalSortError;

impl fmt::Display for LexicographicalTopologicalSortError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "not a dag")
    }
}

impl error::Error for LexicographicalTopologicalSortError {
    fn description(&self) -> &str {
        "not a dag"
    }

    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

#[derive(Debug)]
pub struct LexicographicalTopologicalSort<'a, T: Copy + Debug + Ord, U: Debug> {
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

impl<'a, T: Copy + Debug + Ord, U: Debug> LexicographicalTopologicalSort<'a, T, U> {
    pub(crate) fn for_graph(g: &'a Graph<T, U>) -> Self {
        let mut lexicographical_topological_sort = LexicographicalTopologicalSort {
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
        lexicographical_topological_sort.init();
        lexicographical_topological_sort
    }

    fn init(&mut self) {
        for k in self.graph.nodes.keys() {
            self.processed.insert(k, false);
            self.discovered.insert(k, false);
            self.parent.insert(k, *NULL_KEY);
        }
    }

    pub fn do_topological_sort(
        &mut self,
        node: DefaultKey,
    ) -> LexicographicalTopologicalSortResult<()> {
        let initial_edges = self.graph.edges.clone();
        self.do_topological_sort_inner(node, initial_edges)
    }

    fn do_topological_sort_inner(
        &mut self,
        node: DefaultKey,
        mut edges: SparseSecondaryMap<DefaultKey, Vec<Edge>>,
    ) -> LexicographicalTopologicalSortResult<()> {
        if self.finished {
            return Ok(());
        }

        self.discovered.insert(node, true);
        self.time += 1;

        self.entry_time.insert(node, self.time);

        self.process_node_early(node);

        if let Some(edge_list) = edges.get_mut(node) {
            println!("edge list PRE-lexicographical sort: {:?}", edge_list);

            edge_list.sort_by_cached_key(|e| self.graph.nodes.get(e.dst).unwrap());

            println!("edge list POST-lexicographical sort: {:?}", edge_list);

            for edge in edge_list.iter() {
                self.graph.print_info(edge.dst);

                if !self.discovered.get(edge.dst).unwrap() {
                    self.parent.insert(edge.dst, node);

                    if self.process_edge(node, edge.dst).is_err() {
                        return Err(LexicographicalTopologicalSortError);
                    }

                    // make recursive lexicographical_topological_sort explicit with a stack
                    if self.do_topological_sort(edge.dst).is_err() {
                        return Err(LexicographicalTopologicalSortError);
                    }

                    continue;
                } else if (!self.processed.get(edge.dst).unwrap()
                    && *(self.parent.get(node).unwrap()) != edge.dst)
                    || self.graph.directed
                {
                    if self.process_edge(node, edge.dst).is_err() {
                        return Err(LexicographicalTopologicalSortError);
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
    // vs late in lexicographical_topological sort
    fn process_node_late(&mut self, node: DefaultKey) {
        self.to_yield.push_back(node);
    }

    fn process_edge(
        &mut self,
        src: DefaultKey,
        dst: DefaultKey,
    ) -> LexicographicalTopologicalSortResult<()> {
        // check for back edges
        if self.classify_edge(src, dst) == EdgeKind::Back {
            return Err(LexicographicalTopologicalSortError);
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

impl<'a, T: Copy + Debug + Ord, U: Debug> Iterator for LexicographicalTopologicalSort<'a, T, U> {
    type Item = DefaultKey;

    fn next(&mut self) -> Option<Self::Item> {
        self.to_yield.pop_back()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn real_lexicographical_topological_sort() {
        // testcase from pp179 of skiena (figure 5.15)
        let mut gr = Graph::<i32, &str>::new_directed();

        let a = gr.add_node(0, Some("a"));
        let b = gr.add_node(1, Some("b"));
        let c = gr.add_node(2, Some("c"));
        let d = gr.add_node(3, Some("d"));

        gr.add_edge(a, b, None);
        gr.add_edge(a, c, None);
        gr.add_edge(c, d, None);

        let mut topological_sort = gr.topological_sort().unwrap();
        topological_sort.do_topological_sort(a).unwrap();

        assert_eq!(topological_sort.next(), Some(a));
        assert_eq!(topological_sort.next(), Some(c));
        assert_eq!(topological_sort.next(), Some(d));
        assert_eq!(topological_sort.next(), Some(b));

        println!("\n\n");

        let mut lexicographical_topological_sort = gr.lexicographical_topological_sort().unwrap();
        lexicographical_topological_sort
            .do_topological_sort(a)
            .unwrap();

        assert_eq!(lexicographical_topological_sort.next(), Some(a));
        assert_eq!(lexicographical_topological_sort.next(), Some(b));
        assert_eq!(lexicographical_topological_sort.next(), Some(c));
        assert_eq!(lexicographical_topological_sort.next(), Some(d));
    }
}
