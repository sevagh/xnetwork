use crate::graph::Graph;

#[derive(Debug)]
pub struct IterNode<'a, T: 'a + Copy, U: 'a> {
    key: &'a T,
    extra: &'a U,
}

#[derive(Debug)]
pub struct BFS<'a, T: Copy, U> {
    pub(crate) inner: &'a Graph<T, U>,
}

impl <'a, T: Copy, U> Iterator for BFS<'a, T, U> {
    type Item = &'a IterNode<'a, T, U>;

    fn next(&mut self) -> Option<Self::Item> {
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
