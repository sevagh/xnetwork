extern crate slotmap;
extern crate xnetwork;

use xnetwork::graph::Graph;

/*
   problems from: https://adventofcode.com/2018/day/7
   DAG problem

   Visually, these requirements look like this:

     -->A--->B--
    /    \      \
   C      -->D----->E
    \           /
     ---->F-----
*/

fn main() {
    let mut simple_graph = Graph::new_directed();

    let a = simple_graph.add_node(0, Some("A"));
    let b = simple_graph.add_node(1, Some("B"));
    let c = simple_graph.add_node(2, Some("C"));
    let d = simple_graph.add_node(3, Some("D"));
    let e = simple_graph.add_node(4, Some("E"));
    let f = simple_graph.add_node(5, Some("F"));

    simple_graph.add_edge(c, a, None);
    simple_graph.add_edge(c, f, None);

    simple_graph.add_edge(a, b, None);
    simple_graph.add_edge(a, d, None);

    simple_graph.add_edge(d, e, None);
    simple_graph.add_edge(b, e, None);
    simple_graph.add_edge(f, e, None);

    let mut sorted_order = simple_graph.topological_sort().unwrap();
    sorted_order.do_topological_sort(c).unwrap();

    println!("\n\n");

    println!("lexicographically topologically sorted order:");
    for node in sorted_order {
        simple_graph.print_info(node);
    }
}
