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

    expected answer:
    CABDFE
*/

fn main() {
    let mut g = Graph::new_directed();

    let a = g.add_node(0, Some("A"));
    let b = g.add_node(1, Some("B"));
    let c = g.add_node(2, Some("C"));
    let d = g.add_node(3, Some("D"));
    let e = g.add_node(4, Some("E"));
    let f = g.add_node(5, Some("F"));

    g.add_edge(c, a, None);
    g.add_edge(c, f, None);

    g.add_edge(a, b, None);
    g.add_edge(a, d, None);

    g.add_edge(d, e, None);
    g.add_edge(b, e, None);
    g.add_edge(f, e, None);

    let mut sorted_order = g.lexicographical_topological_sort();
    sorted_order.do_lexicographical_topological_sort().unwrap();

    println!("\n\n");
    println!("graph edges: {}", g.n_edges());

    println!("processed edges 1: {}", sorted_order.get_n_edges());
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

    assert_eq!(lexicographical_traverse_order, "CABDFE");
}
