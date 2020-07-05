extern crate slotmap;
extern crate xnetwork;

use xnetwork::graph::Graph;

/*
   problems from: https://adventofcode.com/2018/day/7
   DAG problem

   with my inputs in advent_of_code_2018_day_7_input.txt

   expected answer:
   BGKDMJCNEQRSTUZWHYLPAFIVXO
*/

fn main() {
    let mut g = Graph::new_directed();

    let a = g.add_node(0, Some("A"));
    let b = g.add_node(1, Some("B"));
    let c = g.add_node(2, Some("C"));
    let d = g.add_node(3, Some("D"));
    let e = g.add_node(4, Some("E"));
    let f = g.add_node(5, Some("F"));
    let g_node = g.add_node(6, Some("G"));
    let h = g.add_node(7, Some("H"));
    let i = g.add_node(8, Some("I"));
    let j = g.add_node(9, Some("J"));
    let k = g.add_node(10, Some("K"));
    let l = g.add_node(11, Some("L"));
    let m = g.add_node(12, Some("M"));
    let n = g.add_node(13, Some("N"));
    let o = g.add_node(14, Some("O"));
    let p = g.add_node(15, Some("P"));
    let q = g.add_node(16, Some("Q"));
    let r = g.add_node(17, Some("R"));
    let s = g.add_node(18, Some("S"));
    let t = g.add_node(19, Some("T"));
    let u = g.add_node(20, Some("U"));
    let v = g.add_node(21, Some("V"));
    let w = g.add_node(22, Some("W"));
    let x = g.add_node(23, Some("X"));
    let y = g.add_node(24, Some("Y"));
    let z = g.add_node(25, Some("Z"));

    g.add_edge(q, i, None);
    g.add_edge(b, m, None);
    g.add_edge(r, f, None);
    g.add_edge(g_node, s, None);
    g.add_edge(m, a, None);
    g.add_edge(z, w, None);
    g.add_edge(j, c, None);
    g.add_edge(k, o, None);
    g.add_edge(c, i, None);
    g.add_edge(y, l, None);
    g.add_edge(n, p, None);
    g.add_edge(s, x, None);
    g.add_edge(e, u, None);
    g.add_edge(u, v, None);
    g.add_edge(d, f, None);
    g.add_edge(w, h, None);
    g.add_edge(t, i, None);
    g.add_edge(h, v, None);
    g.add_edge(l, o, None);
    g.add_edge(p, a, None);
    g.add_edge(a, i, None);
    g.add_edge(f, o, None);
    g.add_edge(v, x, None);
    g.add_edge(i, o, None);
    g.add_edge(x, o, None);
    g.add_edge(f, v, None);
    g.add_edge(l, p, None);
    g.add_edge(y, p, None);
    g.add_edge(y, x, None);
    g.add_edge(y, o, None);
    g.add_edge(d, a, None);
    g.add_edge(t, f, None);
    g.add_edge(w, x, None);
    g.add_edge(r, a, None);
    g.add_edge(e, f, None);
    g.add_edge(h, i, None);
    g.add_edge(k, y, None);
    g.add_edge(w, p, None);
    g.add_edge(v, o, None);
    g.add_edge(n, e, None);
    g.add_edge(l, i, None);
    g.add_edge(b, g_node, None);
    g.add_edge(d, t, None);
    g.add_edge(j, l, None);
    g.add_edge(m, y, None);
    g.add_edge(t, a, None);
    g.add_edge(k, d, None);
    g.add_edge(h, p, None);
    g.add_edge(p, i, None);
    g.add_edge(t, l, None);
    g.add_edge(j, n, None);
    g.add_edge(u, f, None);
    g.add_edge(u, i, None);
    g.add_edge(a, f, None);
    g.add_edge(u, p, None);
    g.add_edge(r, h, None);
    g.add_edge(g_node, v, None);
    g.add_edge(p, f, None);
    g.add_edge(b, d, None);
    g.add_edge(u, x, None);
    g.add_edge(k, a, None);
    g.add_edge(g_node, d, None);
    g.add_edge(n, u, None);
    g.add_edge(u, l, None);
    g.add_edge(m, j, None);
    g.add_edge(i, x, None);
    g.add_edge(h, l, None);
    g.add_edge(m, s, None);
    g.add_edge(e, o, None);
    g.add_edge(q, f, None);
    g.add_edge(a, o, None);
    g.add_edge(t, p, None);
    g.add_edge(f, x, None);
    g.add_edge(d, p, None);
    g.add_edge(a, x, None);
    g.add_edge(g_node, z, None);
    g.add_edge(w, f, None);
    g.add_edge(q, x, None);
    g.add_edge(c, v, None);
    g.add_edge(l, v, None);
    g.add_edge(e, l, None);
    g.add_edge(b, x, None);
    g.add_edge(m, v, None);
    g.add_edge(f, i, None);
    g.add_edge(p, x, None);
    g.add_edge(c, a, None);
    g.add_edge(z, h, None);
    g.add_edge(q, s, None);
    g.add_edge(g_node, x, None);
    g.add_edge(t, o, None);
    g.add_edge(p, o, None);
    g.add_edge(t, v, None);
    g.add_edge(n, v, None);
    g.add_edge(z, x, None);
    g.add_edge(l, x, None);
    g.add_edge(z, y, None);
    g.add_edge(n, t, None);
    g.add_edge(s, t, None);
    g.add_edge(g_node, k, None);
    g.add_edge(t, x, None);
    g.add_edge(r, x, None);

    let mut sorted_order = g.lexicographical_topological_sort();

    // possible starting edges are 'Q', 'R', 'B'
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

    let mut sorted_order2 = g.topological_sort();

    // possible starting edges are 'Q', 'R', 'B'
    sorted_order2.do_topological_sort().unwrap();

    println!("processed edges 2: {}", sorted_order2.get_n_edges());
    let traverse_order = sorted_order2
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
        "non-lexicographic topologically sorted order: {}",
        traverse_order
    );
    println!(
        "expected lexicogr topologically sorted order: {}",
        "BGKDMJCNEQRSTUZWHYLPAFIVXO"
    );
    //assert_eq!(traverse_order, ;
}
