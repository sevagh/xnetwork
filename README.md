# xnetwork

xnetwork is a simple graph library written in Rust. It's kludgy in some places - I implemented it from Skiena's Algorithm Design manual, and tried to avoid looking at existing implementations for inspiration.

## Graph features

In xnetwork, vertices are passed around using their `slotmap::DefaultKey`. Here's an overview of what you can do with xnetwork:

* Directed/undirected

```rust
let mut g_directed: Graph::<i32, &str>::new_directed();
let mut g_undirected: Graph::<i32, &str>::new_undirected();
```

* Primary and secondary key

The primary should implement `Ord` for various traversal purposes. The secondary is purely informational:

```rust
let mut g = Graph::<i32, &str>::new_undirected();

let a = g.add_node(0, Some("a"));
let b = g.add_node(1, Some("b"));
let c = g.add_node(2, Some("c"));
```

* Optionally weighted edges

```rust
let mut g = Graph::<i32, &str>::new_undirected();

let a = g.add_node(0, Some("a"));
let b = g.add_node(1, Some("b"));
let c = g.add_node(2, Some("c"));

g.add_edge(a, b, Some(12));
g.add_edge(b, c, Some(7));
```

* Traversals: BFS, DFS

```rust
let mut g = Graph::<i32, &str>::new_undirected();

let a = g.add_node(0, Some("a"));
let b = g.add_node(1, Some("b"));
let c = g.add_node(2, Some("c"));

let mut bfs = g.bfs();

// compute the bfs
bfs.do_bfs();

// implements iterator
for node in bfs {
    println!("node: {:?}", node);
}
```

Also included are algorithms based on BFS: connected-components and two-color.

* DAG

The module `src/dfs.rs` contains DAG traversals for topological sort and lexicographical topological sort. The unit tests for dfs.rs contain a solution for lexicographical topological sorting in [Advent of Code 2018 Day 7 Part 1](https://adventofcode.com/2018/day/7).

You'll get an error when applying these algorithms to undirected graphs:

```rust
let g = Graph::<i32, &str>::new_undirected();
let dfs = g.topological_sort();
assert!(dfs.is_err());
```

* Minimum spanning tree

Prim's and Kruskal's algorithm are both implemented. You'll get an error if a processed edge is missing a weight, or the graph is directed:

```rust
let mut g1 = Graph::<i32, &str>::new_directed();

let a = g1.add_node(0, Some("a"));
let b = g1.add_node(1, Some("b"));

g1.add_edge(a, b, None);
assert!(g1.mst_prim().is_err());

let mut g2 = Graph::<i32, &str>::new_undirected();

let a = g2.add_node(0, Some("a"));
let b = g2.add_node(1, Some("b"));

g2.add_edge(a, b, None);
g2.mst_prim().unwrap();
assert!(g2.do_prim(a).is_err());
```

## Implementation notes

At the heart of xnetwork is slotmap. Consider the following common graph code:

```c
int N_EDGES = 100;

struct edge edges[N_EDGES];
struct vertex vertices[N_EDGES];

bool visited[N_EDGES];
struct vertex parent[N_EDGES];
...
```

By using slotmap's secondary maps, these are represented neatly with secondary maps (this is not real code, but superficially resembles what's under the hood):

```rust
// graph for i32 nodes
let nodes: SlotMap<_, i32>;

// sparse because there's not necessarily as many edges as vertices
let edges: SparseSecondaryMap<_, Edge>;

// typical traversal structs are still associated to the vertices
// with the slotmap keys
let mut parent: SecondaryMap<_, DefaultKey>;
let mut visited: SecondaryMap<_, bool>;
```

I use a BinaryHeap for priority queues where it's needed (Prim's, topological sort) with a linear `reduce_key`, but decrease key can be done more efficiently, either with additional datastructures (e.g. a hashmap) or more advanced datastructures e.g. pairing or Fibonacci heaps, as recommended by Skiena.

For lexicographical topological sort, I use a priority queue to reduce the indegree of every discovered vertex, so that "unblocked" vertices bubble to the top (and then get sorted lexicographically).
