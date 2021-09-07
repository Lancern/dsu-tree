extern crate dsu_tree;

use std::cmp::{Ordering, Reverse};
use std::collections::BinaryHeap;
use std::cell::RefCell;
use dsu_tree::DsuRoot;

struct Graph {
    edges: Vec<Edge>,
}

impl Graph {
    fn new() -> Self {
        Self {
            edges: Vec::new(),
        }
    }

    fn add_edge(mut self, nodes: [usize; 2], weight: u32) -> Self {
        self.edges.push(Edge { nodes, weight });
        self
    }

    fn take_edges(self) -> Vec<Edge> {
        self.edges
    }
}

struct Edge {
    nodes: [usize; 2],
    weight: u32,
}

impl Eq for Edge {}

impl Ord for Edge {
    fn cmp(&self, other: &Self) -> Ordering {
        self.weight.cmp(&other.weight)
    }
}

impl PartialEq for Edge {
    fn eq(&self, other: &Self) -> bool {
        self.weight == other.weight
    }
}

impl PartialOrd for Edge {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.weight.partial_cmp(&other.weight)
    }
}

struct Dsu {
    roots: Vec<RefCell<DsuRoot<usize>>>,
}

impl Dsu {
    fn new() -> Self {
        Self {
            roots: Vec::new(),
        }
    }

    fn add_root(&mut self, value: usize) {
        self.roots.push(RefCell::new(DsuRoot::new(value)));
    }

    fn find(&self, id: usize) -> usize {
        *self.roots[id].borrow_mut().value()
    }

    fn merge(&mut self, first: usize, second: usize) {
        if first == second {
            return;
        }

        let mut first_root = self.roots[first].borrow_mut();
        let mut second_root = self.roots[second].borrow_mut();
        first_root.merge_into(&mut second_root);
    }
}

fn find_mst(nodes: usize, edges: Vec<Edge>) -> u32 {
    let mut edges_heap = BinaryHeap::new();
    for e in edges {
        edges_heap.push(Reverse(e));
    }

    let mut dsu = Dsu::new();
    for i in 0..nodes {
        dsu.add_root(i);
    }

    let mut mst_weight = 0u32;
    let mut edge_count = 0usize;
    while edge_count < nodes - 1 {
        let edge = edges_heap.pop().unwrap().0;
        if dsu.find(edge.nodes[0]) == dsu.find(edge.nodes[1]) {
            continue;
        }

        mst_weight += edge.weight;
        edge_count += 1;

        dsu.merge(edge.nodes[0], edge.nodes[1]);
    }

    mst_weight
}

fn main() {
    let graph_edges = Graph::new()
        .add_edge([0, 1], 1)
        .add_edge([0, 3], 4)
        .add_edge([0, 4], 3)
        .add_edge([1, 3], 4)
        .add_edge([1, 4], 2)
        .add_edge([2, 4], 4)
        .add_edge([2, 5], 5)
        .add_edge([3, 4], 4)
        .add_edge([4, 5], 7)
        .take_edges();
    let mst_weight = find_mst(6, graph_edges);
    assert_eq!(mst_weight, 16);
    println!("ok");
}
