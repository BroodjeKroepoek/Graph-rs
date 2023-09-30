//! # Graph Library
//!
//! This library provides a generic graph data structure and associated operations.
//!
//! ## Overview
//!
//! - A `Graph<T>` represents a graph where `T` is the type of data associated with each vertex.
//! - Vertices are of type `Vertex<T>` and edges are of type `Edge<T>`.
//!
//! ## Basic Usage
//!
//! To use this library, you can create a graph, insert vertices and edges, and perform various graph operations.
//!
//! ```rust
//! use graph::{Graph, Vertex, Edge};
//!
//! fn main() {
//!     let mut graph = Graph::new();
//!
//!     let vertex_a = Vertex("A");
//!     let vertex_b = Vertex("B");
//!     let edge_ab = Edge(vertex_a, vertex_b);
//!
//!     graph.insert_vertex(vertex_a).expect("Failed to insert vertex");
//!     graph.insert_vertex(vertex_b).expect("Failed to insert vertex");
//!     graph.insert_edge(edge_ab).expect("Failed to insert edge");
//!
//!     println!("{}", graph);
//! }
//! ```
//!
//! ## Error Handling
//!
//! Errors are handled using custom error types `InsertVertexError` and `InsertEdgeError`. These errors indicate issues like duplicate vertices or edges that don't exist.
//!
//! ## Graph Types
//!
//! The library provides functions to create various types of graphs:
//!
//! - `new_complete_graph(size)` creates a complete graph with `size` vertices.
//! - `new_bipartite_graph(size_1, size_2)` creates a bipartite graph with two sets of vertices.
//! - `new_cyclic_graph(size)` creates a cyclic graph.
//! - `new_path_graph(size)` creates a path graph.
//!
//! ## Cartesian Product of Graphs
//!
//! You can compute the Cartesian product of two graphs using the `Mul` trait. This results in a new graph where each vertex is a pair of vertices from the original graphs.
//!
//! ## Examples
//!
//! For more examples and usage, refer to the documentation of specific functions and types.
//!
//! ## License
//!
//! This code is licensed under the MIT License.

use std::{
    collections::{btree_map::Entry, BTreeMap, BTreeSet},
    fmt::{Debug, Display},
    ops::Mul,
};

use thiserror::Error;

/// Represents a vertex in the graph.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct Vertex<T>(pub T)
where
    T: Ord;

impl<T> Display for Vertex<T>
where
    T: Copy + Display + Ord,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Represents an edge between two vertices in the graph.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Edge<T>(pub Vertex<T>, pub Vertex<T>)
where
    T: Ord;

impl<T> Display for Edge<T>
where
    T: Copy + Display + Ord,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {})", self.0, self.1)
    }
}

/// Represents a generic graph.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Graph<T>(pub BTreeMap<Vertex<T>, BTreeSet<Vertex<T>>>)
where
    T: Ord;

impl<T> Display for Graph<T>
where
    T: Copy + Display + Ord,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (vertex, adjacent) in self.0.iter() {
            write!(f, "{} => [", vertex)?;
            let mut first = true;
            for adj in adjacent {
                if !first {
                    write!(f, ", ")?;
                }
                write!(f, "{}", adj)?;
                first = false;
            }
            write!(f, "]\n")?;
        }
        Ok(())
    }
}

/// Error that can occur when inserting a vertex into the graph.
#[derive(Debug, Error)]
pub enum InsertVertexError<T>
where
    T: Debug + Ord,
{
    #[error("ERROR: The vertex `{0}` already exists.")]
    VertexExistsError(Vertex<T>),
}

/// Error that can occur when inserting an edge into the graph.
#[derive(Debug, Error)]
pub enum InsertEdgeError<T>
where
    T: Debug + Ord,
{
    #[error("ERROR: The vertex `{0}` doesn't exist.")]
    VertexNotExistsError(Vertex<T>),
    #[error("ERROR: The vertices `{0}` and `{1}` both don't exist.")]
    BothVerticesDontExistError(Vertex<T>, Vertex<T>),
    #[error("ERROR: The edge `{0}` already exists.")]
    EdgeExistError(Edge<T>),
    #[error("ERROR: Tried inserting a loop `{0}` into the graph, this is not allowed!")]
    TriedInsertEdgeLoop(Edge<T>),
}

impl<T> Graph<T>
where
    T: Copy + Debug + Ord,
{
    /// Constructs a new graph.
    pub fn new() -> Self {
        Self(BTreeMap::new())
    }

    /// Inserts a vertex into the graph.
    ///
    /// Returns an error if the vertex already exists.
    pub fn insert_vertex(&mut self, vertex: Vertex<T>) -> Result<(), InsertVertexError<T>> {
        match self.0.entry(vertex) {
            Entry::Vacant(x) => {
                let _ = x.insert(BTreeSet::new());
                Ok(())
            }
            _ => Err(InsertVertexError::VertexExistsError(vertex)),
        }
    }

    /// Checks if an edge exists.
    pub fn is_edge(&self, edge: &Edge<T>) -> bool {
        if self.is_vertex(&edge.0) && self.is_vertex(&edge.1) {
            self.0[&edge.0].contains(&edge.1) && self.0[&edge.1].contains(&edge.0)
        } else {
            false
        }
    }

    /// Checks if a vertex exists in the graph.
    pub fn is_vertex(&self, vertex: &Vertex<T>) -> bool {
        self.0.contains_key(&vertex)
    }

    /// Inserts an edge into the graph.
    ///
    /// Returns an error in these cases:
    /// - One vertex doesn't exist.
    /// - Both vertices don't exist.
    /// - The edge between these vertices already exists.
    pub fn insert_edge(&mut self, edge: Edge<T>) -> Result<(), InsertEdgeError<T>> {
        if edge.0 == edge.1 {
            Err(InsertEdgeError::TriedInsertEdgeLoop(edge))
        } else {
            match (self.is_vertex(&edge.0), self.is_vertex(&edge.1)) {
                (true, true) => {
                    if self.is_edge(&edge) {
                        Err(InsertEdgeError::EdgeExistError(edge))
                    } else {
                        self.0
                            .entry(edge.0)
                            .or_insert(BTreeSet::new())
                            .insert(edge.1);
                        self.0
                            .entry(edge.1)
                            .or_insert(BTreeSet::new())
                            .insert(edge.0);
                        Ok(())
                    }
                }
                (true, false) => Err(InsertEdgeError::VertexNotExistsError(edge.1)),
                (false, true) => Err(InsertEdgeError::VertexNotExistsError(edge.0)),
                (false, false) => Err(InsertEdgeError::BothVerticesDontExistError(edge.0, edge.1)),
            }
        }
    }

    /// Helper function for depth-first traversal.
    pub fn depth_first_vertex_recursive(
        &self,
        current_vertex: Vertex<T>,
        visited: &mut BTreeSet<Vertex<T>>,
    ) {
        if !visited.contains(&current_vertex) {
            visited.insert(current_vertex);
            for &adj_vertex in &self.0[&current_vertex] {
                self.depth_first_vertex_recursive(adj_vertex, visited);
            }
        }
    }

    /// Depth-first traversal starting from a specific vertex.
    ///
    /// ```
    /// use graph::{Graph, Vertex};
    ///
    /// let graph: Graph<usize> = Graph::new_cyclic_graph(5);
    /// let order = graph.depth_first_vertex_traversal_recursive(Vertex(0));
    /// assert_eq!(order, vec![Vertex(0), Vertex(1), Vertex(2), Vertex(3), Vertex(4)]);
    /// ```
    pub fn depth_first_vertex_traversal_recursive(
        &self,
        start_vertex: Vertex<T>,
    ) -> Vec<Vertex<T>> {
        let mut visited = BTreeSet::new();
        let mut traversal_order = Vec::new();
        self.depth_first_vertex_recursive(start_vertex, &mut visited);
        traversal_order.extend(visited);
        traversal_order
    }
}

impl Graph<usize> {
    /// Constructs a new complete graph of size: `size`.
    ///
    /// Every vertex in the range 0..size is adjacent to every other vertex.
    pub fn new_complete_graph(size: usize) -> Self {
        let mut output = Graph::new();
        for i in 0..size {
            for j in 0..i {
                output.insert_vertex(Vertex(i)).unwrap_or_else(|_| {});
                output.insert_vertex(Vertex(j)).unwrap_or_else(|_| {});
                output.insert_edge(Edge(Vertex(i), Vertex(j))).unwrap();
            }
        }
        output
    }

    /// Constructs a new bipartite graph with sizes: `size_1` and `size_2`.
    ///
    /// There are two disjoint sets of vertices: A := 0..size_1 and B := size_1..size_1+size_2.
    /// All edges between the vertices of A and B exist, but no edges exist within A or within B.
    pub fn new_bipartite_graph(size_1: usize, size_2: usize) -> Self {
        let mut output = Graph::new();
        for i in 0..size_1 {
            for j in size_1..size_1 + size_2 {
                output.insert_vertex(Vertex(i)).unwrap_or_else(|_| {});
                output.insert_vertex(Vertex(j)).unwrap_or_else(|_| {});
                output.insert_edge(Edge(Vertex(i), Vertex(j))).unwrap();
            }
        }
        output
    }

    /// Constructs a new cyclic graph of size: `size`.
    pub fn new_cyclic_graph(size: usize) -> Self {
        let mut output = Graph::new();
        for i in 0..size - 1 {
            output.insert_vertex(Vertex(i)).unwrap_or_else(|_| {});
            output.insert_vertex(Vertex(i + 1)).unwrap_or_else(|_| {});
            output.insert_edge(Edge(Vertex(i), Vertex(i + 1))).unwrap();
        }
        output
            .insert_edge(Edge(Vertex(0), Vertex(size - 1)))
            .unwrap_or_else(|_| {});
        output
    }

    /// Constructs a new path graph of size: `size`.
    pub fn new_path_graph(size: usize) -> Self {
        let mut output = Graph::new();
        for i in 0..size - 1 {
            output.insert_vertex(Vertex(i)).unwrap_or_else(|_| {});
            output.insert_vertex(Vertex(i + 1)).unwrap_or_else(|_| {});
            output.insert_edge(Edge(Vertex(i), Vertex(i + 1))).unwrap();
        }
        output
    }
}

impl<T> Mul<Graph<T>> for Graph<T>
where
    T: Copy + Debug + Display + Ord,
{
    type Output = Graph<(T, T)>;

    /// Computes the Cartesian product of two graphs.
    ///
    /// See: https://en.wikipedia.org/wiki/Cartesian_product_of_graphs
    fn mul(self, rhs: Graph<T>) -> Self::Output {
        let mut output = Graph::new();
        for (vertex_1, _adj_1) in &self.0 {
            for (vertex_2, _adj_2) in &rhs.0 {
                output
                    .insert_vertex(Vertex((vertex_1.0.clone(), vertex_2.0.clone())))
                    .unwrap_or_else(|_| {});
                output
                    .insert_vertex(Vertex((vertex_2.0.clone(), vertex_1.0.clone())))
                    .unwrap_or_else(|_| {});
            }
        }
        output
    }
}
