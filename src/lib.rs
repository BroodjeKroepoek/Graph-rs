use std::{
    collections::{btree_map::Entry, BTreeMap, BTreeSet},
    error::Error,
    fmt::{Debug, Display},
    ops::{Index, IndexMut, Mul},
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct Vertex<T: Ord>(pub T);

impl<T: Ord + Display + Copy> Display for Vertex<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<T: Ord> From<T> for Vertex<T> {
    /// ```
    /// use graph::Graph;
    ///
    /// let mut graph: Graph<&str> = Graph::new();
    /// graph.insert_vertex("Like this!".into()).unwrap();
    /// graph.insert_vertex("Practice makes perfect!".into()).unwrap();
    /// graph.insert_edge(("Like this!", "Practice makes perfect!").into()).unwrap();
    /// assert!(graph.is_edge(("Like this!", "Practice makes perfect!").into()));
    /// ```
    fn from(value: T) -> Self {
        Self(value)
    }
}

impl<T: Ord> From<(Vertex<T>, Vertex<T>)> for Vertex<(T, T)> {
    fn from(value: (Vertex<T>, Vertex<T>)) -> Self {
        Self((value.0 .0, value.1 .0))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Edge<T: Ord>(pub Vertex<T>, pub Vertex<T>);

impl<T: Ord> From<(T, T)> for Edge<T> {
    /// ```
    /// use graph::Graph;
    ///
    /// let mut graph: Graph<&str> = Graph::new();
    /// graph.insert_vertex("Like this!".into()).unwrap();
    /// graph.insert_vertex("Practice makes perfect!".into()).unwrap();
    /// graph.insert_edge(("Like this!", "Practice makes perfect!").into()).unwrap();
    /// assert!(graph.is_edge(("Like this!", "Practice makes perfect!").into()));
    /// ```
    fn from(value: (T, T)) -> Self {
        Self(value.0.into(), value.1.into())
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Graph<T: Ord>(pub BTreeMap<Vertex<T>, Vec<Vertex<T>>>);

impl<T: Ord + Copy> Index<Vertex<T>> for Graph<T> {
    type Output = Vec<Vertex<T>>;

    /// Allows for indexing. The vertex you're indexing must exist, else panic.
    ///
    /// ```
    /// use graph::{Graph, Vertex};
    ///
    /// let mut graph: Graph<&str> = Graph::new();
    /// graph.insert_vertex(Vertex("Hello, World!")).unwrap();
    /// assert_eq!(graph[Vertex("Hello, World!")], []);
    /// ```
    fn index(&self, index: Vertex<T>) -> &Self::Output {
        &self.0.index(&index)
    }
}

impl<T: Ord + Copy> IndexMut<Vertex<T>> for Graph<T> {
    /// Allows for mutating by index. The vertex you're indexing by must exist, else panic.
    ///
    /// ```
    /// use graph::{Graph, Vertex};
    ///
    /// let mut graph: Graph<&str> = Graph::new();
    /// graph.insert_vertex(Vertex("Hello, World!"));
    /// graph[Vertex("Hello, World!")].push(Vertex("Another vertex!")); // It's better to use the api, then do this, but is possible.
    /// assert_eq!(graph[Vertex("Hello, World!")], [Vertex("Another vertex!")]);
    /// ```
    fn index_mut(&mut self, index: Vertex<T>) -> &mut Self::Output {
        if let Some(x) = self.0.get_mut(&index) {
            x
        } else {
            panic!("Vertex not present!")
        }
    }
}

/// Error that can occur when inserting a Vertex into the Graph
#[derive(Debug)]
pub enum InsertVertexError<T: Ord + Debug> {
    /// Vertex already exists in the Graph
    VertexExistsError(Vertex<T>),
}

impl<T: Copy + Ord + Debug> Display for InsertVertexError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InsertVertexError::VertexExistsError(x) => {
                write!(f, "ERROR: The vertex `{:?}` already exists.", x)
            }
        }
    }
}

/// Error that can occur when inserting an Edge into the Graph
#[derive(Debug)]
pub enum InsertEdgeError<T: Ord + Debug> {
    /// One Vertex doesn't exist
    VertexNotExistsError(Vertex<T>),
    /// Both Vertices doesn't exist
    BothVerticesNotExistError(Vertex<T>, Vertex<T>),
    /// The Edge between these Vertices already exists
    EdgeExistError(Edge<T>),
}

impl<T: Copy + Ord + Debug> Display for InsertEdgeError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InsertEdgeError::VertexNotExistsError(x) => {
                write!(f, "ERROR: The vertex `{:?}` doesn't exist.", x)
            }
            InsertEdgeError::BothVerticesNotExistError(x, y) => {
                write!(
                    f,
                    "ERROR: The vertices `{:?}` and `{:?}` both don't exist.",
                    x, y
                )
            }
            InsertEdgeError::EdgeExistError(x) => {
                write!(f, "ERROR: The edge `{:?}` already exists.", x)
            }
        }
    }
}

impl<T: Copy + Ord + Debug> Error for InsertVertexError<T> {}

impl<T: Copy + Ord + Debug> Error for InsertEdgeError<T> {}

impl<T: Ord + Debug + Copy> Graph<T> {
    /// Constructs a new Graph
    pub fn new() -> Self {
        Self(BTreeMap::new())
    }

    /// Inserts a Vertex into the Graph
    ///
    /// Returns an Error in these cases:
    /// - The Vertex already exists.
    pub fn insert_vertex(&mut self, vertex: Vertex<T>) -> Result<(), InsertVertexError<T>> {
        match self.0.entry(vertex) {
            Entry::Vacant(x) => {
                let _ = x.insert(Vec::new());
                Ok(())
            }
            _ => Err(InsertVertexError::VertexExistsError(vertex)),
        }
    }

    /// Does an Edge exists, or not?
    pub fn is_edge(&self, edge: Edge<T>) -> bool {
        self[edge.0].binary_search(&edge.1).is_ok() && self[edge.1].binary_search(&edge.0).is_ok()
    }

    /// Inserts an Edge into the Graph
    ///
    /// Returns an Error in these cases:
    /// - One Vertex doesn't exist.
    /// - Both Vertices don't exist.
    /// - The Edge between these Vertices already exists.
    pub fn insert_edge(&mut self, edge: Edge<T>) -> Result<(), InsertEdgeError<T>> {
        match (self.0.contains_key(&edge.0), self.0.contains_key(&edge.1)) {
            (true, true) => {
                match (
                    self[edge.0].binary_search(&edge.1),
                    self[edge.1].binary_search(&edge.0),
                ) {
                    (Ok(_x), Ok(_y)) => Err(InsertEdgeError::EdgeExistError(edge)),
                    (Err(_x), Err(_y)) => {
                        let adj_to_0 = &mut self[edge.0];
                        adj_to_0.push(edge.1);
                        let adj_to_1 = &mut self[edge.1];
                        adj_to_1.push(edge.0);
                        Ok(())
                    }
                    _ => unreachable!(),
                }
            }
            (true, false) => Err(InsertEdgeError::VertexNotExistsError(edge.1)),
            (false, true) => Err(InsertEdgeError::VertexNotExistsError(edge.0)),
            (false, false) => Err(InsertEdgeError::BothVerticesNotExistError(edge.0, edge.1)),
        }
    }

    /// Helper function for depth-first traversal
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

    /// Depth-first traversal starting from a specific vertex
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
    /// Constructs a new complete Graph of size: `size`
    ///
    /// Every vertex in 0..size is adjacent to every other vertex
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

    /// Constructs a new bipartite Graph of sizes: `size_1` and `size_2`
    ///
    /// There are two disjoint ranges A := 0..size_1 and B := size_1..size_1+size_2
    /// All Edges between the vertices of A and B exist, but no Edges exist inside A itself and inside B itself.
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

    /// Constructs a new cyclic Graph of size: `size`
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
}

impl<T: Ord + Display + Copy> Display for Graph<T> {
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

impl<T: Ord + Debug + Copy + Display> Mul<Graph<T>> for Graph<T> {
    type Output = Graph<(T, T)>;

    fn mul(self, rhs: Graph<T>) -> Self::Output {
        let mut output = Graph::new();
        for (vertex_1, _adj_1) in &self.0 {
            for (vertex_2, _adj_2) in &rhs.0 {
                output
                    .insert_vertex((vertex_1.0.clone(), vertex_2.0.clone()).into())
                    .unwrap_or_else(|_| {});
                output
                    .insert_vertex((vertex_2.0.clone(), vertex_1.0.clone()).into())
                    .unwrap_or_else(|_| {});
            }
        }
        output
    }
}
