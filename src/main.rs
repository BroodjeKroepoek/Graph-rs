use std::error::Error;

use graph::{Edge, Graph, Vertex};

fn main() -> Result<(), Box<dyn Error>> {
    let mut graph: Graph<&str> = Graph::new();
    graph.insert_vertex(Vertex("First"))?;
    graph.insert_vertex(Vertex("Second"))?;
    graph.insert_vertex(Vertex("Third"))?;
    graph.insert_edge(Edge(Vertex("First"), Vertex("Second")))?;
    println!("{}", graph);
    Ok(())
}
