use std::error::Error;

use lib::{Graph, Vertex};

fn main() -> Result<(), Box<dyn Error>> {
    let graph: Graph<usize> = Graph::new_cyclic_graph(50);
    let order = graph.depth_first_vertex_traversal_recursive(Vertex(0));
    println!("{:?}", order);
    Ok(())
}
