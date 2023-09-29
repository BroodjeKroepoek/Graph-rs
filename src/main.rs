use std::error::Error;

use graph::Graph;

fn main() -> Result<(), Box<dyn Error>> {
    let graph: Graph<usize> = Graph::new_cyclic_graph(2);
    let graph2: Graph<usize> = Graph::new_cyclic_graph(2);
    let graph3 = graph * graph2;
    println!("{:?}", graph3);
    Ok(())
}
