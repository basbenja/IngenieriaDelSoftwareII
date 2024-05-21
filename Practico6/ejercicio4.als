sig Node { }

sig Graph {
    edges: Node -> Node
}

pred acyclic [g: Graph] {
    no (^(g.edges) & iden)
}

pred notDirected [g: Graph] {
    g.edges = ~(g.edges)
}

pred stronglyConnected [g: Graph] {
    ^(g.edges) = (Node -> Node)
}

pred connected [g: Graph] {
    ^(g.edges + ~(g.edges)) = (Node -> Node)
}

pred stronglyConnectedComponent [g: Graph] {

}

pred connectedComponent [g: Graph] {

}