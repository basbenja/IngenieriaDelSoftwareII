sig Node { }{
    some g: Graph | Node in g.nodes
}

sig Graph {
    nodes: set Node,
    edges: nodes -> nodes
}

pred Acyclic [g: Graph] {
    no (^(g.edges) & iden)
}

pred NotDirected [g: Graph] {
    g.edges = ~(g.edges)
}

pred StronglyConnected [g: Graph] {
    ^(g.edges) = (g.nodes -> g.nodes)
}

pred Connected [g: Graph] {
    *(g.edges + ~(g.edges)) = (Node -> Node)
}

pred StronglyConnectedComponent [g: Graph] {
    some gIn: Graph |
        (gIn.nodes in g.nodes) &&
        (gIn.edges in g.edges) &&
        StronglyConnected[gIn]
}
run StronglyConnectedComponent for 2 but exactly 1 Graph

pred connectedComponent [g: Graph] {
    some gIn: Graph |
        (gIn.nodes in g.nodes) &&
        (gIn.edges in g.edges) &&
        Connected[gIn]
}