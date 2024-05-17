open util/ordering[State]

abstract sig Object {
    eats: set Object
}

one sig Farmer, Fox, Chicken, Grain
    extends Object {}

fact eating {
    eats = Fox -> Chicken + Chicken -> Grain
}

sig State {
    near: set Object,
    far: set Object
}

fact initialState {
    let s0 = first[] |
        s0.near = Object && no s0.far
}

// Cambios de estados
pred CrossRiver[from_i, from_o, to_i, to_o: set Object]{
    // Se va el granjero solo
    (
        from_o = from_i - Farmer - from_i.eats &&
        to_o = to_i + Farmer
    )
    ||
    // Se va el granjero con alguno de los objetos
    (
        some item: from_i |
            from_o = from_i - Farmer - item - (from_i - item).eats &&
            to_o = to_i + Farmer + item
    )
}

// Transiciones entre estados
fact stateTransitions {
    all s0: State, s1: next[s0] |
        Farmer in s0.near => CrossRiver[s0.near, s1.near, s0.far, s1.far]
        &&
        Farmer in s0.far => CrossRiver[s0.far, s1.far, s0.near, s1.near]
}

pred solvePuzzle[] {
    last[].far = Object
}

run solvePuzzle for 8 State