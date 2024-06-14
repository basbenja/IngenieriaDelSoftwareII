sig State { }
sig Action { }

sig LTS {
    states: set State,
    actions: set Action,
    initial: one states,
    transitions: states -> actions -> states
}{
    (initial -> states) in ^(transitions[actions])
}

sig Relation {
    tuples: State -> State
}

pred Simulation[lts1, lts2: LTS, r: Relation] {

}

pred Bisimulation[lts1, lts2: LTS, r: Relation] {
    
}

pred WeakBisimulation[lts1, lts2: LTS, r: Relation] {
    
}
