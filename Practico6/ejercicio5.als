sig Elem { }

sig BinaryR {
    elems: set Elem,
    tuples: elems -> elems
}

pred preOrder [r: BinaryR] {
    // Reflexividad
    (iden & (Elem -> Elem)) in r.tuples
    // Transitividad
    (r.tuples).(r.tuples) in r.tuples
}

pred partialOrder [r: BinaryR] {
    preOrder[r]
    // Antisimetría
    (r.tuples) & ~(r.tuples) in (iden & (Elem -> Elem))
}

pred totalOrder [r: BinaryR] {
    partialOrder[r]
    // Todos los elementos están relacionados
    r.tuples + ~(r.tuples) = (Elem -> Elem)
}

pred strictOrder [r: BinaryR] {
    // R no es reflexiva
    no (iden & (Elem -> Elem)) & r.tuples
    // Transitividad
    (r.tuples).(r.tuples) in r.tuples
    // Antisimetría
    (r.tuples) & ~(r.tuples) in (iden & (Elem -> Elem))
}

pred hasFirst [r: BinaryR] {
    some e: Elem | r.tuples[e] = r.elems
}

pred hasLast [r: BinaryR] {
    some e: Elem | (~(r.tuples))[e] = r.elems
}
