sig Elem { }

sig BinaryR {
    elems: set Elem,
    tuples: elems -> elems
}

pred reflexive[r: BinaryR] {
    (iden & (r.elems -> r.elems)) in r.tuples
}
pred transitive[r: BinaryR] {
    (r.tuples).(r.tuples) in r.tuples
}
pred antisymmetric[r: BinaryR] {
    (r.tuples) & ~(r.tuples) in (iden & (r.elems -> r.elems))
}

pred preOrder [r: BinaryR] {
    reflexive[r] && transitive[r]
}

pred partialOrder [r: BinaryR] {
    preOrder[r] && antisymmetric[r]
}

pred totalOrder [r: BinaryR] {
    partialOrder[r]
    // Todos los elementos están relacionados
    r.tuples + ~(r.tuples) = (r.elems -> r.elems)
}

pred strictOrder [r: BinaryR] {
    not reflexive[r] && transitive[r] && antisymmetric[r]
}

pred isFirst [r: BinaryR, e: Elem] {
    r.tuples[e] = r.elems
}
pred hasFirst [r: BinaryR] {
    some e: r.elems | isFirst[r, e]
}

pred isLast [r: BinaryR, e: Elem] {
    (~(r.tuples))[e] = r.elems
}
pred hasLast [r: BinaryR] {
    some e: r.elems | isLast[r, e]
}
run hasLast for 6 but exactly 1 BinaryR

assert partialIsTotal {
    all r: BinaryR |
        partialOrder[r] implies totalOrder[r]
}

assert partialHasFirst {
    all r: BinaryR |
        partialOrder[r] implies hasFirst[r]
}

assert totalHasFirstAndLast {
    all r: BinaryR | some x, y: Elem |
        (totalOrder[r] && isFirst[r, x] && isLast[r, y]) implies x != y
}

pred union[r_i1, r_i2, r_out: BinaryR] {
    r_out.elems = r_i1.elems + r_i2.elems
    r_out.tuples = r_i1.tuples + r_i2.tuples
}
assert strictUnionIsStrict {
    all r1, r2, r3: BinaryR |
        (strictOrder[r1] && strictOrder[r2] && union[r1, r2, r3])
            implies strictOrder[r3]
}

pred composition[r_i1, r_i2, r_out: BinaryR] {
    r_out.tuples = (r_i1.tuples).(r_i2.tuples)
    r_out.elems = (r_out.tuples).univ
}
run composition for 3 but exactly 3 BinaryR

assert strictCompositionIsStrict {
    all r1, r2, r3: BinaryR |
        (strictOrder[r1] && strictOrder[r2] && composition[r1, r2, r3])
            implies strictOrder[r3]
}