module tour/addressBook1

sig Name, Addr {}
sig Book {addr: Name -> lone Addr}

pred show (b: Book) {
    #b.addr > 1
    #Name.(b.addr) > 1
}

// The command specifies a scope that bounds the search for instances: in this
// case, to at most three objects in each signature, except for Book, which is
// limited to one object
run show for 3 but 1 Book

pred add (b, b_ : Book, n: Name, a: Addr) {b_.addr = b.addr + n -> a}
pred del (b, b_ : Book, n: Name) {b_.addr = b.addr - n -> Addr}

// The lookup is operation is written as a function rather than a predicate:
// its body is an expression rather than a constarint, and says that the result
// of a lookup is whatever set of addressses the name n maps to under the addr
// mapping of b
fun lookup (b: Book, n: Name): set Addr {n.(b.addr)}

pred showAdd (b, b_: Book, n: Name, a: Addr) {
    add [b, b_, n, a]
    #Name.(b'.addr) > 1
}
run showAdd for 3 but 2 Book

// del undoes add: if no entry already exists for the name n, we add it and then
// delete it, then the b_ is equial to b__
assert delUndoesAdd {
    all b,b_, b__: Book, n: Name, a: Addr |
        no n.(b.addr) and
        add [b,b_,n,a] and del [b_,b__,n] implies b.addr = b__.addr
}

// add is idempotents: repeating an addition has no effect
assert addIdempotent {
all b,b_,b__: Book, n: Name, a: Addr |
            add [b,b_,n,a] and add [b_,b__,n,a] implies b_.addr = b__.addr
}

// add is local: adding an entry for a name n doesn't affect the result of
// a lookup for a different name n_
assert addLocal {
    all b,b_: Book, n,n_: Name, a: Addr |
        add [b,b_,n,a] and n != n_
            implies lookup [b,n_] = lookup [b_,n_]
}

check delUndoesAdd for 10 but 3 Book
check addIdempotent for 3
check addLocal for 3 but 2 Book