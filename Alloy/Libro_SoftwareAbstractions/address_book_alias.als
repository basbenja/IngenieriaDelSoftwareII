module tour/addressBook2

abstract sig Target {}

// A target is either just an address, as before, or a name itself
sig Addr extends Target {}
abstract sig Name extends Target {}

// names are either groups or aliases
sig Alias, Group extends Name {}

sig Book {
    names: set Name,
    // addr maps only names in the set `names`, and maps each to at least one target
    addr: names -> some Target
}
{
    // For any book, there is no name that belongs to the set of targets reachable
    // from the name itself
    // The expression n.^(b.addr) denotes the targets reachable from n, using
    // the transitive closure ^(b.addr) of the address book mapping of b.
    no n: Name | n in n.^(addr)
    // We want alias to be mapped to at most one address
    all a: Alias | lone a.addr
}

// If we ask to see a non-empty book
pred show (b: Book) {some b.addr}

pred add (b_i, b_o: Book, n: Name, t: Target) {b_o.addr = b_i.addr + n -> t}
pred del (b_i, b_o: Book, n: Name, t: Target) {b_o.addr = b_i.addr - n -> t}
fun lookup (b: Book, n: Name): set Addr {n.^(b.addr) & Addr}

// Every lookup for a name in the book yields some results:
assert lookupYields {
    all b: Book, n: b.names | some lookup [b, n]
}

run show for 3 but 1 Book