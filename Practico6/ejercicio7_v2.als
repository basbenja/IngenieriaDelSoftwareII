sig Interpreter { }{
    some c: Catalog | Interpreter in c.interpreters
}
sig Song { }{
    some c: Catalog | Song in c.songs
}

sig Catalog {
    songs: set Song,
    interpreters: set Interpreter,
    interpretations: songs -> interpreters
}

pred consistent[c: Catalog] {
    (c.interpretations).(c.interpreters) = c.songs
    (~(c.interpretations)).(c.songs) = c.interpreters
}

pred addInterpretation[c_in, c_out: Catalog, s: Song, i: Interpreter] {
    c_out.interpretations = c_in.interpretations + (s -> i)
    c_out.songs = c_in.songs + s
    c_out.interpreters = c_in.interpreters + i
}

assert addIsConsistent {
    all c_in, c_out: Catalog, s: Song, i: Interpreter |
        (consistent[c_in] && addInterpretation[c_in, c_out, s, i]) implies consistent[c_out]
}

pred deleteInterpretation[c_in, c_out: Catalog, s: Song, i: Interpreter] {
    c_out.interpretations = c_in.interpretations - (s -> i)
    // c_out.songs = (c_out.interpretations).univ
    // c_out.songs = (c_out.interpretations).Interpreter
    // c_out.interpreters = univ.(c_out.interpretations)
    // c_out.interpreters = (c_out.interpretations)[Song]
    s = c_in.interpretations.i implies c_out.interpreters = c_in.interpreters - i
    s != c_in.interpretations.i implies c_out.interpreters = c_in.interpreters
    i = (c_in.interpretations)[s] implies c_out.songs = c_in.songs - s
    i != (c_in.interpretations)[s] implies c_out.songs = c_in.songs
}

assert deleteIsConsistent {
    all c_in, c_out: Catalog, s: Song, i: Interpreter |
        (consistent[c_in] && deleteInterpretation[c_in, c_out, s, i]) implies consistent[c_out]
}
check deleteIsConsistent for 3 but exactly 2 Catalog

pred addSong[c_in, c_out: Catalog, s: Song] {
    c_out.songs = c_in.songs + s
    c_out.interpreters = c_in.interpreters
    c_out.interpretations = c_in.interpretations
}
run addSong for 3 but exactly 2 Catalog

assert addSongIsConsistent {
    all c_in, c_out: Catalog, s: Song |
        (consistent[c_in] && addSong[c_in, c_out, s]) implies consistent[c_out]
}
check addSongIsConsistent for 3 but exactly 2 Catalog


fun sameSong[c: Catalog] : (c.interpreters -> c.interpreters) {
    { (~(c.interpretations)).(c.interpretations) }
}
