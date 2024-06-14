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
}{
    // all s: songs | some i: interpreters | (s -> i) in interpretations
    // all i: interpreters | some s: songs | (i -> s) in ~interpretations
    interpretations.interpreters = songs
    (~interpretations).songs = interpreters
}

pred addInterpretation[c_in, c_out: Catalog, s: Song, i: Interpreter] {
    c_out.interpretations = c_in.interpretations + (s -> i)
    // Las dos líneas que siguen no son necesarias porque el fact dado sobre los
    // catálogos ya me asegura que al cambiar interpretations, también me va a
    // cambiar songs e interpreters
    // c_out.songs = c_in.songs + s
    // c_out.interpreters = c_in.interpreters + i
}

pred deleteInterpretation[c_in, c_out: Catalog, s: Song, i: Interpreter] {
    c_out.interpretations = c_in.interpretations - (s -> i)
    // Las dos líneas que siguen no son necesarias porque el fact dado sobre los
    // catálogos ya me asegura que al cambiar interpretations, también me va a
    // cambiar songs e interpreters
    // c_out.songs = (c_out.interpretations).univ
    // c_out.interpreters = univ.(c_out.interpretations)
}

pred addSong[c_in, c_out: Catalog, s: Song] {
    c_out.songs = c_in.songs + s
    // En el catálogo resultante, me quedaría una canción sin intérprete.
    // Pero tenemos un fact sobre los catálogos que dice que esto no puede pasar!
    // Entonces, supongamos que "aplicamos" este predicado sobre un catálogo vacío
    // ¿Esto falla o "devuelve" un catálogo vacío? (para poder asegurar el fact)
    // Ninguna de las dos, lo que hace es "inventar" uno o más intérpretes. Esto lo
    // hace porque en el predicado no estamos diciendo quién tiene que ser
    // c_out.interpreters
    // Si en cambio a este predicado le hubieramos agregado la línea:
    // c_out.interpreters = c_in.interpeters
    // c_out.interpretations = c_in.interpretations
    // entonces en este caso el predicado es instatisfactible
}
run addSong for 1 but exactly 1 Catalog

fun sameSong[c: Catalog] : (c.interpreters -> c.interpreters) {
    { (~(c.interpretations)).(c.interpretations) }
}
