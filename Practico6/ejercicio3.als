sig Addr, Data { }

sig Memory {
    addrs: set Addr,
    // lone = a lo sumo uno (o sea, uno o ninguno)
    map: addrs -> lone Data
}

sig MainMemory extends Memory { }

sig Cache extends Memory {
    dirty: set addrs
}

sig System {
    cache: Cache,
    main: MainMemory
}

// Restricción que asegura que la memoria cache no direcciona fuera de la
// memoria principal
fact {
    all s:System | s.cache.addrs in s.main.addrs
}

// La idea es que el Write se va a hacer siempre sobre la cache
// El único momento en que se hace un Write sobre la memoria es cuando se hace
// un Flush sobre la cache
pred Write[m_i, m_o: Memory, a: Addr, d : Data] {
    m_o.map = m_i.map ++ (a -> d)
}

// La idea es que el Read se va a hacer siempre sobre la cache
pred Read[d_o: Data, m: Memory, a: Addr] {
    d_o = m.map[a]
}

// Lo que hace el Flush es limpiar es las direcciones dirty escribirlas en la
// memoria y vaciar el conjunto de direcciones dirty
pred Flush[s_i, s_o: System] {
    all a: s_i.cache.dirty |
        Write[s_i.main, s_o.main, a, s_i.cache.map[a]]
    && s_o.cache.dirty = none
}


// Lo que hace el Load es: al hacer un miss sobre la cache (i.e. no tiene en la
// cache la direccion que se quiere leer), la busca a la memoria principal
pred Load[] {

}

pred Consistent [s: System] {
    s.cache.map - (s.cache.dirty -> Data) in s.main.map
}
