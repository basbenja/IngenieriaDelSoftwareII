sig Addr, Data { }

sig Memory {
    addrs: set Addr,
    map: addrs -> lone Data
}

sig MainMemory extends Memory { }

sig Cache extends Memory {
    dirty: set addrs
}

sig System {
    cache: Cache,
    main: MainMemory
}{
    cache.addrs in main.addrs
}


// Predicados Auxiliares
pred WriteMain[m_i, m_o: MainMemory, a: Addr, d: Data] {
    m_o.map = m_i.map ++ (a -> d)
}

pred ReadMain[m: MainMemory, a: Addr, d_o: Data] {
    // Se hace de esta forma porque en una dirección puede no haber un dato
    // some d se hace verdadero si d no es "nada"
    let d = m.map[a] | some d implies d_o = m.map[a]
}


// Predicados para Sistemas
pred Write[s_i, s_o: System, a: Addr, d: Data] {
    s_o.cache.map = s_i.cache.map ++ (a -> d)
    s_o.cache.dirty = s_i.cache.dirty + a
}

pred Read[s: System, a: Addr, d_o: Data] {
    // Se hace de esta forma porque en una dirección puede no haber un dato
    // some d se hace verdadero si d no es "nada"
    let d = s.cache.map[a] | some d implies d_o = s.cache.map[a]
}

pred Flush[s_i, s_o: System] {
    all a: s_i.cache.dirty | some d: Data |
        Read[s_i, a, d] &&
        WriteMain[s_i.main, s_o.main, a, d]
    s_o.cache.dirty = none
}

// Al hacer un miss sobre la cache (i.e. no tiene en la cache la direccion que
// se quiere leer), la busca a la memoria principal y la escribe en la cache
pred Load[s_i, s_o: System, a: Addr] {
    !(a in s_i.cache.addrs)
    some d: Data |
        ReadMain[s_i.main, a, d] &&
        Write[s_i, s_o, a, d]
    s_o.main = s_i.main
}


// Predicado de Consistencia
pred Consistent [s: System] {
    // Se fija que el map de la cache sea igual al map de la principal excepto
    // por aquellas direcciones que están dirty
    s.cache.map - (s.cache.dirty -> Data) in s.main.map
}


// Aserciones para verificar que las operaciones preservan Consistencia
assert WriteAndConsistent {
    all s_i, s_o: System, a: Addr, d: Data |
        (Consistent[s_i] && Write[s_i, s_o, a, d]) implies Consistent[s_i]
}
check WriteAndConsistent for 3 but exactly 1 System, 2 Memory

assert ReadAndConsistent {
    all s_i: System, d: Data, a: Addr |
        (Consistent[s_i] && Read[s_i, a, d]) implies Consistent[s_i]
}
check ReadAndConsistent for 3 but exactly 1 System, 2 Memory

assert FlushAndConsistent {
    all s_i, s_o: System |
        (Consistent[s_i] && Flush[s_i, s_o]) implies Consistent[s_i]
}
check FlushAndConsistent for 3 but exactly 1 System, 2 Memory

assert LoadAndConsistent {
    all s_i, s_o: System, a: Addr |
        (Consistent[s_i] && Load[s_i, s_o, a]) implies Consistent[s_i]
}
check LoadAndConsistent for 3 but exactly 1 System, 2 Memory