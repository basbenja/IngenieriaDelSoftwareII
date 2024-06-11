sig State { }
sig Action { }

sig LTS {
    states: set State,
    actions: set Action,
    initial: one states,
    transitions: states -> actions -> states
}