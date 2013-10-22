package org.kframework.backend.pdmc.automaton;

import java.util.Set;

/**
 * @author Traian
 */
public interface AutomatonInterface<State, Alphabet> {
    Set<Transition<State, Alphabet>> getTransitions(State state, Alphabet letter);
    State initialState();
    Set<State> getFinalStates();
}
