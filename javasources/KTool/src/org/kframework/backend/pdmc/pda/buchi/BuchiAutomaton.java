package org.kframework.backend.pdmc.pda.buchi;

import org.kframework.backend.pdmc.automaton.BasicAutomaton;
import org.kframework.backend.pdmc.automaton.Transition;
import org.kframework.backend.pdmc.automaton.TransitionIndex;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

/**
 * @author Traian
 */
public class BuchiAutomaton<Control, Atom> extends BasicAutomaton<Control, Set<Atom>> {

    public BuchiAutomaton(Collection<Transition<Control, Set<Atom>>> delta, Control initialState, Collection<Control> finalStates) {
        super(delta, initialState, finalStates);
    }

    public BuchiAutomaton(Map<TransitionIndex<Control, Set<Atom>>, Set<Transition<Control, Set<Atom>>>> deltaIndex, Control initialState, Set<Control> finalStates) {
        super(deltaIndex, initialState, finalStates);
    }
}
