package org.kframework.backend.pdmc.pda.automata;

import java.util.*;

/**
 * @author Traian
 */
public class Automata<Control, Alphabet> {
    private final Map<TransitionIndex<Control, Alphabet>, Set<Transition<Control, Alphabet>>> deltaIndex;

    public Set<State<Control, Alphabet>> getFinalStates() {
        return finalStates;
    }

    private final Set<State<Control, Alphabet>> finalStates;

    public Automata(Collection<Transition<Control, Alphabet>> delta, Set<State<Control, Alphabet>> finalStates) {
        this.finalStates = finalStates;
        deltaIndex = new HashMap<TransitionIndex<Control, Alphabet>, Set<Transition<Control, Alphabet>>>();
        for (Transition<Control, Alphabet> transition : delta) {
            TransitionIndex<Control, Alphabet> index = transition.getIndex();
            Set<Transition<Control, Alphabet>> transitions = deltaIndex.get(index);
            if (transitions == null) {
                transitions = new HashSet<Transition<Control, Alphabet>>();
                deltaIndex.put(index, transitions);
            }
            transitions.add(transition);
        }

    }

    public Automata(Map<TransitionIndex<Control, Alphabet>, Set<Transition<Control, Alphabet>>> deltaIndex, Set<State<Control, Alphabet>> finalStates) {
        this.deltaIndex = deltaIndex;
        this.finalStates = finalStates;
    }

    public Collection<Set<Transition<Control, Alphabet>>> getTransitions() {
        return deltaIndex.values();
    }
}
