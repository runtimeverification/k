package org.kframework.backend.pdmc.pda.pautomaton.util;

import org.kframework.backend.pdmc.automaton.Transition;

import java.util.*;

/**
 * @author Traian
 */
public class IndexedTransitions<State, Alphabet> {
    Set<Transition<State, Alphabet>> rel;
    Map<State, Set<Transition<State, Alphabet>>> backIndex;
    Map<State, Set<Transition<State, Alphabet>>> directIndex;
    public IndexedTransitions() {
        rel = new HashSet<Transition<State, Alphabet>>();
        backIndex = new HashMap<State,
                Set<Transition<State, Alphabet>>>();
        directIndex = new HashMap<State,
                Set<Transition<State, Alphabet>>>();
    }

    public boolean contains(Transition<State, Alphabet> transition) {
        return  rel.contains(transition);
    }

    public Set<Transition<State, Alphabet>>
    getFrontTransitions(State index) {
        Set<Transition<State, Alphabet>> transitions = directIndex.get(index);
        if (transitions == null) transitions
                = Collections.<Transition<State, Alphabet>>emptySet();
        return transitions;
    }

    public Set<Transition<State, Alphabet>>
    getBackEpsilonTransitions(State endState) {
        Set<Transition<State, Alphabet>> transitions = backIndex.get(endState);
        if (transitions == null) transitions
                = Collections.<Transition<State, Alphabet>>emptySet();
        return transitions;
    }

    public void add(Transition<State, Alphabet> transition) {
        if (rel.contains(transition)) return;
        rel.add(transition);
        State index = transition.getStart();
        Set<Transition<State, Alphabet>> transitions = directIndex.get(index);
        if (transitions == null) {
            transitions = new HashSet<Transition<State, Alphabet>>();
            directIndex.put(index, transitions);
        }
        transitions.add(transition);
        if (!isEpsilon(transition.getLetter())) return;
        State end = transition.getEnd();
        transitions = backIndex.get(end);
        if (transitions == null) {
            transitions = new HashSet<Transition<State, Alphabet>>();
            backIndex.put(end, transitions);
        }
        transitions.add(transition);
    }

    public boolean isEpsilon(Alphabet gamma) {
       return gamma == null;
    }

    public Collection<Transition<State, Alphabet>> getTransitions() {
        return rel;
    }
}
