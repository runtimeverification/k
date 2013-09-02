package org.kframework.backend.pdmc.pda.pautomaton.util;

import org.kframework.backend.pdmc.pda.pautomaton.PAutomatonState;
import org.kframework.backend.pdmc.automaton.Transition;

import java.util.*;

/**
 * @author Traian
 */
public class IndexedTransitions<Control, Alphabet> {
    Set<Transition<PAutomatonState<Control, Alphabet>, Alphabet>> rel;
    Map<PAutomatonState<Control,Alphabet>, Set<Transition<PAutomatonState<Control, Alphabet>, Alphabet>>> backIndex;
    Map<PAutomatonState<Control, Alphabet>, Set<Transition<PAutomatonState<Control, Alphabet>, Alphabet>>> directIndex;
    public IndexedTransitions() {
        rel = new HashSet<Transition<PAutomatonState<Control, Alphabet>, Alphabet>>();
        backIndex = new HashMap<PAutomatonState<Control, Alphabet>,
                Set<Transition<PAutomatonState<Control, Alphabet>, Alphabet>>>();
        directIndex = new HashMap<PAutomatonState<Control, Alphabet>,
                Set<Transition<PAutomatonState<Control, Alphabet>, Alphabet>>>();
    }

    public boolean contains(Transition<PAutomatonState<Control, Alphabet>, Alphabet> transition) {
        return  rel.contains(transition);
    }

    public Set<Transition<PAutomatonState<Control, Alphabet>, Alphabet>>
    getFrontTransitions(PAutomatonState<Control, Alphabet> index) {
        Set<Transition<PAutomatonState<Control, Alphabet>, Alphabet>> transitions = directIndex.get(index);
        if (transitions == null) transitions
                = Collections.<Transition<PAutomatonState<Control, Alphabet>, Alphabet>>emptySet();
        return transitions;
    }

    public Set<Transition<PAutomatonState<Control, Alphabet>, Alphabet>>
    getBackEpsilonTransitions(PAutomatonState<Control, Alphabet> endState) {
        Set<Transition<PAutomatonState<Control, Alphabet>, Alphabet>> transitions = backIndex.get(endState);
        if (transitions == null) transitions
                = Collections.<Transition<PAutomatonState<Control, Alphabet>, Alphabet>>emptySet();
        return transitions;
    }

    public void add(Transition<PAutomatonState<Control, Alphabet>, Alphabet> transition) {
        if (rel.contains(transition)) return;
        rel.add(transition);
        PAutomatonState<Control, Alphabet> index = transition.getStart();
        Set<Transition<PAutomatonState<Control, Alphabet>, Alphabet>> transitions = directIndex.get(index);
        if (transitions == null) {
            transitions = new HashSet<Transition<PAutomatonState<Control, Alphabet>, Alphabet>>();
            directIndex.put(index, transitions);
        }
        transitions.add(transition);
        if (transition.getLetter() != null) return;
        PAutomatonState<Control, Alphabet> end = transition.getEnd();
        transitions = backIndex.get(end);
        if (transitions == null) {
            transitions = new HashSet<Transition<PAutomatonState<Control, Alphabet>, Alphabet>>();
            backIndex.put(end, transitions);
        }
        transitions.add(transition);
    }

    public Collection<Transition<PAutomatonState<Control, Alphabet>, Alphabet>> getTransitions() {
        return rel;
    }
}
