package org.kframework.backend.pdmc.pda.automata.util;

import org.kframework.backend.pdmc.pda.automata.State;
import org.kframework.backend.pdmc.pda.automata.Transition;
import org.kframework.backend.pdmc.pda.automata.TransitionIndex;

import java.util.*;

/**
 * @author Traian
 */
public class IndexedTransitions<Control, Alphabet> {
    Set<Transition<Control, Alphabet>> rel;
    Map<State<Control,Alphabet>, Set<Transition<Control, Alphabet>>> backIndex;
    Map<State<Control, Alphabet>, Set<Transition<Control, Alphabet>>> directIndex;

    public boolean contains(Transition<Control, Alphabet> transition) {
        return  rel.contains(transition);
    }

    public Set<Transition<Control, Alphabet>> getFrontTransitions(State<Control, Alphabet> index) {
        Set<Transition<Control, Alphabet>> transitions = directIndex.get(index);
        if (transitions == null) transitions = Collections.<Transition<Control, Alphabet>>emptySet();
        return transitions;
    }

    public Set<Transition<Control, Alphabet>> getBackEpsilonTransitions(State<Control, Alphabet> endState) {
        Set<Transition<Control, Alphabet>> transitions = backIndex.get(endState);
        if (transitions == null) transitions = Collections.<Transition<Control, Alphabet>>emptySet();
        return transitions;
    }

    public void add(Transition<Control, Alphabet> transition) {
        if (rel.contains(transition)) return;
        State<Control, Alphabet> index = transition.getStart();
        Set<Transition<Control, Alphabet>> transitions = directIndex.get(index);
        if (transitions == null) {
            transitions = new HashSet<Transition<Control, Alphabet>>();
            directIndex.put(index, transitions);
        }
        transitions.add(transition);
        if (transition.getLetter() != null) return;
        State<Control, Alphabet> end = transition.getEnd();
        transitions = backIndex.get(end);
        if (transitions == null) {
            transitions = new HashSet<Transition<Control, Alphabet>>();
            backIndex.put(end, transitions);
        }
        transitions.add(transition);
    }

    public Collection<Transition<Control, Alphabet>> getTransitions() {
        return rel;
    }
}
