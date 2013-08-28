package org.kframework.backend.pdmc.automaton;

import com.google.common.base.Joiner;
import org.kframework.backend.pdmc.automaton.AutomatonInterface;
import org.kframework.backend.pdmc.automaton.Transition;
import org.kframework.backend.pdmc.automaton.TransitionIndex;

import java.util.*;

/**
 * @author Traian
 */
public class BasicAutomaton<State, Alphabet> implements AutomatonInterface<State, Alphabet> {
    private final Map<TransitionIndex<State, Alphabet>,
                Set<Transition<State, Alphabet>>> deltaIndex;
    private final State initialState;
    private final Set<State> finalStates;


    @Override
    public Set<Transition<State, Alphabet>> getTransitions(State state, Alphabet letter) {
        Set<Transition<State, Alphabet>> transitions = deltaIndex.get(
                TransitionIndex.<State, Alphabet>of(state, letter) );
        if (transitions == null) transitions =
                Collections.<Transition<State, Alphabet>>emptySet();
        return transitions;
    }

    @Override
    public State initialState() {
        return initialState;
    }

    @Override
    public Set<State> getFinalStates() {
        return finalStates;
    }

    public BasicAutomaton(Collection<Transition<State, Alphabet>> delta,
                          State initialState,
                          Collection<State> finalStates) {
        this.initialState = initialState;
        this.finalStates = new HashSet<State>(finalStates);
        deltaIndex = new HashMap<TransitionIndex<State, Alphabet>,
                Set<Transition<State, Alphabet>>>();
        for (Transition<State, Alphabet> transition : delta) {
            @SuppressWarnings("unchecked")
            TransitionIndex<State, Alphabet> index = transition.getIndex();
            Set<Transition<State, Alphabet>> transitions = deltaIndex.get(index);
            if (transitions == null) {
                transitions = new HashSet<Transition<State, Alphabet>>();
                deltaIndex.put(index, transitions);
            }
            transitions.add(transition);
        }

    }

    public BasicAutomaton(Map<TransitionIndex<State, Alphabet>, Set<Transition<State, Alphabet>>> deltaIndex,
                          State initialState,
                          Set<State> finalStates) {
        this.deltaIndex = deltaIndex;
        this.initialState = initialState;
        this.finalStates = finalStates;
    }

    public Collection<Set<Transition<State, Alphabet>>> getTransitions() {
        return deltaIndex.values();
    }
 
    @Override
    public String toString() {
        Joiner joiner = Joiner.on(";\n");
        List<StringBuilder> builders = new ArrayList<StringBuilder>();
        for (Set<Transition<State, Alphabet>> transitions : deltaIndex.values()) {
            StringBuilder builder = new StringBuilder();
            joiner.appendTo(builder, transitions);
            builders.add(builder);
        }
        builders.add(new StringBuilder(initialState.toString()));
        Joiner joiner1 = Joiner.on(" ");
        StringBuilder builder = new StringBuilder();
        joiner1.appendTo(builder, finalStates);
        builders.add(builder);
        builder = new StringBuilder();
        joiner.appendTo(builder, builders);
        return builder.toString();
    }
}
