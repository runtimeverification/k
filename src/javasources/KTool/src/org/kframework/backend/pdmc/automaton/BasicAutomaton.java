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
    private final Set<Alphabet> letters;


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
        this.letters = new HashSet<>();
        deltaIndex = new HashMap<TransitionIndex<State, Alphabet>,
                Set<Transition<State, Alphabet>>>();
        for (Transition<State, Alphabet> transition : delta) {
            @SuppressWarnings("unchecked")
            TransitionIndex<State, Alphabet> index = transition.getIndex();
            if(index.getLetter() != null) {
                letters.add(index.getLetter());
            }
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
        this.letters = new HashSet<>();
        for (TransitionIndex<State, Alphabet> index : deltaIndex.keySet()) {
            if (index.getLetter()!= null) {
                letters.add(index.getLetter());
            }
        }
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

    /**
     * Given an initial state, a final state and the transition relation of an automaton, find a path of transitions
     * between them
     * @param initialState the state to begin from
     * @param finalState  the final state to reach
     * @return
     */
    public Deque<Transition<State, Alphabet>> getPath(State initialState, State finalState) {
        Deque<State> toProcess = new ArrayDeque<>();
        HashMap<State, Transition<State, Alphabet>> considered = new HashMap<>();
        toProcess.add(initialState);
        considered.put(initialState, null);
        State next;
        while (!toProcess.isEmpty()) {
            next = toProcess.remove();
            for (Set<Transition<State, Alphabet>> transitions: getFrontTransitions(next)) {
                for (Transition<State, Alphabet> transition : transitions) {
                    State endState = transition.getEnd();
                    if (endState.equals(finalState)) {
                        Deque<Transition<State, Alphabet>> result = new ArrayDeque<>();
                        while (transition != null) {
                            result.push(transition);
                            transition = considered.get(transition.getStart());
                        }
                        return result;
                    }
                    if (considered.containsKey(endState)) continue;
                    considered.put(endState, transition);
                    toProcess.add(endState);
                }
            }
        }
        return null;
    }

    private Collection<Set<Transition<State, Alphabet>>> getFrontTransitions(State next) {
        ArrayList<Set<Transition<State, Alphabet>>> result = new ArrayList<>();
        for (Alphabet letter : letters) {
            Set<Transition<State, Alphabet>> transitions = getTransitions(next, letter);
            if (!transitions.isEmpty()) {
                result.add(transitions);
            }
        }
        return result;
    }
}
