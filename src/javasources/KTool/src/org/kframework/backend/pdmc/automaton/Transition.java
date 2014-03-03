package org.kframework.backend.pdmc.automaton;


import org.kframework.backend.pdmc.pda.pautomaton.PAutomatonState;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Traian
 */
public class Transition<State, Alphabet> {
    private static Map<TransitionIndex, Map<Object, Transition>> cache;
    private final State startState;

    public State getEnd() {
        return endState;
    }

    private final State endState;

    public Alphabet getLetter() {
        return letter;
    }

    private final Alphabet letter;

    protected Transition(State startState, Alphabet letter, State endState) {
        this.startState = startState;
        this.endState = endState;
        this.letter = letter;
    }

    public static <State,Alphabet> Transition<State, Alphabet> of(State startState,
                                                                      Alphabet letter,
                                                                      State endState) {
        if (cache == null) cache = new HashMap<>();
        TransitionIndex<State, Alphabet> index = TransitionIndex.of(startState, letter);
        Map<Object, Transition> map = cache.get(index);
        if (map == null) {
            map = new HashMap<>();
            cache.put(index, map);
        }
        @SuppressWarnings("unchecked")
        Transition<State, Alphabet> transition = (Transition<State, Alphabet>) map.get(endState);
        if (transition == null) {
            transition = new Transition<>(startState, letter, endState);
            map.put(endState, transition);
        }
        return transition;
    }

    public State getStart() {
        return startState;
    }

    public TransitionIndex getIndex() {
        return TransitionIndex.of(startState, letter);
    }

    public static Transition<PAutomatonState<String, String>, String> of(String transitionString) {
        String[] strings = transitionString.split("\\s+");
        assert strings.length == 3 || strings.length == 2;
        PAutomatonState<String,String> startState = PAutomatonState.ofString(strings[0]);
        int i = 1;
        String letter = null;
        if (strings.length == 3) {
            letter = strings[i++];
        }
        PAutomatonState<String,String> endState = PAutomatonState.ofString(strings[i]);
        return new Transition<>(startState, letter, endState);
    }

    @Override
    public String toString() {
        return startState + " " + (letter != null ? letter + " " : "") + endState;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Transition that = (Transition) o;

        if (!endState.equals(that.endState)) return false;
        if (letter != null ? !letter.equals(that.letter) : that.letter != null) return false;
        if (!startState.equals(that.startState)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        int result = startState.hashCode();
        result = 31 * result + endState.hashCode();
        result = 31 * result + (letter != null ? letter.hashCode() : 0);
        return result;
    }
}
