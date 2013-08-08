package org.kframework.backend.pdmc.pda.automata;


import java.util.HashMap;
import java.util.Map;

/**
 * @author Traian
 */
public class Transition<Control, Alphabet> {
    private static Map<TransitionIndex, Map<State, Transition>> cache;
    private final State<Control, Alphabet> startState;

    public State<Control, Alphabet> getEnd() {
        return endState;
    }

    private final State<Control, Alphabet> endState;

    public Alphabet getLetter() {
        return letter;
    }

    private final Alphabet letter;

    private Transition(State<Control, Alphabet> startState, Alphabet letter, State<Control, Alphabet> endState) {
        this.startState = startState;
        this.endState = endState;
        this.letter = letter;
    }

    public static <Control,Alphabet> Transition<Control, Alphabet> of(State<Control, Alphabet> startState,
                                                                      Alphabet letter,
                                                                      State<Control, Alphabet> endState) {
        if (cache == null) cache = new HashMap<TransitionIndex, Map<State, Transition>>();
        TransitionIndex<Control, Alphabet> index = TransitionIndex.of(startState, letter);
        Map<State,Transition> map = cache.get(index);
        if (map == null) {
            map = new HashMap<State, Transition>();
            cache.put(index, map);
        }
        Transition<Control, Alphabet> transition = (Transition<Control, Alphabet>) map.get(endState);
        if (transition == null) {
            transition = new Transition<Control, Alphabet>(startState, letter, endState);
            map.put(endState, transition);
        }
        return transition;
    }

    public State<Control,Alphabet> getStart() {
        return startState;
    }

    public TransitionIndex<Control, Alphabet> getIndex() {
        return TransitionIndex.<Control, Alphabet>of(startState, letter);
    }

    public static Transition<String, String> of(String transitionString) {
        String[] strings = transitionString.split("\\s+");
        assert strings.length == 3 || strings.length == 2;
        State<String,String> startState = State.ofString(strings[0]);
        int i = 1;
        String letter = null;
        if (strings.length == 3) {
            letter = strings[i++];
        }
        State<String,String> endState = State.ofString(strings[i]);
        return new Transition<String, String>(startState, letter, endState);
    }

    @Override
    public String toString() {
        return startState + " " + (letter != null ? letter + " " : "") + endState;
    }
}
