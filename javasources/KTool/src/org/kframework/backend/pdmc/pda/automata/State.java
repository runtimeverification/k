package org.kframework.backend.pdmc.pda.automata;

import org.kframework.backend.java.symbolic.Utils;

import java.util.HashMap;

/**
 * @author Traian
 */
public class State<Control, Alphabet> {
    private static HashMap<Object, State> basicCache;
    private static HashMap<Object, HashMap<Object, State>> extendedCache;

    public Control getState() {
        return state;
    }

    public Alphabet getLetter() {
        return letter;
    }

    private final Control state;
    private final Alphabet letter;

    private State(Control state, Alphabet letter) {
        this.state = state;
        this.letter = letter;
    }

    public static<Control, Alphabet> State<Control, Alphabet> of(Control state, Alphabet letter) {
        if (letter == null) return of(state);
        if (extendedCache == null) extendedCache = new HashMap<Object, HashMap<Object, State>>();
        HashMap<Object, State> map = extendedCache.get(state);
        if (map == null) {
            map = new HashMap<Object, State>();
            extendedCache.put(state, map);
        }
        State<Control, Alphabet> state1 = (State<Control, Alphabet>) map.get(letter);
        if (state1 == null) {
            state1 = new State<Control, Alphabet>(state, letter);
            map.put(letter, state1);
        }
        return state1;
     }

    public static <Control, Alphabet> State<Control, Alphabet> of(Control state) {
        if (basicCache == null) basicCache = new HashMap<Object, State>();
        State<Control, Alphabet> state1 = (State<Control, Alphabet>) basicCache.get(state);
        if (state1 == null) {
            state1 = new State<Control, Alphabet>(state, null);
            basicCache.put(state, state1);
        }
        return state1;
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + state.hashCode();
        if (letter != null) {
            hash = hash * Utils.HASH_PRIME + letter.hashCode();
        }
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        return this == obj;
    }
}
