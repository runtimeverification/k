package org.kframework.backend.pdmc.pda.automata;

import org.kframework.backend.java.symbolic.Utils;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Traian
 */
public class TransitionIndex<Control, Alphabet> {
    private static HashMap<State, Map<Object, TransitionIndex>> extendedCache;
    private static HashMap<State, TransitionIndex> basicCache;
    private final State<Control, Alphabet> state;
    private final Alphabet letter;

    private TransitionIndex(State<Control, Alphabet> state, Alphabet letter) {
        this.state = state;
        this.letter = letter;
    }


    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + state.hashCode();
        hash = hash * Utils.HASH_PRIME + letter.hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        /* the cache ensures uniqueness of logically equal object instances */
        return  this == obj;
    }

    public static <Control, Alphabet> TransitionIndex<Control, Alphabet> of(State<Control, Alphabet> start, Alphabet letter) {
        if (letter == null) return of(start);
        if (extendedCache == null) extendedCache = new HashMap<State, Map<Object, TransitionIndex>>();
        Map<Object,TransitionIndex> map = extendedCache.get(start);
        if (map == null) {
            map = new HashMap<Object, TransitionIndex>();
            extendedCache.put(start, map);
        }
        TransitionIndex<Control, Alphabet> index = (TransitionIndex<Control, Alphabet>) map.get(letter);
        if (index == null) {
            index = new TransitionIndex<Control, Alphabet>(start, letter);
            map.put(letter, index);
        }
        return index;
    }

    private static <Control, Alphabet> TransitionIndex<Control, Alphabet> of(State<Control, Alphabet> start) {
        if (basicCache == null) {
            basicCache = new HashMap<State, TransitionIndex>();
        }
        TransitionIndex<Control, Alphabet> index = (TransitionIndex<Control, Alphabet>) basicCache.get(start);
        if (index == null) {
            index = new TransitionIndex<Control, Alphabet>(start, null);
            basicCache.put(start, index);
        }
        return index;

    }
}
