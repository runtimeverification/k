package org.kframework.backend.pdmc.pda.buchi;

import org.kframework.backend.pdmc.pda.buchi.parser.Token;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Traian
 */
public class BuchiState {
    static final public String ACCEPT = "accept";
    static final public String INIT = "init";
    static final Map<String, BuchiState> cache = new HashMap<String, BuchiState>();

    String left;
    String right;

    private BuchiState(String s, String s1) {
        left = s; right = s1;
        if (left.equals(ACCEPT)) left = ACCEPT;
        if (right.equals(INIT)) right = INIT;
    }

    public boolean isFinal() {
        return left == ACCEPT;
    }

    public boolean isStart() {
        return right == INIT;
    }

    @Override
    public String toString() {
        return left + "_" + right;
    }

    public static BuchiState of(Token id) {
        String[] two = id.image.split("_");
        assert two.length == 2 : "Each state should have two parts";
        BuchiState state = cache.get(id.image);
        if (state == null) {
            state = new BuchiState(two[0], two[1]);
            cache.put(id.image, state);
        }
        return state;
    }
}
