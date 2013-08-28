package org.kframework.backend.pdmc.pda;

import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.pdmc.pda.buchi.Evaluator;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Traian
 */
public class ConfigurationHead<Control, Alphabet> {
    private static Map<Object, ConfigurationHead> basicCache;
    private static Map<Object, Map<Object, ConfigurationHead>> extendedCache;

    private final Control state;
    private final Alphabet stackHead;

    private ConfigurationHead(Control state, Alphabet stackHead) {
        this.state = state;
        this.stackHead = stackHead;
    }


    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + state.hashCode();
        if (stackHead != null)
            hash = hash * Utils.HASH_PRIME + stackHead.hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        return (this == obj);
    }

    public boolean isProper() {
        return stackHead != null;
    }

    public Control getState() {
        return state;
    }

    public static <Control, Alphabet> ConfigurationHead<Control, Alphabet> of(Control c, Alphabet gamma) {
        if (gamma == null) return of(c);
        if (extendedCache == null) extendedCache = new HashMap<Object, Map<Object, ConfigurationHead>>();
        Map<Object, ConfigurationHead> map = extendedCache.get(c);
        if (map == null) {
            map = new HashMap<Object, ConfigurationHead>();
            extendedCache.put(c, map);
        }
        @SuppressWarnings("unchecked")
        ConfigurationHead<Control, Alphabet> configurationHead =
                (ConfigurationHead<Control, Alphabet>) map.get(gamma);
        if (configurationHead == null) {
            configurationHead = new ConfigurationHead<Control, Alphabet>(c, gamma);
            map.put(gamma, configurationHead);
        }
        return  configurationHead;
    }

    private static <Control, Alphabet> ConfigurationHead<Control, Alphabet> of(Control c) {
        if (basicCache == null) basicCache = new HashMap<Object, ConfigurationHead>();
        @SuppressWarnings("unchecked")
        ConfigurationHead<Control, Alphabet> configurationHead =
                (ConfigurationHead<Control, Alphabet>) basicCache.get(c);
        if (configurationHead == null) {
            configurationHead = new ConfigurationHead<Control, Alphabet>(c, null);
            basicCache.put(c, configurationHead);
        }
        return  configurationHead;
    }

    public Alphabet getLetter() {
        return stackHead;
    }

    @Override
    public String toString() {
        return "<" + state + "," + stackHead + ">";

    }
}
