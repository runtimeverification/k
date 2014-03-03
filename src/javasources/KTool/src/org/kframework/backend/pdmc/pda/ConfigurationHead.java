package org.kframework.backend.pdmc.pda;

import java.util.HashMap;
import java.util.Map;

/**
 * The head of a pushdown system configuration consisting of a pair between the state of the configuration
 * and the top of the stack (or null, if the stack is empty)
 *
 * @param <Control>  representing the states of a PDS
 * @param <Alphabet> representing the stack alphabet of the PDS
 *
 * @author TraianSF
 */
public class ConfigurationHead<Control, Alphabet> {
    private static Map<Object, ConfigurationHead> basicCache;
    private static Map<Object, Map<Object, ConfigurationHead>> extendedCache;

    private final Control state;
    private final Alphabet stackHead;

    protected ConfigurationHead(Control state, Alphabet stackHead) {
        this.state = state;
        this.stackHead = stackHead;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ConfigurationHead that = (ConfigurationHead) o;

        if (stackHead != null ? !stackHead.equals(that.stackHead) : that.stackHead != null) return false;
        if (!state.equals(that.state)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        int result = state.hashCode();
        result = 31 * result + (stackHead != null ? stackHead.hashCode() : 0);
        return result;
    }

    public boolean isProper() {
        return stackHead != null;
    }

    public Control getState() {
        return state;
    }

    public static <Control, Alphabet> ConfigurationHead<Control, Alphabet> of(Control c, Alphabet gamma) {
        if (gamma == null) return of(c);
        if (extendedCache == null) extendedCache = new HashMap<>();
        Map<Object, ConfigurationHead> map = extendedCache.get(c);
        if (map == null) {
            map = new HashMap<>();
            extendedCache.put(c, map);
        }
        @SuppressWarnings("unchecked")
        ConfigurationHead<Control, Alphabet> configurationHead =
                (ConfigurationHead<Control, Alphabet>) map.get(gamma);
        if (configurationHead == null) {
            configurationHead = new ConfigurationHead<>(c, gamma);
            map.put(gamma, configurationHead);
        }
        return  configurationHead;
    }

    private static <Control, Alphabet> ConfigurationHead<Control, Alphabet> of(Control c) {
        if (basicCache == null) basicCache = new HashMap<>();
        @SuppressWarnings("unchecked")
        ConfigurationHead<Control, Alphabet> configurationHead =
                (ConfigurationHead<Control, Alphabet>) basicCache.get(c);
        if (configurationHead == null) {
            configurationHead = new ConfigurationHead<>(c, null);
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
