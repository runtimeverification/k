package org.kframework.backend.pdmc.pda;

import org.kframework.backend.java.symbolic.Utils;

/**
 * @author Traian
 */
public class ConfigurationHead<Control, Alphabet> {
    private final Control state;
    private final Alphabet stackHead;

    public ConfigurationHead(Control state) {
        this(state, null);
    }

    public ConfigurationHead(Control state, Alphabet stackHead) {
        this.state = state;
        this.stackHead = stackHead;
    }


    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + state.hashCode();
        hash = hash * Utils.HASH_PRIME + stackHead.hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;

        if (!(obj instanceof ConfigurationHead)) return false;

        ConfigurationHead<Control, Alphabet> configurationHead = (ConfigurationHead<Control, Alphabet>) obj;
        return stackHead.equals(configurationHead.stackHead) && state.equals(configurationHead.state);
    }

    public boolean isProper() {
        return stackHead != null;
    }

    public Control getState() {
        return state;
    }
}
