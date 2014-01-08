package org.kframework.backend.java.strategies;

import java.util.Collection;

import org.kframework.backend.java.kil.Rule;

public class NullStrategy implements Strategy {
    public void reset(Collection<Rule> rules) {
        this.rules = rules;
    }

    public Collection<Rule> next() {
        Collection<Rule> n = rules;
        rules = null;
        return n;
    }

    public boolean hasNext() {
        return rules != null;
    }

    private Collection<Rule> rules;
}
