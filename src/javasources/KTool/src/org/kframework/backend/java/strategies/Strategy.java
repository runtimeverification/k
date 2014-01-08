package org.kframework.backend.java.strategies;

import org.kframework.backend.java.kil.Rule;

import java.util.Collection;

public interface Strategy {
    public abstract void reset(Collection<Rule> rules);

    public abstract Collection<Rule> next();

    public abstract boolean hasNext();
}
