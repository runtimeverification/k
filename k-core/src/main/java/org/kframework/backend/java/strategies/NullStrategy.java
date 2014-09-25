// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.strategies;

import java.util.Collection;

import org.kframework.backend.java.kil.Rule;

/**
 * Using the NullStrategy will behave the same as using no strategy at all.
 * Calling next() will just return the collection of rules passed in from
 * reset().
 *
 * @author ericmikida
 *
 */

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
