// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.strategies;

import org.kframework.backend.java.kil.Rule;

import java.util.Collection;

/**
 * Interface definition for an evaluation strategy. Strategies that implement
 * this interface partition collections of Rule objects into equivalence
 * classes of rules and return each equivalence class in a specified order.
 *
 * USAGE:
 * Strategy s = new ConcreteStrategy();
 * s.reset(someRules);
 * while (s.hasNext()) {
 *   Collection<Rule> rules = s.next();
 *   // Process the rules in this equivalence class
 * }
 *
 * @author ericmikida
 *
 */

public interface Strategy {
    /**
     * Reset the strategy to work on the passed in Collection of rules.
     */
    public abstract void reset(Collection<Rule> rules);

    /**
     * Returns the next equivalence class of rules or null if there is no next
     * equivalence class.
     */
    public abstract Collection<Rule> next();

    /**
     * Returns true iff there is a next equivalence class to be returned.
     */
    public abstract boolean hasNext();
}
