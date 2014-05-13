// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.strategies;

import org.kframework.backend.java.kil.Rule;

import java.util.Collection;
import java.util.LinkedList;

/**
 * The TransitionStrategy partitions the rules into transitional rules and
 * structural rules. It is instantiated with a list of transition strings,
 * and upon receiving a new collection of rules, it pulls out any rules
 * tagged with one or more of these transition strings. When iterating over
 * the rule classes, the structural rules are returned first, followed by
 * the transition rules. The idea is that during execution we only want to
 * apply transition rules when there are no more structural rules to be applied.
 *
 * This class also provides a function saying whether the next equivalence
 * class is the transition class. This is used during search in the java
 * rewrite engine, since transition rules are handled differently than
 * structural rules.
 *
 * @author ericmikida
 *
 */

public class TransitionStrategy implements Strategy {
    public TransitionStrategy(Collection<String> tags) {
        this.tags = tags;
    }

    public boolean nextIsTransition() {
        return structural == null && transition != null;
    }

    /**
     * Iterate through each rule in rules and place it in the transition list
     * if it contains a transition tag, otherwise put it in the structural list.
     */
    public void reset(Collection<Rule> rules) {
        transition = new LinkedList<Rule>();
        structural = new LinkedList<Rule>();
        for (Rule r : rules) {
            boolean t = false;
            for (String s : tags) {
                if (r.containsAttribute(s)) {
                    t = true;
                    break;
                }
            }
            if (t) {
                transition.add(r);
            } else {
                structural.add(r);
            }
        }
    }

    /**
     * If we haven't returned structural rules yet, return them and then set
     * them to null. Otherwise return the transition rules and set them to
     * null.
     */
    public Collection<Rule> next() {
        Collection<Rule> n = null;
        if (structural != null) {
            n = structural;
            structural = null;
        } else if (transition != null) {
            n = transition;
            transition = null;
        }
        return n;
    }

    /**
     * There is more equivalence classes to return if at least one of the two
     * lists is still non-null.
     */
    public boolean hasNext() {
        return structural != null || transition != null;
    }

    private Collection<Rule> transition;
    private Collection<Rule> structural;
    private Collection<String> tags;
}
