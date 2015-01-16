// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;

import java.util.Map;

/**
 * Backend Specific Transition.
 * Constains the rule and the substitution
 */

public class ConstrainedTransition {
    private Rule rule;

    private Map<Variable, Term> substitution;

    public ConstrainedTransition(Map<Variable, Term> substitution, Rule rule) {
        this.substitution = substitution;
        this.rule = rule;
    }

    public Rule getRule() {
        return rule;
    }

    public Map<Variable, Term> getSubstitution() {
        return substitution;
    }
}
