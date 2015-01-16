// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.krun.api.Transition;

import java.util.Map;

/**
 * Generic Transition for Rules that have already been converted to generic Kil
 */
public class GenericTransition extends Transition {

    public GenericTransition(TransitionType type, String label, ASTNode rule,
                             Map<Variable, Term> substitution,
                             String readString) {
        super(type, label, rule, substitution, readString);
    }
    @Override
    public ASTNode getRule() {
        return rule;
    }


    @Override
    public Map<Variable, Term> getSubstitution() {
        return substitution;
    }

    public static GenericTransition rule(ASTNode rule) {
        return new GenericTransition(TransitionType.RULE, null, rule, null, null);
    }

    public static GenericTransition label(String label) {
        return new GenericTransition(TransitionType.LABEL, label, null, null, null);
    }

    public static GenericTransition unlabelled() {
        return new GenericTransition(TransitionType.UNLABELLED, null, null, null, null);
    }

    public static GenericTransition deadlock() {
        return new GenericTransition(TransitionType.DEADLOCK, null, null, null, null);
    }

    public static GenericTransition reduce() {
        return new GenericTransition(TransitionType.REDUCE, null, null, null, null);
    }

    public static GenericTransition stdin(String readString) {
        return new GenericTransition(TransitionType.STDIN, null, null, null, readString);
    }
}
