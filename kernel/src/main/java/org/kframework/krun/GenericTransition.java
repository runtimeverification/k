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

    /**
     The string read from stdin.
     */
    private String readString;


    private GenericTransition(TransitionType type, ASTNode rule,
                             Map<Variable, Term> substitution,
                             String readString) {
        super(type, rule, substitution);
        this.readString = readString;
    }
    @Override
    public ASTNode getRule() {
        return rule;
    }

    public String getReadString() {
        return readString;
    }

    @Override
    public Map<Variable, Term> getSubstitution() {
        return substitution;
    }


    public static GenericTransition unlabelled() {
        return new GenericTransition(TransitionType.UNLABELLED, null, null, null);
    }


    public static GenericTransition reduce() {
        return new GenericTransition(TransitionType.REDUCE, null, null, null);
    }

    public static GenericTransition stdin(String readString) {
        return new GenericTransition(TransitionType.STDIN, null, null, readString);
    }
}
