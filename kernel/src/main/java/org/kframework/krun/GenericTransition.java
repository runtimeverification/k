// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.krun.api.Transition;

import java.util.Map;

/**
 * Generic Transition for Rules that have already been converted to generic Kil
 */
public class GenericTransition extends Transition {

    private GenericTransition(TransitionType type, ASTNode rule,
                             Map<Variable, Term> substitution,
                             String readString) {
        super(type, rule, substitution, readString);
    }
    @Override
    public ASTNode getRule() {
        return rule;
    }


    @Override
    public Map<Variable, Term> getSubstitution() {
        return substitution;
    }

    @Override
    public Location getLocation() {
        return rule.getLocation();
    }

    @Override
    public Source getSource() {
        return rule.getSource();
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
