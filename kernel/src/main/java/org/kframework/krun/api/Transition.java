// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.krun.api;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;

import java.io.Serializable;
import java.util.Map;

/**
A transitition in the transition system of a semantics. Used to represent edges in the search graph
associated with breadth-first search, LTL model-checking, and debugging.
*/
public abstract class Transition implements Serializable{

    /**
    The rule transforming the origin state to the destination state
    */
    protected ASTNode rule;

    /**
    The substitution that the rule resulted in.
     */
    protected Map<Variable, Term> substitution;

    /**
     The string read from stdin.
     */
    private String readString;

    private TransitionType type;

    protected Transition(TransitionType type, ASTNode rule, Map<Variable, Term> substitution, String readString) {
        this.type = type;
        this.rule = rule;
        this.substitution = substitution;
        this.readString = readString;
    }

    public abstract ASTNode getRule();

    public void setRule(ASTNode rule) {
        this.rule = rule;
    }

    public abstract Map<Variable, Term> getSubstitution();

    public void setSubstitution(Map<Variable, Term> substitution) {
        this.substitution = substitution;
    }

    public String getReadString() {
        return readString;
    }

    public enum TransitionType {
        /**
        A transition for which the rule transforming the origin to the destination is known
        */
        RULE,

        /**
        A transition for which no further information is available, except that the rule had no
        label.
        */
        UNLABELLED,

        /**
        A rewrite or set of rewrites containing no transitions.
        */
        REDUCE,

        /**
        An action signifying that the user has entered data on the standard input stream.
        */
        STDIN
    }

    public TransitionType getType() {
        return type;
    }

    public abstract Location getLocation();

    public abstract Source getSource();


}
