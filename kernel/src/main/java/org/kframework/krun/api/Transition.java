// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.krun.api;

import java.io.Serializable;
import java.util.Map;
import java.util.Optional;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.omg.CORBA.portable.ValueInputStream;

/**
A transitition in the transition system of a semantics. Used to represent edges in the search graph
associated with breadth-first search, LTL model-checking, and debugging.
*/
public abstract class Transition implements Serializable{

    /**
    The rule transforming the origin state to the destination state
    */
    protected Optional<ASTNode> rule;

    /**
    The substitution that the rule resulted in.
     */
    protected Optional<Map<Variable, Term>> substitution;

    /**
    The label of the rule transforming the origin state to the destination state, if the entire
    rule is unavailable
    */
    private String label;

    /**
    The string read from stdin.
    */
    private String readString;

    private TransitionType type;

    protected Transition(TransitionType type, String label, ASTNode rule, Map<Variable, Term> substitution,
        String readString) {
        this.type = type;
        this.label = label;
        this.rule = Optional.ofNullable(rule);
        this.readString = readString;
        this.substitution = Optional.ofNullable(substitution);
    }

    public abstract ASTNode getRule();

    public void setRule(ASTNode rule) {
        this.rule = Optional.ofNullable(rule);
    }

    public String getLabel() {
        return label;
    }

    public void setLabel(String label) {
        this.label = label;
    }

    @Override
    public abstract int hashCode();

    @Override
    public abstract boolean equals(Object obj);

    public abstract Map<Variable, Term> getSubstitution();

    public void setSubstitution(Optional<Map<Variable, Term>> substitution) {
        this.substitution = substitution;
    }

    public enum TransitionType {
        /**
        A transition for which the rule transforming the origin to the destination is known
        */
        RULE,
        /**
        A transition for which only the rule label of the underlying rule is known.
        */
        LABEL,
        /**
        A transition for which no further information is available, except that the rule had no
        label.
        */
        UNLABELLED,
        /**
        A transition corresponding to a model-checking deadlock.
        */
        DEADLOCK,
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

    public String getReadString() {
        return readString;
    }


}
