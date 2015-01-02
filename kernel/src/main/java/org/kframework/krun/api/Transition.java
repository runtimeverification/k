// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.krun.api;

import java.io.Serializable;

import org.kframework.kil.ASTNode;

/**
A transitition in the transition system of a semantics. Used to represent edges in the search graph
associated with breadth-first search, LTL model-checking, and debugging.
*/
public class Transition implements Serializable{

    /**
    The rule transforming the origin state to the destination state
    */
    private ASTNode rule;

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

    protected Transition(TransitionType type, String label, ASTNode rule,
        String readString) {
        this.type = type;
        this.label = label;
        this.rule = rule;
        this.readString = readString;
    }

    public static Transition rule(ASTNode rule) {
        return new Transition(TransitionType.RULE, null, rule, null);
    }

    public static Transition label(String label) {
        return new Transition(TransitionType.LABEL, label, null, null);
    }

    public static Transition unlabelled() {
        return new Transition(TransitionType.UNLABELLED, null, null, null);
    }

    public static Transition deadlock() {
        return new Transition(TransitionType.DEADLOCK, null, null, null);
    }

    public static Transition reduce() {
        return new Transition(TransitionType.REDUCE, null, null, null);
    }

    public static Transition stdin(String readString) {
        return new Transition(TransitionType.STDIN, null, null, readString);
    }

    public ASTNode getRule() {
        return rule;
    }

    public void setRule(ASTNode rule) {
        this.rule = rule;
    }

    public String getLabel() {
        return label;
    }

    public void setLabel(String label) {
        this.label = label;
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
