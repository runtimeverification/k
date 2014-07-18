// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.api;

import java.io.Serializable;

import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.loader.Context;

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

    protected Context context;

    protected Transition(Context context, TransitionType type, String label, ASTNode rule,
        String readString) {
        this.context = context;
        this.type = type;
        this.label = label;
        this.rule = rule;
        this.readString = readString;
    }

    public static Transition rule(ASTNode rule, Context context) {
        return new Transition(context, TransitionType.RULE, null, rule, null);
    }

    public static Transition label(String label, Context context) {
        return new Transition(context, TransitionType.LABEL, label, null, null);
    }

    public static Transition unlabelled(Context context) {
        return new Transition(context, TransitionType.UNLABELLED, null, null, null);
    }

    public static Transition deadlock(Context context) {
        return new Transition(context, TransitionType.DEADLOCK, null, null, null);
    }

    public static Transition reduce(Context context) {
        return new Transition(context, TransitionType.REDUCE, null, null, null);
    }

    public static Transition stdin(String readString, Context context) {
        return new Transition(context, TransitionType.STDIN, null, null, readString);
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

    @Override
    public String toString() {
        if (type == TransitionType.RULE) {
            Attributes a = rule.getAttributes();
            UnparserFilter unparser = new UnparserFilter(true, context.krunOptions.color(), context.krunOptions.output, context);
            unparser.visitNode(a);
            return "\nRule tagged " + unparser.getResult() + " ";
        } else if (type == TransitionType.LABEL) {
            return "\nRule labelled " + label + " ";
        } else if (type == TransitionType.REDUCE) {
            return "\nMaude 'reduce' command ";
        } else if (type == TransitionType.UNLABELLED) {
            return "\nUnlabelled rule ";
        } else if (type == TransitionType.DEADLOCK) {
            return "\nDeadlock ";
        } else {
            return "\nRead " + StringBuiltin.of(readString).value();
        }
    }
}
