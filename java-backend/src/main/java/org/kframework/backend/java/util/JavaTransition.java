// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.backend.java.kil.Rule;

import org.kframework.backend.java.symbolic.BackendJavaKILtoKILTransformer;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.krun.api.Transition;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;

/**
 * Java Backend Specific Transition Class
 */
public class JavaTransition extends Transition {

    /**
     * Backend specific Rule converted lazily to generic rule on get()
     */
    private Rule javaRule;

    /**
     * Backend specific Substitution converted lazily to generic substitution on get()
     */
    private Map<org.kframework.backend.java.kil.Variable, org.kframework.backend.java.kil.Term> javaSubs;

    private Context context;

    public JavaTransition(TransitionType type, String label, Rule rule,
                          Map<org.kframework.backend.java.kil.Variable, org.kframework.backend.java.kil.Term> javaSubs,
                          String readString, Context context) {
        super(type, label, null, null, readString);
        javaRule = rule;
        this.javaSubs = javaSubs;
        this.context = context;
    }

    public JavaTransition(TransitionType type, String label, ASTNode rule, Map<Variable, Term> subs,
                          String readString) {
        super(type, label, rule, subs, readString);
        javaRule = null;
    }

    public Rule getJavaRule() {
        return javaRule;
    }

    @Override
    public ASTNode getRule() {
        if (rule != null) {
            return rule;
        }

        rule = javaRule.accept(new BackendJavaKILtoKILTransformer(context));
        return rule;
    }

    @Override
    public Map<Variable, Term> getSubstitution() {
        if (substitution != null) {
            return substitution;
        }
        Map<Variable, Term> genericSubs = new LinkedHashMap<>();
        for (org.kframework.backend.java.kil.Variable key : javaSubs.keySet()) {
            org.kframework.backend.java.kil.Term value = javaSubs.get(key);
            Variable genericKey = (Variable) key.accept(new BackendJavaKILtoKILTransformer(context));
            Term genericValue = (Term) value.accept(new BackendJavaKILtoKILTransformer(context));
            genericSubs.put(genericKey, genericValue);
        }
        substitution = genericSubs;
        return substitution;
    }

  
}
