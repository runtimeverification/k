// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.symbolic.BackendJavaKILtoKILTransformer;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;
import org.kframework.krun.api.Transition;

/**
 * Java Backend Specific Transition Class
 *
 */
public class JavaTransition extends Transition{

    private Rule javaRule;
    private Context context;

    public JavaTransition(TransitionType type, String label, Rule rule, String readString, Context context) {
        super(type, label, null, readString);
        javaRule = rule;
        this.context = context;
    }

    public JavaTransition(TransitionType type, String label, ASTNode rule, String readString) {
        super(type, label, rule, readString);
        javaRule = null;
    }
    @Override
    public ASTNode getRule() {
        if (rule.isPresent()) {
            return rule.get();
        }
        return javaRule.accept(new BackendJavaKILtoKILTransformer(context));
    }

    @Override
    public int hashCode() {
        return 0;
    }

    @Override
    public boolean equals(Object obj) {
        return false;
    }
}
