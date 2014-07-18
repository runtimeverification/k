// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;

import java.util.Map;


/**
 * Substitutes variables with terms according to a given substitution map.
 *
 * @author AndreiS
 */
public class TermSubstitutionTransformer extends PrePostTransformer {

    private final Map<? extends Term, ? extends Term> substitution;

    public TermSubstitutionTransformer(Map<? extends Term, ? extends Term> substitution, TermContext context) {
        super(context);
        this.substitution = substitution;
//        preTransformer.addTransformer(new LocalVariableChecker());
        preTransformer.addTransformer(new LocalSubstitutionTransformer());
    }

    private class LocalSubstitutionTransformer extends LocalTransformer {

        @Override
        public ASTNode transform(Term variable) {
            Term term = substitution.get(variable);
            if (term != null) {
                return new DoneTransforming(term);
            } else {
                return variable;
            }
        }
    }

}
