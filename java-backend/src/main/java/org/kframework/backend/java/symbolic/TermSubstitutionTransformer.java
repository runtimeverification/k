// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.Term;

import java.util.Map;


/**
 * Substitutes terms with terms according to a given substitution map.
 *
 * @author AndreiS
 */
public class TermSubstitutionTransformer extends PrePostTransformer {

    private final Map<? extends Term, ? extends Term> substitution;

    public static JavaSymbolicObject substitute(JavaSymbolicObject object,
                                                Map<? extends Term, ? extends Term> substitution) {
        TermSubstitutionTransformer transformer = new TermSubstitutionTransformer(
                substitution);
        return (JavaSymbolicObject) object.accept(transformer);
    }

    private TermSubstitutionTransformer(Map<? extends Term, ? extends Term> substitution) {
        this.substitution = substitution;
        preTransformer.addTransformer(new LocalSubstitutionTransformer());
    }

    private class LocalSubstitutionTransformer extends LocalTransformer {

        @Override
        public JavaSymbolicObject transform(Term term) {
            Term subst = substitution.get(term);
            if (subst != null) {
                return new DoneTransforming(subst);
            } else {
                return term;
            }
        }
    }

}
