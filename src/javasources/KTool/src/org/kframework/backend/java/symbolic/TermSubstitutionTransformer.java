package org.kframework.backend.java.symbolic;

import com.google.common.collect.ImmutableList;
import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;

import java.util.Map;
import java.util.Set;


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
                if (term instanceof KCollectionFragment) {
                    KCollectionFragment fragment = (KCollectionFragment) term;
                    ImmutableList.Builder<Term> builder = new ImmutableList.Builder<Term>();
                    builder.addAll(fragment);

                    KSequence kSequence;
                    if (fragment.hasFrame()) {
                        kSequence = new KSequence(builder.build(), fragment.frame());
                    } else {
                        kSequence = new KSequence(builder.build());
                    }

                    return new DoneTransforming(kSequence);
                } else {
                    return new DoneTransforming(term);
                }
            } else {
                return variable;
            }
        }
    }

}
