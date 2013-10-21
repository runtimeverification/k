package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.*;

import java.util.*;

import com.google.common.collect.ImmutableList;
import org.kframework.kil.ASTNode;


/**
 * Substitutes variables with terms according to a given substitution map.
 * 
 * @author AndreiS
 */
public class SubstitutionTransformer extends PrePostTransformer {

    private final Map<Variable, ? extends Term> substitution;

    public SubstitutionTransformer(Map<Variable, ? extends Term> substitution, TermContext context) {
    	super(context);
        this.substitution = substitution;
        postTransformer.addTransformer(new LocalSubstitutionTransformer());
        postTransformer.addTransformer(new VariableUpdaterTransformer());
//        preTransformer.addTransformer(new LocalVariableChecker());
        preTransformer.addTransformer(new LocalSubstitutionChecker());
    }

    private class LocalSubstitutionTransformer extends LocalTransformer {

        @Override
        public Term transform(Variable variable) {
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

                    return kSequence;
                } else {
                    return term;
                }
            } else {
                return variable;
            }
        }
    }

    /**
     * Checks
     *
     */
    private class LocalSubstitutionChecker extends LocalTransformer {
        @Override
        public KList transform(KList kList) {
            assert !kList.hasFrame() : "only KList with a fixed number of elements is supported";

            return kList;
        }

    }

    private class LocalVariableChecker extends LocalTransformer {
        @Override
        public ASTNode transform(JavaSymbolicObject object) {
            Set<Variable> variables = object.variableSet();
            for (Variable variable : substitution.keySet()) {
                if (variables.contains(variable)) {
                    return object;
                }
            }
            return new DoneTransforming(object);
        }
    }
}
