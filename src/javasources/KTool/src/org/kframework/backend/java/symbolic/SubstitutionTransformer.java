package org.kframework.backend.java.symbolic;

import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;

import com.google.common.collect.ImmutableList;


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
        preTransformer.addTransformer(new LocalVariableChecker());
        postTransformer.addTransformer(new LocalSubstitutionTransformer());
        postTransformer.addTransformer(new VariableUpdaterTransformer());
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

                    KCollection kCollection;
                    if (fragment.getKCollection() instanceof KSequence) {
                        if (fragment.hasFrame()) {
                            kCollection = new KSequence(builder.build(), fragment.frame());
                        } else {
                            kCollection = new KSequence(builder.build());
                        }
                    } else {
                        assert fragment.getKCollection() instanceof KList;

                        if (fragment.hasFrame()) {
                            kCollection = new KList(builder.build(), fragment.frame());
                        } else {
                            kCollection = new KList(builder.build());
                        }
                    }

                    return kCollection;
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
