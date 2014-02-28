package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KCollectionFragment;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.ASTNode;

import java.util.Map;
import java.util.Set;

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
            // TODO(AndreiS) this stops the traversal for ground terms (even if the functions are not fully evaluated)
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
