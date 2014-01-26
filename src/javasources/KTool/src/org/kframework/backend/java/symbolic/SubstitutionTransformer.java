package org.kframework.backend.java.symbolic;

import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.KCollectionFragment;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.ASTNode;

import com.google.common.collect.ImmutableList;


/**
 * Substitutes variables with terms according to a given substitution map.
 * 
 * @author AndreiS
 */
public class SubstitutionTransformer extends PrePostTransformer {

    private final Map<Variable, ? extends Term> substitution;
    
    private boolean changed = false;

    public SubstitutionTransformer(Map<Variable, ? extends Term> substitution, TermContext context) {
    	super(context);
        this.substitution = substitution;
//      preTransformer.addTransformer(new LocalVariableChecker());
        preTransformer.addTransformer(new LocalSubstitutionChecker(context));
        postTransformer.addTransformer(new LocalSubstitutionTransformer());
        postTransformer.addTransformer(new VariableUpdaterTransformer());
        postTransformer.addTransformer(new LocalEvaluationUpdaterTransformer());
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

                    changed = true;
                    return kSequence;
                } else {
                    changed = true;
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
        public LocalSubstitutionChecker(TermContext context) {
            super(context);
        }

        @Override
        public KList transform(KList kList) {
            assert !kList.hasFrame() : "only KList with a fixed number of elements is supported";

            return kList;
        }
    }

    @SuppressWarnings("unused")
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
    
    private class LocalEvaluationUpdaterTransformer extends LocalTransformer {
        @Override
        public ASTNode transform(Term term) {
            // TODO(YilongL): this is the most naive possible implementation,
            // there is really no need to reset the evaluation status of every
            // subterm; fix it later! However, it is no worse than the current
            // implementation which determines whether to evaluate a term by
            // comparing object reference!
            if (changed) {
                term.resetEvalStatus();
            }
            return term;
        }
    }
}
