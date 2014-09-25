// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;

import com.google.common.collect.Sets;

/**
 * Copy on share version of {@link SubstituteAndEvaluateTransformer} aimed at
 * avoiding any undesired sharing between mutable terms.
 *
 * @author YilongL
 *
 */
public class CopyOnShareSubstAndEvalTransformer extends SubstituteAndEvaluateTransformer {

    private final Set<Variable> reusableVariables;

    public CopyOnShareSubstAndEvalTransformer(
            Map<Variable, ? extends Term> substitution,
            Set<Variable> reusableVariables, TermContext context) {
        super(substitution, context);
        // TODO(dwightguth): put this assertion back in once this class is constructed by
        // the injector
//        assert context.definition().context().javaExecutionOptions.fastExecution(
//                context.definition().context().krunOptions.search());
        this.reusableVariables = Sets.newHashSet(reusableVariables);
        this.copyOnShareSubstAndEval = true;
    }

    @Override
    public ASTNode transform(Variable variable) {
        Term term = substitution.get(variable);
        if (term == null) {
            return variable;
        }

        if (reusableVariables.contains(variable)) {
            reusableVariables.remove(variable);
        } else if (term.isMutable()) {
            term = DeepCloner.clone(term);
        }
        return term;
    }

}
