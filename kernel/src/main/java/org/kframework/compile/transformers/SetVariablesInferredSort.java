// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

/**
 * Sets the sort of each {@code Variable} node in the AST to the sort produced by the type
 * inferred by {@link org.kframework.parser.concrete.disambiguate.CollectExpectedVariablesVisitor}.
 *
 * @see org.kframework.parser.concrete.disambiguate.CollectExpectedVariablesVisitor
 *
 * @author AndreiS
 */
public class SetVariablesInferredSort extends CopyOnWriteTransformer {

    public SetVariablesInferredSort(Context context) {
        super("Set the sort of each variable to the inferred sort", context);
    }

    @Override
    public Variable visit(Variable variable, Void _void) {
        Variable result = new Variable(variable);
        result.setSort(variable.getExpectedSort());
        return result;
    }

}
