// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class ResolveAnonymousVariables extends CopyOnWriteTransformer {

    public ResolveAnonymousVariables(Context context) {
        super("Resolve anonymous variables", context);
    }

    @Override
    public ASTNode visit(Variable node, Void _)  {
        if (MetaK.isAnonVar(node))
            return Variable.getFreshVar(node.getSort());
        return node;
    }

}
