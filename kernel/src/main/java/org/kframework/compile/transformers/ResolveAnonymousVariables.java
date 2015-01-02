// Copyright (c) 2012-2015 K Team. All Rights Reserved.
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
    public ASTNode visit(Variable node, Void _void)  {
        if (MetaK.isAnonVar(node)) {
            return Variable.getAnonVar(node.getSort(), node.isFreshVariable(), node.isFreshConstant());
        }
        return node;
    }

}
