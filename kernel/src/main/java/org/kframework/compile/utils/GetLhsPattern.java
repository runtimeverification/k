// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Rewrite;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class GetLhsPattern extends CopyOnWriteTransformer {
    public GetLhsPattern(String s, Context context) {
        super(s, context);
    }

    @Override
    public ASTNode visit(Rewrite node, Void _void)  {
        return node.getLeft();
    }

}
