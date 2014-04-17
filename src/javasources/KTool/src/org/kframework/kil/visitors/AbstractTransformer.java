// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kil.visitors;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;

public abstract class AbstractTransformer extends AbstractVisitor<Void, ASTNode, TransformerException> {

    public AbstractTransformer(String name, Context context) {
        super(name, context);
    }

    @Override
    public ASTNode defaultReturnValue(ASTNode node, Void _) {
        // TODO Auto-generated method stub
        return node;
    }

    @Override
    public ASTNode processChildTerm(ASTNode node, ASTNode child,
            ASTNode childResult, Void _) {
        return childResult;
    }

    @Override
    public boolean cache() {
        return false;
    }

    @Override
    public <T extends ASTNode> boolean changed(T o, T n) {
        // TODO Auto-generated method stub
        return o != n;
    }

}
