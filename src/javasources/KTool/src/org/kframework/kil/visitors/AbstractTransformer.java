package org.kframework.kil.visitors;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;

public abstract class AbstractTransformer<P> extends AbstractVisitor<P, ASTNode> {

    public AbstractTransformer(String name, Context context) {
        super(name, context);
    }

    @Override
    public ASTNode defaultReturnValue(ASTNode node, P p) {
        // TODO Auto-generated method stub
        return node;
    }

    @Override
    public ASTNode processChildTerm(ASTNode node, ASTNode child,
            ASTNode childResult, P p) {
        return childResult;
    }

    @Override
    public boolean cache() {
        return false;
    }

    @Override
    public <T extends ASTNode> boolean change(T o, T n) {
        // TODO Auto-generated method stub
        return o != n;
    }

}
