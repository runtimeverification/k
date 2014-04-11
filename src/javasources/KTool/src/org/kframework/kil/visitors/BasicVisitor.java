package org.kframework.kil.visitors;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;

public class BasicVisitor<P> extends AbstractVisitor<P, Void> {
    
    public BasicVisitor(String name, Context context) {
        super(name, context);
    }

    @Override
    public Void defaultReturnValue(ASTNode node, P p) {
        return null;
    }

    @Override
    public ASTNode processChildTerm(ASTNode node, ASTNode child, Void _, P p) {
        return child;
    }
    
    @Override
    public boolean visitChildren() {
        return true;
    }

    @Override
    public boolean cache() {
        return true;
    }

    @Override
    public boolean copy() {
        return false;
    }

    @Override
    public <T extends ASTNode> boolean change(T o, T n) {
        return false;
    }

}
