// Copyright (C) 2014 K Team. All Rights Reserved.
package org.kframework.kil.visitors;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;

public class BasicVisitor extends AbstractVisitor<Void, Void, RuntimeException> {
    
    public BasicVisitor(Context context) {
        super(context);
    }
    
    public BasicVisitor(String name, Context context) {
        super(name, context);
    }

    @Override
    public Void defaultReturnValue(ASTNode node, Void _) {
        return null;
    }

    @Override
    public ASTNode processChildTerm(ASTNode node, ASTNode child, Void _, Void __) {
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
    public <T extends ASTNode> boolean changed(T o, T n) {
        return false;
    }

    @Override
    public <T extends ASTNode> T copy(T original) {
        return original;
    }

}
