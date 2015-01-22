// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil.visitors;

import org.kframework.kil.ASTNode;
import org.kframework.kil.AbstractVisitor;
import org.kframework.kil.Definition;
import org.kframework.kil.Module;
import org.kframework.kil.loader.Context;

/**
 * A basic visitor pattern which takes no extra parameters, returns nothing, and throws no checked exceptions.
 * @author dwightguth
 *
 */
public class BasicVisitor extends AbstractVisitor<Void, Void, RuntimeException> {

    public BasicVisitor(Context context) {
        super(context);
    }

    public BasicVisitor(String name, Context context) {
        super(name, context);
    }

    @Override
    public Void defaultReturnValue(ASTNode node, Void _void) {
        return null;
    }

    @Override
    public <T extends ASTNode> T processChildTerm(T child, Void _void) {
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
