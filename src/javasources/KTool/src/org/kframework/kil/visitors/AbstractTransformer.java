// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kil.visitors;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * A helper class designed to encapsulate functionality shared between 
 * {@link LocalTransformer}, {@link BasicTransformer}, and {@link CopyOnWriteTransformer}.
 * 
 * This class serves to replace the Transformable interface that existed before, and implements
 * functionality specific to visitors which transform terms.
 * @author dwightguth
 *
 */
public abstract class AbstractTransformer extends AbstractVisitor<Void, ASTNode, TransformerException> {

    public AbstractTransformer(String name, Context context) {
        super(name, context);
    }

    @Override
    public ASTNode defaultReturnValue(ASTNode node, Void _) {
        return node;
    }

    @Override
    public ASTNode processChildTerm(ASTNode child, ASTNode childResult) {
        return childResult;
    }

    @Override
    public boolean cache() {
        return false;
    }

    @Override
    public <T extends ASTNode> boolean changed(T o, T n) {
        return o != n;
    }

}
