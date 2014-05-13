// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kil.visitors;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.ParseFailedException;

/**
 * A {@link AbstractTransformer} which doesn't visit its children. See also 
 * {@link org.kframework.backend.java.symbolic.LocalTransformer}.
 * @author dwightguth
 *
 */
public class LocalTransformer extends AbstractTransformer<ParseFailedException> {

    public LocalTransformer(String name, Context context) {
        super(name, context);
    }

    @Override
    public boolean visitChildren() {
        return false;
    }

    @Override
    public <T extends ASTNode> T copy(T original) {
        return original;
    }
}
