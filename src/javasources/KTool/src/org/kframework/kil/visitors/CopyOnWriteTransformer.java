// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.visitors;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;

/**
 * A transformer useful for performing compilation steps on ASTs. When a term is modified, it is replaced in the
 * tree to avoid affecting other code with references to that AST.
 * @author dwightguth
 *
 */
public class CopyOnWriteTransformer extends AbstractTransformer<RuntimeException> {

    public CopyOnWriteTransformer(String name, Context context) {
        super(name, context);
    }

    public CopyOnWriteTransformer(Context context) {
        super(context);
    }

    @Override
    public boolean visitChildren() {
        return true;
    }

    @SuppressWarnings("unchecked")
    @Override
    public <T extends ASTNode> T copy(T original) {
        return (T)original.shallowCopy();
    }
}
