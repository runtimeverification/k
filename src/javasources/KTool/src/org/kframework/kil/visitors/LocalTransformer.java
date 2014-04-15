package org.kframework.kil.visitors;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;

public class LocalTransformer extends AbstractTransformer {

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
