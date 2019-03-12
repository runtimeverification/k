// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.BasicVisitor;

/**
 * Computes field {@code isCacheable} on the given node and all child nodes recursively.
 */
public class IsCacheableFieldInitializer extends BasicVisitor {

    private boolean isCacheable = true;

    @Override
    public final void visitNode(JavaSymbolicObject node) {
        if (node.isCacheable != null) {
            isCacheable = isCacheable && node.isCacheable;
            return;
        }

        boolean parentIsCacheable = isCacheable;
        isCacheable = true;
        if (!(node instanceof Token)) {
            super.visitNode(node);
        }
        node.isCacheable = isCacheable;
        isCacheable = parentIsCacheable && isCacheable;
    }
}
