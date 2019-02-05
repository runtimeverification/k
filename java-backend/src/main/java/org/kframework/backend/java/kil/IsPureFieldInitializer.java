// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.BasicVisitor;

/**
 * Computes field {@code isPure} on the given node and all child nodes recursively.
 */
public class IsPureFieldInitializer extends BasicVisitor {

    private boolean isPure = true;

    @Override
    public final void visitNode(JavaSymbolicObject node) {
        if (node.isPure != null) {
            isPure = isPure && node.isPure;
            return;
        }

        boolean parentIsPure = isPure;
        isPure = true;
        if (!(node instanceof Token)) {
            super.visitNode(node);
        }
        node.isPure = isPure;
        isPure = parentIsPure && isPure;
    }

    @Override
    public void visit(KLabelConstant kLabelConstant) {
        isPure = !kLabelConstant.isImpure();
    }
}
