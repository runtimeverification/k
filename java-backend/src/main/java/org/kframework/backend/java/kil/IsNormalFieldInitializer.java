// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.BasicVisitor;


public class IsNormalFieldInitializer extends BasicVisitor {

    private boolean isNormal = true;

    @Override
    public void visitNode(JavaSymbolicObject node) {
        if (node.isNormal != null) {
            isNormal = isNormal && node.isNormal;
            return;
        }

        boolean parentIsNormal = isNormal;
        isNormal = true;
        if (!(node instanceof KLabelConstant || node instanceof Token || node instanceof Variable)) {
            super.visitNode(node);
        }
        node.isNormal = isNormal;
        isNormal = parentIsNormal && isNormal;
    }

    @Override
    public void visit(KItem kItem) {
        super.visit(kItem);
        isNormal = isNormal && !kItem.isSymbolic();
    }

    @Override
    public void visit(KItemProjection projection) {
        isNormal = false;
    }

}
