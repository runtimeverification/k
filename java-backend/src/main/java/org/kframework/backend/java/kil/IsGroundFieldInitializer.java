// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.BasicVisitor;


public class IsGroundFieldInitializer extends BasicVisitor {

    private boolean isGround = true;

    @Override
    public final void visitNode(JavaSymbolicObject node) {
        if (node.isGround != null) {
            isGround = isGround && node.isGround;
            return;
        }

        boolean parentIsGround = isGround;
        isGround = true;
        if (!(node instanceof KLabelConstant || node instanceof Token)) {
            super.visitNode(node);
        }
        node.isGround = isGround;
        isGround = parentIsGround && isGround;
    }

    @Override
    public void visit(Variable variable) {
        isGround = false;
    }

}
