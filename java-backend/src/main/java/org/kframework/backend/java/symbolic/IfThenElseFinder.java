// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.TermContext;

import java.util.ArrayList;
import java.util.List;

/**
 * Finds an innermost occurrence of the #if_#then_#else_#fi function.
 *
 * @author Traian
 */
public class IfThenElseFinder extends PrePostVisitor {
    final List<KItem> result;
    private final String IF_THEN_ELSE_LABEL="'#if_#then_#else_#fi";

    public IfThenElseFinder() {
        result = new ArrayList<>();
        preVisitor.addVisitor(new LocalVisitor() {
            @Override
            protected void visit(JavaSymbolicObject object) {
                proceed = result.isEmpty();
            }
        });
        postVisitor.addVisitor(new LocalVisitor(){
            @Override
            public void visit(KItem kItem) {
                if (!result.isEmpty()) return;
                if (kItem.kLabel() instanceof KLabelConstant &&
                        ((KLabelConstant) kItem.kLabel()).label().equals(IF_THEN_ELSE_LABEL)) {
                    result.add(kItem);
                }
            }
        });
    }
}
