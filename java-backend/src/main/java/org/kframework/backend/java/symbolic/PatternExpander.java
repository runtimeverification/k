// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.kil.ASTNode;

/**
 * Expands map patterns according to their definitions.
 */
public class PatternExpander extends CopyOnWriteTransformer {

    private final SymbolicConstraint constraint;
    private final boolean narrowing;

    public PatternExpander(SymbolicConstraint constraint, boolean narrowing) {
        super(constraint.termContext());
        this.constraint = constraint;
        this.narrowing = narrowing;
    }

    @Override
    public ASTNode transform(KItem kItem) {
        return ((KItem) super.transform(kItem)).expandPattern(constraint, narrowing);
    }

}
