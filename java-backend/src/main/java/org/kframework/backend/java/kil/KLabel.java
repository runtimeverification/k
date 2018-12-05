// Copyright (c) 2013-2018 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;


/**
 * A KLabel.
 *
 * @author AndreiS
 */
public abstract class KLabel extends Term {

    protected KLabel() {
        super(Kind.KLABEL);
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public boolean isSymbolic() {
        /* AndreiS: no support for symbolic KLabels */
        return false;
    }

    @Override
    public Sort sort() {
        return kind.asSort();
    }

    /**
     * Checks if this {@code KLabel} represents a constructor. A {@code KLabel}
     * represents a constructor, a function, or a pattern.
     *
     * @return true if this {@code KLabel} represents a constructor; otherwise,
     *         false
     */
    public abstract boolean isConstructor();

    /**
     * Checks if this {@code KLabel} represents a function. A {@code KLabel}
     * represents a constructor, a function, or a pattern.
     *
     * @return true if this {@code KLabel} represents a function; otherwise,
     *         false
     */
    public abstract boolean isFunction();

    public abstract boolean isProjection();

    /**
     * Checks if this {@code KLabel} represents a pattern. A {@code KLabel}
     * represents a constructor, a function, or a pattern.
     *
     * @return true if this {@code KLabel} represents a pattern; otherwise,
     *         false
     */
    public abstract boolean isPattern();

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public JavaSymbolicObject accept(Transformer transformer) {
        return transformer.transform(this);
    }

    public static org.kframework.kore.KLabel parse(String s) {
        return org.kframework.kore.KORE.KLabel(s);
    }
}
