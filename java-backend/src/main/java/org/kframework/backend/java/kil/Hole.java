// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;


/**
 * A hole (a term of the form "HOLE").
 *
 * @author AndreiS
 */
public final class Hole extends Term {

    public static final Hole HOLE = new Hole();

    private Hole() {
        super(Kind.KITEM);
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public boolean isSymbolic() {
        return false;
    }

    @Override
    public Sort sort() {
        return Sort.KITEM;
    }

    @Override
    public boolean equals(Object object) {
        return this == object;
    }

    @Override
    protected int computeHash() {
        return System.identityHashCode(this);
    }

    @Override
    public String toString() {
        return "HOLE";
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public JavaSymbolicObject accept(Transformer transformer) {
        return transformer.transform(this);
    }

    /**
     * Returns the HOLE constant in this session rather than the de-serialized constant.
     */
    private Object readResolve() {
        return HOLE;
    }

}
