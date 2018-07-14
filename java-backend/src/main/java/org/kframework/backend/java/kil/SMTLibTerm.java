// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;

public class SMTLibTerm extends Term {

    private final CharSequence expression;

    public SMTLibTerm(CharSequence expression) {
        super(Kind.KITEM);
        this.expression = expression;
    }

    public CharSequence expression() {
        return expression;
    }

    @Override
    public boolean isExactSort() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isSymbolic() {
        throw new UnsupportedOperationException();
    }

    @Override
    public Sort sort() {
        throw new UnsupportedOperationException();
    }

    @Override
    public JavaSymbolicObject accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    protected int computeHash() {
        return System.identityHashCode(this);
    }

    @Override
    public boolean equals(Object object) {
        return this == object;
    }
}
