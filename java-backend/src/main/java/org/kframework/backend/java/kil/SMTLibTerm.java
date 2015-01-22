// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

public class SMTLibTerm extends Term {

    private final String expression;

    public SMTLibTerm(String expression) {
        super(Kind.KITEM);
        this.expression = expression;
    }

    public String expression() {
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
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
        throw new UnsupportedOperationException();
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
    protected boolean computeMutability() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object object) {
        return this == object;
    }
}
