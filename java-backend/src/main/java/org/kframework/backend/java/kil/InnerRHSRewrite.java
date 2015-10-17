// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.builtin.KLabels;
import org.kframework.kil.ASTNode;
import org.kframework.kore.K;
import org.kframework.kore.KApply;

import java.util.Arrays;
import java.util.stream.Collector;
import java.util.stream.Collectors;

public class InnerRHSRewrite extends Term {
    public final Term[] theRHS;

    public InnerRHSRewrite(Term[] theRHS) {
        super(Kind.KITEM);
        this.theRHS = theRHS;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        InnerRHSRewrite that = (InnerRHSRewrite) o;

        // Probably incorrect - comparing Object[] arrays with Arrays.equals
        return Arrays.equals(theRHS, that.theRHS);

    }

    @Override
    public int computeHash() {
        return Arrays.hashCode(theRHS);
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
    protected boolean computeMutability() {
        return false;
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }
}
