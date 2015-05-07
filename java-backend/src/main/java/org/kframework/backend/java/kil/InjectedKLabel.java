// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.kore.KLabel;

/**
 * Created by dwightguth on 5/4/15.
 */
public class InjectedKLabel extends Term implements org.kframework.kore.InjectedKLabel {

    final Term injectedKLabel;

    public InjectedKLabel(Term injectedKLabel) {
        super(Kind.KITEM);
        this.injectedKLabel = injectedKLabel;
    }

    public Term injectedKLabel() {
        return injectedKLabel;
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
    protected boolean computeMutability() {
        return injectedKLabel.isMutable();
    }

    @Override
    protected int computeHash() {
        return injectedKLabel.hashCode();
    }

    @Override
    public KLabel klabel() {
        return (KLabel) injectedKLabel;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        InjectedKLabel that = (InjectedKLabel) o;

        return injectedKLabel.equals(that.injectedKLabel);

    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        unifier.unify(this, pattern);
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
        matcher.match(this, pattern);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }
}
