// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


/**
 * A hole (a term of the form "HOLE").
 *
 * @author AndreiS
 */
public final class Hole extends Term implements MaximalSharing {

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
    protected boolean computeMutability() {
        return false;
    }

    @Override
    public String toString() {
        return "HOLE";
    }

    @Override
    public void accept(Unifier unifier, Term patten) {
        unifier.unify(this, patten);
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

    /**
     * Returns the HOLE constant in this session rather than the de-serialized constant.
     */
    private Object readResolve() {
        return HOLE;
    }

}
