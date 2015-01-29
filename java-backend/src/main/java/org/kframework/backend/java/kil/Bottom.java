// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


/**
 * Refers to a computation which never completes successfully.
 * A {@link org.kframework.backend.java.symbolic.Equality} instance between
 * bottom and anything else is false and makes the entire constraint false.
 *
 * @see org.kframework.backend.java.symbolic.SymbolicConstraint
 *
 * @author TraianSF
 */
public class Bottom extends Term implements MaximalSharing {

    public static final Bottom BOTTOM = new Bottom();

    private Bottom() {
        super(Kind.BOTTOM);
    }

    @Override
    public boolean isExactSort() {
        return false;
    }

    /**
     * Returns {@code false} so that the unifier/matcher will continue to
     * unify/match it against another term and fail as expected.
     */
    @Override
    public boolean isSymbolic() {
        return false;
    }

    @Override
    public Sort sort() {
        return kind.asSort();
    }

    @Override
    public boolean equals(Object object) {
        return this == object;
    }

    @Override
    protected int computeHash() {
        return kind.hashCode();
    }

    @Override
    protected boolean computeMutability() {
        return false;
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return this;
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
        matcher.match(this, pattern);
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        unifier.unify(this, pattern);
    }

    @Override
    public void accept(Visitor visitor) { }
}
