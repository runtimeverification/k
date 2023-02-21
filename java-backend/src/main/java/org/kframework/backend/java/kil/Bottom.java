// Copyright (c) K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;


/**
 * Refers to a computation which never completes successfully.
 * A {@link org.kframework.backend.java.symbolic.Equality} instance between
 * bottom and anything else is false and makes the entire constraint false.
 *
 * @see org.kframework.backend.java.symbolic.ConjunctiveFormula
 *
 * @author TraianSF
 */
public class Bottom extends Term {

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
    public JavaSymbolicObject<Term> accept(Transformer transformer) {
        return this;
    }

    @Override
    public void accept(Visitor visitor) { }
}
