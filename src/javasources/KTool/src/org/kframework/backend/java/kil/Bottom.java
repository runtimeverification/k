// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.util.HashMap;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import com.google.common.collect.Maps;

/**
 * Refers to a computation which never completes successfully.
 * A {@link org.kframework.backend.java.symbolic.SymbolicConstraint.Equality} instance between
 * bottom and anything else is false and makes the entire constraint false.
 *
 * @see org.kframework.backend.java.symbolic.SymbolicConstraint
 *
 * @author TraianSF
 */
public class Bottom extends Term implements MaximalSharing {

    private static final HashMap<Kind, Bottom> cache = Maps.newHashMap();

    public static Bottom of(Kind kind) {
        Bottom bottom = cache.get(kind);
        if (bottom == null) {
            bottom = new Bottom(kind);
            cache.put(kind, bottom);
        }
        return bottom;
    }

    private Bottom(Kind kind) {
        super(kind);
    }

    @Override
    public boolean isExactSort() {
        return false;
    }

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
    protected boolean computeHasCell() {
        return false;
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return this;
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
        // TODO(YilongL): why not throw an exception here?
    }

    @Override
    public void accept(Unifier unifier, Term pattern) { }

    @Override
    public void accept(Visitor visitor) { }
}
