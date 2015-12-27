// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.apache.commons.lang3.tuple.Pair;
import scala.collection.immutable.List;


public class LocalRewriteTerm extends SMTLibTerm {

    public final scala.collection.immutable.List<Pair<Integer, Integer>> path;
    public final Term rewriteRHS;

    public LocalRewriteTerm(List<Pair<Integer, Integer>> path, Term rewriteRHS) {
        super(null);
        this.path = path;
        this.rewriteRHS = rewriteRHS;
    }

    @Override
    public boolean isExactSort() {
        return false;
    }

    @Override
    public boolean isSymbolic() {
        return true;
    }

    @Override
    public Sort sort() {
        return Sort.KITEM;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        LocalRewriteTerm that = (LocalRewriteTerm) o;

        if (!path.equals(that.path)) return false;
        return rewriteRHS.equals(that.rewriteRHS);

    }

    @Override
    public int computeHash() {
        return path.hashCode();
    }

    @Override
    public boolean isNormal() {
        return false;
    }
}
