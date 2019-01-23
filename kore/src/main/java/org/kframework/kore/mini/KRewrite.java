// Copyright (c) 2016-2019 K Team. All Rights Reserved.
package org.kframework.kore.mini;

import org.kframework.attributes.Att;
import org.kframework.kore.K;

/**
 * Created by dwightguth on 1/11/16.
 */
public class KRewrite implements org.kframework.kore.KRewrite {

    private K left, right;

    public KRewrite(K left, K right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public int cachedHashCode() {
        return hashCode();
    }

    @Override
    public K left() {
        return left;
    }

    @Override
    public K right() {
        return right;
    }

    @Override
    public Att att() {
        return Att.empty();
    }

    @Override
    public int computeHashCode() {
        return hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        KRewrite kRewrite = (KRewrite) o;

        if (!left.equals(kRewrite.left)) return false;
        return right.equals(kRewrite.right);

    }

    @Override
    public int hashCode() {
        int result = left.hashCode();
        result = 31 * result + right.hashCode();
        return result;
    }
}
