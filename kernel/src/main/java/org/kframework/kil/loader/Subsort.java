// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.kil.Sort;

public final class Subsort {
    private Sort bigSort, smallSort;

    public Subsort(Sort bigSort, Sort smallSort) {
        this.bigSort = bigSort;
        this.smallSort = smallSort;
    }

    public Sort getBigSort() {
        return bigSort;
    }

    public Sort getSmallSort() {
        return smallSort;
    }

    @Override
    public String toString() {
        return smallSort + "<" + bigSort;
    }

    @Override
    public boolean equals(Object o) {
        if (o == null)
            return false;
        if (o.getClass() == Subsort.class) {
            Subsort s1 = (Subsort) o;
            return s1.bigSort.equals(bigSort) && s1.smallSort.equals(smallSort);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return bigSort.hashCode() + smallSort.hashCode();
    }
}
