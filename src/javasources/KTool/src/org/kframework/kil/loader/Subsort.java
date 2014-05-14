// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import java.util.HashSet;
import java.util.Set;

import org.kframework.kil.KSorts;

public class Subsort {
    private String bigSort, smallSort;

    public Subsort(String bigSort, String smallSort) {
        this.bigSort = bigSort;
        this.smallSort = smallSort;
    }

    public String getBigSort() {
        return bigSort;
    }

    public String getSmallSort() {
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
