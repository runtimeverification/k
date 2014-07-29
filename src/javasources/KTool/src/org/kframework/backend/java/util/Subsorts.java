// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

import org.kframework.backend.java.kil.Sort;
import org.kframework.kil.loader.Context;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;

/**
 * Subsort relation.
 *
 * @author YilongL
 *
 */
public class Subsorts implements Serializable {

    private final Context context;

    private final Set<Sort> sorts;

    /**
     * {@code subsort[sort1][sort2] = true} iff {@code sort1} is bigger than
     * {@code sort2}.
     */
    private final boolean[][] subsort;

    public Subsorts(Context context) {
        this.context = context;

        Set<org.kframework.kil.Sort> genericKILSorts = context.getAllSorts();
        ImmutableSet.Builder<Sort> setBuilder = ImmutableSet.builder();
        int maxOrd = -1;
        for (org.kframework.kil.Sort genericKILSort : genericKILSorts) {
            /* ensure all sorts in context have Java-backend counterparts */
            Sort sort = Sort.of(genericKILSort.getName());
            setBuilder.add(sort);
            maxOrd = Math.max(maxOrd, sort.ordinal());
        }
        this.sorts = setBuilder.build();

        this.subsort = new boolean[maxOrd + 1][maxOrd + 1];
        for (Sort sort1 : sorts) {
            for (Sort sort2 : sorts) {
                subsort[sort1.ordinal()][sort2.ordinal()] = context
                        .isSubsorted(sort1.toFrontEnd(), sort2.toFrontEnd());
            }
        }
    }

    public Set<Sort> allSorts() {
        return sorts;
    }

    public boolean isSubsorted(Sort bigSort, Sort smallSort) {
        return subsort[bigSort.ordinal()][smallSort.ordinal()];
    }

    public boolean isSubsortedEq(Sort bigSort, Sort smallSort) {
        return bigSort == smallSort || isSubsorted(bigSort, smallSort);
    }

    /**
     * TODO(YilongL): delegates this method to Context#getGLBSort once all
     * string representation of sorts are eliminated
     */
    public Sort getGLBSort(Set<Sort> subset) {
        if (subset == null || subset.size() == 0) {
            return null;
        }
        if (subset.size() == 1) {
            return subset.iterator().next();
        }
        Set<Sort> lowerBounds = new HashSet<>();
        for (Sort elem : sorts) {
            boolean isLowerBound = true;
            for (Sort subsetElem : subset) {
                if (!(isSubsorted(subsetElem, elem) || elem.equals(subsetElem))) {
                    isLowerBound = false;
                    break;
                }
            }
            if (isLowerBound) {
                lowerBounds.add(elem);
            }
        }
        if (lowerBounds.size() == 0) {
            return null;
        }

        Sort candidate = null;
        for (Sort lowerBound2 : lowerBounds) {
            if (candidate == null) {
                candidate = lowerBound2;
            } else {
                if (isSubsorted(lowerBound2, candidate)) {
                    candidate = lowerBound2;
                } else if (!isSubsorted(candidate, lowerBound2)) {
                    /* no relation between lowerBound and candidate; none of them is the GLB */
                    candidate = null;
                }
            }
        }
        /* if there is a GLB, it must be candidate */
        if (candidate != null) {
            for (Sort lowerBound1 : lowerBounds) {
                if (lowerBound1 != candidate && !isSubsorted(candidate, lowerBound1)) {
                    candidate = null;
                    break;
                }
            }
        }
        return candidate;
    }

    public boolean hasCommonSubsort(Sort sort1, Sort sort2) {
        return context.hasCommonSubsort(sort1.toFrontEnd(), sort2.toFrontEnd());
    }

}
