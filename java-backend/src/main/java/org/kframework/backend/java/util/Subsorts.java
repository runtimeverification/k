// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.google.common.collect.ArrayTable;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import com.google.common.collect.Table;
import org.kframework.Collections;
import org.kframework.backend.java.kil.Sort;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.kil.loader.Context;
import org.kframework.utils.errorsystem.KEMException;
import scala.collection.JavaConversions;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;


/**
 * Subsort relation.
 *
 * TODO(YilongL): delegates this to KORE/Context
 *
 * @author YilongL
 */
public class Subsorts implements Serializable {

    private final Set<Sort> sorts;

    /**
     * {@code subsort[sort1][sort2] = true} iff {@code sort1} is bigger than
     * {@code sort2}.
     */
    private final Table<Sort, Sort, Boolean> subsort;

    public Subsorts(Context context) {
        Set<org.kframework.kil.Sort> genericKILSorts = context.getAllSorts();
        ImmutableSet.Builder<Sort> setBuilder = ImmutableSet.builder();
        for (org.kframework.kil.Sort genericKILSort : genericKILSorts) {
            /* ensure all sorts in context have Java-backend counterparts */
            Sort sort = Sort.of(genericKILSort.getName());
            setBuilder.add(sort);
        }
        this.sorts = setBuilder.build();

        this.subsort = ArrayTable.create(sorts, sorts);
        for (Sort sort1 : sorts) {
            for (Sort sort2 : sorts) {
                subsort.put(sort1, sort2, context
                        .isSubsorted(sort1.toFrontEnd(), sort2.toFrontEnd()));
            }
        }
    }

    public Subsorts(Module module) {
        sorts = JavaConversions.asJavaCollection(module.definedSorts()).stream()
                .map(s -> Sort.of(s.name()))
                .collect(Collectors.toSet());

        this.subsort = ArrayTable.create(sorts, sorts);
        Set<org.kframework.kore.Sort> kSorts = Sets.newHashSet(Sorts.K(), Sorts.KList(), Sorts.KItem(), Sorts.KLabel(), Sorts.KBott(), Sorts.KVariable(), Sorts.KString());
        for (org.kframework.kore.Sort sort1 : Collections.iterable(module.definedSorts())) {
            for (org.kframework.kore.Sort sort2 : Collections.iterable(module.definedSorts())) {
                subsort.put(
                        Sort.of(sort1.name()),
                        Sort.of(sort2.name()),
                        module.subsorts().$greater(sort1, sort2));
            }
        }
    }

    public Set<Sort> allSorts() {
        return sorts;
    }

    public boolean isSubsorted(Sort bigSort, Sort smallSort) {
        Boolean isSubsorted = subsort.get(bigSort, smallSort);
        if (isSubsorted == null) {
            if (subsort.containsRow(bigSort)) {
                throw KEMException.criticalError("Sort " + smallSort.toString() + " is undefined.");
            } else {
                throw KEMException.criticalError("Sort " + bigSort.toString() + " is undefined.");
            }
        }
        return isSubsorted;
    }

    public boolean isSubsortedEq(Sort bigSort, Sort smallSort) {
        return bigSort == smallSort || isSubsorted(bigSort, smallSort);
    }

    public Sort getGLBSort(Sort... sorts) {
        return getGLBSort(Sets.newHashSet(sorts));
    }

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
        Sort glbSort = getGLBSort(sort1, sort2);
        return glbSort != null && !glbSort.equals(Sort.BOTTOM);
    }

}
