// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.io.Serializable;
import java.util.Set;

import org.kframework.compile.transformers.CompleteSortLatice;

import com.google.common.collect.ImmutableSet;

public class Sort2 implements Serializable {

    public static final Sort2 K = Sort2.of("K");
    public static final Sort2 KITEM = Sort2.of("KItem");
    public static final Sort2 KLABEL = Sort2.of("KLabel");
    public static final Sort2 KLIST = Sort2.of("KList");
    public static final Sort2 KRESULT = Sort2.of("KResult");

    public static final Sort2 CELL_LABEL = Sort2.of("CellLabel");

    public static final Sort2 BAG = Sort2.of("Bag");
    public static final Sort2 BAG_ITEM = Sort2.of("BagItem");
    public static final Sort2 LIST = Sort2.of("List");
    public static final Sort2 LIST_ITEM = Sort2.of("ListItem");
    public static final Sort2 MAP = Sort2.of("Map");
    public static final Sort2 MAP_ITEM = Sort2.of("MapItem");
    public static final Sort2 SET = Sort2.of("Set");
    public static final Sort2 SET_ITEM = Sort2.of("SetItem");

    public static final Sort2 ID = Sort2.of("Id");
    public static final Sort2 SHARP_ID = Sort2.of("#Id");
    public static final Sort2 INT = Sort2.of("Int");

    public static final Sort2 BOTTOM = Sort2.of(CompleteSortLatice.BOTTOM_SORT_NAME);

    private String name;

    public static Sort2 of(String name) {
        return new Sort2(name);
    }

    private Sort2(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (!(obj instanceof Sort2)) {
            return false;
        }
        Sort2 other = (Sort2) obj;
        return name.equals(other.name);
    }

    @Override
    public int hashCode() {
        return name.hashCode();
    }

    @Override
    public String toString() {
        return name;
    }

    private static Set<Sort2> KSorts = ImmutableSet.of(K, BAG, BAG_ITEM, KITEM,
            KLIST, CELL_LABEL, KLABEL);

    public boolean isKSort() {
        return KSorts.contains(this);
    }

    /**
     * TODO(???)
     * @param sort
     * @return
     */
    public Sort2 getKSort() {
        return KSorts.contains(this) ? this : K;
    }

    public boolean isComputationSort() {
        return equals(K) || equals(KITEM) || !isKSort();
    }

    public boolean isBuiltinSort() {
        /* TODO: replace with a proper table of builtins */
        return equals(BoolBuiltin.SORT)
               || equals(IntBuiltin.SORT)
               || equals(StringBuiltin.SORT)
               || equals(FloatBuiltin.SORT)
               /* LTL builtin sorts */
//               || sort.equals("#LtlFormula")
               || equals(Sort2.of("#Prop"))
               || equals(Sort2.of("#ModelCheckerState"))
               || equals(Sort2.of("#ModelCheckResult"));
    }

    public boolean isDataSort() {
        return equals(BoolBuiltin.SORT)
                || equals(IntBuiltin.SORT)
                || equals(StringBuiltin.SORT);
    }

    /**
     * TODO(???)
     * @return
     */
    public Sort2 mainSort() {
        if (equals(BAG) || equals(BAG_ITEM)) {
            return BAG;
        } else if (equals(KITEM)) {
            return K;
        } else {
            return this;
        }
    }

    public boolean isDefaultable() {
        return equals(K) || equals(BAG);
    }

}
