// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

import com.google.common.collect.ImmutableSet;

public class Sort implements Serializable {

    public static final Sort K = Sort.of("K");
    public static final Sort KITEM = Sort.of("KItem");
    public static final Sort KLABEL = Sort.of("KLabel");
    public static final Sort KLIST = Sort.of("KList");
    public static final Sort KRESULT = Sort.of("KResult");

    public static final Sort CELL_LABEL = Sort.of("CellLabel");

    public static final Sort BAG = Sort.of("Bag");
    public static final Sort BAG_ITEM = Sort.of("BagItem");
    public static final Sort LIST = Sort.of("List");
    public static final Sort LIST_ITEM = Sort.of("ListItem");
    public static final Sort MAP = Sort.of("Map");
    public static final Sort MAP_ITEM = Sort.of("MapItem");
    public static final Sort SET = Sort.of("Set");
    public static final Sort SET_ITEM = Sort.of("SetItem");

    public static final Sort ID = Sort.of("Id");
    public static final Sort INT = Sort.of("Int");
    public static final Sort FLOAT = Sort.of("Float");
    public static final Sort BOOL = Sort.of("Bool");
    public static final Sort STRING = Sort.of("String");

    public static final Sort BUILTIN_ID = Sort.of("#Id");
    public static final Sort BUILTIN_RAT = Sort.of("#Rat");
    public static final Sort BUILTIN_BOOL = Sort.of("#Bool");
    public static final Sort BUILTIN_INT = Sort.of("#Int");
    public static final Sort BUILTIN_FLOAT = Sort.of("#Float");
    public static final Sort BUILTIN_STRING = Sort.of("#String");
    public static final Sort BUILTIN_BOT = Sort.of("#Bot");

    /* IO */
    public static final Sort STREAM = Sort.of("Stream");

    /* tokens */
    public static final Sort BUILTIN_INT32 = Sort.of("#Int32");

    /* LTL builtin sorts */
    public static final Sort BUILTIN_LTL_FORMULA = Sort.of("#LtlFormula");
    public static final Sort BUILTIN_PROP = Sort.of("#Prop");
    public static final Sort BUILTIN_MODEL_CHECKER_STATE = Sort.of("#ModelCheckerState");
    public static final Sort BUILTIN_MODEL_CHECK_RESULT = Sort.of("#ModelCheckResult");

    private final String name;

    public static Sort of(String name) {
        return new Sort(name);
    }

    private Sort(String name) {
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
        if (!(obj instanceof Sort)) {
            return false;
        }
        Sort other = (Sort) obj;
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

    private static Set<Sort> K_SORTS = ImmutableSet.of(K, BAG, BAG_ITEM, KITEM,
            KLIST, CELL_LABEL, KLABEL);

    private static Set<Sort> BASE_SORTS = ImmutableSet.of(K, KRESULT, KITEM,
            KLIST, BAG, BAG_ITEM, KLABEL, CELL_LABEL);

    public boolean isKSort() {
        return K_SORTS.contains(this);
    }

    public boolean isBaseSort() {
        return BASE_SORTS.contains(this);
    }

    public static Set<Sort> getBaseSorts() {
        return new HashSet<Sort>(BASE_SORTS);
    }

    /**
     * TODO(traiansf)
     * @param sort
     * @return
     */
    public Sort getKSort() {
        return K_SORTS.contains(this) ? this : K;
    }

    public boolean isComputationSort() {
        return equals(K) || equals(KITEM) || !isKSort();
    }

    public boolean isBuiltinSort() {
        /* TODO: replace with a proper table of builtins */
        return equals(Sort.BUILTIN_BOOL)
               || equals(Sort.BUILTIN_INT)
               || equals(Sort.BUILTIN_STRING)
               || equals(Sort.BUILTIN_FLOAT)
               /* LTL builtin sorts */
//               || sort.equals(Sort.SHARP_LTL_FORMULA)
               || equals(Sort.BUILTIN_PROP)
               || equals(Sort.BUILTIN_MODEL_CHECKER_STATE)
               || equals(Sort.BUILTIN_MODEL_CHECK_RESULT);
    }

    public boolean isDataSort() {
        return equals(Sort.BUILTIN_BOOL)
                || equals(Sort.BUILTIN_INT)
                || equals(Sort.BUILTIN_STRING);
    }

    public static final String CELL_SORT_NAME = "CellSort";
    public static final String CELL_FRAGMENT_NAME = "CellFragment";
    public static final String LIST_OF_BOTTOM_PREFIX = "#ListOf";

    public boolean isCellSort() {
        return name.endsWith(CELL_SORT_NAME) || name.endsWith(CELL_FRAGMENT_NAME);
    }

    public boolean isCellFragment() {
        return name.endsWith(CELL_FRAGMENT_NAME);
    }

    public boolean isUserListSort() {
        return name.startsWith(LIST_OF_BOTTOM_PREFIX);
    }

    public Sort getUserListSort(String separator) {
        return Sort.of(LIST_OF_BOTTOM_PREFIX + name + "{\"" + separator + "\"}");
    }

    /**
     * TODO(traiansf)
     * @return
     */
    public Sort mainSort() {
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
