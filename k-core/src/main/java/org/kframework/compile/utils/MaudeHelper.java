// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.Sort;

import java.util.HashSet;
import java.util.Set;

public class MaudeHelper {

    public static Set<Sort> declaredSorts = new HashSet<>();
    public static Set<String> kLabels = new HashSet<String>();

    public static boolean isBasicSort(Sort sort) {
        return basicSorts.contains(sort);
    }
    private static Set<Sort> basicSorts = new HashSet<>();
    static {
        basicSorts.add(Sort.K);
        basicSorts.add(Sort.KITEM);
        basicSorts.add(Sort.KLABEL);
        basicSorts.add(Sort.KLIST);
        basicSorts.add(Sort.KRESULT);

        basicSorts.add(Sort.CELL_LABEL);

        basicSorts.add(Sort.BUILTIN_BOOL);
        basicSorts.add(Sort.BUILTIN_INT);
        basicSorts.add(Sort.BUILTIN_STRING);
        basicSorts.add(Sort.BUILTIN_FLOAT);

        basicSorts.add(Sort.BAG);
        basicSorts.add(Sort.BAG_ITEM);
        basicSorts.add(Sort.LIST);
        basicSorts.add(Sort.LIST_ITEM);
        basicSorts.add(Sort.MAP);
        basicSorts.add(Sort.MAP_ITEM);
        basicSorts.add(Sort.SET);
        basicSorts.add(Sort.SET_ITEM);

        basicSorts.add(Sort.BUILTIN_ID);
        basicSorts.add(Sort.BUILTIN_RAT);
        basicSorts.add(Sort.BUILTIN_MODEL_CHECKER_STATE);
        basicSorts.add(Sort.BUILTIN_MODEL_CHECK_RESULT);
        basicSorts.add(Sort.BUILTIN_LTL_FORMULA);
        basicSorts.add(Sort.BUILTIN_PROP);
    }

    public static boolean isConstantSort(Sort sort) {
        return constantSorts.contains(sort);
    }
    private static Set<Sort> constantSorts = new HashSet<>();
    static {
        constantSorts.add(Sort.BUILTIN_BOOL);
        constantSorts.add(Sort.BUILTIN_INT);
        constantSorts.add(Sort.BUILTIN_STRING);
        constantSorts.add(Sort.BUILTIN_FLOAT);

        constantSorts.add(Sort.KLABEL);

        constantSorts.add(Sort.CELL_LABEL);

        /* andreis: not sure if this two are needed */
        constantSorts.add(Sort.BUILTIN_ID);
        constantSorts.add(Sort.BUILTIN_RAT);
    }
}
