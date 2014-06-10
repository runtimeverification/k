// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.FloatBuiltin;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.KSorts;
import org.kframework.kil.StringBuiltin;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class MaudeHelper {

    public static List<String> separators = new ArrayList<String>();
    public static Set<String> declaredSorts = new HashSet<String>();
    public static Set<String> kLabels = new HashSet<String>();

    public static Set<String> basicSorts = new HashSet<String>();
    static {
        basicSorts.add(KSorts.K);
        basicSorts.add(KSorts.KITEM);
        basicSorts.add(KSorts.KLABEL);
        basicSorts.add(KSorts.KLIST);
        basicSorts.add(KSorts.KRESULT);

        basicSorts.add(KSorts.CELL_LABEL);

        basicSorts.add(BoolBuiltin.SORT_NAME);
        basicSorts.add(IntBuiltin.SORT_NAME);
        basicSorts.add(StringBuiltin.SORT_NAME);
        basicSorts.add(FloatBuiltin.SORT_NAME);

        basicSorts.add(KSorts.BAG);
        basicSorts.add(KSorts.BAG_ITEM);
        basicSorts.add(KSorts.LIST);
        basicSorts.add(KSorts.LIST_ITEM);
        basicSorts.add(KSorts.MAP);
        basicSorts.add(KSorts.MAP_ITEM);
        basicSorts.add(KSorts.SET);
        basicSorts.add(KSorts.SET_ITEM);

        basicSorts.add("#Id");
        basicSorts.add("#Rat");
        basicSorts.add("#ModelCheckerState");
        basicSorts.add("#ModelCheckResult");
        basicSorts.add("#LTLFormula");
        basicSorts.add("#Prop");
    }

    public static Set<String> constantSorts = new HashSet<String>();
    static {
        constantSorts.add(BoolBuiltin.SORT_NAME);
        constantSorts.add(IntBuiltin.SORT_NAME);
        constantSorts.add(StringBuiltin.SORT_NAME);
        constantSorts.add(FloatBuiltin.SORT_NAME);

        constantSorts.add(KSorts.KLABEL);

        constantSorts.add(KSorts.CELL_LABEL);

        /* andreis: not sure if this two are needed */
        constantSorts.add("#Id");
        constantSorts.add("#Rat");
    }
}
