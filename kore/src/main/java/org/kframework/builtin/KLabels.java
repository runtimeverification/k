// Copyright (c) 2015-2018 K Team. All Rights Reserved.

package org.kframework.builtin;

import org.kframework.kore.KLabel;

import static org.kframework.kore.KORE.KLabel;

public class KLabels {
    public static final KLabel AND = KLabel("_andBool_");
    public static final KLabel OR = KLabel("_orBool_");

    public static final KLabel KSEQ = KLabel("#KSequence");
    public static final KLabel DOTK = KLabel("#EmptyK");

    public static final KLabel CELLS = KLabel("#cells");

    public static final KLabel DOTS = KLabel("#dots");
    public static final KLabel NO_DOTS = KLabel("#noDots");

    public static final KLabel KREWRITE = KLabel("#KRewrite");

    public static final String GENERATED_TOP_CELL = "generatedTop";
    public static final String THIS_CONFIGURATION = "THIS_CONFIGURATION";
    public static final KLabel ML_FALSE = KLabel("#False");
    public static final KLabel ML_TRUE = KLabel("#True");
    public static final KLabel ML_OR = KLabel("#Or");
    public static final KLabel ML_AND = KLabel("#And");

    public static final KLabel ListItem = KLabel("ListItem");
    public static final KLabel DotMap = KLabel(".Map");
    public static final KLabel List = KLabel("_List_");
    public static final KLabel DotList = KLabel(".List");
    public static final KLabel EQUALS_K = KLabel("_==K_");

    public static final KLabel MAP_CHOICE = KLabel("Map:choice");
    public static final KLabel SET_CHOICE = KLabel("Set:choice");
    public static final KLabel LIST_GET = KLabel("List:get");
    public static final KLabel MAP_LOOKUP = KLabel("Map:lookup");
    public static final KLabel SET_MEMBERSHIP = KLabel("Set:in");
    public static final KLabel LIST_RANGE = KLabel("List:range");
    public static final KLabel MAP_UPDATE = KLabel("updateMap");
    public static final KLabel MAP_REMOVE_ALL = KLabel("removeAll");
    public static final KLabel SET_REMOVE_ALL = KLabel("Set:difference");
    public static final KLabel MAP_KEYS = KLabel("keys");

    public static final String INJ = "inj";
}
