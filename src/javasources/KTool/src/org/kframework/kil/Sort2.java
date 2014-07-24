// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kil;

public class Sort2 {

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

}
