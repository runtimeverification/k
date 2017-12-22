package org.kframework.backend.java.kil;

import org.kframework.kil.Sort;

import java.util.HashMap;

public class DataStructureSort {
    private final String sort;
    private final Sort type;
    private final String klabel;
    private final String element;
    private final String unit;
    private final HashMap<Object, Object> objectObjectHashMap;

    public DataStructureSort(String sort, Sort type, String klabel, String element, String unit, HashMap<Object, Object> objectObjectHashMap) {
        this.sort = sort;
        this.type = type;
        this.klabel = klabel;
        this.element = element;
        this.unit = unit;
        this.objectObjectHashMap = objectObjectHashMap;
    }

    public String elementLabel() {
        return element;
    }

    public String constructorLabel() {
        return klabel;
    }

    public String unitLabel() {
        return unit;
    }
}
