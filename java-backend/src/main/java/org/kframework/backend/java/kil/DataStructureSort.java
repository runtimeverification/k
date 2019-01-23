// Copyright (c) 2017-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;

import java.util.HashMap;

public class DataStructureSort {
    private final KLabel klabel;
    private final KLabel element;
    private final KLabel unit;
    private final HashMap<Object, Object> objectObjectHashMap;

    public DataStructureSort(KLabel klabel, KLabel element, KLabel unit, HashMap<Object, Object> objectObjectHashMap) {
        this.klabel = klabel;
        this.element = element;
        this.unit = unit;
        this.objectObjectHashMap = objectObjectHashMap;
    }

    public KLabel elementLabel() {
        return element;
    }

    public KLabel constructorLabel() {
        return klabel;
    }

    public KLabel unitLabel() {
        return unit;
    }
}
