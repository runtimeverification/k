// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import com.google.common.collect.Maps;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;

import static org.kframework.kore.KORE.*;

import java.util.Map;

public class SortInfo {
    private final Map<Sort, KLabel> closeOperators = Maps.newHashMap();

    protected void addOp(String sort, String label) {
        closeOperators.put(Sort(sort), KLabel(label));
    }

    public SortInfo() {
    }

    public KLabel getCloseOperator(Sort s) {
        return closeOperators.get(s);
    }
}
