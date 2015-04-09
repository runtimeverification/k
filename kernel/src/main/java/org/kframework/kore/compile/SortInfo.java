// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import com.google.common.collect.*;
import org.kframework.Collections;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
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

    public static SortInfo fromModule(Module module) {
        Multimap<Sort, KLabel> joinOps = HashMultimap.create();
        Collections.stream(module.productionsFor()).forEach(x -> {
            if (Collections.stream(x._2()).anyMatch(p -> p.att().contains("assoc")
                    && Collections.stream(p.items()).filter(i -> i instanceof NonTerminal).count() == 2)) {
                joinOps.put(x._2().head().sort(), x._1());
            }
        });
        SortInfo info = new SortInfo();
        joinOps.asMap().forEach((sort, labels) -> {
            info.closeOperators.put(sort, Iterators.getNext(labels.iterator(), null));
        });
        return info;
    }
}
