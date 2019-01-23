// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Iterators;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import org.kframework.Collections;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;

import java.util.Map;

import static org.kframework.kore.KORE.*;

/**
 * Information about sorts which is used in cell completion
 */
public class SortInfo {
    private final Map<Sort, KLabel> closeOperators = Maps.newHashMap();

    protected void addOp(Sort sort, String label) {
        closeOperators.put(sort, KLabel(label));
    }

    public SortInfo() {
    }

    /**
     * If s is the sort of the contents of a leaf cell, this returns the label to be used as
     * the union/append operator when turning dots into an explicit variable
     */
    public KLabel getCloseOperator(Sort s) {
        return closeOperators.get(s);
    }

    /**
     * Gather sort information from a module.
     * Populates the close operators only for sorts which only have a single associative production.
     */
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
