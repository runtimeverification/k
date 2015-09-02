// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.compile.sharing;

import java.util.Collections;
import java.util.Comparator;

import org.apache.commons.collections4.comparators.ComparableComparator;
import org.apache.commons.collections4.comparators.NullComparator;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class SortRulesNormalizer extends CopyOnWriteTransformer {

    public SortRulesNormalizer(Context context) {
        super("Sort rules deterministically", context);
    }

    @Override
    public Module visit(Module module, Void _void) {
        Collections.sort(module.getItems(), new Comparator<ModuleItem>() {
            @Override
            public int compare(ModuleItem arg0, ModuleItem arg1) {
                Comparator<Source> sourceComparator = new Comparator<Source>() {
                    @Override
                    public int compare(Source o1, Source o2) {
                        return o1.toString().compareTo(o2.toString());
                    }
                };
                NullComparator<Source> nullFcc = new NullComparator<>(sourceComparator);
                int x;
                if ((x = nullFcc.compare(arg0.getSource(), arg1.getSource())) != 0) {
                    return x;
                }

                ComparableComparator<Location> lcc = ComparableComparator.comparableComparator();
                NullComparator<Location> nullLcc = new NullComparator<>(lcc);
                if ((x = nullLcc.compare(arg0.getLocation(), arg1.getLocation())) != 0) {
                    return x;
                }
                return arg0.toString().compareTo(arg1.toString());
            }
        });
        return module;
    }
}
