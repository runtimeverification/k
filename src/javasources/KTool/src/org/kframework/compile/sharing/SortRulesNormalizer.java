// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.compile.sharing;

import java.util.Collections;
import java.util.Comparator;

import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class SortRulesNormalizer extends CopyOnWriteTransformer {

    public SortRulesNormalizer(Context context) {
        super("Sort rules deterministically", context);
    }

    @Override
    public Module visit(Module module, Void _) {
        Collections.sort(module.getItems(), new Comparator<ModuleItem>() {
            @Override
            public int compare(ModuleItem arg0, ModuleItem arg1) {
                int x;
                if ((x = arg0.getFilename().compareTo(arg1.getFilename())) != 0) {
                    return x;
                }
                if ((x = arg0.getLocation().compareTo(arg1.getLocation())) != 0) {
                    return x;
                }
                return arg0.toString().compareTo(arg1.toString());
            }
        });
        return module;
    }
}
