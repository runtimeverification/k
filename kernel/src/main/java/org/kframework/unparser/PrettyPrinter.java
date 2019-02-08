// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.unparser;

import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kore.K;

/**
 * @author Denis Bogdanas
 * Created on 07-Feb-19.
 */
public class PrettyPrinter {
    public final KPrint kprint;
    public final Definition def;
    public final Module module;

    public PrettyPrinter(KPrint kprint, Definition def, Module module) {
        this.kprint = kprint;
        this.def = def;
        this.module = module;
    }

    public void prettyPrint(K target) {
        kprint.prettyPrint(def, module, kprint::outputFile, target);
    }
}
