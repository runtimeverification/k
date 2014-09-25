// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.kil.Definition;
import org.kframework.kil.Import;
import org.kframework.kil.Module;
import org.kframework.kil.visitors.NonCachingVisitor;

public class CollectModuleImportsVisitor extends NonCachingVisitor {

    public CollectModuleImportsVisitor(Context context) {
        super(context);
    }

    private String parentModule = null;

    public Void visit(Definition def, Void _) {
        super.visit(def, _);
        context.finalizeModules();
        return null;
    }

    public Void visit(Module m, Void _) {
        parentModule = m.getName();
        return super.visit(m, _);
    }

    public Void visit(Import i, Void _) {
        context.addModuleImport(parentModule, i.getName());
        return null;
    }
}
