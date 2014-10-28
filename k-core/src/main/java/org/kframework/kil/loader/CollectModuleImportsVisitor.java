// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.kil.Definition;
import org.kframework.kil.Import;
import org.kframework.kil.visitors.NonCachingVisitor;

public class CollectModuleImportsVisitor extends NonCachingVisitor {

    public CollectModuleImportsVisitor(Context context) {
        super(context);
    }

    @Override
    public Void visit(Definition d, Void _) {
        super.visit(d, _);
        getCurrentDefinition().finalizeModules();
        return null;
    }

    @Override
    public Void visit(Import i, Void _) {
        getCurrentDefinition().addModuleImport(getCurrentModule().getName(), i.getName());
        return null;
    }
}
