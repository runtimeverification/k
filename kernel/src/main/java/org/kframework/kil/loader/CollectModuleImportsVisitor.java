// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.kil.Definition;
import org.kframework.kil.Import;
import org.kframework.kil.visitors.NonCachingVisitor;

public class CollectModuleImportsVisitor extends NonCachingVisitor {

    public CollectModuleImportsVisitor(Context context) {
        super(context);
    }

    @Override
    public Void visit(Definition d, Void _void) {
        super.visit(d, _void);
        getCurrentDefinition().getDefinitionContext().finalizeModules();
        return null;
    }

    @Override
    public Void visit(Import i, Void _void) {
        getCurrentDefinition().getDefinitionContext().addModuleImport(getCurrentModule().getName(), i.getName());
        return null;
    }
}
