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

    public CollectModuleImportsVisitor(Context context, Definition currentDefinition) {
        super(context, currentDefinition);
    }

    public CollectModuleImportsVisitor(Context context,
                                       Definition currentDefinition, Module currentModule) {
        super(context, currentDefinition, currentModule);
    }

    @Override
    public Void visit(Definition d, Void _) {
        if (getCurrentDefinition() == null) {
            return new CollectModuleImportsVisitor(context, d).visit(d, _);
        } else {
            super.visit(d, _);
            getCurrentDefinition().finalizeModules();
            return null;
        }
    }

    @Override
    public Void visit(Module m, Void _) {
        if (getCurrentModule() == null) {
            return new CollectModuleImportsVisitor(context, getCurrentDefinition(), m).visit(m, _);
        } else {
            return super.visit(m, _);
        }
    }

    @Override
    public Void visit(Import i, Void _) {
        getCurrentDefinition().addModuleImport(getCurrentModule().getName(), i.getName());
        return null;
    }
}
