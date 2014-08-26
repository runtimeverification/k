// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.kil.Module;
import org.kframework.kil.Production;
import org.kframework.kil.Syntax;
import org.kframework.kil.visitors.BasicVisitor;

public class UpdateReferencesVisitor extends BasicVisitor {
    public UpdateReferencesVisitor(Context context) {
        super(context);
    }

    private Syntax prodRoot;
    private String moduleName;

    @Override
    public Void visit(Module mod, Void _) {
        moduleName = mod.getName();
        return super.visit(mod, _);
    }

    /**
     * Add the sort attribute to every production when calling the collector
     */
    @Override
    public Void visit(Syntax syn, Void _) {
        prodRoot = syn;
        context.definedSorts.add(prodRoot.getDeclaredSort().getSort());
        return super.visit(syn, _);
    }

    @Override
    public Void visit(Production node, Void _) {
        node.setSort(prodRoot.getDeclaredSort().getSort());
        node.copyAttributesFrom(prodRoot);
        node.setOwnerModuleName(moduleName);
        return null;
    }
}
