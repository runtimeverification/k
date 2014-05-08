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

    private String prodSort;
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
        context.definedSorts.add(syn.getSort().getName());
        prodSort = syn.getSort().getName();
        return super.visit(syn, _);
    }

    @Override
    public Void visit(Production node, Void _) {
        node.setSort(prodSort);
        node.setOwnerModuleName(moduleName);
        return null;
    }
}
