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

    /**
     * Add the sort attribute to every production when calling the collector
     */
    @Override
    public Void visit(Syntax syn, Void _) {
        prodRoot = syn;
        return super.visit(syn, _);
    }

    @Override
    public Void visit(Production node, Void _) {
        node.setSort(prodRoot.getDeclaredSort().getSort());
        node.copyAttributesFrom(prodRoot);
        node.setOwnerModuleName(this.getCurrentModule().getName());
        return null;
    }
}
