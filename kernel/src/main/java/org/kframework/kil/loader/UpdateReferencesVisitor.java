// Copyright (c) 2012-2015 K Team. All Rights Reserved.
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
    public Void visit(Syntax syn, Void _void) {
        prodRoot = syn;
        return super.visit(syn, _void);
    }

    @Override
    public Void visit(Production node, Void _void) {
        node.setSort(prodRoot.getDeclaredSort().getSort());
        node.copyAttributesFrom(prodRoot);
        node.setOwnerModuleName(this.getCurrentModule().getName());
        return null;
    }
}
