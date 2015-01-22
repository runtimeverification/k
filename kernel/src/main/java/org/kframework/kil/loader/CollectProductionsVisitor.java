// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.kil.Production;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectProductionsVisitor extends BasicVisitor {
    public CollectProductionsVisitor(Context context) {
        super(context);
    }

    @Override
    public Void visit(Production node, Void _void) {
        context.addProduction(node);
        this.getCurrentModule().getModuleContext().addProduction(node);
        return null;
    }
}
