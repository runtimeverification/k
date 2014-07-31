// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.kil.Production;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectProductionsVisitor extends BasicVisitor {
    public CollectProductionsVisitor(Context context) {
        super(context);
    }

    @Override
    public Void visit(Production node, Void _) {
        context.addProduction(node);
        return null;
    }
}
