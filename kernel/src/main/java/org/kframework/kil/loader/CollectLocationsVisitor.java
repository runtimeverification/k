// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.kil.Production;
import org.kframework.kil.Sentence;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectLocationsVisitor extends BasicVisitor {
    public CollectLocationsVisitor() {
        super(null);
    }

    @Override
    public Void visit(Production node, Void _void) {
        getCurrentDefinition().locations.put(node.getSource() + ":" + node.getLocation(), node);
        return null;
    }

    @Override
    public Void visit(Sentence node, Void _void) {
        getCurrentDefinition().locations.put(node.getSource() + ":" + node.getLocation(), node);
        return null;
    }
}
