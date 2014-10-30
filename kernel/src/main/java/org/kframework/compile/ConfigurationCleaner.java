// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Cell.Multiplicity;
import org.kframework.utils.errorsystem.KExceptionManager;

public class ConfigurationCleaner extends CopyOnWriteTransformer {

    public ConfigurationCleaner(Context context) {
        super("Configuration Cleaner", context);
        // TODO Auto-generated constructor stub
    }

    @Override
    public ASTNode visit(Cell node, Void _)  {
        if (node.getMultiplicity() == Multiplicity.ANY || node.getMultiplicity() == Multiplicity.MAYBE) {
            if (node.variables().isEmpty()) {
                return new Bag();
            }
        }

        ASTNode result = super.visit(node, _);
        if (result == null) return null;

        if (result == node) {
            node = node.shallowCopy();
        } else {
            if (!(result instanceof Cell)) {
                throw KExceptionManager.internalError(
                        "Expecting Cell, but got " + node.getClass() + " in Configuration Cleaner.",
                        this, node);
            } else    node = (Cell) result;
        }
        node.setDefaultAttributes();
        node.setEllipses(Ellipses.NONE);
        return node;
    }

}


