// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.kil.*;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KExceptionManager;
import java.util.HashMap;
import java.util.Map;

/**
 * Checks that no two cells with the same name are declared in the configuration.
 */
public class CheckConfigurationCells extends BasicVisitor {

    Map<String,Cell> cells = new HashMap<String,Cell>();

    @Override
    public Void visit(Configuration node, Void _void) {
        cells.clear();
        return super.visit(node, _void);
    }

    public CheckConfigurationCells(org.kframework.kil.loader.Context context) {
        super("Check that configuration cells have unique names", context);
    }

    @Override
    public Void visit(Syntax node, Void _void) {
        return null;
    }

    @Override
    public Void visit(org.kframework.kil.Context node, Void _void) {
        return null;
    }

    @Override
    public Void visit(Rule node, Void _void) {
        return null;
    }

    @Override
    public Void visit(Cell node, Void _void) {
        Cell cell = cells.get(node.getId());
        if (cell != null) {
            throw KExceptionManager.compilerError(
                    "Cell " + node.getId() + " found twice in configuration (once at " + cell.getLocation() + ").",
                    this, node);
        }
        cells.put(node.getId(), node);
        super.visit(node, _void);
        return null;
    }
}