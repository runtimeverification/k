// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.symbolic.LocalVisitor;
import org.kframework.backend.java.symbolic.PrePostVisitor;

/**
 * @author Traian
 */
public class LookupCell extends LocalVisitor {

    public LookupCell(String name) {
        this.cellName = name;
        result = null;
        cellFound = false;
    }

    String cellName;
    Cell result;
    boolean cellFound;

    @Override
    public void visit(Cell cell) {
        if (cell.getLabel().equals(cellName)) {
            result = cell;
            cellFound = true;
        }
        super.visit(cell);
    }

    @Override
    public boolean isProceed() {
        return !cellFound;
    }

    public static Cell find(Term context, final String name) {
        LookupCell cellLocator = new LookupCell(name);
        PrePostVisitor recursiveCellFinder = new PrePostVisitor();
        recursiveCellFinder.getPreVisitor().addVisitor(cellLocator);
        context.accept(recursiveCellFinder);
        return cellLocator.result;
    }
}
