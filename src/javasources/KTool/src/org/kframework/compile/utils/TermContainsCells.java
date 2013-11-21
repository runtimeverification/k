package org.kframework.compile.utils;

import org.kframework.kil.Cell;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

/**
 * Created with IntelliJ IDEA.
 * User: andrei.arusoaie
 * Date: 11/21/13
 * Time: 10:29 AM
 * Checks if a given term contains cells.
 */
public class TermContainsCells extends BasicVisitor {


    private boolean termContainsCells;

    public TermContainsCells(Context context) {
        super(context);
        termContainsCells = false;
    }

    @Override
    public void visit(Cell node) {
        termContainsCells = true;
        super.visit(node);
    }

    public boolean getTermContainsCells() {
        return termContainsCells;
    }
}
