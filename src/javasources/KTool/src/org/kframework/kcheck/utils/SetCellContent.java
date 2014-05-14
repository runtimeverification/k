// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kcheck.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class SetCellContent extends CopyOnWriteTransformer {

    private Term term;
    private String cell;

    public SetCellContent(Context context, Term term, String cell) {
        super("Replace content of the K cell with variable", context);
        this.term = term;
        this.cell = cell;
    }

    @Override
    public ASTNode visit(Cell node, Void _)  {
        if (node.getLabel().equals(cell)){
            Cell newCell = node.shallowCopy();
            newCell.setContents(term);
            return newCell;
        }
        return super.visit(node, _);
    }
}
