// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kcheck.utils;

import org.kframework.kil.Cell;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class ExtractCellContent extends BasicVisitor {

    String cellLabel = null;
    private Term content;

    public ExtractCellContent(Context context, String cellLabel) {
        super(context);
        this.cellLabel = cellLabel;
    }

    @Override
    public Void visit(Cell node, Void _) {

        if (node.getLabel().equals(cellLabel)) {
            content = node.getContents();
        }
        return super.visit(node, _);
    }

    public Term getContent() {
        return content;
    }
}
