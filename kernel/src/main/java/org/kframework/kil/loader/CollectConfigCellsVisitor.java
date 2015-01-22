// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Sentence;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectConfigCellsVisitor extends BasicVisitor {
    public CollectConfigCellsVisitor(Context context) {
        super(context);
    }

    @Override
    public Void visit(Configuration config, Void _void) {
        return super.visit((Sentence) config, _void);
    }

    @Override
    public Void visit(Sentence s, Void _void) {
        return null;
    }

    @Override
    public Void visit(Cell cell, Void _void) {
        context.addCellDecl(cell);
        return super.visit(cell, _void);
    }
}
