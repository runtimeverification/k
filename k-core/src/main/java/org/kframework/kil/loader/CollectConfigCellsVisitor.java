// Copyright (c) 2012-2014 K Team. All Rights Reserved.
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
    public Void visit(Configuration config, Void _) {
        return super.visit((Sentence) config, _);
    }

    @Override
    public Void visit(Sentence s, Void _) {
        return null;
    }

    @Override
    public Void visit(Cell cell, Void _) {
        context.addCellDecl(cell);
        return super.visit(cell, _);
    }
}
