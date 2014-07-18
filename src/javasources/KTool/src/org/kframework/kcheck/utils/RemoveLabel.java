// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kcheck.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class RemoveLabel extends CopyOnWriteTransformer {

    public final String LABEL = "program-label";
    private boolean removed = false;

    public RemoveLabel(Context context) {
        super("Remove the program klabel", context);
        removed = false;
    }

    @Override
    public ASTNode visit(TermCons node, Void _)  {

        if (node.getProduction().containsAttribute(LABEL) && !removed) {
            Term stmt = node.getContents().get(node.getContents().size() - 1);
            removed = true;
            return stmt;
        }

        return super.visit(node, _);
    }
}
